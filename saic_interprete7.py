"""
saic_interprete7.py - Convierte una petición en lenguaje natural en una consulta
validada al SAIC.

Cómo trabaja (la IA es el último recurso, nunca arma la petición al INEGI):
  1. REGLAS (sin IA): detecta años, claves de variable (H001A...), estados,
     "nacional" y los conceptos del GLOSARIO (PIB, empleo...).
  2. Si queda algo sin entender (un municipio, un sector, un concepto
     difuso...), llama UNA vez a Gemini, que solo puede elegir de los catálogos.
  3. Todo lo que devuelve la IA se valida contra los catálogos; lo inválido se
     descarta y se avisa.
  4. Muestra un resumen y pide confirmación antes de descargar.

Uso (en la Terminal, dentro de la carpeta con saic_motor3.py y catalogos/):
    python3 saic_interprete7.py "dame del 2008 de Nuevo León K000A e I000A"
    python3 saic_interprete7.py           (te pregunta la petición)

Para el caso con IA, antes define tu clave (solo en esa ventana de Terminal):
    export GEMINI_API_KEY="tu_clave"
"""

import difflib
import json
import os
import re
import sys
import time

from saic_motor3 import (CARPETA_CAT, Catalogos, consultar_saic, crear_sesion,
                         descargar_excel_oficial, nombre_base, normalizar, _lista)

MODELO = "gemini-3.8-flash"
# Modelos de respaldo, en orden: se usan solos cuando el principal está saturado,
# sin cuota o no disponible. Cada modelo tiene su propia cuota diaria gratuita.
# Se dejaron fuera los de imágenes, voz, video, embeddings y similares, los "pro",
# los 2.5 (ya no están disponibles para cuentas nuevas) y los Gemma (no está
# confirmado que entreguen JSON). Para cambiar la lista sin tocar el código:
#   export GEMINI_MODELOS_RESPALDO="modelo-1,modelo-2"
MODELOS_RESPALDO = ["gemini-3.7-flash", "gemini-3.6-flash", "gemini-3.5-flash",
                    "gemini-3.5-flash-lite", "gemini-3.1-flash-lite"]
_env = os.environ.get("GEMINI_MODELOS_RESPALDO", "").strip()
if _env:
    MODELOS_RESPALDO = [m.strip().replace("models/", "") for m in _env.split(",") if m.strip()]
ESPERAS = (0, 3, 8, 15)   # reintentos del modelo principal si Gemini está saturado (503)
ESPERAS_RESPALDO = (0, 3)  # reintentos de cada modelo de respaldo
MAX_LUGARES = 600         # tope de lugares por consulta (Oaxaca tiene 570 municipios)
RUTA_CACHE_IA = os.path.join(CARPETA_CAT, "_cache_interprete.json")

# Frases que significan "a nivel nacional" (sin acentos; las largas primero)
FRASES_NACIONAL = ("a nivel nacional", "todo el pais", "en el pais", "del pais",
                   "nacionales", "nacional")
FRASES_TODOS_ESTADOS = ("todos los estados", "todas las entidades federativas",
                        "todas las entidades", "cada estado", "cada entidad",
                        "por estado", "por entidad")

# --------------------------------------------------------------------------
# GLOSARIO: conceptos frecuentes -> variables del SAIC.
# ES TUYO: edítalo con tu criterio de economista. Formato:
#   "texto a buscar (sin acentos, minúsculas)": (["CLAVE", ...], "nota o None")
# --------------------------------------------------------------------------
NOTA_PIB = ("El SAIC no publica el PIB. El valor agregado censal bruto (A131A) "
            "es la variable más cercana, pero no equivale al PIB.")
GLOSARIO = {
    "pib": (["A131A"], NOTA_PIB),
    "producto interno bruto": (["A131A"], NOTA_PIB),
    "valor agregado censal bruto": (["A131A"], None),
    "valor agregado": (["A131A"], None),
    "produccion bruta": (["A111A"], None),
    "personal ocupado": (["H001A"], None),
    "empleo": (["H001A"], "Usé personal ocupado total (H001A) como medida de empleo."),
    "empleos": (["H001A"], "Usé personal ocupado total (H001A) como medida de empleo."),
    "remuneraciones": (["J000A"], None),
    "inversion": (["A211A"], None),
    "formacion bruta de capital fijo": (["A221A"], None),
    "activos fijos": (["Q000A"], None),
    "consumo intermedio": (["A121A"], None),
    "unidades economicas": (["UE"], None),
}

# Palabras que no cambian el significado de la petición (ya sin acentos).
RELLENO = {
    "dame", "dime", "quiero", "necesito", "muestra", "muestrame", "entrega",
    "entregame", "descarga", "descargame", "por", "favor", "los", "las", "el",
    "la", "de", "del", "en", "y", "e", "o", "u", "para", "con", "un", "una",
    "al", "a", "ano", "anos", "censal", "censales", "censo", "censos",
    "variable", "variables", "dato", "datos", "todos", "todas", "sectores",
    "total", "millones", "pesos", "relacionada", "relacionadas", "relacionado",
    "relacionados", "estado", "cifras", "informacion", "sobre", "que", "se",
    "entidad", "lugar",
}


# ------------------------------------------------------------------ REGLAS
def _quitar(t, patron):
    """Busca un patrón en el texto, lo recorta y devuelve (coincidencias, texto)."""
    hallados = [m for m in re.finditer(patron, t)]
    for m in hallados:
        t = t[:m.start()] + " " * (m.end() - m.start()) + t[m.end():]
    return hallados, t


def _agregar(lista, nuevos):
    for x in nuevos:
        if x not in lista:
            lista.append(x)


def _resumir(lista, n=5):
    """Acorta listas largas para mostrarlas: primeros n y cuántos más hay."""
    if len(lista) <= n:
        return lista
    return lista[:n] + [f"… y {len(lista) - n} más (total {len(lista)})"]


def _municipios_de(cat, clave_estado):
    return [c for c, f in cat.lugares.items()
            if f["tipo_lugar"] == "municipio" and f["padre"] == clave_estado]


def _patron_todos_estados():
    return r"(?<!\w)(?:" + "|".join(re.escape(f) for f in FRASES_TODOS_ESTADOS) + r")(?!\w)"


def _patron_estados_de(cat):
    """'todos los estados de Chihuahua': un estado no contiene otros estados."""
    nombres = sorted((n for n, c in cat._estados.items() if c != "00" and n != "mexico"),
                     key=len, reverse=True)
    alternativa = "|".join(re.escape(n) for n in nombres)
    return (r"(?<!\w)(?:todos los |todas las |cada |los )?(?:estados|entidades(?:\s+federativas)?)"
            r"\s+(?:de\s+la\s+|de\s+|del\s+|en\s+)(?:estado\s+de\s+)?"
            rf"({alternativa})(?!\w)")


def _aclarar_estados_de(destino, cat, clave):
    nombre = cat.nombre_lugar(clave)
    candidatos = []
    munis = _municipios_de(cat, clave)
    if munis:
        candidatos.append((munis, f"Todos los municipios de {nombre} ({len(munis)})"))
    candidatos.append(([clave], f"Solo {nombre}"))
    estados = [c for c, f in cat.lugares.items() if f["tipo_lugar"] == "estado"]
    candidatos.append((estados, f"Todos los estados del país ({len(estados)})"))
    _aclarar(destino, f"Pides 'todos los estados de {nombre}', pero {nombre} es un estado y no "
                      "contiene otros estados. ¿Qué quieres consultar?", "lugares", candidatos)


def _patron_municipios(cat):
    nombres = sorted((n for n in cat._estados if n not in ("mexico", "nacional", "pais")),
                     key=len, reverse=True)
    alternativa = "|".join(re.escape(n) for n in nombres)
    return (r"(?<!\w)(?:(?:todos los |todas las |cada |los )?(?:municipios|alcaldias)"
            r"|cada municipio|por municipios?)"
            r"\s+(?:de\s+la\s+|de\s+|del\s+|en\s+)?"
            rf"(?:estado\s+de\s+)?({alternativa})(?!\w)")


def _expandir_masivo(texto, cat):
    """
    Entiende 'todos los estados' y 'todos los municipios de X'.
    Devuelve (claves, nota) o None si el texto no es de ese tipo.
    """
    n = " " + re.sub(r"[,;:()\[\]{}¿?¡!\"'.]", " ", normalizar(texto)) + " "
    if re.search(_patron_todos_estados(), n):
        claves = [c for c, f in cat.lugares.items() if f["tipo_lugar"] == "estado"]
        return claves, f"Expandí 'todos los estados' a {len(claves)} estados."
    m = re.search(_patron_municipios(cat), n)
    if m:
        clave = cat._estados[m.group(1)]
        claves = _municipios_de(cat, clave)
        if claves:
            return claves, (f"Expandí 'todos los municipios de {cat.nombre_lugar(clave)}' "
                            f"a {len(claves)} municipios.")
    return None


MENSAJE_MEXICO = ("'México' puede ser el país (Total Nacional, 00) o el Estado de México (15). "
                  "Elige una opción o escribe 'nacional' o 'Estado de México'.")


def _opcion(campo, mensaje, candidatos):
    """Una aclaración con botones: la página muestra un botón por candidato."""
    return {"campo": campo, "mensaje": mensaje,
            "candidatos": [{"valor": v, "texto": t} for v, t in candidatos]}


def _aclarar(destino, mensaje, campo=None, candidatos=None):
    """Registra una aclaración (y sus botones) en un plan o en el resultado de las reglas."""
    if mensaje in destino["aclarar"]:
        return
    destino["aclarar"].append(mensaje)
    if campo and candidatos:
        destino["opciones"].append(_opcion(campo, mensaje, candidatos))


def _cand_anios(cat):
    return [(int(a), str(a)) for a in cat.anios]


def _cand_mexico(cat):
    candidatos = []
    if "00" in cat.lugares:
        candidatos.append(("00", "Total Nacional / país (00)"))
    if "15" in cat.lugares:
        candidatos.append(("15", "Estado de México (15)"))
    return candidatos


def _cand_estratos(cat):
    return [(k, f["nombre"]) for k, f in cat.estratos.items()]


def _cand_lugar(cat, texto, maximo=6):
    """Opciones para un lugar ambiguo (varios municipios iguales) o mal escrito."""
    n = normalizar(texto)
    if "," in n:
        return []
    exactos = cat._municipios.get(n, [])
    if n in cat._estados or len(exactos) == 1:
        return []
    if len(exactos) > 1:
        claves = list(exactos)
    else:
        nombres = difflib.get_close_matches(
            n, list(cat._estados) + list(cat._municipios), n=4, cutoff=0.7)
        claves = []
        for nombre in nombres:
            if nombre in cat._estados:
                claves.append(cat._estados[nombre])
            else:
                claves.extend(cat._municipios[nombre])
    vistos = []
    for c in claves:
        if c not in vistos:
            vistos.append(c)
    return [(c, f"{cat.nombre_lugar(c)} ({c})") for c in vistos[:maximo]]


def _quitar_filtrado(t, patron, aceptar):
    """Recorta solo las coincidencias que 'aceptar' valida (devuelve algo distinto de None)."""
    aceptadas = []
    for m in list(re.finditer(patron, t)):
        valor = aceptar(m)
        if valor is not None:
            aceptadas.append((m, valor))
    for m, _ in aceptadas:
        t = t[:m.start()] + " " * (m.end() - m.start()) + t[m.end():]
    return [v for _, v in aceptadas], t


def _extraer_estratos(t, cat):
    """
    Reconoce estratos escritos de varias formas: "11 a 50", "del 11 al 50", "11-50",
    "251 y más", "más de 250", "suma de estratos". Solo recorta lo que corresponde
    a un estrato real del catálogo; un rango que no existe (p. ej. "11 al 40") se
    deja sin tocar para que se pida aclarar.
    """
    claves = []
    por_rango, por_inicio = {}, {}
    sufijo = r"(?:\s+(?:personas|empleados|trabajadores)(?:\s+ocupad[oa]s)?)?"
    for clave, f in cat.estratos.items():
        nombre = normalizar(f["nombre"])
        m = re.fullmatch(r"(\d+) a (\d+)", nombre)
        if m:
            por_rango[(int(m.group(1)), int(m.group(2)))] = clave
        m = re.fullmatch(r"(\d+) y mas", nombre)
        if m:
            por_inicio[int(m.group(1))] = clave
        hallados, t = _quitar(t, rf"(?<!\w){re.escape(nombre)}(?!\w)" + sufijo)
        if hallados:
            _agregar(claves, [clave])

    nuevas, t = _quitar_filtrado(
        t, r"(?<!\d)(\d+)\s*(?:a|al|hasta|-|–|—)\s*(\d+)(?!\d)" + sufijo,
        lambda m: por_rango.get((int(m.group(1)), int(m.group(2)))))
    for c in nuevas:
        _agregar(claves, [c])
    nuevas, t = _quitar_filtrado(
        t, r"(?<!\d)(\d+)\s*(?:y mas|o mas|\+|en adelante)(?!\w)" + sufijo,
        lambda m: por_inicio.get(int(m.group(1))))
    for c in nuevas:
        _agregar(claves, [c])
    nuevas, t = _quitar_filtrado(
        t, r"(?<!\w)mas de\s+(\d+)(?!\d)" + sufijo,
        lambda m: por_inicio.get(int(m.group(1)) + 1))
    for c in nuevas:
        _agregar(claves, [c])
    return claves, t


def extraer_determinista(texto, cat):
    t = " " + re.sub(r"[,;:()\[\]{}¿?¡!\"'.]", " ", normalizar(texto)) + " "
    r = {"anios": [], "lugares": [], "variables": [], "estratos": [], "notas": [],
         "avisos": [], "aclarar": [], "opciones": [], "residuo": []}
    validos = sorted(int(a) for a in cat.anios)

    # 0a) "todos los estados de X" (ambiguo), "todos los estados" y "todos los municipios de X"
    hallados, t = _quitar(t, _patron_estados_de(cat))
    for m in hallados:
        _aclarar_estados_de(r, cat, cat._estados[m.group(1)])
    hallados, t = _quitar(t, _patron_todos_estados())
    if hallados:
        claves = [c for c, f in cat.lugares.items() if f["tipo_lugar"] == "estado"]
        _agregar(r["lugares"], claves)
        r["notas"].append(f"Expandí 'todos los estados' a {len(claves)} estados.")
    hallados, t = _quitar(t, _patron_municipios(cat))
    for m in hallados:
        clave = cat._estados[m.group(1)]
        claves = _municipios_de(cat, clave)
        if claves:
            _agregar(r["lugares"], claves)
            r["notas"].append(f"Expandí 'todos los municipios de {cat.nombre_lugar(clave)}' "
                              f"a {len(claves)} municipios.")
        else:
            r["aclarar"].append(f"No encontré municipios para '{cat.nombre_lugar(clave)}'.")

    # 0b) "a nivel nacional", "nacionales", "del país" -> Total Nacional (00)
    if "00" in cat.lugares:
        for frase in FRASES_NACIONAL:
            hallados, t = _quitar(t, rf"(?<!\w){re.escape(frase)}(?!\w)")
            if hallados:
                _agregar(r["lugares"], ["00"])

    # 0c) "sin estratos", "ningún estrato", "estratos: ninguno" -> sin filtro de estrato
    hallados, t = _quitar(t, r"(?<!\w)(?:sin|ningun|ninguna)\s+estratos?(?!\w)"
                             r"|(?<!\w)estratos?\s+(?:ninguno|ninguna)(?!\w)")
    r["sin_estratos"] = bool(hallados)

    # 0c-bis) "todas las actividades (económicas)" = todos los sectores (valor por defecto)
    hallados, t = _quitar(t, r"(?<!\w)todas las actividades(?: economicas)?(?!\w)"
                             r"|(?<!\w)sectores economicos(?!\w)")

    # 0d) estratos: "estrato de 11 a 50", "estratos del 11 al 50", "251 y más", "más de 250"
    if re.search(r"(?<!\w)estratos?(?!\w)", t):
        claves, t = _extraer_estratos(t, cat)
        for c in claves:
            _agregar(r["estratos"], [c])
        if r["estratos"]:
            _, t = _quitar(t, r"(?<!\w)estratos?(?!\w)")

    # 1) rangos de años: "2003 a 2023" -> todos los años del catálogo en ese rango
    hallados, t = _quitar(t, r"(?<!\d)(\d{4})\s+(?:a|al|hasta)\s+(\d{4})(?!\d)")
    for m in hallados:
        ini, fin = sorted((int(m.group(1)), int(m.group(2))))
        for a in validos:
            if ini <= a <= fin and a not in r["anios"]:
                r["anios"].append(a)

    # 2) "todos los años"
    hallados, t = _quitar(t, r"\b(?:todos los anos|cada ano|todos los censos|todos los periodos)\b")
    if hallados:
        r["anios"] = list(validos)

    # 3) años sueltos: los válidos se aceptan; los demás se piden aclarar
    hallados, t = _quitar(t, r"(?<!\d)(?:19|20)\d{2}(?!\d)")
    for m in hallados:
        a = int(m.group(0))
        if a in validos:
            if a not in r["anios"]:
                r["anios"].append(a)
        else:
            _aclarar(r, f"El año {a} no existe en el SAIC. Disponibles: {validos}",
                     "anios", _cand_anios(cat))

    # 4) claves de variable explícitas (H001A, K000A, UE...)
    hallados, t = _quitar(t, r"\b(?:[a-z]\d{3}[a-z]|ue)\b")
    for m in hallados:
        clave = m.group(0).upper()
        if clave in cat.variables:
            if clave not in r["variables"]:
                r["variables"].append(clave)
        else:
            r["avisos"].append(f"La clave '{clave}' no existe en el catálogo de variables.")

    # 5) glosario de conceptos (primero los términos más largos)
    for termino in sorted(GLOSARIO, key=len, reverse=True):
        hallados, t = _quitar(t, rf"(?<!\w){re.escape(termino)}(?!\w)")
        if hallados:
            claves, nota = GLOSARIO[termino]
            for c in claves:
                if c in cat.variables and c not in r["variables"]:
                    r["variables"].append(c)
            if nota and nota not in r["notas"]:
                r["notas"].append(nota)

    # 5c) "el municipio de Chihuahua" (singular) es un municipio, no el estado: se deja a la IA
    extra_residuo = []
    nombres_est = sorted((n for n, c in cat._estados.items() if c != "00" and n != "mexico"),
                         key=len, reverse=True)
    if nombres_est:
        alt_est = "|".join(re.escape(n) for n in nombres_est)
        hallados, t = _quitar(t, r"(?<!\w)municipio\s+(?:de\s+la\s+|de\s+|del\s+)?"
                                 rf"(?:estado\s+de\s+)?(?:{alt_est})(?!\w)")
        extra_residuo = [m.group(0).strip() for m in hallados]

    # 6) estados, nacional y alias (nombres más largos primero).
    #    "México" suelto es ambiguo (país o Estado de México): se pide aclarar.
    nombres = sorted((n for n in cat._estados if n != "mexico"), key=len, reverse=True)
    for n in nombres:
        hallados, t = _quitar(t, rf"(?<!\w){re.escape(n)}(?!\w)")
        if hallados and cat._estados[n] not in r["lugares"]:
            r["lugares"].append(cat._estados[n])
    hallados, t = _quitar(t, r"(?<!\w)mexico(?!\w)")
    if hallados:
        _aclarar(r, MENSAJE_MEXICO, "lugares", _cand_mexico(cat))

    # 6b) "por municipio", "con todos sus municipios", "a nivel municipal":
    #     sustituye cada estado mencionado por todos sus municipios
    hallados, t = _quitar(t, r"(?<!\w)(?:con |y )?(?:todos |todas )?sus municipios(?!\w)"
                             r"|(?<!\w)(?:desglosad[oa]s? |desagregad[oa]s? )?por municipios?(?!\w)"
                             r"|(?<!\w)a nivel municipal(?!\w)|(?<!\w)desglose municipal(?!\w)")
    if hallados:
        estados = [c for c in r["lugares"] if cat.lugares[c]["tipo_lugar"] == "estado"]
        if "00" in r["lugares"]:
            _aclarar(r, "Desglosar todo el país por municipio serían unos 2,400 lugares y el máximo "
                        "por consulta es 600. Indica uno o varios estados.")
        elif estados:
            for e in estados:
                munis = _municipios_de(cat, e)
                if not munis:
                    r["avisos"].append(f"No encontré municipios para {cat.nombre_lugar(e)}; "
                                       "dejé el estado completo.")
                    continue
                r["lugares"] = [c for c in r["lugares"] if c != e]
                _agregar(r["lugares"], munis)
                r["notas"].append(f"Entendí 'por municipio' como todos los municipios de "
                                  f"{cat.nombre_lugar(e)} ({len(munis)}). El total del estado no se "
                                  "incluye; pídelo aparte si lo necesitas.")
        elif not r["lugares"]:
            _aclarar(r, "Para desglosar por municipio indica uno o varios estados "
                        "(por ejemplo: 'de Chihuahua por municipio').")

    # 7) lo que sobra: palabras que las reglas no entienden
    sobran = re.findall(r"[a-z0-9\-]+", t)
    r["residuo"] = [w for w in sobran if w not in RELLENO] + extra_residuo
    return r


# ------------------------------------------------------------------ IA
def construir_prompt(texto, cat):
    variables = "\n".join(f"{k}: {f['nombre']}" for k, f in cat.variables.items())
    sectores = "\n".join(f"{k}: {cat.actividades[k]['nombre']}" for k in cat.sectores)
    cands = cat.buscar_actividades(texto, 12)
    candidatas = "\n".join(f"{c['clave']}: {c['nombre']}" for c in cands) or "(ninguna)"
    estratos = "\n".join(f"{k}: {f['nombre']}" for k, f in cat.estratos.items())
    return f"""Eres un traductor de peticiones para el SAIC del INEGI (Censos Económicos).
Convierte la petición en un objeto JSON. Responde SOLO el JSON, sin texto extra.

Llaves obligatorias:
- "anios": lista de años elegidos entre {cat.anios}. Si la petición no menciona año, [].
- "lugares": lista de textos tal como los nombra la persona. Para un municipio usa
  "Municipio, Estado". Si piden datos a nivel nacional (nacional, nacionales, del país),
  devuelve ["Total Nacional"]. Para "todos los municipios de X" o "todos los estados"
  devuelve exactamente ese texto, sin expandirlo. No inventes lugares. Si no menciona
  lugar, [].
- "variables": lista de CLAVES elegidas SOLO de la lista VARIABLES. Si piden un
  concepto, elige las más cercanas de la lista y explícalo en "nota". Nunca inventes claves.
- "actividades": lista de claves SOLO de SECTORES o CANDIDATAS. [] significa todos los sectores.
- "estratos": claves SOLO de ESTRATOS; [] si no los mencionan.
- "nota": una frase corta con lo que elegiste y por qué, o la duda que tengas.

VARIABLES:
{variables}

SECTORES:
{sectores}

CANDIDATAS (actividades más finas que podrían aplicar):
{candidatas}

ESTRATOS:
{estratos}

PETICIÓN: {texto}
"""


def _contiene(mensaje, *marcas):
    return any(m in mensaje for m in marcas)


def llm_gemini(prompt):
    """
    Llama a Gemini y devuelve el texto de la respuesta (JSON).
    Prueba el modelo principal y, si está saturado (503), sin cuota (429) o no
    disponible (404/403), pasa solo al siguiente de MODELOS_RESPALDO.
    """
    clave = os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY")
    if not clave:
        raise RuntimeError("Falta la clave de Gemini. En la Terminal ejecuta:\n"
                           "    export GEMINI_API_KEY=\"tu_clave\"")
    from google import genai
    from google.genai import types

    cliente = genai.Client(api_key=clave)
    modelos = [MODELO] + [m for m in MODELOS_RESPALDO if m != MODELO]

    sin_cuota = saturado = False
    for i, modelo in enumerate(modelos):
        for espera in (ESPERAS if i == 0 else ESPERAS_RESPALDO):
            time.sleep(espera)
            try:
                resp = cliente.models.generate_content(
                    model=modelo, contents=prompt,
                    config=types.GenerateContentConfig(
                        response_mime_type="application/json", temperature=0))
                if i > 0:
                    print(f"[IA] respondió el modelo de respaldo {modelo}")
                return resp.text
            except Exception as e:
                mensaje = str(e)
                if _contiene(mensaje, "429", "RESOURCE_EXHAUSTED"):
                    sin_cuota = True
                    break  # reintentar no ayuda: probar el siguiente modelo
                if _contiene(mensaje, "404", "NOT_FOUND", "403", "PERMISSION_DENIED"):
                    break  # modelo no disponible para esta cuenta: probar el siguiente
                if _contiene(mensaje, "503", "UNAVAILABLE"):
                    saturado = True
                    continue
                if i > 0 and _contiene(mensaje, "400", "INVALID_ARGUMENT"):
                    break  # un respaldo que no acepta esta petición se salta
                raise

    if saturado:
        raise RuntimeError("Gemini está saturado en este momento. Intenta de nuevo en un minuto.")
    if sin_cuota:
        raise RuntimeError("Se agotó la cuota diaria gratuita de Gemini. Se reinicia cada día. "
                           "Mientras tanto, escribe la petición con claves explícitas "
                           "(por ejemplo: 2008, Nuevo León, K000A, I000A).")
    raise RuntimeError("No pude usar Gemini: ningún modelo de la lista está disponible. "
                       "Revisa MODELO y MODELOS_RESPALDO en saic_interprete7.py.")


def _leer_json(texto):
    limpio = re.sub(r"^```(?:json)?|```$", "", texto.strip(), flags=re.MULTILINE).strip()
    try:
        datos = json.loads(limpio)
    except json.JSONDecodeError:
        raise RuntimeError(f"La IA no devolvió un JSON válido: {texto[:300]}")
    if not isinstance(datos, dict):
        raise RuntimeError(f"La IA no devolvió un objeto JSON: {texto[:300]}")
    return datos


def pedir_ia(texto, cat, llm=None, usar_cache=True):
    """Pide la interpretación a la IA (con caché en disco para no gastar cuota)."""
    llave = normalizar(texto)
    cache = {}
    if usar_cache and os.path.exists(RUTA_CACHE_IA):
        with open(RUTA_CACHE_IA, encoding="utf-8") as f:
            cache = json.load(f)
        if llave in cache:
            return cache[llave]

    respuesta = (llm or llm_gemini)(construir_prompt(texto, cat))
    datos = _leer_json(respuesta)

    if usar_cache:
        cache[llave] = datos
        os.makedirs(os.path.dirname(RUTA_CACHE_IA), exist_ok=True)
        with open(RUTA_CACHE_IA, "w", encoding="utf-8") as f:
            json.dump(cache, f, ensure_ascii=False)
    return datos


# ------------------------------------------------------------------ PLAN
def _fusionar(plan, bruto, cat):
    """Valida lo que devolvió la IA contra los catálogos y lo suma al plan."""
    for a in _lista(bruto.get("anios")):
        try:
            v = cat.resolver_anio(a)
        except ValueError as e:
            _aclarar(plan, str(e), "anios", _cand_anios(cat))
            continue
        if v not in plan["anios"]:
            plan["anios"].append(v)

    for x in _lista(bruto.get("lugares")):
        n_x = " " + re.sub(r"[,;:()\[\]{}¿?¡!\"'.]", " ", normalizar(x)) + " "
        m_estados_de = re.search(_patron_estados_de(cat), n_x)
        if m_estados_de:
            _aclarar_estados_de(plan, cat, cat._estados[m_estados_de.group(1)])
            continue
        masivo = _expandir_masivo(x, cat)
        if masivo:
            _agregar(plan["lugares"], masivo[0])
            if masivo[1] not in plan["notas"]:
                plan["notas"].append(masivo[1])
            continue
        if normalizar(x) == "mexico":
            _aclarar(plan, MENSAJE_MEXICO, "lugares", _cand_mexico(cat))
            continue
        try:
            c = cat.resolver_lugar(x)
        except ValueError as e:
            _aclarar(plan, str(e), "lugares", _cand_lugar(cat, x))
            continue
        if c not in plan["lugares"]:
            plan["lugares"].append(c)

    for v in _lista(bruto.get("variables")):
        clave = str(v).strip().upper()
        if clave in cat.variables:
            if clave not in plan["variables"]:
                plan["variables"].append(clave)
        else:
            plan["avisos"].append(f"La IA propuso la variable '{v}', que no existe; la descarté.")

    for a in _lista(bruto.get("actividades")):
        clave = str(a).strip()
        if clave in cat.actividades:
            if clave not in plan["actividades"]:
                plan["actividades"].append(clave)
        else:
            plan["avisos"].append(f"La IA propuso la actividad '{a}', que no existe; la descarté.")

    for e in _lista(bruto.get("estratos")):
        clave = str(e).strip()
        if clave in cat.estratos:
            if clave not in plan["estratos"]:
                plan["estratos"].append(clave)
        else:
            plan["avisos"].append(f"La IA propuso el estrato '{e}', que no existe; lo descarté.")

    if bruto.get("nota"):
        plan["notas"].append(str(bruto["nota"]))


def interpretar(texto, cat=None, llm=None, usar_cache=True):
    """
    Devuelve un plan: {anios, lugares, variables, actividades, estratos,
    usa_ia, supuestos, avisos, aclarar, notas, faltantes, resumen}.
    El plan está listo para consultar solo si 'faltantes' y 'aclarar' están vacíos.
    """
    cat = cat or Catalogos()
    d = extraer_determinista(texto, cat)
    plan = {"anios": d["anios"], "lugares": d["lugares"], "variables": d["variables"],
            "actividades": [], "estratos": d["estratos"], "usa_ia": False, "supuestos": [],
            "avisos": d["avisos"], "aclarar": d["aclarar"], "opciones": d["opciones"],
            "notas": d["notas"]}

    necesita_ia = bool(d["residuo"]) or not d["variables"] or \
        (not d["lugares"] and not d["aclarar"])
    if necesita_ia:
        try:
            _fusionar(plan, pedir_ia(texto, cat, llm, usar_cache), cat)
            plan["usa_ia"] = True
        except RuntimeError as e:
            # Sin lugar y variables entendidos la IA es indispensable: se informa el error.
            if not (d["lugares"] and d["variables"]):
                raise
            sobran = ", ".join(dict.fromkeys(d["residuo"])) or "(ninguna)"
            plan["aclarar"].append(
                f"No pude usar la IA ({e}) y por reglas no entendí estas palabras: {sobran}. "
                "Reescribe la petición con términos técnicos (claves, nombres de estados) "
                "o intenta de nuevo más tarde.")

    if not plan["anios"] and not plan["aclarar"]:
        ultimo = max(int(a) for a in cat.anios)
        plan["anios"] = [ultimo]
        plan["supuestos"].append(f"No indicaste año; usé {ultimo} (el más reciente).")

    norm = normalizar(texto)
    if (re.search(r"(?<!\w)estratos?(?!\w)", norm) and not plan["estratos"]
            and not d["sin_estratos"]):
        disponibles = ", ".join(f["nombre"] for f in cat.estratos.values())
        _aclarar(plan, "Mencionaste un estrato pero no pude identificar cuál. "
                       f"Los disponibles son: {disponibles}.", "estratos", _cand_estratos(cat))

    if len(plan["lugares"]) > MAX_LUGARES:
        plan["aclarar"].append(f"Pediste {len(plan['lugares'])} lugares; el máximo por "
                               f"consulta es {MAX_LUGARES}. Divide la petición.")

    plan["faltantes"] = []
    if not plan["lugares"] and not plan["aclarar"]:
        plan["faltantes"].append("lugar (nacional, un estado o un municipio)")
    if not plan["variables"]:
        plan["faltantes"].append("variables")

    plan["resumen"] = _resumen(plan, cat)
    return plan


def _resumen(plan, cat):
    lugares = _resumir([f"{cat.nombre_lugar(c)} ({c})" for c in plan["lugares"]]) or ["(falta)"]
    variables = [f"{v} {cat.variables[v]['nombre']}" for v in plan["variables"]] or ["(faltan)"]
    if plan["actividades"]:
        acts = [f"{a} {cat.actividades[a]['nombre']}" for a in plan["actividades"]]
    else:
        acts = [f"todos los sectores ({len(cat.sectores)})"]
    estr = [cat.estratos[e]["nombre"] for e in plan["estratos"]] or ["ninguno"]
    return "\n".join([
        f"  Años:        {plan['anios']}",
        f"  Lugares:     {lugares}",
        f"  Variables:   {variables}",
        f"  Actividades: {acts}",
        f"  Estratos:    {estr}",
        f"  Usó IA:      {'sí' if plan['usa_ia'] else 'no (solo reglas)'}",
    ])


def mostrar_plan(plan):
    print("\nEntendí esto:")
    print(plan["resumen"])
    for titulo, clave in (("Supuestos", "supuestos"), ("Notas", "notas"),
                          ("Avisos", "avisos"), ("Necesito que aclares", "aclarar")):
        for linea in plan[clave]:
            print(f"  {titulo}: {linea}")
    for f in plan["faltantes"]:
        print(f"  Falta: {f}")


# ------------------------------------------------------------------ CONSOLA
if __name__ == "__main__":
    texto = " ".join(sys.argv[1:]).strip() or input("¿Qué datos necesitas? ").strip()
    cat = Catalogos()

    try:
        plan = interpretar(texto, cat)
    except RuntimeError as e:
        print(f"\nNo pude interpretar la petición: {e}")
        sys.exit(1)

    mostrar_plan(plan)
    if plan["faltantes"] or plan["aclarar"]:
        print("\nTodavía no puedo consultar. Reescribe la petición con esos datos.")
        sys.exit(1)

    if not input("\n¿Descargo estos datos? (s/n): ").strip().lower().startswith("s"):
        print("Cancelado.")
        sys.exit(0)

    acts = plan["actividades"] or None
    estr = plan["estratos"] or None
    sesion = crear_sesion()
    df = consultar_saic(plan["anios"], plan["lugares"], plan["variables"], acts, estr,
                        cat=cat, sesion=sesion)
    nombres = [cat.nombre_lugar(c) for c in plan["lugares"]]
    base = "saic_" + nombre_base(plan["anios"], nombres)
    if df.empty:
        print("El SAIC no devolvió datos para esta combinación.")
    else:
        print()
        print(df.to_string(max_colwidth=40))
        df.to_excel(f"{base}.xlsx", index=False)
        df.to_csv(f"{base}.csv", index=False, encoding="utf-8-sig")
        print(f"\nGuardado: {base}.xlsx y {base}.csv")
    try:
        ruta = descargar_excel_oficial(plan["anios"], plan["lugares"], plan["variables"],
                                       acts, estr, ruta=f"SAIC_oficial_{nombre_base(plan['anios'], nombres)}.xlsx",
                                       cat=cat, sesion=sesion)
        print(f"Excel oficial guardado: {ruta}")
    except Exception as e:
        print(f"No pude descargar el Excel oficial: {e}")
