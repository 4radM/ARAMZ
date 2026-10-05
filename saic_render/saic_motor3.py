"""
saic_motor3.py - Motor de consulta al SAIC (INEGI) con catálogos. SIN IA.

Requiere la carpeta "catalogos/" (creada por saic_catalogos.py) junto a este
archivo. Valida años, lugares (nacional, estados y municipios), variables,
actividades y estratos contra los catálogos antes de consultar.

Hace dos cosas:
  1. consultar_saic(...)         -> DataFrame con los datos (y los guarda en xlsx/csv)
  2. descargar_excel_oficial(...) -> el MISMO archivo Excel que entrega el botón
                                     de descarga del SAIC

Uso:
    python3 saic_motor3.py

Cambia ANIOS, LUGARES, VARIABLES, ACTIVIDADES y ESTRATOS en la sección
"CONSULTA DE PRUEBA" al final del archivo.
"""

import base64
import difflib
import json
import os
import re
import unicodedata

import pandas as pd
import requests

AQUI = os.path.dirname(os.path.abspath(__file__))
CARPETA_CAT = os.path.join(AQUI, "catalogos")

URL_TABLA = "https://www.inegi.org.mx/app/api/saic/consulta/tabla/6/"
URL_TOTAL = "https://www.inegi.org.mx/app/api/saic/consulta/total/6/"
URL_EXPORTA = "https://www.inegi.org.mx/app/api/saic/exporta/files/1/6/"
URL_PAGINA = "https://www.inegi.org.mx/app/saic/"
TAM_PAGINA = 10
MAX_PAGINAS = 500

STOP = {"de", "la", "el", "los", "las", "y", "en", "por", "del", "al", "un", "una",
        "para", "con", "total", "millones", "pesos", "dame", "datos"}

# Nombres alternos frecuentes de estados (sin acentos, minúsculas) -> clave
ALIAS_ESTADOS = {
    "nacional": "00", "pais": "00", "mexico nacional": "00",
    "cdmx": "09", "df": "09", "distrito federal": "09",
    "estado de mexico": "15", "edomex": "15",
    "coahuila": "05", "michoacan": "16", "veracruz": "30",
}

# Nombres con los que el SAIC devuelve los campos de cada fila
RENOMBRAR = {"anio": "Año censal", "enti": "Entidad", "actividad": "Actividad económica"}


def normalizar(texto):
    """Minúsculas, sin acentos y sin espacios repetidos."""
    texto = unicodedata.normalize("NFD", str(texto).lower().strip())
    texto = "".join(c for c in texto if unicodedata.category(c) != "Mn")
    return re.sub(r"\s+", " ", texto)


def _lista(x):
    """Convierte un valor suelto en lista (y None en lista vacía)."""
    if x is None:
        return []
    if isinstance(x, (list, tuple, set)):
        return list(x)
    return [x]


def _buscar(items, texto, n, usar_definicion):
    """Búsqueda simple por palabras (prefijo) en nombre y, opcional, definición."""
    tokens = [t for t in normalizar(texto).split() if len(t) > 2 and t not in STOP]
    if not tokens:
        return []
    resultados = []
    for it in items:
        palabras = normalizar(it["nombre"]).split()
        puntaje = sum(3 for t in tokens if any(w.startswith(t) for w in palabras))
        if usar_definicion and it.get("definicion"):
            dpal = normalizar(it["definicion"]).split()
            puntaje += sum(1 for t in tokens if any(w.startswith(t) for w in dpal))
        if puntaje:
            resultados.append((puntaje, it))
    resultados.sort(key=lambda x: (-x[0], x[1]["clave"]))
    return [{"clave": it["clave"], "nombre": it["nombre"], "puntaje": p}
            for p, it in resultados[:n]]


# ------------------------------------------------------------------ CATÁLOGOS
class Catalogos:
    def __init__(self, carpeta=CARPETA_CAT):
        def cargar(nombre):
            ruta = os.path.join(carpeta, f"{nombre}.json")
            if not os.path.exists(ruta):
                raise FileNotFoundError(
                    f"Falta {ruta}. Ejecuta primero saic_catalogos.py "
                    "y deja la carpeta 'catalogos' junto a este archivo.")
            with open(ruta, encoding="utf-8") as f:
                return json.load(f)

        self.anios = [f["clave"] for f in cargar("anios")]

        self.lugares = {f["clave"]: f for f in cargar("entidades")}
        # nombre normalizado -> clave (solo alias cuya clave exista en el catálogo)
        self._estados = {a: c for a, c in ALIAS_ESTADOS.items() if c in self.lugares}
        self._municipios = {}  # nombre normalizado -> [claves]
        for clave, f in self.lugares.items():
            n = normalizar(f["nombre"])
            if f["tipo_lugar"] in ("nacional", "estado"):
                self._estados[n] = clave
            elif f["tipo_lugar"] == "municipio":
                self._municipios.setdefault(n, []).append(clave)

        todas_vars = cargar("variables")
        self.variables = {f["clave"].upper(): f for f in todas_vars if not f["tiene_hijos"]}

        self.actividades = {f["clave"]: f for f in cargar("actividades")}
        self.sectores = [k for k, f in self.actividades.items() if f["nivel"] == 1]

        self.estratos = {f["clave"]: f for f in cargar("estratos")}

    # ---- nombres legibles
    def nombre_lugar(self, clave):
        f = self.lugares[clave]
        if f["tipo_lugar"] == "municipio":
            return f"{f['nombre']}, {self.lugares[f['padre']]['nombre']}"
        return f["nombre"]

    # ---- años
    def resolver_anio(self, anio):
        a = str(anio).strip()
        if a not in self.anios:
            raise ValueError(f"El año {anio} no existe en el SAIC. Disponibles: {self.anios}")
        return int(a)

    # ---- lugares
    def _clave_estado(self, texto):
        n = normalizar(texto)
        if n in self._estados:
            return self._estados[n]
        sug = difflib.get_close_matches(n, list(self._estados), n=3, cutoff=0.6)
        raise ValueError(f"No reconozco el estado '{texto}'. ¿Quisiste decir: {sug}?")

    def resolver_lugar(self, texto):
        """
        Acepta: clave ('19', '19039'), estado ('Nuevo León'), o municipio
        escrito 'Municipio, Estado' ('Monterrey, Nuevo León'). Un nombre suelto
        se busca primero entre estados; si no, entre municipios (y si el nombre
        se repite, falla y te dice cuáles son). Nunca cae al nacional.
        """
        t = str(texto).strip()
        if t in self.lugares:
            return t
        if "," in t:
            mun, est = t.split(",", 1)
            clave_est = self._clave_estado(est)
            cands = [c for c in self._municipios.get(normalizar(mun), [])
                     if self.lugares[c]["padre"] == clave_est]
            if len(cands) == 1:
                return cands[0]
            raise ValueError(f"No encontré el municipio '{mun.strip()}' en '{est.strip()}'.")
        n = normalizar(t)
        if n in self._estados:
            return self._estados[n]
        cands = self._municipios.get(n, [])
        if len(cands) == 1:
            return cands[0]
        if len(cands) > 1:
            op = "; ".join(f"{self.nombre_lugar(c)} ({c})" for c in cands)
            raise ValueError(f"'{texto}' es ambiguo: {op}. "
                             "Escribe 'Municipio, Estado' o usa la clave.")
        todos = list(self._estados) + list(self._municipios)
        sug = difflib.get_close_matches(n, todos, n=3, cutoff=0.6)
        raise ValueError(f"No reconozco el lugar '{texto}'. ¿Quisiste decir: {sug}?")

    # ---- variables
    def resolver_variable(self, codigo):
        c = str(codigo).strip().upper()
        if c in self.variables:
            return c
        sug = [r["clave"] for r in self.buscar_variables(str(codigo), 3)]
        raise ValueError(f"La variable '{codigo}' no existe en el catálogo. Cercanas: {sug}")

    def buscar_variables(self, texto, n=8):
        return _buscar(self.variables.values(), texto, n, usar_definicion=True)

    # ---- actividades
    def resolver_actividad(self, codigo):
        c = str(codigo).strip()
        if c in self.actividades:
            return c
        sug = [r["clave"] for r in self.buscar_actividades(c, 3)]
        raise ValueError(f"La actividad '{codigo}' no existe en el catálogo. Cercanas: {sug}")

    def buscar_actividades(self, texto, n=8):
        return _buscar(self.actividades.values(), texto, n, usar_definicion=False)

    # ---- estratos
    def resolver_estrato(self, valor):
        v = str(valor).strip()
        if v in self.estratos:
            return v
        raise ValueError(f"Estrato '{valor}' no válido. Disponibles: "
                         f"{ {k: f['nombre'] for k, f in self.estratos.items()} }")


# ------------------------------------------------------------------ SAIC
def validar_consulta(cat, anios, lugares, variables, actividades, estratos):
    """Valida todo contra los catálogos y devuelve las listas ya resueltas."""
    anios_ok = [cat.resolver_anio(a) for a in _lista(anios)]
    lugares_ok = [cat.resolver_lugar(x) for x in _lista(lugares)]
    vars_ok = [cat.resolver_variable(v) for v in _lista(variables)]
    acts_ok = ([cat.resolver_actividad(a) for a in _lista(actividades)]
               if actividades else list(cat.sectores))
    estr_ok = [cat.resolver_estrato(e) for e in _lista(estratos)]
    if not anios_ok or not lugares_ok or not vars_ok:
        raise ValueError("Indica al menos un año, un lugar y una variable.")

    print("Consulta validada:")
    print("  años:       ", anios_ok)
    print("  lugares:    ", [f"{cat.nombre_lugar(c)} ({c})" for c in lugares_ok])
    print("  variables:  ", [f"{v} {cat.variables[v]['nombre']}" for v in vars_ok])
    print("  actividades:", len(acts_ok), "| estratos:", estr_ok or "ninguno")
    return anios_ok, lugares_ok, vars_ok, acts_ok, estr_ok


def armar_payload(anios, claves_lugares, variables, actecos, estratos, pagina, reg=TAM_PAGINA):
    return {
        "anios": anios,
        "ageos": claves_lugares,
        "actecos": actecos,
        "varcens": [{"nom": v, "pos": i} for i, v in enumerate(variables)],
        "stratums": estratos,
        "indicators": [],
        "calcs": [],
        "total": False,
        "orden": "1",
        "desc": True,
        "page": pagina,
        "reg": reg,
    }


def parsear_respuesta(cuerpo):
    """
    La respuesta trae un JSON dentro de otro JSON: hay que abrir 'data'.
    Conserva TODOS los campos de cada fila (por si el SAIC agrega, por ejemplo,
    un campo de municipio) y renombra los tres conocidos.
    """
    if not cuerpo.get("success"):
        raise RuntimeError(f"El SAIC respondió sin éxito: {cuerpo}")
    info = json.loads(cuerpo["data"]).get("info", [])
    filas = []
    for item in info:
        fila = {}
        for k, v in item.items():
            if k == "zxc":
                continue
            fila[RENOMBRAR.get(k, k)] = v
        for bloque in item.get("zxc", []):
            fila.update(bloque)
        filas.append(fila)
    return filas


def crear_sesion():
    sesion = requests.Session()
    sesion.headers.update({
        "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                      "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120 Safari/537.36",
        "Accept": "application/json, text/plain, */*",
        "Content-Type": "application/json",
        "Origin": "https://www.inegi.org.mx",
        "Referer": URL_PAGINA,
    })
    sesion.get(URL_PAGINA, timeout=30)
    return sesion


def contar_filas(sesion, anios, claves_lugares, actecos, estratos):
    """
    Pregunta al SAIC cuántas filas tendrá la consulta (None si no se pudo).
    Usa el mismo formato que el navegador ("total": False).
    """
    payload = {
        "anios": anios, "ageos": claves_lugares, "actecos": actecos,
        "stratums": estratos, "varcens": None, "calcs": None,
        "total": False, "orden": None, "desc": False, "page": 0, "reg": 0,
    }
    try:
        resp = sesion.post(URL_TOTAL, json=payload, timeout=60)
        resp.raise_for_status()
        return int(resp.json()["info"][0]["total"])
    except Exception:
        return None


def consultar_saic(anios, lugares, variables, actividades=None, estratos=None,
                   cat=None, sesion=None, verificar=True):
    """
    anios: 2023 o [2023, 2018]      lugares: 'Nuevo León' o ['Monterrey, Nuevo León']
    variables: ['H001A', 'A131A']   actividades: None = los sectores principales
    estratos: None = ninguna casilla marcada
    Devuelve un DataFrame (vacío si el SAIC no tiene datos). Las celdas que el
    INEGI omite por confidencialidad quedan como NaN (vacías), nunca como cero.
    """
    cat = cat or Catalogos()
    anios_ok, lugares_ok, vars_ok, acts_ok, estr_ok = validar_consulta(
        cat, anios, lugares, variables, actividades, estratos)

    sesion = sesion or crear_sesion()

    esperadas = contar_filas(sesion, anios_ok, lugares_ok, acts_ok, estr_ok) if verificar else None
    if verificar:
        print("  filas según el SAIC:", esperadas if esperadas is not None else "(no pude verificar)")

    todas, primera_anterior = [], None
    for pagina in range(MAX_PAGINAS):
        payload = armar_payload(anios_ok, lugares_ok, vars_ok, acts_ok, estr_ok, pagina)
        resp = sesion.post(URL_TABLA, json=payload, timeout=60)
        if resp.status_code != 200:
            raise RuntimeError(f"HTTP {resp.status_code}: {resp.text[:500]}")
        filas = parsear_respuesta(resp.json())
        if not filas:
            break
        if primera_anterior is not None and filas[0] == primera_anterior:
            break
        primera_anterior = filas[0]
        todas.extend(filas)
        if len(filas) < TAM_PAGINA:
            break
        if esperadas is not None and len(todas) >= esperadas:
            break

    df = pd.DataFrame(todas)
    if esperadas is not None and len(df) != esperadas:
        print(f"AVISO: el SAIC reporta {esperadas} filas y recibí {len(df)}.")
    elif esperadas is not None:
        print(f"Verificación correcta: {len(df)} filas completas.")
    return df


def descargar_excel_oficial(anios, lugares, variables, actividades=None, estratos=None,
                            ruta=None, cat=None, sesion=None):
    """
    Descarga el archivo Excel oficial del SAIC (el del botón de descarga).
    El servidor lo entrega como texto base64 dentro de la respuesta.
    Devuelve la ruta del archivo guardado.
    """
    cat = cat or Catalogos()
    anios_ok, lugares_ok, vars_ok, acts_ok, estr_ok = validar_consulta(
        cat, anios, lugares, variables, actividades, estratos)
    sesion = sesion or crear_sesion()

    payload = armar_payload(anios_ok, lugares_ok, vars_ok, acts_ok, estr_ok, 0, reg=0)
    resp = sesion.post(URL_EXPORTA, json=payload, timeout=120)
    if resp.status_code != 200:
        raise RuntimeError(f"HTTP {resp.status_code}: {resp.text[:500]}")

    texto = resp.text.strip()
    if texto.startswith('"'):
        texto = json.loads(texto)  # viene como texto JSON entre comillas
    try:
        datos = base64.b64decode(texto, validate=True)
    except Exception:
        raise RuntimeError(f"La respuesta no es un archivo base64: {resp.text[:300]}")
    if not datos.startswith(b"PK"):  # los .xlsx son archivos zip
        raise RuntimeError(f"La respuesta no parece un archivo Excel: {resp.text[:300]}")

    ruta = ruta or f"SAIC_oficial_{nombre_base(anios, lugares)}.xlsx"
    with open(ruta, "wb") as f:
        f.write(datos)
    return ruta


def nombre_base(anios, lugares):
    base = "-".join(str(a) for a in _lista(anios)) + "_"
    ls = _lista(lugares)
    if len(ls) == 1:
        base += normalizar(ls[0]).replace(", ", "_").replace(" ", "_")
    else:
        base += "varios"
    return base


# ------------------------------------------------------------------ CONSULTA DE PRUEBA
if __name__ == "__main__":
    ANIOS = [2023]
    LUGARES = ["Monterrey, Nuevo León"]   # prueba también "Monterrey, Nuevo León"
    VARIABLES = ["H001A", "A111A"]
    ACTIVIDADES = None   # None = los sectores principales; o una lista, ej. ["112"]
    ESTRATOS = None      # None = ninguna casilla marcada

    df = consultar_saic(ANIOS, LUGARES, VARIABLES, ACTIVIDADES, ESTRATOS)

    if df.empty:
        print("El SAIC no devolvió datos para esta combinación.")
    else:
        print("\nColumnas recibidas:", list(df.columns))
        print()
        print(df.to_string(max_colwidth=40))
        base = "saic_" + nombre_base(ANIOS, LUGARES)
        df.to_excel(f"{base}.xlsx", index=False)
        df.to_csv(f"{base}.csv", index=False, encoding="utf-8-sig")
        print(f"\nGuardado: {base}.xlsx y {base}.csv")

    print("\nDescargando el Excel oficial del SAIC...")
    try:
        ruta = descargar_excel_oficial(ANIOS, LUGARES, VARIABLES, ACTIVIDADES, ESTRATOS)
        print(f"Excel oficial guardado: {ruta}")
    except Exception as e:
        print(f"No pude descargar el Excel oficial: {e}")
