"""
app8.py - Página web para consultar el SAIC (INEGI) en lenguaje natural (versión para pruebas con testers).

Requiere, en la MISMA carpeta: saic_motor3.py, saic_interprete7.py y catalogos/
Instalación (una sola vez):   pip3 install flask
Uso:                          python3 app8.py
Luego abre en el navegador:   http://127.0.0.1:8000

La clave de Gemini se lee de la variable de entorno GEMINI_API_KEY y vive solo
en este servidor: nunca llega al navegador.

Para compartirla con testers define un código de acceso (si no lo defines, la
página queda abierta y debes usarla solo en tu computadora):
    export CODIGO_ACCESO="el-codigo-que-les-des"

Se crea la carpeta "registro/" con dos archivos que puedes revisar:
    uso.jsonl        qué piden los testers y si funcionó
    reportes.jsonl   lo que reportan con el botón "Reportar un problema"
"""

import contextlib
import hashlib
import hmac
import io
import json
import os
import secrets
import tempfile
import threading
import time
import traceback
from datetime import timedelta

import pandas as pd
import requests
from datetime import date

from flask import Flask, Response, g, jsonify, request, send_file, session

from saic_interprete7 import MAX_LUGARES, _resumir, interpretar, llm_gemini
from saic_motor3 import (URL_PAGINA, Catalogos, consultar_saic, contar_filas, crear_sesion,
                         descargar_excel_oficial, nombre_base, validar_consulta)

# ------------------------------------------------------------------ LÍMITES
LIMITE_IA_DIARIO = 15       # llamadas a Gemini por día (el plan gratuito da ~20)
MAX_FILAS_VISTA = 300       # filas máximas para mostrar la tabla en la página
MAX_FILAS_DESCARGA = 20000  # filas máximas para el Excel oficial
MAX_TEXTO = 500             # caracteres máximos de la petición
VENTANA_SEG = 60            # ventana del límite por visitante
MAX_POR_VENTANA = 20        # solicitudes por visitante en esa ventana

CODIGO_ACCESO = os.environ.get("CODIGO_ACCESO", "").strip()
CARPETA_REGISTRO = os.path.join(os.path.dirname(os.path.abspath(__file__)), "registro")
MAX_INTENTOS_CODIGO = 8     # intentos de código por visitante...
VENTANA_CODIGO_SEG = 600    # ...cada 10 minutos

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY") or secrets.token_hex(32)
app.config.update(SESSION_COOKIE_HTTPONLY=True, SESSION_COOKIE_SAMESITE="Lax",
                  PERMANENT_SESSION_LIFETIME=timedelta(hours=12))
CAT = Catalogos()
_candado = threading.Lock()
ECO_REGISTRO = bool(os.environ.get("RENDER") or os.environ.get("ECO_REGISTRO"))


def huella_codigo():
    """Marca de la sesión: si cambias el código, las sesiones anteriores dejan de valer."""
    return hashlib.sha256(("saic|" + CODIGO_ACCESO).encode()).hexdigest()[:16]


def sesion_valida():
    return (not CODIGO_ACCESO) or session.get("ok") == huella_codigo()
_intentos = {}

_ia = {"fecha": None, "n": 0}
_visitas = {}


# ------------------------------------------------------------------ UTILIDADES
def ip_visitante():
    """IP real del visitante (detrás de un túnel llega en una cabecera)."""
    return (request.headers.get("CF-Connecting-IP")
            or request.headers.get("X-Forwarded-For", "").split(",")[0].strip()
            or request.remote_addr or "?")


def visitante_id():
    """Identificador corto y anónimo (no se guarda la IP)."""
    return hashlib.sha256(("saic-" + ip_visitante()).encode()).hexdigest()[:10]


def registrar(archivo, datos):
    """Agrega una línea JSON al archivo de registro. Devuelve True si se guardó."""
    try:
        os.makedirs(CARPETA_REGISTRO, exist_ok=True)
        linea = {"hora": time.strftime("%Y-%m-%d %H:%M:%S"), "visitante": visitante_id(), **datos}
        with _candado, open(os.path.join(CARPETA_REGISTRO, archivo), "a", encoding="utf-8") as f:
            f.write(json.dumps(linea, ensure_ascii=False) + "\n")
        if ECO_REGISTRO:
            print(f"[REGISTRO {archivo}] " + json.dumps(linea, ensure_ascii=False), flush=True)
        return True
    except Exception:
        return False


def permitir_intento_codigo():
    ip = ip_visitante()
    ahora = time.time()
    recientes = [t for t in _intentos.get(ip, []) if ahora - t < VENTANA_CODIGO_SEG]
    if len(recientes) >= MAX_INTENTOS_CODIGO:
        return False
    recientes.append(ahora)
    _intentos[ip] = recientes
    return True


def permitir_visita():
    ip = ip_visitante()
    ahora = time.time()
    recientes = [t for t in _visitas.get(ip, []) if ahora - t < VENTANA_SEG]
    if len(recientes) >= MAX_POR_VENTANA:
        return False
    recientes.append(ahora)
    _visitas[ip] = recientes
    return True


def silencioso(funcion, *args, **kwargs):
    """Ejecuta una función del motor sin llenar la Terminal de mensajes."""
    with contextlib.redirect_stdout(io.StringIO()):
        return funcion(*args, **kwargs)


def llm_limitado(prompt):
    """Gemini con tope diario (las respuestas en caché no llegan aquí)."""
    hoy = date.today().isoformat()
    if _ia["fecha"] != hoy:
        _ia["fecha"], _ia["n"] = hoy, 0
    if _ia["n"] >= LIMITE_IA_DIARIO:
        raise RuntimeError("Se alcanzó el límite diario de consultas con IA. "
                           "Intenta mañana o escribe la petición con claves "
                           "explícitas (por ejemplo: 2008, Nuevo León, K000A).")
    texto = llm_gemini(prompt)
    _ia["n"] += 1  # solo cuentan las llamadas que sí se completaron
    return texto


def plan_publico(plan):
    """Plan listo para mostrar en la página (con nombres legibles)."""
    if plan.get("solo_total"):
        acts = ["Solo el total (sin desglose por sector)"]
    elif plan["actividades"]:
        acts = [f"{a} {CAT.actividades[a]['nombre']}" for a in plan["actividades"]]
    else:
        acts = [f"Todos los sectores ({len(CAT.sectores)})"]
    if plan.get("con_total") and not plan.get("solo_total"):
        acts = acts + ["+ fila de total"]
    return {
        "anios": plan["anios"],
        "lugares": plan["lugares"],
        "variables": plan["variables"],
        "actividades": plan["actividades"],
        "estratos": plan["estratos"],
        "solo_total": bool(plan.get("solo_total")),
        "con_total": bool(plan.get("con_total")),
        "anios_txt": [str(a) for a in plan["anios"]],
        "lugares_txt": _resumir([f"{CAT.nombre_lugar(c)} ({c})" for c in plan["lugares"]]),
        "variables_txt": [f"{v} {CAT.variables[v]['nombre']}" for v in plan["variables"]],
        "actividades_txt": acts,
        "estratos_txt": [CAT.estratos[e]["nombre"] for e in plan["estratos"]] or ["Ninguno"],
        "usa_ia": plan["usa_ia"],
        "supuestos": plan["supuestos"],
        "notas": plan["notas"],
        "avisos": plan["avisos"],
        "aclarar": plan["aclarar"],
        "opciones": plan["opciones"],
        "faltantes": plan["faltantes"],
        "listo": not plan["faltantes"] and not plan["aclarar"],
    }


def parametros(cuerpo):
    """Lee y revisa el plan que manda la página (nunca se confía en él a ciegas)."""
    plan = cuerpo.get("plan") if isinstance(cuerpo, dict) else None
    if not isinstance(plan, dict):
        raise ValueError("Falta el plan de consulta.")
    datos = {}
    for clave in ("anios", "lugares", "variables", "actividades", "estratos"):
        valor = plan.get(clave) or []
        tope = MAX_LUGARES if clave == "lugares" else 50
        if not isinstance(valor, list) or len(valor) > tope:
            raise ValueError(f"El campo '{clave}' no es válido.")
        datos[clave] = valor
    for clave in ("anios", "lugares", "variables"):
        if not datos[clave]:
            raise ValueError(f"La consulta no tiene {clave}.")
    solo_total = bool(plan.get("solo_total"))
    con_total = bool(plan.get("con_total"))
    return (datos["anios"], datos["lugares"], datos["variables"],
            None if solo_total else (datos["actividades"] or None),
            datos["estratos"] or None, solo_total, con_total)


def responder_error(e):
    if isinstance(e, ValueError):
        return jsonify(error=str(e)), 400
    if isinstance(e, RuntimeError):
        return jsonify(error=str(e)), 502
    traceback.print_exc()
    return jsonify(error="Ocurrió un error inesperado. Intenta de nuevo."), 500


# ------------------------------------------------------------------ ACCESO Y REGISTRO
RUTAS_CON_PLAN = ("/api/consultar", "/api/descargar", "/api/descargar_csv")


@app.before_request
def exigir_acceso():
    """Con CODIGO_ACCESO definido, la API exige haber entrado con el código."""
    if not CODIGO_ACCESO:
        return None
    if request.path in ("/", "/api/estado", "/api/acceso"):
        return None
    if request.path.startswith("/api/") and not sesion_valida():
        return jsonify(error="Se requiere el código de acceso.", acceso=True), 401
    return None


@app.after_request
def registrar_uso(resp):
    """Deja una línea por cada llamada a la API (sin guardar códigos ni IP)."""
    try:
        if request.path.startswith("/api/") and request.path != "/api/estado":
            info = {"evento": request.path[len("/api/"):], "estado": resp.status_code}
            info.update(getattr(g, "info", {}))
            if request.path in RUTAS_CON_PLAN:
                plan = (request.get_json(silent=True) or {}).get("plan") or {}
                info.update(anios=plan.get("anios"), variables=plan.get("variables"),
                            n_lugares=len(plan.get("lugares") or []))
            if resp.status_code >= 400 and resp.is_json:
                info["error"] = str((resp.get_json(silent=True) or {}).get("error", ""))[:300]
            if request.path != "/api/reportar":
                registrar("uso.jsonl", info)
    except Exception:
        pass
    return resp


# ------------------------------------------------------------------ RUTAS
@app.get("/")
def inicio():
    return Response(PAGINA, mimetype="text/html")


@app.get("/api/estado")
def api_estado():
    return jsonify(requiere_codigo=bool(CODIGO_ACCESO),
                   autenticado=sesion_valida())


@app.get("/api/diagnostico")
def api_diagnostico():
    """Comprueba desde ESTE servidor si el INEGI responde (útil al publicar en la nube)."""
    if not permitir_visita():
        return jsonify(error="Demasiadas solicitudes. Espera un minuto."), 429
    resultado = {
        "gemini_clave_definida": bool(os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY")),
        "catalogos": {"lugares": len(CAT.lugares), "variables": len(CAT.variables),
                      "actividades": len(CAT.actividades)},
    }
    inicio = time.time()
    try:
        r = requests.get(URL_PAGINA, timeout=30, headers={"User-Agent": "Mozilla/5.0"})
        resultado["inegi_pagina_http"] = r.status_code
        filas = contar_filas(crear_sesion(), [2023], ["08"], list(CAT.sectores), [])
        resultado["inegi_filas_chihuahua_2023"] = filas
        resultado["inegi_consulta"] = ("ok" if filas == len(CAT.sectores)
                                       else "respuesta inesperada o bloqueada")
    except Exception as e:
        resultado["inegi_error"] = str(e)[:300]
    resultado["segundos"] = round(time.time() - inicio, 1)
    return jsonify(resultado)


@app.post("/api/acceso")
def api_acceso():
    if not CODIGO_ACCESO:
        return jsonify(ok=True)
    if not permitir_intento_codigo():
        return jsonify(error="Demasiados intentos. Espera unos minutos."), 429
    codigo = str((request.get_json(silent=True) or {}).get("codigo", ""))
    if hmac.compare_digest(codigo.encode(), CODIGO_ACCESO.encode()):
        session["ok"] = huella_codigo()
        session.permanent = True
        return jsonify(ok=True)
    return jsonify(error="Código incorrecto."), 401


@app.post("/api/reportar")
def api_reportar():
    if not permitir_visita():
        return jsonify(error="Demasiadas solicitudes. Espera un minuto."), 429
    try:
        cuerpo = request.get_json(silent=True) or {}
        comentario = str(cuerpo.get("comentario", "")).strip()
        if not comentario:
            raise ValueError("Escribe qué pasó.")
        if len(comentario) > 1000:
            raise ValueError("El comentario es muy largo (máximo 1000 caracteres).")
        tipo = cuerpo.get("tipo") if cuerpo.get("tipo") in ("error", "sugerencia", "otro") else "otro"
        plan = cuerpo.get("plan") if isinstance(cuerpo.get("plan"), dict) else None
        plan_corto = None
        if plan:
            plan_corto = {k: (plan.get(k) if isinstance(plan.get(k), list) else [])[:20]
                          for k in ("anios", "lugares", "variables", "actividades", "estratos")}
        guardado = registrar("reportes.jsonl", {
            "tipo": tipo, "comentario": comentario,
            "texto": str(cuerpo.get("texto", ""))[:MAX_TEXTO], "plan": plan_corto})
        if not guardado:
            raise RuntimeError("No pude guardar el reporte. Intenta de nuevo.")
        return jsonify(ok=True)
    except Exception as e:
        return responder_error(e)


@app.post("/api/interpretar")
def api_interpretar():
    if not permitir_visita():
        return jsonify(error="Demasiadas solicitudes. Espera un minuto."), 429
    try:
        texto = str((request.get_json(silent=True) or {}).get("texto", "")).strip()
        if not texto:
            raise ValueError("Escribe qué datos necesitas.")
        if len(texto) > MAX_TEXTO:
            raise ValueError(f"La petición es muy larga (máximo {MAX_TEXTO} caracteres).")
        publico = plan_publico(interpretar(texto, CAT, llm=llm_limitado))
        g.info = {"texto": texto, "usa_ia": publico["usa_ia"], "listo": publico["listo"],
                  "n_aclarar": len(publico["aclarar"]), "n_lugares": len(publico["lugares"]),
                  "variables": publico["variables"]}
        return jsonify(publico)
    except Exception as e:
        return responder_error(e)


@app.post("/api/consultar")
def api_consultar():
    if not permitir_visita():
        return jsonify(error="Demasiadas solicitudes. Espera un minuto."), 429
    try:
        anios, lugares, variables, acts, estr, solo_total, con_total = parametros(
            request.get_json(silent=True))
        a_ok, l_ok, v_ok, ac_ok, e_ok = silencioso(
            validar_consulta, CAT, anios, lugares, variables, acts, estr, solo_total=solo_total)
        sesion = crear_sesion()
        total = contar_filas(sesion, a_ok, l_ok, ac_ok, e_ok, total=(solo_total or con_total))
        if total is not None and total > MAX_FILAS_VISTA:
            return jsonify(ok=True, demasiado_grande=True, filas=total)
        df = silencioso(consultar_saic, anios, lugares, variables, acts, estr,
                        cat=CAT, sesion=sesion, verificar=False,
                        solo_total=solo_total, con_total=con_total)
        if df.empty:
            return jsonify(ok=True, vacio=True, columnas=[], filas=[])
        df = df.rename(columns={"muni": "Municipio"})
        tabla = json.loads(df.to_json(orient="split", force_ascii=False))
        return jsonify(ok=True, columnas=tabla["columns"], filas=tabla["data"])
    except Exception as e:
        return responder_error(e)


def obtener_excel_oficial(cuerpo):
    """Descarga el Excel oficial del SAIC. Devuelve (bytes, base_del_nombre)."""
    anios, lugares, variables, acts, estr, solo_total, con_total = parametros(cuerpo)
    a_ok, l_ok, v_ok, ac_ok, e_ok = silencioso(
        validar_consulta, CAT, anios, lugares, variables, acts, estr, solo_total=solo_total)
    sesion = crear_sesion()
    total = contar_filas(sesion, a_ok, l_ok, ac_ok, e_ok, total=(solo_total or con_total))
    if total is not None and total > MAX_FILAS_DESCARGA:
        raise ValueError(f"La consulta tiene {total} filas; el máximo permitido es "
                         f"{MAX_FILAS_DESCARGA}. Reduce años, lugares o actividades.")
    with tempfile.TemporaryDirectory() as tmp:
        ruta = os.path.join(tmp, "oficial.xlsx")
        silencioso(descargar_excel_oficial, anios, lugares, variables, acts, estr,
                   ruta=ruta, cat=CAT, sesion=sesion,
                   solo_total=solo_total, con_total=con_total)
        with open(ruta, "rb") as f:
            contenido = f.read()
    nombres = [CAT.nombre_lugar(c) for c in l_ok]
    return contenido, nombre_base(a_ok, nombres)


def excel_oficial_a_csv(contenido):
    """
    Convierte el Excel oficial del SAIC en CSV. El archivo trae encabezados
    institucionales, los nombres de columna en la fila 5, los datos y al final
    una nota de confidencialidad. Las celdas reservadas quedan vacías.
    """
    try:
        df = pd.read_excel(io.BytesIO(contenido), header=4)
    except Exception:
        raise RuntimeError("No pude leer el Excel oficial para convertirlo a CSV.")
    if df.shape[1] < 3 or not str(df.columns[0]).strip().lower().startswith("año"):
        raise RuntimeError("El Excel oficial tiene un formato distinto al esperado; "
                           "descarga el Excel oficial en su lugar.")
    primera = df.columns[0]
    df = df[pd.to_numeric(df[primera], errors="coerce").notna()].copy()
    df[primera] = pd.to_numeric(df[primera]).astype(int)
    for col in df.columns[1:]:
        if pd.api.types.is_float_dtype(df[col]):
            sin_vacios = df[col].dropna()
            if len(sin_vacios) and (sin_vacios % 1 == 0).all():
                df[col] = df[col].astype("Int64")  # sin ".0" en los conteos
    return df.to_csv(index=False)


@app.post("/api/descargar")
def api_descargar():
    if not permitir_visita():
        return jsonify(error="Demasiadas solicitudes. Espera un minuto."), 429
    try:
        contenido, base = obtener_excel_oficial(request.get_json(silent=True))
        return send_file(io.BytesIO(contenido), as_attachment=True,
                         download_name=f"SAIC_oficial_{base}.xlsx",
                         mimetype="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
    except Exception as e:
        return responder_error(e)


@app.post("/api/descargar_csv")
def api_descargar_csv():
    if not permitir_visita():
        return jsonify(error="Demasiadas solicitudes. Espera un minuto."), 429
    try:
        contenido, base = obtener_excel_oficial(request.get_json(silent=True))
        texto = excel_oficial_a_csv(contenido)
        return send_file(io.BytesIO(texto.encode("utf-8-sig")), as_attachment=True,
                         download_name=f"SAIC_{base}.csv", mimetype="text/csv")
    except Exception as e:
        return responder_error(e)


# ------------------------------------------------------------------ PÁGINA
PAGINA = r"""<!doctype html>
<html lang="es">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Consulta SAIC en lenguaje natural</title>
<style>
  :root { --borde:#d5dbe1; --suave:#f5f7f9; --azul:#1e5aa8; --rojo:#b3261e; --ambar:#8a5a00; }
  body { font-family:-apple-system,"Segoe UI",Roboto,sans-serif; max-width:960px; margin:2rem auto;
         padding:0 1rem; color:#1f2933; line-height:1.5; }
  h1 { font-size:1.6rem; margin-bottom:.2rem; }
  .sub { color:#52606d; margin-top:0; }
  textarea { width:100%; box-sizing:border-box; padding:.7rem; font:inherit; border:1px solid var(--borde);
             border-radius:8px; resize:vertical; }
  button { font:inherit; padding:.55rem 1rem; border-radius:8px; border:1px solid var(--azul);
           background:var(--azul); color:#fff; cursor:pointer; }
  button.sec { background:#fff; color:var(--azul); }
  button:disabled { opacity:.5; cursor:not-allowed; }
  .ejemplos { margin:.5rem 0 1rem; font-size:.9rem; color:#52606d; }
  .ejemplos a { color:var(--azul); cursor:pointer; margin-right:.8rem; text-decoration:underline; }
  .tarjeta { border:1px solid var(--borde); border-radius:10px; padding:1rem; margin-top:1rem; background:var(--suave); }
  .tarjeta p { margin:.25rem 0; }
  .msg { padding:.5rem .7rem; border-radius:8px; margin:.4rem 0; font-size:.95rem; }
  .nota { background:#eaf2fb; } .aviso { background:#fff4e0; color:var(--ambar); }
  .error { background:#fdeceb; color:var(--rojo); }
  .acciones { margin-top:.8rem; display:flex; gap:.6rem; flex-wrap:wrap; }
  #estado { margin-top:.8rem; min-height:1.4rem; color:#52606d; }
  #estado.error { color:var(--rojo); }
  .contenedor-tabla { overflow-x:auto; margin-top:1rem; }
  table { border-collapse:collapse; width:100%; font-size:.9rem; }
  th, td { border:1px solid var(--borde); padding:.35rem .5rem; text-align:left; }
  th { background:var(--suave); } td.num { text-align:right; font-variant-numeric:tabular-nums; }
  footer { margin-top:2.5rem; font-size:.85rem; color:#52606d; border-top:1px solid var(--borde); padding-top:.8rem; }
  .badge { display:inline-block; font-size:.8rem; padding:.1rem .6rem; border-radius:999px; margin-left:.5rem; vertical-align:middle; }
  .badge.reglas { background:#e3f4e8; color:#1d6b3a; }
  .badge.ia { background:#fff4e0; color:var(--ambar); }
  .opciones { margin:.2rem 0 .7rem; display:flex; gap:.4rem; flex-wrap:wrap; }
  .opciones button { background:#fff; color:var(--azul); padding:.35rem .7rem; font-size:.9rem; }
  input[type=password], select { font:inherit; padding:.5rem .7rem; border:1px solid var(--borde); border-radius:8px; }
  #acceso { max-width:26rem; margin:3rem auto; }
  #errorAcceso, #estadoReporte { margin-top:.5rem; color:var(--rojo); min-height:1.2rem; }
  #abrirReporte { cursor:pointer; text-decoration:underline; color:var(--azul); }
  .fila { display:flex; gap:.6rem; flex-wrap:wrap; align-items:center; margin:.5rem 0; }
  .controles { display:flex; gap:.8rem; flex-wrap:wrap; align-items:center; margin:.6rem 0; }
  .fuente { font-size:.85rem; color:#52606d; }
</style>
</head>
<body>
<h1>Consulta SAIC en lenguaje natural</h1>
<p class="sub">Pide datos de los Censos Económicos (SAIC del INEGI) con tus propias palabras.</p>

<div id="acceso" class="tarjeta" hidden>
  <strong>Esta página es solo para personas invitadas</strong>
  <p>Escribe el código de acceso que te dieron.</p>
  <div class="fila"><input type="password" id="codigo" placeholder="Código de acceso" autocomplete="off">
    <button id="entrar">Entrar</button></div>
  <div id="errorAcceso"></div>
</div>

<div id="principal" hidden>
<textarea id="texto" rows="3" maxlength="500"
  placeholder="Ej.: gastos por consumo de las manufacturas en Monterrey en 2018"></textarea>
<div class="ejemplos">Ejemplos:
  <a data-ej="Dame del año censal 2008, de Nuevo León, de todos los sectores, variables K000A e I000A">2008 · Nuevo León · K000A e I000A</a>
  <a data-ej="variables relacionadas con el PIB de Chihuahua en 2023">PIB · Chihuahua · 2023</a>
  <a data-ej="gastos por consumo de las manufacturas en Monterrey en 2018">Manufacturas · Monterrey · 2018</a>
  <a data-ej="compara el personal ocupado de Chihuahua y Sonora en 2018 y 2023">Comparar · Chihuahua y Sonora</a>
  <a data-ej="evolución del personal ocupado en Chihuahua entre 2003 y 2023">Evolución · Chihuahua 2003-2023</a>
</div>
<button id="btnInterpretar">Interpretar</button>
<div id="estado"></div>

<div id="plan" class="tarjeta" hidden></div>
<div id="tabla"></div>
<div id="grafica"></div>

<div id="reporte" class="tarjeta" hidden>
  <strong>Reportar un problema o sugerencia</strong>
  <p>Se guardará junto con lo último que escribiste y lo que la página entendió.</p>
  <div class="fila"><select id="tipoReporte">
    <option value="error">Algo salió mal</option><option value="sugerencia">Sugerencia</option>
    <option value="otro">Otro</option></select></div>
  <textarea id="comentario" rows="3" maxlength="1000" placeholder="Cuéntame qué pasó o qué esperabas ver"></textarea>
  <div class="fila"><button id="enviarReporte">Enviar reporte</button>
    <button id="cerrarReporte" class="sec">Cerrar</button></div>
  <div id="estadoReporte"></div>
</div>
</div>

<footer>
  Fuente: INEGI, Censos Económicos 2024 (SAIC). Este sitio es independiente: no está afiliado al INEGI ni cuenta con su respaldo oficial. La interpretación de las peticiones la hace este sitio y puede equivocarse; revisa el resumen antes de usar los datos.
  Las celdas vacías (—) son datos que el INEGI omite por confidencialidad y reserva, no son ceros.
  <br>Para mejorar el servicio se guarda lo que escribes (sin tu nombre ni datos personales).
  <a id="abrirReporte" hidden>Reportar un problema</a>
</footer>

<script>
const $ = id => document.getElementById(id);
let planActual = null;

function vaciar(el) { while (el.firstChild) el.removeChild(el.firstChild); }
function estado(texto, esError) { const e = $('estado'); e.textContent = texto || ''; e.className = esError ? 'error' : ''; }
async function post(url, cuerpo) {
  const r = await fetch(url, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(cuerpo) });
  if (r.status === 401 && url !== '/api/acceso') mostrarAcceso();
  return r;
}
function mostrarAcceso() { $('principal').hidden = true; $('abrirReporte').hidden = true; $('acceso').hidden = false; $('codigo').focus(); }
function mostrarPrincipal() { $('acceso').hidden = true; $('principal').hidden = false; $('abrirReporte').hidden = false; }
async function entrar() {
  const r = await post('/api/acceso', { codigo: $('codigo').value });
  const d = await r.json().catch(() => ({}));
  if (r.ok) { $('codigo').value = ''; $('errorAcceso').textContent = ''; mostrarPrincipal(); }
  else { $('errorAcceso').textContent = d.error || 'Código incorrecto.'; }
}
async function enviarReporte() {
  const comentario = $('comentario').value.trim();
  if (!comentario) { $('estadoReporte').textContent = 'Escribe qué pasó.'; return; }
  const p = planActual ? { anios: planActual.anios, lugares: planActual.lugares, variables: planActual.variables,
    actividades: planActual.actividades, estratos: planActual.estratos } : null;
  const r = await post('/api/reportar', { comentario, tipo: $('tipoReporte').value, texto: $('texto').value, plan: p });
  const d = await r.json().catch(() => ({}));
  if (r.ok) { $('estadoReporte').style.color = '#1d6b3a'; $('estadoReporte').textContent = '¡Gracias! Tu reporte se guardó.'; $('comentario').value = ''; }
  else { $('estadoReporte').style.color = ''; $('estadoReporte').textContent = d.error || 'No pude guardar el reporte.'; }
}
function linea(padre, etiqueta, valores) {
  const p = document.createElement('p'), b = document.createElement('strong');
  b.textContent = etiqueta + ': '; p.appendChild(b);
  p.appendChild(document.createTextNode(valores.join(' · '))); padre.appendChild(p);
}
function mensajes(padre, prefijo, lista, clase) {
  lista.forEach(t => { const d = document.createElement('div'); d.className = 'msg ' + clase;
    d.textContent = prefijo + t; padre.appendChild(d); });
}

function insignia(d) {
  const s = document.createElement('span');
  s.className = 'badge ' + (d.usa_ia ? 'ia' : 'reglas');
  s.textContent = d.usa_ia ? 'Con ayuda de IA · revisa que sea lo que querías' : 'Entendido por reglas, sin IA';
  s.title = d.usa_ia ? 'Una parte de tu frase se interpretó con Gemini; todo se validó contra los catálogos del SAIC.'
                     : 'Se entendió con reglas fijas: no hubo llamada a la IA.';
  return s;
}

function aclaraciones(caja, d) {
  (d.aclarar || []).forEach(t => {
    const m = document.createElement('div'); m.className = 'msg error';
    m.textContent = 'Aclara por favor: ' + t; caja.appendChild(m);
    (d.opciones || []).filter(o => o.mensaje === t).forEach(o => {
      const fila = document.createElement('div'); fila.className = 'opciones';
      o.candidatos.forEach(c => {
        const b = document.createElement('button'); b.className = 'sec'; b.textContent = c.texto;
        b.onclick = () => elegir(o, c); fila.appendChild(b);
      });
      caja.appendChild(fila);
    });
  });
}

function elegir(o, c) {
  const d = planActual;
  if (o.campo === 'lugares') {
    const vals = Array.isArray(c.valor) ? c.valor : [c.valor];
    const nuevos = vals.filter(v => !d.lugares.includes(v));
    if (nuevos.length) { nuevos.forEach(v => d.lugares.push(v)); d.lugares_txt.push(c.texto); }
  } else if (o.campo === 'anios') {
    if (!d.anios.includes(c.valor)) { d.anios.push(c.valor); d.anios.sort((x, y) => x - y); d.anios_txt = d.anios.map(String); }
  } else if (o.campo === 'estratos') {
    if (!d.estratos.includes(c.valor)) {
      d.estratos.push(c.valor); d.estratos_txt = d.estratos_txt.filter(t => t !== 'Ninguno'); d.estratos_txt.push(c.texto);
    }
  }
  d.aclarar = d.aclarar.filter(t => t !== o.mensaje);
  d.opciones = d.opciones.filter(x => x !== o);
  d.listo = d.faltantes.length === 0 && d.aclarar.length === 0;
  mostrarPlan(d);
}

function mostrarPlan(d) {
  const caja = $('plan'); vaciar(caja); caja.hidden = false;
  const h = document.createElement('strong'); h.textContent = 'Esto entendí:'; caja.appendChild(h); caja.appendChild(insignia(d));
  linea(caja, 'Años', d.anios_txt);
  linea(caja, 'Lugares', d.lugares_txt.length ? d.lugares_txt : ['(falta)']);
  linea(caja, 'Variables', d.variables_txt.length ? d.variables_txt : ['(faltan)']);
  linea(caja, 'Actividades', d.actividades_txt);
  linea(caja, 'Estratos', d.estratos_txt);
  mensajes(caja, 'Supuesto: ', d.supuestos, 'aviso');
  mensajes(caja, '', d.notas, 'nota');
  mensajes(caja, '', d.avisos, 'aviso');
  aclaraciones(caja, d);
  mensajes(caja, 'Falta: ', d.faltantes, 'error');
  const acc = document.createElement('div'); acc.className = 'acciones';
  const b1 = document.createElement('button'); b1.textContent = 'Ver datos'; b1.disabled = !d.listo; b1.onclick = verDatos;
  const b2 = document.createElement('button'); b2.textContent = 'Descargar Excel oficial'; b2.className = 'sec';
  b2.disabled = !d.listo;
  b2.onclick = () => descargar('/api/descargar', 'SAIC_oficial.xlsx', 'Preparando el Excel oficial…');
  const b3 = document.createElement('button'); b3.textContent = 'Descargar CSV'; b3.className = 'sec';
  b3.disabled = !d.listo; b3.onclick = () => descargar('/api/descargar_csv', 'SAIC.csv', 'Preparando el CSV…');
  acc.appendChild(b1); acc.appendChild(b2); acc.appendChild(b3); caja.appendChild(acc);
  const fu = document.createElement('p'); fu.className = 'fuente';
  fu.textContent = 'Al usar estos datos cita: Fuente: INEGI, Censos Económicos 2024 (SAIC), consulta del ' + new Date().toLocaleDateString('es-MX') + '.';
  caja.appendChild(fu);
}

async function interpretar() {
  const texto = $('texto').value.trim(); if (!texto) return;
  $('btnInterpretar').disabled = true; vaciar($('tabla')); vaciar($('grafica')); $('plan').hidden = true; estado('Interpretando…');
  try {
    const r = await post('/api/interpretar', { texto }); const d = await r.json();
    if (!r.ok) { estado(d.error || 'Ocurrió un error.', true); return; }
    planActual = d; mostrarPlan(d); estado('');
  } catch (e) { estado('No pude conectar con el servidor.', true); }
  finally { $('btnInterpretar').disabled = false; }
}

function formato(v) {
  if (v === null || v === undefined) return null;
  return typeof v === 'number' ? v.toLocaleString('es-MX') : String(v);
}

async function verDatos() {
  estado('Consultando el SAIC…'); vaciar($('tabla')); vaciar($('grafica'));
  try {
    const r = await post('/api/consultar', { plan: planActual }); const d = await r.json();
    if (!r.ok) { estado(d.error || 'Ocurrió un error.', true); return; }
    if (d.demasiado_grande) { estado('La consulta tiene ' + d.filas + ' filas: es muy grande para mostrarla aquí, pero puedes descargar el Excel oficial.'); return; }
    if (d.vacio) { estado('El SAIC no devolvió datos para esta combinación.'); return; }
    const cont = document.createElement('div'); cont.className = 'contenedor-tabla';
    const t = document.createElement('table'), cab = document.createElement('tr');
    d.columnas.forEach(c => { const th = document.createElement('th'); th.textContent = c.replace('|', ' · '); cab.appendChild(th); });
    t.appendChild(cab);
    d.filas.forEach(fila => {
      const tr = document.createElement('tr');
      fila.forEach(v => { const td = document.createElement('td'); const f = formato(v);
        if (f === null) { td.textContent = '—'; td.title = 'Dato omitido por confidencialidad'; }
        else { td.textContent = f; if (typeof v === 'number') td.className = 'num'; }
        tr.appendChild(td); });
      t.appendChild(tr);
    });
    cont.appendChild(t); $('tabla').appendChild(cont); estado(d.filas.length + ' filas.'); mostrarGrafica(d);
  } catch (e) { estado('No pude conectar con el servidor.', true); }
}

async function descargar(url, respaldo, mensaje) {
  estado(mensaje);
  try {
    const r = await post(url, { plan: planActual });
    if (!r.ok) { const d = await r.json(); estado(d.error || 'Ocurrió un error.', true); return; }
    const blob = await r.blob();
    const m = (r.headers.get('Content-Disposition') || '').match(/filename="?([^";]+)"?/i);
    const a = document.createElement('a'); a.href = URL.createObjectURL(blob);
    a.download = m ? m[1] : respaldo; document.body.appendChild(a); a.click(); a.remove();
    URL.revokeObjectURL(a.href); estado('');
  } catch (e) { estado('No pude conectar con el servidor.', true); }
}

const COLORES = ['#1e5aa8', '#e07b00', '#2a9d8f', '#b3261e', '#7b4bb3', '#6c757d', '#c9a227', '#1d6b3a'];
const SVGNS = 'http://www.w3.org/2000/svg';
const ETIQ = { act: 'Actividad', anio: 'Año', lugar: 'Lugar', 'anio+lugar': 'Año y lugar', ninguno: 'Ninguno' };
const DIM = { act: f => f.act, anio: f => f.anio, lugar: f => f.lugar,
  'anio+lugar': f => f.lugar + ' · ' + f.anio, ninguno: f => 'Valor' };

function filasObjeto(d) {
  const c = d.columnas;
  const iA = c.findIndex(x => x.startsWith('Año')), iE = c.indexOf('Entidad'), iM = c.indexOf('Municipio');
  const iAct = c.findIndex(x => x.startsWith('Actividad'));
  const vars = c.map((n, i) => ({ nombre: n, i })).filter(v => v.nombre.includes('|'));
  const filas = d.filas.map(f => ({
    anio: String(f[iA]),
    lugar: (iM >= 0 && f[iM]) ? String(f[iE]) + ' · ' + String(f[iM]) : String(f[iE]),
    act: iAct >= 0 ? String(f[iAct]) : '',
    vals: vars.map(v => (typeof f[v.i] === 'number' ? f[v.i] : null)),
  }));
  return { filas, vars: vars.map(v => v.nombre.replace('|', ' · ')) };
}

function autoEjes(filas) {
  const n = k => new Set(filas.map(f => f[k])).size;
  const na = n('act'), ny = n('anio'), nl = n('lugar');
  if (na > 1) return { x: 'act', serie: (ny > 1 && nl > 1) ? 'anio+lugar' : (ny > 1 ? 'anio' : (nl > 1 ? 'lugar' : 'ninguno')) };
  if (ny > 1) return { x: 'anio', serie: nl > 1 ? 'lugar' : 'ninguno' };
  if (nl > 1) return { x: 'lugar', serie: 'ninguno' };
  return { x: null, serie: 'ninguno' };
}

function el(tag, attrs, texto) {
  const e = document.createElementNS(SVGNS, tag);
  for (const k in attrs) e.setAttribute(k, attrs[k]);
  if (texto !== undefined) e.textContent = texto;
  return e;
}
function numTxt(v) { return v.toLocaleString('es-MX', { maximumFractionDigits: Math.abs(v) >= 1000 ? 0 : 2 }); }
function corto(s, n) { return s.length > n ? s.slice(0, n - 1) + '…' : s; }

function dibujarGrafica(area, nota, filas, iv, x, serie, nombreVar) {
  vaciar(area); nota.textContent = ''; nota.hidden = true;
  if (serie === x) serie = 'ninguno';
  const fx = DIM[x], fs = DIM[serie];
  const cats = new Map(), totSerie = new Map(); let duplicado = false;
  filas.forEach(f => {
    const c = fx(f), s = fs(f), v = f.vals[iv];
    if (!cats.has(c)) cats.set(c, new Map());
    if (cats.get(c).has(s)) duplicado = true;
    cats.get(c).set(s, v);
    totSerie.set(s, (totSerie.get(s) || 0) + (v || 0));
  });
  if (duplicado) {
    nota.textContent = 'Con esta combinación hay varias filas por barra. Elige una opción en "Colores por" (por ejemplo, Año o Lugar).';
    nota.hidden = false; return;
  }
  let series = [...totSerie.keys()].sort((a, b) => totSerie.get(b) - totSerie.get(a));
  const avisos = [];
  if (series.length > 8) { avisos.push('Se muestran las 8 series mayores de ' + series.length + '.'); series = series.slice(0, 8); }
  const suma = c => series.reduce((a, s) => a + (cats.get(c).get(s) || 0), 0);
  let nombres = [...cats.keys()];
  if (x === 'anio') nombres.sort(); else nombres.sort((a, b) => suma(b) - suma(a));
  if (nombres.length > 25) { avisos.push('Se muestran las 25 categorías mayores de ' + nombres.length + '.'); nombres = nombres.slice(0, 25); }
  if (avisos.length) { nota.textContent = avisos.join(' '); nota.hidden = false; }

  const barH = 16, gap = 12, izq = 260, der = 90, W = 900, top = 56;
  const grupo = series.length * barH + gap, H = top + nombres.length * grupo + 34;
  let max = 0;
  nombres.forEach(c => series.forEach(s => { const v = cats.get(c).get(s); if (typeof v === 'number' && v > max) max = v; }));
  if (max <= 0) max = 1;
  const svg = el('svg', { xmlns: SVGNS, viewBox: '0 0 ' + W + ' ' + H, width: W, height: H });
  svg.style.maxWidth = '100%'; svg.style.height = 'auto';
  svg.appendChild(el('rect', { x: 0, y: 0, width: W, height: H, fill: '#ffffff' }));
  const T = { 'font-family': 'Arial, Helvetica, sans-serif', fill: '#1f2933' };
  svg.appendChild(el('text', Object.assign({ x: 12, y: 22, 'font-size': 15, 'font-weight': 'bold' }, T), corto(nombreVar, 95)));
  if (serie !== 'ninguno') {
    let lx = 12;
    series.forEach((s, i) => {
      svg.appendChild(el('rect', { x: lx, y: 33, width: 11, height: 11, fill: COLORES[i % COLORES.length] }));
      const et = corto(s, 28);
      svg.appendChild(el('text', Object.assign({ x: lx + 16, y: 43, 'font-size': 11 }, T), et));
      lx += 16 + et.length * 6.2 + 18;
    });
  }
  nombres.forEach((c, j) => {
    const y0 = top + j * grupo;
    const et = el('text', Object.assign({ x: izq - 8, y: y0 + (series.length * barH) / 2 + 4, 'font-size': 11, 'text-anchor': 'end' }, T), corto(c, 40));
    et.appendChild(el('title', {}, c)); svg.appendChild(et);
    series.forEach((s, i) => {
      const v = cats.get(c).get(s), y = y0 + i * barH;
      if (typeof v === 'number') {
        const w = Math.max(1, (v / max) * (W - izq - der));
        const r = el('rect', { x: izq, y: y, width: w, height: barH - 3, fill: COLORES[i % COLORES.length], class: 'barra' });
        r.appendChild(el('title', {}, c + (serie !== 'ninguno' ? ' · ' + s : '') + ': ' + numTxt(v))); svg.appendChild(r);
        svg.appendChild(el('text', Object.assign({ x: izq + w + 5, y: y + barH - 5, 'font-size': 10 }, T), numTxt(v)));
      } else {
        svg.appendChild(el('text', { x: izq + 4, y: y + barH - 5, 'font-size': 10, 'font-family': T['font-family'], fill: '#8a949e' }, '— (dato reservado)'));
      }
    });
  });
  svg.appendChild(el('text', { x: 12, y: H - 10, 'font-size': 10, 'font-family': T['font-family'], fill: '#52606d' },
    'Fuente: INEGI, Censos Económicos 2024 (SAIC).'));
  area.appendChild(svg);
}

function descargarPNG(svg) {
  const clon = svg.cloneNode(true); clon.removeAttribute('style');
  const xml = new XMLSerializer().serializeToString(clon);
  const w = parseInt(svg.getAttribute('width'), 10), h = parseInt(svg.getAttribute('height'), 10);
  const img = new Image();
  img.onload = () => {
    const c = document.createElement('canvas'); c.width = w * 2; c.height = h * 2;
    const g = c.getContext('2d'); g.scale(2, 2); g.drawImage(img, 0, 0, w, h);
    c.toBlob(b => {
      const a = document.createElement('a'); a.href = URL.createObjectURL(b); a.download = 'grafica_saic.png';
      document.body.appendChild(a); a.click(); a.remove(); URL.revokeObjectURL(a.href);
    });
  };
  img.src = 'data:image/svg+xml;charset=utf-8,' + encodeURIComponent(xml);
}

function tablaCambios(filas, iv, nombreVar) {
  const anios = [...new Set(filas.map(f => f.anio))].sort();
  if (anios.length < 2) return null;
  const ini = anios[0], fin = anios[anios.length - 1];
  const m = new Map();
  filas.forEach(f => {
    const k = f.lugar + '||' + f.act;
    if (!m.has(k)) m.set(k, { lugar: f.lugar, act: f.act });
    if (f.anio === ini) m.get(k).a = f.vals[iv];
    if (f.anio === fin) m.get(k).b = f.vals[iv];
  });
  let datos = [...m.values()].filter(r => typeof r.a === 'number' && typeof r.b === 'number');
  datos.forEach(r => { r.cambio = r.b - r.a; r.pct = r.a !== 0 ? (r.cambio / r.a) * 100 : null; });
  datos.sort((p, q) => Math.abs(q.cambio) - Math.abs(p.cambio));
  const total = datos.length; datos = datos.slice(0, 30);
  const caja = document.createElement('div'); caja.className = 'contenedor-tabla';
  const h = document.createElement('p'); const hb = document.createElement('strong');
  hb.textContent = 'Cambio entre ' + ini + ' y ' + fin + ' · ' + nombreVar; h.appendChild(hb); caja.appendChild(h);
  if (!datos.length) {
    const p = document.createElement('p'); p.textContent = 'No hay datos comparables entre ' + ini + ' y ' + fin + ' (puede haber datos reservados).';
    caja.appendChild(p); return caja;
  }
  const t = document.createElement('table'), cab = document.createElement('tr');
  ['Lugar', 'Actividad', ini, fin, 'Cambio', 'Cambio %'].forEach(x => { const th = document.createElement('th'); th.textContent = x; cab.appendChild(th); });
  t.appendChild(cab);
  datos.forEach(r => {
    const tr = document.createElement('tr');
    [r.lugar, r.act, numTxt(r.a), numTxt(r.b), (r.cambio > 0 ? '+' : '') + numTxt(r.cambio),
     r.pct === null ? '—' : (r.pct > 0 ? '+' : '') + r.pct.toFixed(1) + ' %'].forEach((x, i) => {
      const td = document.createElement('td'); td.textContent = x; if (i >= 2) td.className = 'num'; tr.appendChild(td);
    });
    t.appendChild(tr);
  });
  caja.appendChild(t);
  const nota = document.createElement('p'); nota.className = 'fuente';
  nota.textContent = (total > 30 ? 'Se muestran los 30 cambios mayores de ' + total + '. ' : '') +
    'Los montos en pesos de censos anteriores pueden requerir ajuste por inflación (la nota metodológica del SAIC menciona inflactores por año); ' +
    'los conteos, como el personal ocupado, no se ven afectados.';
  caja.appendChild(nota);
  return caja;
}

function crearSelect(padre, etiqueta, opciones, valor) {
  const l = document.createElement('label'); l.textContent = etiqueta + ': ';
  const s = document.createElement('select');
  opciones.forEach(([v, t]) => { const o = document.createElement('option'); o.value = v; o.textContent = t; s.appendChild(o); });
  s.value = valor; l.appendChild(s); padre.appendChild(l); return s;
}

function mostrarGrafica(d) {
  const cont = $('grafica'); vaciar(cont);
  const { filas, vars } = filasObjeto(d), auto = autoEjes(filas);
  if (!filas.length || !vars.length || !auto.x) return;
  const panel = document.createElement('div'); panel.className = 'tarjeta';
  const titulo = document.createElement('strong'); titulo.textContent = 'Gráfica y comparación'; panel.appendChild(titulo);
  const ctl = document.createElement('div'); ctl.className = 'controles'; panel.appendChild(ctl);
  const selV = crearSelect(ctl, 'Variable', vars.map((n, i) => [String(i), n]), '0');
  const selX = crearSelect(ctl, 'Eje', ['act', 'anio', 'lugar'].map(k => [k, ETIQ[k]]), auto.x);
  const selS = crearSelect(ctl, 'Colores por', ['ninguno', 'anio', 'lugar', 'act', 'anio+lugar'].map(k => [k, ETIQ[k]]), auto.serie);
  const bPng = document.createElement('button'); bPng.className = 'sec'; bPng.textContent = 'Descargar imagen (PNG)'; ctl.appendChild(bPng);
  const nota = document.createElement('div'); nota.className = 'msg aviso'; nota.hidden = true; panel.appendChild(nota);
  const area = document.createElement('div'); area.className = 'contenedor-tabla'; panel.appendChild(area);
  const cambios = document.createElement('div'); panel.appendChild(cambios);
  const redibujar = () => {
    const iv = parseInt(selV.value, 10);
    dibujarGrafica(area, nota, filas, iv, selX.value, selS.value, vars[iv]);
    vaciar(cambios); const t = tablaCambios(filas, iv, vars[iv]); if (t) cambios.appendChild(t);
  };
  [selV, selX, selS].forEach(s => { s.onchange = redibujar; });
  bPng.onclick = () => { const svg = area.querySelector('svg'); if (svg) descargarPNG(svg); };
  cont.appendChild(panel); redibujar();
}

$('entrar').onclick = entrar;
$('codigo').addEventListener('keydown', e => { if (e.key === 'Enter') entrar(); });
$('abrirReporte').onclick = () => { $('reporte').hidden = false; $('estadoReporte').textContent = ''; $('comentario').focus(); };
$('enviarReporte').onclick = enviarReporte;
$('cerrarReporte').onclick = () => { $('reporte').hidden = true; };
fetch('/api/estado').then(r => r.json())
  .then(d => { if (d.requiere_codigo && !d.autenticado) mostrarAcceso(); else mostrarPrincipal(); })
  .catch(() => mostrarPrincipal());
$('btnInterpretar').onclick = interpretar;
$('texto').addEventListener('keydown', e => { if (e.key === 'Enter' && (e.metaKey || e.ctrlKey)) interpretar(); });
document.querySelectorAll('.ejemplos a').forEach(a => a.onclick = () => { $('texto').value = a.dataset.ej; $('texto').focus(); });
</script>
</body>
</html>
"""


if __name__ == "__main__":
    if not (os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY")):
        print("Aviso: no hay GEMINI_API_KEY; solo funcionarán las peticiones que las "
              "reglas entienden sin IA (años, claves, estados, glosario).")
    if CODIGO_ACCESO:
        print("Código de acceso activado: quien entre deberá escribirlo.")
    else:
        print("Aviso: no hay CODIGO_ACCESO; la página queda abierta. Úsala solo en tu "
              "computadora (no la compartas así).")
    print(f"Los registros de uso y reportes se guardan en: {CARPETA_REGISTRO}")
    print("Abre en tu navegador: http://127.0.0.1:8000   (Ctrl + C para detener)")
    app.run(host="127.0.0.1", port=8000)
