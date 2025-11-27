import streamlit as st
import swisseph as swe
import math, csv, os
from datetime import datetime, timedelta
from collections import defaultdict
import matplotlib.pyplot as plt
from reportlab.lib.pagesizes import letter
from reportlab.platypus import SimpleDocTemplate, Paragraph, Image, Spacer, Table
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
import base64
import tempfile
import io

# ----------------------------- FUNCIONES DE CONVERSIÓN COORDENADAS -----------------------------
def gms_a_gd(grados, minutos, segundos, direccion):
    gd = grados + minutos/60.0 + segundos/3600.0
    if direccion in ['S', 'W']:
        gd = -gd
    return gd

def gd_a_gms(grados_decimal):
    if abs(grados_decimal) > 180:
        grados_decimal = (grados_decimal + 180) % 360 - 180
    
    signo = 1 if grados_decimal >= 0 else -1
    grados_abs = abs(grados_decimal)
    grados = int(grados_abs)
    minutos_decimal = (grados_abs - grados) * 60
    minutos = int(minutos_decimal)
    segundos = (minutos_decimal - minutos) * 60
    
    if abs(grados_decimal) <= 90:
        direccion = 'N' if grados_decimal >= 0 else 'S'
    else:
        direccion = 'E' if grados_decimal >= 0 else 'W'
    
    return abs(grados), minutos, segundos, direccion

# ----------------------------- CLASE DE ANÁLISIS ASTROLÓGICO MEJORADA -----------------------------
class AnalisisAstrologicoWeb:
    def __init__(self):
        self.MAX_YEARS = 120
        self.ASPECT_ORB = 1.0
        
        self.ASPECTS = {
            "Conjunction": 0.0, "Sextile": 60.0, "Square": 90.0, 
            "Trine": 120.0, "Opposition": 180.0
        }
        
        self.ASPECT_COLORS = {
            "Conjunction": "#f2c94c", "Sextile": "#2ecc71", "Trine": "#2f80ed",
            "Square": "#e74c3c", "Opposition": "#c0392b"
        }
        
        self.POINT_Y = {"Hyleg": 3, "Alcocoden": 2, "Ascendente": 1, "Fortuna": 0}
        
        self.TABLA_ANIOS_ALCOCODEN = {
            "Saturn": (30, 43.75, 57), "Jupiter": (12, 45.5, 79), "Mars": (15, 40.5, 66),
            "Sun": (19, 69, 120), "Venus": (8, 45, 82), "Mercury": (13, 48, 76), 
            "Moon": (25, 66, 108)
        }

    def normalizar_grados(self, x): 
        return x % 360.0

    def diferencia_grados(self, a, b):
        d = abs((a - b + 180.0) % 360.0 - 180.0)
        return d

    def esta_combusto(self, planeta_nombre, planeta_lon, sol_lon):
        if planeta_nombre == "Sun": 
            return False
        separacion = self.diferencia_grados(planeta_lon, sol_lon)
        orb_combustion = 8.5 if planeta_nombre == "Moon" else 7.0
        return separacion <= orb_combustion

    def obtener_estado_combustion(self, planeta_nombre, planeta_lon, sol_lon):
        if planeta_nombre == "Sun": 
            return "No aplica (Sol)", 0
        separacion = self.diferencia_grados(planeta_lon, sol_lon)
        orb_combustion = 8.5 if planeta_nombre == "Moon" else 7.0
        combusto = separacion <= orb_combustion
        return "COMBUSTO" if combusto else "No combusto", separacion

    def en_signo_aphetic(self, longitud):
        signo_idx = int(longitud // 30)
        signos_cardinales = [0, 3, 6, 9]
        signos_fijos = [1, 4, 7, 10]
        return signo_idx in (signos_cardinales + signos_fijos)

    def obtener_casa(self, longitud, casas):
        for i in range(12):
            casa_inicio = casas[i]
            casa_fin = casas[(i + 1) % 12]
            if casa_fin < casa_inicio: 
                casa_fin += 360
            punto = longitud if longitud >= casa_inicio else longitud + 360
            if casa_inicio <= punto < casa_fin: 
                return i + 1
        return 1

    def en_casa_fuerte(self, casa_idx):
        casas_angulares = [1, 4, 7, 10]
        casas_sucedentes = [2, 5, 8, 11]
        return casa_idx in (casas_angulares + casas_sucedentes)

    def es_casa_malefica(self, casa_idx):
        return casa_idx in [6, 8, 12]

    def obtener_regente_signo(self, longitud):
        signo_idx = int(longitud // 30)
        signos = ['Aries', 'Tauro', 'Géminis', 'Cáncer', 'Leo', 'Virgo', 
                 'Libra', 'Escorpio', 'Sagitario', 'Capricornio', 'Acuario', 'Piscis']
        signo_nombre = signos[signo_idx]
        regentes = {
            'Aries': 'Mars', 'Tauro': 'Venus', 'Géminis': 'Mercury', 'Cáncer': 'Moon',
            'Leo': 'Sun', 'Virgo': 'Mercury', 'Libra': 'Venus', 'Escorpio': 'Mars',
            'Sagitario': 'Jupiter', 'Capricornio': 'Saturn', 'Acuario': 'Saturn', 'Piscis': 'Jupiter'
        }
        return regentes[signo_nombre], signo_nombre

    def obtener_signo(self, longitud):
        signo_idx = int(longitud // 30)
        signos = ['Aries', 'Tauro', 'Géminis', 'Cáncer', 'Leo', 'Virgo', 
                 'Libra', 'Escorpio', 'Sagitario', 'Capricornio', 'Acuario', 'Piscis']
        return signos[signo_idx]

    def calcular_anios_alcocoden(self, alcocoden_point, alcocoden_casa, alcocoden_combusto):
        if alcocoden_point not in self.TABLA_ANIOS_ALCOCODEN:
            return 0, "Alcocoden no reconocido"
        
        min_anios, med_anios, max_anios = self.TABLA_ANIOS_ALCOCODEN[alcocoden_point]
        
        if alcocoden_combusto or self.es_casa_malefica(alcocoden_casa):
            return min_anios, "Años mínimos (condición débil)"
        elif alcocoden_casa in [1, 4, 7, 10]:
            return max_anios, "Años máximos (casa angular)"
        elif alcocoden_casa in [2, 5, 8, 11]:
            return med_anios, "Años medios (casa sucedente)"
        else:
            return min_anios, "Años mínimos (casa cadente)"

    def calcular_hyleg_tradicional_corregido(self, natal_pos, asc, part_fort, casas, is_diurnal):
        sol_lon = natal_pos["Sun"]
        
        if is_diurnal:
            candidatos = [("Sun", "Sol"), ("Moon", "Luna"), ("Ascendente", "Ascendente"), 
                         ("Fortuna", "Fortuna"), ("Lunacion", "Lunación Previa")]
        else:
            candidatos = [("Moon", "Luna"), ("Sun", "Sol"), ("Ascendente", "Ascendente"), 
                         ("Fortuna", "Fortuna"), ("Lunacion", "Lunación Previa")]
        
        for candidato, nombre in candidatos:
            valido = False
            mensaje = ""
            
            if candidato == "Sun":
                lon = sol_lon
                casa = self.obtener_casa(lon, casas)
                valido = (self.en_signo_aphetic(lon) and self.en_casa_fuerte(casa) and 
                         not self.es_casa_malefica(casa))
                mensaje = f"Sol en {self.obtener_signo(lon)} (casa {casa})"
                
            elif candidato == "Moon":
                lon = natal_pos["Moon"]
                casa = self.obtener_casa(lon, casas)
                combusta = self.esta_combusto("Moon", lon, sol_lon)
                valido = (self.en_signo_aphetic(lon) and self.en_casa_fuerte(casa) and 
                         not self.es_casa_malefica(casa) and not combusta)
                mensaje = f"Luna en {self.obtener_signo(lon)} (casa {casa})"
                if combusta: 
                    mensaje += " - COMBUSTA"
                
            elif candidato == "Ascendente":
                casa = 1
                valido = self.en_signo_aphetic(asc)
                if valido:
                    regente_asc, signo_asc = self.obtener_regente_signo(asc)
                    regente_lon = natal_pos.get(regente_asc)
                    if regente_lon is not None:
                        regente_casa = self.obtener_casa(regente_lon, casas)
                        regente_combusto = self.esta_combusto(regente_asc, regente_lon, sol_lon)
                        regente_valido = (self.en_casa_fuerte(regente_casa) and 
                                         not self.es_casa_malefica(regente_casa) and
                                         not regente_combusto)
                        valido = valido and regente_valido
                mensaje = f"Ascendente en {self.obtener_signo(asc)} (casa {casa})"
                
            elif candidato == "Fortuna":
                casa = self.obtener_casa(part_fort, casas)
                valido = self.en_signo_aphetic(part_fort)
                if valido:
                    regente_fort, signo_fort = self.obtener_regente_signo(part_fort)
                    regente_lon = natal_pos.get(regente_fort)
                    if regente_lon is not None:
                        regente_casa = self.obtener_casa(regente_lon, casas)
                        regente_combusto = self.esta_combusto(regente_fort, regente_lon, sol_lon)
                        regente_valido = (self.en_casa_fuerte(regente_casa) and 
                                         not self.es_casa_malefica(regente_casa) and
                                         not regente_combusto)
                        valido = valido and regente_valido
                mensaje = f"Fortuna en {self.obtener_signo(part_fort)} (casa {casa})"
                
            elif candidato == "Lunacion":
                lon = natal_pos["Moon"]
                casa = self.obtener_casa(lon, casas)
                combusta = self.esta_combusto("Moon", lon, sol_lon)
                valido = (self.en_signo_aphetic(lon) and self.en_casa_fuerte(casa) and
                         not self.es_casa_malefica(casa) and not combusta)
                mensaje = f"Lunación en {self.obtener_signo(lon)} (casa {casa})"
            
            if valido:
                return candidato, f"{nombre} válido - {mensaje}"
        
        return None, "No se encontró Hyleg válido - Carta de vida corta/vulnerable"

    def calcular_alcocoden_tradicional_corregido(self, hyleg_point, natal_pos, casas, sol_lon, asc, part_fort):
        if hyleg_point is None:
            return None, "Sin Hyleg", 0, "No aplica"
        
        if hyleg_point == "Ascendente":
            hyleg_lon = asc
        elif hyleg_point == "Fortuna":
            hyleg_lon = part_fort
        else:
            hyleg_lon = natal_pos[hyleg_point]
        
        alcocoden_nombre, signo_hyleg = self.obtener_regente_signo(hyleg_lon)
        
        if alcocoden_nombre in natal_pos:
            alcocoden_lon = natal_pos[alcocoden_nombre]
            alcocoden_casa = self.obtener_casa(alcocoden_lon, casas)
            alcocoden_combusto = self.esta_combusto(alcocoden_nombre, alcocoden_lon, sol_lon)
            
            anios, mensaje_anios = self.calcular_anios_alcocoden(alcocoden_nombre, alcocoden_casa, alcocoden_combusto)
            
            fuerte = (self.en_casa_fuerte(alcocoden_casa) and 
                     not alcocoden_combusto and
                     not self.es_casa_malefica(alcocoden_casa))
            
            estado = "fuerte" if fuerte else "débil"
            combusto_info = " (COMBUSTO)" if alcocoden_combusto else ""
            casa_info = f" (casa {alcocoden_casa})"
            
            alcocoden_signo_real = self.obtener_signo(alcocoden_lon)
            
            mensaje = f"Alcocoden: {alcocoden_nombre} en {alcocoden_signo_real}{casa_info}{combusto_info} ({estado}) - Regente del Hyleg en {signo_hyleg} - {mensaje_anios}"
            return alcocoden_nombre, mensaje, anios, mensaje_anios
        
        anios, mensaje_anios = self.calcular_anios_alcocoden("Saturn", 12, True)
        return "Saturn", f"Alcocoden por defecto: Saturn - {mensaje_anios}", anios, mensaje_anios

    def calcular_parte_fortuna_corregida(self, asc, sol_lon, luna_lon, is_diurnal):
        fortuna = asc + luna_lon - sol_lon
        return self.normalizar_grados(fortuna)

    # NUEVO: Función para generar PDF (tomada de analisis_astrologico_interfaz.py)
    def generar_pdf_completo(self, resultado, events, consultante_nombre):
        """Genera un PDF completo con todos los resultados"""
        try:
            buffer = io.BytesIO()
            
            styles = getSampleStyleSheet()
            if "CustomTitle" not in styles:
                styles.add(ParagraphStyle(name="CustomTitle", fontSize=18, leading=22, alignment=1))
            styles.add(ParagraphStyle(name="Body", fontSize=10, leading=14, alignment=4))
            styles.add(ParagraphStyle(name="BodyBold", parent=styles["Body"], fontName="Helvetica-Bold"))
            styles.add(ParagraphStyle(name="Center", parent=styles["Body"], alignment=1))
            styles.add(ParagraphStyle(name="Small", parent=styles["Body"], fontSize=8, leading=10))

            doc = SimpleDocTemplate(buffer, pagesize=letter)
            story = []

            # Título principal
            story.append(Paragraph(f"Análisis Astrológico Completo - {consultante_nombre}", styles["CustomTitle"]))
            story.append(Spacer(1,12))

            # Información personal
            story.append(Paragraph("<b>INFORMACIÓN DEL NACIMIENTO:</b>", styles["BodyBold"]))
            story.append(Spacer(1,6))

            info_lines = [
                f"<b>Fecha:</b> {resultado['fecha_nacimiento']}",
                f"<b>Hora local:</b> {resultado['hora_local']}",
                f"<b>Zona horaria:</b> {resultado['zona_horaria']:+}",
                f"<b>Latitud:</b> {resultado['latitud']:.6f}°",
                f"<b>Longitud:</b> {resultado['longitud']:.6f}°",
                f"<b>Genitura:</b> {'DIURNA' if resultado['is_diurnal'] else 'NOCTURNA'}",
                f"<b>Hyleg:</b> {resultado['hyleg_point']}",
                f"<b>Alcocoden:</b> {resultado['alcocoden_point']}",
                f"<b>Años potenciales:</b> {resultado['anios_alcocoden']} años"
            ]

            for line in info_lines:
                story.append(Paragraph(line, styles["Body"]))
            story.append(Spacer(1,12))

            # Estado de combustión
            story.append(Paragraph("<b>ESTADO DE COMBUSTIÓN:</b>", styles["BodyBold"]))
            story.append(Spacer(1,6))

            combustion_data = [["Planeta", "Longitud", "Signo", "Casa", "Estado"]]
            for planeta, longitud in resultado['natal_pos'].items():
                signo = self.obtener_signo(longitud)
                casa = self.obtener_casa(longitud, resultado['houses'])
                estado, separacion = self.obtener_estado_combustion(planeta, longitud, resultado['natal_pos']["Sun"])
                combustion_data.append([planeta, f"{longitud:.2f}°", signo, casa, estado])

            tbl = Table(combustion_data, hAlign='LEFT')
            story.append(tbl)
            story.append(Spacer(1,12))

            # Eventos principales
            story.append(Paragraph("<b>PRÓXIMOS EVENTOS PRINCIPALES:</b>", styles["BodyBold"]))
            story.append(Spacer(1,6))

            events_data = [["Año", "Punto", "Aspecto", "Planeta", "Precisión"]]
            for e in events[:50]:  # Mostrar solo los primeros 50 eventos
                events_data.append([str(e["year"]), e["point"], e["aspect"], e["target"], f"{e['sep']:.3f}°"])

            tbl_events = Table(events_data, hAlign='LEFT', repeatRows=1)
            story.append(tbl_events)
            story.append(Spacer(1,12))

            doc.build(story)
            pdf_bytes = buffer.getvalue()
            buffer.close()
            
            return pdf_bytes
            
        except Exception as e:
            st.error(f"Error al generar PDF: {str(e)}")
            return None

    # NUEVO: Función para generar CSV detallado
    def generar_csv_detallado(self, events, consultante_nombre):
        """Genera un CSV detallado con todos los eventos"""
        output = io.StringIO()
        writer = csv.writer(output)
        writer.writerow(["Año", "Fecha simbólica", "Punto dirigido", "Aspecto", "Planeta natal", "Separación (°)"])
        for e in events:
            writer.writerow([e["year"], e["date"], e["point"], e["aspect"], e["target"], e["sep"]])
        return output.getvalue()

    def realizar_analisis_completo(self, fecha_nacimiento, hora_local, zona_horaria, 
                                 consultante_nombre, latitud_gms, longitud_gms):
        try:
            # Convertir coordenadas
            latitud = gms_a_gd(*latitud_gms)
            longitud = gms_a_gd(*longitud_gms)
            
            # Cálculos de fecha y hora
            year, month, day = map(int, fecha_nacimiento.split("-"))
            h, m = map(int, hora_local.split(":"))
            hour_decimal = h + m/60.0
            jd_ut = swe.julday(year, month, day, hour_decimal - zona_horaria)
            swe.set_topo(longitud, latitud, 0.0)
            
            # Calcular posiciones planetarias
            def planet_lon(pid):
                return self.normalizar_grados(swe.calc_ut(jd_ut, pid)[0][0])
            
            planets = {
                "Sun": swe.SUN, "Moon": swe.MOON, "Mercury": swe.MERCURY, "Venus": swe.VENUS,
                "Mars": swe.MARS, "Jupiter": swe.JUPITER, "Saturn": swe.SATURN
            }
            
            natal_pos = {name: planet_lon(pid) for name, pid in planets.items()}
            
            # Casas y puntos importantes
            houses, ascmc = swe.houses_ex(jd_ut, latitud, longitud, b'P')
            asc = self.normalizar_grados(ascmc[0])
            mc = self.normalizar_grados(ascmc[1])
            
            # Determinar genitura
            eq_sol = swe.calc_ut(jd_ut, swe.SUN, swe.FLG_EQUATORIAL | swe.FLG_TOPOCTR)[0]
            ra_raw = eq_sol[0]
            ra_deg = self.normalizar_grados(ra_raw * 15.0) if ra_raw < 24 else self.normalizar_grados(ra_raw)
            dec = eq_sol[1]
            gmst_deg = self.normalizar_grados(swe.sidtime(jd_ut) * 15.0)
            
            lst_calculada = self.normalizar_grados(gmst_deg + longitud)
            H = lst_calculada - ra_deg
            if H > 180: H -= 360
            if H < -180: H += 360
            phi = math.radians(latitud); delta = math.radians(dec); Hrad = math.radians(H)
            sin_alt = math.sin(phi)*math.sin(delta) + math.cos(phi)*math.cos(delta)*math.cos(Hrad)
            alt_sol_topo = math.degrees(math.asin(max(-1.0,min(1.0,sin_alt))))
            is_diurnal = alt_sol_topo > 0
            
            # Parte de la Fortuna
            part_fort = self.calcular_parte_fortuna_corregida(asc, natal_pos["Sun"], natal_pos["Moon"], is_diurnal)
            
            # Calcular Hyleg y Alcocoden
            hyleg_point, hyleg_mensaje = self.calcular_hyleg_tradicional_corregido(
                natal_pos, asc, part_fort, houses, is_diurnal
            )
            
            alcocoden_point, alcocoden_mensaje, anios_alcocoden, mensaje_anios = self.calcular_alcocoden_tradicional_corregido(
                hyleg_point, natal_pos, houses, natal_pos["Sun"], asc, part_fort
            )
            
            # Preparar puntos para dirección
            if hyleg_point == "Sun":
                hyleg_lon = natal_pos["Sun"]
            elif hyleg_point == "Moon":
                hyleg_lon = natal_pos["Moon"]
            elif hyleg_point == "Ascendente":
                hyleg_lon = asc
            elif hyleg_point == "Fortuna":
                hyleg_lon = part_fort
            else:
                hyleg_lon = natal_pos.get(hyleg_point, natal_pos["Sun"])
            
            alcocoden_lon = natal_pos.get(alcocoden_point, natal_pos["Saturn"])
            
            points = {
                "Hyleg": hyleg_lon,
                "Alcocoden": alcocoden_lon,
                "Ascendente": asc,
                "Fortuna": part_fort
            }
            
            # Calcular direcciones primarias
            events = []  
            for year_ahead in range(1, self.MAX_YEARS+1):
                fecha_simbolica = (datetime(year, month, day) + timedelta(days=year_ahead*365.25)).date()
                for point_key, point_lon in points.items():
                    directed = self.normalizar_grados(point_lon + year_ahead)
                    for target_name, target_lon in natal_pos.items():
                        for asp_name, asp_angle in self.ASPECTS.items():
                            sep = self.diferencia_grados(directed, target_lon)
                            dist_to_asp = abs(sep - asp_angle)
                            if dist_to_asp > 180: 
                                dist_to_asp = abs(dist_to_asp - 360)
                            if dist_to_asp <= self.ASPECT_ORB:
                                events.append({
                                    "year": year_ahead, 
                                    "date": fecha_simbolica.isoformat(),
                                    "point": point_key, 
                                    "aspect": asp_name, 
                                    "target": target_name,
                                    "sep": round(dist_to_asp, 3)
                                })
            
            events.sort(key=lambda e: (e["year"], e["point"], e["aspect"]))
            
            # Crear gráfico
            fig = self.crear_grafico_tiempo(events, consultante_nombre)
            
            # NUEVO: Generar PDF y CSV
            pdf_bytes = self.generar_pdf_completo({
                'fecha_nacimiento': fecha_nacimiento,
                'hora_local': hora_local,
                'zona_horaria': zona_horaria,
                'latitud': latitud,
                'longitud': longitud,
                'is_diurnal': is_diurnal,
                'hyleg_point': hyleg_point,
                'alcocoden_point': alcocoden_point,
                'anios_alcocoden': anios_alcocoden,
                'natal_pos': natal_pos,
                'houses': houses,
                'asc': asc,
                'part_fort': part_fort,
                'points': points
            }, events, consultante_nombre)
            
            csv_content = self.generar_csv_detallado(events, consultante_nombre)
            
            return {
                'success': True,
                'consultante_nombre': consultante_nombre,
                'fecha_nacimiento': fecha_nacimiento,
                'hora_local': hora_local,
                'zona_horaria': zona_horaria,
                'latitud_gms': latitud_gms,
                'longitud_gms': longitud_gms,
                'latitud': latitud,
                'longitud': longitud,
                'is_diurnal': is_diurnal,
                'hyleg_point': hyleg_point,
                'hyleg_mensaje': hyleg_mensaje,
                'alcocoden_point': alcocoden_point,
                'alcocoden_mensaje': alcocoden_mensaje,
                'anios_alcocoden': anios_alcocoden,
                'mensaje_anios': mensaje_anios,
                'natal_pos': natal_pos,
                'houses': houses,
                'asc': asc,
                'part_fort': part_fort,
                'points': points,
                'events': events,
                'figura': fig,
                'pdf_bytes': pdf_bytes,  # NUEVO
                'csv_content': csv_content  # NUEVO
            }
            
        except Exception as e:
            return {'success': False, 'error': str(e)}

    def crear_grafico_tiempo(self, events, consultante_nombre):
        fig, ax = plt.subplots(figsize=(16, 4))
        y_map = {"Hyleg": 3, "Alcocoden": 2, "Ascendente": 1, "Fortuna": 0}
        
        import random
        random.seed(0)
        
        for e in events:
            x = e["year"]
            y = y_map.get(e["point"], 0)
            y_jitter = y + (random.random()-0.5)*0.12
            col = self.ASPECT_COLORS.get(e["aspect"], "#333333")
            marker = "o" if e["aspect"]!="Conjunction" else "D"
            size = 60 if e["aspect"]=="Conjunction" else 35
            ax.scatter(x, y_jitter, color=col, s=size, marker=marker, edgecolors="k", linewidths=0.3, alpha=0.9)
        
        for name, y in y_map.items():
            ax.hlines(y, 0, self.MAX_YEARS, colors="#dddddd", linestyles="dashed", linewidth=1)
            ax.text(-3, y, name, verticalalignment="center", fontsize=10, fontweight="bold")
        
        ax.set_xlim(0, self.MAX_YEARS+1)
        ax.set_ylim(-0.5, max(y_map.values())+0.8)
        ax.set_xlabel("Años simbólicos (1° = 1 año)")
        ax.set_yticks([])
        ax.set_title(f"Línea de vida astrológica - {consultante_nombre}")
        
        from matplotlib.lines import Line2D
        legend_elems = [
            Line2D([0],[0], marker='D', color='w', label='Conjunción', markerfacecolor=self.ASPECT_COLORS["Conjunction"], markersize=8, markeredgecolor='k'),
            Line2D([0],[0], marker='o', color='w', label='Trino', markerfacecolor=self.ASPECT_COLORS["Trine"], markersize=8, markeredgecolor='k'),
            Line2D([0],[0], marker='o', color='w', label='Sextil', markerfacecolor=self.ASPECT_COLORS["Sextile"], markersize=8, markeredgecolor='k'),
            Line2D([0],[0], marker='o', color='w', label='Cuadratura', markerfacecolor=self.ASPECT_COLORS["Square"], markersize=8, markeredgecolor='k'),
            Line2D([0],[0], marker='o', color='w', label='Oposición', markerfacecolor=self.ASPECT_COLORS["Opposition"], markersize=8, markeredgecolor='k')
        ]
        ax.legend(handles=legend_elems, loc='upper right', bbox_to_anchor=(1.0, 1.15), ncol=1)
        
        plt.tight_layout()
        return fig

# ----------------------------- INTERFAZ STREAMLIT MEJORADA -----------------------------

def main():
    st.set_page_config(
        page_title="Análisis Astrológico - Hyleg y Alcocoden",
        page_icon="♋",
        layout="wide"
    )
    
    st.title("♋ Análisis Astrológico Completo - Hyleg y Alcocoden")
    st.markdown("---")
    
    # Sidebar para entrada de datos
    with st.sidebar:
        st.header("📊 Datos de Nacimiento")
        
        consultante_nombre = st.text_input("Nombre del consultante", "Alejo")
        
        col1, col2 = st.columns(2)
        with col1:
            fecha_nacimiento = st.text_input("Fecha (YYYY-MM-DD)", "1981-07-15")
        with col2:
            hora_local = st.text_input("Hora local (HH:MM)", "05:16")
        
        zona_horaria = st.number_input("Zona horaria", value=-4.0, step=0.5)
        
        st.subheader("📍 Coordenadas Geográficas")
        
        st.write("**Latitud:**")
        col_lat1, col_lat2, col_lat3, col_lat4 = st.columns(4)
        with col_lat1:
            lat_grados = st.number_input("Grados", min_value=0, max_value=90, value=8, key="lat_g")
        with col_lat2:
            lat_minutos = st.number_input("Minutos", min_value=0, max_value=59, value=35, key="lat_m")
        with col_lat3:
            lat_segundos = st.number_input("Segundos", value=52.8, key="lat_s")
        with col_lat4:
            lat_direccion = st.selectbox("Dirección", ["N", "S"], key="lat_d")
        
        st.write("**Longitud:**")
        col_lon1, col_lon2, col_lon3, col_lon4 = st.columns(4)
        with col_lon1:
            lon_grados = st.number_input("Grados", min_value=0, max_value=180, value=71, key="lon_g")
        with col_lon2:
            lon_minutos = st.number_input("Minutos", min_value=0, max_value=59, value=8, key="lon_m")
        with col_lon3:
            lon_segundos = st.number_input("Segundos", value=38.4, key="lon_s")
        with col_lon4:
            lon_direccion = st.selectbox("Dirección", ["E", "W"], index=1, key="lon_d")
        
        if st.button("🔄 Verificar Coordenadas", use_container_width=True):
            latitud_gms = (lat_grados, lat_minutos, lat_segundos, lat_direccion)
            longitud_gms = (lon_grados, lon_minutos, lon_segundos, lon_direccion)
            
            latitud_gd = gms_a_gd(*latitud_gms)
            longitud_gd = gms_a_gd(*longitud_gms)
            
            st.success(f"✅ Latitud GD: {latitud_gd:.6f}°")
            st.success(f"✅ Longitud GD: {longitud_gd:.6f}°")
    
    # Botón principal de análisis
    if st.button("🎯 Ejecutar Análisis Astrológico Completo", type="primary", use_container_width=True):
        with st.spinner("Realizando cálculos astrológicos... Esto puede tomar unos segundos."):
            # Preparar parámetros
            latitud_gms = (lat_grados, lat_minutos, lat_segundos, lat_direccion)
            longitud_gms = (lon_grados, lon_minutos, lon_segundos, lon_direccion)
            
            analizador = AnalisisAstrologicoWeb()
            resultado = analizador.realizar_analisis_completo(
                fecha_nacimiento, hora_local, zona_horaria, 
                consultante_nombre, latitud_gms, longitud_gms
            )
            
            if resultado['success']:
                mostrar_resultados(resultado)
            else:
                st.error(f"❌ Error en el análisis: {resultado['error']}")

def mostrar_resultados(resultado):
    st.success("✅ Análisis completado exitosamente!")
    
    # Información básica
    st.header("📋 Información del Análisis")
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("Datos Personales")
        st.write(f"**Consultante:** {resultado['consultante_nombre']}")
        st.write(f"**Fecha de nacimiento:** {resultado['fecha_nacimiento']}")
        st.write(f"**Hora local:** {resultado['hora_local']}")
        st.write(f"**Zona horaria:** UTC{resultado['zona_horaria']:+.1f}")
        st.write(f"**Genitura:** {'DIURNA' if resultado['is_diurnal'] else 'NOCTURNA'}")
    
    with col2:
        st.subheader("Coordenadas")
        st.write(f"**Latitud GMS:** {resultado['latitud_gms'][0]}°{resultado['latitud_gms'][1]}'{resultado['latitud_gms'][2]}\" {resultado['latitud_gms'][3]}")
        st.write(f"**Longitud GMS:** {resultado['longitud_gms'][0]}°{resultado['longitud_gms'][1]}'{resultado['longitud_gms'][2]}\" {resultado['longitud_gms'][3]}")
        st.write(f"**Latitud GD:** {resultado['latitud']:.6f}°")
        st.write(f"**Longitud GD:** {resultado['longitud']:.6f}°")
    
    # Hyleg y Alcocoden
    st.header("🎯 Puntos Vitales")
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("Hyleg")
        st.info(f"**{resultado['hyleg_point']}**")
        st.write(resultado['hyleg_mensaje'])
    
    with col2:
        st.subheader("Alcocoden")
        st.info(f"**{resultado['alcocoden_point']}**")
        st.write(resultado['alcocoden_mensaje'])
        st.write(f"**Años potenciales:** {resultado['anios_alcocoden']} años")
        st.write(f"**Estado:** {resultado['mensaje_anios']}")
    
    # Gráfico de línea de tiempo
    st.header("📈 Línea de Vida Astrológica")
    st.pyplot(resultado['figura'])
    
    # Posiciones planetarias
    st.header("🪐 Posiciones Planetarias")
    planetas_data = []
    for planeta, longitud in resultado['natal_pos'].items():
        signo = AnalisisAstrologicoWeb().obtener_signo(longitud)
        casa = AnalisisAstrologicoWeb().obtener_casa(longitud, resultado['houses'])
        estado, separacion = AnalisisAstrologicoWeb().obtener_estado_combustion(planeta, longitud, resultado['natal_pos']["Sun"])
        planetas_data.append([planeta, f"{longitud:.2f}°", signo, casa, estado])
    
    st.table(planetas_data)
    
    # Eventos importantes (próximos 30 años)
    st.header("📅 Próximos Eventos (30 años)")
    eventos_proximos = [e for e in resultado['events'] if e['year'] <= 30]
    
    if eventos_proximos:
        for evento in eventos_proximos:
            with st.expander(f"Año {evento['year']} - {evento['point']} {evento['aspect']} {evento['target']}"):
                st.write(f"**Fecha simbólica:** {evento['date']}")
                st.write(f"**Precisión:** {evento['sep']:.3f}°")
                st.write(f"**Edad aproximada:** {int(resultado['fecha_nacimiento'][:4]) + evento['year']} años")
    else:
        st.info("No hay eventos significativos en los próximos 30 años")
    
    # NUEVA SECCIÓN: Descargas mejoradas
    st.header("📥 Descargar Resultados Completos")
    
    col1, col2 = st.columns(2)
    
    with col1:
        # Descargar PDF
        if resultado.get('pdf_bytes'):
            st.download_button(
                label="📄 Descargar PDF Completo",
                data=resultado['pdf_bytes'],
                file_name=f"analisis_astrologico_{resultado['consultante_nombre']}.pdf",
                mime="application/pdf",
                use_container_width=True
            )
        else:
            st.warning("PDF no disponible")
    
    with col2:
        # Descargar CSV detallado
        if resultado.get('csv_content'):
            st.download_button(
                label="📊 Descargar CSV Detallado",
                data=resultado['csv_content'],
                file_name=f"eventos_astrologicos_{resultado['consultante_nombre']}.csv",
                mime="text/csv",
                use_container_width=True
            )
        else:
            st.warning("CSV no disponible")
    
    # Información adicional
    with st.expander("📖 Notas importantes"):
        st.write("""
        - **Hyleg**: Punto vital que representa la fuerza de vida según la tradición astrológica
        - **Alcocoden**: Planeta que determina los años potenciales de vida
        - **Direcciones primarias**: Técnica predictiva donde 1° = 1 año
        - Los años potenciales indican períodos críticos, no fechas exactas
        - Este análisis se basa en la tradición de Ben Ragel
        - **NUEVO**: Ahora incluye generación de PDF y CSV completos
        """)

if __name__ == "__main__":
    main()
