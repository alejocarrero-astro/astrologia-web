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
import pytz
from datetime import datetime
import numpy as np

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

    # FUNCIÓN PDF MEJORADA CON GRÁFICO DE CARTA NATAL
    def generar_pdf_completo(self, resultado, events, consultante_nombre, carta_data=None):
        """Genera un PDF completo con gráfico de carta natal"""
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
                f"<b>Consultante:</b> {consultante_nombre}",
                f"<b>Fecha:</b> {resultado['fecha_nacimiento']}",
                f"<b>Hora local:</b> {resultado['hora_local']}",
                f"<b>Zona horaria:</b> UTC{resultado['zona_horaria']:+.1f}",
                f"<b>Latitud GMS:</b> {resultado['latitud_gms'][0]}°{resultado['latitud_gms'][1]}'{resultado['latitud_gms'][2]}\" {resultado['latitud_gms'][3]}",
                f"<b>Longitud GMS:</b> {resultado['longitud_gms'][0]}°{resultado['longitud_gms'][1]}'{resultado['longitud_gms'][2]}\" {resultado['longitud_gms'][3]}",
                f"<b>Genitura:</b> {'DIURNA' if resultado['is_diurnal'] else 'NOCTURNA'}",
                f"<b>Hyleg:</b> {resultado['hyleg_point']} - {resultado['hyleg_mensaje']}",
                f"<b>Alcocoden:</b> {resultado['alcocoden_point']} - {resultado['alcocoden_mensaje']}",
                f"<b>Años potenciales:</b> {resultado['anios_alcocoden']} años - {resultado['mensaje_anios']}"
            ]

            for line in info_lines:
                story.append(Paragraph(line, styles["Body"]))
            story.append(Spacer(1,12))

            # GRÁFICO DE CARTA NATAL (NUEVO)
            if carta_data is not None:
                story.append(Paragraph("<b>CARTA NATAL - GRÁFICO:</b>", styles["BodyBold"]))
                story.append(Spacer(1,6))
                
                # Generar gráfico de carta natal
                fig = self.generar_grafico_carta_natal(carta_data, consultante_nombre)
                if fig is not None:
                    # Guardar figura en buffer
                    img_buffer = io.BytesIO()
                    fig.savefig(img_buffer, format='PNG', dpi=150, bbox_inches='tight')
                    img_buffer.seek(0)
                    
                    # Agregar imagen al PDF
                    img = Image(img_buffer, width=400, height=300)
                    story.append(img)
                    story.append(Spacer(1,12))
                
                # Información de la carta natal
                story.append(Paragraph("<b>INFORMACIÓN DE CARTA NATAL:</b>", styles["BodyBold"]))
                story.append(Spacer(1,6))
                
                # Tabla de posiciones planetarias
                carta_table_data = [["Planeta", "Signo", "Casa", "Elemento", "Longitud"]]
                for planeta, info in carta_data.items():
                    if planeta not in ['ascendente', 'parte_fortuna', 'casas', 'aspectos']:
                        carta_table_data.append([
                            planeta, 
                            info['signo'], 
                            str(info['casa']), 
                            info['elemento'],
                            f"{info['longitud']:.2f}°"
                        ])

                tbl_carta = Table(carta_table_data, hAlign='LEFT')
                story.append(tbl_carta)
                story.append(Spacer(1,12))

            # Estado de combustión
            story.append(Paragraph("<b>ESTADO DE COMBUSTIÓN DE LOS PLANETAS:</b>", styles["BodyBold"]))
            story.append(Spacer(1,6))

            combustion_data = [["Planeta", "Longitud", "Signo", "Casa", "Estado", "Separación Sol"]]
            for planeta in ["Sun", "Moon", "Mercury", "Venus", "Mars", "Jupiter", "Saturn"]:
                if planeta in resultado['natal_pos']:
                    estado, separacion = self.obtener_estado_combustion(planeta, resultado['natal_pos'][planeta], resultado['natal_pos']["Sun"])
                    signo = self.obtener_signo(resultado['natal_pos'][planeta])
                    casa = self.obtener_casa(resultado['natal_pos'][planeta], resultado['houses'])
                    combustion_data.append([
                        planeta, 
                        f"{resultado['natal_pos'][planeta]:.2f}°", 
                        signo, 
                        str(casa),
                        estado, 
                        f"{separacion:.2f}°" if planeta != "Sun" else "N/A"
                    ])

            tbl = Table(combustion_data, hAlign='LEFT')
            story.append(tbl)
            story.append(Spacer(1,12))

            # Puntos principales
            story.append(Paragraph("<b>PUNTOS PRINCIPALES:</b>", styles["BodyBold"]))
            story.append(Spacer(1,6))

            points_data = [["Punto", "Longitud", "Signo", "Casa"]]
            for punto, longitud in resultado['points'].items():
                signo = self.obtener_signo(longitud)
                casa = self.obtener_casa(longitud, resultado['houses'])
                points_data.append([punto, f"{longitud:.2f}°", signo, str(casa)])

            tbl_points = Table(points_data, hAlign='LEFT')
            story.append(tbl_points)
            story.append(Spacer(1,12))

            # Posiciones planetarias
            story.append(Paragraph("<b>POSICIONES PLANETARIAS NATALES:</b>", styles["BodyBold"]))
            story.append(Spacer(1,6))

            planets_data = [["Planeta", "Longitud", "Signo", "Casa", "Estado Combustión"]]
            for planeta, longitud in resultado['natal_pos'].items():
                signo = self.obtener_signo(longitud)
                casa = self.obtener_casa(longitud, resultado['houses'])
                estado, separacion = self.obtener_estado_combustion(planeta, longitud, resultado['natal_pos']["Sun"])
                planets_data.append([planeta, f"{longitud:.2f}°", signo, str(casa), estado])

            tbl_planets = Table(planets_data, hAlign='LEFT', repeatRows=1)
            story.append(tbl_planets)
            story.append(Spacer(1,12))

            # EVENTOS PRINCIPALES HASTA 100 AÑOS
            story.append(Paragraph("<b>PRÓXIMOS EVENTOS PRINCIPALES (hasta 100 años):</b>", styles["BodyBold"]))
            story.append(Spacer(1,6))

            priority_aspects = ["Opposition", "Square", "Conjunction", "Trine", "Sextile"]
            events_hasta_100 = [e for e in events if e['year'] <= 100 and e['aspect'] in priority_aspects]

            def aspect_priority(aspect_name):
                priority_order = {"Opposition": 1, "Square": 2, "Conjunction": 3, "Trine": 4, "Sextile": 5}
                return priority_order.get(aspect_name, 6)

            events_sorted = sorted(events_hasta_100, key=lambda x: (x['year'], aspect_priority(x['aspect'])))

            events_data = [["Año", "Edad", "Punto", "Aspecto", "Planeta", "Precisión"]]
            for e in events_sorted[:50]:  # Limitar a 50 eventos para PDF
                edad_aproximada = int(resultado['fecha_nacimiento'][:4]) + e['year']
                events_data.append([
                    str(e['year']),
                    str(edad_aproximada),
                    e['point'],
                    e['aspect'],
                    e['target'],
                    f"{e['sep']:.3f}°"
                ])

            tbl_events = Table(events_data, hAlign='LEFT', repeatRows=1)
            story.append(tbl_events)
            story.append(Spacer(1,12))

            # INTERPRETACIÓN POR BIENIOS
            story.append(Paragraph("<b>INTERPRETACIÓN POR BIENIOS (períodos de 2 años):</b>", styles["BodyBold"]))
            story.append(Spacer(1,8))
            
            story.append(Paragraph(f"<b>Período crítico primario:</b> {resultado['anios_alcocoden']} años (alrededor del año {int(resultado['fecha_nacimiento'][:4]) + resultado['anios_alcocoden']})", styles["Body"]))
            story.append(Paragraph(f"<b>Estado del Alcocoden:</b> {resultado['mensaje_anios']}", styles["Body"]))
            story.append(Spacer(1,8))
            
            bienios = defaultdict(list)
            for e in events:
                if e['year'] <= 100:
                    bienio = (e["year"] // 2) * 2
                    bienios[bienio].append(e)

            for bienio in sorted(bienios.keys()):
                bucket = bienios[bienio]
                
                tensions = [x for x in bucket if x["aspect"] in ("Opposition", "Square")]
                harmonies = [x for x in bucket if x["aspect"] in ("Trine", "Sextile")]
                conjs = [x for x in bucket if x["aspect"] == "Conjunction"]
                
                if tensions or harmonies or conjs:
                    tension_set = set()
                    harmony_set = set()
                    conj_set = set()
                    
                    for t in tensions:
                        tension_set.add(f"{t['point']}→{t['target']}")
                    for h in harmonies:
                        harmony_set.add(f"{h['point']}→{h['target']}")
                    for c in conjs:
                        conj_set.add(f"{c['point']}→{c['target']}")
                    
                    bienio_text = f"<b>Bienio {bienio}-{bienio+1}:</b> "
                    parts = []
                    
                    if tensions:
                        parts.append(f"{len(tensions)} tensos")
                    if harmonies:
                        parts.append(f"{len(harmonies)} armónicos")
                    if conjs:
                        parts.append(f"{len(conjs)} conjunciones")
                    
                    bienio_text += "; ".join(parts)
                    story.append(Paragraph(bienio_text, styles["Body"]))
                    story.append(Spacer(1,4))

            # Nota final
            story.append(Spacer(1,12))
            story.append(Paragraph("<b>NOTA IMPORTANTE:</b>", styles["BodyBold"]))
            story.append(Paragraph("Este análisis se basa en las direcciones primarias (1° = 1 año) y el cálculo tradicional de Hyleg y Alcocoden según Ben Ragel.", styles["Body"]))
            story.append(Paragraph("La Parte de la Fortuna se calcula con la fórmula tradicional corregida: Ascendente + Luna - Sol", styles["Body"]))
            if carta_data is not None:
                story.append(Paragraph("<b>INCLUYE:</b> Gráfico e información completa de la carta natal.", styles["Body"]))
            story.append(Paragraph("Los años potenciales indican períodos críticos, no fechas exactas de eventos.", styles["Body"]))

            # Construir el PDF
            doc.build(story)
            pdf_bytes = buffer.getvalue()
            buffer.close()
            
            return pdf_bytes
            
        except Exception as e:
            st.error(f"Error al generar PDF: {str(e)}")
            return None

    def generar_grafico_carta_natal(self, carta_data, consultante_nombre):
        """Genera un gráfico de carta natal simplificado"""
        try:
            fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(15, 6))
            
            # Gráfico 1: Planetas por signo
            signos = {}
            for planeta, info in carta_data.items():
                if planeta not in ['ascendente', 'parte_fortuna', 'casas', 'aspectos']:
                    signo = info['signo']
                    if signo not in signos:
                        signos[signo] = []
                    signos[signo].append(planeta)
            
            # Preparar datos para el gráfico de barras
            signos_nombres = list(signos.keys())
            conteo_signos = [len(signos[signo]) for signo in signos_nombres]
            
            colors = ['#FF6B6B', '#4ECDC4', '#45B7D1', '#96CEB4', '#FFEAA7', '#DDA0DD',
                     '#98D8C8', '#F7DC6F', '#BB8FCE', '#85C1E9', '#F8C471', '#82E0AA']
            
            bars = ax1.bar(signos_nombres, conteo_signos, color=colors[:len(signos_nombres)])
            ax1.set_title(f'Planetas por Signo - {consultante_nombre}', fontsize=14, fontweight='bold')
            ax1.set_ylabel('Número de Planetas')
            ax1.tick_params(axis='x', rotation=45)
            
            # Agregar valores en las barras
            for bar, count in zip(bars, conteo_signos):
                height = bar.get_height()
                ax1.text(bar.get_x() + bar.get_width()/2., height + 0.1,
                        f'{count}', ha='center', va='bottom')
            
            # Gráfico 2: Planetas por casa
            casas = {}
            for planeta, info in carta_data.items():
                if planeta not in ['ascendente', 'parte_fortuna', 'casas', 'aspectos']:
                    casa = info['casa']
                    if casa not in casas:
                        casas[casa] = []
                    casas[casa].append(planeta)
            
            # Preparar datos para el gráfico de casas
            casas_numeros = list(casas.keys())
            conteo_casas = [len(casas[casa]) for casa in casas_numeros]
            
            bars2 = ax2.bar([f'Casa {c}' for c in casas_numeros], conteo_casas, color='lightblue')
            ax2.set_title('Planetas por Casa', fontsize=14, fontweight='bold')
            ax2.set_ylabel('Número de Planetas')
            ax2.tick_params(axis='x', rotation=45)
            
            # Agregar valores en las barras
            for bar, count in zip(bars2, conteo_casas):
                height = bar.get_height()
                ax2.text(bar.get_x() + bar.get_width()/2., height + 0.1,
                        f'{count}', ha='center', va='bottom')
            
            plt.tight_layout()
            return fig
            
        except Exception as e:
            st.error(f"Error al generar gráfico de carta natal: {e}")
            return None

    # Función para generar CSV detallado
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
            
            # Crear gráfico de línea de tiempo
            fig = self.crear_grafico_tiempo(events, consultante_nombre)
            
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
                'figura': fig
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

# ----------------------------- CARTA NATAL INTEGRADA (SOLO pyswisseph) -----------------------------

class CartaNatalIntegrada:
    def __init__(self):
        self.analizador_web = AnalisisAstrologicoWeb()
    
    def generar_carta_natal_completa(self, fecha_nacimiento, hora_local, zona_horaria, 
                                   consultante_nombre, latitud_gms, longitud_gms):
        """Genera una carta natal completa usando pyswisseph"""
        
        try:
            # Usar el análisis astrológico existente como base
            resultado_base = self.analizador_web.realizar_analisis_completo(
                fecha_nacimiento, hora_local, zona_horaria,
                consultante_nombre, latitud_gms, longitud_gms
            )
            
            if not resultado_base['success']:
                return {'success': False, 'error': resultado_base['error']}
            
            # Extraer datos para la carta natal
            natal_pos = resultado_base['natal_pos']
            houses = resultado_base['houses']
            asc = resultado_base['asc']
            part_fort = resultado_base['part_fort']
            
            # Calcular información adicional para la carta natal
            carta_data = self._calcular_info_carta_natal(natal_pos, houses, asc, part_fort)
            
            # Generar PDF con gráfico de carta natal
            pdf_bytes = self.analizador_web.generar_pdf_completo(
                resultado_base, 
                resultado_base['events'], 
                consultante_nombre, 
                carta_data
            )
            
            # Combinar resultados
            resultado_completo = {
                'success': True,
                'analisis_base': resultado_base,
                'carta_natal': carta_data,
                'interpretaciones': self._generar_interpretaciones(carta_data, resultado_base),
                'pdf_bytes': pdf_bytes
            }
            
            return resultado_completo
            
        except Exception as e:
            return {'success': False, 'error': str(e)}
    
    def _calcular_info_carta_natal(self, natal_pos, houses, asc, part_fort):
        """Calcula información específica para la carta natal usando pyswisseph"""
        
        carta = {}
        
        # Signos y casas para cada planeta
        for planeta, longitud in natal_pos.items():
            signo = self.analizador_web.obtener_signo(longitud)
            casa = self.analizador_web.obtener_casa(longitud, houses)
            
            carta[planeta] = {
                'longitud': longitud,
                'signo': signo,
                'casa': casa,
                'elemento': self._obtener_elemento_signo(signo),
                'cualidad': self._obtener_cualidad_signo(signo),
                'estado_combustion': self.analizador_web.obtener_estado_combustion(
                    planeta, longitud, natal_pos["Sun"]
                )
            }
        
        # Información del Ascendente
        signo_asc = self.analizador_web.obtener_signo(asc)
        regente_asc, _ = self.analizador_web.obtener_regente_signo(asc)
        
        carta['ascendente'] = {
            'longitud': asc,
            'signo': signo_asc,
            'regente': regente_asc,
            'casa': 1
        }
        
        # Información de la Parte de la Fortuna
        signo_fortuna = self.analizador_web.obtener_signo(part_fort)
        casa_fortuna = self.analizador_web.obtener_casa(part_fort, houses)
        
        carta['parte_fortuna'] = {
            'longitud': part_fort,
            'signo': signo_fortuna,
            'casa': casa_fortuna
        }
        
        # Casas astrológicas
        carta['casas'] = {}
        for i in range(12):
            cuspide = houses[i]
            signo_casa = self.analizador_web.obtener_signo(cuspide)
            carta['casas'][i+1] = {
                'cuspide': cuspide,
                'signo': signo_casa
            }
        
        # Aspectos importantes
        carta['aspectos'] = self._calcular_aspectos_importantes(natal_pos)
        
        return carta
    
    def _obtener_elemento_signo(self, signo):
        elementos = {
            'Aries': 'Fuego', 'Tauro': 'Tierra', 'Géminis': 'Aire', 'Cáncer': 'Agua',
            'Leo': 'Fuego', 'Virgo': 'Tierra', 'Libra': 'Aire', 'Escorpio': 'Agua',
            'Sagitario': 'Fuego', 'Capricornio': 'Tierra', 'Acuario': 'Aire', 'Piscis': 'Agua'
        }
        return elementos.get(signo, 'Desconocido')
    
    def _obtener_cualidad_signo(self, signo):
        cualidades = {
            'Aries': 'Cardinal', 'Tauro': 'Fijo', 'Géminis': 'Mutable',
            'Cáncer': 'Cardinal', 'Leo': 'Fijo', 'Virgo': 'Mutable',
            'Libra': 'Cardinal', 'Escorpio': 'Fijo', 'Sagitario': 'Mutable',
            'Capricornio': 'Cardinal', 'Acuario': 'Fijo', 'Piscis': 'Mutable'
        }
        return cualidades.get(signo, 'Desconocido')
    
    def _calcular_aspectos_importantes(self, natal_pos):
        """Calcula los aspectos más importantes entre planetas usando pyswisseph"""
        aspectos = []
        
        planetas = list(natal_pos.keys())
        
        for i in range(len(planetas)):
            for j in range(i + 1, len(planetas)):
                planeta1 = planetas[i]
                planeta2 = planetas[j]
                
                lon1 = natal_pos[planeta1]
                lon2 = natal_pos[planeta2]
                
                for aspecto, angulo in self.analizador_web.ASPECTS.items():
                    separacion = self.analizador_web.diferencia_grados(lon1, lon2)
                    distancia_al_aspecto = abs(separacion - angulo)
                    
                    if distancia_al_aspecto > 180:
                        distancia_al_aspecto = abs(distancia_al_aspecto - 360)
                    
                    if distancia_al_aspecto <= 3.0:  # Orb más amplio para aspectos natales
                        aspectos.append({
                            'planeta1': planeta1,
                            'planeta2': planeta2,
                            'aspecto': aspecto,
                            'separacion': separacion,
                            'precision': distancia_al_aspecto,
                            'color': self.analizador_web.ASPECT_COLORS.get(aspecto, "#333333")
                        })
        
        return aspectos
    
    def _generar_interpretaciones(self, carta_data, resultado_base):
        """Genera interpretaciones básicas para la carta natal"""
        
        interpretaciones = {}
        
        # Interpretación del Sol
        sol_info = carta_data.get('Sun', {})
        if sol_info:
            interpretaciones['sol'] = self._interpretar_sol(
                sol_info['signo'], 
                sol_info['casa'],
                resultado_base.get('is_diurnal', True)
            )
        
        # Interpretación de la Luna
        luna_info = carta_data.get('Moon', {})
        if luna_info:
            interpretaciones['luna'] = self._interpretar_luna(
                luna_info['signo'],
                luna_info['casa']
            )
        
        # Interpretación del Ascendente
        asc_info = carta_data.get('ascendente', {})
        if asc_info:
            interpretaciones['ascendente'] = self._interpretar_ascendente(
                asc_info['signo'],
                asc_info['regente']
            )
        
        # Síntesis general
        interpretaciones['sintesis'] = self._generar_sintesis(
            sol_info, luna_info, asc_info, resultado_base
        )
        
        return interpretaciones
    
    def _interpretar_sol(self, signo, casa, es_diurno):
        interpretaciones_sol = {
            'Aries': "Energía vital fuerte, espíritu pionero, iniciativa personal",
            'Tauro': "Constancia, búsqueda de estabilidad, valores prácticos",
            'Géminis': "Comunicación, versatilidad, curiosidad intelectual",
            'Cáncer': "Sensibilidad, protección, conexión emocional profunda",
            'Leo': "Creatividad, expresión personal, necesidad de reconocimiento",
            'Virgo': "Servicio, perfección, análisis detallado",
            'Libra': "Armonía, relaciones, búsqueda de equilibrio",
            'Escorpio': "Intensidad, transformación, profundidad psicológica",
            'Sagitario': "Expansión, filosofía, búsqueda de significado",
            'Capricornio': "Ambición, estructura, disciplina personal",
            'Acuario': "Innovación, libertad, pensamiento original",
            'Piscis': "Inspiración, compasión, conexión espiritual"
        }
        
        base = interpretaciones_sol.get(signo, "Expresión solar única")
        casa_text = f" en casa {casa}" if casa else ""
        diurno_text = " (acentuado por genitura diurna)" if es_diurno else " (matizado por genitura nocturna)"
        
        return base + casa_text + diurno_text
    
    def _interpretar_luna(self, signo, casa):
        interpretaciones_luna = {
            'Aries': "Emociones rápidas, espontáneas, necesidad de acción",
            'Tauro': "Estabilidad emocional, necesidad de seguridad material",
            'Géminis': "Variedad emocional, necesidad de comunicación y cambio",
            'Cáncer': "Profundidad emocional, intuición aguda, apego familiar",
            'Leo': "Dramatismo emocional, necesidad de reconocimiento afectivo",
            'Virgo': "Emociones prácticas, necesidad de utilidad y orden",
            'Libra': "Armonía emocional, necesidad de equilibrio en relaciones",
            'Escorpio': "Intensidad emocional, pasión, transformación",
            'Sagitario': "Optimismo emocional, necesidad de libertad y aventura",
            'Capricornio': "Control emocional, necesidad de estructura y respeto",
            'Acuario': "Objetividad emocional, independencia, idealismo",
            'Piscis': "Sensibilidad emocional, compasión, imaginación"
        }
        
        base = interpretaciones_luna.get(signo, "Naturaleza emocional única")
        casa_text = f" en casa {casa}" if casa else ""
        
        return base + casa_text
    
    def _interpretar_ascendente(self, signo, regente):
        interpretaciones_asc = {
            'Aries': "Personalidad dinámica, emprendedora, directa",
            'Tauro': "Aproximación estable, perseverante, sensorial",
            'Géminis': "Comunicativo, adaptable, mentalmente activo",
            'Cáncer': "Sensible, protector, intuitivo",
            'Leo': "Magnánimo, creativo, expresivo",
            'Virgo': "Analítico, servicial, perfeccionista",
            'Libra': "Diplomático, armonioso, social",
            'Escorpio': "Intenso, transformador, perceptivo",
            'Sagitario': "Optimista, aventurero, filosófico",
            'Capricornio': "Práctico, ambicioso, responsable",
            'Acuario': "Innovador, independiente, humanitario",
            'Piscis': "Sensible, inspirado, compasivo"
        }
        
        base = interpretaciones_asc.get(signo, "Expresión personal única")
        regente_text = f", regido por {regente}" if regente else ""
        
        return base + regente_text
    
    def _generar_sintesis(self, sol_info, luna_info, asc_info, resultado_base):
        """Genera una síntesis interpretativa general"""
        
        sintesis = []
        
        # Síntesis basada en elementos
        elemento_sol = sol_info.get('elemento', '')
        elemento_luna = luna_info.get('elemento', '')
        
        if elemento_sol == elemento_luna:
            sintesis.append(f"Armonía elemental: Sol y Luna en {elemento_sol}")
        else:
            sintesis.append(f"Equilibrio entre {elemento_sol} (Sol) y {elemento_luna} (Luna)")
        
        # Síntesis basada en Hyleg y Alcocoden
        hyleg = resultado_base.get('hyleg_point', '')
        alcocoden = resultado_base.get('alcocoden_point', '')
        anios = resultado_base.get('anios_alcocoden', 0)
        
        sintesis.append(f"Vitalidad: Hyleg en {hyleg}, Alcocoden en {alcocoden} ({anios} años potenciales)")
        
        # Síntesis basada en casas
        casa_sol = sol_info.get('casa', 0)
        if casa_sol in [1, 4, 7, 10]:
            sintesis.append("Énfasis en casas angulares: fuerte impacto en el mundo exterior")
        elif casa_sol in [2, 5, 8, 11]:
            sintesis.append("Énfasis en casas sucedentes: desarrollo de recursos y relaciones")
        else:
            sintesis.append("Énfasis en casas cadentes: aprendizaje y transformación interna")
        
        return " | ".join(sintesis)

# ----------------------------- FUNCIONES DE VISUALIZACIÓN -----------------------------

def mostrar_carta_natal(resultado):
    """Muestra los resultados de la carta natal usando solo pyswisseph"""
    
    st.success("✅ Carta Natal generada exitosamente!")
    
    carta_data = resultado['carta_natal']
    interpretaciones = resultado['interpretaciones']
    analisis_base = resultado['analisis_base']
    
    # Información básica
    st.header("📋 Información de la Carta Natal")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("Planetas y Posiciones")
        for planeta, info in carta_data.items():
            if planeta not in ['ascendente', 'parte_fortuna', 'casas', 'aspectos']:
                with st.expander(f"{planeta} - {info['signo']} (Casa {info['casa']})"):
                    st.write(f"**Longitud:** {info['longitud']:.2f}°")
                    st.write(f"**Elemento:** {info['elemento']}")
                    st.write(f"**Cualidad:** {info['cualidad']}")
                    estado, separacion = info['estado_combustion']
                    st.write(f"**Estado:** {estado}")
                    if planeta != "Sun":
                        st.write(f"**Separación del Sol:** {separacion:.2f}°")
    
    with col2:
        st.subheader("Puntos Importantes")
        
        # Ascendente
        asc = carta_data.get('ascendente', {})
        if asc:
            st.info(f"**Ascendente:** {asc['signo']}")
            st.write(f"Regente: {asc['regente']}")
            st.write(f"Longitud: {asc['longitud']:.2f}°")
        
        # Parte de la Fortuna
        fortuna = carta_data.get('parte_fortuna', {})
        if fortuna:
            st.info(f"**Parte de la Fortuna:** {fortuna['signo']}")
            st.write(f"Casa: {fortuna['casa']}")
            st.write(f"Longitud: {fortuna['longitud']:.2f}°")
        
        # Interpretaciones
        st.subheader("Interpretaciones Clave")
        for punto, interpretacion in interpretaciones.items():
            if punto != 'sintesis':
                st.write(f"**{punto.capitalize()}:** {interpretacion}")
        
        # Síntesis
        if 'sintesis' in interpretaciones:
            st.subheader("💫 Síntesis")
            st.info(interpretaciones['sintesis'])
    
    # Aspectos
    st.header("🔗 Aspectos Importantes")
    aspectos = carta_data.get('aspectos', [])
    
    if aspectos:
        # Mostrar aspectos más precisos primero
        aspectos_ordenados = sorted(aspectos, key=lambda x: x['precision'])
        
        col1, col2 = st.columns(2)
        with col1:
            st.subheader("Aspectos Mayores")
            for aspecto in aspectos_ordenados[:8]:
                if aspecto['aspecto'] in ["Conjunction", "Opposition", "Square", "Trine"]:
                    st.write(
                        f"**{aspecto['planeta1']} {aspecto['aspecto']} {aspecto['planeta2']}** "
                        f"({aspecto['separacion']:.1f}°, precisión: {aspecto['precision']:.2f}°)"
                    )
        
        with col2:
            st.subheader("Aspectos Menores")
            for aspecto in aspectos_ordenados[:8]:
                if aspecto['aspecto'] in ["Sextile"]:
                    st.write(
                        f"**{aspecto['planeta1']} {aspecto['aspecto']} {aspecto['planeta2']}** "
                        f"({aspecto['separacion']:.1f}°, precisión: {aspecto['precision']:.2f}°)"
                    )
    else:
        st.info("No se encontraron aspectos significativos dentro del orb de 3°")
    
    # Casas
    st.header("🏠 Casas Astrológicas")
    casas = carta_data.get('casas', {})
    
    if casas:
        cols = st.columns(3)
        for i, (num_casa, info_casa) in enumerate(casas.items()):
            with cols[i % 3]:
                st.write(f"**Casa {num_casa}:** {info_casa['signo']}")
                st.write(f"Cúspide: {info_casa['cuspide']:.2f}°")

def mostrar_analisis_integral(resultado_base, resultado_carta):
    """Muestra el análisis integral combinado usando solo pyswisseph"""
    
    st.success("✅ Análisis Integral completado!")
    
    # Crear pestañas para organizar la información
    tab1, tab2, tab3 = st.tabs(["🎯 Hyleg y Alcocoden", "📊 Carta Natal", "🌌 Visión Integral"])
    
    with tab1:
        mostrar_resultados(resultado_base)
    
    with tab2:
        mostrar_carta_natal(resultado_carta)
    
    with tab3:
        st.header("🌌 Síntesis Integral")
        
        # Combinar información clave de ambos análisis
        col1, col2 = st.columns(2)
        
        with col1:
            st.subheader("Puntos Vitales")
            st.write(f"**Hyleg:** {resultado_base['hyleg_point']}")
            st.write(f"**Alcocoden:** {resultado_base['alcocoden_point']}")
            st.write(f"**Años potenciales:** {resultado_base['anios_alcocoden']}")
            
            # Interpretación del Sol desde la carta natal
            sol_info = resultado_carta['carta_natal'].get('Sun', {})
            if sol_info:
                st.write(f"**Sol en:** {sol_info['signo']} (casa {sol_info['casa']})")
                st.write(f"**Elemento:** {sol_info['elemento']}")
        
        with col2:
            st.subheader("Características Personales")
            asc_info = resultado_carta['carta_natal'].get('ascendente', {})
            if asc_info:
                st.write(f"**Ascendente:** {asc_info['signo']}")
                st.write(f"**Regente:** {asc_info['regente']}")
            
            luna_info = resultado_carta['carta_natal'].get('Moon', {})
            if luna_info:
                st.write(f"**Luna en:** {luna_info['signo']} (casa {luna_info['casa']})")
                st.write(f"**Elemento:** {luna_info['elemento']}")
        
        # Recomendaciones basadas en el análisis combinado
        st.subheader("💫 Recomendaciones Integrales")
        
        recomendaciones = []
        
        # Recomendación basada en Hyleg
        hyleg = resultado_base['hyleg_point']
        if hyleg == "Sun":
            recomendaciones.append("**Fortalece tu energía vital** a través de la expresión creativa y el reconocimiento personal")
        elif hyleg == "Moon":
            recomendaciones.append("**Cuida tu mundo emocional** y busca entornos que te brinden seguridad emocional")
        elif hyleg == "Ascendente":
            recomendaciones.append("**Desarrolla tu identidad personal** y trabaja en tu autoexpresión")
        elif hyleg == "Fortuna":
            recomendaciones.append("**Aprovecha los ciclos de fortuna** y desarrolla tus talentos naturales")
        
        # Recomendación basada en Alcocoden
        alcocoden = resultado_base['alcocoden_point']
        anios = resultado_base['anios_alcocoden']
        recomendaciones.append(f"**Período crítico alrededor de los {anios} años** - momento para reevaluar y transformar")
        
        # Recomendación basada en elementos
        sol_info = resultado_carta['carta_natal'].get('Sun', {})
        elemento_sol = sol_info.get('elemento', '')
        if elemento_sol == 'Fuego':
            recomendaciones.append("**Canaliza tu energía** con actividad física y proyectos inspiradores")
        elif elemento_sol == 'Tierra':
            recomendaciones.append("**Estabilidad y paciencia** - construye bases sólidas paso a paso")
        elif elemento_sol == 'Aire':
            recomendaciones.append("**Comunica tus ideas** - el intercambio intelectual te vitaliza")
        elif elemento_sol == 'Agua':
            recomendaciones.append("**Cuida tu sensibilidad** - busca equilibrio entre dar y recibir apoyo emocional")
        
        for rec in recomendaciones:
            st.write(f"• {rec}")

# ----------------------------- INTERFAZ STREAMLIT AMPLIADA -----------------------------

def main_ampliada():
    """Versión ampliada del main para incluir carta natal usando solo pyswisseph"""
    
    st.set_page_config(
        page_title="Astrología Integral - Hyleg & Carta Natal",
        page_icon="♋",
        layout="wide"
    )
    
    st.title("♋ Astrología Integral - Hyleg & Carta Natal")
    st.markdown("---")
    
    # Sidebar para selección de módulo
    with st.sidebar:
        st.header("🔮 Módulos de Análisis")
        
        modulo = st.radio(
            "Selecciona el tipo de análisis:",
            ["🎯 Hyleg y Alcocoden", "📊 Carta Natal Completa", "🌌 Análisis Integral"],
            index=0
        )
        
        st.markdown("---")
        st.header("📊 Datos de Nacimiento")
        
        # Los mismos inputs de datos que ya tienes...
        consultante_nombre = st.text_input("Nombre del consultante", "Alejo")
        
        col1, col2 = st.columns(2)
        with col1:
            fecha_nacimiento = st.text_input("Fecha (YYYY-MM-DD)", "1981-07-15")
        with col2:
            hora_local = st.text_input("Hora local (HH:MM)", "05:16")
        
        zona_horaria = st.number_input("Zona horaria", value=-4.0, step=0.5)
        
        st.subheader("📍 Coordenadas Geográficas")
        
        # ... (mantener tus inputs de coordenadas existentes)
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
    
    # Botón de análisis según el módulo seleccionado
    analizar_text = ""
    if modulo == "🎯 Hyleg y Alcocoden":
        analizar_text = "🎯 Ejecutar Análisis de Hyleg y Alcocoden"
    elif modulo == "📊 Carta Natal Completa":
        analizar_text = "📊 Generar Carta Natal Completa"
    else:
        analizar_text = "🌌 Ejecutar Análisis Integral Completo"
    
    if st.button(analizar_text, type="primary", use_container_width=True):
        with st.spinner("Realizando cálculos astrológicos... Esto puede tomar unos segundos."):
            latitud_gms = (lat_grados, lat_minutos, lat_segundos, lat_direccion)
            longitud_gms = (lon_grados, lon_minutos, lon_segundos, lon_direccion)
            
            if modulo == "🎯 Hyleg y Alcocoden":
                # Usar tu análisis original
                analizador = AnalisisAstrologicoWeb()
                resultado = analizador.realizar_analisis_completo(
                    fecha_nacimiento, hora_local, zona_horaria, 
                    consultante_nombre, latitud_gms, longitud_gms
                )
                
                if resultado['success']:
                    # Generar PDF para Hyleg y Alcocoden
                    pdf_bytes = analizador.generar_pdf_completo(
                        resultado, resultado['events'], consultante_nombre
                    )
                    resultado['pdf_bytes'] = pdf_bytes
                    
                    mostrar_resultados(resultado)
                else:
                    st.error(f"❌ Error en el análisis: {resultado['error']}")
            
            elif modulo == "📊 Carta Natal Completa":
                # Usar el nuevo análisis de carta natal
                carta_natal = CartaNatalIntegrada()
                resultado = carta_natal.generar_carta_natal_completa(
                    fecha_nacimiento, hora_local, zona_horaria,
                    consultante_nombre, latitud_gms, longitud_gms
                )
                
                if resultado['success']:
                    mostrar_carta_natal(resultado)
                else:
                    st.error(f"❌ Error en la carta natal: {resultado['error']}")
            
            else:  # Análisis integral
                # Ejecutar ambos análisis
                analizador_web = AnalisisAstrologicoWeb()
                carta_natal = CartaNatalIntegrada()
                
                resultado_base = analizador_web.realizar_analisis_completo(
                    fecha_nacimiento, hora_local, zona_horaria,
                    consultante_nombre, latitud_gms, longitud_gms
                )
                
                if resultado_base['success']:
                    resultado_carta = carta_natal.generar_carta_natal_completa(
                        fecha_nacimiento, hora_local, zona_horaria,
                        consultante_nombre, latitud_gms, longitud_gms
                    )
                    
                    if resultado_carta['success']:
                        mostrar_analisis_integral(resultado_base, resultado_carta)
                    else:
                        st.error(f"❌ Error en carta natal: {resultado_carta['error']}")
                else:
                    st.error(f"❌ Error en análisis base: {resultado_base['error']}")

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
    
    # Descargas
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
            st.info("✅ PDF incluye: Información completa, tablas detalladas, eventos hasta 100 años, interpretación por bienios")
        else:
            st.warning("PDF no disponible")
    
    with col2:
        # Descargar CSV detallado
        if resultado.get('events'):
            csv_content = AnalisisAstrologicoWeb().generar_csv_detallado(resultado['events'], resultado['consultante_nombre'])
            st.download_button(
                label="📊 Descargar CSV Detallado",
                data=csv_content,
                file_name=f"eventos_astrologicos_{resultado['consultante_nombre']}.csv",
                mime="text/csv",
                use_container_width=True
            )
            st.info("✅ CSV incluye: Todos los eventos astrológicos con años, fechas y precisiones")
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
        - **NUEVO**: PDF completo incluye toda la información de la versión desktop
        - **Incluye**: Tablas detalladas, interpretación por bienios, eventos hasta 100 años
        """)

# ============================= LLAMADO FINAL ACTUALIZADO =============================
if __name__ == "__main__":
    main_ampliada()