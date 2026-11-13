#!/usr/bin/env python3
"""Robô do Radar das Licitações (Licittapar).

Roda sozinho todo dia no GitHub Actions, sem o Claude:
  1. busca notícias dos últimos dias no Google Notícias (RSS gratuito);
  2. descarta o que não é licitação/contratação pública e o que já está no Radar;
  3. identifica órgão, estado e categoria;
  4. escreve o resumo (com a IA gratuita do Google Gemini, se houver chave;
     sem chave, usa o trecho de abertura publicado pela própria fonte);
  5. grava noticias.json (máx. 80 notícias) — o site lê esse arquivo.
"""
import html
import json
import os
import re
import sys
import time
import unicodedata
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from urllib.parse import quote_plus, urlparse

import requests
from concurrent.futures import ThreadPoolExecutor

_POOL = ThreadPoolExecutor(max_workers=2)

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ARQ = os.path.join(BASE, "noticias.json")
TZ = timezone(timedelta(hours=-3))  # Brasília
HOJE = datetime.now(TZ).date()
DIAS = int(os.environ.get("RADAR_DIAS", "3"))
MAX_NOVAS = int(os.environ.get("RADAR_MAX_NOVAS", "10"))
MAX_TOTAL = 80
UA = {"User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Safari/537.36",
      "Accept-Language": "pt-BR,pt;q=0.9"}

# ---------------------------------------------------------------- buscas
BUSCAS = [
    '"Tribunal de Contas" suspende licitação',
    'TCE suspende pregão',
    'TCE suspende licitação prefeitura',
    'TCM suspende licitação',
    'TCU licitação acórdão',
    'TCU contratação irregularidade',
    'liminar suspende licitação',
    '"mandado de segurança" licitação',
    'Justiça suspende pregão',
    'desembargador suspende edital licitação',
    'STJ licitação',
    'operação fraude licitação',
    'Polícia Federal operação licitação prefeitura',
    'Gaeco fraude licitação',
    'TCE/SC licitação',
    '"Tribunal de Contas de Santa Catarina" licitação',
    '"Lei 14.133" nova regra',
    'decreto licitações contratações públicas',
]

UFS = {
    "acre": "AC", "alagoas": "AL", "amapa": "AP", "amazonas": "AM", "bahia": "BA",
    "ceara": "CE", "distrito federal": "DF", "espirito santo": "ES", "goias": "GO",
    "maranhao": "MA", "mato grosso do sul": "MS", "mato grosso": "MT",
    "minas gerais": "MG", "para": "PA", "paraiba": "PB", "parana": "PR",
    "pernambuco": "PE", "piaui": "PI", "rio de janeiro": "RJ",
    "rio grande do norte": "RN", "rio grande do sul": "RS", "rondonia": "RO",
    "roraima": "RR", "santa catarina": "SC", "sao paulo": "SP", "sergipe": "SE",
    "tocantins": "TO",
}
SIGLAS = set(UFS.values())
CAPITAIS = {
    "rio branco": "AC", "maceio": "AL", "macapa": "AP", "manaus": "AM",
    "salvador": "BA", "fortaleza": "CE", "brasilia": "DF", "vitoria": "ES",
    "goiania": "GO", "sao luis": "MA", "cuiaba": "MT", "campo grande": "MS",
    "belo horizonte": "MG", "belem": "PA", "joao pessoa": "PB", "curitiba": "PR",
    "recife": "PE", "teresina": "PI", "natal": "RN", "porto alegre": "RS",
    "porto velho": "RO", "boa vista": "RR", "florianopolis": "SC",
    "aracaju": "SE", "palmas": "TO",
}
GENTILICOS = {
    "gaucho": "RS", "catarinense": "SC", "paranaense": "PR", "paulista": "SP", "mineiro": "MG",
    "baiano": "BA", "fluminense": "RJ", "carioca": "RJ", "goiano": "GO", "capixaba": "ES",
    "potiguar": "RN", "pernambucano": "PE", "cearense": "CE", "maranhense": "MA",
    "paraense": "PA", "amazonense": "AM", "tocantinense": "TO", "sul-mato-grossense": "MS",
    "mato-grossense": "MT", "sergipano": "SE", "alagoano": "AL", "paraibano": "PB",
    "piauiense": "PI", "rondoniense": "RO", "roraimense": "RR", "acreano": "AC", "amapaense": "AP",
}
# veículos regionais frequentes → estado (ajuda quando a notícia não diz o estado)
FONTE_UF = {
    "nd+": "SC", "ndmais": "SC", "nsc total": "SC", "sctodod": "SC", "sctd": "SC",
    "sergio oliveira": "SC", "olhar direto": "MT", "folhamax": "MT", "momento mt": "MT",
    "a tarde": "BA", "farol da bahia": "BA", "jornal da chapada": "BA",
    "gazeta do cerrado": "TO", "jd1": "MS", "campo grande": "MS", "marilia": "SP",
    "jornal cruzeiro do sul": "SP", "gaucha": "RS", "gzh": "RS", "zero hora": "RS",
    "correio do povo": "RS", "o popular": "GO", "portal 6": "GO", "estado de minas": "MG",
    "o tempo": "MG", "gazeta do povo": "PR", "bem parana": "PR", "diario do nordeste": "CE",
    "o povo": "CE", "jornal do commercio": "PE", "folha de pernambuco": "PE",
    "a gazeta": "ES", "folha de boa vista": "RR", "roraima em foco": "RR",
    "o liberal": "PA", "diario do para": "PA", "imirante": "MA", "o estado ma": "MA",
    "tribuna do norte": "RN", "cidadeverde": "PI", "meionorte": "PI", "jornal da paraiba": "PB",
    "a critica": "AM", "acritica": "AM", "rondoniaovivo": "RO", "infonet": "SE",
    "ac24horas": "AC", "selesnafes": "AP", "gazetaweb": "AL", "tnh1": "AL",
}

TEMA = re.compile(r"licita|preg[aã]o|edital|concorr[eê]ncia|dispensa|inexigibil|"
                  r"contrata[cç][aã]o|contrato|ata de registro|"
                  r"credenciamento|chamamento|14\.133|compras p[uú]blicas|superfaturamento|"
                  r"sobrepre[cç]o", re.I)
FORA = re.compile(r"\bconcurso|financiamento|empr[eé]stimo consignado|vestibular|enem\b|processo seletivo|"
                  r"futebol|campeonato|novela|bbb\b|hor[oó]scopo|vaga de emprego|"
                  r"aprovados no concurso|leil[aã]o de im[oó]ve(l|is) (residenciais|particulares)", re.I)


def sem_acento(s):
    return "".join(c for c in unicodedata.normalize("NFD", s) if unicodedata.category(c) != "Mn").lower()


def limpa(s):
    s = html.unescape(re.sub(r"<[^>]+>", " ", s or ""))
    return re.sub(r"\s+", " ", s).strip()


# ---------------------------------------------------------------- coleta
def google_news(q):
    url = ("https://news.google.com/rss/search?q=" + quote_plus(f"{q} when:{DIAS}d")
           + "&hl=pt-BR&gl=BR&ceid=BR:pt-419")
    try:
        r = requests.get(url, headers=UA, timeout=25)
        r.raise_for_status()
        root = ET.fromstring(r.content)
    except Exception as e:  # noqa: BLE001
        print(f"  ! falha na busca '{q}': {e}")
        return []
    itens = []
    for it in root.iter("item"):
        titulo = limpa(it.findtext("title"))
        fonte_el = it.find("source")
        fonte = limpa(fonte_el.text) if fonte_el is not None else ""
        if fonte and titulo.endswith(" - " + fonte):
            titulo = titulo[: -len(fonte) - 3].strip()
        try:
            dt = parsedate_to_datetime(it.findtext("pubDate")).astimezone(TZ)
        except Exception:  # noqa: BLE001
            continue
        itens.append({"titulo": titulo, "fonte": fonte, "link": it.findtext("link") or "",
                      "data": dt.date(), "site": fonte_el.get("url", "") if fonte_el is not None else ""})
    return itens


def link_original(link):
    """Troca o link do Google Notícias pelo link da matéria."""
    if "news.google.com" not in link:
        return link
    try:
        from googlenewsdecoder import gnewsdecoder
        r = _POOL.submit(gnewsdecoder, link, 1).result(timeout=25)
        if (r.get("success") or r.get("status")) and r.get("decoded_url"):
            return r["decoded_url"]
        print(f"  ! não decodificou link: {r.get('message')}")
    except Exception as e:  # noqa: BLE001
        print(f"  ! não decodificou link: {e}")
    try:
        r = requests.get(link, headers=UA, timeout=(8, 15), allow_redirects=True)
        if "news.google.com" not in r.url:
            return r.url
    except Exception:  # noqa: BLE001
        pass
    return link


def abre_materia(url):
    """Lê o texto de abertura publicado pela própria fonte."""
    try:
        r = requests.get(url, headers=UA, timeout=(8, 15))
        if r.status_code >= 400:
            return "", ""
        try:
            t = r.content.decode("utf-8")
        except UnicodeDecodeError:
            t = r.content.decode(r.apparent_encoding or "latin-1", errors="replace")
        t = re.sub(r"<(script|style|noscript)[^>]*>.*?</\1>", " ", t, flags=re.I | re.S)
    except Exception:  # noqa: BLE001
        return "", ""
    desc = ""
    for pat in (r'<meta[^>]+property=["\']og:description["\'][^>]+content=["\']([^"\']+)',
                r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+property=["\']og:description',
                r'<meta[^>]+name=["\']description["\'][^>]+content=["\']([^"\']+)'):
        m = re.search(pat, t, re.I)
        if m:
            desc = limpa(m.group(1))
            break
    m = re.search(r"<article[^>]*>(.*?)</article>", t, re.I | re.S)
    regiao = m.group(1) if m and len(m.group(1)) > 1500 else t
    paras = [limpa(p) for p in re.findall(r"<p(?:\s[^>]*)?>(.*?)</p>", regiao, re.I | re.S)]
    corpo = " ".join(p for p in paras if 80 < len(p) < 2500 and "{" not in p and "©" not in p
                     and re.search(r"[a-zà-ú]{3,}[.,;:] ", p) and not re.search(r"cookies?|assine|newsletter", p, re.I))[:6000]
    return desc, corpo


# ---------------------------------------------------------------- classificação
def acha_uf(texto, fonte=""):
    t = sem_acento(texto)
    m = re.search(r"\b(?:tce|tcm|tj|mp|mpe|trf|tre)[\s/\-]?([a-z]{2})\b", t)
    if m and m.group(1).upper() in SIGLAS:
        return m.group(1).upper()
    for nome in sorted(UFS, key=len, reverse=True):
        if re.search(r"\b(do|da|de|no|na|em)\s+" + nome + r"\b", t):
            return UFS[nome]
    for gent, uf in GENTILICOS.items():
        if re.search(r"\b" + gent + r"(s|a|as)?\b", t):
            return uf
    for cap, uf in CAPITAIS.items():
        if re.search(r"\b" + cap + r"\b", t):
            return uf
    m = re.search(r"[\(\-–/]\s?([A-Z]{2})\)?(?:\s|$|,)", texto)
    if m and m.group(1) in SIGLAS:
        return m.group(1)
    f = sem_acento(fonte)
    for k, uf in FONTE_UF.items():
        if k in f:
            return uf
    return ""


def classifica(texto, fonte=""):
    """Devolve (categoria, orgao_grupo, uf) ou None se não der para identificar."""
    t = sem_acento(texto)
    uf = acha_uf(texto, fonte)
    if re.search(r"\btcu\b|tribunal de contas da uniao", t):
        return "TCU", "TCU", uf or "BR"
    m = re.search(r"\btcm[\s/\-]?([a-z]{2})\b", t)
    if m and m.group(1).upper() in SIGLAS:
        return "Tribunal de Contas", "TCM-" + m.group(1).upper(), m.group(1).upper()
    if re.search(r"\btcm\b|tribunal de contas dos municipios|tribunal de contas do municipio", t):
        u = uf or ""
        return ("Tribunal de Contas", "TCM-" + u, u) if u else None
    m = re.search(r"\btce[\s/\-]?([a-z]{2})\b", t)
    if m and m.group(1).upper() in SIGLAS:
        return "Tribunal de Contas", "TCE-" + m.group(1).upper(), m.group(1).upper()
    if re.search(r"\btce\b|tribunal de contas", t):
        return ("Tribunal de Contas", "TCE-" + uf, uf) if uf else None
    if re.search(r"\bstf\b|supremo tribunal federal", t):
        return "Justiça / Mandado de segurança", "STF", uf or "BR"
    if re.search(r"\bstj\b|superior tribunal de justica", t):
        return "Justiça / Mandado de segurança", "STJ", uf or "BR"
    m = re.search(r"\btrf[\s\-]?([1-6])\b", t)
    if m:
        return "Justiça / Mandado de segurança", "TRF-" + m.group(1), uf or "BR"
    if re.search(r"\bpolicia federal\b|\bpf\b|operacao|\bgaeco\b", t):
        if re.search(r"policia federal|\bpf\b", t):
            return "Operações e investigações", "PF", uf or "BR"
        if re.search(r"\bcgu\b", t):
            return "Operações e investigações", "CGU", uf or "BR"
        if re.search(r"gaeco|ministerio publico|\bmp[\s\-]?[a-z]{2}\b|\bmpe\b", t):
            return ("Operações e investigações", "MP-" + uf, uf) if uf else None
        if re.search(r"policia civil", t):
            return ("Operações e investigações", "Polícia Civil-" + uf, uf) if uf else None
    if re.search(r"\bjustica\b|\bjuiz\b|\bjuiza\b|liminar|mandado de seguranca|desembargador|"
                 r"tribunal de justica|\btj[\s\-]?[a-z]{2}\b|vara da fazenda", t):
        return ("Justiça / Mandado de segurança", "TJ-" + uf, uf) if uf else None
    if re.search(r"14\.133|decreto|instrucao normativa|portaria|pncp|nova lei de licitac", t):
        return "Normas e orientações", "Normas", uf or "BR"
    return None


COMUNS = set("""suspende suspensao suspenso suspensa licitacao licitacoes pregao contra fraude fraudes operacao
prefeitura prefeituras contrato contratos tribunal contas justica mandados cumpre milhoes milhao para apos sobre
determina investiga investigacao suspeita suspeitos empresa empresas municipio municipal estado publica publico
eletronico concorrencia edital contratacao servicos obras compra aquisicao""".split())


def norm_titulo(s):
    return set(w for w in re.findall(r"[a-z0-9]{4,}", sem_acento(s)))


NAO_NOME = set("""justica tribunal policia federal ministerio publico operacao prefeitura contas estado gaeco
camara governo secretaria municipio caixa civil regional superior nacional uniao brasil sul norte
grande mato gerais santa catarina paulo janeiro espirito santo""".split()) | {w for n in UFS for w in n.split()}


def nomes_proprios(s):
    """Cidades/nomes próprios citados no título (palavras com maiúscula, fora a 1ª do título)."""
    out = set()
    for m in re.finditer(r"\b[A-ZÀ-Ý][a-zà-ÿ]{3,}(?:-[A-ZÀ-Ý][a-zà-ÿ]+)?", s):
        w = sem_acento(m.group(0))
        if m.start() == 0 or w in NAO_NOME:
            continue
        out.add(w)
    return out


def mesmo_caso(a, b):
    """Mesmo órgão + mesma cidade/nome próprio, ou várias palavras específicas em comum = mesmo caso."""
    if nomes_proprios(a) & nomes_proprios(b):
        return True
    a, b = norm_titulo(a) - COMUNS, norm_titulo(b) - COMUNS
    comum = a & b
    return len(comum) >= 2 and len(comum) / max(1, len(a | b)) >= 0.25


def parecido(a, b):
    a, b = norm_titulo(a), norm_titulo(b)
    if not a or not b:
        return False
    return len(a & b) / len(a | b) >= 0.45


def slug(s):
    return re.sub(r"[^a-z0-9]+", "-", sem_acento(s))[:60].strip("-")


def corta(s, n):
    if len(s) <= n:
        return s
    s = s[:n]
    p = max(s.rfind(". "), s.rfind("; "))
    return (s[: p + 1] if p > n * 0.5 else s.rsplit(" ", 1)[0] + "…").strip()


# ---------------------------------------------------------------- IA opcional (Gemini, gratuita)
GEMINI_KEY = os.environ.get("GEMINI_API_KEY", "").strip()
# modelos tentados em ordem; se um esgotar a cota gratuita ou falhar, passa para o próximo
GEMINI_MODELOS = [m.strip() for m in os.environ.get(
    "GEMINI_MODEL", "gemini-flash-lite-latest,gemini-2.5-flash-lite,gemini-flash-latest"
).split(",") if m.strip()]
GEMINI_MODEL = GEMINI_MODELOS[0]

PROMPT = """Você alimenta o "Radar das Licitações", página pública de notícias sobre licitações e contratações públicas no Brasil.
Analise a notícia abaixo e responda SOMENTE com um JSON:
{{"relevante": true/false, "titulo": "...", "resumo": "...", "categoria": "...", "orgao": "...", "orgao_grupo": "...", "uf": "..."}}
Regras:
- relevante = true só se for fato concreto sobre licitação, contrato administrativo ou contratação pública no Brasil (suspensão, anulação, decisão de Tribunal de Contas ou da Justiça, operação policial/MP sobre fraude em licitação, nova norma). false para concurso público, opinião, propaganda, notícia sem fato novo.
- titulo: com suas palavras, até 18 palavras, tom neutro.
- resumo: com suas palavras (não copie frases), no máximo 3 frases, tom neutro, só fatos que estão no texto. Em operações policiais use "investiga"/"suspeita", nunca afirme culpa.
- categoria: exatamente uma de "Tribunal de Contas", "TCU", "Justiça / Mandado de segurança", "Operações e investigações", "Normas e orientações".
- orgao: sigla e detalhe separados por " · " (ex.: "TCE-SP · Conselheiro Dimas Ramalho", "TJ-MT · 1ª Câmara de Direito Público").
- orgao_grupo: só a sigla com hífen ("TCU", "STJ", "STF", "TRF-4", "TJ-SP", "TCE-SC", "TCM-BA", "PF", "MP-SP", "CGU"). Juiz de 1ª instância estadual = TJ do estado.
- uf: sigla do estado; "BR" se nacional.
- Não invente números, nomes, processos ou datas.

FONTE: {fonte}
TÍTULO: {titulo}
TEXTO: {texto}"""


GEMINI_FALHAS = {}
GEMINI_ULTIMA = 0.0


def gemini(fonte, titulo, texto):
    global GEMINI_ULTIMA
    if not GEMINI_KEY:
        return None
    body = {"contents": [{"parts": [{"text": PROMPT.format(fonte=fonte, titulo=titulo, texto=texto[:5000])}]}],
            "generationConfig": {"temperature": 0.2, "responseMimeType": "application/json"}}
    for modelo in GEMINI_MODELOS:
        if GEMINI_FALHAS.get(modelo, 0) >= 2:
            continue  # este modelo está fora hoje
        espera = 6 - (time.time() - GEMINI_ULTIMA)  # no máx. ~10 pedidos/min (limite gratuito)
        if espera > 0:
            time.sleep(espera)
        GEMINI_ULTIMA = time.time()
        url = f"https://generativelanguage.googleapis.com/v1beta/models/{modelo}:generateContent"
        try:
            r = requests.post(url, json=body, headers={"x-goog-api-key": GEMINI_KEY}, timeout=(10, 45))
            if r.status_code != 200:
                GEMINI_FALHAS[modelo] = GEMINI_FALHAS.get(modelo, 0) + (2 if r.status_code in (404, 429) else 1)
                msg = re.sub(r"\s+", " ", r.text)[:160]
                print(f"  ! Gemini {modelo} respondeu {r.status_code}: {msg}")
                continue
            txt = r.json()["candidates"][0]["content"]["parts"][0]["text"]
            res = json.loads(re.sub(r"^```(json)?|```$", "", txt.strip()))
            GEMINI_FALHAS[modelo] = 0
            return res
        except Exception as e:  # noqa: BLE001
            GEMINI_FALHAS[modelo] = GEMINI_FALHAS.get(modelo, 0) + 1
            print(f"  ! Gemini {modelo} falhou: {e}")
    return None


# ---------------------------------------------------------------- principal
def main():
    with open(ARQ, encoding="utf-8") as f:
        dados = json.load(f)
    antigas = dados.get("noticias", [])
    urls = {n.get("url") for n in antigas}
    titulos = [n.get("titulo", "") for n in antigas]
    grupos = [(n.get("orgao_grupo"), n.get("titulo", "")) for n in antigas]

    print(f"Radar · {HOJE} · IA: {'Gemini ' + '/'.join(GEMINI_MODELOS) if GEMINI_KEY else 'desligada (resumo = abertura da fonte)'}")
    candidatos = []
    for q in BUSCAS:
        r = google_news(q)
        print(f"- {q}: {len(r)}")
        candidatos += r
        time.sleep(1)

    limite = HOJE - timedelta(days=DIAS)
    vistos, fila = [], []
    for c in sorted(candidatos, key=lambda x: x["data"], reverse=True):
        if c["data"] < limite or c["data"] > HOJE:
            continue
        txt = c["titulo"]
        if not TEMA.search(txt) or FORA.search(txt):
            continue
        if any(parecido(txt, t) for t in titulos + vistos):
            continue
        if classifica(txt, c["fonte"]) is None and not GEMINI_KEY:
            continue
        vistos.append(txt)
        fila.append(c)
    print(f"Candidatas após filtro: {len(fila)}")

    novas = []
    inicio = time.time()
    for c in fila[:30]:
        if len(novas) >= MAX_NOVAS:
            break
        if time.time() - inicio > 600:  # no máx. 10 minutos analisando matérias
            print("  ! tempo esgotado, publicando o que já foi analisado")
            break
        url = link_original(c["link"])
        if url in urls:
            continue
        desc, corpo = abre_materia(url) if "news.google.com" not in url else ("", "")
        texto_todo = " ".join([c["titulo"], desc, corpo])
        if FORA.search(c["titulo"] + " " + desc):
            continue

        ia = gemini(c["fonte"], c["titulo"], (desc + "\n" + corpo).strip() or c["titulo"])
        if ia is not None:
            if not ia.get("relevante"):
                print(f"  · IA descartou: {c['titulo']}")
                continue
            item = {
                "titulo": corta(limpa(ia.get("titulo") or c["titulo"]), 180),
                "resumo": corta(limpa(ia.get("resumo") or desc), 480),
                "categoria": ia.get("categoria"),
                "orgao": limpa(ia.get("orgao") or ""),
                "orgao_grupo": limpa(ia.get("orgao_grupo") or ""),
                "uf": (ia.get("uf") or "BR").upper()[:2],
            }
            if item["categoria"] not in {"Tribunal de Contas", "TCU", "Justiça / Mandado de segurança",
                                         "Operações e investigações", "Normas e orientações"}:
                cl = classifica(texto_todo, c["fonte"])
                if not cl:
                    continue
                item["categoria"] = cl[0]
            if not item["orgao_grupo"]:
                continue
            m = re.match(r"(TCE|TCM|TJ|MP|Polícia Civil)-([A-Z]{2})$", item["orgao_grupo"])
            if m and item["uf"] in SIGLAS and m.group(2) != item["uf"]:
                item["orgao_grupo"] = f"{m.group(1)}-{item['uf']}"  # sigla coerente com o estado
                item["orgao"] = re.sub(r"^(TCE|TCM|TJ|MP)-[A-Z]{2}", item["orgao_grupo"], item["orgao"])
            if not item["orgao"]:
                item["orgao"] = item["orgao_grupo"]
        else:
            cl = classifica(c["titulo"], c["fonte"]) or classifica(texto_todo, c["fonte"])
            if not cl:
                continue
            cat, grupo, uf = cl
            if uf in ("", "BR") and cat == "Operações e investigações":
                uf = acha_uf(" ".join([c["titulo"], desc]), c["fonte"]) or uf
            resumo = ""
            if desc and not parecido(desc, c["titulo"]) and len(desc) > 60 and desc.rstrip()[-1] in ".!?…»\"":
                resumo = corta(desc, 420)
            if not resumo and corpo:
                resumo = corta(corpo, 420)
            if not resumo and desc and len(desc) > 60:
                resumo = corta(desc, 420)
            if not resumo:
                resumo = "Abra a fonte para ler os detalhes da decisão."
            item = {"titulo": c["titulo"], "resumo": resumo, "categoria": cat,
                    "orgao": grupo, "orgao_grupo": grupo, "uf": uf}
        if url in urls or any(parecido(item["titulo"], t) for t in titulos):
            continue
        if any(g == item["orgao_grupo"] and (mesmo_caso(item["titulo"], t) or mesmo_caso(c["titulo"], t))
               for g, t in grupos):
            print(f"  · repetida: {item['titulo']}")
            continue
        item.update({
            "id": f"{slug(item['orgao_grupo'] + ' ' + item['titulo'])}-{c['data']}",
            "data": c["data"].isoformat(),
            "fonte": c["fonte"] or urlparse(url).netloc,
            "url": url,
            "auto": True,
        })
        novas.append(item)
        urls.add(url)
        titulos.append(item["titulo"])
        grupos.append((item["orgao_grupo"], item["titulo"]))
        print(f"  + [{item['orgao_grupo']}/{item['uf']}] {item['titulo']}")

    ordem = ["id", "data", "categoria", "orgao", "orgao_grupo", "uf", "titulo", "resumo", "fonte", "url", "auto"]
    novas = [{k: n[k] for k in ordem if k in n} for n in novas]
    todas = sorted(novas + antigas, key=lambda n: n.get("data", ""), reverse=True)[:MAX_TOTAL]
    dados["noticias"] = todas
    dados["atualizado_em"] = HOJE.isoformat()
    with open(ARQ, "w", encoding="utf-8") as f:
        json.dump(dados, f, ensure_ascii=False, indent=2)
        f.write("\n")
    print(f"\nEntraram {len(novas)} notícia(s). Total no Radar: {len(todas)}.")
    gh = os.environ.get("GITHUB_STEP_SUMMARY")
    if gh:
        with open(gh, "a", encoding="utf-8") as f:
            f.write(f"### Radar {HOJE}: {len(novas)} notícia(s) nova(s)\n\n")
            for n in novas:
                f.write(f"- **{n['orgao_grupo']}/{n['uf']}** — [{n['titulo']}]({n['url']})\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
