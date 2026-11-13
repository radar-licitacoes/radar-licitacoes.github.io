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
                  r"contrata[cç][aã]o p[uú]blica|contrato|ata de registro|"
                  r"credenciamento|chamamento|14\.133|compras p[uú]blicas|superfaturamento|"
                  r"sobrepre[cç]o|fraude", re.I)
FORA = re.compile(r"concurso p[uú]blico|vestibular|enem\b|processo seletivo|"
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
        r = gnewsdecoder(link, interval=1)
        if r.get("status") and r.get("decoded_url"):
            return r["decoded_url"]
    except Exception as e:  # noqa: BLE001
        print(f"  ! não decodificou link: {e}")
    try:
        r = requests.get(link, headers=UA, timeout=20, allow_redirects=True)
        if "news.google.com" not in r.url:
            return r.url
    except Exception:  # noqa: BLE001
        pass
    return link


def abre_materia(url):
    """Lê o texto de abertura publicado pela própria fonte."""
    try:
        r = requests.get(url, headers=UA, timeout=20)
        if r.status_code >= 400:
            return "", ""
        t = r.text
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
    paras = [limpa(p) for p in re.findall(r"<p[^>]*>(.*?)</p>", t, re.I | re.S)]
    corpo = " ".join(p for p in paras if len(p) > 80)[:6000]
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


def norm_titulo(s):
    return set(w for w in re.findall(r"[a-z0-9]{4,}", sem_acento(s)))


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
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-flash-latest").strip()

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


def gemini(fonte, titulo, texto):
    if not GEMINI_KEY:
        return None
    url = (f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent")
    body = {"contents": [{"parts": [{"text": PROMPT.format(fonte=fonte, titulo=titulo, texto=texto[:5000])}]}],
            "generationConfig": {"temperature": 0.2, "responseMimeType": "application/json"}}
    for tentativa in range(3):
        try:
            r = requests.post(url, json=body, headers={"x-goog-api-key": GEMINI_KEY}, timeout=60)
            if r.status_code == 429:
                time.sleep(20)
                continue
            r.raise_for_status()
            txt = r.json()["candidates"][0]["content"]["parts"][0]["text"]
            return json.loads(re.sub(r"^```(json)?|```$", "", txt.strip()))
        except Exception as e:  # noqa: BLE001
            print(f"  ! Gemini falhou ({tentativa + 1}/3): {e}")
            time.sleep(5)
    return None


# ---------------------------------------------------------------- principal
def main():
    with open(ARQ, encoding="utf-8") as f:
        dados = json.load(f)
    antigas = dados.get("noticias", [])
    urls = {n.get("url") for n in antigas}
    titulos = [n.get("titulo", "") for n in antigas]

    print(f"Radar · {HOJE} · IA: {'Gemini ' + GEMINI_MODEL if GEMINI_KEY else 'desligada (resumo = abertura da fonte)'}")
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
    for c in fila:
        if len(novas) >= MAX_NOVAS:
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
            if not item["orgao"]:
                item["orgao"] = item["orgao_grupo"]
        else:
            cl = classifica(c["titulo"], c["fonte"]) or classifica(texto_todo, c["fonte"])
            if not cl:
                continue
            cat, grupo, uf = cl
            resumo = corta(desc, 420) if desc and not parecido(desc, c["titulo"]) else ""
            if not resumo and corpo:
                resumo = corta(corpo, 420)
            if not resumo:
                resumo = "Abra a fonte para ler os detalhes da decisão."
            item = {"titulo": c["titulo"], "resumo": resumo, "categoria": cat,
                    "orgao": grupo, "orgao_grupo": grupo, "uf": uf}
        if url in urls or any(parecido(item["titulo"], t) for t in titulos):
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
