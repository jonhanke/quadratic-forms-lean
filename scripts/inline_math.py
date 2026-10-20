#!/usr/bin/env python3
"""Replace inline expressions with blackboard/fraktur/calligraphic letters by LaTeX-rendered SVGs.

GitHub math draws \\mathbb, \\mathfrak and \\mathcal as plain letters, and Unicode letters in the
text font do not match its TeX font. This script finds the Unicode/HTML forms used in the public
docs (e.g. β<sub>𝔭</sub>(<i>L</i>, <i>m</i>)), renders each as a small SVG with LaTeX (12pt,
white background, so it reads in light and dark mode) and swaps in an inline <img>. Headings, bold
labels and link texts keep Unicode. The LaTeX is stored in the alt text.

Usage: scripts/inline_math.py FILE.md ...   (needs latex and dvisvgm)
"""
import hashlib, os, re, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "docs", "images", "inline")

# Longest patterns first.
PATTERNS = [
    (r"β<sub>𝔭</sub>\(<i>(\w)</i>, <i>(\w)</i>\)", r"\beta_{\mathfrak{p}}(\1, \2)"),
    (r"α<sub>𝔭</sub>\(<i>(\w)</i>, <i>(\w)</i>\)", r"\alpha_{\mathfrak{p}}(\1, \2)"),
    (r"λ<sub>𝔭</sub> = <i>L</i><sub>𝔭</sub>\(1, χ\)", r"\lambda_{\mathfrak{p}} = L_{\mathfrak{p}}(1, \chi)"),
    (r"\(1 − χ\(𝔭\)/N𝔭\)", r"(1 - \chi(\mathfrak{p})/\mathrm{N}\mathfrak{p})"),
    (r"𝒪<sub><i>F</i></sub>\[√−<i>D</i>\]", r"\mathcal{O}_F[\sqrt{-D}]"),
    (r"𝒪<sub><i>F</i></sub><sup><i>n</i></sup>", r"\mathcal{O}_F^n"),
    (r"𝒪<sub><i>F</i></sub>", r"\mathcal{O}_F"),
    (r"𝔡<sub><i>L</i></sub>", r"\mathfrak{d}_L"),
    (r"𝔭<sup><i>k</i></sup>", r"\mathfrak{p}^k"),
    (r"ℚ<sub>p</sub><sup>×</sup>", r"\mathbb{Q}_p^\times"),
    (r"ℚ<sub>p</sub>", r"\mathbb{Q}_p"),
    (r"α<sub>𝔭</sub>", r"\alpha_{\mathfrak{p}}"),
    (r"β<sub>𝔭</sub>", r"\beta_{\mathfrak{p}}"),
    (r"𝔭", r"\mathfrak{p}"),
    (r"ℚ", r"\mathbb{Q}"), (r"ℤ", r"\mathbb{Z}"), (r"ℝ", r"\mathbb{R}"), (r"ℂ", r"\mathbb{C}"),
]
COMBINED = re.compile("|".join(f"(?:{p})" for p, _ in PATTERNS))
# Spans left alone: code, protected GitHub math, bold, link text, existing images/tags.
PROTECT = re.compile(r"`[^`]*`|\$`[^`]*`\$|\*\*[^*]+\*\*|\[[^\]]*\]\([^)]*\)|<img [^>]*>")

TEX = r"""\documentclass[12pt,border=1pt]{standalone}
\usepackage{amsmath,amssymb}
\begin{document}\(%s\)\end{document}
"""

def latex_of(text):
    for p, r in PATTERNS:
        m = re.fullmatch(p, text)
        if m:
            out = r
            for i, g in enumerate(m.groups(), 1):
                out = out.replace("\\%d" % i, g)
            return out
    raise ValueError(text)

def render(tex):
    name = hashlib.sha1(tex.encode()).hexdigest()[:12] + ".svg"
    path = os.path.join(OUT, name)
    if not os.path.exists(path):
        os.makedirs(OUT, exist_ok=True)
        with tempfile.TemporaryDirectory() as d:
            open(os.path.join(d, "f.tex"), "w").write(TEX % tex)
            subprocess.run(["latex", "-interaction=nonstopmode", "f.tex"], cwd=d, check=True, capture_output=True)
            subprocess.run(["dvisvgm", "--no-fonts", "--exact-bbox", "-o", "f.svg", "f.dvi"], cwd=d, check=True, capture_output=True)
            s = open(os.path.join(d, "f.svg")).read()
        x, y, w, h = map(float, re.search(r"viewBox='([-\d.]+) ([-\d.]+) ([-\d.]+) ([-\d.]+)'", s).groups())
        s = re.sub(r"(<svg[^>]*>)", lambda m: m.group(1) + f"\n<rect x='{x}' y='{y}' width='{w}' height='{h}' fill='white'/>", s, count=1)
        open(path, "w").write(s)
    return name

def convert(md_path):
    rel = os.path.relpath(OUT, os.path.dirname(os.path.abspath(md_path)))
    out_lines = []
    for line in open(md_path).read().split("\n"):
        if line.lstrip().startswith("#") or line.startswith("```") or line.startswith("    "):
            out_lines.append(line); continue
        pieces, last = [], 0
        for m in PROTECT.finditer(line):
            pieces.append((False, line[last:m.start()])); pieces.append((True, m.group(0))); last = m.end()
        pieces.append((False, line[last:]))
        new = ""
        for protected, seg in pieces:
            if protected:
                new += seg; continue
            def sub(m):
                tex = latex_of(m.group(0))
                alt = tex.replace('"', "&quot;")
                return f'<img src="{rel}/{render(tex)}" align="absmiddle" alt="{alt}">'
            new += COMBINED.sub(sub, seg)
        out_lines.append(new)
    open(md_path, "w").write("\n".join(out_lines))

if __name__ == "__main__":
    for f in sys.argv[1:]:
        convert(f)
        print("converted", f)
