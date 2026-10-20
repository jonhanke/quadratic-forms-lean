#!/bin/bash
# Render every docs/images/*.tex (standalone LaTeX) to an SVG on a white card, for GitHub pages.
# Needs latex and dvisvgm. Usage: scripts/render_formulas.sh
set -euo pipefail
cd "$(dirname "$0")/../docs/images"
tmp=$(mktemp -d)
for tex in *.tex; do
  base=${tex%.tex}
  cp "$tex" "$tmp/"
  (cd "$tmp" && latex -interaction=nonstopmode "$tex" >/dev/null && dvisvgm --no-fonts --exact-bbox -o "$base.svg" "$base.dvi" >/dev/null 2>&1)
  python3 - "$tmp/$base.svg" "$base.svg" <<'PY'
import re, sys
s = open(sys.argv[1]).read()
x, y, w, h = map(float, re.search(r"viewBox='([-\d.]+) ([-\d.]+) ([-\d.]+) ([-\d.]+)'", s).groups())
s = re.sub(r"(<svg[^>]*>)", lambda m: m.group(1) + f"\n<rect x='{x}' y='{y}' width='{w}' height='{h}' rx='6' fill='white'/>", s, count=1)
open(sys.argv[2], "w").write(s)
PY
  echo "rendered $base.svg"
done
