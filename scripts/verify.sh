#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
unzip -q "$root/original/oeis-a326602-lean.zip" -d "$tmp"
source="$tmp/oeis-a326602-lean/326602.lean"
python3 - "$source" "$root/FormalConjectures/OEIS/326602.lean" <<'PY'
import pathlib, sys
def normalize(p):
    return [line.strip() for line in pathlib.Path(p).read_text(encoding="utf-8-sig").splitlines() if line.strip()]
assert normalize(sys.argv[1]) == normalize(sys.argv[2]), "Source copy differs from original ZIP"
PY
if grep -En '^[[:space:]]*(sorry|admit|axiom)[[:space:]]*($|[^[:alnum:]_])' "$source"; then exit 1; fi
git clone --filter=blob:none https://github.com/google-deepmind/formal-conjectures.git "$tmp/upstream"
cd "$tmp/upstream"
git checkout f606af160664c5a10952e9a957b100a1cd45bbeb
mkdir -p FormalConjectures/OEIS
cp "$source" FormalConjectures/OEIS/326602.lean
lake exe cache get
lake build 'FormalConjectures.OEIS.«326602»'
cat > Audit326602.lean <<'LEAN'
import FormalConjectures.OEIS.«326602»
#print axioms OeisA326602.termSeries_spec
#print axioms OeisA326602.coeff_termSeries_eq_zero_of_lt
#print axioms OeisA326602.coeff_A_eq_triple_sum
#print axioms OeisA326602.coeff_A_odd_eq_zero
#print axioms OeisA326602.conjecture_parity
#print axioms OeisA326602.a_0
#print axioms OeisA326602.a_1
#print axioms OeisA326602.a_2
#print axioms OeisA326602.a_3
LEAN
lake env lean Audit326602.lean | tee "$root/lean-axioms.txt"
python3 - "$root/lean-axioms.txt" <<'PY'
import pathlib,re,sys
s=pathlib.Path(sys.argv[1]).read_text()
matches=re.findall(r"depends on axioms:\s*\[([^\]]*)\]",s)
assert len(matches)==9, s
allowed={"propext","Classical.choice","Quot.sound"}
for m in matches:
    assert {x.strip() for x in m.split(",") if x.strip()} <= allowed, m
PY
