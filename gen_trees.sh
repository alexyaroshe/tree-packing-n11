# gentreeg (nauty) tree generator
set -euo pipefail
NMAX="${1:?usage: gen_trees.sh NMAX [outfile]}"
OUT="${2:-trees.txt}"

command -v gentreeg >/dev/null || { echo "FATAL: gentreeg (nauty) not on PATH" >&2; exit 2; }

: > "$OUT"
for ((k=2; k<=NMAX; k++)); do
  echo "# $k" >> "$OUT"
  gentreeg -p -q "$k" >> "$OUT"
done

EXPECT=(0 0 1 1 2 3 6 11 23 47 106 235 551 1301 3159)
fail=0
for ((k=2; k<=NMAX; k++)); do
  got=$(awk -v want="$k" '/^#/{sec=$2; next} sec==want{c++} END{print c+0}' "$OUT")
  exp=${EXPECT[$k]}
  if [ "$got" != "$exp" ]; then
    echo "GATE FAIL: k=$k produced $got trees, A000055 says $exp" >&2
    fail=1
  else
    echo "  k=$k: $got trees (A000055 ok)"
  fi
done
[ "$fail" = 0 ] || exit 1
echo "wrote $OUT ($(wc -l < "$OUT") lines)"
