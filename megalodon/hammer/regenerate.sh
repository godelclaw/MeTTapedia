#!/usr/bin/env bash
# Regenerate the TPTP problem sets that used to be committed under megalodon/,
# and check them against manifest.sha256.
#
#   megalodon/hammer/regenerate.sh [OUT_DIR]   (default: megalodon/hammer/out, git-ignored)
#
# Sets:
#   hammer_test     Megalodon 1.13's own example examples/hammer/100thms_12_h.mg,
#                   exported with `megalodon -fof hammer_test`: one FOF problem for
#                   each first-order "aby" call, named by its line number.
#                   Needs bin/megalodon and examples/ from ../setup_megalodon.sh.
#   triangle_split  Adj17 triangle-freeness split into one problem per vertex
#                   triple, by tools/split_ramsey_triangle.py from
#                   ramsey36/adj17_triangle_free.tptp. The dedukti_bridge test
#                   generates the same files in its own directory.
#
# The exports of the archived Ramsey(3,6) files (adj17sym.770, ramsey36_atp.*,
# r36atp.50) were removed with the committed sets; recover them with
#   git log --diff-filter=D --name-only -- 'megalodon/*.fof.p' 'megalodon/experiments/hammer_tests'
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mega="$(dirname "$here")"
repo="$(dirname "$mega")"
out="${1:-$here/out}"
manifest="$here/manifest.sha256"

set_digest() {
  (cd "$1" && find . -maxdepth 1 -type f -name '*.p' -printf '%f\n' | LC_ALL=C sort |
     xargs -d '\n' sha256sum) | sha256sum | cut -d' ' -f1
}

# Check the pinned inputs first, so that a changed input is reported as such.
if ! (cd "$mega" && grep -E '^[0-9a-f]{64}  ' "$manifest" | sha256sum --check --quiet); then
  echo "An input differs from manifest.sha256; outputs would not be comparable." >&2
  exit 1
fi

mkdir -p "$out"
for set in hammer_test triangle_split; do
  rm -rf -- "${out:?}/$set"
  mkdir -p "$out/$set"
done

(cd "$out/hammer_test" && "$mega/bin/megalodon" -fof hammer_test "$mega/examples/hammer/100thms_12_h.mg" >/dev/null)
python3 -I "$repo/tools/split_ramsey_triangle.py" --source "$mega/ramsey36/adj17_triangle_free.tptp" \
  --out-dir "$out/triangle_split" >/dev/null

status=0
while read -r tag digest count set; do
  [ "$tag" = set ] || continue
  got_count=$(find "$out/$set" -maxdepth 1 -type f -name '*.p' | wc -l)
  got=$(set_digest "$out/$set")
  if [ "$got" = "$digest" ] && [ "$got_count" -eq "$count" ]; then
    echo "$set: $count files, identical to the manifest"
  else
    echo "$set: MISMATCH, $got_count files, digest $got" >&2
    status=1
  fi
done < "$manifest"
exit $status
