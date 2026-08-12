#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <SWI-Prolog git tree>" >&2
  exit 2
fi

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SWI_TREE="$(realpath "$1")"
PIN="6be143dbd030cc9ea621cde719a37f8385575453"

git -C "$SWI_TREE" cat-file -e "$PIN^{commit}"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
git -C "$SWI_TREE" archive "$PIN" library/assoc.pl | tar -x -C "$TMP"

pushd "$ROOT_DIR" >/dev/null
lake env lean --run scripts/prolog/pinned_assoc_conditional.lean \
  "$TMP/library/assoc.pl" > "$TMP/actual"
popd >/dev/null

cat > "$TMP/expected" <<'EOF'
items=110
clauses=106
directives=4
pending_goals=0
private_btree_calls=0
ssu_rules=18
get_assoc_heads=10
EOF

diff -u "$TMP/expected" "$TMP/actual"
echo "Pinned assoc conditional selection: PASS (portable arm selected; 18 SSU rules typed)"
