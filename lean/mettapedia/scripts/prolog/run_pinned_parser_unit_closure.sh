#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <PeTTa git tree>" >&2
  exit 2
fi

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PETTA_TREE="$(realpath "$1")"
PIN="6b7f52f064bdbc82fabd0a0998404121fb01d52e"
SWI_VERSION="SWI-Prolog version 10.1.9"

if [[ "$(swipl --version)" != "$SWI_VERSION"* ]]; then
  echo "pinned source-unit gate requires $SWI_VERSION" >&2
  exit 1
fi

git -C "$PETTA_TREE" cat-file -e "$PIN^{commit}"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

git -C "$PETTA_TREE" archive "$PIN" src/parser.pl | tar -x -C "$TMP"
DCG_BASICS="$(swipl -q -g \
  "absolute_file_name(library('dcg/basics'), P, [file_type(prolog), access(read)]), write(P), halt")"

pushd "$ROOT_DIR" >/dev/null
lake env lean --run scripts/prolog/pinned_parser_unit_closure.lean \
  "$TMP/src/parser.pl" "$DCG_BASICS" > "$TMP/actual"
popd >/dev/null

cat > "$TMP/expected" <<'EOF'
units=2
unit:parser clauses=30 imports=1 directives=1
unit:library(dcg/basics) clauses=58 imports=2 directives=3
external=library(lists) options=0
external=library(error) options=0
linked_clauses=88
declarations=0
pending_goals=0
EOF

diff -u "$TMP/expected" "$TMP/actual"
echo "Pinned parser source-unit closure: PASS (88 canonical clauses; externals explicit)"
