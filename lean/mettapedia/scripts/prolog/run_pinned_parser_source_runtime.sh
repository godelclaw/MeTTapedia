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
  echo "pinned parser runtime gate requires $SWI_VERSION" >&2
  exit 1
fi

git -C "$PETTA_TREE" cat-file -e "$PIN^{commit}"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
git -C "$PETTA_TREE" archive "$PIN" src/parser.pl | tar -x -C "$TMP"

DCG_BASICS="$(swipl -q -g \
  "absolute_file_name(library('dcg/basics'), P, [file_type(prolog), access(read)]), write(P), halt")"
LISTS="$(swipl -q -g \
  "absolute_file_name(library(lists), P, [file_type(prolog), access(read)]), write(P), halt")"
ERROR="$(swipl -q -g \
  "absolute_file_name(library(error), P, [file_type(prolog), access(read)]), write(P), halt")"

pushd "$ROOT_DIR" >/dev/null
if ! lake env lean --run scripts/prolog/pinned_parser_source_runtime.lean \
    "$TMP/src/parser.pl" "$DCG_BASICS" "$LISTS" "$ERROR" > "$TMP/lean.out"; then
  cat "$TMP/lean.out" >&2
  popd >/dev/null
  exit 1
fi
popd >/dev/null

cat > "$TMP/lean.expected" <<'EOF'
empty_codes=[40,41]
empty_cleanup=0/0
atom_list_codes=[40,97,41]
atom_list_cleanup=0/0
read_atom=[|](a,[])
read_cleanup=0/0
read_list=exact
read_string=exact
read_nested=exact
EOF
diff -u "$TMP/lean.expected" "$TMP/lean.out"

swipl -q -s "$TMP/src/parser.pl" \
  -g "phrase(swrite_exp([]), Empty), write_canonical(Empty), nl, phrase(swrite_exp([a]), AtomList), write_canonical(AtomList), nl, phrase(sexpr(ReadAtom, [], _), [40,97,41]), write_canonical(ReadAtom), nl, phrase(sexpr(ReadList, [], _), [40,97,32,98,41]), write_canonical(ReadList), nl, phrase(sexpr(ReadString, [], _), [40,34,97,34,41]), write_canonical(ReadString), nl, phrase(sexpr(ReadNested, [], _), [40,40,97,41,41]), write_canonical(ReadNested), nl, halt" \
  > "$TMP/swi.out"
printf '%s\n' '[40,41]' '[40,97,41]' '[a]' '[a,b]' '["a"]' '[[a]]' > "$TMP/swi.expected"
diff -u "$TMP/swi.expected" "$TMP/swi.out"

echo "Pinned parser source runtime: PASS (writes and four reader shapes exact; clean closure)"
