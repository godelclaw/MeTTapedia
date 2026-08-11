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
  echo "reader differential requires $SWI_VERSION" >&2
  exit 1
fi

git -C "$PETTA_TREE" cat-file -e "$PIN^{commit}"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

FILES=(
  src/main.pl
  src/metta.pl
  src/translator.pl
  src/parser.pl
  src/specializer.pl
  src/filereader.pl
  src/spaces.pl
)

git -C "$PETTA_TREE" archive "$PIN" "${FILES[@]}" | tar -x -C "$TMP"

ABS_FILES=()
for file in "${FILES[@]}"; do
  ABS_FILES+=("$TMP/$file")
done

pushd "$ROOT_DIR" >/dev/null
lake env lean --run scripts/prolog/reader_pinned_differential.lean \
  "${ABS_FILES[@]}" | jq -c . > "$TMP/lean.jsonl"
swipl -q -f scripts/prolog/reader_pinned_oracle.pl -- \
  "${ABS_FILES[@]}" | jq -c . > "$TMP/swi.jsonl"
popd >/dev/null

if [[ "$(wc -l < "$TMP/lean.jsonl")" -ne 317 ]]; then
  echo "Lean reader did not emit exactly 317 pinned forms" >&2
  exit 1
fi
if [[ "$(wc -l < "$TMP/swi.jsonl")" -ne 317 ]]; then
  echo "SWI reader did not emit exactly 317 pinned forms" >&2
  exit 1
fi

diff -u "$TMP/swi.jsonl" "$TMP/lean.jsonl"
echo "Pinned reader differential: PASS (317/317 exact recursive term shapes)"
