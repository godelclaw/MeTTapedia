#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <PeTTa git tree> <SWI-Prolog git tree>" >&2
  exit 2
fi

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PETTA_TREE="$(realpath "$1")"
SWI_TREE="$(realpath "$2")"
PETTA_PIN="6b7f52f064bdbc82fabd0a0998404121fb01d52e"
SWI_PIN="6be143dbd030cc9ea621cde719a37f8385575453"

git -C "$PETTA_TREE" cat-file -e "$PETTA_PIN^{commit}"
if [[ "$(git -C "$SWI_TREE" rev-parse HEAD)" != "$SWI_PIN" ]]; then
  echo "owned parser smoke requires SWI source commit $SWI_PIN" >&2
  exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
git -C "$PETTA_TREE" archive "$PETTA_PIN" src/parser.pl | tar -x -C "$TMP"
git -C "$SWI_TREE" archive "$SWI_PIN" \
  library/dcg/basics.pl library/error.pl library/pairs.pl | tar -x -C "$TMP"

cd "$ROOT_DIR"
lake env lean --run scripts/prolog/owned_lists_parser_smoke.lean \
  "$TMP/src/parser.pl" "$TMP/library/dcg/basics.pl" \
  "$TMP/library/error.pl" "$TMP/library/pairs.pl"
