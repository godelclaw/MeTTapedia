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
  echo "pinned source-runtime differential requires $SWI_VERSION" >&2
  exit 1
fi

git -C "$PETTA_TREE" cat-file -e "$PIN^{commit}"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

git -C "$PETTA_TREE" archive "$PIN" src/spaces.pl | tar -x -C "$TMP"

pushd "$ROOT_DIR" >/dev/null
lake env lean --run scripts/prolog/pinned_spaces_runtime.lean \
  "$TMP/src/spaces.pl" > "$TMP/lean.out"
swipl -q -f scripts/prolog/pinned_spaces_oracle.pl -- \
  "$TMP/src/spaces.pl" > "$TMP/swi.out"
popd >/dev/null

diff -u "$TMP/swi.out" "$TMP/lean.out"
echo "Pinned spaces.pl runtime: PASS (exact answer count and clean runtime closure)"
