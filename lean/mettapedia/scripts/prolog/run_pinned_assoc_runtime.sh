#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SWI_DIR="${1:?usage: run_pinned_assoc_runtime.sh /path/to/swipl-devel}"
SWI_PIN="6be143dbd030cc9ea621cde719a37f8385575453"
SWI_VERSION="SWI-Prolog version 10.1.9"

if [[ "$(git -C "$SWI_DIR" rev-parse HEAD)" != "$SWI_PIN" ]]; then
  echo "pinned assoc runtime requires SWI source commit $SWI_PIN" >&2
  exit 1
fi
if [[ "$(swipl --version)" != "$SWI_VERSION"* ]]; then
  echo "pinned assoc runtime requires $SWI_VERSION" >&2
  exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
git -C "$SWI_DIR" archive "$SWI_PIN" library/assoc.pl | tar -x -C "$TMP"

pushd "$ROOT_DIR" >/dev/null
lake env lean --run scripts/prolog/pinned_assoc_runtime.lean \
  "$TMP/library/assoc.pl" > "$TMP/lean.txt"
swipl -p "library=$TMP/library" -q \
  -f scripts/prolog/pinned_assoc_runtime_oracle.pl > "$TMP/swi.txt"
popd >/dev/null

diff -u "$TMP/swi.txt" "$TMP/lean.txt"
COUNT="$(wc -l < "$TMP/lean.txt" | tr -d '[:space:]')"
if [[ "$COUNT" != 4 ]]; then
  echo "pinned assoc runtime expected 4 traces, got $COUNT" >&2
  exit 1
fi
echo "Pinned assoc runtime: PASS ($COUNT/$COUNT exact ordered traces)"
