#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SWI_VERSION="SWI-Prolog version 10.1.9"

if [[ "$(swipl --version)" != "$SWI_VERSION"* ]]; then
  echo "runtime-control differential requires $SWI_VERSION" >&2
  exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

pushd "$ROOT_DIR" >/dev/null
lake env lean --run scripts/prolog/runtime_control_differential.lean \
  > "$TMP/lean.txt"
swipl -q -f scripts/prolog/runtime_control_oracle.pl > "$TMP/swi.txt"
popd >/dev/null

diff -u "$TMP/swi.txt" "$TMP/lean.txt"
echo "Runtime-control differential: PASS (33/33 exact answer/exception traces)"
