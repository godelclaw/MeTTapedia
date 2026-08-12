#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SWI_VERSION="SWI-Prolog version 10.1.9"

if [[ "$(swipl --version)" != "$SWI_VERSION"* ]]; then
  echo "source-term-order differential requires $SWI_VERSION" >&2
  exit 1
fi

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

pushd "$ROOT_DIR" >/dev/null
lake build Mettapedia.Logic.Prolog.SourceTermOrderRegression >/dev/null
lake env lean --run scripts/prolog/source_term_order_differential.lean \
  > "$TMP/lean.txt"
swipl -q -f scripts/prolog/source_term_order_oracle.pl > "$TMP/swi.txt"
popd >/dev/null

diff -u "$TMP/swi.txt" "$TMP/lean.txt"
COUNT="$(wc -l < "$TMP/lean.txt" | tr -d '[:space:]')"
echo "Source-term-order differential: PASS ($COUNT/$COUNT exact sorted terms)"
