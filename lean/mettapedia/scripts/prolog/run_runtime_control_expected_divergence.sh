#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SWI_VERSION="SWI-Prolog version 10.1.9"

if [[ "$(swipl --version)" != "$SWI_VERSION"* ]]; then
  echo "runtime-control divergence gate requires $SWI_VERSION" >&2
  exit 1
fi

pushd "$ROOT_DIR" >/dev/null
LEAN_OUTPUT="$(lake env lean --run \
  scripts/prolog/runtime_control_expected_divergence.lean)"
SWI_OUTPUT="$(swipl -q -f \
  scripts/prolog/runtime_control_expected_divergence.pl)"
popd >/dev/null

[[ "$LEAN_OUTPUT" == "throw_variable=accepted" ]]
[[ "$SWI_OUTPUT" == "throw_variable=instantiation_error" ]]
[[ "$LEAN_OUTPUT" != "$SWI_OUTPUT" ]]

echo "Runtime-control expected divergence: PASS (throw/1 variable ball)"
