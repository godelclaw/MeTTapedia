#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/.." && pwd)
build_dir=$(mktemp -d "${TMPDIR:-/tmp}/sti-conformance-vectors.XXXXXX")
trap 'rm -rf -- "$build_dir"' EXIT

# Compile the semantic authority privately so stdout remains canonical JSONL.
lean -o "$build_dir/StiMass.olean" \
  "$repo_root/lean/pettaclaw/StiMass.lean" >/dev/null

if [[ -n "${LEAN_PATH:-}" ]]; then
  export LEAN_PATH="$build_dir:$LEAN_PATH"
else
  export LEAN_PATH="$build_dir"
fi

lean --run "$repo_root/lean/pettaclaw/StiConformanceVectors.lean"
