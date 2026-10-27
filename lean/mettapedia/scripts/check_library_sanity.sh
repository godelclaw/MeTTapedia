#!/usr/bin/env bash
# Build the library aggregates and comparison entrypoints, then check freshness.
# --no-build checks existing artifacts without rebuilding; --list prints targets.
set -euo pipefail

mode=${1:-build}
if (( $# > 1 )); then
  printf 'Usage: %s [--no-build|--list]\n' "$0" >&2
  exit 2
fi
case "$mode" in
  build|--no-build|--list) ;;
  *) printf 'Usage: %s [--no-build|--list]\n' "$0" >&2; exit 2 ;;
esac

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
targets=(
  Mettapedia
  Mettapedia.Languages
  Mettapedia.PLN
  Mettapedia.Languages.MeTTa.PrimeCandidates.NativeSemanticWeights
  Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslateExamples
  Mettapedia.Languages.MeTTa.Translation.HEPeTTaSemanticForms
  Mettapedia.Languages.MeTTa.QueryRevisionBridge
)

for target in "${targets[@]}"; do
  source_file=${target//./\/}.lean
  if [[ ! -f "$source_file" ]]; then
    printf 'Missing sanity target source: %s\n' "$source_file" >&2
    exit 2
  fi
done

if [[ "$mode" == --list ]]; then
  printf '%s\n' "${targets[@]}"
  exit 0
fi
python3 scripts/check_lake_checkouts.py
if [[ "$mode" == build ]]; then
  lake build "${targets[@]}"
fi
exec lake --no-build build "${targets[@]}"
