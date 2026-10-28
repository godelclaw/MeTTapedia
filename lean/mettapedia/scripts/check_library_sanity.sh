#!/usr/bin/env bash
# Check dependency sources, named aggregates, freshness, and source coverage.
# An aggregate build alone does not qualify sources outside its import closure.
set -euo pipefail

mode=${1:-build}
if (( $# > 1 )); then
  printf 'Usage: %s [--no-build|--coverage|--list]\n' "$0" >&2
  exit 2
fi
case "$mode" in
  build|--no-build|--coverage|--list) ;;
  *) printf 'Usage: %s [--no-build|--coverage|--list]\n' "$0" >&2; exit 2 ;;
esac

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
targets=(
  Mettapedia
  Mettapedia.Languages
  Mettapedia.PLN
  Mettapedia.Languages.MeTTa.PrimeCandidates.Strategies.NativeSemanticWeights
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

coverage_args=()
for target in "${targets[@]}"; do
  coverage_args+=(--root "$target")
done
source_status=0
python3 scripts/check_import_closure.py --tracked --require-covered \
  --report "${SANITY_COVERAGE_REPORT:-.lake/library-sanity-coverage.json}" \
  "${coverage_args[@]}" || source_status=$?
if [[ "$mode" == --coverage ]]; then
  exit "$source_status"
fi

# Check cached Git access and origins before invoking Lake.
python3 scripts/check_lake_checkouts.py

dependency_status=0
python3 ../upgrades/4.33.1/replay.py --verify-required || dependency_status=$?
build_status=0
freshness_status=0
if [[ "$mode" == build ]]; then
  lake build "${targets[@]}" || build_status=$?
fi
lake --no-build build "${targets[@]}" || freshness_status=$?
printf 'Sanity exit statuses: build=%s freshness=%s imports/coverage=%s dependencies=%s\n' \
  "$([[ "$mode" == build ]] && printf '%s' "$build_status" || printf 'not-run')" \
  "$freshness_status" "$source_status" "$dependency_status"
if (( build_status || freshness_status || source_status || dependency_status )); then
  printf 'Library qualification incomplete; see the failures and coverage report.\n' >&2
  exit 1
fi
