#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
external="$script_dir/externals/LeaTTa"

if [ ! -f "$external/lakefile.lean" ] && [ ! -f "$external/lakefile.toml" ]; then
  echo "LeaTTa is not prepared; run $script_dir/bootstrap_local_repos.sh --with-leatta" >&2
  exit 2
fi

restore_core_configuration() {
  lake --dir="$script_dir/mettapedia" --reconfigure check-build >/dev/null
}
trap restore_core_configuration EXIT

lake \
  --dir="$script_dir/mettapedia" \
  --reconfigure \
  -Kleatta \
  --packages="$script_dir/mettapedia/leatta-packages.json" \
  build LeaTTaIntegration
