#!/usr/bin/env bash
set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

failed=0
slash=/
home_path_regex="(${slash}home${slash}[[:alnum:]_.-]+${slash}|~${slash}[[:alnum:]_.-]+${slash})"

if git grep -nI -E "$home_path_regex" -- .; then
  echo "error: tracked text contains a machine-local home-directory path" >&2
  failed=1
fi

if git grep -nI -E '!\(import![^\n]*[[:space:]]/' -- '*.metta'; then
  echo "error: a tracked MeTTa import uses an absolute filesystem path" >&2
  failed=1
fi

while IFS= read -r -d '' path; do
  if strings "$path" 2>/dev/null | grep -Eq "$home_path_regex"; then
    echo "$path: embedded machine-local home-directory path" >&2
    failed=1
  fi
done < <(git ls-files -z)

if (( failed )); then
  exit 1
fi

echo "OK: tracked text, binaries, and MeTTa imports contain no machine-local home paths"
