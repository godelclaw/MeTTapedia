#!/usr/bin/env bash
# Replay the reviewed compatibility patch; never reset or replace upstream files.
set -euo pipefail

ns_package_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
ns_upstream_dir="$ns_package_dir/.lake/packages/EulerBlowup"
ns_patch="$ns_package_dir/patches/euler-blowup-lean-4.34.patch"
ns_expected_rev=d0124689230b58b4f86e7b90ac59de06404b3b6b

if [[ "$(git -C "$ns_upstream_dir" rev-parse HEAD)" != "$ns_expected_rev" ]]; then
  echo 'EulerBlowup revision differs from the reviewed pin; review the patch before continuing.' >&2
  exit 1
fi

if git -C "$ns_upstream_dir" apply --reverse --check "$ns_patch" 2>/dev/null; then
  echo 'EulerBlowup Lean 4.34 compatibility patch already applied.'
elif git -C "$ns_upstream_dir" apply --check "$ns_patch"; then
  git -C "$ns_upstream_dir" apply "$ns_patch"
  echo 'Applied EulerBlowup Lean 4.34 compatibility patch (five lemma-name updates).'
else
  echo 'EulerBlowup patch does not apply cleanly; no files were changed.' >&2
  exit 1
fi
