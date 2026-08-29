#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

clone_or_sync_repo() {
  local rel_path=$1
  local branch=$2
  local pinned_rev=$3
  local work_branch=$4
  local origin_url=$5
  local upstream_url=${6:-}
  local dest="$script_dir/$rel_path"
  local cloned_now=0

  if [ -e "$dest" ]; then
    echo "skip $rel_path: already exists"
  else
    mkdir -p "$(dirname "$dest")"
    git clone --branch "$branch" "$origin_url" "$dest"
    cloned_now=1
    echo "cloned $rel_path"
  fi

  git -C "$dest" remote set-url origin "$origin_url"

  if [ -n "$upstream_url" ] && git -C "$dest" remote get-url upstream >/dev/null 2>&1; then
    git -C "$dest" remote set-url upstream "$upstream_url"
  elif [ -n "$upstream_url" ]; then
      git -C "$dest" remote add upstream "$upstream_url"
  fi

  if [ -n "$pinned_rev" ] && ! git -C "$dest" cat-file -e "${pinned_rev}^{commit}" 2>/dev/null; then
    git -C "$dest" fetch origin "$pinned_rev" ||
      { [ -n "$upstream_url" ] && git -C "$dest" fetch upstream "$pinned_rev"; }
  fi

  if [ -n "$pinned_rev" ] && [ "$cloned_now" -eq 1 ]; then
    git -C "$dest" checkout -B "$work_branch" "$pinned_rev"
    echo "pinned $rel_path -> $work_branch @ ${pinned_rev:0:12}"
  elif [ -n "$pinned_rev" ] &&
      [ "$(git -C "$dest" rev-parse HEAD)" != "$pinned_rev" ]; then
    echo "error: $rel_path exists at a revision other than the required pin" >&2
    echo "preserving the existing checkout; realign it explicitly before building" >&2
    return 1
  fi
}

# Integration repos are pinned to the exact revisions that the root Mettapedia
# build was verified against. Standalone repos are pinned too, so repeated
# bootstraps select the same source revisions.
clone_or_sync_repo "externals/Foundation" "mettapedia" \
  "85314e340ea03e62c38a78e2d24c0643578d10ee" "mettapedia" \
  "https://github.com/zariuq/Foundation.git" \
  "https://github.com/FormalizedFormalLogic/Foundation.git"
clone_or_sync_repo "externals/exchangeability" "mettapedia" \
  "05330d5c92f4400161d5e31632efcaa4a2d91361" "mettapedia" \
  "https://github.com/zariuq/exchangeability.git" \
  "https://github.com/cameronfreer/exchangeability.git"
clone_or_sync_repo "externals/Metatheory" "main" \
  "8f3275528034ceb002e7e3dba0bbeacc8de258c4" "main" \
  "https://github.com/zariuq/Metatheory.git" \
  "https://github.com/Arthur742Ramos/Metatheory.git"
clone_or_sync_repo "externals/LeaTTa" "integration/mettapedia-20260827" \
  "26d05f0663a1083085565b2e161a683542df53a8" "mettapedia-integration" \
  "https://github.com/godelclaw/LeaTTa.git" \
  "https://github.com/zariuq/LeaTTa.git"
clone_or_sync_repo "externals/certifyingDatalog" "main" \
  "91adc633bfd8d2a1565f46ba7876b73dcda55471" "main" \
  "https://github.com/zariuq/CertifyingDatalog.git" \
  "https://github.com/knowsys/CertifyingDatalog.git"
clone_or_sync_repo "externals/ordered_semigroups" "mettapedia" \
  "4324a78c436f2150403159b96b91d0f8692f3b80" "mettapedia" \
  "https://github.com/zariuq/OrderedSemigroups.git" \
  "https://github.com/ericluap/OrderedSemigroups.git"
clone_or_sync_repo "externals/provenance" "update/4.28" \
  "fe0bb6d4b2a7acf99edb13d672b7483da95937a5" "update/4.28" \
  "https://github.com/zariuq/provenance-lean.git" \
  "https://github.com/PierreSenellart/provenance-lean.git"
clone_or_sync_repo "externals/lean4lean" "master" \
  "ef849dfbd94ab5a6f3ad2793a57b8a1cbe19d923" "mettapedia-4.31" \
  "https://github.com/zariuq/lean4lean.git" \
  "https://github.com/digama0/lean4lean.git"
clone_or_sync_repo "externals/CeTTa" "main" \
  "12da03b4b055bfecff2add505e7e1ad4125bb352" "mettapedia-runtime" \
  "https://github.com/zariuq/CeTTa.git"
clone_or_sync_repo "externals/PeTTa" "main" \
  "ae66fa8e41dcd5539d614706bd4e5cfb34f9608d" "mettapedia-runtime" \
  "https://github.com/trueagi-io/PeTTa.git"
if [ "${METTAPEDIA_WITH_GF_DATA:-0}" = "1" ]; then
  clone_or_sync_repo "externals/gf-rgl" "master" \
    "0201d62777fc9c8f4ca59623d3db3fe8915e401a" "mettapedia-runtime" \
    "https://github.com/GrammaticalFramework/gf-rgl.git"
  clone_or_sync_repo "externals/gf-wordnet" "master" \
    "7cde8e343cbe967da86f928ef2aa98d3262a5c40" "mettapedia-runtime" \
    "https://github.com/GrammaticalFramework/gf-wordnet.git"
fi
clone_or_sync_repo "externals/dedukti" "master" \
  "f3c0eba869ddd46f2e75c123a59f2b612076dba0" "mettapedia-runtime" \
  "https://github.com/Deducteam/dedukti.git"
clone_or_sync_repo "externals/mm-lean4" "verified-mm-latest" \
  "c5bbaa0d6d11dccf614dadd279ca56730887fe78" "verified-mm-latest" \
  "https://github.com/zariuq/mm-lean4.git" \
  "https://github.com/digama0/mm-lean4.git"

clone_or_sync_repo "standalone/mm-lean4" "verified-mm-latest" \
  "54801711a39ebfedab9700c8989deee30196a948" "mettapedia-4.31" \
  "https://github.com/zariuq/mm-lean4.git" \
  "https://github.com/digama0/mm-lean4.git"
clone_or_sync_repo "standalone/ks-foundations-of-inference" "lean-upgrade/4.31" \
  "0072878914cfbc012ccb6ce1d2f1f8840e2b2c6a" "mettapedia-4.31" \
  "https://github.com/zariuq/ks-foundations-of-inference.git"
