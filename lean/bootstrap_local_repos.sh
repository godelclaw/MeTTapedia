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
clone_or_sync_repo "externals/Foundation" "port/lean-4.34" \
  "6769009b4ca6006aefcf4176e0c7297a108a28df" "port/lean-4.34" \
  "https://github.com/zariuq/Foundation.git" \
  "https://github.com/FormalizedFormalLogic/Foundation.git"
clone_or_sync_repo "externals/exchangeability" "port/lean-4.34" \
  "772f04604bc1c503f514b5624a0a9014f15de5ac" "port/lean-4.34" \
  "https://github.com/zariuq/exchangeability.git" \
  "https://github.com/cameronfreer/exchangeability.git"
clone_or_sync_repo "externals/Metatheory" "port/lean-4.34" \
  "19129cc90a9cfb76340d69242c531a0786f8baff" "port/lean-4.34" \
  "https://github.com/zariuq/Metatheory.git" \
  "https://github.com/Arthur742Ramos/Metatheory.git"
clone_or_sync_repo "externals/LeaTTa" "port/lean-4.34" \
  "0bd84692cec20b8c605923cf7d387fda4902cfbc" "port/lean-4.34" \
  "https://github.com/godelclaw/LeaTTa.git" \
  "https://github.com/zariuq/LeaTTa.git"
clone_or_sync_repo "externals/certifyingDatalog" "port/lean-4.34" \
  "66e6308fe8382cbda43b0361d41c863ffca68040" "port/lean-4.34" \
  "https://github.com/zariuq/CertifyingDatalog.git" \
  "https://github.com/knowsys/CertifyingDatalog.git"
clone_or_sync_repo "externals/ordered_semigroups" "port/lean-4.34" \
  "fdc9df6998d1e6b3844f794371663bedc628233d" "port/lean-4.34" \
  "https://github.com/zariuq/OrderedSemigroups.git" \
  "https://github.com/ericluap/OrderedSemigroups.git"
clone_or_sync_repo "externals/provenance" "port/lean-4.34" \
  "77d0609534f3e856371e8531f46a051934cea5d5" "port/lean-4.34" \
  "https://github.com/zariuq/provenance-lean.git" \
  "https://github.com/PierreSenellart/provenance-lean.git"
clone_or_sync_repo "externals/lean4lean" "port/lean-4.34" \
  "3885cb8dc3b65d0f1dc4e7c43f0cecffea2b9add" "port/lean-4.34" \
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
clone_or_sync_repo "externals/mm-lean4" "port/lean-4.34" \
  "198f0b42b7164b66bc2ce92870226e7c35de1f7a" "port/lean-4.34" \
  "https://github.com/zariuq/mm-lean4.git" \
  "https://github.com/digama0/mm-lean4.git"

clone_or_sync_repo "standalone/mm-lean4" "port/lean-4.34" \
  "4ccd2babdf4b9d16650d8846a21c7dee2f22e1f9" "port/lean-4.34" \
  "https://github.com/zariuq/mm-lean4.git" \
  "https://github.com/digama0/mm-lean4.git"
clone_or_sync_repo "standalone/ks-foundations-of-inference" "port/lean-4.34" \
  "a329e75e33fa0515eaade0a9b0597c2cdf794313" "port/lean-4.34" \
  "https://github.com/zariuq/ks-foundations-of-inference.git"
