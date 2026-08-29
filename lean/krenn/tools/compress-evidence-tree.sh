#!/bin/bash
# Non-destructive: transparent Btrfs zstd. No file removed, no path changed.
SC="$1"; T=${KRENN_ARTIFACTS:-artifacts}/allcollapse_case_artifacts
LOG="$SC/allcollapse.log"
{
  echo "start $(date -Is)  free=$(df -h /shared | tail -1 | awk '{print $4}')"
  find "$T" -name "system.json" 2>/dev/null | head -20 > "$SC/ac_s.txt"
  while read f; do sha256sum "$f"; done < "$SC/ac_s.txt" > "$SC/ac_hb.txt" 2>/dev/null
  echo "sampled $(wc -l < "$SC/ac_hb.txt") files for the integrity gate"
  BEFORE=$(df --output=avail -B1 /shared | tail -1)
  btrfs property set "$T" compression zstd 2>/dev/null || true
  # process per-component so progress is visible and failure is contained
  for d in "$T"/case_0/*/; do
    ionice -c3 nice -n19 btrfs filesystem defragment -r -czstd "$d" >/dev/null 2>&1
  done
  ionice -c3 nice -n19 btrfs filesystem defragment -r -czstd "$T" >/dev/null 2>&1
  sync
  AFTER=$(df --output=avail -B1 /shared | tail -1)
  echo "reclaimed $(( (AFTER-BEFORE)/1024/1024 )) MiB"
  while read f; do sha256sum "$f"; done < "$SC/ac_s.txt" > "$SC/ac_ha.txt" 2>/dev/null
  if diff -q "$SC/ac_hb.txt" "$SC/ac_ha.txt" >/dev/null; then
    echo "INTEGRITY PASS - all sampled files byte-identical"
  else
    echo "INTEGRITY FAIL"; diff "$SC/ac_hb.txt" "$SC/ac_ha.txt"
  fi
  echo "done $(date -Is)  free=$(df -h /shared | tail -1 | awk '{print $4}')"
} > "$LOG" 2>&1
