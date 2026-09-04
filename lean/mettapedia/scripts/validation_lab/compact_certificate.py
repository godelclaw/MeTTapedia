"""Compact a streamed derivation DAG: per derivation keep (word, x, y, subsets)
where subsets are listed in the canonical order of the matchings of the
word's pair-ports — lexicographic order of the sorted pair list — which any
verifier can recompute independently. Concatenates several JSONL files in
order (shallow depth files first). Output: one JSON with 'derivations' and
the cap; typically ~1-2 MB instead of GBs."""
import sys, json
out, cap_json, files = sys.argv[1], sys.argv[2], sys.argv[3:]
best = json.load(open(cap_json))
def canon_key(mu): return tuple(sorted(tuple(sorted(p)) for p in mu))
ders = []; seen = set()
for f in files:
    for line in open(f):
        r = json.loads(line)
        w = tuple(r['word'])
        if w in seen: continue
        seen.add(w)
        entries = sorted(((canon_key(mu), sub) for mu, sub in r['entries']), key=lambda t: t[0])
        # subset indices refer to the producer's pair order inside mu; re-express as pairs
        subs = []
        for (mu, sub) in r['entries']:
            pass
        # store subsets as the actual chain pairs (sorted), keyed by canonical matching order
        bypairs = {}
        for mu, sub in r['entries']:
            bypairs[canon_key(mu)] = sorted(tuple(sorted(mu[t])) for t in sub)
        ordered = [bypairs[k] for k in sorted(bypairs)]
        ders.append([list(w), r['x'], r['y'], ordered])
json.dump(dict(cap=(best[0] if isinstance(best, list) else best)['cap'], derivations=ders), open(out, 'w'))
print(f"compact certificate: {len(ders)} derivations -> {out}")
