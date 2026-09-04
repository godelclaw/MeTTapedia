"""Step 3 wall test at radius 1.

Build a large hexagonal-lattice patch, apply a periodic pattern of
Stone-Wales bond rotations (each turns the four hexagons around a bond into
5,7,5,7), keep only patterns whose faces all lie in [5,7], and collect the
radius-1 flower types F(s; s_1..s_s) occurring at interior faces.  Look each
type up in the radius-1 reducibility table (patch_reducibility sweep log).

Pre-registered outcomes: WA = every curvature-dense pattern contains a
reducible flower type (the wall is excluded at radius 1 by a finite list);
WB = some pattern has NO reducible flower type and no unknown type -> an
outcome-B candidate wall (all its radius-1 disks are minimal under the
menu); WU = the verdict hinges on flower types outside the table's range.
"""
import sys, os, json, math
from collections import defaultdict, Counter
sys.path.insert(0, os.environ.get('KEMPE_DIR', '/home/oruzi/repos/ai-agents/lean/private/4cp-hexagon-lp'))
from patch_reducibility_lab import canon_outs

S3 = math.sqrt(3)


def hex_lattice(R):
    """hexagon centres within hex distance R; returns vertex positions, rotation
    system (CCW neighbour lists) and the hexagon face id map."""
    centres = {}
    for q in range(-R, R + 1):
        for s in range(-R, R + 1):
            if abs(q + s) <= R:
                centres[(q, s)] = (q * S3 + s * S3 / 2, s * 1.5)
    key = lambda p: (round(p[0] * 1000), round(p[1] * 1000))
    vid, vpos = {}, []
    hexes = {}
    edges = set()
    for c, (cx, cy) in centres.items():
        corners = []
        for k in range(6):
            th = math.radians(30 + 60 * k)
            p = (cx + math.cos(th), cy + math.sin(th))
            kk = key(p)
            if kk not in vid:
                vid[kk] = len(vpos); vpos.append(p)
            corners.append(vid[kk])
        hexes[c] = corners
        for k in range(6):
            a, b = corners[k], corners[(k + 1) % 6]
            edges.add((min(a, b), max(a, b)))
    nb = defaultdict(list)
    for a, b in edges:
        nb[a].append(b); nb[b].append(a)
    rot = {}
    for v in range(len(vpos)):
        rot[v] = sorted(nb[v], key=lambda w: math.atan2(vpos[w][1] - vpos[v][1], vpos[w][0] - vpos[v][0]))
    return vpos, rot, hexes, centres


def sw_rotate(rot, a, b):
    """rotate bond (a,b): a loses c gains e, b loses e gains c (CCW lists)."""
    ra, rb = rot[a], rot[b]
    if len(ra) != 3 or len(rb) != 3: return False
    if b not in ra or a not in rb: return False
    ia, ib = ra.index(b), rb.index(a)
    c, d = ra[(ia + 1) % 3], ra[(ia + 2) % 3]
    e, f = rb[(ib + 1) % 3], rb[(ib + 2) % 3]
    if len(rot[c]) != 3 or len(rot[e]) != 3: return False
    if e in ra or c in rb: return False
    rot[a] = [b, d, e]; rot[b] = [a, f, c]
    rot[c] = [b if w == a else w for w in rot[c]]
    rot[e] = [a if w == b else w for w in rot[e]]
    return True


def faces_of(rot):
    seen = set(); faces = []
    for u in rot:
        for v in rot[u]:
            if (u, v) in seen: continue
            f = []; cur = (u, v)
            while cur not in seen:
                seen.add(cur); f.append(cur)
                x, y = cur; r = rot[y]; k = r.index(x)
                cur = (y, r[(k + 1) % len(r)])
            faces.append(f)
    return faces


def flowers_of(rot, vpos, R):
    """interior faces (all vertices within radius R-2 of the centre) and their flower types."""
    faces = faces_of(rot)
    fverts = [[u for (u, v) in f] for f in faces]
    face_of_dart = {}
    for fi, f in enumerate(faces):
        for d in f: face_of_dart[d] = fi
    def interior(fi):
        return all(math.hypot(*vpos[v]) < (R - 2) * S3 - 0.5 for v in fverts[fi])
    types = Counter()
    for fi, f in enumerate(faces):
        if not interior(fi): continue
        s = len(f)
        outs = []
        for (u, v) in f:
            g = face_of_dart[(v, u)]      # face across this edge
            outs.append(len(faces[g]))
        types[(s, canon_outs(s, outs))] += 1
    return types, faces


def load_table(paths):
    tab = {}
    for p in paths:
        if not os.path.exists(p): continue
        for line in open(p):
            if line.startswith('{'):
                r = json.loads(line)
                tab[(r['s'], tuple(r['outs']))] = r
    return tab


def run_pattern(R, bonds_fn, name, table):
    vpos, rot, hexes, centres = hex_lattice(R)
    n_rot = 0
    for c in centres:
        for k in bonds_fn(c):
            a, b = hexes[c][k], hexes[c][(k + 1) % 6]
            if sw_rotate(rot, a, b): n_rot += 1
    types, faces = flowers_of(rot, vpos, R)
    sizes = Counter(len(f) for f in faces)
    bad = [sz for sz in sizes if sz < 5 or (sz > 7 and sz < 20)]
    if bad:
        return dict(name=name, valid=False, face_sizes=dict(sizes))
    verdict = Counter(); red_types = []; unk = []
    for (s, outs), cnt in types.items():
        r = table.get((s, outs))
        if r is None:
            verdict['unknown'] += cnt; unk.append((s, outs))
        elif r['reducible']:
            verdict['reducible'] += cnt; red_types.append((s, outs, r['certificate'] if r['certificate'] == 'D' else r['certificate'][0]))
        else:
            verdict['irreducible'] += cnt
    return dict(name=name, valid=True, rotations=n_rot, interior_faces=sum(types.values()),
                flower_types=len(types), verdict=dict(verdict), reducible_types=red_types[:6], unknown_types=unk[:6],
                face_size_hist={k: v for k, v in sizes.items() if k < 20})


def run_lattice(R, k, gens, table):
    """rotate bond k of every hexagon centre in the sublattice spanned by gens
    (interior sites only); validity judged on interior faces."""
    vpos, rot, hexes, centres = hex_lattice(R)
    (a1, b1), (a2, b2) = gens
    det = abs(a1 * b2 - a2 * b1)
    chosen = set()
    for i in range(-3 * R, 3 * R + 1):
        for j in range(-3 * R, 3 * R + 1):
            c = (i * a1 + j * a2, i * b1 + j * b2)
            if c in centres: chosen.add(c)
    n_rot = skipped = 0
    for c in sorted(chosen):
        a, b = hexes[c][k], hexes[c][(k + 1) % 6]
        deep = all(len(rot[w]) == 3 for w in [a, b] + rot[a] + rot[b])
        if not deep:
            skipped += 1; continue
        if sw_rotate(rot, a, b): n_rot += 1
        else: skipped += 1
    types, faces = flowers_of(rot, vpos, R)
    fverts = [[u for (u, v) in f] for f in faces]
    interior_sizes = Counter(len(f) for fi, f in enumerate(faces)
                             if all(math.hypot(*vpos[v]) < (R - 2) * S3 - 0.5 for v in fverts[fi]))
    valid = all(5 <= sz <= 7 for sz in interior_sizes)
    name = f"k{k} L<({a1},{b1}),({a2},{b2})> idx{det}"
    if not valid:
        return dict(name=name, valid=False, rotations=n_rot, skipped=skipped, face_sizes=dict(interior_sizes))
    verdict = Counter(); typ = []
    for (s_, outs), cnt in sorted(types.items()):
        r = table.get((s_, outs)); ring = sum(x - 4 for x in outs)
        st = 'unknown' if r is None else ('reducible' if r['reducible'] else 'irreducible')
        verdict[st] += cnt; typ.append((s_, list(outs), ring, st))
    return dict(name=name, valid=True, rotations=n_rot, skipped=skipped, interior_faces=sum(types.values()),
                face_size_hist=dict(interior_sizes), verdict=dict(verdict), types=typ)


if __name__ == '__main__':
    vpos0, rot0, hexes0, centres0 = hex_lattice(4)
    a0, b0 = hexes0[(0, 0)][0], hexes0[(0, 0)][1]
    assert sw_rotate(rot0, a0, b0)
    sz = Counter(len(f) for f in faces_of(rot0))
    assert sz[5] == 2 and sz[7] == 2, "SW rotation not 5,7,5,7"
    table = load_table(sys.argv[1:] or ['patch_sweep_B7_r12.log'])
    print(f"table: {len(table)} flower types ({sum(1 for r in table.values() if r['reducible'])} reducible)")
    R = 10
    out = []; seen = set()
    gens_list = []
    for a1 in range(0, 3):
        for b1 in range(-2, 3):
            for a2 in range(-2, 3):
                for b2 in range(0, 3):
                    det = abs(a1 * b2 - a2 * b1)
                    if det in (2, 3, 4): gens_list.append(((a1, b1), (a2, b2)))
    for k in (0, 1, 2):
        for gens in gens_list:
            r = run_lattice(R, k, gens, table)
            if not r['valid']: continue
            key = (k, tuple(sorted((t[0], tuple(t[1])) for t in r['types'])))
            if key in seen: continue
            seen.add(key); out.append(r)
            print(json.dumps(r)[:700], flush=True)
    json.dump(out, open('wall_flower_results.json', 'w'), indent=1)
    dense = [r for r in out if r['face_size_hist'].get(6, 0) * 1.0 < 0.5 * sum(r['face_size_hist'].values())]
    for r in dense: print('DENSE', r['name'], r['face_size_hist'], r['verdict'], [t for t in r['types']])
    cands = [r for r in out if r['verdict'].get('reducible', 0) == 0]
    print(f"valid tilings: {len(out)}; curvature-dense (hexagons < 50%): {len(dense)}")
    print("OUTCOME:", ("WB/WU candidates: " + "; ".join(f"{r['name']} unknown={r['verdict'].get('unknown',0)} irreducible={r['verdict'].get('irreducible',0)}" for r in cands)) if cands else "WA (every valid tiling has a reducible flower)")
