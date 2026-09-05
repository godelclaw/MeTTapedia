#!/usr/bin/env python3
"""Presentation data modules for presented slab shapes.

A presentation is (V, N, k, tri, ends, inpos, outpos): `tri[v]` lists the three
slots at vertex `v` in rotation order (('edge', j) | ('inp', i) | ('out', i)),
`ends[j]` the two positions (v, s) of edge `j` (false end, true end),
`inpos[i]`/`outpos[i]` the position of in-/out-port `i`.

`enum_mask` reproduces the Lean enumerator `Pres.enumMask`: for in-word `X`
(little-endian base 3, digits 0/1/2), the bitmask of out-word numerals of the
proper colourings.  `emit` writes the Lean data module (presentation, validity
by kernel decision, literal table).  Builders: `rung(L)` (thickness-`L`
rung, width `L+2`).

Usage: presented_cell_data_gen.py check          -- self-check against sealed tables
       presented_cell_data_gen.py rung <L> <Name> -- emit the rung data module
"""
import os, re, sys, itertools

LEAN_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..',
                        'Mettapedia', 'GraphTheory', 'FourColor')


def enum_mask(V, N, k, tri, ends, inpos, outpos, X):
    x = [(X // 3 ** i) % 3 for i in range(k)]
    states = [({}, {})]  # (edge digits, out digits)
    for v in range(V):
        new = []
        for e, o in states:
            slots = tri[v]

            def look(s, e=e, o=o):
                t, i = s
                if t == 'edge':
                    return e.get(i)
                if t == 'inp':
                    return x[i]
                return o.get(i)

            def branches(s, e, o):
                if look(s, e, o) is not None:
                    yield e, o
                    return
                t, i = s
                for d in range(3):
                    if t == 'edge':
                        e2 = dict(e); e2[i] = d; yield e2, o
                    else:
                        o2 = dict(o); o2[i] = d; yield e, o2
            for e1, o1 in branches(slots[0], e, o):
                for e2, o2 in branches(slots[1], e1, o1):
                    for e3, o3 in branches(slots[2], e2, o2):
                        vals = [look(s, e3, o3) for s in slots]
                        if len(set(vals)) == 3:
                            new.append((e3, o3))
        states = new
    mask = 0
    for e, o in states:
        Y = sum(o.get(i, 0) * 3 ** i for i in range(k))
        mask |= 1 << Y
    return mask


def table(V, N, k, tri, ends, inpos, outpos):
    return [enum_mask(V, N, k, tri, ends, inpos, outpos, X) for X in range(3 ** k)]


def rung(L):
    """vertices c=0, d_t=2t-1, e_t=2t, c'=2L+1; path edges 0..2L; in-ports at c, d_t, c';
    out-ports at c, e_t, c'"""
    V, N, k = 2 * L + 2, 2 * L + 1, L + 2
    tri = [None] * V
    tri[0] = [('inp', 0), ('out', 0), ('edge', 0)]
    for t in range(1, L + 1):
        tri[2 * t - 1] = [('edge', 2 * t - 2), ('edge', 2 * t - 1), ('inp', t)]
        tri[2 * t] = [('edge', 2 * t - 1), ('edge', 2 * t), ('out', t)]
    tri[V - 1] = [('edge', 2 * L), ('inp', L + 1), ('out', L + 1)]
    ends = []
    for j in range(N):
        # edge j joins vertex j and vertex j+1 along the path
        u, w = j, j + 1
        su = tri[u].index(('edge', j)); sw = tri[w].index(('edge', j))
        ends.append(((u, su), (w, sw)))
    inpos = [(0, 0)] + [(2 * t - 1, 2) for t in range(1, L + 1)] + [(V - 1, 1)]
    outpos = [(0, 1)] + [(2 * t, 2) for t in range(1, L + 1)] + [(V - 1, 2)]
    return V, N, k, tri, ends, inpos, outpos


def rung_pair(L):
    """two rungs of thickness L, the second mirrored (slot order reversed): the layer that
    grows a strip at both ends; ports of the second copy follow those of the first"""
    V1, N1, k1, tri1, ends1, in1, out1 = rung(L)

    def sh(s, dv, de, dp):
        t, i = s
        return (t, i + de) if t == 'edge' else (t, i + dp)
    tri = [list(row) for row in tri1] + [[sh(s, V1, N1, k1) for s in reversed(row)] for row in tri1]
    ends = list(ends1)
    for (u, su), (w, sw) in ends1:
        ends.append(((u + V1, 2 - su), (w + V1, 2 - sw)))
    inpos = list(in1) + [(v + V1, 2 - sl) for v, sl in in1]
    outpos = list(out1) + [(v + V1, 2 - sl) for v, sl in out1]
    return 2 * V1, 2 * N1, 2 * k1, tri, ends, inpos, outpos


def slot_str(s):
    return f'{s[0]} {s[1]}'


def emit(name, doc, V, N, k, tri, ends, inpos, outpos, tab):
    out = ['import Mettapedia.GraphTheory.FourColor.PresentedEnum', '', '/-!', doc, '-/', '',
           f'namespace Mettapedia.GraphTheory.FourColor.TubeSlab.{name}', 'open Presented Slot', '',
           f'def tri : Fin {V} → Fin 3 → Slot {N} {k} := ![']
    out.append(',\n'.join('  ![' + ', '.join(slot_str(s) for s in tri[v]) + ']' for v in range(V)) + ']')
    out += ['', f'def endTab : Fin {N} → Pos {V} × Pos {V} := ![']
    out.append(',\n'.join(f'  (({a}, {b}), ({c}, {d}))' for (a, b), (c, d) in ends) + ']')
    out += ['', f'def endPos (e : Fin {N}) (b : Bool) : Pos {V} := if b then (endTab e).2 else (endTab e).1',
            f'def inPos : Fin {k} → Pos {V} := ![' + ', '.join(f'({a}, {b})' for a, b in inpos) + ']',
            f'def outPos : Fin {k} → Pos {V} := ![' + ', '.join(f'({a}, {b})' for a, b in outpos) + ']', '',
            f'def P : Pres {V} {N} {k} := ⟨tri, endPos, inPos, outPos⟩',
            'set_option maxRecDepth 100000 in', 'set_option maxHeartbeats 0 in',
            'theorem valid : P.Valid := by decide +kernel', '',
            'def labTable : List Nat := [']
    out.append(',\n'.join(f'  {m}' for m in tab) + ']')
    out += ['', f'end Mettapedia.GraphTheory.FourColor.TubeSlab.{name}', '']
    open(os.path.join(LEAN_DIR, name + '.lean'), 'w').write('\n'.join(out))


def parse_data_module(path):
    """read a presentation back from a data module (for self-checks)"""
    s = open(path).read()
    V, N, k = map(int, re.search(r'def P : Pres (\d+) (\d+) (\d+)', s).groups())
    tri_src = re.search(r'def tri[^\[]*\[(.*?)\]\]\n', s, re.S).group(1)
    tri = []
    for row in re.findall(r'!\[(.*?)\]', tri_src + ']'):
        tri.append([(a, int(b)) for a, b in re.findall(r'(edge|inp|out) (\d+)', row)])
    end_src = re.search(r'def endTab[^\[]*\[(.*?)\]\n', s, re.S).group(1)
    ends = [((int(a), int(b)), (int(c), int(d))) for a, b, c, d in
            re.findall(r'\(\((\d+), (\d+)\), \((\d+), (\d+)\)\)', end_src)]
    inpos = [(int(a), int(b)) for a, b in re.findall(r'\((\d+), (\d+)\)', re.search(r'def inPos.*', s).group(0))]
    outpos = [(int(a), int(b)) for a, b in re.findall(r'\((\d+), (\d+)\)', re.search(r'def outPos.*', s).group(0))]
    tab = [int(m) for m in re.findall(r'^\s+(\d+),?\]?$', s.split('def labTable')[1], re.M)]
    return V, N, k, tri, ends, inpos, outpos, tab


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'check':
        V, N, k, tri, ends, inpos, outpos, tab = parse_data_module(os.path.join(LEAN_DIR, 'PentaCell.lean'))
        mine = table(V, N, k, tri, ends, inpos, outpos)
        print('PentaCell: table entries', len(tab), 'match' if mine == tab else
              f'MISMATCH at {[i for i in range(len(tab)) if mine[i] != tab[i]][:5]}')
        # thickness-2 rung against the sealed literal
        lit = open(os.path.join(LEAN_DIR, 'RungTwoTable.lean')).read().split('def rungTableLit')[1]
        lit = [int(m) for m in re.findall(r'\b(\d+)\b', lit.split(']')[0])]
        mine = table(*rung(2))
        print('rung(2) vs rungTableLit:', 'match' if mine == lit[:len(mine)] and len(lit) == 81 else 'MISMATCH')
    elif cmd == 'rungpair':
        L, name = int(sys.argv[2]), sys.argv[3]
        data = rung_pair(L)
        emit(name, f'# Two thickness-{L} rungs, the second mirrored: the layer of a strip growing at both ends\n\nWidth {2 * L + 4}.  No word table: the corridor bound comes from the tube-free\nlemma; only the shape check is needed.', *data, [])
        print(name, 'written (no table)')
    elif cmd == 'rung':
        L, name = int(sys.argv[2]), sys.argv[3]
        data = rung(L)
        tab = table(*data)
        emit(name, f'# The thickness-{L} rung as a presented slab shape\n\nPath `c, d1, e1, …, d{L}, e{L}, c\'` of width {L + 2}: in-ports at `c`, the `d`s and `c\'`,\nout-ports at `c`, the `e`s and `c\'`.  `labTable` is the enumerator\'s table as\ncomputed by the lab, re-derived word by word in the kernel.', *data, tab)
        print(name, 'written;', 3 ** data[2], 'words')
