#!/usr/bin/env python3
"""Generate the Lean modules sealing a presented slab shape's corridor theorem.

Input: a data module with the presentation `P : Pres V N k`, `valid : P.Valid`,
`endTab : Fin N → Pos V × Pos V` and the literal table `labTable`.
Output (same directory): word-chunk modules (one kernel theorem per boundary
word, assembled per chunk), the table module (table equality + chunked
stabilisation check), the shape module (two darts per vertex with explicit
witnesses, connectivity by spanning-tree chains) and the corridor module.

Usage: presented_cell_lean_gen.py <Name> <V> <N> <k> <index> <chunk> [period]
The data module `<Name>.lean` must already exist beside this script's Lean tree.
"""
import re, sys, os, math

name, V, N, k = sys.argv[1], *map(int, sys.argv[2:5])
weak = sys.argv[5] == 'weak'
index, chunk = (0, 0) if weak else map(int, sys.argv[5:7])
period = int(sys.argv[7]) if len(sys.argv) > 7 else 1
lean_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..',
                        'Mettapedia', 'GraphTheory', 'FourColor')
data = open(os.path.join(lean_dir, name + '.lean')).read()
nwords = 3 ** k
NS = f'Mettapedia.GraphTheory.FourColor.TubeSlab.{name}'
IMP = f'import Mettapedia.GraphTheory.FourColor.{name}'
OPTS = 'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n'

# --- parse endTab: edge j -> ((v,s),(v',s')) ---
m = re.search(r'def endTab[^\[]*\[(.*?)\]\n', data, re.S)
pairs = re.findall(r'\(\((\d+), (\d+)\), \((\d+), (\d+)\)\)', m.group(1))
assert len(pairs) == N, (len(pairs), N)
ends = [((int(a), int(b)), (int(c), int(d))) for a, b, c, d in pairs]

# --- word chunks ---
nchunks = 0 if weak else math.ceil(nwords / chunk)
for c in range(nchunks):
    lo, hi = c * chunk, min((c + 1) * chunk, nwords)
    out = [IMP, 'import Mathlib.Tactic.IntervalCases', '',
           f'/-! Boundary words {lo}–{hi - 1} of `{name}`: one kernel theorem per word. -/', '',
           f'namespace {NS}', f'namespace W{c}', '']
    for X in range(lo, hi):
        out.append(f'{OPTS}theorem w{X} : P.enumMask {X} = labTable[{X}]! := by decide +kernel\n')
    bound = f'(h1 : {lo} ≤ X) ' if lo > 0 else ''
    out.append(f'theorem chunk (X : Nat) {bound}(h2 : X < {hi}) : P.enumMask X = labTable[X]! := by')
    out.append('  interval_cases X')
    for X in range(lo, hi):
        out.append(f'  · exact w{X}')
    out += ['', f'end W{c}', f'end {NS}', '']
    open(os.path.join(lean_dir, f'{name}Words{c}.lean'), 'w').write('\n'.join(out))

# --- table module ---
out = [f'import Mettapedia.GraphTheory.FourColor.{name}Words{c}' for c in range(nchunks)]
if weak:
    out = []
out += ['import Mettapedia.GraphTheory.FourColor.PresentedShape', '',
        f'/-! The table of `{name}` equals the literal, and the corridor stabilises at index {index}. -/', '',
        f'namespace {NS}', '', 'open Presented Pres', '',
        'theorem all_words : ∀ X, X < ' + str(nwords) + ' → P.enumMask X = labTable[X]! := by',
        '  intro X hX']
for c in range(nchunks):
    lo, hi = c * chunk, min((c + 1) * chunk, nwords)
    if c < nchunks - 1:
        out.append(f'  by_cases c{c} : X < {hi}')
        out.append(f'  · exact W{c}.chunk X ' + ('' if lo == 0 else '(by omega) ') + f'c{c}')
    else:
        out.append(f'  exact W{c}.chunk X ' + ('' if lo == 0 else '(by omega) ') + 'hX')
out += ['', 'theorem table_eq : P.table = labTable :=',
        '  table_eq_of_forall P labTable (by decide) all_words', '']
PER = '' if period == 1 else 'Period'
PARG = '' if period == 1 else f' {period}'
for c in range(nchunks):
    out.append(f'{OPTS}theorem range{c} : stabilizesRangeAt{PER} {index}{PARG} {c * chunk} {chunk} labTable = true := by decide +kernel\n')
out += [f'theorem stabilizes : stabilizesAt{PER} {index}{PARG} {nwords} P.table = true := by',
        '  rw [table_eq]',
        f'  apply stabilizesAt{PER}_of_ranges {index}{PARG} {nwords} {chunk} labTable (by norm_num)',
        '  intro c hc',
        f'  have : c < {nchunks} := by omega',
        '  interval_cases c']
for c in range(nchunks):
    out.append(f'  · exact range{c}')
out += ['', f'end {NS}', '']
if not weak:
    open(os.path.join(lean_dir, f'{name}Table.lean'), 'w').write('\n'.join(out))

# --- shape module ---
# non-out darts at each vertex: ('edge', j, b) or ('inp', i)
at = [[] for _ in range(V)]
for j, (e0, e1) in enumerate(ends):
    at[e0[0]].append(('edge', j, 'false'))
    at[e1[0]].append(('edge', j, 'true'))
tri_src = re.search(r'def tri[^\[]*\[(.*?)\]\]\n', data, re.S).group(1) + ']'
for v, row in enumerate(re.findall(r'!\[(.*?)\]', tri_src)):
    for t, i in re.findall(r'(edge|inp|out) (\d+)', row):
        if t == 'inp':
            at[v].append(('inp', int(i)))


def dart(d):
    return f'Sum.inl ({d[1]}, {d[2]})' if d[0] == 'edge' else f'Sum.inr (Sum.inl {d[1]})'


def not_out(d):
    return 'P.notOut_inl valid _' if d[0] == 'edge' else 'P.notOut_inp valid _'


def distinct(d, d2):
    if d[0] == 'edge' and d2[0] == 'edge':
        return 'P.distinctEdge_inl valid (by decide)'
    if d[0] == 'inp':
        return 'P.distinctEdge_inp_inl valid _ _'
    return 'P.distinctEdge_inl_inp valid _ _'
adj = [[] for _ in range(V)]
for j, (e0, e1) in enumerate(ends):
    adj[e0[0]].append((e1[0], j, 'fwd'))   # false end -> true end
    adj[e1[0]].append((e0[0], j, 'bwd'))
def tree(root):
    parent = {root: None}
    order = [root]
    for u in order:
        for v, j, d in adj[u]:
            if v not in parent:
                parent[v] = (u, j, d)
                order.append(v)
    return parent, order


in_src = re.search(r'def inPos.*', data).group(0)
out_src = re.search(r'def outPos.*', data).group(0)
inpos = [(int(a), int(b)) for a, b in re.findall(r'\((\d+), (\d+)\)', in_src)]
outpos = [(int(a), int(b)) for a, b in re.findall(r'\((\d+), (\d+)\)', out_src)]
parent, order = tree(0)
if not weak:
    assert len(order) == V, 'interior graph not connected'
out = [IMP, 'import Mettapedia.GraphTheory.FourColor.PresentedShape', '',
       f'/-! `{name}` is a slab shape: two edge-darts per vertex and a connected interior. -/', '',
       f'namespace {NS}', '', 'open Presented Pres', '',
       'theorem two_darts : ∀ v : Fin ' + str(V) + ', ∃ x x\' : SlabDart (P.toTangle valid),',
       '    (P.toTangle valid).vertOf x = v ∧ (P.toTangle valid).vertOf x\' = v ∧',
       '    NotOut x ∧ NotOut x\' ∧ DistinctEdge x x\' := by',
       '  intro v', '  fin_cases v']
for v in range(V):
    d, d2 = at[v][0], at[v][1]
    assert d != d2 and not (d[0] == 'inp' and d2[0] == 'inp')
    if d[0] == 'inp':
        d, d2 = d2, d
    assert d[0] == 'edge' and (d2[0] == 'inp' or d[1] != d2[1])
    if d2[0] == 'inp':
        out.append(f'  · exact ⟨{dart(d2)}, {dart(d)}, rfl, rfl, {not_out(d2)}, {not_out(d)}, {distinct(d2, d)}⟩')
    else:
        out.append(f'  · exact ⟨{dart(d)}, {dart(d2)}, rfl, rfl, {not_out(d)}, {not_out(d2)}, {distinct(d, d2)}⟩')
out += ['', 'abbrev R := InteriorAdj (P.toTangle valid)', '']


def chains(root, tag):
    parent, order = tree(root)
    lines = []
    for v in order:
        if v == root:
            lines.append(f'theorem {tag}_{v} : Relation.ReflTransGen R {root} {v} := Relation.ReflTransGen.refl')
            continue
        u, j, d = parent[v]
        fwd = 'adj' if d == 'fwd' else 'adj\''
        lines.append(f'theorem {tag}_{v} : Relation.ReflTransGen R {root} {v} :=')
        lines.append(f'  {tag}_{u}.trans (Relation.ReflTransGen.single (P.{fwd} valid {j}))')
    return order, lines


if weak:
    # one tree per in-port root and per out-port root that is needed
    reach_in, reach_out = {}, {}
    for i, (v0, _) in enumerate(inpos):
        order_i, lines = chains(v0, f'in{i}')
        new = [v for v in order_i if v not in reach_in]
        if new:
            out += lines
            for v in new:
                reach_in[v] = (i, f'in{i}_{v}')
    for i, (v0, _) in enumerate(outpos):
        order_i, lines = chains(v0, f'out{i}')
        new = [v for v in order_i if v not in reach_out]
        if new:
            out += lines
            for v in new:
                reach_out[v] = (i, f'out{i}_{v}')
    assert len(reach_in) == V and len(reach_out) == V, 'a vertex reaches no port'
    out += ['', 'theorem reach_in : ∀ v : Fin ' + str(V) + ', ∃ i : Fin ' + str(k) + ',',
            '    Relation.ReflTransGen R ((P.toTangle valid).vertOf (Sum.inr (Sum.inl i))) v := by',
            '  intro v', '  fin_cases v']
    for v in range(V):
        out.append(f'  · exact ⟨{reach_in[v][0]}, {reach_in[v][1]}⟩')
    out += ['', 'theorem reach_out : ∀ v : Fin ' + str(V) + ', ∃ i : Fin ' + str(k) + ',',
            '    Relation.ReflTransGen R ((P.toTangle valid).vertOf (Sum.inr (Sum.inr i))) v := by',
            '  intro v', '  fin_cases v']
    for v in range(V):
        out.append(f'  · exact ⟨{reach_out[v][0]}, {reach_out[v][1]}⟩')
    out += ['', 'theorem shapeW : SlabShapeW (P.toTangle valid) := ⟨two_darts, reach_in, reach_out⟩', '',
            f'end {NS}', '']
    open(os.path.join(lean_dir, f'{name}Shape.lean'), 'w').write('\n'.join(out))
    # corridor via the tube-free lemma
    cor = ['import Mettapedia.GraphTheory.FourColor.GeneralTubeAny',
           f'import Mettapedia.GraphTheory.FourColor.{name}Shape', '',
           f'/-! No long `{name}` chain in a least counterexample, from the tube-free lemma. -/', '',
           f'namespace {NS}', '', 'open Presented Pres',
           'open GoertzelV24TwoEdgeCutMinimality GoertzelV24ConnectedEdgeShoreMajority', '',
           'variable {V : Type} [Fintype V] [DecidableEq V]',
           'variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]',
           'variable {rotation : SimpleGraphDartRotation.Data G}', '',
           f'/-- **No long `{name}` chain in a least counterexample.** -/',
           'theorem le_of_tube (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)',
           '    {inner : V → Prop} {n : Nat}',
           '    (t : TubeOf rotation.toRotationSystem (P.toTangle valid) inner n)',
           '    (hgood : GoodSide (G := G) inner) (hconn : EdgeShoreConnected G (sideShore inner))',
           '    (hcconn : EdgeShoreConnected G (ZigzagSlab.compShore (t.side n))) :',
           f'    n + 1 ≤ Nat.factorial {k} * (Nat.factorial {k} * (6 * {k} + 1)) * 2 ^ (4 ^ {k}) :=',
           '  TubeOf.le_of_tubeOf_any shapeW minimal (by norm_num) t hgood hconn hcconn', '',
           f'end {NS}', '']
    open(os.path.join(lean_dir, f'{name}Corridor.lean'), 'w').write('\n'.join(cor))
    print(f'{name}: weak shape, {V} vertices, {N} edges, width {k}')
    sys.exit(0)

for v in order:
    if v == 0:
        out.append(f'theorem up_0 : Relation.ReflTransGen R 0 0 := Relation.ReflTransGen.refl')
        out.append(f'theorem down_0 : Relation.ReflTransGen R 0 0 := Relation.ReflTransGen.refl')
        continue
    u, j, d = parent[v]
    fwd, bwd = ('adj', 'adj\'') if d == 'fwd' else ('adj\'', 'adj')
    out.append(f'theorem up_{v} : Relation.ReflTransGen R 0 {v} :=')
    out.append(f'  up_{u}.trans (Relation.ReflTransGen.single (P.{fwd} valid {j}))')
    out.append(f'theorem down_{v} : Relation.ReflTransGen R {v} 0 :=')
    out.append(f'  (Relation.ReflTransGen.single (P.{bwd} valid {j})).trans down_{u}')
out += ['', 'theorem up (v : Fin ' + str(V) + ') : Relation.ReflTransGen R 0 v := by', '  fin_cases v']
for v in range(V):
    out.append(f'  · exact up_{v}')
out += ['', 'theorem down (v : Fin ' + str(V) + ') : Relation.ReflTransGen R v 0 := by', '  fin_cases v']
for v in range(V):
    out.append(f'  · exact down_{v}')
out += ['', 'theorem connected (u v : Fin ' + str(V) + ') : Relation.ReflTransGen R u v := (down u).trans (up v)', '',
        'theorem shape : SlabShape (P.toTangle valid) := ⟨two_darts, connected⟩', '',
        f'end {NS}', '']
open(os.path.join(lean_dir, f'{name}Shape.lean'), 'w').write('\n'.join(out))

# --- corridor module ---
bound = period * math.factorial(k) ** 2 * (6 * k + 1) + index - 1
out = [f'import Mettapedia.GraphTheory.FourColor.{name}Table',
       f'import Mettapedia.GraphTheory.FourColor.{name}Shape', '',
       f'/-! No long `{name}` tube in a least counterexample. -/', '',
       f'namespace {NS}', '', 'open Presented Pres TubeRingOrbit ZigzagRing',
       'open GoertzelV24TwoEdgeCutMinimality GoertzelV24ConnectedEdgeShoreMajority', '',
       f'/-- **the abstract stabilisation hypothesis at index {index}, period {period}** -/',
       'theorem hstab (W : Set (Fin ' + str(k) + ' → Color)) :',
       f'    (relImage (P.toTangle valid))^[{index} + {period}] W = (relImage (P.toTangle valid))^[{index}] W :=',
       f'  P.hstab_of_stabilizesAt{PER} valid stabilizes (by norm_num) W', '',
       'variable {V : Type} [Fintype V] [DecidableEq V]',
       'variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]',
       'variable {rotation : SimpleGraphDartRotation.Data G}', '',
       f'/-- **No long `{name}` tube in a least counterexample.** -/',
       'theorem le_of_tube (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)',
       '    {inner : V → Prop} {n : Nat}',
       '    (t : TubeOf rotation.toRotationSystem (P.toTangle valid) inner n) (hc : t.Coherent)',
       '    (hgood : GoodSide (G := G) inner) (hconn : EdgeShoreConnected G (sideShore inner))',
       '    (hcconn : EdgeShoreConnected G (ZigzagSlab.compShore (t.side n))) :',
       f'    n ≤ {bound} := by',
       ('  have := TubeOf.le_of_tubeOf shape minimal hstab (by norm_num) t hc hgood hconn hcconn' if period == 1 else
        '  have := TubeOf.le_of_tubeOf_period shape minimal (by norm_num) hstab (by norm_num) t hc hgood hconn hcconn'),
       '  norm_num [Nat.factorial] at this',
       '  omega', '',
       f'end {NS}', '']
open(os.path.join(lean_dir, f'{name}Corridor.lean'), 'w').write('\n'.join(out))
print(f'{name}: {nchunks} word chunks, {V} vertices, {N} edges, bound {bound}')
