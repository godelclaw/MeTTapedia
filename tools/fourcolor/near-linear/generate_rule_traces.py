#!/usr/bin/env python3
"""Compile rooted dart traversals from the complete pinned discharging rules.

Generation is untrusted. RuleTraversalData.valid certifies every emitted
source transition and endpoint in the Lean kernel.
"""

import argparse
from collections import deque
from hashlib import sha256
import json
from pathlib import Path


def compile_traces(data):
    n, sender, receiver, _ = data[0]
    rotations = {r[0] - 1: [v - 1 if v > 0 else -1 for v in r[3:]] for r in data[1:]}
    start = (sender - 1, receiver - 1)
    routes, pending, vertices = {start: []}, deque([start]), {}
    while pending:
        a, b = d = pending.popleft()
        vertices.setdefault(a, routes[d])
        row = rotations[a]
        j = row.index(b)
        for op, target in [(0, (b, a)), (1, (a, row[(j + 1) % len(row)])),
                           (2, (a, row[(j - 1) % len(row)]))]:
            if -1 in target or target in routes:
                continue
            routes[target] = routes[d] + [(op, *target)]
            pending.append(target)
    if set(vertices) != set(range(n)):
        raise ValueError('Rooted dart traversal does not reach every source vertex')
    return [vertices[v] for v in range(n)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Write the generated Lean module')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / 'discharging-sources.json').read_text())
    encoded, lengths = [], []
    for item in manifest['files']:
        raw = (here / 'discharging-rules' / item['file']).read_bytes()
        if sha256(raw).hexdigest() != item['sha256']:
            raise ValueError('Pinned source hash differs')
        data = [[int(x) for x in row.split()] for row in raw.decode().splitlines() if row.strip()]
        traces = compile_traces(data)
        lengths.extend(map(len, traces))
        encoded.append('\n'.join(' '.join(map(str, [v] + [x for step in trace for x in step]))
                                 for v, trace in enumerate(traces)) + '\n')
    assert len(encoded) == 84
    header = '''import MettapediaFourColor.RuleTraversal

/-!
# Checked traversal programs for all oriented rules

Generated from the complete pinned source by generate_rule_traces.py.
The generator supplies candidates only. Each trace is checked against the
original rule edges and known cyclic steps, and reaches its advertised vertex.
The source rules and their MIT attribution are in NearLinearRuleData.
-/

namespace FourColor.RuleTraversalData

open NearLinearRuleData RuleTraversal

set_option maxRecDepth 65536
set_option maxHeartbeats 0

set_option linter.style.longLine false in
def source (r : Fin 84) : String :=
  match r.val with
'''
    source = header + ''.join(f'  | {i} => {json.dumps(s)}\n' for i, s in enumerate(encoded))
    source += '''  | _ => ""

def vertex (r : Fin 84) (n : ℕ) : Vertex r :=
  ⟨n % size r, Nat.mod_lt _ (by have := (headers r).1; omega)⟩

def decodeMove (n : ℕ) : Move :=
  if n = 0 then .flip else if n = 1 then .next else .previous

def decode (r : Fin 84) : List ℕ → Trace r
  | op :: a :: b :: tail => (decodeMove op, (vertex r a, vertex r b)) :: decode r tail
  | _ => []

def rows (r : Fin 84) : List (List ℕ) := NearLinearDiamondData.rows (source r)
def trace (r : Fin 84) (v : Vertex r) : Trace r := decode r ((rows r).getD v.val []).tail
def root (r : Fin 84) : State r := (sender r, receiver r)

theorem valid : ∀ r : Fin 84, ∀ v : Vertex r,
    Valid r (root r) (trace r v) ∧ (lastState (root r) (trace r v)).1 = v := by
  intro r
  fin_cases r <;> decide +kernel

theorem length_le_seven : ∀ r : Fin 84, ∀ v : Vertex r, (trace r v).length ≤ 7 := by
  intro r
  fin_cases r <;> decide +kernel

end FourColor.RuleTraversalData
'''
    if args.output:
        args.output.write_text(source)
    else:
        existing = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/RuleTraversalData.lean'
        if existing.read_text() != source:
            raise ValueError('Generated Lean source differs')
    print(json.dumps({'oriented_rules': len(encoded), 'vertex_traces': len(lengths),
                      'total_operations': sum(lengths), 'maximum_operations': max(lengths),
                      'lean_source_sha256': sha256(source.encode()).hexdigest(),
                      'scope': 'Generation and source replay; kernel theorem certifies validity.'}, indent=2))


if __name__ == '__main__':
    main()
