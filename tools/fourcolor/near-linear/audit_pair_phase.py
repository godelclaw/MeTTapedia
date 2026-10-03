#!/usr/bin/env python3
"""Exhaust a fixed-pair phase through its original boundary components.

Any number of switches using one pair has the same boundary endpoint as
switching a subset of the original components. PairHistory proves this
normal form. Source nonextension is certified separately in Lean; spherical
geometry and the component-to-boundary correspondence are program evidence.
"""
import argparse
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import random

from audit_boundary_observation import components, proper, switch
from audit_diamond_sources import require
from audit_forest_repair import load_case
from audit_two_port_core import eliminate
from audit_two_step_core import verify as verify_source, lean_module as prior_lean

PAIRS = tuple(combinations(range(4), 2))


def canonical(word):
    names = {}
    return tuple(names.setdefault(c, len(names)) for c in word)


def renaming(word, target):
    mapping = {}
    for a, b in zip(word, target):
        if a in mapping and mapping[a] != b:
            return None
        mapping[a] = b
    if len(set(mapping.values())) != len(mapping):
        return None
    mapping.update(zip(sorted(set(range(4)) - mapping.keys()),
                       sorted(set(range(4)) - set(mapping.values()))))
    return [mapping[c] for c in range(4)]


def sample(adj, initial, ports, patch, ring, seed):
    """A fixed bounded sample, not an arbitrary-exterior repair theorem."""
    rng, cache, seen, counts = random.Random(seed), {}, set(), {1: 0, 2: 0}
    def extends(C):
        word = tuple(C[x] for x in ports)
        if word not in cache:
            cache[word] = eliminate(patch, ring, word)[0] is not None
        return cache[word]
    def moves(C):
        for pair in PAIRS:
            for support in components(adj, C, pair):
                yield pair, support
    def apply(C, pair, support):
        a, b = pair
        return C | {x: b if C[x] == a else a for x in support}
    def distance(C):
        first = []
        for pair, support in moves(C):
            D = apply(C, pair, support)
            if extends(D):
                return 1
            first.append(D)
        for D in first:
            for pair, support in moves(D):
                if support.intersection(ports) and extends(apply(D, pair, support)):
                    return 2
        return None
    C = initial
    for step in range(10001):
        key = canonical([C[x] for x in sorted(C)])
        if not extends(C) and key not in seen:
            seen.add(key)
            d = distance(C)
            require(d is not None, 'The bounded sample now contains an exterior needing more than two switches')
            counts[d] += 1
            if len(seen) == 100:
                return {'seed': seed, 'nonextendible_colourings': len(seen),
                        'distinct_modulo_global_palette': True, 'walk_steps': step,
                        'shortest_switch_counts': counts,
                        'scope': 'One deterministic Kempe walk on a fixed spherical exterior; no uniform bound.'}
        pair, support = rng.choice(list(moves(C)))
        C = apply(C, pair, support)
        proper(adj, C)
    raise ValueError('The walk did not supply the stated sample')


def verify(here):
    prior = verify_source(here)
    repo = here.parents[2]
    require((repo / 'lean/fourcolor-classical/MettapediaFourColor/TwoStepCoreProgress.lean').read_text()
            == prior_lean(prior), 'Earlier source proofs differ from their replay')
    cases = json.loads((here / 'independent-repair-example.json').read_text())['cases']
    results = []
    for i, case in enumerate(cases):
        ambient, adj, occurrence, ring, patch, ports, C = load_case(here, case)
        old = prior['cases'][i]
        references = [old['initial_boundary']] + [r['word'] for r in old['visible_moves']]
        phases, extra = [], []
        for pair in PAIRS:
            blocks = [s for s in components(adj, C, pair) if s.intersection(ports)]
            require(len(blocks) <= 4, 'The four-bit source phase representation no longer applies')
            ids = [next((j for j, s in enumerate(blocks) if v in s), 4) for v in ports]
            outcomes, codes = [], []
            for mask in range(2 ** len(blocks)):
                D = dict(C)
                for j, support in enumerate(blocks):
                    if mask >> j & 1:
                        D, actual = switch(adj, D, pair, min(support))
                        require(actual == support, 'A fixed-pair component changed during its phase')
                word = [D[x] for x in ports]
                require(eliminate(patch, ring, word)[0] is None, 'A fixed-pair phase repairs the core')
                matches = [(j, renaming(word, w)) for j, w in enumerate(references + extra)]
                found = next(((j, p) for j, p in matches if p is not None), None)
                if found is None:
                    target = list(canonical(word))
                    extra.append(target)
                    found = len(references) + len(extra) - 1, renaming(word, target)
                j, permutation = found
                require(sorted(permutation) == list(range(4)) and
                        [permutation[c] for c in word] == (references + extra)[j], 'Bad palette transport')
                codes.append([j, permutation])
                outcomes.append(word)
            phases.append({'pair': list(pair), 'boundary_component_count': len(blocks),
                           'component_ids': ids, 'normal_forms': codes, 'outcomes': outcomes})
        require(len(extra) == (3 if i == 0 else 0), 'Unexpected number of new rejection words')
        result = {'configuration': occurrence['configuration'], 'phases': phases,
                        'additional_words': extra,
                        'subsets_including_empty': sum(len(p['outcomes']) for p in phases),
                        'distinct_boundary_endpoints': len({tuple(w) for p in phases for w in p['outcomes']}),
                        'bounded_sample': sample(adj, C, ports, patch, ring, 2026100300 + i)}
        if i == 0:
            nearby = min(old['silent_preparation']['successful_next_moves'], key=lambda r: r['size'])['word']
            require(sum(a != b for a, b in zip(old['initial_boundary'], nearby)) == 1,
                    'The nearby supported boundary is not one edit away')
            core, _ = eliminate(patch, ring, nearby)
            require(core is not None, 'The nearby word does not extend')
            result['one_port_extension'] = {'boundary': nearby,
                'core': [core[x] for x in range(ring, len(patch))],
                'scope': 'Distance in boundary colours is one; no fixed-pair physical phase reaches any extension.'}
        results.append(result)
    return {'evidence': 'General fixed-pair history invariant and source phase nonextension kernel checked; spherical correspondence and samples program checked.',
            'source_fixture_sha256': prior['fixture_sha256'], 'cases': results,
            'scope': 'The two original exteriors require a change of colour pair to repair. '
                     'Mixed-pair two-switch repairs remain available. The bounded samples prove no universal two-switch bound.'}


def lean_module(result):
    colours = lambda xs: '[' + ','.join('c' + str(c) for c in xs) + ']'
    out = ['import MettapediaFourColor.TwoStepCoreProgress',
           'import Mettapedia.GraphTheory.Kempe.PairHistory', '', '/-!',
           '# Exact source obstructions for whole fixed-pair phases', '',
           'Generated by `audit_pair_phase.py`. The component labels are the',
           'program-checked boundary observations of the spherical exteriors.',
           'Every subset is transported by an injective palette renaming to an',
           'earlier rejection word or one of three additional words.',
           'No bound on the length of a fixed-pair history is being assumed.', '-/', '',
           'namespace FourColor.PairPhaseCore', '',
           'open Color FiveTriangleCollapseObstruction TwoStepCoreProgress',
           'open SimpleGraph.ColoringListPropagation', '',
           'def pairs : Fin 6 → Color × Color := ![(c0,c1),(c0,c2),(c0,c3),(c1,c2),(c1,c3),(c2,c3)]',
           'def tag : Color → Nat | c0 => 0 | c1 => 1 | c2 => 2 | c3 => 3',
           'def rename (code : Nat × List Color) (c : Color) : Color := code.2.getD (tag c) c0', '',
           'def extraWord : Fin 3 → Fin 11 → Color :=',
           '  ![' + ',\n    '.join('!' + colours(w) for w in result['cases'][0]['additional_words']) + ']', '',
           'theorem extra_empty : ∀ i : Fin 3, run (upperLists (extraWord i)) (upperTrace 0) 6 = ∅ := by',
           '  decide +kernel', '',
           'theorem extra_no_extension (i : Fin 3) (C : upper.graph.Coloring Color)',
           '    (boundary : ∀ j : Fin 11, C (j.castAdd 7) = extraWord i j) : False := by',
           '  let D : (TwoPortCoreElimination.core false).Coloring Color :=',
           '    .mk (fun v => C (TwoPortCoreElimination.upperVertex v)) (fun h => C.valid h)',
           '  have fits (v : Fin 7) : D v ∈ upperLists (extraWord i) v := by',
           '    simp only [upperLists, Finset.mem_filter, Finset.mem_univ, true_and]',
           '    intro j hj',
           '    change C (TwoPortCoreElimination.upperVertex v) ≠ extraWord i j',
           '    simpa only [boundary j] using C.valid hj',
           '  exact empty_refutes (upperLists (extraWord i)) (upperTrace 0)',
           '    (upper_traces_valid 0).1 6 (extra_empty i) ⟨D, fits⟩', '']
    for name, ring, n, row in zip(['upper', 'lower'], [11, 10], [15, 14], result['cases']):
        out += [f'def {name}Reference (i : Nat) : Fin {ring} → Color :=']
        if name == 'upper':
            out += ['  if h : i < 15 then upperWord ⟨i, h⟩',
                    '  else extraWord ⟨(i - 15) % 3, Nat.mod_lt _ (by decide)⟩']
        else:
            out += ['  lowerWord ⟨i % 14, Nat.mod_lt _ (by decide)⟩']
        out += ['', f'theorem {name}_reference_rejects (i : Nat) (C : {name}.graph.Coloring Color)',
                f'    (boundary : ∀ j : Fin {ring}, C (j.castAdd 7) = {name}Reference i j) : False := by']
        if name == 'upper':
            out += ['  unfold upperReference at boundary', '  split at boundary',
                    '  · exact upper_no_extension _ C boundary', '  · exact extra_no_extension _ C boundary']
        else:
            out += ['  exact lower_no_extension _ C boundary']
        out += ['', f'def {name}Blocks : Fin 6 → Fin {ring} → Nat :=',
                '  ![' + ',\n    '.join('![' + ','.join(map(str, p['component_ids'])) + ']'
                                       for p in row['phases']) + ']', '',
                f'def {name}Counts : Fin 6 → Nat := ![' + ','.join(str(p['boundary_component_count']) for p in row['phases']) + ']', '',
                f'def {name}Table : Fin 6 → List (Nat × List Color) :=',
                '  ![' + ',\n    '.join('[' + ','.join(f'({j},{colours(p)})' for j, p in phase['normal_forms']) + ']'
                                       for phase in row['phases']) + ']', '',
                f'def {name}Code (p : Fin 6) (m : Fin 16) : Nat × List Color :=',
                f'  ({name}Table p).getD (m.val % 2 ^ {name}Counts p) (0, [c0,c1,c2,c3])', '',
                f'def {name}Phase (p : Fin 6) (m : Fin 16) (j : Fin {ring}) : Color :=',
                f'  if m.val.testBit ({name}Blocks p j) then',
                f'    Equiv.swap (pairs p).1 (pairs p).2 ({name}Word 0 j) else {name}Word 0 j', '',
                f'theorem {name}_matches : ∀ p m, Function.Injective (rename ({name}Code p m)) ∧',
                f'    ∀ j, rename ({name}Code p m) ({name}Phase p m j) = {name}Reference ({name}Code p m).1 j := by',
                '  decide +kernel', '',
                f'theorem {name}_phase_rejects (p : Fin 6) (m : Fin 16) (C : {name}.graph.Coloring Color)',
                f'    (boundary : ∀ j : Fin {ring}, C (j.castAdd 7) = {name}Phase p m j) : False := by',
                f'  let f := rename ({name}Code p m)',
                f'  let D : {name}.graph.Coloring Color := .mk (fun v => f (C v)) (fun h =>',
                f'    fun eq => C.valid h (({name}_matches p m).1 eq))',
                f'  apply {name}_reference_rejects ({name}Code p m).1 D',
                '  intro j',
                f'  change rename ({name}Code p m) (C (j.castAdd 7)) = _',
                '  rw [boundary j]',
                f'  exact ({name}_matches p m).2 j', '']
    near = result['cases'][0]['one_port_extension']
    out += ['def upperNearby : Fin 18 → Color :=',
            '  !' + colours(near['boundary'] + near['core']), '',
            'theorem upper_nearby_proper : ∀ x y, upper.graph.Adj x y →',
            '    upperNearby x ≠ upperNearby y := by decide +kernel', '',
            'theorem upper_nearby_one_port :',
            '    (Finset.univ.filter fun j : Fin 11 => upperNearby (j.castAdd 7) ≠ upperWord 0 j).card = 1 := by',
            '  decide +kernel', '']
    return '\n'.join(out + ['end FourColor.PairPhaseCore', ''])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--lean-output', type=Path)
    parser.add_argument('--check-lean', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    generated = lean_module(result)
    if args.lean_output:
        args.lean_output.write_text(generated)
    if args.check_lean:
        require(args.check_lean.read_text() == generated, 'Lean phase module differs from replay')
    output = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(output)
    print(output, end='')
