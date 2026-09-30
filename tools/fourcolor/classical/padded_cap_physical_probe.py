#!/usr/bin/env python3
"""Replay adjacent matching choices and literal coupled cap repairs.

Independent finite program evidence, separate from the uniform Lean proofs.
The literal examples have connected cyclic exteriors; they are not asserted
to satisfy minimal-counterexample normal form or to provide coverage.
"""
from functools import lru_cache
from collections import Counter
from pathlib import Path
import hashlib
import json

from padded_cap_geometry_probe import cycle, padded, sew
from padded_cap_probe import reconstruct

HERE = Path(__file__).resolve().parent
COLOURS = (1, 2, 3)
if not __debug__:
    raise SystemExit("Run without Python optimization: assertions are audit checks.")


def cycle_witness(word):
    for start in COLOURS:
        colour, edges = start, [start]
        for port in word:
            colour ^= port
            if colour == 0:
                break
            edges.append(colour)
        else:
            if colour == start:
                return edges[:-1]
    return None


@lru_cache(None)
def noncrossing(vertices):
    if not vertices:
        return ((),)
    first, result = vertices[0], []
    for j in range(1, len(vertices), 2):
        for inside in noncrossing(vertices[1:j]):
            for outside in noncrossing(vertices[j+1:]):
                result.append(((first, vertices[j]),) + inside + outside)
    return tuple(result)


def matching_checks(n):
    matchings, tested = noncrossing(tuple(range(n))), 0
    for matching in matchings:
        assert any(b == a+1 for a, b in matching)
        ears = [(a,b) for a,b in matching if b == a+1 or (a,b) == (0,n-1)]
        for a,b in ears:
            for old in COLOURS:
                for new in COLOURS:
                    if old == new:
                        continue
                    word = [old]*n
                    word[a] = word[b] = new
                    edges = cycle_witness(word)
                    assert edges is not None
                    assert all(edges[i] ^ edges[(i+1) % n] == word[i] for i in range(n))
                    tested += 1
    return dict(ports=n, noncrossing_matchings=len(matchings), adjacent_pair_colour_tests=tested)


def check_colour(vertex, alpha, colours):
    assert set(vertex) == set(colours)
    assert all(colours[d] == colours[alpha[d]] for d in vertex)
    stars = {}
    for d,v in vertex.items():
        stars.setdefault(v,[]).append(colours[d])
    assert all(set(cs) == set(COLOURS) and len(cs) == 3 for cs in stars.values())


def physical_example(m, old=1, new=2):
    n = 2*m
    other = old ^ new
    assert old != new and other in COLOURS
    outside, small, cap = cycle(n), cycle(n), padded(m)
    smaller, vs, al, _ = sew(outside,small)
    original, vo, ao, faces = sew(outside,cap)
    outside_edges = [new if j % 2 == 0 else other for j in range(n)]
    source_edges = [other if j % 2 == 0 else new for j in range(n)]
    before = {}
    for side,d in vs:
        before[side,d] = old if d[0] == "p" else (
            outside_edges if side == 0 else source_edges)[d[1]]
    check_colour(vs,al,before)

    # The selected literal two-colour component consists of edge zero and
    # the two ports at its endpoints. Read those ports through the sewing.
    selected = {(0,("e",0,0)),(0,("e",0,1)),(0,("p",0)),(0,("p",n-1))}
    assert all(before[d] in (old,new) for d in selected)
    for v in {vs[d] for d in selected}:
        assert {d for d in vs if d[0] == 0 and vs[d] == v and before[d] in (old,new)} <= selected
    after_outside = {d:before[0,d] for d in outside["vertex"]}
    for _,d in selected:
        after_outside[d] = new if after_outside[d] == old else old

    # Align the shared cycle edge with new, then change it to old. The
    # adjacent source ports change together with the exterior component.
    source_edges[1] = old
    word = [old]*n
    word[0] = word[1] = new
    assert all(source_edges[j] ^ source_edges[(j+1) % n] == word[j] for j in range(n))
    repaired = {(side,d):(after_outside[d] if side == 0 else
        word[d[1]] if d[0] == "p" else source_edges[d[1]]) for side,d in vs}
    check_colour(vs,al,repaired)
    assert len(set(word)) == 2
    internal, q = reconstruct(word,source_edges[::2])
    restored = {(side,d):(after_outside[d] if side == 0 else
        word[d[1]] if d[0] == "p" else internal[d[1],d[2]]) for side,d in vo}
    check_colour(vo,ao,restored)
    assert all(restored[0,d] == repaired[0,d] for d in outside["vertex"])
    assert len(original)-len(smaller) == 6*m
    return dict(sectors=m, original_vertices=len(original), smaller_vertices=len(smaller),
                vertex_loss=6*m, old_boundary_colour=old, new_boundary_colour=new,
                repaired_boundary_word=word, shared_radial_choices=q,
                exterior_darts_changed=sum(before[0,d] != after_outside[d] for d in after_outside),
                original_face_lengths=dict(sorted(Counter(map(len,faces)).items())),
                spherical_cubic_connected_bridgeless=True, actual_colouring_reconstructed=True,
                normal_form_asserted=False)


def main():
    obstruction = [2,1,1,2,1,1]
    assert cycle_witness(obstruction) is None
    checks = [matching_checks(n) for n in (6,10,14)]
    examples = [physical_example(m,c,d) for m in range(2,16)
                for c in COLOURS for d in COLOURS if c != d]
    report = dict(evidence="Independent finite program checks; not Lean certificates or a coverage theorem.",
                  program_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  dependencies=[dict(source=p.name,source_sha256=hashlib.sha256(p.read_bytes()).hexdigest())
                                for p in (HERE/"padded_cap_probe.py",HERE/"padded_cap_geometry_probe.py")],
                  opposite_parity_counterexample=dict(word=obstruction,
                      noncrossing_matching=[[0,3],[1,2],[4,5]],cycle_witness_exists=False),
                  matching_checks=checks,physical_examples=examples)
    (HERE/"padded-cap-physical-probe.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(matchings=sum(r["noncrossing_matchings"] for r in checks),
                         adjacent_tests=sum(r["adjacent_pair_colour_tests"] for r in checks),
                         physical_examples=len(examples),example=physical_example(5))))


if __name__ == "__main__":
    main()
