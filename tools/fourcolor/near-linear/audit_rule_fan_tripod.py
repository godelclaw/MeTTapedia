#!/usr/bin/env python3
"""Check both tripod guards on legal prefixes of the saved spherical construction.

This tests actual shared faces and ambient degrees. The complete spheres and
their charge profiles are not kernel-certified by this program.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from audit_chain_boundary import subdivide
from audit_diamond_sources import read_rows, require
from audit_four_triangle_sources import verify as verify_sources
from probe_flat_pairs import geometry, initial_faces


def verify(here):
    source = verify_sources(here)
    path = here / 'seven-pair-four-triangle-example.json'
    fixture = json.loads(path.read_text())
    require(fixture['configuration_revision'] == source['revision'], 'Source revision differs')
    rows = read_rows((here / 'D0052.conf').read_text())
    n, ring = rows[0]
    require((n, ring) == (16, 10), 'Source dimensions differ')
    core = {a - ring - 1: (degree, vs) for a, degree, *vs in rows[1:]}
    cases = {
        83: dict(side=0, root=[49, 121], star=[121, 18, 104, 12, 1, 50], tip=47),
        103: dict(side=1, root=[111, 110], star=[110, 112, 77, 78, 114, 14], tip=35),
    }
    faces = subdivide(initial_faces())
    require(faces == list(map(tuple, fixture['initial_faces'])), 'Initial sphere differs')
    hits = []
    for step in range(max(cases) + 1):
        darts, ns, turn, _ = geometry(faces)
        if step in cases:
            case = cases[step]
            centre, receiver = case['root']
            require(len(ns[centre]) == 6, 'Centre degree differs')
            star = [receiver]
            for _ in range(5):
                star.append(turn[centre, star[-1]])
            require(star == case['star'], 'Star reading differs')
            require(all(len(ns[star[i]]) == 5 for i in (1, 2, 5)), 'Fixed fan differs')
            a, b = star[3:5]
            free = [len(ns[a]), len(ns[b])]
            require(free == ([7, 6] if case['side'] == 0 else [6, 7]), 'Free degrees differ')
            tip = turn[b, a]
            require(tip == case['tip'] and len(ns[tip]) == 5, 'Shared tip differs')
            images = ([star[5], centre, b, a, tip, star[2]] if case['side'] == 0
                      else [star[2], a, centre, b, star[5], tip])
            require(len(set(images)) == 6, 'Core collision')
            edges, corners = set(), set()
            for i, (degree, vs) in core.items():
                require(len(ns[images[i]]) == degree, 'Ambient source degree differs')
                neighbors = {v - ring - 1 for v in vs if v > ring}
                for j in core:
                    require((images[j] in ns[images[i]]) == (j in neighbors), 'Core edge differs')
                    if j in neighbors:
                        edges.add(tuple(sorted((i, j))))
                for u, v in zip(vs, vs[1:] + vs[:1]):
                    if u > ring and v > ring:
                        j, k = u - ring - 1, v - ring - 1
                        require(turn[images[i], images[j]] == images[k], 'Core turn differs')
                        corners.add((i, j, k))
            require(len(edges) == 9 and len(corners) == 12, 'Face inventory differs')
            hits.append(dict(step=step, **case, free_degrees=free,
                core_images=images, core_edges=len(edges), oriented_core_corners=len(corners)))
        if step == max(cases):
            break
        a, b, c, d = fixture['edge_flip_history'][step]
        i, ac = darts[a, b]
        j, ad = darts[b, a]
        require((ac, ad) == (c, d) and d not in ns[c], 'Illegal recorded flip')
        require(min(len(ns[a]), len(ns[b])) >= 6 and max(len(ns[c]), len(ns[d])) <= 6,
                'Flip degree guard differs')
        faces[i], faces[j] = (c, d, b), (d, c, a)
    return dict(evidence='Independent finite geometry checks; not a flat-pair coverage proof.',
        vertices=len(ns), checked_prefix_flips=max(cases), occurrences=hits,
        fixture_sha256=sha256(path.read_bytes()).hexdigest(),
        source_revision=source['revision'],
        verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
