#!/usr/bin/env python3
"""Independently check the finite inputs to the shared seven-pair sector.

The Lean theorem concerns actual facial readings in arbitrary ambient maps.
This program checks its chart, rule maps, exclusion paths and eight low
boundary assignments; it does not establish geometric coverage.
"""
from hashlib import sha256
import itertools
import json
from pathlib import Path
import re

from audit_diamond_sources import require
from probe_flat_pairs import read_rules, geometry, reading
from audit_chain_boundary import distances


def verify(here):
    source = here.parents[2] / 'lean/fourcolor-classical/MettapediaFourColor/SevenPairSectorData.lean'
    raw = source.read_bytes()
    text = raw.decode()
    proof = source.with_name('SevenPairSector.lean').read_text()
    match = re.search(r'def observed : Finset Label := \{([^}]+)\}', proof)
    require(match is not None, 'Missing observed degree set')
    observed = set(map(int, match[1].split(',')))

    def array(name):
        match = re.search(r'def ' + name + r' : ByteArray := ("(?:\\.|[^"\\])*")\.toUTF8', text)
        require(match is not None, f'Missing {name}')
        return [ord(c) - 65 for c in json.loads(match[1])]

    words = array('faceBytes')
    require(len(words) == 93, 'Expected 31 facial triangles')
    faces = [tuple(words[i:i+3]) for i in range(0, len(words), 3)]
    degrees = array('degreeBytes')
    require(len(degrees) == 21, 'Expected 21 encoded degree values')
    nxt, prv, neighbors = {}, {}, {i: set() for i in range(24)}
    for a, b, c in faces:
        require(len({a,b,c}) == 3, 'Degenerate source face')
        for u, v, w in [(a,b,c), (b,c,a), (c,a,b)]:
            require((u,v) not in nxt, 'Overlapping source corners')
            nxt[u,v], prv[u,w] = w, v
            neighbors[u].update([v,w])
    tips, witness = array('tipBytes'), array('witnessBytes')
    require(len(tips) == len(witness) == 576, 'Lookup sizes differ')
    for a, b in itertools.product(range(24), repeat=2):
        require(tips[24*a+b] == nxt.get((a,b), -1)+1, 'Tip lookup differs')
        require((tips[24*a+b] != 0 or tips[24*b+a] != 0) == (b in neighbors[a]),
                'Direct edge lookup differs from the facial adjacency')
        if (a,b) in nxt:
            f = faces[witness[24*a+b]]
            require((a,b,nxt[a,b]) in [f, (f[1],f[2],f[0]), (f[2],f[0],f[1])],
                    'Face witness differs')
    rim_match = re.search(r'def rim : Fin 7 → Label := !\[([^]]+)\]', proof)
    require(rim_match is not None, 'Missing ordered centre rim')
    outer_rims = re.findall(r'!\[([^]]+)\] : Fin 6 → Label', proof)
    require(outer_rims and len(set(outer_rims)) == 1, 'Outer cyclic lists disagree')
    centre_rim = list(map(int, rim_match[1].split(',')))
    outer_rim = list(map(int, outer_rims[0].split(',')))
    for centre, rim in [(1, centre_rim), (15, outer_rim)]:
        require(all(nxt[centre,a] == b for a,b in zip(rim,rim[1:]+rim[:1])),
                'Cyclic order used for local injectivity differs')
    for a,b,c in re.findall(r'SevenPairSectorData\.Turn (\d+) (\d+) (\d+)', proof):
        require(nxt[int(a),int(b)] == int(c), 'Chord exclusion corners differ')
    rules, revision = read_rules(here)

    def follow(trace, root):
        a, b = root
        path = []
        for op, _, _ in trace:
            if op == 0:
                a, b = b, a
            elif op == 1:
                b = nxt[a,b]
            else:
                b = prv[a,b]
            require(b in neighbors[a], 'Path leaves observed edges')
            path.extend([a,b])
        return (a,b), path

    block = text.split('def blockedWords', 1)[1].split('local instance', 1)[0]
    excluded = 0
    for r, row in re.findall(r'\| (\d+) => "([^"]+)"', block):
        r = int(r)
        if r == 15:
            continue
        i, a, b, *route = map(int, row.split())
        end, actual = follow(rules[r][2][i], (1,0))
        require(end == (a,b) and actual == route, 'Rule exclusion path differs')
        _, lo, hi, *_ = rules[r][1][i+1]
        require(a in observed and not (lo <= degrees[a] and (hi == 0 or degrees[a] <= hi)),
                'Rule exclusion has no contradictory degree')
        excluded += 1
    require(excluded == 83, 'Not every alternative outflow is excluded')

    maps = []
    for index, rule, values in re.findall(
            r'def map(\d+) : Vertex (\d+) → Point := !\[([^]]+)\]', text):
        mapping = list(map(int, values.split(',')))
        require({i for i in mapping if i < 21} <= observed, 'Unretained degree used')
        rule = int(rule)
        data, traces = rules[rule][1:]
        sender, receiver = mapping[data[0][1]-1], mapping[data[0][2]-1]
        require(receiver == 1, 'Map has a different receiver')
        require(len(mapping) == data[0][0], 'Map has a different size')
        for i, trace in enumerate(traces):
            require(follow(trace, (sender,receiver))[0][0] == mapping[i], 'Map trace differs')
        for i, _, _, *row in data[1:]:
            a = mapping[i-1]
            for j in row:
                if j != -1:
                    require(mapping[j-1] in neighbors[a], 'Missing mapped edge')
            for j, k in zip(row, row[1:]+row[:1]):
                if j != -1 and k != -1:
                    require(nxt.get((a,mapping[j-1])) == mapping[k-1], 'Missing mapped turn')
        maps.append((int(index), rule, sender, mapping))
    require(len(maps) == 11, 'Expected eleven source-rule maps')

    cases = []
    for boundary in itertools.product([5,6], repeat=3):
        assigned = degrees + list(boundary)
        contributions = {}
        used = []
        for index, rule, sender, mapping in maps:
            rows = rules[rule][1]
            fits = all(lo <= assigned[mapping[i-1]] and
                       (hi == 0 or assigned[mapping[i-1]] <= hi)
                       for i, lo, hi, *_ in rows[1:])
            if fits:
                used.append(index)
                contributions[sender] = contributions.get(sender, 0) + rows[0][3]
        require(set(range(9)) <= set(used), 'Base transfer missing')
        require((9 in used) != (10 in used), 'Five/six repair branches differ')
        charge_lower = -10 + sum(contributions.values()) - 1
        require(charge_lower == 1, 'Signed charge lower bound differs')
        cases.append({'outer_degrees': list(boundary), 'charge_lower': charge_lower,
                      'additional_rule': maps[9 if 9 in used else 10][1]})
    fixture_path = here / 'seven-pair-sector-example.json'
    fixture = json.loads(fixture_path.read_text())
    darts, ns, fw, rv = geometry(fixture['faces'])
    require(all((b, a) in darts for a, b in darts), 'Sphere has an open edge')
    require(len(distances(ns, 0)) == len(ns), 'Sphere is disconnected')
    for v, neighbors in ns.items():
        start = min(neighbors)
        current, visited = start, set()
        while current not in visited:
            visited.add(current)
            current = fw[v, current]
        require(current == start and visited == neighbors, 'Vertex link is not one cycle')
    require(len(ns) - len(darts)//2 + len(fixture['faces']) == 2, 'Euler characteristic differs')
    require(all(fw[a,b] == c for a,b,c in faces), 'The shared sector is not realized')
    require(all(len(ns[v]) == degrees[v] for v in observed), 'Actual profile differs')
    require(all(5 <= len(ns[v]) <= 6 for v in [21,22,23]), 'Actual low guards differ')
    actual_charge = 10*(6-len(ns[1]))
    for w in ns[1]:
        for a,b,sign in [(w,1,1),(1,w,-1)]:
            actual_charge += sign*sum(r[1][0][3] for r in rules
                                     if reading(r,a,b,ns,fw,rv) is not None)
    require(actual_charge >= 1, 'Actual charge contradicts the proved lower bound')
    return {
        'evidence': 'Independent finite checks; geometric coverage is not claimed.',
        'rule_revision': revision, 'source_sha256': sha256(raw).hexdigest(),
        'chart_vertices': 24, 'facial_triangles': 31,
        'fixed_degrees': {i: degrees[i] for i in sorted(observed)},
        'unrestricted_chart_degrees': sorted(set(range(21)) - observed),
        'centres': [0,1], 'outflow_rules_excluded': excluded, 'source_rule_maps': len(maps),
        'low_boundary_cases': cases, 'further_high_candidates': [21,22,23],
        'spherical_example': {
            'fixture_sha256': sha256(fixture_path.read_bytes()).hexdigest(),
            'vertices': len(ns), 'faces': len(fixture['faces']),
            'outer_degrees': [len(ns[v]) for v in [21,22,23]],
            'second_centre_charge': actual_charge,
            'evidence': 'Independent program check of an actual profile realization; not Lean certified.'},
        'claimed_scope': 'A specified shared facial degree profile forces a further high vertex '
                         'if its second centre is flat. No patch injectivity is assumed. '
                         'Actual minimal-map geometry separates this vertex from both centres.'}


if __name__ == '__main__':
    here = Path(__file__).resolve().parent
    result = verify(here)
    (here / 'seven-pair-sector-audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
