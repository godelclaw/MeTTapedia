#!/usr/bin/env python3
"""Test shared bulk certificates from intersections of configuration supports.

Inputs are the pinned reference's cpc.py output; --planes is its compiled
tools/planes.c. This is exploratory program evidence, not a Lean proof. Failure
only means that this bulk rule did not cover the union of contract supports.
"""

import argparse
from collections import defaultdict
import hashlib
from itertools import combinations
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


SWAP = str.maketrans("123", "132")
DIGITS = str.maketrans("123", "012")


def parity(word):
    value = 0
    for c in word:
        value ^= int(c)
    return str(value)


def orient(words, rotation, reflected):
    result = set()
    for word in words:
        full = parity(word) + word
        if reflected:
            full = full[::-1]
        full = full[rotation:] + full[:rotation]
        result.add(full[1:])
    return result


def close_colors(words):
    # cpc.py already closes under the three cyclic colour permutations.
    return words | {word.translate(SWAP) for word in words}


def mask(words, ring):
    bits = bytearray((3 ** (ring - 1) + 7) // 8)
    for word in words:
        index = int(word.translate(DIGITS), 3)
        bits[index // 8] |= 1 << (index % 8)
    return int.from_bytes(bits, "little")


def read_input(path):
    data = path.read_bytes()
    lines = data.decode().splitlines()
    assert len(lines) == 3 and lines[0].startswith("ring ")
    ring = int(lines[0].split()[1])
    assert lines[1].startswith("GOOD ") and lines[2].startswith("CTR ")
    good, contract = (set(line.split()[1:]) for line in lines[1:])
    for word in good | contract:
        assert len(word) == ring - 1 and set(word) <= set("123")
        assert parity(word) != "0", "Only proper completed traces may be reoriented"
    return ring, good, contract, hashlib.sha256(data).hexdigest()


def check(planes, ring, good, contract, scratch):
    text = (f"ring {ring}\nGOOD " + " ".join(sorted(good)) +
            "\nCTR " + " ".join(sorted(contract)) + "\n")
    env = os.environ.copy()
    # Suppress inherited certificate-output locations.
    env.pop("EMIT", None)
    env.pop("EMIT2", None)
    result = subprocess.run([str(planes)], input=text, text=True,
                            capture_output=True, check=True, env=env, cwd=scratch)
    report = result.stdout + result.stderr
    matches = re.findall(r"residual_orbits=(\d+)", report)
    assert matches, "Missing bulk residual count"
    return int(matches[0])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs", required=True, type=Path)
    parser.add_argument("--planes", required=True, type=Path)
    parser.add_argument("--rings", nargs="+", type=int, default=[8, 9, 10])
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    planes = args.planes.resolve()
    selected, by_ring, inputs = {}, defaultdict(list), []
    for path in sorted(args.inputs.glob("*.in"), key=lambda p: int(p.stem)):
        index = int(path.stem)
        ring, good, contract, digest = read_input(path)
        inputs.append(dict(index=index, ring=ring, sha256=digest))
        by_ring[ring].append((index, mask(good, ring)))
        if ring in args.rings:
            selected[index] = ring, close_colors(good), close_colors(contract)
    inclusions = []
    for rows in by_ring.values():
        for i, good in rows:
            for j, other in rows:
                if i != j and good & ~other == 0:
                    inclusions.append([i, j])
    assert selected, "No configurations in the requested rings"
    controls, trials = [], []
    with tempfile.TemporaryDirectory() as scratch:
        # A checked bulk example supplies both a positive and an empty-base control.
        control_index = min(selected)
        ring, good, contract = selected[control_index]
        positive = check(planes, ring, good, contract, scratch)
        negative = check(planes, ring, set(), contract, scratch)
        assert positive == 0 and negative > 0, "The control configuration must be bulk-reducible"
        controls.append(dict(index=control_index, positive_residual=positive,
                             empty_base_residual=negative))
        for ring in sorted(set(args.rings)):
            indices = [i for i, row in selected.items() if row[0] == ring]
            for i, j in combinations(indices, 2):
                _, good, contract = selected[i]
                _, other_good, other_contract = selected[j]
                for reflected in (False, True):
                    for rotation in range(ring):
                        h = orient(other_good, rotation, reflected)
                        d = orient(other_contract, rotation, reflected)
                        assert len(h) == len(other_good) and len(d) == len(other_contract)
                        common, demand = good & h, contract | d
                        residual = check(planes, ring, common, demand, scratch)
                        trials.append(dict(indices=[i, j], ring=ring,
                                           rotation=rotation, reflected=reflected,
                                           common_support=len(common),
                                           contract_union=len(demand),
                                           residual_orbits=residual))
    report = dict(evidence="program check; not a Lean theorem",
                  inputs=inputs, rings=sorted(set(args.rings)), controls=controls,
                  fixed_order_stored_support_inclusions=inclusions,
                  pair_alignments=len(trials),
                  successes=sum(t["residual_orbits"] == 0 for t in trials),
                  closest=sorted(trials, key=lambda t: t["residual_orbits"])[:5],
                  trials=trials)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in
                      ("evidence", "pair_alignments", "successes", "controls")}))


if __name__ == "__main__":
    main()
