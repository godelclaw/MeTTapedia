#!/usr/bin/env python3
"""Find paired charge bounds related by reflection and exchanging endpoints.

This inventory is a program search. Lean consumers must check the full part
identities and use the semantic transport lemmas before any savings count.
"""

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re

from reflection_candidates import parse_part, read_queries, reflect, rotate
from replay_adapters import REFERENCE_REVISION, capture


def pair_orbit(part, offset):
    """The four presentations of one unordered pair in the map and its mirror."""
    n = len(part)
    if not n or not 0 <= offset <= n:
        raise ValueError("Invalid paired charge offset")
    reflected = reflect(part)
    return dict(identity=(part, offset),
                swap=(rotate(part, offset), n - offset),
                reflect=(reflected, n - offset),
                reflect_swap=(rotate(reflected, n - offset), offset))


def read_paired_queries(reference, n):
    source = (reference / f"FourColor/Present{n}Defs.lean").read_bytes()
    parts = {name: parse_part(body) for name, body in
             re.findall(r"^def (\w+) : Part := (.*)$", source.decode(), re.M)}
    if not parts or any(len(p) != n for p in parts.values()):
        raise ValueError("Unexpected presentation part sizes")
    rows, digest = read_queries(reference, n)
    result = []
    for row in rows:
        expression = " ".join(row["expression"].split())
        if not expression.startswith("check2Dbound2 "):
            continue
        match = re.fullmatch(
            rf"check2Dbound2 theRedpart rf{n} \(hubcapRot {n} (\d+) (\w+)\) "
            rf"\(hubSubn {n} (\d+) (\d+)\) \(?(-?\d+)\)?", expression)
        if not match:
            raise ValueError("Unrecognized paired check: " + expression)
        i, name, k, start, bound = match.groups()
        i, k, start, bound = map(int, (i, k, start, bound))
        if start != i or not 0 <= i < n or not 0 <= k < n:
            raise ValueError("Invalid paired checker indices")
        part = rotate(parts[name], (i - 2) % n)
        offset = (k - i) % n
        result.append(dict(row, expression=expression, part=part, offset=offset,
                           bound=bound, part_name=name,
                           part_expression=f"hubcapRot {n} {i} {name}"))
    return result, hashlib.sha256(source).hexdigest(), digest


def inspect_arity(reference, n):
    rows, source_digest, checker_digest = read_paired_queries(reference, n)
    exact, reflected, combined = defaultdict(list), defaultdict(list), defaultdict(list)
    observed = {}
    for row in rows:
        orbit = pair_orbit(row["part"], row["offset"])
        exact[(orbit["identity"], row["bound"])].append(row["name"])
        reflected[(min(orbit["identity"], orbit["reflect"]), row["bound"])].append(row["name"])
        combined[(min(orbit.values()), row["bound"])].append(row["name"])
        observed[row["name"]] = orbit["identity"]
    savings = lambda groups: sum(len(names) - 1 for names in groups.values())
    groups = [names for names in combined.values()
              if len({observed[name] for name in names}) > 1]
    return dict(arity=n, paired_queries=len(rows), exact_input_duplicates=savings(exact),
                reflection_orbit_savings=savings(reflected),
                reflection_and_swap_savings=savings(combined),
                additional_symmetry_savings=savings(combined) - savings(exact),
                new_groups=groups, source_sha256=source_digest,
                checker_sources_digest=checker_digest)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    reference = args.reference.resolve()
    if capture(["git", "rev-parse", "HEAD"], reference) != REFERENCE_REVISION:
        raise SystemExit("Reference revision differs from the audited pin")
    arities = [inspect_arity(reference, n) for n in range(5, 12)]
    report = dict(reference_revision=REFERENCE_REVISION,
                  evidence="Program search; checked consumers are recorded separately in the ledger.",
                  scope="Explicit paired charge queries at arities five through eleven, with equal bounds.",
                  arities=arities,
                  additional_symmetry_savings=sum(r["additional_symmetry_savings"] for r in arities))
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    for row in arities:
        print(json.dumps({k: v for k, v in row.items()
                          if k not in ("new_groups", "source_sha256", "checker_sources_digest")}))


if __name__ == "__main__":
    main()
