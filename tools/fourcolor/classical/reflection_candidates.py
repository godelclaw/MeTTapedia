#!/usr/bin/env python3
"""Find single-edge charge certificates related by reflection.

This is a candidate search, not a proof or a Boolean checker-equivariance
claim. The semantic transport theorem is FourColor.ChargeBound.reflect.
Each proposed replacement still needs a checked consumer in the coverage
argument. Exact rotated-input duplicates are counted separately.
"""

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re

from replay_adapters import REFERENCE_REVISION, capture


PART_TOKEN = r"Part\.(?:cons8|cons7|cons6|cons|nil)|\.pr[5-9][5-9]"


def parse_part(body):
    """Read the pinned presentation's literal list of subparts, including fans."""
    tokens = re.findall(PART_TOKEN, body)
    remaining = re.sub(PART_TOKEN + r"|[()\s]", "", body)
    if remaining:
        raise ValueError("Unexpected part syntax: " + remaining)
    answer = []
    i = 0
    while tokens[i] != "Part.nil":
        constructor = tokens[i].removeprefix("Part.")
        count = {"cons": 2, "cons6": 2, "cons7": 3, "cons8": 4}[constructor]
        ranges = tuple(tokens[i + 1:i + count + 1])
        if len(ranges) != count or not all(r.startswith(".pr") for r in ranges):
            raise ValueError("Malformed subpart literal")
        answer.append((constructor, ranges))
        i += count + 1
    if i + 1 != len(tokens):
        raise ValueError("More than one part literal")
    return tuple(answer)


def rotate(part, n):
    if not 0 <= n <= len(part):
        raise ValueError("Rotation outside the part")
    return part[n:] + part[:n]


def mirror(part):
    """Part.mirror: move each hat, reverse the list, and reverse each fan."""
    def hat(subpart):
        return subpart[1][1 if subpart[0] == "cons" else 0]

    result = []
    for i, (constructor, ranges) in enumerate(part):
        next_hat = hat(part[(i + 1) % len(part)])
        fields = ((ranges[0], next_hat) if constructor == "cons" else
                  (next_hat, *reversed(ranges[1:])))
        result.append((constructor, fields))
    return tuple(reversed(result))


def reflect(part):
    """The reference's reflectDrule, including its five backward rotations."""
    result = mirror(part)
    for _ in range(5):
        result = rotate(result, len(part) - 1)
    return result


def read_queries(reference, n):
    rows, hashes = [], []
    for path in sorted((reference / "FourColor").glob(f"Present{n}Chk*.lean")):
        source = path.read_bytes()
        hashes.append((path.name, hashlib.sha256(source).hexdigest()))
        for name, expression in re.findall(
                r"theorem (c\w+)\s*:\s*(.*?)\s*= true := by\s*decide \+kernel",
                source.decode(), re.S):
            rows.append(dict(name=name, expression=expression.strip()))
    digest = hashlib.sha256(json.dumps(hashes).encode()).hexdigest()
    return rows, digest


def inspect_arity(reference, n):
    queries, digest = read_queries(reference, n)
    data = (reference / f"FourColor/Present{n}Defs.lean").read_text()
    parts = {name: parse_part(body) for name, body in
             re.findall(r"^def (\w+) : Part := (.*)$", data, re.M)}
    if not parts or any(len(p) != n for p in parts.values()):
        raise ValueError("Unexpected presentation part sizes")
    exact, reflected, observed = defaultdict(list), defaultdict(list), {}
    for query in queries:
        expression = query["expression"]
        if not expression.startswith("checkDbound2 "):
            continue
        match = re.fullmatch(
            r"checkDbound2 theRedpart rf(\d+)\s+"
            r"\(hubcapRot (\d+) (\d+) (\w+)\)\s+\(?(-?\d+)\)?", expression)
        if not match:
            raise ValueError("Unrecognized single-edge check: " + expression)
        fork, hub, j, name, bound = match.groups()
        if int(fork) != n or int(hub) != n:
            raise ValueError("The checker and hub arities disagree")
        j, bound = int(j), int(bound)
        part = rotate(parts[name], j - 2 if j >= 2 else n + j - 2)
        reflection = reflect(part)
        if reflect(reflection) != part:
            raise ValueError("Reflection failed its involution check")
        exact[(part, bound)].append(query["name"])
        reflected[(min(part, reflection), bound)].append(query["name"])
        observed[query["name"]] = part
    original = sum(len(names) - 1 for names in exact.values())
    potential = sum(len(names) - 1 for names in reflected.values())
    new_groups = [names for names in reflected.values()
                  if len({observed[name] for name in names}) > 1]
    return dict(arity=n, single_edge_queries=len(observed),
                exact_input_duplicates=original,
                reflection_orbit_savings=potential,
                additional_reflection_savings=potential - original,
                new_groups=new_groups,
                source_sha256=hashlib.sha256(data.encode()).hexdigest(),
                checker_sources_digest=digest)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    reference = args.reference.resolve()
    if capture(["git", "rev-parse", "HEAD"], reference) != REFERENCE_REVISION:
        raise SystemExit("Reference revision differs from the audited pin")
    report = dict(
        reference_revision=REFERENCE_REVISION,
        evidence="Program search only; no additional compression credited.",
        scope="All explicit single-edge checkDbound2 queries in arities 5 through 11; "
              "exact equal bounds; no dual-edge queries.",
        mechanism="Semantic charge transport along reflectDrule; "
                  "no Boolean checker-equivariance assumption.",
        arities=[])
    for n in range(5, 12):
        record = inspect_arity(reference, n)
        report["arities"].append(record)
        print(json.dumps({k: v for k, v in record.items() if k not in
                          ("new_groups", "source_sha256", "checker_sources_digest")}),
              flush=True)
    total = sum(r["additional_reflection_savings"] for r in report["arities"])
    report["additional_reflection_savings"] = total
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print("Total extra reflected matches:", total)


if __name__ == "__main__":
    main()
