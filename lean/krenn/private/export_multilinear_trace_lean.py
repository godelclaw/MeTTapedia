#!/usr/bin/env python3
"""Export a checked krenn-case-trace-v1 JSONL DAG as Lean certificate data.

The exporter is intentionally untrusted.  It reconstructs source-polynomial
witnesses for each rule, but the generated module is accepted only when
`Krenn.MultilinearTrace.Certificate.check` reduces to true in Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


Poly = list[list[int]]


def load_records(path: Path) -> list[dict[str, Any]]:
    records = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()]
    if not records or records[0].get("type") != "header":
        raise ValueError("missing trace header")
    if records[0].get("format") != "krenn-case-trace-v1":
        raise ValueError("unsupported trace format")
    if records[-1].get("type") != "footer" or records[-1].get("closed") is not True:
        raise ValueError("trace is not closed")
    return records


def bits(mask: int) -> list[int]:
    result: list[int] = []
    while mask:
        bit = mask & -mask
        result.append(bit.bit_length() - 1)
        mask ^= bit
    return result


def reduced(poly: Poly, zero: int) -> Poly:
    return [term for term in poly if not term[0] & zero]


def active_ids(base_count: int, extras: list[int]) -> list[int]:
    return list(range(base_count)) + extras


def find_source(polys: list[Poly], active: list[int], zero: int, predicate) -> int:
    matches = [source for source in active if predicate(reduced(polys[source], zero))]
    if not matches:
        raise ValueError("no active source polynomial witnesses a trace rule")
    return matches[0]


def finset(items: list[int]) -> str:
    if not items:
        return "∅"
    return "{" + ", ".join(map(str, items)) + "}"


def integer(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def lean_term(term: list[int]) -> str:
    mask, coefficient = term
    return (
        "{ coefficient := "
        + integer(coefficient)
        + ", support := "
        + finset(bits(mask))
        + " }"
    )


def lean_poly(poly: Poly) -> str:
    return "[" + ", ".join(lean_term(term) for term in poly) + "]"


def state(zero: int, extras: list[int]) -> str:
    zero_list = "[" + ", ".join(map(str, bits(zero))) + "]"
    extras_list = "[" + ", ".join(map(str, extras)) + "]"
    return "{ zero := " + zero_list + ", extras := " + extras_list + " }"


def collect(records: list[dict[str, Any]]) -> tuple[list[Poly], list[dict[str, Any]], dict[str, Any]]:
    header = records[0]
    polys: list[Poly] = list(header["base"])
    nodes: list[dict[str, Any]] = []
    for record in records[1:-1]:
        kind = record.get("type")
        if kind == "poly":
            if record.get("id") != len(polys):
                raise ValueError("nonsequential derived polynomial ID")
            polys.append(record["terms"])
        elif kind == "node":
            if record.get("id") != len(nodes):
                raise ValueError("nonsequential node ID")
            nodes.append(record)
        else:
            raise ValueError(f"unexpected trace record: {kind}")
    footer = records[-1]
    if footer.get("nodes") != len(nodes):
        raise ValueError("footer node count mismatch")
    return polys, nodes, footer


def lean_rule(node: dict[str, Any], polys: list[Poly], base_count: int) -> str:
    zero = node["zero"]
    active = active_ids(base_count, node["extras"])
    rule = node["rule"]
    if rule == "contradiction":
        source = find_source(
            polys,
            active,
            zero,
            lambda poly: len(poly) == 1 and poly[0][0] == 0 and poly[0][1] != 0,
        )
        return f".contradiction {source}"
    if rule == "forced":
        sources: list[tuple[int, int]] = []
        for index in bits(node["forced"]):
            mask = 1 << index
            source = find_source(
                polys,
                active,
                zero,
                lambda poly, mask=mask: len(poly) == 1
                and poly[0][0] == mask
                and poly[0][1] != 0,
            )
            sources.append((index, source))
        pairs = "[" + ", ".join(f"({index}, {source})" for index, source in sources) + "]"
        return f".forced {pairs} {node['child']}"
    if rule == "pure":
        monomial = node["monomial"]
        source = find_source(
            polys,
            active,
            zero,
            lambda poly: len(poly) == 1
            and poly[0][0] == monomial
            and poly[0][1] != 0,
        )
        indexes = bits(monomial)
        if len(indexes) != len(node["children"]):
            raise ValueError("pure child count mismatch")
        children = "[" + ", ".join(
            f"({index}, {child})" for index, child in zip(indexes, node["children"])
        ) + "]"
        return f".pure {source} {children}"
    if rule == "factor":
        pivot_mask = node["variable"]
        if pivot_mask <= 0 or pivot_mask & (pivot_mask - 1):
            raise ValueError("factor variable is not a singleton bit")
        quotient = node["quotient"]

        def witnesses(poly: Poly) -> bool:
            if not poly or any(mask == 0 or not mask & pivot_mask for mask, _ in poly):
                return False
            divided = [[mask ^ pivot_mask, coefficient] for mask, coefficient in poly]
            return divided == polys[quotient]

        source = find_source(polys, active, zero, witnesses)
        pivot = pivot_mask.bit_length() - 1
        return (
            f".factor {source} {quotient} {pivot} "
            f"{node['zero_child']} {node['quotient_child']}"
        )
    raise ValueError(f"unsupported rule: {rule}")


def frozen_base(data: dict[str, Any]) -> list[Poly]:
    variable_count = len(data["variables"])
    result: list[Poly] = []
    for equation in data["equations"]:
        combined: dict[int, int] = {}
        for coefficient, exponents in equation:
            if type(coefficient) is not int or len(exponents) != variable_count:
                raise ValueError("malformed frozen exact polynomial")
            mask = 0
            for index, exponent in enumerate(exponents):
                if type(exponent) is not int or exponent not in (0, 1):
                    raise ValueError("frozen polynomial is not multilinear")
                if exponent:
                    mask |= 1 << index
            combined[mask] = combined.get(mask, 0) + coefficient
        result.append([[mask, coefficient] for mask, coefficient in sorted(combined.items())
                       if coefficient])
    return result


def verify_frozen_binding(
    frozen_system: Path, header: dict[str, Any]
) -> tuple[str, str]:
    raw = frozen_system.read_bytes()
    data = json.loads(raw)
    if data.get("variables") != header.get("variables"):
        raise ValueError("trace variables do not equal the frozen system")
    if frozen_base(data) != header.get("base"):
        raise ValueError("trace base does not equal the frozen system")
    metadata = header.get("metadata", {})
    file_digest = hashlib.sha256(raw).hexdigest()
    if metadata.get("frozen_system_file_sha256") != file_digest:
        raise ValueError("trace metadata does not bind the frozen file bytes")
    semantic_digest = data.get("system_sha256")
    if metadata.get("frozen_system_sha256") != semantic_digest:
        raise ValueError("trace metadata does not bind the frozen semantic digest")
    return file_digest, semantic_digest


def render_data(trace: Path, frozen_system: Path, namespace: str) -> tuple[str, int]:
    records = load_records(trace)
    header = records[0]
    polys, nodes, footer = collect(records)
    base_count = len(header["base"])
    system_file_digest, frozen_semantic_digest = verify_frozen_binding(
        frozen_system, header
    )
    polynomial_lines = ["      " + lean_poly(poly) for poly in polys]
    node_lines = []
    for node in nodes:
        node_lines.append(
            "      { state := "
            + state(node["zero"], node["extras"])
            + ", rule := "
            + lean_rule(node, polys, base_count)
            + " }"
        )
    trace_digest = hashlib.sha256(trace.read_bytes()).hexdigest()
    system_digest = header["system_sha256"]
    text = f"""import KrennMultilinearTrace

namespace {namespace}

open Krenn.MultilinearTrace
open Krenn.MultilinearTrace.Certificate

def traceSHA256 : String := \"{trace_digest}\"
def traceSystemSHA256 : String := \"{system_digest}\"
def frozenSystemSemanticSHA256 : String := \"{frozen_semantic_digest}\"
def frozenSystemFileSHA256 : String := \"{system_file_digest}\"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
abbrev certificate : Certificate :=
  {{ baseCount := {base_count}
    polynomials :=
#[
{',\n'.join(polynomial_lines)}
    ]
    nodes :=
#[
{',\n'.join(node_lines)}
    ]
    root := {footer['root']} }}

end {namespace}
"""
    return text, len(nodes)


def render_proof(
    data_module: str,
    data_namespace: str,
    namespace: str,
    node_count: int,
    chunk_size: int,
) -> str:
    chunks: list[tuple[int, int, str]] = []
    for start in range(0, node_count, chunk_size):
        count = min(chunk_size, node_count - start)
        name = f"chunk_{start}_{start + count}"
        chunks.append((start, count, name))
    chunk_theorems = "\n\n".join(
        f"""set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem {name} : certificate.NodeChunkValid {start} {count} :=
  nodeChunkValid_of_checkNodes (by decide)"""
        for start, count, name in chunks
    )
    coverage_steps: list[str] = []
    for start, count, name in chunks[:-1]:
        end = start + count
        coverage_steps.extend(
            [
                f"  by_cases before_{end} : position < {end}",
                f"  · exact {name} position (by omega) before_{end}",
            ]
        )
    last_start, last_count, last_name = chunks[-1]
    coverage_steps.append(
        f"  exact {last_name} position (by omega) (by omega)"
    )
    coverage = "\n".join(coverage_steps)
    return f"""import {data_module}

namespace {namespace}

open Krenn.MultilinearTrace
open Krenn.MultilinearTrace.Certificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

abbrev certificate : Certificate := {data_namespace}.certificate
def traceSHA256 : String := {data_namespace}.traceSHA256
def traceSystemSHA256 : String := {data_namespace}.traceSystemSHA256
def frozenSystemSemanticSHA256 : String := {data_namespace}.frozenSystemSemanticSHA256
def frozenSystemFileSHA256 : String := {data_namespace}.frozenSystemFileSHA256

{chunk_theorems}

theorem valid : certificate.Valid := by
  refine ⟨by decide, by decide, validRootB_eq_true.mp (by decide), ?_⟩
  intro position inRange
  have positionBound : position < {node_count} := by simpa using inRange
{coverage}

theorem closed {{R : Type*}} [Field R] [CharZero R] :
    certificate.ClosedState (R := R) {{ zero := [], extras := [] }} :=
  closed_root_of_valid valid

/-- Concrete finite-leaf interface: the frozen base polynomials have no
common zero.  Derived quotient polynomials are internal to the checked DAG. -/
theorem baseHasNoCommonZero {{R : Type*}} [Field R] [CharZero R] :
    ¬ ∃ values : Nat → R,
      ∀ index polynomial, index < certificate.baseCount →
        certificate.polynomials[index]? = some polynomial →
        polynomial.eval values = 0 := by
  rintro ⟨values, base⟩
  exact closed values ⟨base, by simp, by simp⟩

end {namespace}

#print axioms {namespace}.valid
#print axioms {namespace}.closed
#print axioms {namespace}.baseHasNoCommonZero
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("trace", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--frozen-system", type=Path, required=True)
    parser.add_argument("--module", default="KrennX5Case1Trace")
    parser.add_argument("--namespace", default="Krenn.X5Case1Trace")
    parser.add_argument("--data-only", action="store_true")
    parser.add_argument("--data-module")
    parser.add_argument("--data-namespace")
    parser.add_argument("--chunk-size", type=int, default=64)
    args = parser.parse_args()
    data_text, node_count = render_data(args.trace, args.frozen_system, args.namespace)
    if args.data_only:
        text = data_text
    else:
        if not args.data_module or not args.data_namespace:
            parser.error("proof output requires --data-module and --data-namespace")
        text = render_proof(
            args.data_module,
            args.data_namespace,
            args.namespace,
            node_count,
            args.chunk_size,
        )
    args.output.write_text(text, encoding="utf-8")
    print(
        f"exported {args.output}: bytes={len(text.encode())} "
        f"sha256={hashlib.sha256(text.encode()).hexdigest()}"
    )


if __name__ == "__main__":
    main()
