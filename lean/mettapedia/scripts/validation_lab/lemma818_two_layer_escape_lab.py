#!/usr/bin/env python3
"""Two-layer ambient execution probe for section 9.2 Step 4.

The lab keeps the collar move honest: first compute a single Kempe switch in
the outer collar alone, then execute the same seed and color pair in the
two-layer ambient chain.  A verdict is recorded whenever the ambient component
leaves the outer collar, reaches the fixed outer inputs, or restricts to a
different outer-collar move.
"""

from __future__ import annotations

from itertools import product
from pathlib import Path
import argparse
import json
import os
from typing import Iterable

from lemma814_lkr_in_lab import COLOR_PAIRS, COLORS, TAU, proper_states
from lemma818_composite_lkr_gate1_lab import (
    GADGET_TYPES,
    GadgetType,
    word_key,
    word_names,
    words_of_length,
)
import lemma818_frontier_automaton_lab as lab


def edge_key(ref: lab.EdgeRef) -> tuple[int, str]:
    return (ref.occ, ref.edge)


def edge_ref_payload(ref: lab.EdgeRef) -> dict[str, object]:
    return {"occ": ref.occ, "edge": ref.edge}


def component_payload(component: Iterable[lab.EdgeRef]) -> list[dict[str, object]]:
    return [edge_ref_payload(ref) for ref in sorted(component, key=edge_key)]


def outer_input_refs(word: tuple[GadgetType, ...]) -> set[lab.EdgeRef]:
    return {lab.EdgeRef(0, edge) for edge in lab.orient_input_order(word[0])}


def outer_output_refs(word: tuple[GadgetType, ...]) -> set[lab.EdgeRef]:
    last = len(word) - 1
    return {lab.EdgeRef(last, edge) for edge in lab.orient_output_order(word[-1])}


def interface_key(
    outer_word: tuple[GadgetType, ...],
    outer_sequence: tuple[tuple[str, ...], ...],
) -> tuple[str, ...]:
    last = len(outer_word) - 1
    return tuple(
        lab.chain_color(outer_sequence, lab.EdgeRef(last, edge))
        for edge in lab.orient_output_order(outer_word[-1])
    )


def switched_outer_tuple_from_component(
    outer_word: tuple[GadgetType, ...],
    base_colors: tuple[str, ...],
    pair: tuple[str, str],
    component: set[lab.EdgeRef],
) -> tuple[str, ...]:
    return lab.switched_representative_color_tuple_from_base(
        outer_word, base_colors, pair, component
    )


def clear_frontier_caches() -> None:
    lab.DIRECT_PARTITION_CACHE.clear()
    lab.LIGHT_PARTITION_CACHE.clear()
    lab.BEHAVIOR_PARTITION_CACHE.clear()
    lab.representative_edges.cache_clear()
    lab.edge_adjacency.cache_clear()
    lab.representative_edge_positions.cache_clear()
    lab.local_pair_components.cache_clear()
    lab.transition_signature.cache_clear()


def slice_words(lengths: list[int]) -> list[tuple[GadgetType, ...]]:
    return [word for length in lengths for word in words_of_length(length)]


def run_id_for(
    outer_word: tuple[GadgetType, ...],
    inner_word: tuple[GadgetType, ...],
    input_key: tuple[str, ...],
) -> str:
    return f"{word_key(outer_word)}//{word_key(inner_word)}::{''.join(input_key)}"


def witness_payload(
    *,
    outer_word: tuple[GadgetType, ...],
    inner_word: tuple[GadgetType, ...],
    input_key: tuple[str, ...],
    outer_sequence_index: int,
    inner_sequence_index: int,
    outer_sequence: tuple[tuple[str, ...], ...],
    inner_sequence: tuple[tuple[str, ...], ...],
    pair: tuple[str, str],
    seed: lab.EdgeRef,
    certified_component: set[lab.EdgeRef],
    ambient_component: set[lab.EdgeRef],
    ambient_outer_component: set[lab.EdgeRef],
    target_outer_colors: tuple[str, ...],
    ambient_restricted_target: tuple[str, ...],
) -> dict[str, object]:
    return {
        "outer_word": list(word_names(outer_word)),
        "inner_word": list(word_names(inner_word)),
        "outer_input_key": list(input_key),
        "shared_interface_key": list(interface_key(outer_word, outer_sequence)),
        "outer_sequence_index": outer_sequence_index,
        "inner_sequence_index": inner_sequence_index,
        "outer_sequence_colors": [list(state) for state in outer_sequence],
        "inner_sequence_colors": [list(state) for state in inner_sequence],
        "color_pair": list(pair),
        "seed": edge_ref_payload(seed),
        "certified_component": component_payload(certified_component),
        "ambient_component": component_payload(ambient_component),
        "ambient_outer_component": component_payload(ambient_outer_component),
        "ambient_inner_component": component_payload(
            ref for ref in ambient_component if ref.occ >= len(outer_word)
        ),
        "outer_inputs_hit": component_payload(
            ambient_outer_component & outer_input_refs(outer_word)
        ),
        "target_outer_colors": list(target_outer_colors),
        "ambient_restricted_target": list(ambient_restricted_target),
        "restriction_matches_certified_target": (
            ambient_restricted_target == target_outer_colors
        ),
    }


def audit_input_fiber(
    outer_word: tuple[GadgetType, ...],
    inner_word: tuple[GadgetType, ...],
    input_key: tuple[str, ...],
    tau_states: list[tuple[str, ...]],
) -> dict[str, object]:
    outer_sequences = lab.compatible_local_sequences_for_input(
        outer_word, tau_states, input_key
    )
    outer_index_by_colors = {
        lab.representative_color_tuple(outer_word, sequence): i
        for i, sequence in enumerate(outer_sequences)
    }
    if len(outer_index_by_colors) != len(outer_sequences):
        raise AssertionError(("duplicate outer color tuple", word_names(outer_word)))

    input_refs = outer_input_refs(outer_word)
    output_refs = outer_output_refs(outer_word)
    ambient_word = outer_word + inner_word

    certified_outer_moves = 0
    ambient_lifts = 0
    strict_escapes = 0
    outer_boundary_violations = 0
    restriction_mismatches = 0
    first_strict_escape = None
    first_breaking_escape = None

    for outer_index, outer_sequence in enumerate(outer_sequences):
        outer_colors = lab.representative_color_tuple(outer_word, outer_sequence)
        for pair in COLOR_PAIRS:
            for component in lab.chain_pair_components(outer_word, outer_sequence, pair):
                if component & input_refs:
                    continue
                if not component & output_refs:
                    continue
                target_outer_colors = switched_outer_tuple_from_component(
                    outer_word, outer_colors, pair, component
                )
                if target_outer_colors not in outer_index_by_colors:
                    raise AssertionError(
                        ("missing switched outer state", word_names(outer_word))
                    )

                certified_outer_moves += 1
                shared_key = interface_key(outer_word, outer_sequence)
                inner_sequences = lab.compatible_local_sequences_for_input(
                    inner_word, tau_states, shared_key
                )
                seed = min(component, key=edge_key)

                for inner_index, inner_sequence in enumerate(inner_sequences):
                    ambient_lifts += 1
                    ambient_sequence = outer_sequence + inner_sequence
                    ambient_component = None
                    for candidate in lab.chain_pair_components(
                        ambient_word, ambient_sequence, pair
                    ):
                        if seed in candidate:
                            ambient_component = candidate
                            break
                    if ambient_component is None:
                        raise AssertionError(("missing ambient component", seed))

                    ambient_outer = {
                        ref for ref in ambient_component if ref.occ < len(outer_word)
                    }
                    ambient_restricted_target = switched_outer_tuple_from_component(
                        outer_word, outer_colors, pair, ambient_outer
                    )
                    leaves_outer = any(
                        ref.occ >= len(outer_word) for ref in ambient_component
                    )
                    hits_outer_input = bool(ambient_outer & input_refs)
                    restriction_mismatch = (
                        ambient_restricted_target != target_outer_colors
                    )

                    if leaves_outer:
                        strict_escapes += 1
                    if hits_outer_input:
                        outer_boundary_violations += 1
                    if restriction_mismatch:
                        restriction_mismatches += 1

                    if leaves_outer and first_strict_escape is None:
                        first_strict_escape = witness_payload(
                            outer_word=outer_word,
                            inner_word=inner_word,
                            input_key=input_key,
                            outer_sequence_index=outer_index,
                            inner_sequence_index=inner_index,
                            outer_sequence=outer_sequence,
                            inner_sequence=inner_sequence,
                            pair=pair,
                            seed=seed,
                            certified_component=component,
                            ambient_component=ambient_component,
                            ambient_outer_component=ambient_outer,
                            target_outer_colors=target_outer_colors,
                            ambient_restricted_target=ambient_restricted_target,
                        )
                    if (
                        hits_outer_input or restriction_mismatch
                    ) and first_breaking_escape is None:
                        first_breaking_escape = witness_payload(
                            outer_word=outer_word,
                            inner_word=inner_word,
                            input_key=input_key,
                            outer_sequence_index=outer_index,
                            inner_sequence_index=inner_index,
                            outer_sequence=outer_sequence,
                            inner_sequence=inner_sequence,
                            pair=pair,
                            seed=seed,
                            certified_component=component,
                            ambient_component=ambient_component,
                            ambient_outer_component=ambient_outer,
                            target_outer_colors=target_outer_colors,
                            ambient_restricted_target=ambient_restricted_target,
                        )

    clear_frontier_caches()
    return {
        "run_id": run_id_for(outer_word, inner_word, input_key),
        "outer_word": list(word_names(outer_word)),
        "inner_word": list(word_names(inner_word)),
        "outer_input_key": list(input_key),
        "outer_state_count": len(outer_sequences),
        "certified_outer_moves_touching_inner_boundary": certified_outer_moves,
        "ambient_lifts_tested": ambient_lifts,
        "strict_escape_count": strict_escapes,
        "outer_boundary_violation_count": outer_boundary_violations,
        "restriction_mismatch_count": restriction_mismatches,
        "passes_outer_boundary_invariance": outer_boundary_violations == 0,
        "passes_inner_restriction_correctness": restriction_mismatches == 0,
        "passes_no_inner_boundary_escape": strict_escapes == 0,
        "first_strict_escape": first_strict_escape,
        "first_breaking_escape": first_breaking_escape,
    }


def refresh_summary(report: dict[str, object]) -> None:
    fibers = report.get("fibers", [])
    assert isinstance(fibers, list)
    planned = report.get("planned_fiber_count", 0)
    assert isinstance(planned, int)
    strict = sum(int(fiber.get("strict_escape_count", 0)) for fiber in fibers)
    boundary = sum(
        int(fiber.get("outer_boundary_violation_count", 0)) for fiber in fibers
    )
    mismatch = sum(
        int(fiber.get("restriction_mismatch_count", 0)) for fiber in fibers
    )
    first_strict = next(
        (fiber.get("first_strict_escape") for fiber in fibers if fiber.get("first_strict_escape")),
        None,
    )
    first_breaking = next(
        (fiber.get("first_breaking_escape") for fiber in fibers if fiber.get("first_breaking_escape")),
        None,
    )
    report["summary"] = {
        "planned_fiber_count": planned,
        "completed_fiber_count": len(fibers),
        "remaining_fiber_count": max(0, planned - len(fibers)),
        "complete": len(fibers) == planned,
        "outer_state_count": sum(int(fiber.get("outer_state_count", 0)) for fiber in fibers),
        "certified_outer_moves_touching_inner_boundary": sum(
            int(fiber.get("certified_outer_moves_touching_inner_boundary", 0))
            for fiber in fibers
        ),
        "ambient_lifts_tested": sum(
            int(fiber.get("ambient_lifts_tested", 0)) for fiber in fibers
        ),
        "strict_escape_count": strict,
        "outer_boundary_violation_count": boundary,
        "restriction_mismatch_count": mismatch,
        "all_outer_boundary_invariance_passed": boundary == 0,
        "all_inner_restriction_correctness_passed": mismatch == 0,
        "all_no_inner_boundary_escape_passed": strict == 0,
        "verdict": (
            "counterexample"
            if strict or boundary or mismatch
            else ("pass" if len(fibers) == planned else "incomplete")
        ),
        "first_strict_escape": first_strict,
        "first_breaking_escape": first_breaking,
    }


def new_report(
    outer_lengths: list[int],
    inner_lengths: list[int],
    tau_state_count: int,
) -> dict[str, object]:
    outer_words = slice_words(outer_lengths)
    inner_words = slice_words(inner_lengths)
    planned = len(outer_words) * len(inner_words) * (len(COLORS) ** 4)
    report: dict[str, object] = {
        "schema": "fourcolor-section-9-2-two-layer-escape-l2-v1",
        "source": "Section 9.2 Step 4 two-layer ambient execution probe",
        "model": {
            "outer_layer": "tau/mirror chain used as the collar under test",
            "inner_layer": "one downstream tau/mirror chain sharing the outer layer output interface",
            "ambient_rule": "serial composition of outer and inner chains",
            "certified_move_rule": (
                "single outer-chain Kempe component disjoint from the outer input stubs "
                "and touching the shared output interface"
            ),
            "ambient_execution_rule": (
                "execute the same color pair and seed in the full two-layer chain"
            ),
        },
        "outer_lengths": outer_lengths,
        "inner_lengths": inner_lengths,
        "outer_words": [list(word_names(word)) for word in outer_words],
        "inner_words": [list(word_names(word)) for word in inner_words],
        "local_tau_state_count": tau_state_count,
        "planned_fiber_count": planned,
        "fibers": [],
    }
    refresh_summary(report)
    return report


def write_json_report(path: Path, report: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    os.replace(tmp, path)


def parse_lengths(text: str) -> list[int]:
    lengths = [int(part) for part in text.split(",") if part]
    if not lengths or any(length <= 0 for length in lengths):
        raise argparse.ArgumentTypeError("lengths must be a comma-separated list of positive integers")
    return lengths


def run_two_layer_l2(
    output: Path | None,
    resume: bool,
    outer_lengths: list[int],
    inner_lengths: list[int],
    continue_after_counterexample: bool,
) -> dict[str, object]:
    tau_states = proper_states(TAU)
    if resume and output is not None and output.exists():
        report = json.loads(output.read_text())
        report.setdefault("fibers", [])
    else:
        report = new_report(outer_lengths, inner_lengths, len(tau_states))

    fibers = report["fibers"]
    assert isinstance(fibers, list)
    done = {fiber.get("run_id") for fiber in fibers if isinstance(fiber, dict)}

    for outer_word in slice_words(outer_lengths):
        for inner_word in slice_words(inner_lengths):
            for input_key_raw in product(COLORS, repeat=4):
                input_key = tuple(input_key_raw)
                run_id = run_id_for(outer_word, inner_word, input_key)
                if run_id in done:
                    continue
                fiber = audit_input_fiber(outer_word, inner_word, input_key, tau_states)
                fibers.append(fiber)
                done.add(run_id)
                refresh_summary(report)
                if output is not None:
                    write_json_report(output, report)
                summary = report["summary"]
                assert isinstance(summary, dict)
                if (
                    summary.get("verdict") == "counterexample"
                    and not continue_after_counterexample
                ):
                    return report

    refresh_summary(report)
    if output is not None:
        write_json_report(output, report)
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, help="write a resumable JSON verdict")
    parser.add_argument("--resume", action="store_true", help="resume from --output")
    parser.add_argument(
        "--outer-lengths",
        type=parse_lengths,
        default=[2],
        help="comma-separated outer collar lengths; default: 2",
    )
    parser.add_argument(
        "--inner-lengths",
        type=parse_lengths,
        default=[1],
        help="comma-separated downstream chain lengths; default: 1",
    )
    parser.add_argument(
        "--continue-after-counterexample",
        action="store_true",
        help="finish the selected finite slice after the first counterexample",
    )
    args = parser.parse_args()

    report = run_two_layer_l2(
        output=args.output,
        resume=args.resume,
        outer_lengths=args.outer_lengths,
        inner_lengths=args.inner_lengths,
        continue_after_counterexample=args.continue_after_counterexample,
    )
    print(json.dumps(report, indent=2, sort_keys=True))
    summary = report.get("summary", {})
    if isinstance(summary, dict) and summary.get("verdict") == "counterexample":
        raise SystemExit(2)


if __name__ == "__main__":
    main()
