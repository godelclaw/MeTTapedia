#!/usr/bin/env python3
"""Fail-closed tests for receipt-backed paper table generation."""

from __future__ import annotations

import copy
import tempfile
import unittest
from pathlib import Path

import generate_wm_pln_fusion_tables as tables


H1 = "1" * 64
H2 = "2" * 64


def reducer_receipt() -> dict:
    return {
        "backend": "cetta-group-fold",
        "backend_role": "load-bearing-reducer",
        "fusion_policy": "conservative-max",
        "input_rows": 3,
        "packet_rows": 3,
        "group_rows": 2,
        "candidate_rows": 2,
        "exact_duplicate_rows_collapsed": 0,
        "partition_shards": 8,
        "active_shards": 2,
        "prediction_sha256": H1,
        "shard_manifest_sha256": H2,
        "differential_oracle": {
            "status": "passed",
            "source_rows": {"source-a": 2, "source-b": 1},
            "comparison": {"rows": 2, "maximum_absolute_error": 0.0},
            "oracle": {
                "backend": "sqlite-differential-oracle",
                "prediction_sha256": H1,
            },
        },
    }


def candidate_receipt() -> dict:
    return {
        "status": "validation-candidate-complete-not-selected-not-test",
        "job_id": "pln-path-evidence--seed-7",
        "experiment_fingerprint": H1,
        "test_split_opened": False,
        "test_plan_state": "unarmed",
        "model": {
            "sha256": H2,
            "template_count": 12,
            "parameters": {
                "max_depth": 3,
                "minimum_support": 2,
                "path_cap": 64,
                "alpha": 1,
                "beta": 1,
                "seed": 7,
            },
            "training_statistics": {
                "supervised_positive_count": 10,
                "requested_sampled_negative_count": 40,
                "actual_sampled_negative_count": 39,
                "sampled_negative_shortfall_count": 1,
                "positives_without_type_matched_negative_candidates": 1,
                "sampled_negative_shortfall_policy": "record; never broaden type",
            },
        },
        "validation": {
            "queries": 3,
            "candidate_count": {"mean": 5.0},
            "metrics": {
                "mrr": 0.2,
                "mr": 3.0,
                "hits@1": 0.0,
                "hits@3": 0.5,
                "hits@10": 1.0,
                "sampled_negative_brier": 0.1,
                "sampled_negative_brier_examples": 15,
            },
        },
    }


def plan_receipt() -> dict:
    jobs = [{"job_id": f"job-{index}"} for index in range(15)]
    return {
        "experiment_fingerprint": H1,
        "jobs": jobs,
        "test_policy": {
            "state": "unarmed",
            "split": "test.txt",
            "split_sha256": H2,
            "required_job_ids": [job["job_id"] for job in jobs],
        },
    }


def cafa_full_receipt() -> dict:
    metric_row = {
        "method": "method-a",
        "namespace": "bp",
        "threshold": 0.5,
        "value": 0.4,
        "coverage": 0.8,
    }
    return {
        "status": "full-data-cetta-group-fold-evaluation-complete",
        "target_count": 100,
        "source_inputs": [
            {
                "source": "source-a",
                "dependence_group": "group-a",
                "bytes": 1000,
                "sha256": H1,
            }
        ],
        "fusion": {
            "backend_role": "load-bearing-reducer",
            "fusion_policy": "conservative-max",
            "candidate_rows": 20,
            "prediction_sha256": H1,
            "trail_sha256": H2,
            "differential_oracle": {"status": "passed"},
        },
        "official_evaluator": {
            "canonical_summary_sha256": H1,
            "canonical_summary": {
                "result_kind": "full-partial-knowledge-evaluation",
                "semantic_sha256": H2,
                "metrics": {
                    "f_max": [metric_row],
                    "weighted_f_max": [metric_row],
                    "unweighted_semantic_distance_min": [metric_row],
                    "weighted_semantic_distance_min": [metric_row],
                },
            },
        },
    }


def grid_receipt() -> dict:
    systems = []
    for seed in (1, 2, 3, 4, 5):
        for system in (
            "biopathnet-control",
            "pln-path-evidence",
            "biopathnet-pln-hybrid",
        ):
            systems.append(
                {
                    "system": system,
                    "seed": seed,
                    "metrics": {
                        "mrr": 0.2,
                        "mr": 3.0,
                        "hits@1": 0.1,
                        "hits@3": 0.3,
                        "hits@10": 0.8,
                    },
                }
            )
    return {
        "schema_version": 1,
        "status": "frozen-one-use-test-complete",
        "split": "test",
        "test_split_opened": True,
        "experiment_fingerprint": H1,
        "systems": systems,
        "primary_comparison": {
            "left": "biopathnet-pln-hybrid",
            "right": "biopathnet-control",
            "metric": "mrr",
            "mean_difference": 0.01,
            "confidence": 0.95,
            "lower": -0.01,
            "upper": 0.03,
            "replicates": 1000,
            "query_count": 100,
        },
    }


class ReceiptTableTests(unittest.TestCase):
    def test_current_and_future_table_contracts_render(self) -> None:
        self.assertIn("byte-identical", tables.reducer_equivalence_table(reducer_receipt()))
        self.assertIn("MRR & 0.200000", tables.biopathnet_candidate_table(candidate_receipt()))
        self.assertIn("Frozen jobs & 15", tables.preregistration_table(plan_receipt(), candidate_receipt()))
        self.assertIn("Official full-target", tables.cafa5_full_table(cafa_full_receipt()))
        self.assertIn("hybrid minus fresh control", tables.biopathnet_grid_table(grid_receipt()))

    def test_omitted_receipt_is_explicitly_pending(self) -> None:
        self.assertIn("PENDING", tables.cafa5_full_table(None))
        self.assertIn("PENDING", tables.biopathnet_grid_table(None))

    def test_explicit_missing_receipt_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(tables.ReceiptError):
                tables.load(Path(directory) / "missing.json", "test")

    def test_missing_previously_defaulted_field_fails(self) -> None:
        receipt = reducer_receipt()
        del receipt["candidate_rows"]
        with self.assertRaises(tables.ReceiptFieldMissing):
            tables.reducer_equivalence_table(receipt)

    def test_candidate_shortfall_must_balance(self) -> None:
        receipt = candidate_receipt()
        receipt["model"]["training_statistics"]["actual_sampled_negative_count"] = 38
        with self.assertRaisesRegex(tables.ReceiptError, "shortfall"):
            tables.biopathnet_candidate_table(receipt)

    def test_validation_receipt_must_keep_test_closed(self) -> None:
        receipt = candidate_receipt()
        receipt["test_split_opened"] = True
        with self.assertRaisesRegex(tables.ReceiptError, "opened"):
            tables.biopathnet_candidate_table(receipt)

    def test_differential_digest_mismatch_fails(self) -> None:
        receipt = reducer_receipt()
        receipt["differential_oracle"]["oracle"]["prediction_sha256"] = H2
        with self.assertRaisesRegex(tables.ReceiptError, "digests differ"):
            tables.reducer_equivalence_table(receipt)

    def test_grid_requires_three_systems_by_five_seeds(self) -> None:
        receipt = grid_receipt()
        receipt["systems"].pop()
        with self.assertRaises(tables.ReceiptError):
            tables.biopathnet_grid_table(receipt)

    def test_receipt_text_is_latex_escaped(self) -> None:
        receipt = candidate_receipt()
        receipt["job_id"] = "job_with&meta"
        rendered = tables.biopathnet_candidate_table(receipt)
        self.assertIn(r"job\_with\&meta", rendered)

    def test_fixtures_are_not_mutated(self) -> None:
        receipt = candidate_receipt()
        original = copy.deepcopy(receipt)
        tables.biopathnet_candidate_table(receipt)
        self.assertEqual(receipt, original)


if __name__ == "__main__":
    unittest.main()
