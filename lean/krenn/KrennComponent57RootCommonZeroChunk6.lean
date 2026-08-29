import KrennComponent57RootBridge

namespace Krenn.Component57RootCommonZero.Chunk6

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData
open Krenn.FrozenCase0CollapseLayer
open Krenn.Component57Normalization
open Krenn.Component57RootBridge

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1500000 in
theorem rootBlock_of_base_and_component {R : Type*} [CommRing R]
    (full : Fin 75 → R) (base : Krenn.FrozenCase0System.CommonZero full)
    (selectedVanish : ∀ generator ∈ componentGenerators 56,
      generatorEval (reduceRaw (rawValues full)) generator = 0) :
    ∀ offset : Fin 40, eval₂Hom (Int.castRingHom R) (rootValues full)
      (Krenn.Component57.Tree.rootEquations ⟨240 + offset.val, by omega⟩).toPoly = 0 := by
  have collapse := raw_collapse_of_base_common_zero full base
  have rawZero : ∀ index, rawGeneratorEval (rawValues full) index = 0 :=
    rawComponent57_vanishes (rawValues full) collapse selectedVanish
  have identified := full_eq_reconstruct_of_raw_component full rawZero
  intro offset
  fin_cases offset
  · have source := base 49
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 51
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 633
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 558
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 264
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 265
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 77
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 78
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 79
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 80
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 268
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 561
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 564
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 14
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 274
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 89
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 90
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 91
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 279
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 634
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := rawZero 8
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate, monomial_add, monomial_single_one, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 281
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 573
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 575
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 103
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 104
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 576
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 577
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 111
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 112
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 113
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 114
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 115
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 116
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 117
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 118
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 119
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 120
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 625
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 130
    rw [identified] at source
    simp [Krenn.Component57.Tree.rootEquations, Krenn.Component57.LeafB0_0.parentEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl

end Krenn.Component57RootCommonZero.Chunk6
