import KrennComponent48RootBridge

namespace Krenn.Component48RootCommonZero.Chunk1

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData
open Krenn.FrozenCase0CollapseLayer
open Krenn.Component48Normalization
open Krenn.Component48RootBridge

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1500000 in
theorem rootBlock_of_base_and_component {R : Type*} [CommRing R]
    (full : Fin 75 → R) (base : Krenn.FrozenCase0System.CommonZero full)
    (selectedVanish : ∀ generator ∈ componentGenerators 47,
      generatorEval (reduceRaw (rawValues full)) generator = 0) :
    ∀ offset : Fin 40, eval₂Hom (Int.castRingHom R) (rootValues full)
      (Krenn.Component48.Tree.rootEquations ⟨40 + offset.val, by omega⟩).toPoly = 0 := by
  have collapse := raw_collapse_of_base_common_zero full base
  have rawZero : ∀ index, rawGeneratorEval (rawValues full) index = 0 :=
    rawComponent48_vanishes (rawValues full) collapse selectedVanish
  have identified := full_eq_reconstruct_of_raw_component full rawZero
  intro offset
  fin_cases offset
  · have source := base 396
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 397
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 429
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 612
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 218
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 463
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 221
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 468
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 470
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 223
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 478
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 227
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 445
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 492
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 616
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 230
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 511
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 233
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 512
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 514
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 235
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 525
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 236
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 239
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 438
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 240
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 536
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 190
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 543
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 185
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 188
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 45
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 47
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 48
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 49
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 51
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 59
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 61
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 62
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 63
    rw [identified] at source
    simp [Krenn.Component48.Tree.rootEquations, Krenn.Component48.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl

end Krenn.Component48RootCommonZero.Chunk1
