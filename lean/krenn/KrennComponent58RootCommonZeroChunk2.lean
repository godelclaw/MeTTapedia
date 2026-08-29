import KrennComponent58RootBridge

namespace Krenn.Component58RootCommonZero.Chunk2

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData
open Krenn.FrozenCase0CollapseLayer
open Krenn.Component58Normalization
open Krenn.Component58RootBridge

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1500000 in
theorem rootBlock_of_base_and_component {R : Type*} [CommRing R]
    (full : Fin 75 → R) (base : Krenn.FrozenCase0System.CommonZero full)
    (selectedVanish : ∀ generator ∈ componentGenerators 57,
      generatorEval (reduceRaw (rawValues full)) generator = 0) :
    ∀ offset : Fin 40, eval₂Hom (Int.castRingHom R) (rootValues full)
      (Krenn.Component58.Tree.rootEquations ⟨80 + offset.val, by omega⟩).toPoly = 0 := by
  have collapse := raw_collapse_of_base_common_zero full base
  have rawZero : ∀ index, rawGeneratorEval (rawValues full) index = 0 :=
    rawComponent58_vanishes (rawValues full) collapse selectedVanish
  have identified := full_eq_reconstruct_of_raw_component full rawZero
  intro offset
  fin_cases offset
  · have source := base 528
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 529
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 238
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 486
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 531
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 239
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 240
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 241
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 541
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 542
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 543
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 242
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 63
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 246
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 65
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 250
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 251
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 557
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 262
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 415
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 264
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 268
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 86
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 484
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 88
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 564
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 424
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 565
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 269
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 270
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 271
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 405
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 274
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 100
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 273
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 102
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 276
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 277
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 571
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 407
    rw [identified] at source
    simp [Krenn.Component58.Tree.rootEquations, Krenn.Component58.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl

end Krenn.Component58RootCommonZero.Chunk2
