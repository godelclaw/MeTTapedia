import KrennComponent62RootBridge

namespace Krenn.Component62RootCommonZero.Chunk10

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData
open Krenn.FrozenCase0CollapseLayer
open Krenn.Component62Normalization
open Krenn.Component62RootBridge

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1500000 in
theorem rootBlock_of_base_and_component {R : Type*} [CommRing R]
    (full : Fin 75 → R) (base : Krenn.FrozenCase0System.CommonZero full)
    (selectedVanish : ∀ generator ∈ componentGenerators 61,
      generatorEval (reduceRaw (rawValues full)) generator = 0) :
    ∀ offset : Fin 40, eval₂Hom (Int.castRingHom R) (rootValues full)
      (Krenn.Component62.Tree.rootEquations ⟨400 + offset.val, by omega⟩).toPoly = 0 := by
  have collapse := raw_collapse_of_base_common_zero full base
  have rawZero : ∀ index, rawGeneratorEval (rawValues full) index = 0 :=
    rawComponent62_vanishes (rawValues full) collapse selectedVanish
  have identified := full_eq_reconstruct_of_raw_component full rawZero
  intro offset
  fin_cases offset
  · have source := base 314
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 355
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 579
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 295
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 296
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 297
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 298
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 299
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 300
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 301
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 303
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 181
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 254
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 190
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 191
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 185
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 188
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 418
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 412
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 630
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 215
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 625
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 217
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 633
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 638
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 243
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 244
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 250
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 290
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 311
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 256
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 315
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 258
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 257
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 312
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 318
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 320
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 321
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 323
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 347
    rw [identified] at source
    simp [Krenn.Component62.Tree.rootEquations, Krenn.Component62.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl

end Krenn.Component62RootCommonZero.Chunk10
