import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripke
import Foundation.Modal.Kripke.Logic.K
import Foundation.Modal.Kripke.Logic.KT
import Foundation.Modal.Kripke.Logic.KD
import Foundation.Modal.Kripke.Logic.K4

/-!
# Kripke WM Proof-Theoretic Closure (Implication Fragment)

This module connects class-indexed Kripke proof theory (`Sound`/`Complete`)
to WM singleton/multiset consequence inequalities for implication queries.
-/

namespace Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeCompleteness

open LO
open LO.Modal
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripke
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
open scoped ENNReal

/-- A pointed Kripke model is admissible for a frame class when its frame is in
the class. -/
def inClass (C : Kripke.FrameClass) (pk : PointedKripke) : Prop :=
  pk.model.toFrame ∈ C

/-! ## Soundness/completeness bridge from Foundation Kripke logic -/

/-- Soundness lift: provable implication gives class-indexed singleton WM consequence. -/
theorem singletonStrengthLEOn_of_provable_imp
    {S : Type*} [Entailment S (LO.Modal.Formula ℕ)]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    {φ ψ : (LO.Modal.Formula ℕ)}
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    singletonStrengthLEOn PointedKripke.satisfies (inClass C) φ ψ := by
  have himp : pointwiseImpliesOn PointedKripke.satisfies (inClass C) φ ψ := by
    intro pk hC hφ
    have hvalid : C ⊧ (φ ➝ ψ) := Sound.sound (𝓢 := 𝓢) (𝓜 := C) hprov
    have hframe : pk.model.toFrame ⊧ (φ ➝ ψ) := hvalid hC
    have hmodel : pk.model ⊧ (φ ➝ ψ) := hframe pk.model.Val
    have hworld : Formula.Kripke.Satisfies pk.model pk.world (φ ➝ ψ) := hmodel pk.world
    exact (Formula.Kripke.Satisfies.imp_def.mp hworld) hφ
  exact (pointwiseImpliesOn_iff_singletonStrengthLEOn PointedKripke.satisfies (inClass C) φ ψ).mp himp

/-- Completeness lift: class-indexed singleton WM consequence yields provable implication. -/
theorem provable_imp_of_singletonStrengthLEOn
    {S : Type*} [Entailment S (LO.Modal.Formula ℕ)]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Complete 𝓢 C]
    {φ ψ : (LO.Modal.Formula ℕ)}
    (hsing : singletonStrengthLEOn PointedKripke.satisfies (inClass C) φ ψ) :
    𝓢 ⊢ (φ ➝ ψ) := by
  have himp : pointwiseImpliesOn PointedKripke.satisfies (inClass C) φ ψ :=
    (pointwiseImpliesOn_iff_singletonStrengthLEOn PointedKripke.satisfies (inClass C) φ ψ).mpr hsing
  have hvalid : C ⊧ (φ ➝ ψ) := by
    intro F hF V x
    let pk : PointedKripke := {
      model := (⟨F, V⟩ : Kripke.Model)
      world := x
    }
    have hpx : pk.satisfies φ → pk.satisfies ψ := himp pk (by simpa [pk, inClass] using hF)
    exact Formula.Kripke.Satisfies.imp_def.mpr (by
      intro hx
      exact hpx hx)
  exact Complete.complete (𝓢 := 𝓢) (𝓜 := C) hvalid

/-- Implication-level proof-theoretic closure for class-indexed singleton WM consequence. -/
theorem provable_imp_iff_singletonStrengthLEOn
    {S : Type*} [Entailment S (LO.Modal.Formula ℕ)]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C] [Complete 𝓢 C]
    {φ ψ : (LO.Modal.Formula ℕ)} :
    (𝓢 ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn PointedKripke.satisfies (inClass C) φ ψ := by
  constructor
  · intro hprov
    exact singletonStrengthLEOn_of_provable_imp (S := S) (𝓢 := 𝓢) (C := C) hprov
  · intro hsing
    exact provable_imp_of_singletonStrengthLEOn (S := S) (𝓢 := 𝓢) (C := C) hsing

/-- Soundness-to-executable consequence bridge on multisets in frame class `C`. -/
theorem multiset_strength_le_of_provable_imp
    {S : Type*} [Entailment S (LO.Modal.Formula ℕ)]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    {W : Multiset PointedKripke} {φ ψ : (LO.Modal.Formula ℕ)}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W ψ := by
  have hsing : singletonStrengthLEOn PointedKripke.satisfies (inClass C) φ ψ :=
    singletonStrengthLEOn_of_provable_imp (S := S) (𝓢 := 𝓢) (C := C) hprov
  exact multiset_strength_le_of_singletonStrengthLEOn PointedKripke.satisfies (inClass C) W φ ψ hW hsing

/-! ## Concrete Foundation instantiations: K and KT -/

theorem provable_imp_iff_singletonStrengthLEOn_K
    {φ ψ : (LO.Modal.Formula ℕ)} :
    (Modal.K ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn PointedKripke.satisfies (inClass Kripke.FrameClass.K) φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.K) (C := Kripke.FrameClass.K)

theorem provable_imp_iff_singletonStrengthLEOn_KT
    {φ ψ : (LO.Modal.Formula ℕ)} :
    (Modal.KT ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn PointedKripke.satisfies (inClass Kripke.FrameClass.KT) φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.KT) (C := Kripke.FrameClass.KT)

theorem multiset_strength_le_of_provable_imp_K
    {W : Multiset PointedKripke} {φ ψ : (LO.Modal.Formula ℕ)}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ Kripke.FrameClass.K)
    (hprov : Modal.K ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.K) (C := Kripke.FrameClass.K) hW hprov

theorem multiset_strength_le_of_provable_imp_KT
    {W : Multiset PointedKripke} {φ ψ : (LO.Modal.Formula ℕ)}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ Kripke.FrameClass.KT)
    (hprov : Modal.KT ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.KT) (C := Kripke.FrameClass.KT) hW hprov

theorem provable_imp_iff_singletonStrengthLEOn_KD
    {φ ψ : (LO.Modal.Formula ℕ)} :
    (Modal.KD ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn PointedKripke.satisfies (inClass Kripke.FrameClass.KD) φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.KD) (C := Kripke.FrameClass.KD)

theorem provable_imp_iff_singletonStrengthLEOn_K4
    {φ ψ : (LO.Modal.Formula ℕ)} :
    (Modal.K4 ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn PointedKripke.satisfies (inClass Kripke.FrameClass.K4) φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.K4) (C := Kripke.FrameClass.K4)

theorem multiset_strength_le_of_provable_imp_KD
    {W : Multiset PointedKripke} {φ ψ : (LO.Modal.Formula ℕ)}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ Kripke.FrameClass.KD)
    (hprov : Modal.KD ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.KD) (C := Kripke.FrameClass.KD) hW hprov

theorem multiset_strength_le_of_provable_imp_K4
    {W : Multiset PointedKripke} {φ ψ : (LO.Modal.Formula ℕ)}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ Kripke.FrameClass.K4)
    (hprov : Modal.K4 ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.K4) (C := Kripke.FrameClass.K4) hW hprov

/-- Governance-facing corollary of the Kripke implication bridge:
provability of `□φ ➝ ◇φ` yields multiset WM strength inequality between the
obligation/permitted modal forms. -/
theorem multiset_ob_pe_strength_le_of_provable
    {S : Type*} [Entailment S (LO.Modal.Formula ℕ)]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    {W : Multiset PointedKripke} {φ : (LO.Modal.Formula ℕ)}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (□φ ➝ ◇φ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W (□φ) ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W (◇φ) := by
  exact
    multiset_strength_le_of_provable_imp
      (S := S) (𝓢 := 𝓢) (C := C) (W := W) (φ := □φ) (ψ := ◇φ) hW hprov

/-- Kripke-side T-family convenience wrapper:
`□φ ➝ φ` provability in KT yields the multiset WM inequality `□φ ⪯ φ`. -/
theorem multiset_rexist_strength_le_of_provable_KT
    {W : Multiset PointedKripke} {φ : (LO.Modal.Formula ℕ)}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ Kripke.FrameClass.KT)
    (hprov : Modal.KT ⊢ (□φ ➝ φ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W (□φ) ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W φ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.KT) (C := Kripke.FrameClass.KT)
      (W := W) (φ := □φ) (ψ := φ) hW hprov

/-- Kripke-side D-family convenience wrapper:
`□φ ➝ ◇φ` provability in KD yields the multiset WM inequality `□φ ⪯ ◇φ`. -/
theorem multiset_ob_pe_strength_le_of_provable_KD
    {W : Multiset PointedKripke} {φ : (LO.Modal.Formula ℕ)}
    (hW : ∀ pk ∈ W, pk.model.toFrame ∈ Kripke.FrameClass.KD)
    (hprov : Modal.KD ⊢ (□φ ➝ ◇φ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W (□φ) ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := (LO.Modal.Formula ℕ)) W (◇φ) := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.KD) (C := Kripke.FrameClass.KD)
      (W := W) (φ := □φ) (ψ := ◇φ) hW hprov

end Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeCompleteness
