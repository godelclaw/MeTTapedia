import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhood
import Foundation.Modal.Neighborhood.Logic.E
import Foundation.Modal.Neighborhood.Logic.EMN
import Foundation.Modal.Neighborhood.Logic.EMT
import Foundation.Modal.Neighborhood.Logic.ED

/-!
# Neighborhood WM Proof-Theoretic Closure (Implication Fragment)

This module connects class-indexed neighborhood proof theory (`Sound`/`Complete`)
to WM singleton/multiset consequence inequalities for implication queries.
-/

namespace Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhoodCompleteness

open LO
open LO.Modal
open Formula.Neighborhood
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhood
open Mettapedia.PLN.WorldModel.PLNWorldModelCrispSpecialization
open scoped ENNReal

/-- A pointed neighborhood model is admissible for a frame class when its frame
is in the class. -/
def inClass (C : Neighborhood.FrameClass) (pn : PointedNeighborhood) : Prop :=
  pn.model.toFrame ∈ C

/-! ## Soundness/completeness bridge from Foundation neighborhood logic -/

/-- Soundness lift: provable implication gives class-indexed singleton WM consequence. -/
theorem singletonStrengthLEOn_of_provable_imp
    {S : Type*} [Entailment S (LO.Modal.Formula ℕ)]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    {φ ψ : (LO.Modal.Formula ℕ)}
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    singletonStrengthLEOn PointedNeighborhood.satisfies (inClass C) φ ψ := by
  have himp : pointwiseImpliesOn PointedNeighborhood.satisfies (inClass C) φ ψ := by
    intro pn hC hφ
    have hvalid : C ⊧ (φ ➝ ψ) := Sound.sound (𝓢 := 𝓢) (𝓜 := C) hprov
    have hframe : pn.model.toFrame ⊧ (φ ➝ ψ) := hvalid hC
    have hmodel : pn.model ⊧ (φ ➝ ψ) := hframe pn.model.Val
    have hworld : Formula.Neighborhood.Satisfies pn.model pn.world (φ ➝ ψ) := hmodel pn.world
    exact (Formula.Neighborhood.Satisfies.def_imp.mp hworld) hφ
  exact (pointwiseImpliesOn_iff_singletonStrengthLEOn PointedNeighborhood.satisfies (inClass C) φ ψ).mp himp

/-- Completeness lift: class-indexed singleton WM consequence yields provable implication. -/
theorem provable_imp_of_singletonStrengthLEOn
    {S : Type*} [Entailment S (LO.Modal.Formula ℕ)]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Complete 𝓢 C]
    {φ ψ : (LO.Modal.Formula ℕ)}
    (hsing : singletonStrengthLEOn PointedNeighborhood.satisfies (inClass C) φ ψ) :
    𝓢 ⊢ (φ ➝ ψ) := by
  have himp : pointwiseImpliesOn PointedNeighborhood.satisfies (inClass C) φ ψ :=
    (pointwiseImpliesOn_iff_singletonStrengthLEOn PointedNeighborhood.satisfies (inClass C) φ ψ).mpr hsing
  have hvalid : C ⊧ (φ ➝ ψ) := by
    intro F hF V x
    let pn : PointedNeighborhood := {
      model := (⟨F, V⟩ : Neighborhood.Model)
      world := x
    }
    have hpx : pn.satisfies φ → pn.satisfies ψ := himp pn (by simpa [pn, inClass] using hF)
    exact Formula.Neighborhood.Satisfies.def_imp.mpr (fun hx => hpx hx)
  exact Complete.complete (𝓢 := 𝓢) (𝓜 := C) hvalid

/-- Implication-level proof-theoretic closure for class-indexed singleton WM consequence. -/
theorem provable_imp_iff_singletonStrengthLEOn
    {S : Type*} [Entailment S (LO.Modal.Formula ℕ)]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C] [Complete 𝓢 C]
    {φ ψ : (LO.Modal.Formula ℕ)} :
    (𝓢 ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn PointedNeighborhood.satisfies (inClass C) φ ψ := by
  constructor
  · intro hprov
    exact singletonStrengthLEOn_of_provable_imp (S := S) (𝓢 := 𝓢) (C := C) hprov
  · intro hsing
    exact provable_imp_of_singletonStrengthLEOn (S := S) (𝓢 := 𝓢) (C := C) hsing

/-- Soundness-to-executable consequence bridge on multisets in frame class `C`. -/
theorem multiset_strength_le_of_provable_imp
    {S : Type*} [Entailment S (LO.Modal.Formula ℕ)]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    {W : Multiset PointedNeighborhood} {φ ψ : (LO.Modal.Formula ℕ)}
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := (LO.Modal.Formula ℕ)) W φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := (LO.Modal.Formula ℕ)) W ψ := by
  have hsing : singletonStrengthLEOn PointedNeighborhood.satisfies (inClass C) φ ψ :=
    singletonStrengthLEOn_of_provable_imp (S := S) (𝓢 := 𝓢) (C := C) hprov
  exact multiset_strength_le_of_singletonStrengthLEOn PointedNeighborhood.satisfies (inClass C) W φ ψ hW hsing

/-! ## Concrete Foundation instantiations: E and EMN -/

theorem provable_imp_iff_singletonStrengthLEOn_E
    {φ ψ : (LO.Modal.Formula ℕ)} :
    (Modal.E ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn PointedNeighborhood.satisfies (inClass Neighborhood.FrameClass.E) φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.E) (C := Neighborhood.FrameClass.E)

theorem provable_imp_iff_singletonStrengthLEOn_EMN
    {φ ψ : (LO.Modal.Formula ℕ)} :
    (Modal.EMN ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn PointedNeighborhood.satisfies (inClass Neighborhood.FrameClass.EMN) φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.EMN) (C := Neighborhood.FrameClass.EMN)

theorem multiset_strength_le_of_provable_imp_E
    {W : Multiset PointedNeighborhood} {φ ψ : (LO.Modal.Formula ℕ)}
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ Neighborhood.FrameClass.E)
    (hprov : Modal.E ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := (LO.Modal.Formula ℕ)) W φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := (LO.Modal.Formula ℕ)) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.E) (C := Neighborhood.FrameClass.E) hW hprov

theorem multiset_strength_le_of_provable_imp_EMN
    {W : Multiset PointedNeighborhood} {φ ψ : (LO.Modal.Formula ℕ)}
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ Neighborhood.FrameClass.EMN)
    (hprov : Modal.EMN ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := (LO.Modal.Formula ℕ)) W φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := (LO.Modal.Formula ℕ)) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.EMN) (C := Neighborhood.FrameClass.EMN) hW hprov

theorem provable_imp_iff_singletonStrengthLEOn_EMT
    [Complete Modal.EMT Neighborhood.FrameClass.EMT]
    {φ ψ : (LO.Modal.Formula ℕ)} :
    (Modal.EMT ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn PointedNeighborhood.satisfies (inClass Neighborhood.FrameClass.EMT) φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.EMT) (C := Neighborhood.FrameClass.EMT)

theorem provable_imp_iff_singletonStrengthLEOn_ED
    [Complete Modal.ED Neighborhood.FrameClass.ED]
    {φ ψ : (LO.Modal.Formula ℕ)} :
    (Modal.ED ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOn PointedNeighborhood.satisfies (inClass Neighborhood.FrameClass.ED) φ ψ := by
  exact
    provable_imp_iff_singletonStrengthLEOn
      (S := Logic ℕ) (𝓢 := Modal.ED) (C := Neighborhood.FrameClass.ED)

theorem multiset_strength_le_of_provable_imp_EMT
    {W : Multiset PointedNeighborhood} {φ ψ : (LO.Modal.Formula ℕ)}
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ Neighborhood.FrameClass.EMT)
    (hprov : Modal.EMT ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := (LO.Modal.Formula ℕ)) W φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := (LO.Modal.Formula ℕ)) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.EMT) (C := Neighborhood.FrameClass.EMT) hW hprov

theorem multiset_strength_le_of_provable_imp_ED
    {W : Multiset PointedNeighborhood} {φ ψ : (LO.Modal.Formula ℕ)}
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ Neighborhood.FrameClass.ED)
    (hprov : Modal.ED ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := (LO.Modal.Formula ℕ)) W φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := (LO.Modal.Formula ℕ)) W ψ := by
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.ED) (C := Neighborhood.FrameClass.ED) hW hprov

end Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhoodCompleteness
