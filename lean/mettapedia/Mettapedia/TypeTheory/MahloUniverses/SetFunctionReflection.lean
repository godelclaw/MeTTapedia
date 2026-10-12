import Mettapedia.TypeTheory.MahloUniverses.MahloCardinals

/-!
# Mahlo cardinals reflect functions on sets

For inaccessible `κ`, `κ` is Mahlo exactly when every function on sets that maps `V_κ` into
itself has a closed member of `V_κ` containing `ω` that is closed under it
(`isMahlo_iff_forall_closed_under`). The closed sets containing `ω` are the levels `V_μ` at
inaccessible `μ` (`closed_omega_mem_iff`), so this is the closure-point characterization of
Mahlo cardinals read on sets instead of ordinals. It is the form in which a Mahlo universe is
stated in higher-order Tarski–Grothendieck set theory, where closed transitive sets play the
role of inaccessible cardinals.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MahloUniverses

open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
open Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels
open Cardinal
open scoped ZFSet Ordinal

universe u

variable {κ : Cardinal.{u}}

/-- **A Mahlo cardinal reflects every function on its level.** -/
theorem IsMahlo.exists_level_closed_under (hκ : IsMahlo κ) {F : ZFSet.{u} → ZFSet.{u}}
    (hF : ∀ x ∈ V_ κ.ord, F x ∈ V_ κ.ord) :
    ∃ μ : Cardinal.{u}, μ.IsInaccessible ∧ μ < κ ∧ ∀ x ∈ V_ μ.ord, F x ∈ V_ μ.ord := by
  have inaccessible := hκ.isInaccessible
  have bound : ∀ α < κ.ord, ∃ β < κ.ord, ∀ x : {x : ZFSet.{u} // x ∈ V_ α}, (F x.1).rank < β := by
    intro α hα
    refine exists_bound_lt_ord (ι := {x : ZFSet.{u} // x ∈ V_ α}) inaccessible.isRegular ?_
      (fun x => (F x.1).rank)
      (fun x => ZFSet.mem_vonNeumann.mp
        (hF x.1 (ZFSet.mem_vonNeumann.mpr ((ZFSet.mem_vonNeumann.mp x.2).trans hα))))
    rw [ZFSet.cardinalMk_coe_sort, Cardinal.lift_lift, Cardinal.lift_lt, ZFSet.card_vonNeumann,
      ← inaccessible.preBeth_ord]
    exact Cardinal.preBeth_strictMono hα
  choose! g hgκ hg using bound
  obtain ⟨μ, hμ, hμκ, closure⟩ := hκ.exists_inaccessible_closurePoint hgκ
  refine ⟨μ, hμ, hμκ, fun x hx => ?_⟩
  have succBelow : Order.succ x.rank < μ.ord :=
    (Cardinal.isSuccLimit_ord hμ.aleph0_lt.le).succ_lt (ZFSet.mem_vonNeumann.mp hx)
  have image := hg _ (succBelow.trans (Cardinal.ord_lt_ord.mpr hμκ))
    ⟨x, ZFSet.mem_vonNeumann_succ x⟩
  exact ZFSet.mem_vonNeumann.mpr (image.trans (closure _ succBelow))

/-- Conversely, an inaccessible cardinal whose level reflects every function on sets is Mahlo:
the function `x ↦ f (rank x)`, read as a von Neumann ordinal, transfers closure to `f`. -/
theorem isMahlo_of_forall_level_closed_under (hκ : κ.IsInaccessible)
    (h : ∀ F : ZFSet.{u} → ZFSet.{u}, (∀ x ∈ V_ κ.ord, F x ∈ V_ κ.ord) →
      ∃ μ : Cardinal.{u}, μ.IsInaccessible ∧ μ < κ ∧ ∀ x ∈ V_ μ.ord, F x ∈ V_ μ.ord) :
    IsMahlo κ := by
  refine isMahlo_of_forall_closurePoint hκ fun f hf => ?_
  obtain ⟨μ, hμ, hμκ, closed⟩ := h (fun x => (f x.rank).toZFSet) (fun x hx => by
    rw [ZFSet.mem_vonNeumann, Ordinal.rank_toZFSet]
    exact hf _ (ZFSet.mem_vonNeumann.mp hx))
  refine ⟨μ, hμ, hμκ, fun α hα => ?_⟩
  have member := closed α.toZFSet
    (ZFSet.mem_vonNeumann.mpr (by rw [Ordinal.rank_toZFSet]; exact hα))
  rwa [ZFSet.mem_vonNeumann, Ordinal.rank_toZFSet, Ordinal.rank_toZFSet] at member

/-- **The closed sets containing `ω` are the levels at inaccessible cardinals.** -/
theorem closed_omega_mem_iff (W : ZFSet.{u}) :
    Closed W ∧ (ω : Ordinal.{u}).toZFSet ∈ W ↔
      ∃ μ : Cardinal.{u}, μ.IsInaccessible ∧ W = V_ μ.ord := by
  constructor
  · rintro ⟨hW, hω⟩
    rcases (closed_iff W).mp hW with rfl | rfl | ⟨μ, hμ, rfl⟩
    · exact absurd hω (ZFSet.notMem_empty _)
    · rw [ZFSet.mem_vonNeumann, Ordinal.rank_toZFSet] at hω
      exact absurd hω (lt_irrefl _)
    · exact ⟨μ, hμ, rfl⟩
  · rintro ⟨μ, hμ, rfl⟩
    refine ⟨inaccessible_closed hμ, ?_⟩
    rw [ZFSet.mem_vonNeumann, Ordinal.rank_toZFSet, ← Cardinal.ord_aleph0]
    exact Cardinal.ord_lt_ord.mpr hμ.aleph0_lt

/-- **Mahlo cardinals as reflecting universes.** For inaccessible `κ`, `κ` is Mahlo exactly when
every function on sets that maps `V_κ` into itself has a closed member of `V_κ` containing `ω`
closed under it. -/
theorem isMahlo_iff_forall_closed_under (hκ : κ.IsInaccessible) :
    IsMahlo κ ↔ ∀ F : ZFSet.{u} → ZFSet.{u}, (∀ x ∈ V_ κ.ord, F x ∈ V_ κ.ord) →
      ∃ W ∈ V_ κ.ord, Closed W ∧ (ω : Ordinal.{u}).toZFSet ∈ W ∧ ∀ x ∈ W, F x ∈ W := by
  constructor
  · intro hmahlo F hF
    obtain ⟨μ, hμ, hμκ, closed⟩ := hmahlo.exists_level_closed_under hF
    obtain ⟨hW, hω⟩ := (closed_omega_mem_iff (V_ μ.ord)).mpr ⟨μ, hμ, rfl⟩
    exact ⟨V_ μ.ord, ZFSet.vonNeumann_mem_vonNeumann_iff.mpr (Cardinal.ord_lt_ord.mpr hμκ),
      hW, hω, closed⟩
  · intro h
    refine isMahlo_of_forall_level_closed_under hκ fun F hF => ?_
    obtain ⟨W, hWκ, hW, hω, closed⟩ := h F hF
    obtain ⟨μ, hμ, rfl⟩ := (closed_omega_mem_iff W).mp ⟨hW, hω⟩
    exact ⟨μ, hμ, Cardinal.ord_lt_ord.mp (ZFSet.vonNeumann_mem_vonNeumann_iff.mp hWκ), closed⟩

/-- Negative example: at the least inaccessible cardinal, the identity function has no closed
member containing `ω`. -/
theorem IsLeastInaccessible.no_closed_member {κ : Cardinal.{u}} (hκ : IsLeastInaccessible κ) :
    ¬ ∃ W ∈ V_ κ.ord, Closed W ∧ (ω : Ordinal.{u}).toZFSet ∈ W := by
  rintro ⟨W, hWκ, hW, hω⟩
  obtain ⟨μ, hμ, rfl⟩ := (closed_omega_mem_iff W).mp ⟨hW, hω⟩
  exact (hκ.2 μ hμ).not_gt
    (Cardinal.ord_lt_ord.mp (ZFSet.vonNeumann_mem_vonNeumann_iff.mp hWκ))

#print axioms IsMahlo.exists_level_closed_under
#print axioms isMahlo_of_forall_level_closed_under
#print axioms closed_omega_mem_iff
#print axioms isMahlo_iff_forall_closed_under
#print axioms IsLeastInaccessible.no_closed_member

end Mettapedia.TypeTheory.MahloUniverses
