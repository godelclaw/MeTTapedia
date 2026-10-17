import Mettapedia.OSLF.NativeTypes.SortProfiles.SiteInterfaces

/-!
# Forgetting index coordinates of a generated site

The index/rely/target interface and the older rely/output interface have a
computable comparison on their sort assignments. Forgetting index coordinates
is surjective. Its fibre consists of exactly the discarded index assignments,
so it is faithful precisely when the generated site has no index variables.

This compares coordinates only. It does not identify the formation judgments,
output carriers, or equation-admission policies of the two constructions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Projection

open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef)
open Mettapedia.OSLF.NativeTypes.Generation.Occurrences (Site)

/-- Keep the index coordinates distinct from the retained rely/target block. -/
abbrev Full (indices retained : Nat) := (Fin indices ⊕ Fin retained) → HSort

def forget {indices retained : Nat} (profile : Full indices retained) :
    Fin retained → HSort := fun position => profile (.inr position)

def extend {indices retained : Nat} (index : Fin indices → HSort)
    (profile : Fin retained → HSort) : Full indices retained := Sum.elim index profile

@[simp] theorem forget_extend {indices retained : Nat} (index : Fin indices → HSort)
    (profile : Fin retained → HSort) : forget (extend index profile) = profile := rfl

theorem forget_surjective (indices retained : Nat) :
    Function.Surjective (@forget indices retained) := by
  intro profile
  exact ⟨extend (fun _ => .star) profile, forget_extend _ _⟩

/-- Every completion of a reduced profile retains exactly its index choices. -/
def fibreEquiv (indices retained : Nat) (profile : Fin retained → HSort) :
    {full : Full indices retained // forget full = profile} ≃ (Fin indices → HSort) where
  toFun full := fun position => full.val (.inl position)
  invFun index := ⟨extend index profile, forget_extend index profile⟩
  left_inv := by
    intro full
    apply Subtype.ext
    funext position
    cases position with
    | inl index => rfl
    | inr retained => exact (congrFun full.property retained).symm
  right_inv := by intro index; rfl

theorem fibre_card (indices retained : Nat) (profile : Fin retained → HSort) :
    Fintype.card {full : Full indices retained // forget full = profile} = 2 ^ indices := by
  rw [Fintype.card_congr (fibreEquiv indices retained profile), Fintype.card_fun,
    HSort.card, Fintype.card_fin]

theorem forget_injective_iff (indices retained : Nat) :
    Function.Injective (@forget indices retained) ↔ indices = 0 := by
  constructor
  · intro injective
    by_contra nonzero
    have positive : 0 < indices := Nat.pos_of_ne_zero nonzero
    let position : Fin indices := ⟨0, positive⟩
    have equal := injective (forget_extend (fun _ => HSort.star) (fun _ => HSort.star) |>.trans
      (forget_extend (fun _ => HSort.box) (fun _ => HSort.star)).symm)
    have different : HSort.star = HSort.box := congrFun equal (.inl position)
    cases different
  · rintro rfl first second equal
    funext position
    cases position with
    | inl index => exact Fin.elim0 index
    | inr retained => exact congrFun equal retained

/-- This coordinate count is derived from the authored site's variable split. -/
abbrev SiteFull (language : LanguageDef) (site : Site) :=
  Full (SiteInterfaces.indexNames site).length (Slots.modalFamily language site).slotCount

theorem site_full_card (language : LanguageDef) (site : Site) :
    Fintype.card (SiteFull language site) = 2 ^ SiteInterfaces.slotCount site := by
  rw [SiteInterfaces.slotCount_eq_family language site]
  simp only [SiteFull, Full, Fintype.card_fun, HSort.card, Fintype.card_sum,
    Fintype.card_fin]

theorem site_forget_injective_iff (language : LanguageDef) (site : Site) :
    Function.Injective (@forget (SiteInterfaces.indexNames site).length
      (Slots.modalFamily language site).slotCount) ↔ SiteInterfaces.indexNames site = [] := by
  rw [forget_injective_iff, List.length_eq_zero_iff]

end Mettapedia.OSLF.NativeTypes.SortProfiles.Projection
