import Mettapedia.Combinatorics.PolymerGas.Measure
import Mathlib.Tactic

/-!
# Regrouping activities by their support

A product of sums over fibres is a sum over sets choosing one element in each
fibre. This permits polymer activities with the same support to be added.
-/

set_option autoImplicit false
noncomputable section

open Finset
open scoped Classical

namespace Mettapedia.Combinatorics.PolymerGas

variable {α β R : Type*} [DecidableEq α] [DecidableEq β] [CommSemiring R]

/-- Expanding fibre sums amounts to choosing an injective section over the
set of labels. -/
theorem prod_fiberSums (A : Finset α) (f : α → β) (w : α → R) (Γ : Finset β) :
    (∏ b ∈ Γ, ∑ a ∈ A.filter (fun a => f a = b), w a) =
      ∑ I ∈ A.powerset.filter (fun I : Finset α => Set.InjOn f (I : Set α) ∧ I.image f = Γ),
        ∏ a ∈ I, w a := by
  classical
  rw [← Finset.prod_attach Γ]
  change (∏ b : Γ, ∑ a ∈ A.filter (fun a => f a = b.1), w a) = _
  rw [Finset.prod_univ_sum]
  let choices := Fintype.piFinset (fun b : Γ => A.filter (fun a => f a = b.1))
  have hc_spec : ∀ c ∈ choices, ∀ b : Γ, c b ∈ A ∧ f (c b) = b.1 := by
    intro c hc b
    exact mem_filter.mp ((Fintype.mem_piFinset.mp hc) b)
  have hc_inj : ∀ c ∈ choices, Function.Injective c := by
    intro c hc b d h
    apply Subtype.ext
    exact ((hc_spec c hc b).2.symm.trans (congrArg f h)).trans (hc_spec c hc d).2
  apply Finset.sum_bij (fun c _ => univ.image c)
  · intro c hc
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha
      exact (hc_spec c hc b).1
    · intro a ha a' ha' heq
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha
      obtain ⟨d, _, rfl⟩ := mem_image.mp ha'
      have : b = d := Subtype.ext
        (((hc_spec c hc b).2.symm.trans heq).trans (hc_spec c hc d).2)
      exact congrArg c this
    · ext b
      simp only [mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨a, ⟨d, rfl⟩, rfl⟩
        exact (hc_spec c hc d).2.symm ▸ d.2
      · intro hb
        exact ⟨c ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, (hc_spec c hc _).2⟩
  · intro c hc d hd heq
    funext b
    have : c b ∈ univ.image d := heq ▸ mem_image.mpr ⟨b, mem_univ _, rfl⟩
    obtain ⟨b', _, hbc⟩ := mem_image.mp this
    have hbb' : b' = b := Subtype.ext
      (((hc_spec d hd b').2.symm.trans (congrArg f hbc)).trans (hc_spec c hc b).2)
    simpa only [hbb'] using hbc.symm
  · intro I hI
    obtain ⟨hIA, hinj, himage⟩ := mem_filter.mp hI
    have hex : ∀ b : Γ, ∃ a ∈ I, f a = b.1 := by
      intro b
      exact mem_image.mp (himage.symm ▸ b.2)
    choose c hcI hcf using hex
    have hc : c ∈ choices := Fintype.mem_piFinset.mpr fun b =>
      mem_filter.mpr ⟨(mem_powerset.mp hIA) (hcI b), hcf b⟩
    refine ⟨c, hc, ?_⟩
    ext a
    constructor
    · intro ha
      obtain ⟨b, _, rfl⟩ := mem_image.mp ha
      exact hcI b
    · intro ha
      have hb : f a ∈ Γ := himage ▸ mem_image.mpr ⟨a, ha, rfl⟩
      exact mem_image.mpr ⟨⟨f a, hb⟩, mem_univ _, hinj (hcI _) ha (hcf _)⟩
  · intro c hc
    exact (prod_image (hc_inj c hc).injOn).symm

/-- Regroup a sum of fibre choices while imposing a condition on their labels. -/
theorem sum_prod_fiberSums [Fintype β] (A : Finset α) (f : α → β) (w : α → R)
    (P : Finset β → Prop) :
    (∑ Γ : Finset β, if P Γ then
      ∏ b ∈ Γ, ∑ a ∈ A.filter (fun a => f a = b), w a else 0) =
    ∑ I ∈ A.powerset, if Set.InjOn f (I : Set α) ∧ P (I.image f) then
      ∏ a ∈ I, w a else 0 := by
  classical
  calc
    _ = ∑ Γ : Finset β, ∑ I ∈ A.powerset,
        if I.image f = Γ then
          if Set.InjOn f (I : Set α) ∧ P Γ then ∏ a ∈ I, w a else 0
        else 0 := by
      apply sum_congr rfl
      intro Γ _
      rw [prod_fiberSums, sum_filter]
      by_cases hP : P Γ
      · simp only [hP, ↓reduceIte]
        apply sum_congr rfl
        intro I _
        split_ifs <;> simp_all
      · simp [hP]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro I _
      rw [sum_eq_single (I.image f)]
      · simp
      · intro Γ _ hΓ
        simp [Ne.symm hΓ]
      · simp

#print axioms prod_fiberSums
#print axioms sum_prod_fiberSums

end Mettapedia.Combinatorics.PolymerGas
