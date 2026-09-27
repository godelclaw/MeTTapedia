import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedMapEulerBound

/-!
# Edge presentations adapted to invariant subsets

Restricting an involution to an invariant subset retains precisely its
two-cycles there and fixes the complement. Presentations of the two parts
concatenate to a presentation of the original involution, with exactly
the same number of edges. This permits planar edge deletion in a chosen
geometric order without changing the underlying darts.
-/

namespace Mettapedia.GraphTheory.FourColor.InvolutionRestrictionEdgeList

open Equiv Equiv.Perm
open GoertzelV24MapEulerBound GoertzelV24InvolutionEdgeList
open GoertzelV24ConnectedMapEulerBound

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable section

attribute [local instance] Classical.propDecidable

def restrict (a : Perm D) (ha : Function.Involutive a) (keep : D → Prop)
    (hk : ∀ d, keep (a d) ↔ keep d) : Perm D := by
  classical
  let f := fun d => if keep d then a d else d
  have hf : Function.Involutive f := by
    intro d
    by_cases h : keep d
    · simp [f, h, (hk d).mpr h, ha d]
    · simp [f, h]
  exact ⟨f, f, hf, hf⟩

omit [Fintype D] [DecidableEq D] in
theorem restrict_apply (a : Perm D) (ha : Function.Involutive a)
    (keep : D → Prop) (hk : ∀ d, keep (a d) ↔ keep d) (d : D) :
    restrict a ha keep hk d = if keep d then a d else d := by
  classical
  rfl

omit [Fintype D] [DecidableEq D] in
theorem restrict_involutive (a : Perm D) (ha : Function.Involutive a)
    (keep : D → Prop) (hk : ∀ d, keep (a d) ↔ keep d) :
    Function.Involutive (restrict a ha keep hk) := by
  intro d
  exact (restrict a ha keep hk).left_inv d

theorem mem_moved_restrict (a : Perm D) (ha : Function.Involutive a)
    (keep : D → Prop) (hk : ∀ d, keep (a d) ↔ keep d) (d : D) :
    d ∈ movedFinset (restrict a ha keep hk) ↔ keep d ∧ d ∈ movedFinset a := by
  classical
  simp only [mem_movedFinset, restrict_apply]
  split_ifs <;> simp_all

omit [Fintype D] [DecidableEq D] in
theorem restrict_compl_mul (a : Perm D) (ha : Function.Involutive a)
    (keep : D → Prop) (hk : ∀ d, keep (a d) ↔ keep d) :
    restrict a ha (fun d => ¬ keep d) (fun d => not_congr (hk d)) *
      restrict a ha keep hk = a := by
  classical
  ext d
  simp only [Perm.mul_apply, restrict_apply]
  by_cases h : keep d
  · simp [h, (hk d).mpr h]
  · simp [h]

theorem length_restrict_add_compl (a : Perm D) (ha : Function.Involutive a)
    (keep : D → Prop) (hk : ∀ d, keep (a d) ↔ keep d) :
    (edgeList (restrict a ha (fun d => ¬ keep d) (fun d => not_congr (hk d)))).length +
      (edgeList (restrict a ha keep hk)).length = (edgeList a).length := by
  classical
  let p := restrict a ha keep hk
  let q := restrict a ha (fun d => ¬ keep d) (fun d => not_congr (hk d))
  have hp := two_mul_length_edgeList_eq_card_movedFinset p
    (restrict_involutive a ha keep hk)
  have hq := two_mul_length_edgeList_eq_card_movedFinset q
    (restrict_involutive a ha _ _)
  have h := two_mul_length_edgeList_eq_card_movedFinset a ha
  have hd : Disjoint (movedFinset q) (movedFinset p) := by
    apply Finset.disjoint_left.mpr
    intro d hq hp
    exact (mem_moved_restrict a ha _ _ d).mp hq |>.1
      ((mem_moved_restrict a ha _ _ d).mp hp).1
  have hu : movedFinset q ∪ movedFinset p = movedFinset a := by
    ext d
    simp only [Finset.mem_union, mem_moved_restrict, p, q]
    tauto
  have hc := Finset.card_union_of_disjoint hd
  rw [hu] at hc
  change (edgeList q).length + (edgeList p).length = (edgeList a).length
  omega

omit [Fintype D] in
theorem swapProduct_append (first second : List (D × D)) :
    swapProduct (first ++ second) = swapProduct first * swapProduct second := by
  induction first with
  | nil => simp [swapProduct_nil]
  | cons e rest ih => simp only [List.cons_append, swapProduct_cons, ih, mul_assoc]

end
end Mettapedia.GraphTheory.FourColor.InvolutionRestrictionEdgeList
