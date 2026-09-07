import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic

/-!
# Parity boundaries of finite sets of original edges

Incidence is kept as an arbitrary relation, so different original edges
with the same endpoints are not identified. Symmetric difference adds
boundaries over the field with two elements.
-/

namespace Mettapedia.GraphTheory.FourColor.FiniteEdgeParity

open scoped BigOperators symmDiff

variable {E F : Type*}

noncomputable section

def mark (f v : F) : ZMod 2 := by
  classical
  exact if f = v then 1 else 0

def boundary (inc : E → F → Prop) (edges : Finset E) (v : F) : ZMod 2 := by
  classical
  exact ∑ e ∈ edges, if inc e v then 1 else 0

theorem boundary_eq_card (inc : E → F → Prop) (edges : Finset E) (v : F)
    [DecidablePred (fun e => inc e v)] :
    boundary inc edges v = ((edges.filter fun e => inc e v).card : ZMod 2) := by
  classical
  induction edges using Finset.induction_on with
  | empty => simp [boundary]
  | @insert e s he ih =>
    by_cases hi : inc e v
    · simpa [boundary, he, hi, Finset.filter_insert, add_comm] using
        congrArg (fun z : ZMod 2 => 1 + z) ih
    · simpa [boundary, he, hi, Finset.filter_insert] using ih

theorem boundary_eq_zero_iff_even (inc : E → F → Prop) (edges : Finset E) (v : F)
    [DecidablePred (fun e => inc e v)] :
    boundary inc edges v = 0 ↔ Even (edges.filter fun e => inc e v).card := by
  rw [boundary_eq_card]
  exact ZMod.natCast_eq_zero_iff_even

@[simp] theorem boundary_empty (inc : E → F → Prop) (v : F) : boundary inc ∅ v = 0 := by
  simp [boundary]

@[simp] theorem boundary_singleton (inc : E → F → Prop) (e : E) (v : F) :
    boundary inc {e} v = (by classical exact if inc e v then 1 else 0) := by
  classical
  simp [boundary]

theorem boundary_insert [DecidableEq E] (inc : E → F → Prop) (edges : Finset E)
    (e : E) (hne : e ∉ edges) (v : F) :
    boundary inc (insert e edges) v = boundary inc {e} v + boundary inc edges v := by
  classical
  simp [boundary, hne]

theorem boundary_symmDiff [DecidableEq E] (inc : E → F → Prop)
    (s t : Finset E) (v : F) :
    boundary inc (s ∆ t) v = boundary inc s v + boundary inc t v := by
  classical
  have heq : s ∆ t = (s ∪ t) \ (s ∩ t) := by
    ext e
    simp only [Finset.mem_symmDiff, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    tauto
  let w : E → ZMod 2 := fun e => if inc e v then 1 else 0
  have hs := Finset.sum_sdiff (f := w)
    (show s ∩ t ⊆ s ∪ t from Finset.inter_subset_left.trans Finset.subset_union_left)
  rw [heq]
  change (∑ e ∈ (s ∪ t) \ (s ∩ t), w e) = (∑ e ∈ s, w e) + ∑ e ∈ t, w e
  calc
    _ = ((∑ e ∈ (s ∪ t) \ (s ∩ t), w e) + ∑ e ∈ s ∩ t, w e) +
        ∑ e ∈ s ∩ t, w e := (CharTwo.add_cancel_right _ _).symm
    _ = (∑ e ∈ s ∪ t, w e) + ∑ e ∈ s ∩ t, w e := by rw [hs]
    _ = _ := Finset.sum_union_inter

/-- Distinct endpoints contribute one at each endpoint, including with parallel edges. -/
theorem boundary_singleton_eq_marks (inc : E → F → Prop) (e : E)
    (f g : F) (hne : f ≠ g) (hinc : ∀ v, inc e v ↔ f = v ∨ g = v) (v : F) :
    boundary inc {e} v = mark f v + mark g v := by
  classical
  by_cases hf : f = v <;> by_cases hg : g = v
  · exact (hne (hf.trans hg.symm)).elim
  all_goals simp [boundary, mark, hinc, hf, hg]

end
end Mettapedia.GraphTheory.FourColor.FiniteEdgeParity
