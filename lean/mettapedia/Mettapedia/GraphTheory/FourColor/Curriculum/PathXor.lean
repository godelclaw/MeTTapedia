import Mettapedia.GraphTheory.FourColor.ColorAlgebra

namespace Mettapedia.GraphTheory.FourColor.Curriculum

/-- A lightweight edge path used for finite XOR-sum algebra. -/
abbrev EdgePath (E : Type*) := List E

/-- The `𝔽₂` sum of edge weights along a finite edge path. -/
def pathXor {E : Type*} (weight : E → F2) (path : EdgePath E) : F2 :=
  (path.map weight).sum

@[simp] theorem pathXor_nil {E : Type*} (weight : E → F2) :
    pathXor weight [] = 0 :=
  rfl

@[simp] theorem pathXor_singleton {E : Type*} (weight : E → F2) (e : E) :
    pathXor weight [e] = weight e := by
  simp [pathXor]

theorem pathXor_singleton_ne_zero {E : Type*} (weight : E → F2) {e : E}
    (hweight : weight e = 1) :
    pathXor weight [e] ≠ 0 := by
  rw [pathXor_singleton, hweight]
  decide

theorem pathXor_singleton_ne_zero_iff {E : Type*} (weight : E → F2) {e : E} :
    pathXor weight [e] ≠ 0 ↔ weight e ≠ 0 := by
  rw [pathXor_singleton]

theorem exists_mem_weight_ne_zero_singleton_iff {E : Type*} (weight : E → F2) {e : E} :
    (∃ x, x ∈ ([e] : EdgePath E) ∧ weight x ≠ 0) ↔ weight e ≠ 0 := by
  simp

theorem pathXor_eq_zero_of_forall_mem_eq_zero {E : Type*} (weight : E → F2)
    {path : EdgePath E} (hzero : ∀ e, e ∈ path → weight e = 0) :
    pathXor weight path = 0 := by
  induction path with
  | nil =>
      rfl
  | cons e path ih =>
      have he : weight e = 0 := hzero e (by simp)
      have htail : pathXor weight path = 0 := by
        exact ih (fun e heMem => hzero e (by simp [heMem]))
      rw [pathXor]
      simp [he]
      simpa [pathXor] using htail

theorem exists_mem_weight_ne_zero_of_pathXor_ne_zero {E : Type*} (weight : E → F2)
    {path : EdgePath E} (hxor : pathXor weight path ≠ 0) :
    ∃ e, e ∈ path ∧ weight e ≠ 0 := by
  by_contra hnone
  have hzero : ∀ e, e ∈ path → weight e = 0 := by
    intro e heMem
    by_contra hweight
    exact hnone ⟨e, heMem, hweight⟩
  exact hxor (pathXor_eq_zero_of_forall_mem_eq_zero weight hzero)

theorem pathXor_append {E : Type*} (weight : E → F2) (p q : EdgePath E) :
    pathXor weight (p ++ q) = pathXor weight p + pathXor weight q := by
  simp [pathXor, List.map_append, List.sum_append]

theorem pathXor_edge_then_back {E : Type*} (weight : E → F2) (e : E) :
    pathXor weight [e, e] = 0 := by
  simp [pathXor, zmod2_add_self]

theorem pathXor_append_reverse {E : Type*} (weight : E → F2) (p : EdgePath E) :
    pathXor weight (p ++ p.reverse) = 0 := by
  rw [pathXor_append]
  unfold pathXor
  rw [List.map_reverse, List.sum_reverse]
  exact zmod2_add_self _

end Mettapedia.GraphTheory.FourColor.Curriculum
