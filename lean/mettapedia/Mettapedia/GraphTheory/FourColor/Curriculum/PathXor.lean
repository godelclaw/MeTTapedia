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
