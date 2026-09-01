import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mettapedia.GraphTheory.FiniteDegree
import Mettapedia.GraphTheory.FourColor.RotationSystem

namespace Mettapedia.GraphTheory.FourColor

namespace SimpleGraphDartRotation

variable {V : Type*}
variable (G : SimpleGraph V)

/-- Flip a graph dart to the opposite orientation of the same unoriented edge. -/
def dartFlip : Equiv.Perm G.Dart where
  toFun := SimpleGraph.Dart.symm
  invFun := SimpleGraph.Dart.symm
  left_inv := SimpleGraph.Dart.symm_symm
  right_inv := SimpleGraph.Dart.symm_symm

@[simp]
theorem dartFlip_apply (d : G.Dart) :
    dartFlip G d = d.symm :=
  rfl

/-- The remaining non-face data needed to turn `SimpleGraph.Dart` into the bare
`RotationSystem` carrier: a cyclic order of outgoing darts at each vertex and a
chosen outer dart.  Facial-cycle data should eventually construct this package,
then prove the stronger `RotationSystem.PlanarGeometry` fields. -/
structure Data where
  vertexRotation : Equiv.Perm G.Dart
  vertexRotation_fst : ∀ d : G.Dart, (vertexRotation d).fst = d.fst
  outer : G.Dart

namespace Data

variable (data : Data G)

/-- The vertex rotation is a single cycle on the outgoing darts at every
vertex.  This is the graph-backed, representation-independent formulation of
cyclic vertex rotations. -/
def IsVertexwiseCyclic : Prop :=
  ∀ vertex,
    data.vertexRotation.IsCycleOn
      {dart : G.Dart | dart.fst = vertex}

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Three distinct outgoing darts at a degree-three vertex exhaust its dart
fiber.  Hence a cyclic vertex rotation sends the first dart to one of the
other two. -/
theorem vertexRotation_apply_eq_second_or_third_of_regularThree
    [G.LocallyFinite]
    (hregular : G.IsRegularOfDegree 3)
    (hcyclic : data.IsVertexwiseCyclic)
    {first second third : G.Dart}
    (hsecondBase : second.fst = first.fst)
    (hthirdBase : third.fst = first.fst)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    data.vertexRotation first = second ∨
      data.vertexRotation first = third := by
  let fiber : Finset G.Dart :=
    Finset.univ.filter fun dart => dart.fst = first.fst
  have hfirstMem : first ∈ fiber := by
    simp [fiber]
  have hsecondMem : second ∈ fiber := by
    simp [fiber, hsecondBase]
  have hthirdMem : third ∈ fiber := by
    simp [fiber, hthirdBase]
  have htripleSubset : ({first, second, third} : Finset G.Dart) ⊆ fiber := by
    intro dart hdart
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdart
    rcases hdart with rfl | rfl | rfl
    · exact hfirstMem
    · exact hsecondMem
    · exact hthirdMem
  have htripleCard : ({first, second, third} : Finset G.Dart).card = 3 := by
    simp [hfirstSecond, hfirstThird, hsecondThird]
  have hfiberCard : fiber.card = 3 := by
    change ({dart : G.Dart | dart.fst = first.fst} : Finset G.Dart).card = 3
    rw [G.dart_fst_fiber_card_eq_degree]
    exact (SimpleGraph.degree_instance_independent first.fst _ _).symm.trans
      (hregular.degree_eq first.fst)
  have htripleEq : ({first, second, third} : Finset G.Dart) = fiber := by
    apply Finset.eq_of_subset_of_card_le htripleSubset
    rw [htripleCard, hfiberCard]
  have hrotationMem : data.vertexRotation first ∈ fiber := by
    simp [fiber, data.vertexRotation_fst]
  rw [← htripleEq] at hrotationMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrotationMem
  rcases hrotationMem with hfixed | hsecond | hthird
  · have hfiberNontrivial : fiber.Nontrivial := by
      apply Finset.one_lt_card_iff_nontrivial.mp
      rw [hfiberCard]
      omega
    have hsetNontrivial : (fiber : Set G.Dart).Nontrivial := by
      simpa only [Finset.coe_sort_coe] using hfiberNontrivial
    exact False.elim
      ((hcyclic first.fst).apply_ne (by simpa [fiber] using hsetNontrivial)
        (by simp) hfixed)
  · exact Or.inl hsecond
  · exact Or.inr hthird

/-- Once the first step of a cyclic three-dart vertex fiber is fixed, the
remaining two rotation steps are forced. -/
theorem vertexRotation_three_cycle_of_eq_second
    [G.LocallyFinite]
    (hregular : G.IsRegularOfDegree 3)
    (hcyclic : data.IsVertexwiseCyclic)
    {first second third : G.Dart}
    (hsecondBase : second.fst = first.fst)
    (hthirdBase : third.fst = first.fst)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hfirst : data.vertexRotation first = second) :
    data.vertexRotation second = third ∧
      data.vertexRotation third = first := by
  have hnext := vertexRotation_apply_eq_second_or_third_of_regularThree
    (G := G) data hregular hcyclic
    (first := second) (second := third) (third := first)
    (hthirdBase.trans hsecondBase.symm) hsecondBase.symm
    hsecondThird hfirstSecond.symm hfirstThird.symm
  rcases hnext with hsecond | hback
  · let fiber : Finset G.Dart :=
      Finset.univ.filter fun dart => dart.fst = first.fst
    have hfirstMem : first ∈ fiber := by simp [fiber]
    have hfiberCard : fiber.card = 3 := by
      change ({dart : G.Dart | dart.fst = first.fst} : Finset G.Dart).card = 3
      rw [G.dart_fst_fiber_card_eq_degree]
      exact (SimpleGraph.degree_instance_independent first.fst _ _).symm.trans
        (hregular.degree_eq first.fst)
    have hcycle : data.vertexRotation.IsCycleOn (fiber : Set G.Dart) := by
      simpa [fiber] using hcyclic first.fst
    have hcube := hcycle.pow_card_apply hfirstMem
    rw [hfiberCard] at hcube
    have hthird : data.vertexRotation third = first := by
      simpa [pow_succ, hfirst, hsecond] using hcube
    exact ⟨hsecond, hthird⟩
  · let fiber : Finset G.Dart :=
      Finset.univ.filter fun dart => dart.fst = first.fst
    have hfirstMem : first ∈ fiber := by simp [fiber]
    have hfiberCard : fiber.card = 3 := by
      change ({dart : G.Dart | dart.fst = first.fst} : Finset G.Dart).card = 3
      rw [G.dart_fst_fiber_card_eq_degree]
      exact (SimpleGraph.degree_instance_independent first.fst _ _).symm.trans
        (hregular.degree_eq first.fst)
    have hcycle : data.vertexRotation.IsCycleOn (fiber : Set G.Dart) := by
      simpa [fiber] using hcyclic first.fst
    have hcube := hcycle.pow_card_apply hfirstMem
    rw [hfiberCard] at hcube
    have hsecondFirst : second = first := by
      simpa [pow_succ, hfirst, hback] using hcube
    exact False.elim (hfirstSecond hsecondFirst.symm)

/-- A finite simple graph, equipped with a vertex rotation on darts and an outer
dart, determines the bare rotation-system structure.  This construction proves
the edge-flip and two-darts-per-edge obligations from Mathlib's `SimpleGraph`
dart API; it does not assert planarity. -/
noncomputable def toRotationSystem : RotationSystem V G.edgeSet where
  D := G.Dart
  edgeOf := fun d => ⟨d.edge, d.edge_mem⟩
  vertOf := fun d => d.fst
  alpha := dartFlip G
  rho := data.vertexRotation
  alpha_involutive := by
    intro d
    simp [dartFlip]
  alpha_fixfree := by
    intro d
    simpa [dartFlip] using SimpleGraph.Dart.symm_ne d
  edge_alpha := by
    intro d
    apply Subtype.ext
    simp [dartFlip]
  edge_fiber_two := by
    intro e
    have hfilter :
        (Finset.univ.filter
            (fun d : G.Dart => (⟨d.edge, d.edge_mem⟩ : G.edgeSet) = e)) =
          Finset.univ.filter (fun d : G.Dart => d.edge = e.1) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [hfilter]
    simpa using SimpleGraph.dart_edge_fiber_card (G := G) e.1 e.2
  vert_rho := data.vertexRotation_fst
  outer := data.outer
  no_self_loops := by
    intro d
    simp [dartFlip, SimpleGraph.Dart.fst_ne_snd d]

@[simp]
theorem toRotationSystem_edgeOf (d : G.Dart) :
    data.toRotationSystem.edgeOf d = ⟨d.edge, d.edge_mem⟩ :=
  rfl

@[simp]
theorem toRotationSystem_vertOf (d : G.Dart) :
    data.toRotationSystem.vertOf d = d.fst :=
  rfl

@[simp]
theorem toRotationSystem_alpha (d : G.Dart) :
    data.toRotationSystem.alpha d = d.symm :=
  rfl

@[simp]
theorem toRotationSystem_rho (d : G.Dart) :
    data.toRotationSystem.rho d = data.vertexRotation d :=
  rfl

/-- For a rotation system constructed from a finite simple graph, the
three-darts-per-vertex predicate is exactly graph-theoretic 3-regularity. -/
theorem toRotationSystem_isCubic_iff :
    data.toRotationSystem.IsCubic ↔ G.IsRegularOfDegree 3 := by
  unfold RotationSystem.IsCubic SimpleGraph.IsRegularOfDegree
  change (∀ v : V, ({d : G.Dart | d.fst = v} : Finset _).card = 3) ↔
    ∀ v : V, G.degree v = 3
  constructor
  · intro h v
    rw [← G.dart_fst_fiber_card_eq_degree v]
    exact h v
  · intro h v
    rw [G.dart_fst_fiber_card_eq_degree v]
    exact h v

end Data

/-- A global face-successor package on `SimpleGraph.Dart`.  In a rotation
system, the face permutation is `rho * alpha`; conversely, a global permutation
that sends each dart to a dart starting at its terminal vertex determines the
vertex rotation by composing with the edge flip.  Face-local successor-cycle
data should prove this stronger global package before claiming a full
rotation-system realization. -/
structure FaceSuccessorData where
  faceSuccessor : Equiv.Perm G.Dart
  faceSuccessor_fst : ∀ d : G.Dart, (faceSuccessor d).fst = d.snd
  outer : G.Dart

namespace FaceSuccessorData

variable (data : FaceSuccessorData G)

/-- Convert a global face successor into the vertex-rotation data needed by
`SimpleGraphDartRotation.Data`. -/
def toData : Data G where
  vertexRotation := data.faceSuccessor * dartFlip G
  vertexRotation_fst := by
    intro d
    change (data.faceSuccessor d.symm).fst = d.fst
    simpa using data.faceSuccessor_fst d.symm
  outer := data.outer

@[simp]
theorem toData_vertexRotation (d : G.Dart) :
    data.toData.vertexRotation d = data.faceSuccessor d.symm :=
  rfl

@[simp]
theorem toData_outer : data.toData.outer = data.outer :=
  rfl

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The rotation system determined by a global face successor. -/
noncomputable def toRotationSystem : RotationSystem V G.edgeSet :=
  data.toData.toRotationSystem

@[simp]
theorem toRotationSystem_alpha (d : G.Dart) :
    data.toRotationSystem.alpha d = d.symm :=
  rfl

@[simp]
theorem toRotationSystem_rho (d : G.Dart) :
    data.toRotationSystem.rho d = data.faceSuccessor d.symm :=
  rfl

@[simp]
theorem toRotationSystem_phi (d : G.Dart) :
    data.toRotationSystem.phi d = data.faceSuccessor d := by
  simp [RotationSystem.phi]

end FaceSuccessorData

/-- A proof-friendly way to construct global face-successor data: give the
successor as an explicit function, give an explicit inverse/predecessor, and
prove the two inverse laws.  Concrete finite examples can usually prove these
laws by case analysis, then lower to `FaceSuccessorData` without hand-building
an `Equiv.Perm`. -/
structure FaceSuccessorFunctionData where
  faceSuccessor : G.Dart → G.Dart
  facePredecessor : G.Dart → G.Dart
  left_inv : Function.LeftInverse facePredecessor faceSuccessor
  right_inv : Function.RightInverse facePredecessor faceSuccessor
  faceSuccessor_fst : ∀ d : G.Dart, (faceSuccessor d).fst = d.snd
  outer : G.Dart

namespace FaceSuccessorFunctionData

variable (data : FaceSuccessorFunctionData G)

/-- Promote explicit successor/predecessor functions to a permutation. -/
def faceSuccessorPerm : Equiv.Perm G.Dart where
  toFun := data.faceSuccessor
  invFun := data.facePredecessor
  left_inv := data.left_inv
  right_inv := data.right_inv

@[simp]
theorem faceSuccessorPerm_apply (d : G.Dart) :
    (faceSuccessorPerm (G := G) data) d = data.faceSuccessor d :=
  rfl

@[simp]
theorem faceSuccessorPerm_symm_apply (d : G.Dart) :
    (faceSuccessorPerm (G := G) data).symm d = data.facePredecessor d :=
  rfl

/-- Lower explicit successor/predecessor data to the global face-successor
package. -/
def toFaceSuccessorData : FaceSuccessorData G where
  faceSuccessor := faceSuccessorPerm (G := G) data
  faceSuccessor_fst := data.faceSuccessor_fst
  outer := data.outer

@[simp]
theorem toFaceSuccessorData_faceSuccessor (d : G.Dart) :
    data.toFaceSuccessorData.faceSuccessor d = data.faceSuccessor d :=
  rfl

@[simp]
theorem toFaceSuccessorData_outer :
    data.toFaceSuccessorData.outer = data.outer :=
  rfl

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The bare rotation system determined by explicit global face-successor and
predecessor functions. -/
noncomputable def toRotationSystem : RotationSystem V G.edgeSet :=
  data.toFaceSuccessorData.toRotationSystem

@[simp]
theorem toRotationSystem_phi (d : G.Dart) :
    data.toRotationSystem.phi d = data.faceSuccessor d := by
  exact FaceSuccessorData.toRotationSystem_phi (G := G) data.toFaceSuccessorData d

end FaceSuccessorFunctionData

end SimpleGraphDartRotation

end Mettapedia.GraphTheory.FourColor
