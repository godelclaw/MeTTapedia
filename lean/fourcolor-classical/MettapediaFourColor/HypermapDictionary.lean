import FourColor.Euler
import Mettapedia.GraphTheory.Hypermap.Connectivity

/-!
An exact dictionary on a fixed finite dart type. Both hypermap presentations
retain the three permutations, their components and their planarity condition.
This does not identify labelled rotation systems with arbitrary hypermaps.
-/

namespace Mettapedia.GraphTheory.Hypermap.Reference

variable {D : Type*} [Fintype D] [DecidableEq D]

def toReference (H : Mettapedia.GraphTheory.Hypermap D) : _root_.FourColor.Hypermap D where
  edge := H.edge
  node := H.node
  face := H.face
  node_face_edge := by
    ext d
    exact H.cancel3 d

def fromReference (H : _root_.FourColor.Hypermap D) : Mettapedia.GraphTheory.Hypermap D where
  edge := H.edge
  node := H.node
  face := H.face
  cancel3 d := by
    have equal := congrArg (fun σ : Equiv.Perm D => σ d) H.node_face_edge
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using equal

@[simp] theorem from_to (H : Mettapedia.GraphTheory.Hypermap D) :
    fromReference (toReference H) = H := by
  cases H
  rfl

@[simp] theorem to_from (H : _root_.FourColor.Hypermap D) :
    toReference (fromReference H) = H := by
  cases H
  rfl

def presentationEquiv :
    Mettapedia.GraphTheory.Hypermap D ≃ _root_.FourColor.Hypermap D where
  toFun := toReference
  invFun := fromReference
  left_inv := from_to
  right_inv := to_from

@[simp] theorem edge_preserved (H : Mettapedia.GraphTheory.Hypermap D) :
    (toReference H).edge = H.edge := rfl

@[simp] theorem node_preserved (H : Mettapedia.GraphTheory.Hypermap D) :
    (toReference H).node = H.node := rfl

@[simp] theorem face_preserved (H : Mettapedia.GraphTheory.Hypermap D) :
    (toReference H).face = H.face := rfl

#print axioms presentationEquiv

open FourColor.GoertzelV24WordReachability
open FourColor.GoertzelV24PermutationOrbitSurgery

theorem step_iff (H : Mettapedia.GraphTheory.Hypermap D) (x y : D) :
    WordStep [H.edge, H.node, H.face] x y ↔ (toReference H).GLink x y := by
  simp [WordStep, _root_.FourColor.Hypermap.GLink, toReference, eq_comm]

/-- Forward generator paths and the reference's equivalence closure give the
same components; finiteness makes every permutation step reversible. -/
theorem reachable_iff (H : Mettapedia.GraphTheory.Hypermap D) (x y : D) :
    WordReachable [H.edge, H.node, H.face] x y ↔
      Relation.EqvGen (toReference H).GLink x y := by
  constructor
  · intro path
    induction path with
    | refl => exact .refl _
    | @tail b c _ step ih =>
      exact .trans _ _ _ ih (.rel _ _ ((step_iff H _ _).mp step))
  · intro path
    induction path with
    | rel a b step => exact .single ((step_iff H _ _).mpr step)
    | refl a => exact WordReachable.refl _ a
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem compCount_preserved (H : Mettapedia.GraphTheory.Hypermap D) :
    (toReference H).compCount = H.compCount := by
  unfold _root_.FourColor.Hypermap.compCount compCount wordOrbitCount
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Quotient.congr (Equiv.refl D)
    (fun x y => (reachable_iff H x y).symm))

omit [DecidableEq D] in
theorem orbitCount_eq_cycleCount (σ : Equiv.Perm D) :
    orbitCount σ = _root_.FourColor.cycleCount σ := by
  unfold orbitCount _root_.FourColor.cycleCount
  exact Nat.card_eq_fintype_card.symm

/-- The names of the Euler sides are reversed between the two APIs. -/
theorem eulerLhs_preserved (H : Mettapedia.GraphTheory.Hypermap D) :
    (toReference H).EulerLhs = H.eulerRhs := by
  rw [_root_.FourColor.Hypermap.EulerLhs, compCount_preserved,
    eulerRhs_eq_card_add_two_mul_compCount, Nat.card_eq_fintype_card]
  omega

theorem eulerRhs_preserved (H : Mettapedia.GraphTheory.Hypermap D) :
    (toReference H).EulerRhs = H.eulerLhs := by
  simp only [_root_.FourColor.Hypermap.EulerRhs, eulerLhs, edge_preserved,
    node_preserved, face_preserved, orbitCount_eq_cycleCount, Nat.add_assoc]

/-- Exact Euler arithmetic prevents the reference's natural subtraction and
division from hiding a positive or odd defect. -/
theorem planar_iff (H : Mettapedia.GraphTheory.Hypermap D) :
    (toReference H).Planar ↔ H.Planar := by
  have exactEuler := (toReference H).evenGenus
  change (toReference H).EulerLhs =
    2 * (toReference H).genus + (toReference H).EulerRhs at exactEuler
  rw [eulerLhs_preserved, eulerRhs_preserved] at exactEuler
  change (toReference H).genus = 0 ↔ (H.eulerLhs : ℤ) - H.eulerRhs = 0
  omega

#print axioms reachable_iff
#print axioms compCount_preserved
#print axioms planar_iff

end Mettapedia.GraphTheory.Hypermap.Reference
