import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# Transporting graph-backed rotations across graph isomorphisms

Several source-opening comparisons in this development first identify two
simple graphs.  A graph isomorphism is enough to transport the complete
graph-backed rotation datum as well: it carries oriented darts, conjugates the
vertex and face permutations, and transports the chosen outer dart.  This is
carrier plumbing only.  It makes no planarity, Euler, or assertion identifying
the source annulus's named hole faces.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SimpleGraphRotationIsoTransport

open SimpleGraph
open SimpleGraphDartRotation

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W}

noncomputable section

/-- The oriented-dart equivalence induced by a simple-graph isomorphism. -/
def dartEquiv (iso : G ≃g H) : G.Dart ≃ H.Dart where
  toFun := fun dart => ⟨(iso dart.toProd.1, iso dart.toProd.2),
    (iso.map_rel_iff).mpr dart.adj⟩
  invFun := fun dart => ⟨(iso.symm dart.toProd.1, iso.symm dart.toProd.2),
    (iso.symm.map_rel_iff).mpr dart.adj⟩
  left_inv := by
    intro dart
    cases dart
    simp
  right_inv := by
    intro dart
    cases dart
    simp

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem dartEquiv_fst (iso : G ≃g H) (dart : G.Dart) :
    (dartEquiv iso dart).toProd.1 = iso dart.toProd.1 :=
  rfl

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem dartEquiv_symm_fst (iso : G ≃g H) (dart : H.Dart) :
    ((dartEquiv iso).symm dart).toProd.1 = iso.symm dart.toProd.1 :=
  rfl

/-- The dart equivalence commutes with reversal of an oriented edge. -/
@[simp] theorem dartEquiv_alpha
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (iso : G ≃g H) (dart : G.Dart) :
    dartEquiv iso dart.symm = (dartEquiv iso dart).symm := by
  apply SimpleGraph.Dart.ext
  rfl

/-- Transport a graph-backed vertex rotation and its distinguished outer dart
across a graph isomorphism.  The transport identifies the carrier and its face
permutation, but supplies no identification of the source's intended hole
faces. -/
def transportData (iso : G ≃g H) (data : Data G) : Data H where
  vertexRotation := (dartEquiv iso).permCongr data.vertexRotation
  vertexRotation_fst := by
    intro dart
    simp only [Equiv.permCongr_apply, dartEquiv_fst, dartEquiv_symm_fst,
      data.vertexRotation_fst]
    exact iso.apply_symm_apply dart.toProd.1
  outer := dartEquiv iso data.outer

/-- Transporting graph-backed rotation data conjugates the complete face
permutation.  This is the carrier-level part of face transport; selecting and
ordering the source annulus's hole faces remains a separate geometric task. -/
theorem transportData_phi_eq_permCongr
    [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (iso : G ≃g H) (data : Data G) :
    (transportData iso data).toRotationSystem.phi =
      (dartEquiv iso).permCongr data.toRotationSystem.phi := by
  apply Equiv.ext
  intro dart
  simp only [RotationSystem.phi]
  change dartEquiv iso
      (data.vertexRotation
        ((dartEquiv iso).symm dart).symm) =
    dartEquiv iso
      (data.vertexRotation
        ((dartEquiv iso).symm dart).symm)
  rfl

/-- One face step in transported data is the image of the corresponding old
face step.  This is the convenient form for transporting a fully retained
face orbit through a graph-presentation comparison. -/
theorem transportData_phi_apply
    [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (iso : G ≃g H) (data : Data G) (dart : G.Dart) :
    (transportData iso data).toRotationSystem.phi (dartEquiv iso dart) =
      dartEquiv iso (data.toRotationSystem.phi dart) := by
  change (transportData iso data).vertexRotation
      ((dartEquiv iso dart).symm) =
    dartEquiv iso (data.vertexRotation dart.symm)
  rw [← dartEquiv_alpha]
  change ((dartEquiv iso).permCongr data.vertexRotation)
      (dartEquiv iso dart.symm) = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]

end

end GoertzelV24SimpleGraphRotationIsoTransport

end Mettapedia.GraphTheory.FourColor
