import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# Transporting graph-backed rotations across graph isomorphisms

Several source-opening comparisons in this development first identify two
simple graphs.  A graph isomorphism is enough to transport the complete
graph-backed rotation datum as well: it carries oriented darts, conjugates the
vertex rotation, and transports the chosen outer dart.  This is carrier
plumbing only.  It makes no planarity, Euler, or face-order assertion.
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

/-- Transport a graph-backed vertex rotation and its distinguished outer dart
across a graph isomorphism.  The transport deliberately stops before face
orbits: an arbitrary graph isomorphism alone supplies no identification of
the source's intended hole faces. -/
def transportData (iso : G ≃g H) (data : Data G) : Data H where
  vertexRotation := (dartEquiv iso).permCongr data.vertexRotation
  vertexRotation_fst := by
    intro dart
    simp only [Equiv.permCongr_apply, dartEquiv_fst, dartEquiv_symm_fst,
      data.vertexRotation_fst]
    exact iso.apply_symm_apply dart.toProd.1
  outer := dartEquiv iso data.outer

end

end GoertzelV24SimpleGraphRotationIsoTransport

end Mettapedia.GraphTheory.FourColor
