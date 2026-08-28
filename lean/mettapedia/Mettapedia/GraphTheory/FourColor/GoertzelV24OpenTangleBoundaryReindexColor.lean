import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleBoundaryReindex
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideReassembly

/-!
# Boundary coordinates do not change a physical composite's Tait problem

The normalized receipt puts every seam on a standard finite carrier.  This
module proves that changing only the displayed coordinates on the left open
tangle produces an exactly dart-isomorphic closed composite.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenTangleBoundaryReindexColor

open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24VertexSideReassembly

noncomputable section

universe u

variable {V W I J L S R : Type u}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype S] [DecidableEq S]
  [Fintype R] [DecidableEq R]

/-- Propositionally equal seam matchings present the same Tait problem.
This small transport lemma is needed because the matching participates in the
dependent edge carrier of the composite rotation system. -/
theorem rotationSystemTaitColorable_compose_iff_of_matching_eq
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching matching' : L ≃ R) (hmatching : matching = matching') :
    RotationSystemTaitColorable
        (left.composeRotationSystem right matching) ↔
      RotationSystemTaitColorable
        (left.composeRotationSystem right matching') := by
  subst matching'
  rfl

/-- The same left piece after replacing its boundary carrier `L` by `S`. -/
abbrev reindexedLeftCompositeRS
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (coordinate : L ≃ S) :=
  (left.reindexBoundary coordinate.symm).composeRotationSystem right
    (coordinate.symm.trans matching)

/-- Undo the displayed coordinate change on the left seam summand. -/
def reindexedLeftCompositeDartEquiv
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (coordinate : L ≃ S) :
    (reindexedLeftCompositeRS left right matching coordinate).D ≃
      (left.composeRotationSystem right matching).D :=
  Equiv.sumCongr (Equiv.refl (I ⊕ J))
    (Equiv.sumCongr coordinate.symm (Equiv.refl R))

theorem reindexedLeftCompositeDartEquiv_alpha
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (coordinate : L ≃ S)
    (dart : (reindexedLeftCompositeRS left right matching coordinate).D) :
    reindexedLeftCompositeDartEquiv left right matching coordinate
        ((reindexedLeftCompositeRS left right matching coordinate).alpha dart) =
      (left.composeRotationSystem right matching).alpha
        (reindexedLeftCompositeDartEquiv left right matching coordinate dart) := by
  rcases dart with (leftInterior | rightInterior) | (leftPort | rightPort)
  · rfl
  · rfl
  · rfl
  · change
      Sum.inr (Sum.inl
        (coordinate.symm (coordinate (matching.symm rightPort)))) =
      Sum.inr (Sum.inl (matching.symm rightPort))
    simp

theorem reindexedLeftCompositeDartEquiv_vertOf
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (coordinate : L ≃ S)
    (dart : (reindexedLeftCompositeRS left right matching coordinate).D) :
    (Equiv.refl (V ⊕ W))
        ((reindexedLeftCompositeRS left right matching coordinate).vertOf dart) =
      (left.composeRotationSystem right matching).vertOf
        (reindexedLeftCompositeDartEquiv left right matching coordinate dart) := by
  rcases dart with (leftInterior | rightInterior) | (leftPort | rightPort) <;> rfl

/-- Reindexing the left boundary and transporting the seam matching preserves
Tait colorability of the literal sewn rotation system. -/
theorem rotationSystemTaitColorable_reindexedLeftComposite_iff
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (coordinate : L ≃ S) :
    RotationSystemTaitColorable
        (reindexedLeftCompositeRS left right matching coordinate) ↔
      RotationSystemTaitColorable
        (left.composeRotationSystem right matching) :=
  rotationSystemTaitColorable_iff_of_dartEquiv
    (reindexedLeftCompositeRS left right matching coordinate)
    (left.composeRotationSystem right matching)
    (reindexedLeftCompositeDartEquiv left right matching coordinate)
    (Equiv.refl (V ⊕ W))
    (reindexedLeftCompositeDartEquiv_alpha left right matching coordinate)
    (reindexedLeftCompositeDartEquiv_vertOf left right matching coordinate)

end


end GoertzelV24OpenTangleBoundaryReindexColor

end Mettapedia.GraphTheory.FourColor
