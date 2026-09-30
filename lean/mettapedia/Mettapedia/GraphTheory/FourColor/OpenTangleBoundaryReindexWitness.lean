import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleBoundaryReindex
import Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphismColoring

/-! # Whole colouring witnesses under boundary-coordinate changes

The existing boundary-reindex constructor is an exact open-tangle isomorphism.
Its generic witness transport therefore preserves every edge assignment,
boundary observation and inverse reconstruction, across arbitrary carriers.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphism

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData

variable {V I B C : Type*}

noncomputable def boundaryReindex (T : OpenTangleData V I B) (order : C ≃ B) :
    Iso (T.reindexBoundary order) T where
  vertex := Equiv.refl _
  interior := Equiv.refl _
  boundary := order
  alpha _ := rfl
  vert d := by cases d <;> rfl
  rotation d := by
    change boundaryReindexDartEquiv order
      ((boundaryReindexDartEquiv order).symm
        (T.rho (boundaryReindexDartEquiv order d))) = _
    exact (boundaryReindexDartEquiv order).apply_symm_apply _

end Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphism
