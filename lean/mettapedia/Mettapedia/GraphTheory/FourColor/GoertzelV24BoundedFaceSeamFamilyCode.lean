import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedSupportGraphCode

/-!
# Finite families of bounded face-seam graphs

An occurrence-sensitive boundary profile has a finite, exact number of real
face fragments.  This module packages one bounded support-graph code for each
such fragment while retaining that exact count; no padding coordinate is
identified with a genuine fragment.

The type is a representation interface only.  It does not identify a
particular geometric seam or assert that a profile determines its seam code.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedSupportGraphCode

/-- A bounded family of local face-seam graphs, indexed by exactly the real
boundary fragments. -/
structure BoundedFaceSeamFamilyCode (faceFragmentBound supportBound : Nat) where
  faceFragmentCount : Fin (faceFragmentBound + 1)
  seamCode : Fin faceFragmentCount.val → BoundedSupportGraphCode supportBound

noncomputable instance (faceFragmentBound supportBound : Nat) :
    DecidableEq (BoundedFaceSeamFamilyCode faceFragmentBound supportBound) :=
  Classical.decEq _

private def boundedFaceSeamFamilyCodeEquiv
    (faceFragmentBound supportBound : Nat) :
    BoundedFaceSeamFamilyCode faceFragmentBound supportBound ≃
      Σ faceFragmentCount : Fin (faceFragmentBound + 1),
        Fin faceFragmentCount.val → BoundedSupportGraphCode supportBound where
  toFun code := ⟨code.faceFragmentCount, code.seamCode⟩
  invFun code := ⟨code.1, code.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (faceFragmentBound supportBound : Nat) :
    Fintype (BoundedFaceSeamFamilyCode faceFragmentBound supportBound) :=
  Fintype.ofEquiv _
    (boundedFaceSeamFamilyCodeEquiv faceFragmentBound supportBound).symm

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
