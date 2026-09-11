import Mettapedia.GraphTheory.FourColor.SerialTangleFaceCode

/-!
# Joint colour and structural semantics for physical serial tangles

One extraction and one transfer track colour support, the cyclic face
return, realized small cuts, and Euler mass on the same sewn object.
The face and cut operations use boundary data only. Euler mass is an
integer: this theorem alone asserts neither a finite range for all
inputs nor global bounded-width coverage or descent.
-/

namespace Mettapedia.GraphTheory.FourColor.SerialTangleJointTransfer

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24CompositeSeamMultigraph OpenTangleReplacementEuler
open SerialTangleSmallCutTransfer SerialTangleFaceTransfer
open GoertzelV24RetainedSpliceFaceCount

noncomputable section
attribute [local instance] Classical.propDecidable

@[ext] structure Signature (L R : Type*) where
  colours : Set ((L → Color) × (R → Color))
  face : Equiv.Perm (L ⊕ R)
  cuts : Set (BoundarySmallCutProfile.State (L ⊕ R))
  mass : ℤ

variable {V W I J L P R : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]
  [Fintype R] [DecidableEq R]

def encode (T : TwoSidedOpenTangleData V I L R) : Signature L R where
  colours := {xy | T.AcceptsBoundaryWords xy.1 xy.2}
  face := SerialTangleFaceCode.encode T
  cuts := BoundarySmallCutProfile.profile (sideMultigraph (asOpen T)) (asOpen T).boundaryVert
  mass := eulerMass (asOpen T)

def transfer (a : Signature L P) (b : Signature P R) : Signature L R where
  colours := {xy | ∃ middle, (xy.1, middle) ∈ a.colours ∧ (middle, xy.2) ∈ b.colours}
  face := SerialTangleFaceCode.transfer a.face b.face
  cuts := BoundarySmallCutTransfer.composeProfile a.cuts b.cuts
  mass := a.mass + b.mass - 2 * Fintype.card P +
    2 * ((Equiv.Perm.partition (Equiv.sumCongr a.face b.face *
      SerialTangleFaceCode.codeSwap)).parts.card : ℤ) -
    2 * ((Equiv.Perm.partition (Equiv.sumCongr a.face b.face)).parts.card : ℤ)

omit [DecidableEq V] [DecidableEq W] in
/-- All four coordinates commute with the very same literal constructor.
There is no assumed existence or validity of a replacement in this statement. -/
theorem encode_serial (A : TwoSidedOpenTangleData V I L P)
    (B : TwoSidedOpenTangleData W J P R) :
    encode (A.serialCompose B (Equiv.refl P)) = transfer (encode A) (encode B) := by
  apply Signature.ext
  · ext xy
    exact serialCompose_acceptsBoundaryWords_iff A B (Equiv.refl P) xy.1 xy.2
  · exact SerialTangleFaceCode.encode_serial A B
  · exact profile_serial A B
  · have h := serial_eulerMass A B
    have hin := card_permCongr_partition_parts
      (SerialTangleFaceCode.combinedCoordinate (I := I) (J := J)) (combinedReturn A B)
    have hout := card_permCongr_partition_parts
      (SerialTangleFaceCode.combinedCoordinate (I := I) (J := J))
      (combinedReturn A B * boundarySwap)
    rw [SerialTangleFaceCode.combined_code] at hin
    rw [SerialTangleFaceCode.rewired_code] at hout
    dsimp only [encode, transfer]
    omega

end
end Mettapedia.GraphTheory.FourColor.SerialTangleJointTransfer
