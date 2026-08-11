import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialOpenTangleCountSupport

/-!
# Support pumping for serial open tangles

The corridor-pumping step uses an identity-like open piece: inserting that
piece between two existing factors must preserve a positive `Count` entry.
Boundary carriers arising from two geometric cuts are generally distinct
types, even when both cuts have the same source order.  The statement below
therefore records all three boundary transports explicitly and never
identifies carriers merely because they have the same cardinality.

This is the support-level form of the source's L2 premise.  It proves the
insertion consequence; it does not assert that every relevant geometric
profile has such an identity-like realization.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenTangleComposition

noncomputable section

namespace TwoSidedOpenTangleData

variable {V W X I L R J M N K P S : Type*}

/-- Identity support restricted to the profiles relevant to the surrounding
counterexample species.  This is the source-faithful L2 shape: irrelevant
boundary words need not admit a stay transition. -/
def SupportsTransportedIdentityOn
    (loop : TwoSidedOpenTangleData W J M N)
    (leftToLoop : R ≃ M) (loopToRight : N ≃ P)
    (skip : R ≃ P) (Relevant : (R → Color) → Prop) : Prop :=
  ∀ word : R → Color,
    Relevant word →
      loop.AcceptsBoundaryWords
        (fun input => word (leftToLoop.symm input))
        (fun output => word (skip.symm (loopToRight output)))

/-- An open tangle acts like the identity between two externally chosen
coordinate systems when it accepts every word transported from the skipped
seam on both of its boundaries. -/
def SupportsTransportedIdentity
    (loop : TwoSidedOpenTangleData W J M N)
    (leftToLoop : R ≃ M) (loopToRight : N ≃ P)
    (skip : R ≃ P) : Prop :=
  ∀ word : R → Color,
    loop.AcceptsBoundaryWords
      (fun input => word (leftToLoop.symm input))
      (fun output => word (skip.symm (loopToRight output)))

/-- Inserting an identity-like piece on relevant seam words preserves an
accepted exterior pair.  Relevance is established from the two factors of
the shortened coloring, rather than assumed for arbitrary words. -/
theorem serialCompose_acceptsBoundaryWords_of_transportedIdentityOn
    (left : TwoSidedOpenTangleData V I L R)
    (loop : TwoSidedOpenTangleData W J M N)
    (right : TwoSidedOpenTangleData X K P S)
    (leftToLoop : R ≃ M) (loopToRight : N ≃ P)
    (skip : R ≃ P) (Relevant : (R → Color) → Prop)
    (hloop : loop.SupportsTransportedIdentityOn
      leftToLoop loopToRight skip Relevant)
    (leftWord : L → Color) (rightWord : S → Color)
    (hrelevant : ∀ middle : R → Color,
      left.AcceptsBoundaryWords leftWord middle →
      right.AcceptsBoundaryWords
        (fun input => middle (skip.symm input)) rightWord →
      Relevant middle)
    (hshort : (serialCompose left right skip).AcceptsBoundaryWords
      leftWord rightWord) :
    (serialCompose (serialCompose left loop leftToLoop) right loopToRight)
        |>.AcceptsBoundaryWords leftWord rightWord := by
  rw [serialCompose_acceptsBoundaryWords_iff] at hshort
  rcases hshort with ⟨middle, hleft, hright⟩
  rw [serialCompose_acceptsBoundaryWords_iff]
  let afterLoop : N → Color :=
    fun output => middle (skip.symm (loopToRight output))
  refine ⟨afterLoop, ?_, ?_⟩
  · rw [serialCompose_acceptsBoundaryWords_iff]
    exact ⟨middle, hleft, hloop middle (hrelevant middle hleft hright)⟩
  · simpa [afterLoop] using hright

/-- Inserting a transported identity-like open piece preserves every
accepted exterior boundary pair.  This is the literal support-pumping law:
the short composite supplies the seam word, the middle piece realizes that
same word in its own coordinates, and the two applications of serial `Count`
composition perform the gluing. -/
theorem serialCompose_acceptsBoundaryWords_of_transportedIdentity
    (left : TwoSidedOpenTangleData V I L R)
    (loop : TwoSidedOpenTangleData W J M N)
    (right : TwoSidedOpenTangleData X K P S)
    (leftToLoop : R ≃ M) (loopToRight : N ≃ P)
    (skip : R ≃ P)
    (hloop : loop.SupportsTransportedIdentity leftToLoop loopToRight skip)
    (leftWord : L → Color) (rightWord : S → Color)
    (hshort : (serialCompose left right skip).AcceptsBoundaryWords
      leftWord rightWord) :
    (serialCompose (serialCompose left loop leftToLoop) right loopToRight)
        |>.AcceptsBoundaryWords leftWord rightWord := by
  apply serialCompose_acceptsBoundaryWords_of_transportedIdentityOn
    left loop right leftToLoop loopToRight skip (fun _ => True)
  · intro word _
    exact hloop word
  · intro _ _ _
    trivial
  · exact hshort

/-- Same-carrier specialization of identity support. -/
def SupportsIdentity
    (loop : TwoSidedOpenTangleData W J R R) : Prop :=
  ∀ word : R → Color, loop.AcceptsBoundaryWords word word

/-- Familiar same-coordinate form of support pumping. -/
theorem serialCompose_acceptsBoundaryWords_of_identity
    (left : TwoSidedOpenTangleData V I L R)
    (loop : TwoSidedOpenTangleData W J R R)
    (right : TwoSidedOpenTangleData X K R S)
    (hloop : loop.SupportsIdentity)
    (leftWord : L → Color) (rightWord : S → Color)
    (hshort : (serialCompose left right (Equiv.refl R)).AcceptsBoundaryWords
      leftWord rightWord) :
    (serialCompose (serialCompose left loop (Equiv.refl R)) right
        (Equiv.refl R)).AcceptsBoundaryWords leftWord rightWord := by
  apply serialCompose_acceptsBoundaryWords_of_transportedIdentity
    left loop right (Equiv.refl R) (Equiv.refl R) (Equiv.refl R)
  · intro word
    simpa using hloop word
  · exact hshort

end TwoSidedOpenTangleData

end

end GoertzelV24OpenTangleComposition

end Mettapedia.GraphTheory.FourColor
