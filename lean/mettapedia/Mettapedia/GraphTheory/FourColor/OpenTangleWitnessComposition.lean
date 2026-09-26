import Mettapedia.GSLT.Core.LooseRelationEquipment
import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialOpenTangleCountSupport
import Mathlib.Data.Fintype.Pi

/-!
# Literal colourings as proof-relevant compositional relations

The support theorem for serial gluing is strengthened to an equivalence of
colouring fibres. It retains the common boundary word and both actual dart
colourings. Thus the same gluing operation has witness, support and counting
interpretations. A map of the middle colouring fibres extends through an
arbitrary serial exterior context.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleWitnessComposition

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open Mettapedia.GSLT.LooseRelationEquipment

noncomputable section

universe u
variable {V W I J L R S : Type u}

/-- The relation retains the actual colouring, not only its existence. -/
def colourRelation (piece : TwoSidedOpenTangleData V I L R) :
    Loose (L → Color) (R → Color) :=
  fun x y => {color : piece.Coloring // piece.IsTaitColoring color ∧
    piece.leftBoundaryColor color = x ∧ piece.rightBoundaryColor color = y}

instance [Finite I] [Finite L] [Finite R]
    (piece : TwoSidedOpenTangleData V I L R) (x : L → Color) (y : R → Color) :
    Finite (colourRelation piece x y) := by
  unfold colourRelation
  infer_instance

theorem nonempty_colourRelation_iff (piece : TwoSidedOpenTangleData V I L R)
    (x : L → Color) (y : R → Color) :
    Nonempty (colourRelation piece x y) ↔ piece.AcceptsBoundaryWords x y := by
  constructor
  · rintro ⟨⟨color, proof⟩⟩
    exact ⟨color, proof⟩
  · rintro ⟨color, proof⟩
    exact ⟨⟨color, proof⟩⟩

variable (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J R S)

def splitWitness (x : L → Color) (z : S → Color)
    (witness : colourRelation (serialCompose left right (Equiv.refl R)) x z) :
    comp (colourRelation left) (colourRelation right) x z := by
  let lc := leftRestriction left right (Equiv.refl R) witness.val
  let rc := rightRestriction left right (Equiv.refl R) witness.val
  refine ⟨left.rightBoundaryColor lc,
    ⟨lc, leftRestriction_isTait left right _ _ witness.property.1, ?_, rfl⟩,
    ⟨rc, rightRestriction_isTait left right _ _ witness.property.1, ?_, ?_⟩⟩
  · exact witness.property.2.1
  · funext port
    exact (restrictions_seamColorAgreement left right (Equiv.refl R)
      witness.val witness.property.1 port).symm
  · exact witness.property.2.2

def glueWitness (x : L → Color) (z : S → Color)
    (witness : comp (colourRelation left) (colourRelation right) x z) :
    colourRelation (serialCompose left right (Equiv.refl R)) x z := by
  refine ⟨serialColor left right witness.2.1.val witness.2.2.val,
    serialColor_isTait left right (Equiv.refl R) _ _
      witness.2.1.property.1 witness.2.2.property.1 ?_, ?_, ?_⟩
  · intro port
    exact (congrFun witness.2.1.property.2.2 port).trans
      (congrFun witness.2.2.property.2.1 port).symm
  · exact witness.2.1.property.2.1
  · exact witness.2.2.property.2.2

theorem leftRestriction_serialColor (lc : left.Coloring) (rc : right.Coloring) :
    leftRestriction left right (Equiv.refl R) (serialColor left right lc rc) = lc := by
  funext dart
  simp only [leftRestriction, serialColor, Equiv.symm_apply_apply, serialSourceColor]

theorem rightRestriction_serialColor (lc : left.Coloring) (rc : right.Coloring) :
    rightRestriction left right (Equiv.refl R) (serialColor left right lc rc) = rc := by
  funext dart
  simp only [rightRestriction, serialColor, Equiv.symm_apply_apply, serialSourceColor]

/-- Literal gluing is precisely composition of colouring relations, with
both directions and both inverse laws proved on actual dart functions. -/
def serialEquiv (x : L → Color) (z : S → Color) :
    colourRelation (serialCompose left right (Equiv.refl R)) x z ≃
      comp (colourRelation left) (colourRelation right) x z where
  toFun := splitWitness left right x z
  invFun := glueWitness left right x z
  left_inv witness := by
    rcases witness with ⟨color, hc, hx, hz⟩
    apply Subtype.ext
    funext dart
    rcases dart with ((i | j) | (r | m)) | (l | s) <;> rfl
  right_inv witness := by
    rcases witness with ⟨middle, ⟨lc, hlc, hx, hm⟩, ⟨rc, hrc, hm', hz⟩⟩
    cases hm
    simp only [splitWitness, glueWitness, leftRestriction_serialColor,
      rightRestriction_serialColor]
    rfl

/-- Counting the actual composite fibre counts compatible pairs exactly. -/
theorem card_serial (x : L → Color) (z : S → Color) :
    Nat.card (colourRelation (serialCompose left right (Equiv.refl R)) x z) =
      Nat.card (comp (colourRelation left) (colourRelation right) x z) :=
  Nat.card_congr (serialEquiv left right x z)

/-- Finite colouring counts obey ordinary matrix multiplication. Vertex
carriers need not be finite: finiteness of the dart carriers is sufficient. -/
theorem count_serial [Finite I] [Finite J] [Finite L] [Fintype R] [DecidableEq R] [Finite S]
    (x : L → Color) (z : S → Color) :
    Nat.card (colourRelation (serialCompose left right (Equiv.refl R)) x z) =
      ∑ middle : R → Color,
        Nat.card (colourRelation left x middle) * Nat.card (colourRelation right middle z) := by
  rw [card_serial]
  unfold comp
  rw [Nat.card_sigma]
  exact Finset.sum_congr rfl (fun middle _ => Nat.card_prod _ _)

variable {A B K P Q T : Type u}

/-- A witness-preserving replacement of the middle tangle preserves the
literal colouring witnesses of every fixed serial exterior. -/
def replaceInContext
    (initial : TwoSidedOpenTangleData A K P L)
    {original : TwoSidedOpenTangleData V I L R}
    {replacement : TwoSidedOpenTangleData B T L R}
    (transport : Cell id id (colourRelation original) (colourRelation replacement))
    (final : TwoSidedOpenTangleData W J R Q) :
    Cell id id
      (colourRelation (serialCompose
        (serialCompose initial original (Equiv.refl L)) final (Equiv.refl R)))
      (colourRelation (serialCompose
        (serialCompose initial replacement (Equiv.refl L)) final (Equiv.refl R))) where
  map := fun {x z} witness => by
    let outer := serialEquiv (serialCompose initial original (Equiv.refl L)) final x z witness
    let inner := serialEquiv initial original x outer.1 outer.2.1
    let changed := transport.map inner.2.2
    let joined := (serialEquiv initial replacement x outer.1).symm
      ⟨inner.1, inner.2.1, changed⟩
    exact (serialEquiv (serialCompose initial replacement (Equiv.refl L)) final x z).symm
      ⟨outer.1, joined, outer.2.2⟩

end
end Mettapedia.GraphTheory.FourColor.OpenTangleWitnessComposition
