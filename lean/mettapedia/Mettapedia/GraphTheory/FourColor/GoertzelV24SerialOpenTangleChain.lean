import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorTransferWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialOpenTangleCountSupport

/-!
# Heterogeneous chains of serial open tangles

Successive source Cells need not have the same vertex or interior-dart
carrier.  They do, however, expose interfaces with one common source
coordinate type.  This file hides the changing internal carriers while
retaining explicit equivalences from the common coordinates to both literal
boundary carriers.

Serial composition then extends from two pieces to an arbitrary nonempty
heterogeneous chain.  Its boundary-word support is exactly the
`ExactTransferWord` relation of the individual literal supports.  This is the
support-level matrix-product law; no ambient-region realization or profile
factorization is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenTangleComposition

open GoertzelV24CorridorTransferWord

noncomputable section

universe u v

/-- A two-sided open tangle whose changing internal carriers are hidden and
whose two boundary carriers are explicitly indexed by one common source
coordinate type. -/
structure CoordinatizedTwoSidedOpenTangle (B : Type u) where
  V : Type (max u v)
  I : Type (max u v)
  L : Type u
  R : Type u
  data : TwoSidedOpenTangleData V I L R
  leftCoordinate : B ≃ L
  rightCoordinate : B ≃ R

namespace CoordinatizedTwoSidedOpenTangle

variable {B : Type u}

/-- Read a word in common source coordinates on the literal left boundary. -/
def leftBoundaryWord
    (data : CoordinatizedTwoSidedOpenTangle.{u, v} B)
    (word : B → Color) : data.L → Color :=
  fun dart => word (data.leftCoordinate.symm dart)

/-- Read a word in common source coordinates on the literal right boundary. -/
def rightBoundaryWord
    (data : CoordinatizedTwoSidedOpenTangle.{u, v} B)
    (word : B → Color) : data.R → Color :=
  fun dart => word (data.rightCoordinate.symm dart)

/-- Support of one literal tangle, expressed entirely in the common source
coordinates. -/
def AcceptsBoundaryWords
    (data : CoordinatizedTwoSidedOpenTangle.{u, v} B)
    (leftWord rightWord : B → Color) : Prop :=
  data.data.AcceptsBoundaryWords
    (data.leftBoundaryWord leftWord) (data.rightBoundaryWord rightWord)

/-- Serially compose two carrier-hidden tangles by matching equal source
coordinates. -/
noncomputable def serialCompose
    (left right : CoordinatizedTwoSidedOpenTangle.{u, v} B) :
    CoordinatizedTwoSidedOpenTangle.{u, v} B where
  V := left.V ⊕ right.V
  I := (left.I ⊕ right.I) ⊕ (left.R ⊕ right.L)
  L := left.L
  R := right.R
  data := TwoSidedOpenTangleData.serialCompose left.data right.data
    (left.rightCoordinate.symm.trans right.leftCoordinate)
  leftCoordinate := left.leftCoordinate
  rightCoordinate := right.rightCoordinate

/-- Literal support composition is relational composition in the common
source coordinates. -/
theorem serialCompose_acceptsBoundaryWords_iff
    (left right : CoordinatizedTwoSidedOpenTangle.{u, v} B)
    (leftWord rightWord : B → Color) :
    (serialCompose left right).AcceptsBoundaryWords leftWord rightWord ↔
      ∃ middleWord : B → Color,
        left.AcceptsBoundaryWords leftWord middleWord ∧
          right.AcceptsBoundaryWords middleWord rightWord := by
  unfold AcceptsBoundaryWords
  change
    (TwoSidedOpenTangleData.serialCompose left.data right.data
      (left.rightCoordinate.symm.trans right.leftCoordinate)).AcceptsBoundaryWords
        (left.leftBoundaryWord leftWord)
        (right.rightBoundaryWord rightWord) ↔ _
  rw [TwoSidedOpenTangleData.serialCompose_acceptsBoundaryWords_iff]
  constructor
  · rintro ⟨middle, hleft, hright⟩
    let middleWord : B → Color := fun step => middle (left.rightCoordinate step)
    refine ⟨middleWord, ?_, ?_⟩
    · have hmiddle : left.rightBoundaryWord middleWord = middle := by
        funext dart
        simp [rightBoundaryWord, middleWord]
      rw [hmiddle]
      exact hleft
    · have htransport : right.leftBoundaryWord middleWord =
          (fun dart => middle
            (left.rightCoordinate (right.leftCoordinate.symm dart))) := by
        rfl
      rw [htransport]
      exact hright
  · rintro ⟨middleWord, hleft, hright⟩
    refine ⟨left.rightBoundaryWord middleWord, hleft, ?_⟩
    have htransport :
        (fun dart => left.rightBoundaryWord middleWord
          ((left.rightCoordinate.symm.trans right.leftCoordinate).symm dart)) =
        right.leftBoundaryWord middleWord := by
      funext dart
      simp [leftBoundaryWord, rightBoundaryWord, Equiv.trans_apply]
    rw [htransport]
    exact hright

/-- Right-associated serial composition of a nonempty heterogeneous chain. -/
noncomputable def composeNonempty
    (first : CoordinatizedTwoSidedOpenTangle.{u, v} B) :
    List (CoordinatizedTwoSidedOpenTangle.{u, v} B) →
      CoordinatizedTwoSidedOpenTangle.{u, v} B
  | [] => first
  | next :: rest => serialCompose first (composeNonempty next rest)

/-- The source-ordered support word of a nonempty literal chain. -/
def supportWord
    (first : CoordinatizedTwoSidedOpenTangle.{u, v} B)
    (rest : List (CoordinatizedTwoSidedOpenTangle.{u, v} B)) :
    List ((B → Color) → (B → Color) → Prop) :=
  first.AcceptsBoundaryWords :: rest.map AcceptsBoundaryWords

/-- A heterogeneous literal chain accepts exactly the paths of its support
word.  This is finite matrix multiplication at positivity level, with no
homogeneity premise on successive pieces. -/
theorem composeNonempty_acceptsBoundaryWords_iff_exactTransferWord
    (first : CoordinatizedTwoSidedOpenTangle.{u, v} B)
    (rest : List (CoordinatizedTwoSidedOpenTangle.{u, v} B))
    (leftWord rightWord : B → Color) :
    (composeNonempty first rest).AcceptsBoundaryWords leftWord rightWord ↔
      ExactTransferWord (supportWord first rest) leftWord rightWord := by
  induction rest generalizing first leftWord with
  | nil =>
      simp [composeNonempty, supportWord, ExactTransferWord]
  | cons next rest ih =>
      rw [composeNonempty, serialCompose_acceptsBoundaryWords_iff]
      simp only [supportWord, List.map_cons, ExactTransferWord]
      constructor
      · rintro ⟨middleWord, hfirst, hrest⟩
        exact ⟨middleWord, hfirst, (ih next middleWord).1 hrest⟩
      · rintro ⟨middleWord, hfirst, hrest⟩
        exact ⟨middleWord, hfirst, (ih next middleWord).2 hrest⟩

/-- A pointwise map of a heterogeneous relation word sends every exact path
to an exact path.  The theorem is deliberately one-way: projecting a finite
profile can merge states, so a path between projected words need not lift
without a separate factorization theorem. -/
theorem exactTransferWord_map_of_forall₂
    {Profile Word : Type*}
    (project : Profile → Word)
    {profileSteps : List (Profile → Profile → Prop)}
    {wordSteps : List (Word → Word → Prop)}
    (hsteps : List.Forall₂
      (fun profileStep wordStep =>
        ∀ left right, profileStep left right →
          wordStep (project left) (project right))
      profileSteps wordSteps)
    {left right : Profile}
    (hpath : ExactTransferWord profileSteps left right) :
    ExactTransferWord wordSteps (project left) (project right) := by
  induction hsteps generalizing left with
  | nil =>
      simpa [ExactTransferWord] using congrArg project hpath
  | cons hstep _hrest ih =>
      rcases hpath with ⟨middle, hfirst, htail⟩
      exact ⟨project middle, hstep left middle hfirst, ih htail⟩

end CoordinatizedTwoSidedOpenTangle

end

end GoertzelV24OpenTangleComposition

end Mettapedia.GraphTheory.FourColor
