import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDDimension16Census

/-!
# Derivative-label alpha reduction on the unpadded dimension-sixteen carrier

The unpadded raw syntax uses a finite label type for active derivative slots.
Those labels are not physical data.  This module gives `derivativeOrder` the
explicit interpretation of a map from ordered positions to active labels and
then separates the raw derivative data into

* a permutation of the derivative labels, and
* the owner and spacetime axis at each ordered position.

Dropping the first coordinate is therefore an exact alpha quotient, not a
choice of representatives.  The quotient is constructed as a genuine
`Quotient`, proved equivalent to the ordered-word carrier, and shown to
commute with the literal hypercubic action while preserving the active tensor
sign.  No field antisymmetry, Bianchi, EOM, IBP, trace, commutator, or
Cayley--Hamilton identity is imposed here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16AlphaReduction

open V14HypercubicFDCensus
open HypercubicUnpaddedFDSyntax
open HypercubicRawFDCharacterCensus
open HypercubicRawFDDimension16Census

/-! ## Ordered derivative words -/

/-- Derivative ownership and spacetime axes indexed by ordered positions,
rather than by disposable active labels. -/
structure OrderedDerivativeWord (fieldCount derivativeCount : ℕ) where
  ownerAtPosition : Fin derivativeCount → Fin fieldCount
  axisAtPosition : Fin derivativeCount → Axis
deriving DecidableEq, Fintype

@[ext] theorem OrderedDerivativeWord.ext
    {fieldCount derivativeCount : ℕ}
    (left right : OrderedDerivativeWord fieldCount derivativeCount)
    (howner : left.ownerAtPosition = right.ownerAtPosition)
    (haxis : left.axisAtPosition = right.axisAtPosition) : left = right := by
  cases left
  cases right
  simp_all

theorem unpaddedDerivativeLayout_ext
    {fieldCount derivativeCount : ℕ}
    (left right : UnpaddedDerivativeLayout fieldCount derivativeCount)
    (horder : left.derivativeOrder = right.derivativeOrder)
    (howner : left.derivativeOwner = right.derivativeOwner) : left = right := by
  cases left
  cases right
  simp_all

theorem unpaddedAxisAssignment_ext
    {fieldCount derivativeCount : ℕ}
    (left right : UnpaddedAxisAssignment fieldCount derivativeCount)
    (hfirst : left.fieldFirst = right.fieldFirst)
    (hsecond : left.fieldSecond = right.fieldSecond)
    (hderivative : left.derivativeAxis = right.derivativeAxis) :
    left = right := by
  cases left
  cases right
  simp_all

theorem unpaddedFDSector_ext
    {fieldCount derivativeCount : ℕ}
    (left right : UnpaddedFDSector fieldCount derivativeCount)
    (htrace : left.trace = right.trace)
    (hderivatives : left.derivatives = right.derivatives)
    (haxes : left.axes = right.axes) : left = right := by
  cases left
  cases right
  simp_all

/-- Read the raw derivative layout as an ordered word.  A position is first
sent through `derivativeOrder` to its active label; ownership and axis data
are then read at that label. -/
def orderedDerivativeWord
    {fieldCount derivativeCount : ℕ}
    (layout : UnpaddedDerivativeLayout fieldCount derivativeCount)
    (axis : Fin derivativeCount → Axis) :
    OrderedDerivativeWord fieldCount derivativeCount where
  ownerAtPosition := fun position =>
    layout.derivativeOwner (layout.derivativeOrder position)
  axisAtPosition := fun position =>
    axis (layout.derivativeOrder position)

/-- The raw labeled presentation is exactly a label permutation together
with an ordered derivative word. -/
def derivativePresentationEquiv (fieldCount derivativeCount : ℕ) :
    (UnpaddedDerivativeLayout fieldCount derivativeCount ×
        (Fin derivativeCount → Axis)) ≃
      (Equiv.Perm (Fin derivativeCount) ×
        OrderedDerivativeWord fieldCount derivativeCount) where
  toFun data :=
    (data.1.derivativeOrder, orderedDerivativeWord data.1 data.2)
  invFun data :=
    ( { derivativeOrder := data.1
        derivativeOwner := fun label =>
          data.2.ownerAtPosition (data.1.symm label) },
      fun label => data.2.axisAtPosition (data.1.symm label) )
  left_inv data := by
    rcases data with ⟨⟨order, owner⟩, axis⟩
    apply Prod.ext
    · apply unpaddedDerivativeLayout_ext
      · rfl
      · funext label
        simp [orderedDerivativeWord]
    · funext label
      simp [orderedDerivativeWord]
  right_inv data := by
    rcases data with ⟨order, word⟩
    apply Prod.ext
    · rfl
    · cases word
      simp [orderedDerivativeWord]

/-! ## Alpha relabeling and its complete invariant -/

/-- Rename active derivative labels while leaving their ordered positions
unchanged.  If `rename` sends an old label to a new one, the order map is
postcomposed by `rename`, while owner and axis data are pulled back along its
inverse. -/
def relabelDerivatives
    {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin derivativeCount))
    (layout : UnpaddedDerivativeLayout fieldCount derivativeCount)
    (axis : Fin derivativeCount → Axis) :
    UnpaddedDerivativeLayout fieldCount derivativeCount ×
      (Fin derivativeCount → Axis) :=
  ( { derivativeOrder := layout.derivativeOrder.trans rename
      derivativeOwner := fun label =>
        layout.derivativeOwner (rename.symm label) },
    fun label => axis (rename.symm label) )

theorem orderedDerivativeWord_relabelDerivatives
    {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin derivativeCount))
    (layout : UnpaddedDerivativeLayout fieldCount derivativeCount)
    (axis : Fin derivativeCount → Axis) :
    orderedDerivativeWord (relabelDerivatives rename layout axis).1
        (relabelDerivatives rename layout axis).2 =
      orderedDerivativeWord layout axis := by
  cases layout with
  | mk order owner =>
      apply OrderedDerivativeWord.ext <;> funext position <;>
        simp [orderedDerivativeWord, relabelDerivatives]

/-- Equality of ordered words is exactly derivative-label alpha
equivalence. -/
def DerivativeAlphaEquivalent
    {fieldCount derivativeCount : ℕ}
    (left right : UnpaddedDerivativeLayout fieldCount derivativeCount ×
      (Fin derivativeCount → Axis)) : Prop :=
  orderedDerivativeWord left.1 left.2 =
    orderedDerivativeWord right.1 right.2

instance derivativeAlphaSetoid (fieldCount derivativeCount : ℕ) :
    Setoid (UnpaddedDerivativeLayout fieldCount derivativeCount ×
      (Fin derivativeCount → Axis)) where
  r := DerivativeAlphaEquivalent
  iseqv := by
    constructor
    · intro value
      rfl
    · intro left right h
      exact h.symm
    · intro left middle right hlm hmr
      exact hlm.trans hmr

abbrev DerivativeAlphaQuotient (fieldCount derivativeCount : ℕ) :=
  Quotient (derivativeAlphaSetoid fieldCount derivativeCount)

/-- Every raw labeled presentation maps to its ordered derivative word. -/
def derivativeAlphaClassToWord (fieldCount derivativeCount : ℕ) :
    DerivativeAlphaQuotient fieldCount derivativeCount →
      OrderedDerivativeWord fieldCount derivativeCount :=
  Quotient.lift
    (fun data => orderedDerivativeWord data.1 data.2)
    (by
      intro left right h
      exact h)

/-- Canonical raw representative with identity derivative labeling. -/
def orderedDerivativeWordRepresentative
    {fieldCount derivativeCount : ℕ}
    (word : OrderedDerivativeWord fieldCount derivativeCount) :
    UnpaddedDerivativeLayout fieldCount derivativeCount ×
      (Fin derivativeCount → Axis) :=
  ( { derivativeOrder := Equiv.refl _
      derivativeOwner := word.ownerAtPosition },
    word.axisAtPosition )

/-- The derivative-label alpha quotient is exactly the ordered-word carrier. -/
def derivativeAlphaQuotientEquiv (fieldCount derivativeCount : ℕ) :
    DerivativeAlphaQuotient fieldCount derivativeCount ≃
      OrderedDerivativeWord fieldCount derivativeCount where
  toFun := derivativeAlphaClassToWord fieldCount derivativeCount
  invFun word := Quotient.mk _ (orderedDerivativeWordRepresentative word)
  left_inv quotient := by
    refine Quotient.inductionOn quotient ?_
    intro data
    apply Quotient.sound
    change orderedDerivativeWord
        (orderedDerivativeWordRepresentative
          (orderedDerivativeWord data.1 data.2)).1
        (orderedDerivativeWordRepresentative
          (orderedDerivativeWord data.1 data.2)).2 =
      orderedDerivativeWord data.1 data.2
    cases data with
    | mk layout axis =>
        cases layout
        rfl
  right_inv word := by
    cases word
    rfl

/-- Two labeled presentations have the same ordered word precisely when one
is obtained from the other by a unique derivative-label renaming. -/
theorem derivativeAlphaEquivalent_iff_existsUnique_relabel
    {fieldCount derivativeCount : ℕ}
    (left right : UnpaddedDerivativeLayout fieldCount derivativeCount ×
      (Fin derivativeCount → Axis)) :
    DerivativeAlphaEquivalent left right ↔
      ∃! rename : Equiv.Perm (Fin derivativeCount),
        relabelDerivatives rename left.1 left.2 = right := by
  constructor
  · intro h
    let rename := left.1.derivativeOrder.symm.trans
      right.1.derivativeOrder
    refine ⟨rename, ?_, ?_⟩
    · rcases left with ⟨⟨leftOrder, leftOwner⟩, leftAxis⟩
      rcases right with ⟨⟨rightOrder, rightOwner⟩, rightAxis⟩
      dsimp [DerivativeAlphaEquivalent, orderedDerivativeWord] at h
      apply Prod.ext
      · apply unpaddedDerivativeLayout_ext
        · apply Equiv.ext
          intro position
          change rightOrder (leftOrder.symm (leftOrder position)) =
            rightOrder position
          simp
        · funext label
          have howner := congrArg
            (fun word : OrderedDerivativeWord fieldCount derivativeCount =>
              word.ownerAtPosition (rightOrder.symm label)) h
          simpa [relabelDerivatives, rename, orderedDerivativeWord] using howner
      · funext label
        have haxis := congrArg
          (fun word : OrderedDerivativeWord fieldCount derivativeCount =>
            word.axisAtPosition (rightOrder.symm label)) h
        simpa [relabelDerivatives, rename, orderedDerivativeWord] using haxis
    · intro other hother
      have horder := congrArg
        (fun data : UnpaddedDerivativeLayout fieldCount derivativeCount ×
          (Fin derivativeCount → Axis) => data.1.derivativeOrder) hother
      apply Equiv.ext
      intro label
      have := congrArg (fun order : Equiv.Perm (Fin derivativeCount) =>
        order (left.1.derivativeOrder.symm label)) horder
      simpa [relabelDerivatives, rename] using this
  · rintro ⟨rename, hrename, _⟩
    rw [← hrename]
    exact (orderedDerivativeWord_relabelDerivatives
      rename left.1 left.2).symm

/-! ## Reduced sectors and the exact dimension-sixteen count -/

/-- One field-labeled sector after removing only derivative-label alpha
redundancy.  Trace cycles and field labels remain untouched. -/
structure DerivativeAlphaReducedSector
    (fieldCount derivativeCount : ℕ) where
  trace : UnpaddedTraceLayout fieldCount
  fieldFirst : Fin fieldCount → Axis
  fieldSecond : Fin fieldCount → Axis
  derivativeWord : OrderedDerivativeWord fieldCount derivativeCount
deriving DecidableEq, Fintype

@[ext] theorem DerivativeAlphaReducedSector.ext
    {fieldCount derivativeCount : ℕ}
    (left right : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (htrace : left.trace = right.trace)
    (hfirst : left.fieldFirst = right.fieldFirst)
    (hsecond : left.fieldSecond = right.fieldSecond)
    (hword : left.derivativeWord = right.derivativeWord) : left = right := by
  cases left
  cases right
  simp_all

/-- The complete raw sector is exactly a derivative-label permutation times
the derivative-alpha-reduced sector. -/
def unpaddedSectorDerivativeAlphaEquiv
    (fieldCount derivativeCount : ℕ) :
    UnpaddedFDSector fieldCount derivativeCount ≃
      (Equiv.Perm (Fin derivativeCount) ×
        DerivativeAlphaReducedSector fieldCount derivativeCount) where
  toFun sector :=
    (sector.derivativeOrder,
      { trace := sector.trace
        fieldFirst := sector.fieldFirst
        fieldSecond := sector.fieldSecond
        derivativeWord := orderedDerivativeWord sector.derivatives
          sector.derivativeAxis })
  invFun data :=
    { trace := data.2.trace
      derivatives :=
        { derivativeOrder := data.1
          derivativeOwner := fun label =>
            data.2.derivativeWord.ownerAtPosition (data.1.symm label) }
      axes :=
        { fieldFirst := data.2.fieldFirst
          fieldSecond := data.2.fieldSecond
          derivativeAxis := fun label =>
            data.2.derivativeWord.axisAtPosition (data.1.symm label) } }
  left_inv sector := by
    rcases sector with
      ⟨trace, ⟨order, owner⟩, ⟨fieldFirst, fieldSecond, derivativeAxis⟩⟩
    apply unpaddedFDSector_ext
    · rfl
    · apply unpaddedDerivativeLayout_ext
      · rfl
      · funext label
        change owner (order (order.symm label)) = owner label
        simp
    · apply unpaddedAxisAssignment_ext
      · rfl
      · rfl
      · funext label
        change derivativeAxis (order (order.symm label)) =
          derivativeAxis label
        simp
  right_inv data := by
    rcases data with ⟨order, reduced⟩
    rcases reduced with
      ⟨trace, fieldFirst, fieldSecond, ⟨ownerAtPosition, axisAtPosition⟩⟩
    apply Prod.ext
    · rfl
    · apply DerivativeAlphaReducedSector.ext
      · rfl
      · rfl
      · rfl
      · apply OrderedDerivativeWord.ext
        · funext position
          change ownerAtPosition (order.symm (order position)) =
            ownerAtPosition position
          simp
        · funext position
          change axisAtPosition (order.symm (order position)) =
            axisAtPosition position
          simp

/-- Exact-dimension-sixteen raw syntax with the disposable derivative-label
permutation split off as an explicit coordinate. -/
abbrev ExactDimension16DerivativeAlphaPresentation :=
  (fieldCount : Fin 9) ×'
    (Equiv.Perm (Fin (dimension16DerivativeCount fieldCount)) ×
      DerivativeAlphaReducedSector fieldCount.1
        (dimension16DerivativeCount fieldCount))

/-- The alpha presentation is an equivalence from the literal exact
dimension-sixteen subtype, not a replacement enumeration. -/
def exactDimension16DerivativeAlphaPresentationEquiv :
    ExactDimension16UnpaddedRawFDMonomial ≃
      ExactDimension16DerivativeAlphaPresentation :=
  exactDimension16MonomialSectorEquiv.trans <|
    Equiv.psigmaCongrRight fun fieldCount : Fin 9 =>
      unpaddedSectorDerivativeAlphaEquiv fieldCount.1
        (dimension16DerivativeCount fieldCount)

/-- The actual exact carrier after quotienting only derivative-label alpha
redundancy. -/
abbrev ExactDimension16DerivativeAlphaReducedCarrier :=
  (fieldCount : Fin 9) ×'
    DerivativeAlphaReducedSector fieldCount.1
      (dimension16DerivativeCount fieldCount)

/-- Forget only the separated derivative-label permutation. -/
def exactDimension16DerivativeAlphaNormalize
    (monomial : ExactDimension16UnpaddedRawFDMonomial) :
    ExactDimension16DerivativeAlphaReducedCarrier :=
  let presentation :=
    exactDimension16DerivativeAlphaPresentationEquiv monomial
  ⟨presentation.1, presentation.2.2⟩

def ExactDimension16DerivativeAlphaEquivalent
    (left right : ExactDimension16UnpaddedRawFDMonomial) : Prop :=
  exactDimension16DerivativeAlphaNormalize left =
    exactDimension16DerivativeAlphaNormalize right

instance exactDimension16DerivativeAlphaSetoid :
    Setoid ExactDimension16UnpaddedRawFDMonomial where
  r := ExactDimension16DerivativeAlphaEquivalent
  iseqv := by
    constructor
    · intro value
      rfl
    · intro left right h
      exact h.symm
    · intro left middle right hlm hmr
      exact hlm.trans hmr

abbrev ExactDimension16DerivativeAlphaQuotient :=
  Quotient exactDimension16DerivativeAlphaSetoid

/-- The quotient of the original exact carrier is equivalent to the reduced
carrier, so no representative is silently selected in later work. -/
def exactDimension16DerivativeAlphaQuotientEquiv :
    ExactDimension16DerivativeAlphaQuotient ≃
      ExactDimension16DerivativeAlphaReducedCarrier where
  toFun := Quotient.lift exactDimension16DerivativeAlphaNormalize
    (by
      intro left right h
      exact h)
  invFun reduced :=
    Quotient.mk _
      (exactDimension16DerivativeAlphaPresentationEquiv.symm
        ⟨reduced.1,
          (Equiv.refl (Fin (dimension16DerivativeCount reduced.1)),
            reduced.2)⟩)
  left_inv quotient := by
    refine Quotient.inductionOn quotient ?_
    intro monomial
    apply Quotient.sound
    change exactDimension16DerivativeAlphaNormalize
        (exactDimension16DerivativeAlphaPresentationEquiv.symm
          ⟨(exactDimension16DerivativeAlphaNormalize monomial).1,
            (Equiv.refl
              (Fin (dimension16DerivativeCount
                (exactDimension16DerivativeAlphaNormalize monomial).1)),
              (exactDimension16DerivativeAlphaNormalize monomial).2)⟩) =
      exactDimension16DerivativeAlphaNormalize monomial
    obtain ⟨presentation, rfl⟩ :=
      exactDimension16DerivativeAlphaPresentationEquiv.symm.surjective
        monomial
    rcases presentation with ⟨fieldCount, labelPermutation, reduced⟩
    rfl
  right_inv reduced := by
    rcases reduced with ⟨fieldCount, reduced⟩
    rfl

/-- Product presentation used to count one reduced sector. -/
def derivativeAlphaReducedSectorEquivProduct
    (fieldCount derivativeCount : ℕ) :
    DerivativeAlphaReducedSector fieldCount derivativeCount ≃
      UnpaddedTraceLayout fieldCount ×
        ((Fin fieldCount → Axis) × (Fin fieldCount → Axis)) ×
          ((Fin derivativeCount → Fin fieldCount) ×
            (Fin derivativeCount → Axis)) where
  toFun sector :=
    (sector.trace, (sector.fieldFirst, sector.fieldSecond),
      (sector.derivativeWord.ownerAtPosition,
        sector.derivativeWord.axisAtPosition))
  invFun data :=
    { trace := data.1
      fieldFirst := data.2.1.1
      fieldSecond := data.2.1.2
      derivativeWord :=
        { ownerAtPosition := data.2.2.1
          axisAtPosition := data.2.2.2 } }
  left_inv sector := by
    cases sector
    rfl
  right_inv data := by
    rcases data with ⟨trace, ⟨fieldFirst, fieldSecond⟩,
      ⟨ownerAtPosition, axisAtPosition⟩⟩
    rfl

theorem card_derivativeAlphaReducedSector
    (fieldCount derivativeCount : ℕ) :
    Fintype.card
        (DerivativeAlphaReducedSector fieldCount derivativeCount) =
      Nat.factorial fieldCount *
        (4 ^ fieldCount * 4 ^ fieldCount) *
          (fieldCount ^ derivativeCount * 4 ^ derivativeCount) := by
  rw [Fintype.card_congr
    (derivativeAlphaReducedSectorEquivProduct fieldCount derivativeCount)]
  simp [card_unpaddedTraceLayout]
  ring

/-- Exact cardinality of the original dimension-sixteen carrier after the
derivative-label alpha quotient and before physical relations. -/
theorem card_exactDimension16DerivativeAlphaReducedCarrier :
    Fintype.card ExactDimension16DerivativeAlphaReducedCarrier =
      21606911019319296 := by
  rw [Fintype.card_congr
    (Equiv.psigmaEquivSigma fun fieldCount : Fin 9 =>
      DerivativeAlphaReducedSector fieldCount.1
        (dimension16DerivativeCount fieldCount)),
    Fintype.card_sigma]
  simp_rw [card_derivativeAlphaReducedSector]
  norm_num [dimension16DerivativeCount, Nat.factorial,
    Fin.sum_univ_succ]

/-- Layout data after derivative-label alpha reduction; spacetime axes are
still kept in the common rank-sixteen tensor fiber. -/
abbrev Dimension16DerivativeAlphaReducedLayout :=
  (fieldCount : Fin 9) ×'
    (UnpaddedTraceLayout fieldCount.1 ×
      (Fin (dimension16DerivativeCount fieldCount) → Fin fieldCount.1))

def dimension16DerivativeAlphaReducedLayoutMultiplicityFor
    (fieldCount : Fin 9) : ℕ :=
  Nat.factorial fieldCount.1 *
    fieldCount.1 ^ dimension16DerivativeCount fieldCount

def dimension16DerivativeAlphaReducedLayoutMultiplicity : ℕ :=
  ∑ fieldCount : Fin 9,
    dimension16DerivativeAlphaReducedLayoutMultiplicityFor fieldCount

theorem card_dimension16DerivativeAlphaReducedLayout :
    Fintype.card Dimension16DerivativeAlphaReducedLayout =
      dimension16DerivativeAlphaReducedLayoutMultiplicity := by
  rw [Fintype.card_congr
    (Equiv.psigmaEquivSigma fun fieldCount : Fin 9 =>
      UnpaddedTraceLayout fieldCount.1 ×
        (Fin (dimension16DerivativeCount fieldCount) → Fin fieldCount.1)),
    Fintype.card_sigma]
  unfold dimension16DerivativeAlphaReducedLayoutMultiplicity
  apply Finset.sum_congr rfl
  intro fieldCount _
  rw [Fintype.card_prod, card_unpaddedTraceLayout,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rfl

/-- Removing disposable derivative labels shrinks the exact layout count from
`5,361,612,271,200` to `5,030,751`, before any physical relation is used. -/
theorem dimension16DerivativeAlphaReducedLayoutMultiplicity_exact :
    dimension16DerivativeAlphaReducedLayoutMultiplicity = 5030751 := by
  norm_num [dimension16DerivativeAlphaReducedLayoutMultiplicity,
    dimension16DerivativeAlphaReducedLayoutMultiplicityFor,
    dimension16DerivativeCount, Nat.factorial, Fin.sum_univ_succ]

/-! ## Hypercubic compatibility -/

def orderedDerivativeWordAct (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (word : OrderedDerivativeWord fieldCount derivativeCount) :
    OrderedDerivativeWord fieldCount derivativeCount where
  ownerAtPosition := word.ownerAtPosition
  axisAtPosition := fun position => h.perm (word.axisAtPosition position)

def derivativeAlphaReducedSectorAct (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    DerivativeAlphaReducedSector fieldCount derivativeCount where
  trace := sector.trace
  fieldFirst := fun slot => h.perm (sector.fieldFirst slot)
  fieldSecond := fun slot => h.perm (sector.fieldSecond slot)
  derivativeWord := orderedDerivativeWordAct h sector.derivativeWord

def exactDimension16DerivativeAlphaReducedAct (h : Hypercubic4)
    (carrier : ExactDimension16DerivativeAlphaReducedCarrier) :
    ExactDimension16DerivativeAlphaReducedCarrier :=
  ⟨carrier.1, derivativeAlphaReducedSectorAct h carrier.2⟩

def derivativeAlphaReducedSectorTensorSign (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) : ℚ :=
  (∏ slot, Hypercubic4.axisSign h (sector.fieldFirst slot)) *
    (∏ slot, Hypercubic4.axisSign h (sector.fieldSecond slot)) *
      ∏ position, Hypercubic4.axisSign h
        (sector.derivativeWord.axisAtPosition position)

def exactDimension16DerivativeAlphaReducedTensorSign (h : Hypercubic4)
    (carrier : ExactDimension16DerivativeAlphaReducedCarrier) : ℚ :=
  derivativeAlphaReducedSectorTensorSign h carrier.2

theorem orderedDerivativeWord_act
    (h : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (layout : UnpaddedDerivativeLayout fieldCount derivativeCount)
    (axis : Fin derivativeCount → Axis) :
    orderedDerivativeWord layout (fun label => h.perm (axis label)) =
      orderedDerivativeWordAct h (orderedDerivativeWord layout axis) := by
  rfl

theorem unpaddedSectorDerivativeAlphaEquiv_act
    (h : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (sector : UnpaddedFDSector fieldCount derivativeCount) :
    unpaddedSectorDerivativeAlphaEquiv fieldCount derivativeCount
        { trace := sector.trace
          derivatives := sector.derivatives
          axes :=
            { fieldFirst := fun slot => h.perm (sector.fieldFirst slot)
              fieldSecond := fun slot => h.perm (sector.fieldSecond slot)
              derivativeAxis := fun slot =>
                h.perm (sector.derivativeAxis slot) } } =
      ((unpaddedSectorDerivativeAlphaEquiv fieldCount derivativeCount
          sector).1,
        derivativeAlphaReducedSectorAct h
          (unpaddedSectorDerivativeAlphaEquiv fieldCount derivativeCount
            sector).2) := by
  cases sector with
  | mk trace derivatives axes =>
      cases derivatives
      cases axes
      rfl

/-- The exact alpha normalization commutes with the action on the original
unpadded exact-dimension subtype. -/
theorem exactDimension16DerivativeAlphaNormalize_act
    (h : Hypercubic4)
    (monomial : ExactDimension16UnpaddedRawFDMonomial) :
    exactDimension16DerivativeAlphaNormalize
        (exactDimension16UnpaddedAct h monomial) =
      exactDimension16DerivativeAlphaReducedAct h
        (exactDimension16DerivativeAlphaNormalize monomial) := by
  obtain ⟨sector, rfl⟩ :=
    exactDimension16MonomialSectorEquiv.symm.surjective monomial
  rw [exactDimension16UnpaddedAct_symm_apply]
  rcases sector with ⟨fieldCount, sector⟩
  change
    (⟨fieldCount,
      (unpaddedSectorDerivativeAlphaEquiv fieldCount.1
        (dimension16DerivativeCount fieldCount)
        { trace := sector.trace
          derivatives := sector.derivatives
          axes :=
            { fieldFirst := fun slot => h.perm (sector.fieldFirst slot)
              fieldSecond := fun slot => h.perm (sector.fieldSecond slot)
              derivativeAxis := fun slot =>
                h.perm (sector.derivativeAxis slot) } }).2⟩ :
        ExactDimension16DerivativeAlphaReducedCarrier) =
      ⟨fieldCount,
        derivativeAlphaReducedSectorAct h
          (unpaddedSectorDerivativeAlphaEquiv fieldCount.1
            (dimension16DerivativeCount fieldCount) sector).2⟩
  have hsnd := congrArg Prod.snd
    (unpaddedSectorDerivativeAlphaEquiv_act h sector)
  exact congrArg
    (fun reduced : DerivativeAlphaReducedSector fieldCount.1
        (dimension16DerivativeCount fieldCount) =>
      (⟨fieldCount, reduced⟩ :
        ExactDimension16DerivativeAlphaReducedCarrier)) hsnd

theorem orderedDerivativeWord_sign
    (h : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (layout : UnpaddedDerivativeLayout fieldCount derivativeCount)
    (axis : Fin derivativeCount → Axis) :
    (∏ label, Hypercubic4.axisSign h (axis label)) =
      ∏ position, Hypercubic4.axisSign h
        ((orderedDerivativeWord layout axis).axisAtPosition position) := by
  classical
  exact (Equiv.prod_comp layout.derivativeOrder
    (fun label => Hypercubic4.axisSign h (axis label))).symm

/-- The quotient presentation preserves the complete active tensor sign on
the original exact carrier. -/
theorem exactDimension16DerivativeAlphaNormalize_tensorSign
    (h : Hypercubic4)
    (monomial : ExactDimension16UnpaddedRawFDMonomial) :
    monomial.1.tensorSign h =
      exactDimension16DerivativeAlphaReducedTensorSign h
        (exactDimension16DerivativeAlphaNormalize monomial) := by
  obtain ⟨sector, rfl⟩ :=
    exactDimension16MonomialSectorEquiv.symm.surjective monomial
  rcases sector with ⟨fieldCount, sector⟩
  rw [tensorSign_exactDimension16MonomialSectorEquiv_symm_apply]
  unfold exactDimension16DerivativeAlphaReducedTensorSign
    derivativeAlphaReducedSectorTensorSign
  change
    (∏ slot, Hypercubic4.axisSign h (sector.axes.fieldFirst slot)) *
        (∏ slot, Hypercubic4.axisSign h (sector.axes.fieldSecond slot)) *
          (∏ slot, Hypercubic4.axisSign h
            (sector.axes.derivativeAxis slot)) =
      (∏ slot, Hypercubic4.axisSign h (sector.axes.fieldFirst slot)) *
        (∏ slot, Hypercubic4.axisSign h (sector.axes.fieldSecond slot)) *
          ∏ position, Hypercubic4.axisSign h
            ((orderedDerivativeWord sector.derivatives
              sector.axes.derivativeAxis).axisAtPosition position)
  rw [orderedDerivativeWord_sign h sector.derivatives
    sector.axes.derivativeAxis]

/-- The alpha reduction commutes with signed coordinate permutations. -/
theorem derivativeAlphaReduction_hypercubic_equivariant
    (h : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (layout : UnpaddedDerivativeLayout fieldCount derivativeCount)
    (axis : Fin derivativeCount → Axis) :
    derivativeAlphaClassToWord fieldCount derivativeCount
        (Quotient.mk _ (layout, fun label => h.perm (axis label))) =
      orderedDerivativeWordAct h
        (derivativeAlphaClassToWord fieldCount derivativeCount
          (Quotient.mk _ (layout, axis))) := by
  exact orderedDerivativeWord_act h layout axis

/-- The derivative part of the active tensor sign is unchanged by passing
from disposable labels to ordered positions. -/
theorem derivativeAlphaReduction_preserves_tensorSign
    (h : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (layout : UnpaddedDerivativeLayout fieldCount derivativeCount)
    (axis : Fin derivativeCount → Axis) :
    (∏ label, Hypercubic4.axisSign h (axis label)) =
      ∏ position, Hypercubic4.axisSign h
        ((derivativeAlphaClassToWord fieldCount derivativeCount
          (Quotient.mk _ (layout, axis))).axisAtPosition position) := by
  exact orderedDerivativeWord_sign h layout axis

end HypercubicDimension16AlphaReduction
end YangMills
end QuantumTheory
end Mettapedia
