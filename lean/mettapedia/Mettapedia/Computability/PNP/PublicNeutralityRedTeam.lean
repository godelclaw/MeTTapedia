import Mettapedia.Computability.PNP.CoarseProjectionObstruction

/-!
# Public-neutrality red-team checks for the PNP v13 interface

This file isolates finite checks for the public-input interface.  The full
public instance and the neutral public skeleton are different formal types.
Neutral skeletons may agree across message-opposite pairs, but any
target-determining use of the full public instance must appear through a
charged safe or gauge evidence leaf.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u v w

/-! ## Type-level public-input split -/

/-- Full public input wrapper.  This is deliberately not the neutral skeleton
type. -/
structure Yfull (Raw : Type u) where
  raw : Raw
deriving DecidableEq, Repr

/-- Target-blind neutral skeleton wrapper. -/
structure Yneu (Raw : Type u) where
  raw : Raw
deriving DecidableEq, Repr

/-- Neutral atoms are parameterized only by the neutral skeleton payload. -/
structure NeutralPublicAtom (RawNeu : Type u) where
  atom : Yneu RawNeu
deriving DecidableEq, Repr

/-- A public instance split into full input, neutral skeleton, and charged
evidence payload. -/
structure PublicInstanceSplit
    (Omega : Type u) (RawFull : Type v) (RawNeu : Type w)
    (Charged : Type v) where
  yfull : Omega -> Yfull RawFull
  yneu : Omega -> Yneu RawNeu
  ycharged : Omega -> Charged

/-! ## Red-team test 1: full public equality cannot cross target phases -/

theorem sameFullY_noOpposite
    {Omega YType : Type*} (Y : Omega -> YType) (B : Omega -> Bool)
    (hSingle : ∀ w0 w1, Y w0 = Y w1 -> B w0 = B w1) :
    ¬ ∃ w0 w1,
      Y w0 = Y w1 ∧ B w0 = false ∧ B w1 = true := by
  intro h
  rcases h with ⟨w0, w1, hY, h0, h1⟩
  have hB := hSingle w0 w1 hY
  rw [h0, h1] at hB
  cases hB

/-! ## Red-team tests 2 and 7: neutral atoms cannot generate the target -/

/-- Pair-neutrality: the statistic agrees on every supported opposite pair. -/
def PairNeutral {Omega K : Type*}
    (Support : Omega -> Omega -> Prop) (N : Omega -> K) : Prop :=
  ∀ w0 w1, Support w0 w1 -> N w0 = N w1

/-- Opposite support with an explicit inhabited pair. -/
def HasMessageOppositePair {Omega : Type*}
    (Support : Omega -> Omega -> Prop) (B : Omega -> Bool) : Prop :=
  ∃ w0 w1, Support w0 w1 ∧ B w0 = false ∧ B w1 = true

theorem neutral_generates_target_contradiction
    {Omega K : Type*} (Support : Omega -> Omega -> Prop)
    (N : Omega -> K) (B : Omega -> Bool)
    (hNeutral : PairNeutral Support N)
    (hGen : ∃ f : K -> Bool, ∀ w, B w = f (N w))
    (hOpp : HasMessageOppositePair Support B) :
    False := by
  rcases hGen with ⟨f, hf⟩
  rcases hOpp with ⟨w0, w1, hSupport, h0, h1⟩
  have hN := hNeutral w0 w1 hSupport
  have hB : B w0 = B w1 := by
    rw [hf w0, hf w1, hN]
  rw [h0, h1] at hB
  cases hB

theorem neutralSkeleton_not_sufficient
    {Omega K : Type*} (Support : Omega -> Omega -> Prop)
    (Yneu : Omega -> K) (B : Omega -> Bool)
    (hNeutral : PairNeutral Support Yneu)
    (hOppSupport : HasMessageOppositePair Support B) :
    ¬ ∃ f : K -> Bool, ∀ w, B w = f (Yneu w) := by
  intro hGen
  exact
    neutral_generates_target_contradiction
      Support Yneu B hNeutral hGen hOppSupport

/-! ## Red-team test 3: full public bits carry derivative mass -/

/-- A finite coupling whose pairs always cross from target false to target
true. -/
structure CouplingOnOppositePhases (Omega : Type u) (B : Omega -> Bool) where
  Pair : Type v
  pairFinite : Fintype Pair
  nonempty : Nonempty Pair
  left : Pair -> Omega
  right : Pair -> Omega
  opposite : ∀ p, B (left p) = false ∧ B (right p) = true

def publicBitDerivativeMass {Omega : Type u} {n : Nat}
    (Ybit : Fin n -> Omega -> Bool)
    {B : Omega -> Bool} (Gamma : CouplingOnOppositePhases Omega B)
    (r : Fin n) : Nat := by
  classical
  letI := Gamma.pairFinite
  exact
    Fintype.card
      {p : Gamma.Pair // Ybit r (Gamma.left p) ≠ Ybit r (Gamma.right p)}

def publicBitTotalDerivativeMass {Omega : Type u} {n : Nat}
    (Ybit : Fin n -> Omega -> Bool)
    {B : Omega -> Bool} (Gamma : CouplingOnOppositePhases Omega B) : Nat :=
  Finset.univ.sum (fun r : Fin n => publicBitDerivativeMass Ybit Gamma r)

theorem publicBit_derivative_mass_ge_one
    {Omega : Type u} {n : Nat} (Ybit : Fin n -> Omega -> Bool)
    (B : Omega -> Bool) (Gamma : CouplingOnOppositePhases Omega B)
    (hGen : ∃ f : (Fin n -> Bool) -> Bool,
      ∀ w, B w = f (fun r => Ybit r w)) :
    1 ≤ publicBitTotalDerivativeMass Ybit Gamma := by
  classical
  rcases hGen with ⟨f, hf⟩
  let p : Gamma.Pair := Classical.choice Gamma.nonempty
  have hOpp := Gamma.opposite p
  have hExists :
      ∃ r : Fin n, Ybit r (Gamma.left p) ≠ Ybit r (Gamma.right p) := by
    by_contra hnone
    have hsame :
        (fun r : Fin n => Ybit r (Gamma.left p)) =
          (fun r : Fin n => Ybit r (Gamma.right p)) := by
      funext r
      by_contra hneq
      exact hnone ⟨r, hneq⟩
    have hB : B (Gamma.left p) = B (Gamma.right p) := by
      rw [hf (Gamma.left p), hf (Gamma.right p), hsame]
    rw [hOpp.1, hOpp.2] at hB
    cases hB
  rcases hExists with ⟨r, hr⟩
  have hpos : 0 < publicBitDerivativeMass Ybit Gamma r := by
    letI := Gamma.pairFinite
    unfold publicBitDerivativeMass
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨p, hr⟩⟩
  unfold publicBitTotalDerivativeMass
  exact
    le_trans (Nat.succ_le_of_lt hpos)
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r))

/-! ## Red-team test 4: target-measurable fields are not admissible -/

/-- A finite field represented by its atom map. -/
structure FiniteSigmaField (Omega : Type u) where
  Atom : Type v
  atomDecidable : DecidableEq Atom
  atom : Omega -> Atom

def MeasurableWrt {Omega : Type u}
    (C : FiniteSigmaField Omega) (B : Omega -> Bool) : Prop :=
  Sufficient C.atom B

def BalancedConditioning {Omega : Type u} [Fintype Omega]
    (C : FiniteSigmaField Omega) (B : Omega -> Bool) : Prop :=
  letI := C.atomDecidable
  Neutral C.atom B

theorem measurable_not_admissible
    {Omega : Type u} [Fintype Omega] (B : Omega -> Bool)
    (C : FiniteSigmaField Omega)
    (hMeas : MeasurableWrt C B)
    (hNondeg : NontrivialWitnessBit B) :
    ¬ BalancedConditioning C B := by
  letI := C.atomDecidable
  intro hBalanced
  exact
    noThreading_neutral_sufficient_blocks_nontrivial_bit
      (u := C.atom) (x := B) hNondeg ⟨hBalanced, hMeas⟩

/-! ## Red-team test 5: sufficient boundary summaries force large error -/

/-- Balanced bit, represented as the success rate of the constant-true
predictor. -/
def BalancedBit {Omega : Type u} [Fintype Omega]
    (B : Omega -> Bool) : Prop :=
  globalDecoderSuccess (fun _ : Omega => true) B = (1 : Rat) / 2

/-- Boundary mixing relative to the balanced baseline. -/
def BoundaryMixingBound {Omega ZType : Type*} [Fintype Omega]
    (B : Omega -> Bool) (Z : Omega -> ZType) (eps : Rat) : Prop :=
  ∀ h : ZType -> Bool,
    globalDecoderSuccess (fun w => h (Z w)) B ≤
      globalDecoderSuccess (fun _ : Omega => true) B + eps

theorem boundaryFeatureSuccess_eq_one_of_sufficient
    {Omega ZType : Type*} [Fintype Omega] [Nonempty Omega]
    (B : Omega -> Bool) (Z : Omega -> ZType) (h0 : ZType -> Bool)
    (hSuff : ∀ w, B w = h0 (Z w)) :
    globalDecoderSuccess (fun w => h0 (Z w)) B = 1 := by
  classical
  unfold globalDecoderSuccess
  have hcard :
      Fintype.card {w : Omega // h0 (Z w) = B w} =
        Fintype.card Omega := by
    apply Fintype.card_congr
    exact
      { toFun := fun w => w.val
        invFun := fun w => ⟨w, (hSuff w).symm⟩
        left_inv := by
          intro w
          cases w
          rfl
        right_inv := by
          intro w
          rfl }
  have hnonzero : ((Fintype.card Omega : Nat) : Rat) ≠ 0 := by
    have hpos : 0 < Fintype.card Omega :=
      Fintype.card_pos_iff.mpr ‹Nonempty Omega›
    exact_mod_cast Nat.ne_of_gt hpos
  rw [hcard]
  field_simp [hnonzero]

theorem sufficient_boundary_feature_forces_eps_ge_half
    {Omega ZType : Type*} [Fintype Omega] [Nonempty Omega]
    (B : Omega -> Bool) (Z : Omega -> ZType) {eps : Rat}
    (hBalanced : BalancedBit B)
    (hSuff : ∃ h0 : ZType -> Bool, ∀ w, B w = h0 (Z w))
    (hMix : BoundaryMixingBound B Z eps) :
    (1 : Rat) / 2 ≤ eps := by
  rcases hSuff with ⟨h0, hh0⟩
  have hle := hMix h0
  rw [boundaryFeatureSuccess_eq_one_of_sufficient B Z h0 hh0, hBalanced] at hle
  linarith

/-! ## Red-team test 8: public reads normalize to neutral or charged leaves -/

/-- Interface discipline for public reads.  The main theorem below returns the
named structure field; it is an explicit obligation of the interface. -/
structure PublicReadDiscipline (PublicSymbol : Type u) (Leaf : Type v) where
  targetBlind : PublicSymbol -> Prop
  chargedLeaf : PublicSymbol -> Leaf -> Prop
  isSafe : Leaf -> Prop
  isGauge : Leaf -> Prop
  normalizes_neutral_or_charged :
    ∀ theta,
      targetBlind theta ∨
        ∃ leaf, chargedLeaf theta leaf ∧ (isSafe leaf ∨ isGauge leaf)

theorem public_read_normalizes_neutral_or_charged
    {PublicSymbol : Type u} {Leaf : Type v}
    (D : PublicReadDiscipline PublicSymbol Leaf) (theta : PublicSymbol) :
    D.targetBlind theta ∨
      ∃ leaf, D.chargedLeaf theta leaf ∧ (D.isSafe leaf ∨ D.isGauge leaf) :=
  D.normalizes_neutral_or_charged theta

/-! ## Inhabited toy witnesses -/

def publicNeutralityToyFullY (w : Bool) : Yfull Bool :=
  ⟨w⟩

def publicNeutralityToyYneu (_w : Bool) : Yneu Unit :=
  ⟨()⟩

def publicNeutralityToyB (w : Bool) : Bool :=
  w

def publicNeutralityToySupport (w0 w1 : Bool) : Prop :=
  w0 = false ∧ w1 = true

theorem publicNeutralityToy_sameFullY_noOpposite :
    ¬ ∃ w0 w1,
      publicNeutralityToyFullY w0 = publicNeutralityToyFullY w1 ∧
        publicNeutralityToyB w0 = false ∧
        publicNeutralityToyB w1 = true := by
  apply sameFullY_noOpposite
  intro w0 w1 hY
  cases w0 <;> cases w1 <;>
    simp [publicNeutralityToyFullY, publicNeutralityToyB] at hY ⊢

theorem publicNeutralityToy_pairNeutral :
    PairNeutral publicNeutralityToySupport publicNeutralityToyYneu := by
  intro w0 w1 _h
  simp [publicNeutralityToyYneu]

theorem publicNeutralityToy_hasOppositePair :
    HasMessageOppositePair publicNeutralityToySupport publicNeutralityToyB := by
  exact ⟨false, true, ⟨rfl, rfl⟩, rfl, rfl⟩

theorem publicNeutralityToy_neutralSkeleton_not_sufficient :
    ¬ ∃ f : Yneu Unit -> Bool,
      ∀ w, publicNeutralityToyB w = f (publicNeutralityToyYneu w) :=
  neutralSkeleton_not_sufficient
    publicNeutralityToySupport publicNeutralityToyYneu publicNeutralityToyB
    publicNeutralityToy_pairNeutral publicNeutralityToy_hasOppositePair

def publicNeutralityToyYbit : Fin 1 -> Bool -> Bool :=
  fun _ w => publicNeutralityToyB w

def publicNeutralityToyCoupling :
    CouplingOnOppositePhases Bool publicNeutralityToyB where
  Pair := Unit
  pairFinite := inferInstance
  nonempty := inferInstance
  left := fun _ => false
  right := fun _ => true
  opposite := by
    intro p
    cases p
    exact ⟨rfl, rfl⟩

theorem publicNeutralityToy_publicBit_derivative_mass_ge_one :
    1 ≤
      publicBitTotalDerivativeMass
        publicNeutralityToyYbit publicNeutralityToyCoupling := by
  apply publicBit_derivative_mass_ge_one
  exact
    ⟨fun bits => bits 0, by
      intro w
      cases w <;> rfl⟩

def publicNeutralityToySigmaField : FiniteSigmaField Bool where
  Atom := Bool
  atomDecidable := inferInstance
  atom := publicNeutralityToyB

theorem publicNeutralityToy_measurable :
    MeasurableWrt publicNeutralityToySigmaField publicNeutralityToyB := by
  intro w0 w1 h
  exact h

theorem publicNeutralityToy_nontrivial :
    NontrivialWitnessBit publicNeutralityToyB := by
  exact ⟨true, false, rfl, rfl⟩

theorem publicNeutralityToy_measurable_not_admissible :
    ¬ BalancedConditioning
        publicNeutralityToySigmaField publicNeutralityToyB :=
  measurable_not_admissible
    publicNeutralityToyB publicNeutralityToySigmaField
    publicNeutralityToy_measurable publicNeutralityToy_nontrivial

theorem publicNeutralityToy_balanced :
    BalancedBit publicNeutralityToyB := by
  norm_num [BalancedBit, globalDecoderSuccess, publicNeutralityToyB]

theorem publicNeutralityToy_boundary_forces_eps_ge_half {eps : Rat}
    (hMix : BoundaryMixingBound
      publicNeutralityToyB publicNeutralityToyB eps) :
    (1 : Rat) / 2 ≤ eps :=
  sufficient_boundary_feature_forces_eps_ge_half
    publicNeutralityToyB publicNeutralityToyB
    publicNeutralityToy_balanced
    ⟨fun z => z, by intro w; rfl⟩
    hMix

inductive ToyPublicSymbol where
  | neutral
  | safe
  | gauge
deriving DecidableEq, Repr

inductive ToyEvidenceLeaf where
  | safe
  | gauge
deriving DecidableEq, Repr

def toyPublicReadDiscipline :
    PublicReadDiscipline ToyPublicSymbol ToyEvidenceLeaf where
  targetBlind
    | .neutral => True
    | .safe => False
    | .gauge => False
  chargedLeaf
    | .safe, .safe => True
    | .gauge, .gauge => True
    | _, _ => False
  isSafe
    | .safe => True
    | .gauge => False
  isGauge
    | .safe => False
    | .gauge => True
  normalizes_neutral_or_charged := by
    intro theta
    cases theta
    · simp
    · exact Or.inr ⟨ToyEvidenceLeaf.safe, by simp⟩
    · exact Or.inr ⟨ToyEvidenceLeaf.gauge, by simp⟩

theorem toy_public_read_normalizes_neutral_or_charged
    (theta : ToyPublicSymbol) :
    toyPublicReadDiscipline.targetBlind theta ∨
      ∃ leaf,
        toyPublicReadDiscipline.chargedLeaf theta leaf ∧
          (toyPublicReadDiscipline.isSafe leaf ∨
            toyPublicReadDiscipline.isGauge leaf) :=
  public_read_normalizes_neutral_or_charged
    toyPublicReadDiscipline theta

end Mettapedia.Computability.PNP
