import Mathlib.Tactic

/-!
# PNP v13 finite evidence spine

This module records the finite rational-probability part of the v13 conditional
architecture.  It deliberately avoids measure theory: all probabilities are
finite sums of rational weights over a `Fintype`.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u v w x y

/-- A finite rational probability law. -/
structure FiniteRationalLaw (Omega : Type u) [Fintype Omega] where
  weight : Omega -> Rat
  nonnegative : ∀ omega, 0 ≤ weight omega
  total_weight : Finset.univ.sum weight = 1

namespace FiniteRationalLaw

variable {Omega : Type u} [Fintype Omega]

/-- Weight of a decidable finite event. -/
noncomputable def eventWeight (mu : FiniteRationalLaw Omega)
    (E : Omega -> Prop) [DecidablePred E] : Rat :=
  Finset.univ.sum (fun omega => if E omega then mu.weight omega else 0)

/-- Conditional probability of `E` inside a Boolean phase. -/
noncomputable def conditionalProb (mu : FiniteRationalLaw Omega)
    (B : Omega -> Bool) (phase : Bool)
    (E : Omega -> Prop) [DecidablePred E] : Rat :=
  mu.eventWeight (fun omega => B omega = phase ∧ E omega) /
    mu.eventWeight (fun omega => B omega = phase)

end FiniteRationalLaw

/-- Boolean observations as rational indicators. -/
def boolRat (b : Bool) : Rat :=
  if b then 1 else 0

/-- Half absolute difference, the normalization used for target gaps. -/
def halfAbsDiff (a b : Rat) : Rat :=
  |a - b| / 2

/-- Target gap for an observer `g` after a finite transcript map `T`. -/
noncomputable def Gap {Omega : Type u} [Fintype Omega]
    (mu : FiniteRationalLaw Omega) (B : Omega -> Bool)
    {Transcript : Type v} (T : Omega -> Transcript)
    (g : Transcript -> Bool) : Rat :=
  halfAbsDiff
    (mu.conditionalProb B true (fun omega => g (T omega) = true))
    (mu.conditionalProb B false (fun omega => g (T omega) = true))

theorem Gap_eq_half_abs_conditional
    {Omega : Type u} [Fintype Omega]
    (mu : FiniteRationalLaw Omega) (B : Omega -> Bool)
    {Transcript : Type v} (T : Omega -> Transcript)
    (g : Transcript -> Bool) :
    Gap mu B T g =
      |mu.conditionalProb B true (fun omega => g (T omega) = true) -
        mu.conditionalProb B false (fun omega => g (T omega) = true)| / 2 := by
  rfl

/-- Coupling mass of the transcript-separation event. -/
noncomputable def couplingSepMass
    {Omega : Type u} {Transcript : Type v} {Pair : Type w}
    [Fintype Pair] [DecidableEq Transcript]
    (T : Omega -> Transcript) (pairWeight : Pair -> Rat)
    (left right : Pair -> Omega) : Rat :=
  Finset.univ.sum
    (fun p => if T (left p) = T (right p) then 0 else pairWeight p)

/-- Legacy static pair surface.  It records weighted opposite endpoints but
does not itself require normalization or exact phase marginals.  The faithful
version below adds those equations; users of this legacy record must supply
`CapturesGap` separately. -/
structure StaticPairwiseCapture
    {Omega : Type u} [Fintype Omega]
    (mu : FiniteRationalLaw Omega) (B : Omega -> Bool)
    {Transcript : Type v} [DecidableEq Transcript]
    (T : Omega -> Transcript) (g : Transcript -> Bool)
    (Pair : Type w) [Fintype Pair] where
  pairWeight : Pair -> Rat
  pairNonnegative : ∀ p, 0 ≤ pairWeight p
  left : Pair -> Omega
  right : Pair -> Omega
  opposite : ∀ p, B (left p) = false ∧ B (right p) = true

namespace StaticPairwiseCapture

variable {Omega : Type u} [Fintype Omega]
variable {mu : FiniteRationalLaw Omega} {B : Omega -> Bool}
variable {Transcript : Type v} [DecidableEq Transcript]
variable {T : Omega -> Transcript} {g : Transcript -> Bool}
variable {Pair : Type w} [Fintype Pair]

noncomputable def sepMass
    (Gamma : StaticPairwiseCapture mu B T g Pair) : Rat :=
  couplingSepMass T Gamma.pairWeight Gamma.left Gamma.right

end StaticPairwiseCapture

/-! ## Faithful Phase-A coupling statement -/

/-- Phase-A compatible coupling with normalization and exact conditioned phase
marginals in the record itself.  Event marginals are stated for every event on
the finite world, matching Appendix D.47(i). -/
structure FaithfulStaticPairwiseCoupling
    {Omega : Type u} [Fintype Omega]
    (mu : FiniteRationalLaw Omega) (B : Omega -> Bool)
    (Pair : Type w) [Fintype Pair] where
  pairWeight : Pair -> Rat
  pairNonnegative : forall p, 0 <= pairWeight p
  normalized : Finset.univ.sum pairWeight = 1
  left : Pair -> Omega
  right : Pair -> Omega
  opposite : forall p, B (left p) = false ∧ B (right p) = true
  left_exact_phase_marginal : forall event : Omega -> Bool,
    Finset.univ.sum (fun p => if event (left p) then pairWeight p else 0) =
      mu.conditionalProb B false (fun omega => event omega = true)
  right_exact_phase_marginal : forall event : Omega -> Bool,
    Finset.univ.sum (fun p => if event (right p) then pairWeight p else 0) =
      mu.conditionalProb B true (fun omega => event omega = true)

namespace StaticPairwiseCapture

variable {Omega : Type u} [Fintype Omega]
variable {mu : FiniteRationalLaw Omega} {B : Omega -> Bool}
variable {Transcript : Type v} [DecidableEq Transcript]
variable {T : Omega -> Transcript} {g : Transcript -> Bool}
variable {Pair : Type w} [Fintype Pair]

/-- Capture inequality for the separation event. -/
def CapturesGap (Gamma : StaticPairwiseCapture mu B T g Pair) : Prop :=
  Gap mu B T g ≤ (1 / 2 : Rat) * Gamma.sepMass

end StaticPairwiseCapture

theorem static_pairwise_capture
    {Omega : Type u} [Fintype Omega]
    {mu : FiniteRationalLaw Omega} {B : Omega -> Bool}
    {Transcript : Type v} [DecidableEq Transcript]
    {T : Omega -> Transcript} {g : Transcript -> Bool}
    {Pair : Type w} [Fintype Pair]
    (Gamma : StaticPairwiseCapture mu B T g Pair)
    (hCapture : Gamma.CapturesGap) :
    Gap mu B T g ≤ (1 / 2 : Rat) * Gamma.sepMass :=
  hCapture

/-- Finite derivative-telescoping certificate for a refinement sequence. -/
structure DerivativeTelescoping (Stage : Type u) (Branch : Type v) where
  stageFinite : Fintype Stage
  branchFinite : Fintype Branch
  finalWeight : Rat
  derivative : Stage -> Branch -> Rat
  derivativeNonnegative : ∀ r h, 0 ≤ derivative r h
  telescopes :
    1 - finalWeight =
      Finset.univ.sum
        (fun r : Stage => Finset.univ.sum (fun h : Branch => derivative r h))

namespace DerivativeTelescoping

variable {Stage : Type u} {Branch : Type v}

noncomputable def derivativeSum (D : DerivativeTelescoping Stage Branch) : Rat :=
  letI := D.stageFinite
  letI := D.branchFinite
  Finset.univ.sum
    (fun r : Stage => Finset.univ.sum (fun h : Branch => D.derivative r h))

theorem derivative_telescoping (D : DerivativeTelescoping Stage Branch) :
    1 - D.finalWeight = D.derivativeSum := by
  unfold derivativeSum
  exact D.telescopes

end DerivativeTelescoping

/-- Faithful named Phase-A target.  The coupling equations are structural;
trace capture and the refinement comparison remain separately visible open
obligations until proved for the real execution/refinement sequence. -/
structure V13FaithfulPhaseACaptureTarget
    {Omega : Type u} [Fintype Omega]
    (mu : FiniteRationalLaw Omega) (B : Omega -> Bool)
    {Transcript : Type v} [DecidableEq Transcript]
    (T : Omega -> Transcript) (observerBit : Transcript -> Bool)
    (Pair : Type w) [Fintype Pair] (Stage : Type x) (Branch : Type y) where
  coupling : FaithfulStaticPairwiseCoupling mu B Pair
  captures_actual_trace :
    Gap mu B T observerBit <=
      (1 / 2 : Rat) *
        couplingSepMass T coupling.pairWeight coupling.left coupling.right
  telescoping : DerivativeTelescoping Stage Branch
  separation_le_derivative_sum :
    couplingSepMass T coupling.pairWeight coupling.left coupling.right <=
      telescoping.derivativeSum

/-- Legacy conditional Phase-A certificate combining assumed capture and
assumed derivative accounting. -/
structure EvidenceSpineBound
    {Omega : Type u} [Fintype Omega]
    (mu : FiniteRationalLaw Omega) (B : Omega -> Bool)
    {Transcript : Type v} [DecidableEq Transcript]
    (T : Omega -> Transcript) (g : Transcript -> Bool)
    (Pair : Type w) [Fintype Pair] (Stage : Type x) (Branch : Type y) where
  capture : StaticPairwiseCapture mu B T g Pair
  capturesGap : capture.CapturesGap
  telescoping : DerivativeTelescoping Stage Branch
  sep_le_derivativeSum :
    capture.sepMass ≤ telescoping.derivativeSum

/-- Conditional certificate eliminator: this theorem chains `capturesGap` and
`sep_le_derivativeSum`; it does not construct a coupling or prove either input. -/
theorem phaseA_gap_le_half_derivative_sum
    {Omega : Type u} [Fintype Omega]
    {mu : FiniteRationalLaw Omega} {B : Omega -> Bool}
    {Transcript : Type v} [DecidableEq Transcript]
    {T : Omega -> Transcript} {g : Transcript -> Bool}
    {Pair : Type w} [Fintype Pair] {Stage : Type x} {Branch : Type y}
    (C : EvidenceSpineBound mu B T g Pair Stage Branch) :
    Gap mu B T g ≤ (1 / 2 : Rat) * C.telescoping.derivativeSum := by
  have hhalf : 0 ≤ (1 / 2 : Rat) := by norm_num
  exact
    le_trans (static_pairwise_capture C.capture C.capturesGap)
      (mul_le_mul_of_nonneg_left C.sep_le_derivativeSum hhalf)

/-! ## Two-point toy instantiation -/

def toyV13Phase (omega : Bool) : Bool :=
  omega

def toyV13Transcript (omega : Bool) : Bool :=
  omega

def toyV13Observer (t : Bool) : Bool :=
  t

def toyV13Law : FiniteRationalLaw Bool where
  weight := fun _ => (1 / 2 : Rat)
  nonnegative := by
    intro omega
    norm_num
  total_weight := by
    norm_num

theorem toyV13_gap_eq_half :
    Gap toyV13Law toyV13Phase toyV13Transcript toyV13Observer =
      (1 / 2 : Rat) := by
  norm_num [Gap, halfAbsDiff, FiniteRationalLaw.conditionalProb,
    FiniteRationalLaw.eventWeight, toyV13Law, toyV13Phase,
    toyV13Transcript, toyV13Observer]

def toyV13StaticCapture :
    StaticPairwiseCapture toyV13Law toyV13Phase
      toyV13Transcript toyV13Observer Unit where
  pairWeight := fun _ => 1
  pairNonnegative := by
    intro p
    norm_num
  left := fun _ => false
  right := fun _ => true
  opposite := by
    intro p
    cases p
    exact ⟨rfl, rfl⟩

theorem toyV13StaticCapture_sepMass :
    toyV13StaticCapture.sepMass = 1 := by
  norm_num [StaticPairwiseCapture.sepMass, couplingSepMass,
    toyV13StaticCapture, toyV13Transcript]

theorem toyV13StaticCapture_capturesGap :
    toyV13StaticCapture.CapturesGap := by
  rw [StaticPairwiseCapture.CapturesGap, toyV13_gap_eq_half,
    toyV13StaticCapture_sepMass]
  norm_num

def toyV13Telescoping :
    DerivativeTelescoping Unit Unit where
  stageFinite := inferInstance
  branchFinite := inferInstance
  finalWeight := 0
  derivative := fun _ _ => 1
  derivativeNonnegative := by
    intro r h
    norm_num
  telescopes := by
    norm_num

def toyV13EvidenceSpineBound :
    EvidenceSpineBound toyV13Law toyV13Phase toyV13Transcript
      toyV13Observer Unit Unit Unit where
  capture := toyV13StaticCapture
  capturesGap := toyV13StaticCapture_capturesGap
  telescoping := toyV13Telescoping
  sep_le_derivativeSum := by
    rw [toyV13StaticCapture_sepMass]
    norm_num [DerivativeTelescoping.derivativeSum, toyV13Telescoping]

theorem toyV13_phaseA_gap_le_half_derivative_sum :
    Gap toyV13Law toyV13Phase toyV13Transcript toyV13Observer ≤
      (1 / 2 : Rat) * toyV13Telescoping.derivativeSum :=
  phaseA_gap_le_half_derivative_sum toyV13EvidenceSpineBound

end Mettapedia.Computability.PNP
