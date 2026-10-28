import Mathlib.Tactic
import Mettapedia.Computability.PNP.NoThreadingLemma

/-!
# Coarse-projection obstruction for the PNP steelman

This file records the finite obstruction to repairing success-domination by
conditioning only on the coarse `(z, a_i)` statistic.  The checked content is:

* the coarse statistic is invariant under a `b ↦ b xor a` flip while the full
  `(z, a_i, b)` statistic need not be;
* on any neutral finite interface, local domination is exactly the statement
  that the external decoder cannot beat the half bound;
* a two-point model shows domination fails for a decoder that reads `b`;
* neutrality and sufficiency are inconsistent for the coarse statistic.

The final ensemble-level statement keeps the two open inputs explicit:
`EnsembleCoarseNeutral` and `StarSWImpliesSeparation`.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-! ## Coarse/full interfaces and the flip -/

/-- Boolean addition by the local row bit `a`: if `a` is active, toggle `b`. -/
def toggleBy (b a : Bool) : Bool :=
  if a then !b else b

/-- Full statistic `(z, a_i, b)`. -/
def uFull {Phi Z : Type*} (z : Phi -> Z) (a b : Phi -> Bool) :
    Phi -> (Z × Bool) × Bool :=
  fun phi => ((z phi, a phi), b phi)

/-- Coarse statistic `(z, a_i)`, dropping the right-hand side `b`. -/
def uCoarse {Phi Z : Type*} (z : Phi -> Z) (a : Phi -> Bool) :
    Phi -> Z × Bool :=
  fun phi => (z phi, a phi)

/--
Finite interface for a switch map that preserves `(z, a_i)` and toggles `b`
when `a_i = true`.
-/
structure CoarseFlipInterface (Phi Z : Type*) where
  z : Phi -> Z
  a : Phi -> Bool
  b : Phi -> Bool
  T : Phi -> Phi
  T_involutive : Function.Involutive T
  z_T : ∀ phi : Phi, z (T phi) = z phi
  a_T : ∀ phi : Phi, a (T phi) = a phi
  b_T : ∀ phi : Phi, b (T phi) = toggleBy (b phi) (a phi)
  togglePoint : Phi
  togglePoint_active : a togglePoint = true

def CoarseFlipInterface.coarse {Phi Z : Type*}
    (I : CoarseFlipInterface Phi Z) : Phi -> Z × Bool :=
  uCoarse I.z I.a

def CoarseFlipInterface.full {Phi Z : Type*}
    (I : CoarseFlipInterface Phi Z) : Phi -> (Z × Bool) × Bool :=
  uFull I.z I.a I.b

/-- The coarse statistic is invariant under the switch map. -/
theorem uCoarse_T_invariant {Phi Z : Type*}
    (I : CoarseFlipInterface Phi Z) (phi : Phi) :
    I.coarse (I.T phi) = I.coarse phi := by
  simp [CoarseFlipInterface.coarse, uCoarse, I.z_T phi, I.a_T phi]

/-- Function-level version of coarse invariance. -/
theorem uCoarse_comp_T {Phi Z : Type*}
    (I : CoarseFlipInterface Phi Z) :
    I.coarse ∘ I.T = I.coarse := by
  funext phi
  exact uCoarse_T_invariant I phi

/-- At an active point, the full statistic changes under the switch map. -/
theorem uFull_T_moves_at {Phi Z : Type*}
    (I : CoarseFlipInterface Phi Z) :
    I.full (I.T I.togglePoint) ≠ I.full I.togglePoint := by
  intro hfull
  have hb_same :
      I.b (I.T I.togglePoint) = I.b I.togglePoint :=
    congrArg Prod.snd hfull
  have hb_toggle :
      I.b (I.T I.togglePoint) = !I.b I.togglePoint := by
    simpa [toggleBy, I.togglePoint_active] using I.b_T I.togglePoint
  cases hbit : I.b I.togglePoint
  · simp [hbit] at hb_toggle
    simp [hbit, hb_toggle] at hb_same
  · simp [hbit] at hb_toggle
    simp [hbit, hb_toggle] at hb_same

/-! ## Finite local-success bookkeeping -/

def fiberTrueCount {Phi U : Type*} [Fintype Phi] [DecidableEq U]
    (u : Phi -> U) (x : Phi -> Bool) (v : U) : Nat :=
  Fintype.card (FiberTrue u x v)

def fiberFalseCount {Phi U : Type*} [Fintype Phi] [DecidableEq U]
    (u : Phi -> U) (x : Phi -> Bool) (v : U) : Nat :=
  Fintype.card (FiberFalse u x v)

/-- The half-mass on a neutral interface, counted by true points per fiber. -/
def neutralHalfMass {Phi U : Type*} [Fintype Phi] [Fintype U]
    [DecidableEq U] (u : Phi -> U) (x : Phi -> Bool) : Nat :=
  Finset.univ.sum (fun v : U => fiberTrueCount u x v)

/-- Total finite fiber mass, written through true/false fiber counts. -/
def totalFiberMass {Phi U : Type*} [Fintype Phi] [Fintype U]
    [DecidableEq U] (u : Phi -> U) (x : Phi -> Bool) : Nat :=
  Finset.univ.sum
    (fun v : U => fiberTrueCount u x v + fiberFalseCount u x v)

/-- Correct count for a local predictor `U -> Bool`. -/
def localPredictorCorrectCount {Phi U : Type*} [Fintype Phi]
    [Fintype U] [DecidableEq U] (u : Phi -> U) (x : Phi -> Bool)
    (predict : U -> Bool) : Nat :=
  Finset.univ.sum
    (fun v : U =>
      if predict v then fiberTrueCount u x v else fiberFalseCount u x v)

/-- Best local correct count: choose the majority label independently on each
finite fiber. -/
def bestLocalCorrectCount {Phi U : Type*} [Fintype Phi]
    [Fintype U] [DecidableEq U] (u : Phi -> U) (x : Phi -> Bool) : Nat :=
  Finset.univ.sum
    (fun v : U => max (fiberTrueCount u x v) (fiberFalseCount u x v))

def successRatio (num den : Nat) : Rat :=
  (num : Rat) / (den : Rat)

/-- Success of a concrete local predictor. -/
def localPredictorSuccess {Phi U : Type*} [Fintype Phi]
    [Fintype U] [DecidableEq U] (u : Phi -> U) (x : Phi -> Bool)
    (predict : U -> Bool) : Rat :=
  successRatio (localPredictorCorrectCount u x predict) (totalFiberMass u x)

/-- Best success available to a predictor measurable with respect to `u`. -/
def bestLocalSuccess {Phi U : Type*} [Fintype Phi] [Fintype U]
    [DecidableEq U] (u : Phi -> U) (x : Phi -> Bool) : Rat :=
  successRatio (bestLocalCorrectCount u x) (totalFiberMass u x)

theorem localPredictorCorrectCount_le_bestLocalCorrectCount
    {Phi U : Type*} [Fintype Phi] [Fintype U] [DecidableEq U]
    (u : Phi -> U) (x : Phi -> Bool) (predict : U -> Bool) :
    localPredictorCorrectCount u x predict ≤ bestLocalCorrectCount u x := by
  classical
  unfold localPredictorCorrectCount bestLocalCorrectCount
  apply Finset.sum_le_sum
  intro v hv
  by_cases hp : predict v
  · simp [hp]
  · simp [hp]

theorem bestLocalCorrectCount_eq_halfMass_of_neutral
    {Phi U : Type*} [Fintype Phi] [Fintype U] [DecidableEq U]
    {u : Phi -> U} {x : Phi -> Bool} (hN : Neutral u x) :
    bestLocalCorrectCount u x = neutralHalfMass u x := by
  classical
  unfold bestLocalCorrectCount neutralHalfMass
  apply Finset.sum_congr rfl
  intro v hv
  simp [fiberTrueCount, fiberFalseCount, hN v]

theorem totalFiberMass_eq_two_mul_halfMass_of_neutral
    {Phi U : Type*} [Fintype Phi] [Fintype U] [DecidableEq U]
    {u : Phi -> U} {x : Phi -> Bool} (hN : Neutral u x) :
    totalFiberMass u x = 2 * neutralHalfMass u x := by
  classical
  unfold totalFiberMass neutralHalfMass
  calc
    Finset.univ.sum
        (fun v : U => fiberTrueCount u x v + fiberFalseCount u x v)
        =
      Finset.univ.sum (fun v : U => fiberTrueCount u x v +
        fiberTrueCount u x v) := by
        apply Finset.sum_congr rfl
        intro v hv
        simp [fiberTrueCount, fiberFalseCount, hN v]
    _ = 2 * Finset.univ.sum (fun v : U => fiberTrueCount u x v) := by
      simp [two_mul, Finset.sum_add_distrib]

theorem neutralHalfMass_pos_of_neutral
    {Phi U : Type*} [Fintype Phi] [Nonempty Phi] [Fintype U]
    [DecidableEq U] {u : Phi -> U} {x : Phi -> Bool}
    (hN : Neutral u x) :
    0 < neutralHalfMass u x := by
  classical
  let phi : Phi := Classical.choice ‹Nonempty Phi›
  have hmem : u phi ∈ (Finset.univ : Finset U) := Finset.mem_univ _
  have hterm : 0 < fiberTrueCount u x (u phi) := by
    cases hx : x phi
    · have hfalse : 0 < fiberFalseCount u x (u phi) := by
        apply Fintype.card_pos_iff.mpr
        exact ⟨⟨phi, ⟨rfl, hx⟩⟩⟩
      simpa [fiberTrueCount, fiberFalseCount, hN (u phi)] using hfalse
    · apply Fintype.card_pos_iff.mpr
      exact ⟨⟨phi, ⟨rfl, hx⟩⟩⟩
  exact
    lt_of_lt_of_le hterm
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem)

/-- On a nonempty neutral interface, the best local predictor has success 1/2. -/
theorem bestLocalSuccess_eq_half_of_neutral
    {Phi U : Type*} [Fintype Phi] [Nonempty Phi] [Fintype U]
    [DecidableEq U] {u : Phi -> U} {x : Phi -> Bool}
    (hN : Neutral u x) :
    bestLocalSuccess u x = (1 : Rat) / 2 := by
  classical
  have hpos := neutralHalfMass_pos_of_neutral (u := u) (x := x) hN
  have hn : ((neutralHalfMass u x : Nat) : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  unfold bestLocalSuccess successRatio
  rw [bestLocalCorrectCount_eq_halfMass_of_neutral hN,
    totalFiberMass_eq_two_mul_halfMass_of_neutral hN]
  rw [Nat.cast_mul]
  field_simp [hn]
  norm_num

/-! ## Domination is the SW half-bound on a neutral interface -/

def StarSW {Decoder : Type*} (decoderSuccess : Decoder -> Rat)
    (slack : Rat) : Prop :=
  ∀ dec : Decoder, decoderSuccess dec ≤ (1 : Rat) / 2 + slack

def Dominates {Phi U Decoder : Type*} [Fintype Phi] [Fintype U]
    [DecidableEq U] (u : Phi -> U) (x : Phi -> Bool)
    (decoderSuccess : Decoder -> Rat) (slack : Rat) (dec : Decoder) :
    Prop :=
  decoderSuccess dec ≤ bestLocalSuccess u x + slack

def CoarseDominationAll {Phi U Decoder : Type*} [Fintype Phi]
    [Fintype U] [DecidableEq U] (u : Phi -> U) (x : Phi -> Bool)
    (decoderSuccess : Decoder -> Rat) (slack : Rat) : Prop :=
  ∀ dec : Decoder, Dominates u x decoderSuccess slack dec

theorem dominates_iff_half_bound_of_neutral
    {Phi U Decoder : Type*} [Fintype Phi] [Nonempty Phi] [Fintype U]
    [DecidableEq U] {u : Phi -> U} {x : Phi -> Bool}
    {decoderSuccess : Decoder -> Rat} {slack : Rat} (dec : Decoder)
    (hN : Neutral u x) :
    Dominates u x decoderSuccess slack dec ↔
      decoderSuccess dec ≤ (1 : Rat) / 2 + slack := by
  unfold Dominates
  rw [bestLocalSuccess_eq_half_of_neutral hN]

theorem coarseDominationAll_iff_starSW_of_neutral
    {Phi U Decoder : Type*} [Fintype Phi] [Nonempty Phi] [Fintype U]
    [DecidableEq U] {u : Phi -> U} {x : Phi -> Bool}
    {decoderSuccess : Decoder -> Rat} {slack : Rat}
    (hN : Neutral u x) :
    CoarseDominationAll u x decoderSuccess slack ↔
      StarSW decoderSuccess slack := by
  constructor
  · intro hdom dec
    exact (dominates_iff_half_bound_of_neutral dec hN).mp (hdom dec)
  · intro hSW dec
    exact (dominates_iff_half_bound_of_neutral dec hN).mpr (hSW dec)

/-! ## No-threading instance -/

theorem neutral_not_sufficient
    {Phi U : Type*} [Fintype Phi] [Nonempty Phi] [DecidableEq U]
    {u : Phi -> U} {x : Phi -> Bool}
    (hN : Neutral u x) :
    ¬ Sufficient u x := by
  intro hS
  exact noThreading_absurd_at hN hS (Classical.choice ‹Nonempty Phi›)

/-! ## Concrete two-point counterexample -/

def coarseProjectionToyZ (_phi : Bool) : Unit :=
  ()

def coarseProjectionToyA (_phi : Bool) : Bool :=
  true

def coarseProjectionToyB (phi : Bool) : Bool :=
  phi

def coarseProjectionToyT (phi : Bool) : Bool :=
  !phi

def coarseProjectionToyUCoarse : Bool -> Unit × Bool :=
  uCoarse coarseProjectionToyZ coarseProjectionToyA

def coarseProjectionToyUFull : Bool -> (Unit × Bool) × Bool :=
  uFull coarseProjectionToyZ coarseProjectionToyA coarseProjectionToyB

def coarseProjectionToyWitness : Bool -> Bool :=
  coarseProjectionToyB

def coarseProjectionToyInterface : CoarseFlipInterface Bool Unit where
  z := coarseProjectionToyZ
  a := coarseProjectionToyA
  b := coarseProjectionToyB
  T := coarseProjectionToyT
  T_involutive := by
    intro phi
    cases phi <;> rfl
  z_T := by
    intro phi
    rfl
  a_T := by
    intro phi
    rfl
  b_T := by
    intro phi
    cases phi <;> rfl
  togglePoint := false
  togglePoint_active := rfl

theorem coarseProjectionToy_coarse_invariant :
    coarseProjectionToyInterface.coarse ∘ coarseProjectionToyInterface.T =
      coarseProjectionToyInterface.coarse :=
  uCoarse_comp_T coarseProjectionToyInterface

theorem coarseProjectionToy_full_moves :
    coarseProjectionToyInterface.full
        (coarseProjectionToyInterface.T
          coarseProjectionToyInterface.togglePoint) ≠
      coarseProjectionToyInterface.full
        coarseProjectionToyInterface.togglePoint :=
  uFull_T_moves_at coarseProjectionToyInterface

theorem coarseProjectionToy_neutral :
    Neutral coarseProjectionToyUCoarse coarseProjectionToyWitness := by
  intro v
  rcases v with ⟨unitValue, bit⟩
  cases unitValue
  cases bit <;>
    simp [coarseProjectionToyUCoarse, coarseProjectionToyWitness,
      coarseProjectionToyB, uCoarse, coarseProjectionToyZ,
      coarseProjectionToyA, FiberTrue, FiberFalse]

/-- A full decoder that reads `b`. -/
def coarseProjectionToyDecoder : Bool -> Bool :=
  coarseProjectionToyB

def globalDecoderSuccess {Phi : Type*} [Fintype Phi]
    (decoder : Phi -> Bool) (x : Phi -> Bool) : Rat :=
  (Fintype.card {phi : Phi // decoder phi = x phi} : Rat) /
    (Fintype.card Phi : Rat)

theorem coarseProjectionToy_decoderSuccess_eq_one :
    globalDecoderSuccess coarseProjectionToyDecoder
      coarseProjectionToyWitness = 1 := by
  norm_num [globalDecoderSuccess, coarseProjectionToyDecoder,
    coarseProjectionToyWitness, coarseProjectionToyB]

theorem coarseProjectionToy_bestLocalSuccess_eq_half :
    bestLocalSuccess coarseProjectionToyUCoarse coarseProjectionToyWitness =
      (1 : Rat) / 2 :=
  bestLocalSuccess_eq_half_of_neutral coarseProjectionToy_neutral

/--
The concrete failure: with zero slack, domination would read `1 ≤ 1/2` for the
decoder that reads `b`.
-/
theorem coarseProjectionToy_not_dominates :
    ¬ Dominates coarseProjectionToyUCoarse coarseProjectionToyWitness
      (fun dec : Bool -> Bool =>
        globalDecoderSuccess dec coarseProjectionToyWitness)
      0 coarseProjectionToyDecoder := by
  intro hdom
  unfold Dominates at hdom
  change globalDecoderSuccess coarseProjectionToyDecoder
      coarseProjectionToyWitness ≤
    bestLocalSuccess coarseProjectionToyUCoarse coarseProjectionToyWitness + 0
      at hdom
  rw [coarseProjectionToy_decoderSuccess_eq_one,
    coarseProjectionToy_bestLocalSuccess_eq_half] at hdom
  norm_num at hdom

theorem coarseProjectionToy_neutral_not_sufficient
    (hN : Neutral coarseProjectionToyUCoarse coarseProjectionToyWitness) :
    ¬ Sufficient coarseProjectionToyUCoarse coarseProjectionToyWitness :=
  neutral_not_sufficient hN

theorem coarseProjectionToy_not_sufficient :
    ¬ Sufficient coarseProjectionToyUCoarse coarseProjectionToyWitness :=
  coarseProjectionToy_neutral_not_sufficient coarseProjectionToy_neutral

/-! ## Ensemble-level conditional with explicit open inputs -/

/--
The honest conditional conclusion.  If the intended ensemble really is neutral
after projecting to `(z, a_i)`, then coarse-domination is exactly the SW
half-bound; if the separate SW-to-separation chain is supplied, the domination
statement implies the abstract endpoint.  Both inputs remain hypotheses.
-/
theorem coarseProjectionRepair_obstruction_conditional
    {Phi U Decoder : Type*} [Fintype Phi] [Nonempty Phi] [Fintype U]
    [DecidableEq U] {u : Phi -> U} {x : Phi -> Bool}
    {decoderSuccess : Decoder -> Rat} {slack : Rat}
    {pNeNPClaim : Prop}
    (EnsembleCoarseNeutral : Neutral u x)
    (StarSWImpliesSeparation :
      StarSW decoderSuccess slack -> pNeNPClaim) :
    (CoarseDominationAll u x decoderSuccess slack ↔
        StarSW decoderSuccess slack) ∧
      (CoarseDominationAll u x decoderSuccess slack -> pNeNPClaim) := by
  have hiff :=
    coarseDominationAll_iff_starSW_of_neutral
      (u := u) (x := x) (decoderSuccess := decoderSuccess)
      (slack := slack) EnsembleCoarseNeutral
  exact ⟨hiff, fun hdom => StarSWImpliesSeparation (hiff.mp hdom)⟩

end Mettapedia.Computability.PNP
