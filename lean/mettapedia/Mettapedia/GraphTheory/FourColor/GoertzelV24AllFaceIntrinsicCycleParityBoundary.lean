import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceEscapeStateCycleResidue
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseOddMonodromy

/-!
# Parity boundary for closed intrinsic reentry cycles

Local singleton-collar monodromies live on state-dependent carriers.  Any
global noncancellation argument must first transport them to one fixed finite
carrier.  This file records the exact consequence available after such a
transport is supplied: the product sign is `(-1)` to the number of reentry
steps.  Hence identification with the canonical closed affine color word can
force only even cycle length.  Two odd permutations can already cancel in two
steps, so local oddness alone is not a closed-orbit contradiction.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u w

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}

namespace GoertzelV24AllFaceIntrinsicCycleParityBoundary

open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24AdjacentPairInsertion.AdjacentPairData.RotationOrderedFusionEscapeColorState
open GoertzelV24AdjacentPairInsertion.AdjacentPairData.CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle.IntrinsicShortTargetEscapeCollar

abbrev State :=
  RotationOrderedFusionEscapeColorState.AdmissibleState
    (graphData := graphData) (minimal := minimal)

abbrev IntrinsicStep :=
  RotationOrderedFusionEscapeColorState.IntrinsicOddSignedReentry
    (graphData := graphData) (minimal := minimal)

/-- The interface a global monodromy argument must provide: every local
intrinsic transport is represented on one fixed finite carrier, and remains
odd there.  The definition deliberately asks for no edge label, since that
label changes when the scalar support orientation is reversed. -/
structure FixedCarrierOddTransport
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (Carrier : Type w) [Fintype Carrier] [DecidableEq Carrier] where
  step : ∀ {source target : State (graphData := graphData) (minimal := minimal)},
    IntrinsicStep (graphData := graphData) (minimal := minimal) source target →
      Equiv.Perm Carrier
  step_sign : ∀ {source target : State (graphData := graphData) (minimal := minimal)}
      (transition :
        IntrinsicStep (graphData := graphData) (minimal := minimal)
          source target),
    Equiv.Perm.sign (step transition) = -1

namespace FixedCarrierOddTransport

variable {Carrier : Type w} [Fintype Carrier] [DecidableEq Carrier]
  (transport : FixedCarrierOddTransport graphData minimal Carrier)

/-- An explicitly counted intrinsic path together with the product of its
fixed-carrier transports.  The total is retained as an index because the
underlying transition proofs live in `Prop`. -/
inductive Word : Nat →
    State (graphData := graphData) (minimal := minimal) →
    State (graphData := graphData) (minimal := minimal) →
    Equiv.Perm Carrier → Prop
  | refl (state) : Word 0 state state 1
  | tail {length source middle target total}
      (path : Word length source middle total)
      (transition :
        IntrinsicStep (graphData := graphData) (minimal := minimal)
          middle target) :
      Word (length + 1) source target
        (transport.step transition * total)

/-- Every explicitly counted intrinsic path has a fixed-carrier transport
word. -/
theorem exists_word_of_exactSteps {length : Nat}
    {source target : State (graphData := graphData) (minimal := minimal)}
    (run : ExactRebaseRelation.ExactSteps
      (IntrinsicStep (graphData := graphData) (minimal := minimal))
      length source target) :
    ∃ total : Equiv.Perm Carrier,
      Word transport length source target total := by
  induction run with
  | refl => exact ⟨1, .refl _⟩
  | tail path transition ih =>
      rcases ih with ⟨total, word⟩
      exact ⟨transport.step transition * total,
        .tail word transition⟩

/-- The only parity information obtained by multiplying local odd
transports is parity of the number of steps. -/
theorem word_sign {length : Nat}
    {source target : State (graphData := graphData) (minimal := minimal)}
    {total : Equiv.Perm Carrier}
    (word : Word transport length source target total) :
    Equiv.Perm.sign total = (-1) ^ length := by
  induction word with
  | refl => simp
  | tail path transition ih =>
      rw [Equiv.Perm.sign_mul, transport.step_sign transition, ih]
      calc
        (-1 : ℤˣ) * (-1) ^ _ = (-1) ^ _ * (-1 : ℤˣ) := mul_comm _ _
        _ = (-1 : ℤˣ) ^ Nat.succ _ := (pow_succ _ _).symm
        _ = (-1 : ℤˣ) ^ (_ + 1) := rfl

/-- Every closed intrinsic residue has a positive explicit length, and any
fixed-carrier odd transport has product sign `(-1)` to that length. -/
theorem exists_positive_exactSteps_product_sign
    {state : State (graphData := graphData) (minimal := minimal)}
    (residue :
      GoertzelV24AllFaceEscapeStateCycleResidue.ClosedIntrinsicResidue
        graphData minimal state) :
    ∃ length : Nat, 0 < length ∧
      ∃ total : Equiv.Perm Carrier,
        Word transport length state state total ∧
          Equiv.Perm.sign total = (-1) ^ length := by
  rcases ExactRebaseRelation.transGen_exists_exactSteps_pos
      residue.intrinsicCycle with ⟨length, hpositive, run⟩
  rcases exists_word_of_exactSteps transport run with ⟨total, word⟩
  exact ⟨length, hpositive, total, word,
    word_sign transport word⟩

/-- If a fixed-carrier geometric product is identified with the canonical
closed affine color transport, the cycle length must be even.  Thus this
identification does not turn local oddness into a contradiction unless an
independent odd-length theorem is also supplied. -/
theorem length_even_of_wordProduct_eq_closedGaugeConjugate
    {length : Nat}
    {state : State (graphData := graphData) (minimal := minimal)}
    {geometricProduct : Equiv.Perm Carrier}
    (geometricWord :
      Word transport length state state geometricProduct)
    {translation :
      RotationOrderedFusionEscapeColorState.ReentryTranslation
        (graphData := graphData) (minimal := minimal)}
    {word : List (Color × ColorNameSymmetry)}
    (gaugeWord :
      RotationOrderedFusionEscapeColorState.ReentryColorGaugeWord
        translation state state word)
    (coordinates : Color ≃ Carrier)
    (identified :
      geometricProduct =
        coordinates.permCongr (colorAffineWordTransfer word)) :
    Even length := by
  have hsign := congrArg Equiv.Perm.sign identified
  rw [word_sign transport geometricWord, Equiv.Perm.sign_permCongr,
    gaugeWord.transfer_sign_eq_one_of_closed] at hsign
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp hsign

end FixedCarrierOddTransport

/-- A two-step algebraic model witnesses the residual cancellation: the
same odd transposition taken twice has identity product.  This is not asserted
to be an ambient reentry cycle; it shows exactly why odd local signs alone do
not rule one out. -/
theorem two_odd_transpositions_can_cancel :
    let swap : Equiv.Perm Bool := Equiv.swap false true
    Equiv.Perm.sign swap = -1 ∧ swap * swap = 1 := by
  dsimp
  constructor
  · exact Equiv.Perm.sign_swap (by decide)
  · simp

end GoertzelV24AllFaceIntrinsicCycleParityBoundary

end

end Mettapedia.GraphTheory.FourColor
