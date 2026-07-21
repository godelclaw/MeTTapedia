import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitSignature
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartData

/-!
# Fixed-width data interface for the positive eight-field orbit chart

The generated payload contains a forward trace permutation, its independently
stored inverse, and eight oriented-plane colors.  This file defines the
validity predicate and its standard decoders without assuming the payload is
valid.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitChartCore

open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16TraceOrbitSignature
open HypercubicDimension16TraceOrbitChartData
open SU2LatticeFDCensusNoGo

abbrev PositiveRepresentativeIndex := Fin positiveRepresentativeCount

def positiveRepresentativeCode (index : PositiveRepresentativeIndex) :
    Array Nat :=
  (positiveRepresentativeCode? index.1).getD #[]

def encodedTraceForward (code : Array Nat) (field : Fin 8) : Fin 8 :=
  Fin.ofNat 8 (code.getD field.1 0)

def encodedTraceBackward (code : Array Nat) (field : Fin 8) : Fin 8 :=
  Fin.ofNat 8 (code.getD (8 + field.1) 0)

def encodedPlane (code : Array Nat) (field : Fin 8) : OrientedPlane :=
  Fin.ofNat 6 (code.getD (16 + field.1) 0)

/-- Independent validity conditions for one fixed-width labeled entry. -/
abbrev EncodedRepresentativeValid (code : Array Nat) : Prop :=
  code.size = encodedRepresentativeWidth ∧
    (∀ field : Fin 8, code.getD field.1 0 < 8) ∧
    (∀ field : Fin 8, code.getD (8 + field.1) 0 < 8) ∧
    (∀ field : Fin 8, code.getD (16 + field.1) 0 < 6) ∧
    (∀ field : Fin 8,
      encodedTraceBackward code (encodedTraceForward code field) = field) ∧
    (∀ field : Fin 8,
      encodedTraceForward code (encodedTraceBackward code field) = field)

end HypercubicDimension16TraceOrbitChartCore
end YangMills
end QuantumTheory
end Mettapedia
