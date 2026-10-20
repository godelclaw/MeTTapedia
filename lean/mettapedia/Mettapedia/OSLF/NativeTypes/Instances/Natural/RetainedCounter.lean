import Mettapedia.OSLF.NativeTypes.Instances.Natural.Provider

/-!
# Recurrence of the counter on retained integer values

Edges are successful calls of the existing retained provider. Decoding only
defines the observation: it is not used to execute an edge. Sound arithmetic
preserves paths. Lifting the finite parity verdict to an infinite execution
additionally requires availability on every admitted retained value. A fault
is not an edge and cannot be hidden by mathematical totality of successor.

This is a provider contract, not a proof that a finite-memory native machine
will run forever. No incoming coverage or scheduler fairness is inferred.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Natural.RetainedCounter

open Mettapedia.GSLT.LanguageDef
open IntegerRepresentationExternalCall
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Semantics.BuchiTransport
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Executable
open Reference.Core (Outcome)

variable {Storage Fault : Type*}

def Value (decode : Storage → Int) := {value : Retained.Value Storage // 0 ≤ resultInteger decode value}

def number (decode : Storage → Int) (value : Value decode) : Nat :=
  (resultInteger decode value.val).toNat

def span (encode : Int → Storage) (decode : Storage → Int) (provider : Provider Storage Fault) :
    ReductionSpan (Value decode) where
  Edge := {pair : Value decode × Value decode //
    Retained.add encode provider pair.1.val (.inl 1) = .ok pair.2.val}
  source edge := edge.val.1
  target edge := edge.val.2

theorem step_number (encode : Int → Storage) (decode : Storage → Int)
    (roundtrip : Function.LeftInverse decode encode) (provider : Provider Storage Fault)
    (sound : SuccessfulSound decode provider) (edge : (span encode decode provider).Edge) :
    number decode edge.val.2 = number decode edge.val.1 + 1 := by
  have correct := Retained.add_sound encode decode roundtrip provider sound
    edge.val.1.val (.inl 1) edge.val.2.val edge.property
  have one : resultInteger decode (.inl (1 : Int64)) = 1 := rfl
  rw [one] at correct
  have nonneg := edge.val.1.property
  unfold number
  rw [correct]
  omega

def observation (encode : Int → Storage) (decode : Storage → Int)
    (roundtrip : Function.LeftInverse decode encode) (provider : Provider Storage Fault)
    (sound : SuccessfulSound decode provider) : SpanMap (span encode decode provider) Counter.counter where
  states := number decode
  events edge := number decode edge.val.1
  source_comm _ := rfl
  target_comm edge := (step_number encode decode roundtrip provider sound edge).symm

/-- Availability is about retained operands, including metadata held by their
provider. Availability on fresh encodings alone is insufficient. -/
def Available (encode : Int → Storage) (decode : Storage → Int) (provider : Provider Storage Fault) : Prop :=
  ∀ value : Value decode, Retained.fast? value.val (.inl 1) = none →
    ∃ result, provider .add (Retained.stored encode value.val) (Retained.stored encode (.inl 1)) = .ok result

theorem outgoing_coverage (encode : Int → Storage) (decode : Storage → Int)
    (roundtrip : Function.LeftInverse decode encode) (provider : Provider Storage Fault)
    (sound : SuccessfulSound decode provider) (available : Available encode decode provider) :
    (observation encode decode roundtrip provider sound).SourceLifts := by
  intro value event starts
  obtain ⟨result, returned⟩ := Retained.add_available encode provider value.val (.inl 1) (available value)
  have correct := Retained.add_sound encode decode roundtrip provider sound value.val (.inl 1) result returned
  have one : resultInteger decode (.inl (1 : Int64)) = 1 := rfl
  rw [one] at correct
  have nonneg : 0 ≤ resultInteger decode result := by rw [correct]; have := value.property; omega
  let next : Value decode := ⟨result, nonneg⟩
  let edge : (span encode decode provider).Edge := ⟨(value, next), returned⟩
  refine ⟨edge, rfl, ?_⟩
  change event = number decode value at starts
  change number decode next = Counter.counter.target event
  rw [starts]
  exact step_number encode decode roundtrip provider sound edge

def accepting (decode : Storage → Int) (phases : Finset (Fin 2)) : Set (Value decode) :=
  {value | Counter.phase (number decode value) ∈ phases}

/-- The finite public query and actual provider paths agree when successful
successor service is available throughout the retained natural carrier. -/
theorem check_buchi_iff (encode : Int → Storage) (decode : Storage → Int)
    (roundtrip : Function.LeftInverse decode encode) (provider : Provider Storage Fault)
    (sound : SuccessfulSound decode provider) (available : Available encode decode provider)
    (phases : Finset (Fin 2)) (budget : Nat) (value : Value decode)
    (enough : FiniteMuCalculus.requiredBudget (State := Fin 2)
      (Formula.buchi Traversal.future) ≤ budget) :
    (Finite.check Counter.table (Formula.buchi .future) (fun _ => phases)
      budget (Counter.phase (number decode value))).map Outcome.answer = some (some true) ↔
    BuchiPath (transitionSystem (span encode decode provider)) .future (accepting decode phases) value := by
  exact (Finite.check_buchi_iff Counter.table phases budget _ enough).trans
    ((path_pullback Counter.observation Counter.outgoing_coverage (↑phases : Set (Fin 2)) _).trans
      (path_pullback (observation encode decode roundtrip provider sound)
        (outgoing_coverage encode decode roundtrip provider sound available)
        (Counter.observation.states ⁻¹' (↑phases : Set (Fin 2))) value))

/-- This direction needs soundness only: a successful infinite provider path
has the claimed arithmetic observations, even for a partial provider. -/
theorem path_preserves_counter (encode : Int → Storage) (decode : Storage → Int)
    (roundtrip : Function.LeftInverse decode encode) (provider : Provider Storage Fault)
    (sound : SuccessfulSound decode provider) (phases : Finset (Fin 2)) (value : Value decode)
    (path : BuchiPath (transitionSystem (span encode decode provider)) .future (accepting decode phases) value) :
    BuchiPath (transitionSystem Counter.counter) .future
      (Counter.observation.states ⁻¹' (↑phases : Set (Fin 2))) (number decode value) :=
  path_preserved (observation encode decode roundtrip provider sound) _ value path

/-- The admitted provider and the original authored counter have the same
recurrence observations, through the single public finite query. -/
theorem authored_buchi_iff (encode : Int → Storage) (decode : Storage → Int)
    (roundtrip : Function.LeftInverse decode encode) (provider : Provider Storage Fault)
    (sound : SuccessfulSound decode provider) (available : Available encode decode provider)
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator)
    (phases : Finset (Fin 2)) (value : Value decode) :
    BuchiPath (transitionSystem (span encode decode provider)) .future (accepting decode phases) value ↔
      BuchiPath (transitionSystem (gsltSpan (Authored.theory base))) .future
        (Authored.accepting phases) (Examples.NativeNaturalCounter.counter (number decode value)) :=
  (check_buchi_iff encode decode roundtrip provider sound available phases 1000 value
    (by decide +kernel)).symm.trans
      (Authored.check_buchi_iff base phases 1000 (number decode value) (by decide +kernel))

#print axioms check_buchi_iff

end Mettapedia.OSLF.NativeTypes.Instances.Natural.RetainedCounter
