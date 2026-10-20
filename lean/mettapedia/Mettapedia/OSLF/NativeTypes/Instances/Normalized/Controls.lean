import Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend
import Mettapedia.OSLF.NativeTypes.Decision.Machine

/-!
# Finite quotient-native backend controls

The raw machine has one firing source and two distinct physical origins for
its transition. A declared alias adds another source presentation. Its
normalizer retains firing coverage. The negative machine has the opposite
firing source: it has the same equality normalizer, but normalization hides
its only step. These finite semantic controls do not claim admission through
the authored pattern-language compiler.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Normalized.Controls

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Complete.Coherence
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Decision.Scheduling (Stream)

inductive Term where
  | a
  | b
  | done
  deriving DecidableEq, Repr

def equation (left right : Term) : Prop := left = .b ∧ right = .a

def normal : Term → Term
  | .b => .a
  | other => other

theorem normalizer : Normalizer equation normal where
  sound term := by
    cases term with
    | a => exact .refl _
    | b => exact .rel _ _ ⟨rfl, rfl⟩
    | done => exact .refl _
  canonical left right move := by
    rcases move with ⟨rfl, rfl⟩
    rfl

theorem equation_nonempty : ∃ left right, equation left right :=
  ⟨.b, .a, rfl, rfl⟩

theorem normalization_changes_source : normal .b ≠ .b := by decide

def raw : GSLT where
  Term := Term
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := source = .a ∧ target = .done
  rewrites_resp_left := by
    intro source same target related step
    cases related
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target same step related
    cases related
    exact step

def rawAdmitted (source : Term) : Prop := source ≠ .b

theorem raw_admitted_normal {source : Term} (_admitted : rawAdmitted source) :
    rawAdmitted (normal source) := by
  cases source <;> simp [rawAdmitted, normal]

theorem every_normal_admitted (source : Term) : rawAdmitted (normal source) := by
  cases source <;> simp [rawAdmitted, normal]

theorem raw_step_nonempty : raw.Step .a .done := ⟨rfl, rfl⟩

theorem normalizes_step {source target : raw.Term} (step : raw.Step source target) :
    ∃ next, raw.Step (normal source) next ∧ Relation.EqvGen equation target next := by
  rcases step with ⟨rfl, rfl⟩
  exact ⟨.done, ⟨rfl, rfl⟩, .refl _⟩

def frontier (budget : Nat) (source : Term) : List Bool :=
  if budget = 0 then [] else if source = .a then [false, true] else []

def closed (budget : Nat) (_source : Term) : Bool := budget != 0

theorem frontier_source {budget : Nat} {source : Term} {origin : Bool}
    (listed : origin ∈ frontier budget source) : source = .a := by
  unfold frontier at listed
  split at listed
  · simp at listed
  · split at listed
    · assumption
    · simp at listed

def rawBackend : Backend raw rawAdmitted where
  Receipt _ := Bool
  target _ _ := .done
  frontier := frontier
  closed := closed
  sound _ _ _ listed := ⟨frontier_source listed, rfl⟩
  coverage budget source finished target step := by
    rcases step with ⟨rfl, rfl⟩
    have nonzero : budget ≠ 0 := by simpa [closed] using finished
    exact ⟨false, by simp [frontier, nonzero], rfl⟩
  target_admitted _ _ _ _ _ := by change Term.done ≠ Term.b; decide
  completionBudget _ := 1
  complete_at _ _ := rfl
  frontier_stable source budget enough := by
    have nonzero : budget ≠ 0 := by omega
    simp [frontier, nonzero]
  closed_stable _ budget enough := by
    have nonzero : budget ≠ 0 := by omega
    simp [closed, nonzero]

def tasks (source : Term) : Stream Bool :=
  .pause fun _ => if source = .a then
    .yield false (fun _ => .yield true (fun _ => .done))
  else .done

theorem tasks_flatten (source : Term) :
    (tasks source).flatten = frontier 1 source := by
  by_cases fires : source = .a <;> simp [tasks, frontier, fires, Stream.flatten]

def rawCursor : Mettapedia.OSLF.NativeTypes.Decision.Machine.CursorBackend raw rawAdmitted where
  Receipt _ := Bool
  target _ _ := .done
  tasks := tasks
  sound source _ listed := by
    cases source <;> simp_all [tasks, Stream.flatten, GSLT.Step, raw]
  coverage source _ target step := by
    rcases step with ⟨rfl, rfl⟩
    exact ⟨false, by simp [tasks, Stream.flatten], rfl⟩
  target_admitted _ _ _ _ := by change Term.done ≠ Term.b; decide

def isDone (source : Term) : Bool := source == .done

theorem isDone_invariant {first second : Term}
    (related : Relation.EqvGen equation first second) :
    isDone first = isDone second := by
  have same := normalizer.eqvGen_eq related
  cases first <;> cases second <;> simp_all [normal, isDone]

def badRaw : GSLT where
  Term := Term
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := source = .b ∧ target = .done
  rewrites_resp_left := by
    intro source same target related step
    cases related
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target same step related
    cases related
    exact step

theorem normalization_can_hide_firing :
    ¬ (∀ {source target : badRaw.Term}, badRaw.Step source target →
      ∃ next, badRaw.Step (normal source) next ∧ Relation.EqvGen equation target next) := by
  intro preserves
  obtain ⟨next, fires, _⟩ := preserves (source := .b) (target := .done) ⟨rfl, rfl⟩
  have impossible : Term.a = Term.b := fires.1
  cases impossible

def literalHeadB (source : Term) : Bool := source == .b

theorem literal_observation_not_invariant :
    ¬ (∀ first second, Relation.EqvGen equation first second →
      literalHeadB first = literalHeadB second) := by
  intro invariant
  have impossible := invariant .b .a (.rel _ _ ⟨rfl, rfl⟩)
  contradiction

theorem certificate :
    Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.Certificate raw equation normal where
  normalizer := normalizer
  raw_equations related := by cases related; exact .refl _
  normalize_step := normalizes_step

abbrev model := Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.theory raw equation

def liftedBackend :=
  Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.backend certificate
    (fun _ accepted => raw_admitted_normal accepted) rawBackend

def liftedCursor :=
  Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.cursorBackend certificate
    (fun _ accepted => raw_admitted_normal accepted) rawCursor

def terminalTests (_leaf : Unit) :=
  Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.test
    (accepted := rawAdmitted) certificate isDone

def terminalLeaves (_leaf : Unit) :=
  Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.leafBackend
    (accepted := rawAdmitted) certificate isDone

def terminalSuccessor : Formula Unit := .possibility (.atom ())
def everySuccessorTerminal : Formula Unit := .outgoingUniversal (.atom ())

def answer (formula : Formula Unit) (source : Term) (budget : Nat) : Option Bool :=
  (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.raw
    liftedBackend terminalTests budget formula source).answer

def run (formula : Formula Unit) (source : Term) (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Decision.Machine.run liftedCursor terminalLeaves
    formula source (every_normal_admitted source) budget

def retainedOrigins (formula : Formula Unit) (source : Term) (budget : Nat) : List Bool :=
  ((run formula source budget).observations.filterMap
    Mettapedia.OSLF.NativeTypes.Decision.Machine.Evidence.operational?).map
      (fun observation => observation.receipt)

theorem aliased_native_member :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF model).satisfies
      .b (nativeType terminalTests terminalSuccessor).pred :=
  Outcome.positive
    (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.raw
      liftedBackend terminalTests 2 terminalSuccessor .b) (by decide)

theorem terminal_native_nonmember :
    ¬ (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF model).satisfies
      .done (nativeType terminalTests terminalSuccessor).pred :=
  Outcome.negative
    (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.raw
      liftedBackend terminalTests 2 terminalSuccessor .done) (by decide)

theorem raw_alias_has_no_step : ¬ raw.Step .b .done := by
  intro impossible
  have mismatch : Term.b = Term.a := impossible.1
  cases mismatch

theorem quotient_alias_has_step : model.Step .b .done :=
  certificate.step_of_raw (source := .b) raw_step_nonempty

theorem both_origins_retained : liftedBackend.frontier 1 .b = [false, true] := rfl

theorem cursor_both_origins_retained : (liftedCursor.tasks .b).flatten = [false, true] := rfl

theorem absent_firing_certificate_rejected :
    ¬ Mettapedia.OSLF.NativeTypes.Decision.NormalizedBackend.Certificate badRaw equation normal := by
  intro candidate
  exact normalization_can_hide_firing candidate.normalize_step

theorem resumed_matches_uninterrupted :
    Mettapedia.OSLF.NativeTypes.Decision.Machine.resume 124
      (run everySuccessorTerminal .b 4) = run everySuccessorTerminal .b 128 :=
  (Mettapedia.OSLF.NativeTypes.Decision.Machine.exact_run_resume liftedCursor terminalLeaves
    everySuccessorTerminal .b (every_normal_admitted .b) 4 124).symm

#guard frontier 0 .a = []
#guard frontier 1 .a = [false, true]
#guard frontier 1 .b = []
#guard normal .b = .a
#guard isDone .done
#guard !isDone .b
#guard literalHeadB .b != literalHeadB .a
#guard answer terminalSuccessor .b 0 = none
#guard answer terminalSuccessor .b 1 = none
#guard answer terminalSuccessor .b 2 = some true
#guard answer everySuccessorTerminal .b 2 = some true
#guard answer terminalSuccessor .done 2 = some false
#guard answer everySuccessorTerminal .done 2 = some true
#guard answer (.outgoingUniversal (.neg (.atom ()))) .b 3 = some false
#guard (run terminalSuccessor .b 0).outcome.answer = none
#guard (run terminalSuccessor .b 128).outcome.answer = some true
#guard (run everySuccessorTerminal .b 128).outcome.answer = some true
#guard (run terminalSuccessor .done 128).outcome.answer = some false
#guard retainedOrigins everySuccessorTerminal .b 128 = [false, true]
#guard (liftedCursor.tasks .b).workBound = 4
#guard liftedBackend.closed 0 .b = false
#guard liftedBackend.closed 1 .b = true

end Mettapedia.OSLF.NativeTypes.Instances.Normalized.Controls
