import Mettapedia.OSLF.MeTTaIL.Complete.Classes
import Mettapedia.OSLF.MeTTaIL.CollectionLaws

/-!
# Runs under declared collection laws

A language that declares collection laws (`CollectionLaws.declared`) or scope extrusion
(`CollectionLaws.extrusions`) runs on their standard forms: the search modulo equations is
unchanged, and a committed receipt's target is put in standard form before the next search
begins. This is the semantics of normalized execution: a step of the plan's GSLT followed by
the standard form.

- `normalizedSearch_lawful`: runs and publications are the plain search's, so the search
  stays lawful;
- `run_chain`: in chronological order, the states of every run start at the source and each
  reaches the next by a step followed by normalization;
- `done_no_step`: a normal ending leaves no step at all;
- `target_within`: a normalized target keeps exactly the free names of the target.

That normalized execution agrees with rewriting modulo the declared laws is a separate
coherence property of a language.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Normalized

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open Mettapedia.Machines.ResumableSearchRunner (Search Machine Reached)

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-- The declared laws of the plan's language. -/
def laws : List CollectionLaws.Laws := CollectionLaws.declared plan.snapshot.language

/-- The declared scope-extrusion laws of the plan's language. -/
def extrusions : List CollectionLaws.Extrusion := CollectionLaws.extrusions plan.snapshot.language

/-- The standard form of the plan's declared laws. -/
def standard (pattern : Pattern) : Pattern := CollectionLaws.standardForm (laws plan) (extrusions plan) pattern

/-- A step of the plan's GSLT followed by the normal form. -/
def NormalizedStep (source target : Pattern) : Prop :=
  ∃ reached, (GeneralOccurrenceSemantics.gslt plan bound expected).Step source reached ∧
    standard plan reached = target

/-- The search modulo equations, committing normalized targets. -/
def search : Search Pattern (Classes.State plan) GeneralOccurrenceSemantics.Receipt :=
  { Classes.search plan bound expected with
    target := fun receipt => standard plan receipt.target }

theorem search_lawful : (search plan bound expected).Lawful where
  resume_run := (Classes.search_lawful plan bound expected).resume_run
  publication_prefix := (Classes.search_lawful plan bound expected).publication_prefix
  sound := (Classes.search_lawful plan bound expected).sound

/-- **Every normalized run is a chain of normalized steps.** -/
theorem run_chain (source : Pattern) (ticks quantum : Nat) :
    let machine := Machine.advance (search plan bound expected) ticks quantum
      (Machine.begin (search plan bound expected) source)
    machine.states.reverse.head? = some source ∧
      machine.states.reverse.IsChain (NormalizedStep plan bound expected) :=
  Mettapedia.Machines.ResumableSearchRunner.run_chain (search_lawful plan bound expected)
    (fun valid => ⟨_, GeneralOccurrenceSemantics.Receipt.semantic_step plan bound expected valid, rfl⟩)
    source ticks quantum

/-- **A normal ending is exact**: a reached machine that is done has no step at its state. -/
theorem done_no_step (checked : Predecessors.equationsChecked plan = true)
    {machine : Machine Pattern (Classes.State plan) GeneralOccurrenceSemantics.Receipt}
    (reached : Reached (search plan bound expected) machine) (done : machine.phase = .done) :
    ∀ target, ¬ (GeneralOccurrenceSemantics.gslt plan bound expected).Step machine.state target :=
  Mettapedia.Machines.ResumableSearchRunner.done_no_step (S := search plan bound expected)
    (fun state work complete published => Classes.no_step_of_complete plan bound expected checked state work
      complete published)
    reached done

/-- A standard form keeps exactly the pattern's free names, so it stays in any footprint. -/
theorem standard_within (pattern : Pattern) (footprint : List String)
    (inside : ∀ name ∈ pattern.freeFvarNames, name ∈ footprint) :
    ∀ name ∈ (standard plan pattern).freeFvarNames, name ∈ footprint :=
  fun name member => inside name
    ((CollectionLaws.standardForm_freeFvarNames (laws plan) (extrusions plan) pattern name).mp member)

/-- A target in standard form keeps exactly the target's free names, so it stays in any footprint. -/
theorem target_within (receipt : GeneralOccurrenceSemantics.Receipt) (footprint : List String)
    (inside : ∀ name ∈ receipt.target.freeFvarNames, name ∈ footprint) :
    ∀ name ∈ ((search plan bound expected).target receipt).freeFvarNames, name ∈ footprint :=
  fun name member => inside name
    ((CollectionLaws.standardForm_freeFvarNames (laws plan) (extrusions plan) receipt.target name).mp member)

theorem standard_lawFree (free : laws plan = [] ∧ extrusions plan = []) (pattern : Pattern) :
    standard plan pattern = pattern := by
  unfold standard
  rw [free.1, free.2, CollectionLaws.standardForm_nil]

/-- **A language that declares no laws runs as before**: its normalized search is the search
modulo equations. -/
theorem search_lawFree (free : laws plan = [] ∧ extrusions plan = []) :
    search plan bound expected = Classes.search plan bound expected := by
  have identity : (fun receipt : GeneralOccurrenceSemantics.Receipt => standard plan receipt.target) =
      GeneralOccurrenceSemantics.Receipt.target := by
    funext receipt
    exact standard_lawFree plan free receipt.target
  simp only [search, identity]
  rfl

/-- Without declared laws a normalized step is a step. -/
theorem normalizedStep_lawFree (free : laws plan = [] ∧ extrusions plan = []) (source target : Pattern) :
    NormalizedStep plan bound expected source target ↔
      (GeneralOccurrenceSemantics.gslt plan bound expected).Step source target := by
  constructor
  · rintro ⟨reached, step, rfl⟩
    exact (congrArg (fun next : Pattern => (GeneralOccurrenceSemantics.gslt plan bound expected).Step source next)
      (standard_lawFree plan free reached)).mpr step
  · intro step
    exact ⟨target, step, standard_lawFree plan free target⟩

end Mettapedia.OSLF.MeTTaIL.Complete.Normalized
