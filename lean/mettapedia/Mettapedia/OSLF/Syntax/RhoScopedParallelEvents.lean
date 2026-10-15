import Mettapedia.OSLF.Syntax.RhoScopedParallelPathReadout

/-!
# Authored scoped rho events as complete root-and-surrounding factorizations

Rules retain their original schema terms and their declared admission.
Complete root instances retain both metavariable assignments and valuations
of rule variables. The independently defined permitted-path event relation
is compared in both directions with adjoining an original process class.
The comparison uses the actual rho source equations at every ambient scope.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedParallelEvents

open _root_.CategoryTheory RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open ScopedEncoding ScopedEquationContexts ScopedEquationEvents
open RhoScopedEquationEventControls RhoScopedParallelPathReadout
open Mettapedia.CategoryTheory.GroundPath

universe u

local instance : Quiver (Scope sig) := bindingFrameQuiver sig

/-- A process-result schema retains the actual sorted source and target terms. -/
structure ProcessRule where
  ruleContext : Ctx schemaSig
  source : Term schemaSig ruleContext Srt.pr
  target : Term schemaSig ruleContext Srt.pr

def ProcessRule.schema (rule : ProcessRule) : UnpositionedRewrite schemaSig where
  ctx := rule.ruleContext
  sort := Srt.pr
  lhs := rule.source
  rhs := rule.target

variable {Index : Type u} (rules : Index → ProcessRule) (admitted : Index → Prop)

abbrev Selected := {index : Index // admitted index}

def schemas : Selected admitted → UnpositionedRewrite schemaSig :=
  fun selected => (rules selected.val).schema

abbrev Root (context : Ctx sig) :=
  (selected : Selected admitted) × ContextualRootEvents.Instance (schemas rules admitted selected) context

abbrev Occurrence (context : Ctx sig) :=
  Event (schemas rules admitted) parallelPermission (context, Srt.pr)

variable {rules admitted}

def Root.source {context : Ctx sig} (root : Root rules admitted context) : Process context :=
  project root.2.source

def Root.target {context : Ctx sig} (root : Root rules admitted context) : Process context :=
  project root.2.target

/-- The original event support is defined before any relative-pushout comparison. -/
def Step {context : Ctx sig} (first second : Process context) : Prop :=
  ∃ occurrence : Occurrence rules admitted context,
    occurrence.sourceClass rhoSourceE = first ∧ occurrence.targetClass rhoSourceE = second

theorem occurrence_factorization {context : Ctx sig}
    (occurrence : Occurrence rules admitted context) :
    ∃ root : Root rules admitted context, ∃ surrounding : Process context,
      occurrence.sourceClass rhoSourceE = join root.source surrounding ∧
      occurrence.targetClass rhoSourceE = join root.target surrounding := by
  rcases occurrence with ⟨index, holeContext, root, path, permitted⟩
  have same := scope_readout path permitted
  have contexts : holeContext = context := congrArg Prod.fst same
  subst holeContext
  obtain ⟨surrounding, reads⟩ := fixed_scope_readout path permitted
  refine ⟨⟨index, root⟩, surrounding, ?_, ?_⟩
  · exact reads (project root.source)
  · exact reads (project root.target)

theorem factorization_occurrence {context : Ctx sig} (root : Root rules admitted context)
    (surrounding : Process context) :
    ∃ occurrence : Occurrence rules admitted context,
      occurrence.sourceClass rhoSourceE = join root.source surrounding ∧
      occurrence.targetClass rhoSourceE = join root.target surrounding := by
  obtain ⟨path, allowed, reads⟩ := every_surrounding_realized surrounding
  refine ⟨⟨root.1, context, root.2, path, allowed⟩, ?_, ?_⟩
  · exact reads (project root.2.source)
  · exact reads (project root.2.target)

/-- Whole-event support is characterized for every original scoped equation class. -/
theorem step_iff_root_surrounding {context : Ctx sig} (first second : Process context) :
    Step (rules := rules) (admitted := admitted) first second ↔
      ∃ root : Root rules admitted context, ∃ surrounding : Process context,
        first = join root.source surrounding ∧ second = join root.target surrounding := by
  constructor
  · rintro ⟨occurrence, sourceRead, targetRead⟩
    obtain ⟨root, surrounding, sourceShape, targetShape⟩ := occurrence_factorization occurrence
    exact ⟨root, surrounding, sourceRead.symm.trans sourceShape, targetRead.symm.trans targetShape⟩
  · rintro ⟨root, surrounding, rfl, rfl⟩
    exact factorization_occurrence root surrounding

theorem step_join {context : Ctx sig} {first second : Process context}
    (step : Step (rules := rules) (admitted := admitted) first second)
    (additional : Process context) :
    Step (rules := rules) (admitted := admitted) (join first additional) (join second additional) := by
  obtain ⟨root, surrounding, sourceRead, targetRead⟩ :=
    (step_iff_root_surrounding first second).mp step
  apply (step_iff_root_surrounding _ _).mpr
  exact ⟨root, join surrounding additional,
    (congrArg (join · additional) sourceRead).trans (RhoScopedParallelPathReadout.join_assoc _ _ _),
    (congrArg (join · additional) targetRead).trans (RhoScopedParallelPathReadout.join_assoc _ _ _)⟩

def Root.map {context destination : Ctx sig} (substitution : Sub sig context destination)
    (root : Root rules admitted context) : Root rules admitted destination :=
  ⟨root.1, root.2.map substitution⟩

theorem Root.source_map {context destination : Ctx sig} (substitution : Sub sig context destination)
    (root : Root rules admitted context) :
    (root.map substitution).source = bindQ substitution root.source :=
  congrArg (fun term : Term sig destination Srt.pr => (project term : Process destination))
    (ContextualRootEvents.Instance.source_map substitution root.2)

theorem Root.target_map {context destination : Ctx sig} (substitution : Sub sig context destination)
    (root : Root rules admitted context) :
    (root.map substitution).target = bindQ substitution root.target :=
  congrArg (fun term : Term sig destination Srt.pr => (project term : Process destination))
    (ContextualRootEvents.Instance.target_map substitution root.2)

theorem Root.map_origin {context destination : Ctx sig} (substitution : Sub sig context destination)
    (root : Root rules admitted context) : (root.map substitution).1 = root.1 := rfl

theorem step_substitution {context destination : Ctx sig}
    (substitution : Sub sig context destination) {first second : Process context}
    (step : Step (rules := rules) (admitted := admitted) first second) :
    Step (rules := rules) (admitted := admitted)
      (bindQ substitution first) (bindQ substitution second) := by
  obtain ⟨occurrence, sourceRead, targetRead⟩ := step
  refine ⟨occurrence.map destination substitution, ?_, ?_⟩
  · exact (Event.sourceClass_map rhoSourceE destination substitution occurrence).trans
      (congrArg (bindQ substitution) sourceRead)
  · exact (Event.targetClass_map rhoSourceE destination substitution occurrence).trans
      (congrArg (bindQ substitution) targetRead)

/-- The source's COMM rule, with its full original continuation term. -/
def communication : ProcessRule where
  ruleContext := comm.ctx
  source := comm.lhs
  target := comm.rhs

/-- The separate source Drop rule is retained as a separate schema. -/
def reflection : ProcessRule where
  ruleContext := dropRule.ctx
  source := dropRule.lhs
  target := dropRule.rhs

theorem communication_schema : communication.schema = comm.unpositioned := rfl

theorem reflection_schema : reflection.schema = dropRule.unpositioned := rfl

inductive SourceRule where
  | communication
  | reflection
  deriving DecidableEq

def sourceRules : SourceRule → ProcessRule
  | .communication => communication
  | .reflection => reflection

def core : SourceRule → Prop
  | .communication => True
  | .reflection => False

def withReflection : SourceRule → Prop := fun _ => True

end Mettapedia.OSLF.Binding.RhoScopedParallelEvents
