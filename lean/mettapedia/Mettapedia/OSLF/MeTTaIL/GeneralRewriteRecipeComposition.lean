import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeExpansion
import Mettapedia.OSLF.Framework.PathTypeSynthesis

/-!
# Retained rewrite-recipe traces and finite-path possibility

The local recipe checks one authored rewrite with equation evidence on both
sides. A trace retains its intermediate states and one such recipe per rewrite.
An unresolved draft supplies no authority. Semantic traces additionally retain
endpoint conversions, including paths with no primitive rewrite at all.

The modal readout is existential finite reachability in the existing path GSLT.
It does not certify all executions, termination, or exhaustive absence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeComposition

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open GeneralRewriteRecipe
open Mettapedia.OSLF.Framework.PathTypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- The literal next state remains in the trace rather than being recovered
by an unrecorded search through possible reducts. -/
structure Link where
  next : Pattern
  step : StepTrace
  deriving Repr

abbrev Trace := List Link

namespace Trace

variable (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)

/-- Independent replay meaning for the exact submitted sequence. -/
inductive Valid : Trace → Pattern → Pattern → Prop where
  | nil (source : Pattern) : Valid [] source source
  | cons {link : Link} {rest : Trace} {source target : Pattern} :
      StepTrace.Valid plan bound type source link.next link.step →
      Valid rest link.next target → Valid (link :: rest) source target

theorem valid_nil_iff (source target : Pattern) :
    Valid plan bound type [] source target ↔ source = target := by
  constructor
  · intro held
    cases held
    rfl
  · rintro rfl
    exact .nil source

theorem valid_cons_iff (link : Link) (rest : Trace) (source target : Pattern) :
    Valid plan bound type (link :: rest) source target ↔
      StepTrace.Valid plan bound type source link.next link.step ∧
        Valid plan bound type rest link.next target := by
  constructor
  · intro held
    cases held with
    | cons head tail => exact ⟨head, tail⟩
  · rintro ⟨head, tail⟩
    exact .cons head tail

/-- Only the supplied local recipe is checked at each explicitly retained
intermediate state. This layer does not enumerate possible source paths. -/
def replay (source : Pattern) : Trace → Option Pattern
  | [] => some source
  | link :: rest =>
      if GeneralRewriteRecipe.check plan bound type source link.next link.step then
        replay link.next rest
      else none

theorem replay_exact (trace : Trace) (source target : Pattern) :
    replay plan bound type source trace = some target ↔
      Valid plan bound type trace source target := by
  induction trace generalizing source with
  | nil => simp only [replay, Option.some.injEq, valid_nil_iff]
  | cons link rest ih =>
      rw [valid_cons_iff]
      cases accepted : GeneralRewriteRecipe.check plan bound type source link.next link.step with
      | false =>
          have refused : ¬ StepTrace.Valid plan bound type source link.next link.step := by
            intro held
            have := (GeneralRewriteRecipe.check_exact plan bound type source link.next link.step).mpr held
            simp only [accepted, Bool.false_eq_true] at this
          simp [replay, accepted, refused]
      | true =>
          have held := (GeneralRewriteRecipe.check_exact plan bound type source link.next link.step).mp accepted
          simpa only [replay, accepted, ↓reduceIte, held, true_and] using ih link.next

def check (source target : Pattern) (trace : Trace) : Bool :=
  decide (replay plan bound type source trace = some target)

theorem check_exact (source target : Pattern) (trace : Trace) :
    check plan bound type source target trace = true ↔
      Valid plan bound type trace source target := by
  simp only [check, decide_eq_true_eq, replay_exact]

theorem wrong_target_refused {source target wrong : Pattern} {trace : Trace}
    (accepted : check plan bound type source target trace = true)
    (different : wrong ≠ target) : check plan bound type source wrong trace = false := by
  have replayed : replay plan bound type source trace = some target := of_decide_eq_true accepted
  simp only [check, replayed, Option.some.injEq]
  exact decide_eq_false (Ne.symm different)

/-- Concatenation checks the same literal joining state on both sides. -/
theorem replay_append (source : Pattern) (front back : Trace) :
    replay plan bound type source (front ++ back) =
      (replay plan bound type source front).bind (fun middle => replay plan bound type middle back) := by
  induction front generalizing source with
  | nil => rfl
  | cons link rest ih =>
      cases accepted : GeneralRewriteRecipe.check plan bound type source link.next link.step <;>
        simp only [List.cons_append, replay, accepted, Bool.false_eq_true, ↓reduceIte,
          Option.bind_none, ih]

theorem valid_append_iff (front back : Trace) (source target : Pattern) :
    Valid plan bound type (front ++ back) source target ↔
      ∃ middle, Valid plan bound type front source middle ∧
        Valid plan bound type back middle target := by
  induction front generalizing source with
  | nil =>
      constructor
      · intro held
        exact ⟨source, .nil source, held⟩
      · rintro ⟨middle, frontValid, backValid⟩
        have same := (valid_nil_iff plan bound type source middle).mp frontValid
        cases same
        exact backValid
  | cons link rest ih =>
      simp only [List.cons_append, valid_cons_iff]
      constructor
      · rintro ⟨head, tail⟩
        obtain ⟨middle, frontValid, backValid⟩ := (ih link.next).mp tail
        exact ⟨middle, ⟨head, frontValid⟩, backValid⟩
      · rintro ⟨middle, ⟨head, frontValid⟩, backValid⟩
        exact ⟨head, (ih link.next).mpr ⟨middle, frontValid, backValid⟩⟩

/-- Exact finite recipes construct an original proof-relevant rewrite path.
Recursion follows submitted data; no global proof choice is needed. -/
def toRewritePath : (trace : Trace) → (source target : Pattern) →
    Valid plan bound type trace source target →
      (GeneralOccurrenceSemantics.gslt plan bound type).RewritePath source target
  | [], source, target, held => by
      have same := (valid_nil_iff plan bound type source target).mp held
      cases same
      exact @Mettapedia.GSLT.GSLT.RewritePath.nil (GeneralOccurrenceSemantics.gslt plan bound type) source
  | link :: rest, source, target, held =>
      let clauses := (valid_cons_iff plan bound type link rest source target).mp held
      .cons ((exists_valid_iff_step plan bound type source link.next).mp ⟨link.step, clauses.1⟩)
        (toRewritePath rest link.next target clauses.2)

theorem toRewritePath_length (trace : Trace) (source target : Pattern)
    (held : Valid plan bound type trace source target) :
    (toRewritePath plan bound type trace source target held).length = trace.length := by
  induction trace generalizing source with
  | nil =>
      have same := (valid_nil_iff plan bound type source target).mp held
      cases same
      rfl
  | cons link rest ih =>
      simp only [toRewritePath, Mettapedia.GSLT.GSLT.RewritePath.length, List.length_cons]
      rw [ih]
      omega

theorem exists_valid_of_rewritePath {source target : Pattern}
    (path : (GeneralOccurrenceSemantics.gslt plan bound type).RewritePath source target) :
    ∃ trace, Valid plan bound type trace source target ∧ trace.length = path.length := by
  refine @Mettapedia.GSLT.GSLT.RewritePath.rec (GeneralOccurrenceSemantics.gslt plan bound type)
    (fun first last path => ∃ trace, Valid plan bound type trace first last ∧ trace.length = path.length)
    ?_ ?_ source target path
  · intro first
    exact ⟨[], .nil first, rfl⟩
  · intro first middle last step rest ih
    obtain ⟨recipe, recipeValid⟩ :=
      (GeneralRewriteRecipe.exists_valid_iff_step plan bound type first middle).mpr step
    obtain ⟨trace, tail, length⟩ := ih
    exact ⟨⟨middle, recipe⟩ :: trace, .cons recipeValid tail, by
      simp only [List.length_cons, Mettapedia.GSLT.GSLT.RewritePath.length, length]
      omega⟩

theorem exists_valid_iff_rewritePath (source target : Pattern) :
    (∃ trace, Valid plan bound type trace source target) ↔
      Nonempty ((GeneralOccurrenceSemantics.gslt plan bound type).RewritePath source target) := by
  constructor
  · rintro ⟨trace, held⟩
    exact ⟨toRewritePath plan bound type trace source target held⟩
  · rintro ⟨path⟩
    obtain ⟨trace, held, _⟩ := exists_valid_of_rewritePath plan bound type path
    exact ⟨trace, held⟩

theorem exists_checked_iff_rewritePath (source target : Pattern) :
    (∃ trace, check plan bound type source target trace = true) ↔
      Nonempty ((GeneralOccurrenceSemantics.gslt plan bound type).RewritePath source target) := by
  simp only [check_exact]
  exact exists_valid_iff_rewritePath plan bound type source target

theorem exists_valid_iff_multiStep (source target : Pattern) :
    (∃ trace, Valid plan bound type trace source target) ↔
      (GeneralOccurrenceSemantics.gslt plan bound type).MultiStep source target := by
  constructor
  · rintro ⟨trace, held⟩
    induction held with
    | nil source => exact @Mettapedia.GSLT.GSLT.MultiStep.refl (GeneralOccurrenceSemantics.gslt plan bound type) source
    | @cons link rest source target head _ ih =>
        exact .step ((GeneralRewriteRecipe.exists_valid_iff_step plan bound type source link.next).mp
          ⟨link.step, head⟩) ih
  · intro path
    refine @Mettapedia.GSLT.GSLT.MultiStep.rec (GeneralOccurrenceSemantics.gslt plan bound type)
      (fun first last _ => ∃ trace, Valid plan bound type trace first last)
      ?_ ?_ source target path
    · intro first
      exact ⟨[], .nil first⟩
    · intro first middle last step rest ih
      obtain ⟨recipe, recipeValid⟩ :=
        (GeneralRewriteRecipe.exists_valid_iff_step plan bound type first middle).mpr step
      obtain ⟨trace, tail⟩ := ih
      exact ⟨⟨middle, recipe⟩ :: trace, .cons recipeValid tail⟩

end Trace

/-- Equation evidence at a trace join becomes part of the next recipe's
source walk. The selected firing and its target walk remain unchanged. -/
def prependConversions (conversions : List GeneralOccurrenceSemantics.Conversion)
    (recipe : StepTrace) : StepTrace where
  before := {recipe.before with conversions := conversions ++ recipe.before.conversions}
  after := recipe.after

theorem prependConversions_valid (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    {source middle target : Pattern} {conversions : List GeneralOccurrenceSemantics.Conversion}
    {recipe : StepTrace}
    (before : GeneralOccurrenceSemantics.ConversionPath plan bound type source middle conversions)
    (held : StepTrace.Valid plan bound type middle target recipe) :
    StepTrace.Valid plan bound type source target (prependConversions conversions recipe) := by
  rcases held with ⟨⟨original, firing⟩, after⟩
  exact ⟨⟨GeneralOccurrenceSemantics.ConversionPath.append plan bound type before original, firing⟩, after⟩

/-- The endpoint conversions are explicit data even when the primitive trace
is empty. Their lengths do not contribute to the primitive rewrite count. -/
structure SemanticTrace where
  startRepresentative : Pattern
  endRepresentative : Pattern
  before : List GeneralOccurrenceSemantics.Conversion
  trace : Trace
  after : List GeneralOccurrenceSemantics.Conversion
  deriving Repr

namespace SemanticTrace

variable (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)

def Valid (source target : Pattern) (receipt : SemanticTrace) : Prop :=
  GeneralOccurrenceSemantics.ConversionPath plan bound type source receipt.startRepresentative receipt.before ∧
    Trace.Valid plan bound type receipt.trace receipt.startRepresentative receipt.endRepresentative ∧
      GeneralOccurrenceSemantics.ConversionPath plan bound type receipt.endRepresentative target receipt.after

def check (source target : Pattern) (receipt : SemanticTrace) : Bool :=
  GeneralRewriteRecipe.checkConversions plan bound type source receipt.startRepresentative receipt.before &&
    Trace.check plan bound type receipt.startRepresentative receipt.endRepresentative receipt.trace &&
      GeneralRewriteRecipe.checkConversions plan bound type receipt.endRepresentative target receipt.after

theorem check_exact (source target : Pattern) (receipt : SemanticTrace) :
    check plan bound type source target receipt = true ↔ Valid plan bound type source target receipt := by
  simp only [check, Valid, Bool.and_eq_true, GeneralRewriteRecipe.checkConversions_exact,
    Trace.check_exact, and_assoc]

/-- Compose semantic traces without discovering another rewrite. At a
nonempty second trace, join conversions enter its first recipe; otherwise
all joining conversions remain in the final walk. -/
def append (front back : SemanticTrace) : SemanticTrace :=
  match back.trace with
  | [] =>
      {startRepresentative := front.startRepresentative
       endRepresentative := front.endRepresentative
       before := front.before
       trace := front.trace
       after := (front.after ++ back.before) ++ back.after}
  | link :: rest =>
      {startRepresentative := front.startRepresentative
       endRepresentative := back.endRepresentative
       before := front.before
       trace := front.trace ++
         ({link with step := prependConversions (front.after ++ back.before) link.step} :: rest)
       after := back.after}

theorem append_valid {source middle target : Pattern} {front back : SemanticTrace}
    (frontValid : Valid plan bound type source middle front)
    (backValid : Valid plan bound type middle target back) :
    Valid plan bound type source target (append front back) := by
  cases second : back.trace with
  | nil =>
      simp only [Valid, append, second]
      have same := (Trace.valid_nil_iff plan bound type back.startRepresentative back.endRepresentative).mp
        (second ▸ backValid.2.1)
      have last : GeneralOccurrenceSemantics.ConversionPath plan bound type
          back.startRepresentative target back.after := by
        simpa only [same] using backValid.2.2
      exact ⟨frontValid.1, frontValid.2.1,
        GeneralOccurrenceSemantics.ConversionPath.append plan bound type
          (GeneralOccurrenceSemantics.ConversionPath.append plan bound type frontValid.2.2 backValid.1) last⟩
  | cons link rest =>
      simp only [Valid, append, second]
      have clauses := (Trace.valid_cons_iff plan bound type link rest
        back.startRepresentative back.endRepresentative).mp (second ▸ backValid.2.1)
      have bridge := GeneralOccurrenceSemantics.ConversionPath.append plan bound type frontValid.2.2 backValid.1
      have head := prependConversions_valid plan bound type bridge clauses.1
      refine ⟨frontValid.1, ?_, backValid.2.2⟩
      exact (Trace.valid_append_iff plan bound type front.trace _
        front.startRepresentative back.endRepresentative).mpr
          ⟨front.endRepresentative, frontValid.2.1, .cons head clauses.2⟩

theorem append_checked {source middle target : Pattern} {front back : SemanticTrace}
    (frontChecked : check plan bound type source middle front = true)
    (backChecked : check plan bound type middle target back = true) :
    check plan bound type source target (append front back) = true :=
  (check_exact plan bound type _ _ _).mpr
    (append_valid plan bound type ((check_exact plan bound type _ _ _).mp frontChecked)
      ((check_exact plan bound type _ _ _).mp backChecked))

theorem append_primitive_count (front back : SemanticTrace) :
    (append front back).trace.length = front.trace.length + back.trace.length := by
  cases second : back.trace <;> simp only [append, second, List.length_append, List.length_cons, List.length_nil, Nat.add_zero]

def toSemanticPath (source target : Pattern) (receipt : SemanticTrace)
    (held : Valid plan bound type source target receipt) :
    SemanticPath (GeneralOccurrenceSemantics.gslt plan bound type) source target where
  startRepresentative := receipt.startRepresentative
  endRepresentative := receipt.endRepresentative
  sourceEquation := held.1.equivalent
  path := Trace.toRewritePath plan bound type receipt.trace _ _ held.2.1
  targetEquation := held.2.2.equivalent

theorem exists_valid_iff_semanticPath (source target : Pattern) :
    (∃ receipt, Valid plan bound type source target receipt) ↔
      Nonempty (SemanticPath (GeneralOccurrenceSemantics.gslt plan bound type) source target) := by
  constructor
  · rintro ⟨receipt, held⟩
    exact ⟨toSemanticPath plan bound type source target receipt held⟩
  · rintro ⟨path⟩
    obtain ⟨before, beforeValid⟩ :=
      (GeneralRewriteRecipe.exists_conversionPath_iff_equiv plan bound type source path.startRepresentative).mpr path.sourceEquation
    obtain ⟨trace, traceValid⟩ :=
      (Trace.exists_valid_iff_rewritePath plan bound type path.startRepresentative path.endRepresentative).mpr ⟨path.path⟩
    obtain ⟨after, afterValid⟩ :=
      (GeneralRewriteRecipe.exists_conversionPath_iff_equiv plan bound type path.endRepresentative target).mpr path.targetEquation
    exact ⟨⟨path.startRepresentative, path.endRepresentative, before, trace, after⟩,
      beforeValid, traceValid, afterValid⟩

theorem exists_checked_iff_semanticPath (source target : Pattern) :
    (∃ receipt, check plan bound type source target receipt = true) ↔
      Nonempty (SemanticPath (GeneralOccurrenceSemantics.gslt plan bound type) source target) := by
  simp only [check_exact]
  exact exists_valid_iff_semanticPath plan bound type source target

/-- Exact-target may reachability is an existing native type of the path
theory, rather than a new modal interpretation chosen by the checker. -/
theorem exists_checked_iff_exactTargetNativeType (source target : Pattern) :
    (∃ receipt, check plan bound type source target receipt = true) ↔
      (gsltOSLF (pathGSLT (GeneralOccurrenceSemantics.gslt plan bound type))).satisfies source
        (exactTargetNativeType (pathGSLT (GeneralOccurrenceSemantics.gslt plan bound type)) target).pred := by
  exact (exists_checked_iff_semanticPath plan bound type source target).trans
    (satisfies_exactTargetNativeType_iff_step
      (pathGSLT (GeneralOccurrenceSemantics.gslt plan bound type)) source target).symm

def toGradedSemanticPath (source target : Pattern) (receipt : SemanticTrace)
    (held : Valid plan bound type source target receipt) :
    GradedSemanticPath (GeneralOccurrenceSemantics.gslt plan bound type) receipt.trace.length source target where
  toSemanticPath := toSemanticPath plan bound type source target receipt held
  length_eq := Trace.toRewritePath_length plan bound type receipt.trace _ _ held.2.1

theorem exists_valid_iff_gradedSemanticPath (steps : Nat) (source target : Pattern) :
    (∃ receipt, Valid plan bound type source target receipt ∧ receipt.trace.length = steps) ↔
      Nonempty (GradedSemanticPath (GeneralOccurrenceSemantics.gslt plan bound type) steps source target) := by
  constructor
  · rintro ⟨receipt, held, same⟩
    exact ⟨same ▸ toGradedSemanticPath plan bound type source target receipt held⟩
  · rintro ⟨path⟩
    obtain ⟨before, beforeValid⟩ :=
      (GeneralRewriteRecipe.exists_conversionPath_iff_equiv plan bound type source path.startRepresentative).mpr path.sourceEquation
    obtain ⟨trace, traceValid, length⟩ := Trace.exists_valid_of_rewritePath plan bound type path.path
    obtain ⟨after, afterValid⟩ :=
      (GeneralRewriteRecipe.exists_conversionPath_iff_equiv plan bound type path.endRepresentative target).mpr path.targetEquation
    exact ⟨⟨path.startRepresentative, path.endRepresentative, before, trace, after⟩,
      ⟨beforeValid, traceValid, afterValid⟩, length.trans path.length_eq⟩

theorem exists_checked_iff_gradedTargetNativeType (steps : Nat) (source target : Pattern) :
    (∃ receipt, check plan bound type source target receipt = true ∧ receipt.trace.length = steps) ↔
      (gsltOSLF (gradedPathGSLT (GeneralOccurrenceSemantics.gslt plan bound type) steps)).satisfies source
        (exactTargetNativeType (gradedPathGSLT (GeneralOccurrenceSemantics.gslt plan bound type) steps) target).pred := by
  simp only [check_exact]
  exact (exists_valid_iff_gradedSemanticPath plan bound type steps source target).trans
    (satisfies_exactTargetNativeType_iff_step
      (gradedPathGSLT (GeneralOccurrenceSemantics.gslt plan bound type) steps) source target).symm

/-- Existing equation-respecting finite-path possibility, with a submitted
trace as witness. It has no universal-execution consequence. -/
theorem exists_checked_iff_pathDiamond
    (predicate : EquationPredicate (pathGSLT (GeneralOccurrenceSemantics.gslt plan bound type)))
    (source : Pattern) :
    (∃ target receipt, check plan bound type source target receipt = true ∧ predicate target) ↔
      pathDiamond (GeneralOccurrenceSemantics.gslt plan bound type) predicate source := by
  apply Iff.trans ?_ (pathDiamond_spec (GeneralOccurrenceSemantics.gslt plan bound type) predicate source).symm
  constructor
  · rintro ⟨target, receipt, checked, holds⟩
    exact ⟨target, (exists_checked_iff_semanticPath plan bound type source target).mp ⟨receipt, checked⟩, holds⟩
  · rintro ⟨target, path, holds⟩
    obtain ⟨receipt, checked⟩ := (exists_checked_iff_semanticPath plan bound type source target).mpr path
    exact ⟨target, receipt, checked, holds⟩

theorem exists_checked_iff_reachingNativeType
    (predicate : EquationPredicate (pathGSLT (GeneralOccurrenceSemantics.gslt plan bound type)))
    (source : Pattern) :
    (∃ target receipt, check plan bound type source target receipt = true ∧ predicate target) ↔
      (pathOSLF (GeneralOccurrenceSemantics.gslt plan bound type)).satisfies source
        (reachingNativeType (GeneralOccurrenceSemantics.gslt plan bound type) predicate).pred :=
  exists_checked_iff_pathDiamond plan bound type predicate source

end SemanticTrace

/-- A draft fixes the intended next state while leaving its local evidence
unresolved. A supplied recipe is still subject to independent checking. -/
structure PlanLink where
  next : Pattern
  step : Option StepTrace
  deriving Repr

abbrev TracePlan := List PlanLink

namespace TracePlan

def assemble : TracePlan → Option Trace
  | [] => some []
  | link :: rest => do
      let recipe ← link.step
      let trace ← assemble rest
      pure (⟨link.next, recipe⟩ :: trace)

def retain (trace : Trace) : TracePlan := trace.map fun link => ⟨link.next, some link.step⟩

@[simp] theorem assemble_retain (trace : Trace) : assemble (retain trace) = some trace := by
  induction trace with
  | nil => rfl
  | cons link rest ih =>
      change (assemble (retain rest)).bind (fun trace => some (link :: trace)) = some (link :: rest)
      rw [ih]
      rfl

theorem assemble_length {draft : TracePlan} {trace : Trace} (assembled : assemble draft = some trace) :
    trace.length = draft.length := by
  induction draft generalizing trace with
  | nil => cases Option.some.inj assembled; rfl
  | cons link rest ih =>
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff] at assembled
      obtain ⟨recipe, _, later, obtained, same⟩ := assembled
      cases Option.some.inj same
      simp only [List.length_cons, ih obtained]

theorem assemble_none_iff (draft : TracePlan) :
    assemble draft = none ↔ ∃ link ∈ draft, link.step = none := by
  induction draft with
  | nil => simp [assemble]
  | cons link rest ih =>
      cases recipe : link.step with
      | none => simp [assemble, recipe]
      | some value =>
          cases gathered : assemble rest <;>
            simp [assemble, recipe, Option.bind_eq_bind, List.mem_cons, ← ih, gathered]

inductive Result where
  | pending
  | refused
  | verified (target : Pattern)
  deriving DecidableEq, Repr

/-- Missing evidence is pending. A complete submitted sequence can be refused;
neither case asserts that the requested state is unreachable. -/
def run (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) (draft : TracePlan) : Result :=
  match assemble draft with
  | none => .pending
  | some trace =>
      match Trace.replay plan bound type source trace with
      | none => .refused
      | some target => .verified target

theorem run_verified_iff (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source target : Pattern) (draft : TracePlan) :
    run plan bound type source draft = .verified target ↔
      ∃ trace, assemble draft = some trace ∧ Trace.Valid plan bound type trace source target := by
  cases assembled : assemble draft with
  | none => simp [run, assembled]
  | some trace =>
      cases replayed : Trace.replay plan bound type source trace with
      | none => simp [run, assembled, ← Trace.replay_exact, replayed]
      | some final => simp [run, assembled, ← Trace.replay_exact, replayed]

theorem run_pending_iff (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (draft : TracePlan) :
    run plan bound type source draft = .pending ↔ ∃ link ∈ draft, link.step = none := by
  rw [← assemble_none_iff]
  cases assembled : assemble draft with
  | none => simp [run, assembled]
  | some trace =>
      cases replayed : Trace.replay plan bound type source trace <;> simp [run, assembled, replayed]

theorem run_retained_verified_iff (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source target : Pattern) (trace : Trace) :
    run plan bound type source (retain trace) = .verified target ↔
      Trace.Valid plan bound type trace source target := by
  rw [run_verified_iff]
  constructor
  · rintro ⟨actual, assembled, held⟩
    have same : trace = actual := Option.some.inj ((assemble_retain trace).symm.trans assembled)
    exact same.symm ▸ held
  · intro held
    exact ⟨trace, assemble_retain trace, held⟩

end TracePlan


/-- A rewrite plan contains primitive recipes whose choices may still be
open. Computed intermediate states belong to the resulting trace. -/
abbrev RecipePlan := List (Option Recipe)

namespace RecipePlan

def assemble : RecipePlan → Option (List Recipe)
  | [] => some []
  | choice :: rest => do
      let recipe ← choice
      let recipes ← assemble rest
      pure (recipe :: recipes)

theorem assemble_none_iff (choices : RecipePlan) :
    assemble choices = none ↔ none ∈ choices := by
  induction choices with
  | nil => simp [assemble]
  | cons choice rest ih =>
      cases choice <;> cases assembled : assemble rest <;>
        simp [assemble, Option.bind_eq_bind, List.mem_cons, ← ih, assembled]

/-- Fill each recipe's deterministic fields, then continue from the computed
result. No endpoint or successor enumeration is supplied by the caller. -/
def replay (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern) :
    List Recipe → Option (Pattern × Trace)
  | [] => some (source, [])
  | recipe :: rest => do
      let receipt ← expand plan bound type source recipe
      let (target, tail) ← replay plan bound type receipt.target rest
      pure (target, ⟨receipt.target, ⟨⟨source, [], receipt⟩, []⟩⟩ :: tail)

theorem replay_sound {plan : Plan} {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {choices : List Recipe} {trace : Trace}
    (replayed : replay plan bound type source choices = some (target, trace)) :
    Trace.Valid plan bound type trace source target := by
  induction choices generalizing source target trace with
  | nil => cases Option.some.inj replayed; exact .nil _
  | cons recipe rest ih =>
      simp only [replay, Option.bind_eq_bind, Option.bind_eq_some_iff] at replayed
      obtain ⟨receipt, expanded, later, replayed, same⟩ := replayed
      cases later with
      | mk last tail =>
          cases Option.some.inj same
          exact .cons ⟨⟨.nil _, expand_sound expanded⟩, .nil _⟩ (ih replayed)

inductive Result where
  | pending
  | refused
  | verified (target : Pattern) (trace : Trace)
  deriving Repr

def run (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) (source : Pattern)
    (choices : RecipePlan) : Result :=
  match assemble choices with
  | none => .pending
  | some recipes =>
      match replay plan bound type source recipes with
      | none => .refused
      | some (target, trace) => .verified target trace

theorem run_pending_iff (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (choices : RecipePlan) :
    run plan bound type source choices = .pending ↔ none ∈ choices := by
  rw [← assemble_none_iff]
  unfold run
  cases assembled : assemble choices with
  | none => simp
  | some recipes =>
      cases replayed : replay plan bound type source recipes with
      | none => simp [replayed]
      | some result => cases result; simp [replayed]

theorem run_verified_sound {plan : Plan} {bound : List TypeExpr} {type : TypeExpr}
    {source target : Pattern} {choices : RecipePlan} {trace : Trace}
    (verified : run plan bound type source choices = .verified target trace) :
    Trace.Valid plan bound type trace source target := by
  unfold run at verified
  split at verified
  · cases verified
  · split at verified
    · cases verified
    · cases verified
      exact replay_sound ‹_›

end RecipePlan

end Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeComposition
