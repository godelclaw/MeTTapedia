import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestTypes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ScopedSubstitutionInversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaboration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursorDerivation

/-!
# Constructor clauses compiled to existing indexed eliminators

This scoped elaboration stage consumes the admitted constructor telescope.
There is one linear, top-level constructor clause per source occurrence, in
source order. Its body may call the defined function only through recursive
children listed by that telescope. Exact inverse substitution replaces those
calls by induction hypotheses, and existing lambda abstraction builds methods.
The eliminator itself is supplied by admission rather than generated again.

The source call template has the original ambient variables followed by the
recursive index and child. Different source argument orders are represented
by this template, with no change to the eliminator calling convention.
Text parsing, nested pattern matrices and declaration admission are separate
stages. Successful whole-term elaboration uses the independent typed checker.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.CaseElaboration

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality.Normalization

universe u
variable {I : Interface.{u}} {Head : Type} {n : Nat}

/-- The clause body sees ambient parameters followed by constructor fields
in the original lexical order. Recursive calls have ordinary core syntax. -/
structure Clause (Head : Type) (ambient : Nat) where
  constructor : String
  fields : Nat
  body : Tm Head (ambient + fields)

/-- Finite input to the clause compiler, before any semantic interpretation.
A source adapter must separately compare these fields and calls with its
admitted inventory. A plan itself carries no typing or computation authority. -/
structure BranchPlan (Head : Type) (ambient : Nat) where
  name : String
  fields : Nat
  recursiveCalls : List (Tm Head (ambient + fields))
  deriving DecidableEq, Repr

def fieldTerms (constructor : NamedConstructor I []) :
    Fin (Guest.fieldCount constructor.body) → Tm Head (n + Guest.fieldCount constructor.body) :=
  fun index => .var ⟨Guest.fieldCount constructor.body - 1 - index.val, by omega⟩

def children (indices : Guest.IndexSyntax I Head) (constructor : NamedConstructor I []) :
    List (Tm Head (n + Guest.fieldCount constructor.body) ×
      Tm Head (n + Guest.fieldCount constructor.body)) :=
  Guest.recursiveArguments indices constructor.body PUnit.unit (fieldTerms constructor)

def calls (indices : Guest.IndexSyntax I Head) (constructor : NamedConstructor I [])
    (template : Tm Head (n + 2)) : List (Tm Head (n + Guest.fieldCount constructor.body)) :=
  (children indices constructor).map fun pair =>
    subst (consSub pair.2 (consSub pair.1 (fun index =>
      .var ⟨index.val + Guest.fieldCount constructor.body, by omega⟩))) template

def plan (indices : Guest.IndexSyntax I Head) (constructor : NamedConstructor I [])
    (template : Tm Head (n + 2)) : BranchPlan Head n :=
  ⟨constructor.name, Guest.fieldCount constructor.body, calls indices constructor template⟩

def BranchPlan.substitution (plan : BranchPlan Head n) :
    Sub Head (n + plan.fields + plan.recursiveCalls.length) (n + plan.fields) :=
  extendSub ids (fun index => plan.recursiveCalls.getD index defaultTm) plan.recursiveCalls.length

def BranchPlan.method (plan : BranchPlan Head n)
    (body : Tm Head (n + plan.fields + plan.recursiveCalls.length)) : Tm Head n :=
  lams plan.fields (lams plan.recursiveCalls.length body)

def callSubstitution (indices : Guest.IndexSyntax I Head) (constructor : NamedConstructor I [])
    (template : Tm Head (n + 2)) :
    Sub Head (n + Guest.fieldCount constructor.body + (calls indices constructor template).length)
      (n + Guest.fieldCount constructor.body) :=
  (plan indices constructor template).substitution

def method (indices : Guest.IndexSyntax I Head) (constructor : NamedConstructor I [])
    (template : Tm Head (n + 2))
    (body : Tm Head (n + Guest.fieldCount constructor.body +
      (calls indices constructor template).length)) : Tm Head n :=
  (plan indices constructor template).method body

def adaptFields (name : String) (fields : Nat) (clause : Clause Head n) :
    Option (Tm Head (n + fields)) :=
  if clause.constructor = name then
    if same : clause.fields = fields then some (same ▸ clause.body) else none
  else none

/-- Arity and name are checked before the dependent cast. An arbitrary
clause cannot silently acquire another constructor's telescope. -/
def adaptClause (constructor : NamedConstructor I []) (clause : Clause Head n) :
    Option (Tm Head (n + Guest.fieldCount constructor.body)) :=
  adaptFields constructor.name (Guest.fieldCount constructor.body) clause

theorem adaptClause_name (constructor : NamedConstructor I []) (clause : Clause Head n)
    (body : Tm Head (n + Guest.fieldCount constructor.body))
    (accepted : adaptClause constructor clause = some body) :
    clause.constructor = constructor.name ∧ clause.fields = Guest.fieldCount constructor.body := by
  unfold adaptClause adaptFields at accepted
  split at accepted
  · rename_i named
    split at accepted
    · rename_i arity
      exact ⟨named, arity⟩
    · cases accepted
  · cases accepted

variable [DecidableEq Head]

def compilePlan (plan : BranchPlan Head n) (forbidden : DeclName)
    (clause : Clause Head n) : Option (Tm Head n) := do
  let source ← adaptFields plan.name plan.fields clause
  let body ← ScopedSubstitutionInversion.invert forbidden plan.substitution source
  return plan.method body

/-- The executable plan interface has the same reconstruction boundary as
the semantic inventory adapter; proposed plans do not bypass typed replay. -/
theorem compilePlan_reconstructs (plan : BranchPlan Head n) (forbidden : DeclName)
    (clause : Clause Head n) (compiled : Tm Head n)
    (accepted : compilePlan plan forbidden clause = some compiled) :
    ∃ source body,
      adaptFields plan.name plan.fields clause = some source ∧
      subst plan.substitution body = source ∧
      forbidden ∉ ConstantExpansion.constantNames body ∧
      compiled = plan.method body := by
  cases adapted : adaptFields plan.name plan.fields clause with
  | none => simp [compilePlan, adapted] at accepted
  | some source =>
      cases inverted : ScopedSubstitutionInversion.invert forbidden plan.substitution source with
      | none => simp [compilePlan, adapted, inverted] at accepted
      | some body =>
          have same : plan.method body = compiled := by
            simpa [compilePlan, adapted, inverted] using accepted
          obtain ⟨restores, free⟩ := ScopedSubstitutionInversion.invert_sound _ _ _ _ inverted
          exact ⟨source, body, rfl, restores, free, same.symm⟩

def compileBranch (indices : Guest.IndexSyntax I Head) (forbidden : DeclName)
    (template : Tm Head (n + 2)) (constructor : NamedConstructor I [])
    (clause : Clause Head n) : Option (Tm Head n) :=
  compilePlan (plan indices constructor template) forbidden clause

/-- Every emitted method reconstructs the original submitted clause when its
hypotheses are replaced by exactly the declared recursive child calls. -/
theorem compileBranch_reconstructs (indices : Guest.IndexSyntax I Head) (forbidden : DeclName)
    (template : Tm Head (n + 2)) (constructor : NamedConstructor I [])
    (clause : Clause Head n) (compiled : Tm Head n)
    (accepted : compileBranch indices forbidden template constructor clause = some compiled) :
    ∃ source body,
      adaptClause constructor clause = some source ∧
      subst (callSubstitution indices constructor template) body = source ∧
      forbidden ∉ ConstantExpansion.constantNames body ∧
      compiled = method indices constructor template body :=
  compilePlan_reconstructs (plan indices constructor template) forbidden clause compiled accepted

def compilePlans (plans : List (BranchPlan Head n)) (forbidden : DeclName)
    (clauses : List (Clause Head n)) : Option (List (Tm Head n)) :=
  if clauses.map Clause.constructor = plans.map BranchPlan.name then
    (plans.zip clauses).mapM fun pair => compilePlan pair.1 forbidden pair.2
  else none

theorem compilePlans_coverage (plans : List (BranchPlan Head n)) (forbidden : DeclName)
    (clauses : List (Clause Head n)) (methods : List (Tm Head n))
    (accepted : compilePlans plans forbidden clauses = some methods) :
    clauses.map Clause.constructor = plans.map BranchPlan.name := by
  unfold compilePlans at accepted
  split at accepted
  · assumption
  · cases accepted

def compileMethods (indices : Guest.IndexSyntax I Head) (admitted : Admitted I [])
    (forbidden : DeclName) (template : Tm Head (n + 2)) (clauses : List (Clause Head n)) :
    Option (List (Tm Head n)) :=
  compilePlans (admitted.constructors.map (fun constructor => plan indices constructor template))
    forbidden clauses

theorem compileMethods_coverage (indices : Guest.IndexSyntax I Head) (admitted : Admitted I [])
    (forbidden : DeclName) (template : Tm Head (n + 2)) (clauses : List (Clause Head n))
    (methods : List (Tm Head n))
    (accepted : compileMethods indices admitted forbidden template clauses = some methods) :
    clauses.map Clause.constructor = admitted.constructors.map NamedConstructor.name := by
  simpa only [List.map_map, Function.comp_def, plan] using compilePlans_coverage _ _ _ _ accepted

structure Result (Head : Type) (RootCode : Nat → Type) (ambient : Nat) where
  methods : List (Tm Head ambient)
  submission : FormationSensitiveElaboration.Submission Head RootCode ambient

variable (R : Rules Head)
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]
variable (decoder : StructuralConversionCode.RootDecoder R.computation)

def elaborate (choices : FormationSensitiveElaboration.Choices Head decoder.Code) (fuel : Nat)
    (indices : Guest.IndexSyntax I Head) (admitted : Admitted I [])
    (forbidden : DeclName) (template : Tm Head (n + 2)) (clauses : List (Clause Head n))
    (context : Ctx Head n) (recursor motive index value expected : Tm Head n) :
    Option (Result Head decoder.Code n) := do
  let methods ← compileMethods indices admitted forbidden template clauses
  let submission ← FormationSensitiveElaboration.elaborate R decoder choices fuel context
    (Guest.Types.recursorAt recursor motive methods index value) expected
  return ⟨methods, submission⟩

theorem elaborate_sound (choices : FormationSensitiveElaboration.Choices Head decoder.Code) (fuel : Nat)
    (indices : Guest.IndexSyntax I Head) (admitted : Admitted I [])
    (forbidden : DeclName) (template : Tm Head (n + 2)) (clauses : List (Clause Head n))
    (context : Ctx Head n) (recursor motive index value expected : Tm Head n)
    (result : Result Head decoder.Code n)
    (accepted : elaborate R decoder choices fuel indices admitted forbidden template clauses
      context recursor motive index value expected = some result) :
    FormationSensitive.Judgment R context
      (Guest.Types.recursorAt recursor motive result.methods index value) expected := by
  cases compiled : compileMethods indices admitted forbidden template clauses with
  | none => simp [elaborate, compiled] at accepted
  | some methods =>
      cases checked : FormationSensitiveElaboration.elaborate R decoder choices fuel context
          (Guest.Types.recursorAt recursor motive methods index value) expected with
      | none => simp [elaborate, compiled, checked] at accepted
      | some submission =>
          have same : Result.mk methods submission = result := by
            simpa [elaborate, compiled, checked] using accepted
          cases same
          exact FormationSensitiveElaboration.elaborate_sound R decoder choices _ _ _ _ _ checked

end Mettapedia.GSLT.LanguageDef.IndexedInductive.CaseElaboration
