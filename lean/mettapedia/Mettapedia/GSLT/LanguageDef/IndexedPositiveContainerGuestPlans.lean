import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestTypes
import Mettapedia.GSLT.LanguageDef.IndexedInductiveCaseElaboration
import Mettapedia.GSLT.LanguageDef.IndexedInductiveOperationSource

/-!
# Recursive-call plans from registered-container constructor codes

The source clause context contains all original fields. Scanning the admitted
code supplies exactly the direct children and nested fields in lexical order.
Earlier data fields populate the scoped environment used by both the recursive
family index and the container output expression.

The source library supplies call expressions with substitution coherence.
Their meaning and the adapters from complete induction bundles remain separate
obligations. A plan is input to the existing inverse-substitution compiler; it
confers no typing, semantic interpretation or computation authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestPlans

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open IndexedInductive.Guest
open IndexedInductive.CaseElaboration
open IndexedPositiveContainerGuestTypes

universe u
variable {I : Interface.{u}} {registry : Registry I} {Head : Type}

def fieldCount {parameters : Nat} : {context : List I.SortCode} →
    Code I registry parameters context → Nat
  | _, .result _ => 0
  | _, .data _ rest => fieldCount rest + 1
  | _, .recursive _ rest => fieldCount rest + 1
  | _, .nested _ _ _ _ _ rest => fieldCount rest + 1
termination_by structural _ code => code

/-- Count method arguments: one for each direct child and one complete bundle
for each nested field. This is not the number of semantic container positions. -/
def hypothesisCount {parameters : Nat} : {context : List I.SortCode} →
    Code I registry parameters context → Nat
  | _, .result _ => 0
  | _, .data _ rest => hypothesisCount rest
  | _, .recursive _ rest => hypothesisCount rest + 1
  | _, .nested _ _ _ _ _ rest => hypothesisCount rest + 1
termination_by structural _ code => code

/-- Source operations may refer to the original ambient variables. Their
recursive input is supplied by the admitted code, rather than a name lookup. -/
structure CallSyntax (I : Interface.{u}) (registry : Registry I) (Head : Type)
    (ambient : Nat) where
  direct : ∀ {context : List I.SortCode} {n : Nat},
    (Fin ambient → Tm Head n) → I.IndexExpr context →
      TermEnv I Head n context → Tm Head n → Tm Head n
  nested : ∀ {context : List I.SortCode} {n : Nat}
    (name : String) (entry : Entry I), registry.lookup name = some entry →
      (Fin ambient → Tm Head n) → entry.OutputExpr context → I.IndexExpr context →
      TermEnv I Head n context → Tm Head n → Tm Head n
  direct_substitute : ∀ {context n m} (outer : Fin ambient → Tm Head n)
    (index : I.IndexExpr context) (environment : TermEnv I Head n context)
    (child : Tm Head n) (substitution : Sub Head n m),
    subst substitution (direct outer index environment child) =
      direct (fun i => subst substitution (outer i)) index
        (mapEnv (subst substitution) environment) (subst substitution child)
  nested_substitute : ∀ {context n m} name entry registered
    (outer : Fin ambient → Tm Head n) (output : entry.OutputExpr context)
    (index : I.IndexExpr context) (environment : TermEnv I Head n context)
    (children : Tm Head n) (substitution : Sub Head n m),
    subst substitution (nested name entry registered outer output index environment children) =
      nested name entry registered (fun i => subst substitution (outer i)) output index
        (mapEnv (subst substitution) environment) (subst substitution children)

def calls {ambient parameters : Nat} (operations : CallSyntax I registry Head ambient) :
    {context : List I.SortCode} →
      (code : Code I registry parameters context) → {n : Nat} →
      (Fin ambient → Tm Head n) → TermEnv I Head n context →
      (Fin (fieldCount code) → Tm Head n) → List (Tm Head n)
  | _, .result _, _, _, _, _ => []
  | _, .data _ rest, _, outer, environment, arguments =>
      calls operations rest outer
        (arguments ⟨0, by simp [fieldCount]⟩, environment) (fun i => arguments i.succ)
  | _, .recursive index rest, _, outer, environment, arguments =>
      operations.direct outer index environment (arguments ⟨0, by simp [fieldCount]⟩) ::
        calls operations rest outer environment (fun i => arguments i.succ)

  | _, .nested name entry registered output index rest, _, outer, environment, arguments =>
      operations.nested name entry registered outer output index environment
          (arguments ⟨0, by simp [fieldCount]⟩) ::
        calls operations rest outer environment (fun i => arguments i.succ)
termination_by structural _ code _ _ _ _ => code

theorem calls_length {ambient parameters : Nat}
    (operations : CallSyntax I registry Head ambient) {context : List I.SortCode}
    (code : Code I registry parameters context) {n : Nat}
    (outer : Fin ambient → Tm Head n) (environment : TermEnv I Head n context)
    (arguments : Fin (fieldCount code) → Tm Head n) :
    (calls operations code outer environment arguments).length = hypothesisCount code := by
  induction code with
  | result _ => rfl
  | data sort rest ih => exact ih _ _
  | recursive index rest ih =>
      simp only [calls, List.length_cons, ih, hypothesisCount]
  | nested name entry registered output index rest ih =>
      simp only [calls, List.length_cons, ih, hypothesisCount]

theorem calls_substitute {ambient parameters : Nat}
    (operations : CallSyntax I registry Head ambient) {context : List I.SortCode}
    (code : Code I registry parameters context) {n m : Nat}
    (outer : Fin ambient → Tm Head n) (environment : TermEnv I Head n context)
    (arguments : Fin (fieldCount code) → Tm Head n) (substitution : Sub Head n m) :
    (calls operations code outer environment arguments).map (subst substitution) =
      calls operations code (fun i => subst substitution (outer i))
        (mapEnv (subst substitution) environment) (fun i => subst substitution (arguments i)) := by
  induction code with
  | result _ => rfl
  | data sort rest ih =>
      simpa only [calls, mapEnv] using
        ih (arguments ⟨0, by simp [fieldCount]⟩, environment) (fun i => arguments i.succ)
  | recursive index rest ih =>
      simp only [calls, List.map_cons, operations.direct_substitute, ih]
  | nested name entry registered output index rest ih =>
      simp only [calls, List.map_cons, operations.nested_substitute, ih]

/-- Lexical field zero is the oldest of the newly bound fields. -/
def fieldTerms {ambient parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) :
    Fin (fieldCount code) → Tm Head (ambient + fieldCount code) :=
  fun index => .var ⟨fieldCount code - 1 - index.val, by omega⟩

def outerTerms {ambient parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) :
    Fin ambient → Tm Head (ambient + fieldCount code) :=
  fun index => .var ⟨fieldCount code + index.val, by omega⟩

def plan {ambient parameters : Nat} (operations : CallSyntax I registry Head ambient)
    (name : String) (code : Code I registry parameters []) : BranchPlan Head ambient :=
  ⟨name, fieldCount code, calls operations code (outerTerms code) PUnit.unit (fieldTerms code)⟩

theorem plan_call_count {ambient parameters : Nat}
    (operations : CallSyntax I registry Head ambient) (name : String)
    (code : Code I registry parameters []) :
    (plan operations name code).recursiveCalls.length = hypothesisCount code :=
  calls_length operations code (outerTerms code) PUnit.unit (fieldTerms code)

/-- Every accepted compilation has the source name/arity and reconstructs the
actual source body. The call list was obtained from the admitted telescope. -/
theorem compile_reconstructs [DecidableEq Head] {ambient parameters : Nat}
    (operations : CallSyntax I registry Head ambient) (name : String)
    (code : Code I registry parameters []) (forbidden : DeclName)
    (clause : Clause Head ambient) (compiled : Tm Head ambient)
    (accepted : compilePlan (plan operations name code) forbidden clause = some compiled) :
    clause.constructor = name ∧ clause.fields = fieldCount code ∧
      (plan operations name code).recursiveCalls.length = hypothesisCount code ∧
      ∃ source body,
        adaptFields name (fieldCount code) clause = some source ∧
        subst (plan operations name code).substitution body = source ∧
        forbidden ∉ ConstantExpansion.constantNames body ∧
        compiled = (plan operations name code).method body := by
  obtain ⟨source, body, adapted, restored, free, emitted⟩ :=
    compilePlan_reconstructs _ _ _ _ accepted
  have named : clause.constructor = name := by
    unfold adaptFields at adapted
    split at adapted
    · assumption
    · cases adapted
  have arity : clause.fields = fieldCount code := by
    unfold adaptFields at adapted
    split at adapted
    · split at adapted
      · assumption
      · cases adapted
    · cases adapted
  exact ⟨named, arity, plan_call_count operations name code, source, body,
    adapted, restored, free, emitted⟩

/-! ## Compatibility with the ordinary indexed call compiler -/

/-- The ordinary fragment has no registered nested fields. Its existing
index/child template gives a coherent direct-call library without inventing
an implementation for an impossible container lookup. -/
def templateCalls {ambient : Nat} (indices : IndexSyntax I Head)
    (template : Tm Head (ambient + 2))
    (empty : ∀ name, registry.lookup name = none) : CallSyntax I registry Head ambient where
  direct outer index environment child :=
    subst (consSub child (consSub (indices.term index environment) outer)) template
  nested := by
    intro context n name entry registered
    rw [empty name] at registered
    cases registered
  direct_substitute := by
    intro context n m outer index environment child substitution
    rw [subst_comp]
    apply subst_ext
    intro position
    refine Fin.cases ?_ (fun rest => Fin.cases ?_ (fun _ => ?_) rest) position
    · rfl
    · exact indices.substitute index environment substitution
    · rfl
  nested_substitute := by
    intro context n m name entry registered
    rw [empty name] at registered
    cases registered

/-- Adding nested fields preserves every ordinary constructor telescope. -/
theorem fieldCount_ordinary {parameters : Nat} {context : List I.SortCode}
    (code : Mettapedia.TypeTheory.IndexedPolynomial.Description.Code I context) :
    fieldCount (ordinaryCode (registry := registry) (parameters := parameters) code) =
      IndexedInductive.Guest.fieldCount code := by
  induction code with
  | result _ => rfl
  | data sort rest ih => simpa only [ordinaryCode, fieldCount, IndexedInductive.Guest.fieldCount] using congrArg (· + 1) ih
  | recursive index rest ih => simpa only [ordinaryCode, fieldCount, IndexedInductive.Guest.fieldCount] using congrArg (· + 1) ih

/-- Reuse the existing source argument positions through the proved arity equality. -/
def ordinaryArguments {parameters n : Nat} {context : List I.SortCode}
    (code : Mettapedia.TypeTheory.IndexedPolynomial.Description.Code I context)
    (arguments : Fin (fieldCount (ordinaryCode (registry := registry) (parameters := parameters) code)) → Tm Head n) :
    Fin (IndexedInductive.Guest.fieldCount code) → Tm Head n :=
  fun i => arguments ⟨i.val, by rw [fieldCount_ordinary]; exact i.isLt⟩

/-- On the ordinary fragment, a direct-call template yields exactly the
existing index/child call list, including data between recursive fields. -/
theorem calls_ordinary {ambient parameters : Nat}
    (operations : CallSyntax I registry Head ambient) (indices : IndexSyntax I Head)
    (template : Tm Head (ambient + 2))
    (direct : ∀ {context n} (outer : Fin ambient → Tm Head n)
      (index : I.IndexExpr context) (environment : TermEnv I Head n context) (child : Tm Head n),
      operations.direct outer index environment child =
        subst (consSub child (consSub (indices.term index environment) outer)) template)
    {context : List I.SortCode}
    (code : Mettapedia.TypeTheory.IndexedPolynomial.Description.Code I context)
    {n : Nat} (outer : Fin ambient → Tm Head n) (environment : TermEnv I Head n context)
    (arguments : Fin (fieldCount (ordinaryCode (parameters := parameters) code)) → Tm Head n) :
    calls operations (ordinaryCode code) outer environment arguments =
      (IndexedInductive.Guest.recursiveArguments indices code environment
        (ordinaryArguments code arguments)).map (fun pair =>
          subst (consSub pair.2 (consSub pair.1 outer)) template) := by
  induction code with
  | result index => rfl
  | data sort rest ih =>
      exact ih (arguments ⟨0, by simp [ordinaryCode, fieldCount]⟩, environment)
          (fun i => arguments i.succ)
  | recursive index rest ih =>
      simp only [ordinaryCode, calls, IndexedInductive.Guest.recursiveArguments, ordinaryArguments, List.map_cons]
      rw [direct]
      exact congrArg (List.cons _) (ih environment (fun i => arguments i.succ))

/-! ## Source clauses checked against their generated dependent method type -/

section CheckedSource

variable [DecidableEq Head]
variable (R : Rules Head)
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]
variable (decoder : StructuralConversionCode.RootDecoder R.computation)

/-- The producer reads every source field, abstracts only code-derived calls,
and checks the emitted method at the generated dependent interface. Neither
the call syntax nor a successful parse substitutes for this replay. -/
def elaborateClause {ambient parameters : Nat}
    (operations : CallSyntax I registry Head ambient)
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (code : Code I registry parameters []) (types : TypeSyntax I Head ambient)
    (motive : Tm Head ambient) (name operation : String)
    (constructorParameters : List (Fin ambient))
    (symbols : List (IndexedInductive.OperationSource.Symbol Head))
    (producerFuel : Nat) (forbidden : DeclName)
    (rule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule)
    (choices : FormationSensitiveElaboration.Choices Head decoder.Code)
    (checkingFuel : Nat) (context : Ctx Head ambient) :
    Option (Tm Head ambient × FormationSensitiveElaboration.Submission Head decoder.Code ambient) := do
  let generated := plan operations name code
  let header := IndexedInductive.OperationSource.Header.fromPlan generated operation constructorParameters
  let method ← IndexedInductive.OperationSource.compileRule symbols producerFuel forbidden
    header generated.recursiveCalls rule
  let checked ← FormationSensitiveElaboration.elaborate R decoder choices checkingFuel context
    method (methodType indexing containers code types motive name)
  return (method, checked)

theorem elaborateClause_sound {ambient parameters : Nat}
    (operations : CallSyntax I registry Head ambient)
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (code : Code I registry parameters []) (types : TypeSyntax I Head ambient)
    (motive : Tm Head ambient) (name operation : String)
    (constructorParameters : List (Fin ambient))
    (symbols : List (IndexedInductive.OperationSource.Symbol Head))
    (producerFuel : Nat) (forbidden : DeclName)
    (rule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule)
    (choices : FormationSensitiveElaboration.Choices Head decoder.Code)
    (checkingFuel : Nat) (context : Ctx Head ambient)
    (result : Tm Head ambient × FormationSensitiveElaboration.Submission Head decoder.Code ambient)
    (accepted : elaborateClause R decoder operations indexing containers code types motive name operation
      constructorParameters symbols producerFuel forbidden rule choices checkingFuel context = some result) :
    FormationSensitive.Judgment R context result.1
        (methodType indexing containers code types motive name) ∧
      IndexedInductive.OperationSource.compileRule symbols producerFuel forbidden
        (IndexedInductive.OperationSource.Header.fromPlan (plan operations name code)
          operation constructorParameters)
        (plan operations name code).recursiveCalls rule = some result.1 := by
  cases compiled : IndexedInductive.OperationSource.compileRule symbols producerFuel forbidden
      (IndexedInductive.OperationSource.Header.fromPlan (plan operations name code)
        operation constructorParameters)
      (plan operations name code).recursiveCalls rule with
  | none => simp [elaborateClause, compiled] at accepted
  | some method =>
      cases checked : FormationSensitiveElaboration.elaborate R decoder choices checkingFuel context
          method (methodType indexing containers code types motive name) with
      | none => simp [elaborateClause, compiled, checked] at accepted
      | some submission =>
          have same : (method, submission) = result := by
            simpa [elaborateClause, compiled, checked] using accepted
          cases same
          exact ⟨FormationSensitiveElaboration.elaborate_sound R decoder choices _ _ _ _ _ checked,
            rfl⟩

end CheckedSource

end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestPlans
