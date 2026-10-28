import Mettapedia.Machines.ReadOnlyQuery

/-!
# Callability-sensitive translation and retained plans

An ordered source tree distinguishes opaque values from applications. Translation
marks each application as a call or data, according to the names available at
that translation boundary. A separate query-based compiler records every lookup,
including an absent name. The two compilers agree structurally.

A captured translation can be reused after precisely those reads validate.
Otherwise a new translation is published; the prior capture remains a value
with its original interpretation. This is the callability component of a
compiler contract. Types, effects, intrinsic forms, native ownership and the
adequacy of a concrete source elaborator are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CallabilityTranslation

open ReadOnlyQuery

mutual
  inductive Source (Name Value : Type) where
    | value (payload : Value)
    | apply (head : Name) (arguments : Arguments Name Value)
  inductive Arguments (Name Value : Type) where
    | nil
    | cons (first : Source Name Value) (rest : Arguments Name Value)
end

abbrev Plan (Name Value : Type) := Source (Bool × Name) Value
abbrev PlanArguments (Name Value : Type) := Arguments (Bool × Name) Value

variable {Name Value : Type}

mutual
  /-- Direct translation into a tree with explicit call/data decisions. -/
  def compile (available : Name → Bool) : Source Name Value → Plan Name Value
    | .value payload => .value payload
    | .apply head arguments =>
        .apply (available head, head) (compileArguments available arguments)
  def compileArguments (available : Name → Bool) :
      Arguments Name Value → PlanArguments Name Value
    | .nil => .nil
    | .cons first rest =>
        .cons (compile available first) (compileArguments available rest)
end

mutual
  /-- A compiler expressed through the shared pure-query interface. -/
  def query : Source Name Value → Program Name Bool (Plan Name Value)
    | .value payload => .pure (.value payload)
    | .apply head arguments =>
        .read head fun callable =>
          bind (queryArguments arguments) fun plans =>
            .pure (.apply (callable, head) plans)
  def queryArguments :
      Arguments Name Value → Program Name Bool (PlanArguments Name Value)
    | .nil => .pure .nil
    | .cons first rest =>
        bind (query first) fun plan =>
          bind (queryArguments rest) fun plans => .pure (.cons plan plans)
end

mutual
  /-- The names whose callability the source actually asks about. -/
  def observedNames : Source Name Value → List Name
    | .value _ => []
    | .apply head arguments => head :: observedArgumentNames arguments
  def observedArgumentNames : Arguments Name Value → List Name
    | .nil => []
    | .cons first rest => observedNames first ++ observedArgumentNames rest
end

mutual
  theorem query_compiles (available : Name → Bool) (source : Source Name Value) :
      (run available (query source)).answer = compile available source := by
    cases source with
    | value payload => rfl
    | apply head arguments =>
        simp [query, run, run_bind, compile, queryArguments_compile]
  theorem queryArguments_compile (available : Name → Bool)
      (arguments : Arguments Name Value) :
      (run available (queryArguments arguments)).answer =
        compileArguments available arguments := by
    cases arguments with
    | nil => rfl
    | cons first rest =>
        simp [queryArguments, run_bind, run, compileArguments,
          query_compiles, queryArguments_compile]
end

mutual
  theorem query_reads (available : Name → Bool) (source : Source Name Value) :
      (run available (query source)).reads =
        (observedNames source).map (fun name => (name, available name)) := by
    cases source with
    | value payload => rfl
    | apply head arguments =>
        simp [query, run, run_bind, observedNames, queryArguments_reads]
  theorem queryArguments_reads (available : Name → Bool) (arguments : Arguments Name Value) :
      (run available (queryArguments arguments)).reads =
        (observedArgumentNames arguments).map (fun name => (name, available name)) := by
    cases arguments with
    | nil => rfl
    | cons first rest =>
        simp [queryArguments, run_bind, run, observedArgumentNames,
          query_reads, queryArguments_reads, List.map_append]
end

mutual
  /-- Two translations are identical exactly when their answers agree on
  every callability observation made by this source. -/
  theorem compile_eq_iff_names (first second : Name → Bool) (source : Source Name Value) :
      compile first source = compile second source ↔
        ∀ name ∈ observedNames source, first name = second name := by
    cases source with
    | value payload => simp [compile, observedNames]
    | apply head arguments =>
        simp [compile, observedNames, compileArguments_eq_iff_names]
  theorem compileArguments_eq_iff_names (first second : Name → Bool)
      (arguments : Arguments Name Value) :
      compileArguments first arguments = compileArguments second arguments ↔
        ∀ name ∈ observedArgumentNames arguments, first name = second name := by
    cases arguments with
    | nil => simp [compileArguments, observedArgumentNames]
    | cons firstArg rest =>
        simp [compileArguments, observedArgumentNames, compile_eq_iff_names,
          compileArguments_eq_iff_names, List.mem_append, or_imp, forall_and]
end

/-- The complete public value of a captured source translation. -/
structure Capture (Name Value : Type) where
  source : Source Name Value
  plan : Plan Name Value
  reads : Reads Name Bool

def capture (available : Name → Bool) (source : Source Name Value) : Capture Name Value :=
  let result := run available (query source)
  ⟨source, result.answer, result.reads⟩

/-- Retain the old plan when its actual observations still hold. -/
def refresh (available : Name → Bool) (saved : Capture Name Value) : Plan Name Value :=
  if checkReads available saved.reads then saved.plan else compile available saved.source

theorem capture_compiles (available : Name → Bool) (source : Source Name Value) :
    (capture available source).plan = compile available source :=
  query_compiles available source

theorem refresh_capture (first second : Name → Bool) (source : Source Name Value) :
    refresh second (capture first source) = compile second source := by
  by_cases valid : checkReads second (run first (query source)).reads = true
  · simp only [refresh, capture, valid, ↓reduceIte]
    rw [← query_compiles second source]
    exact (validated_answer first second (query source) valid).symm
  · simp [refresh, capture, valid]

/-- A disjoint change needs no recompilation; equality includes all child
plans and their order, not only the root's call/data decision. -/
theorem reuse_of_reads_agree (first second : Name → Bool) (source : Source Name Value)
    (agree : Agrees second (capture first source).reads) :
    compile second source = (capture first source).plan := by
  rw [← query_compiles second source]
  exact congrArg Observation.answer (run_eq_of_agrees first second (query source) agree)

/-- Changes outside the names actually examined by a source preserve its
complete translated tree. Repeated names remain repeated observations. -/
theorem reuse_of_names_agree (first second : Name → Bool) (source : Source Name Value)
    (agree : ∀ name ∈ observedNames source, second name = first name) :
    compile second source = (capture first source).plan := by
  apply reuse_of_reads_agree
  intro read member
  simp only [capture, query_reads, List.mem_map] at member
  obtain ⟨name, present, rfl⟩ := member
  exact agree name present

/-- When either a wildcard or a named definition makes a head callable, the
exact dependency is their disjunction at each observed head. -/
theorem effective_callability_exact (wildFirst wildSecond : Bool)
    (first second : Name → Bool) (source : Source Name Value) :
    compile (fun name => wildFirst || first name) source =
        compile (fun name => wildSecond || second name) source ↔
      ∀ name ∈ observedNames source,
        (wildFirst || first name) = (wildSecond || second name) :=
  compile_eq_iff_names _ _ source

theorem values_read_nothing (available : Name → Bool) (payload : Value) :
    (capture available (.value payload)).reads = [] := rfl

namespace Controls

def before : Nat → Bool := fun _ => false
def after : Nat → Bool := fun name => name == 7
def caller : Source Nat Nat := .apply 7 (.cons (.value 41) .nil)
def unrelated : Source Nat Nat := .apply 9 (.cons (.value 41) .nil)

theorem absent_name_is_a_read : (capture before caller).reads = [(7, false)] := rfl

theorem new_name_invalidates : checkReads after (capture before caller).reads = false := by
  decide

theorem unrelated_change_reuses : checkReads after (capture before unrelated).reads = true := by
  decide

theorem new_call_is_published :
    refresh after (capture before caller) =
      .apply (true, 7) (.cons (.value 41) .nil) := rfl

/-- A frozen old plan and a fresh translation intentionally differ. -/
theorem retaining_stale_translation_changes_interpretation :
    (capture before caller).plan ≠ compile after caller := by
  intro equality
  cases equality

theorem repeated_occurrences_are_read_in_order :
    (capture before (.apply 9 (.cons caller (.cons caller .nil)))).reads =
      [(9, false), (7, false), (7, false)] := rfl

/-! A component revision can change even while the disjunction observed by a
translation stays true. Conversely, equal endpoints do not describe the
intervening history. These are different contracts. -/

def switchingWitnesses : List (Bool × Bool) :=
  [(true, true), (false, true), (true, true), (true, false)]

/-- Neither underlying witness is stable, although their disjunction is
continuously true. Requiring one fixed witness is sufficient but not exact. -/
theorem switching_witnesses_remain_admitted :
    switchingWitnesses.all (fun state => state.1 || state.2) = true ∧
    switchingWitnesses.all (fun state => state.1) = false ∧
    switchingWitnesses.all (fun state => state.2) = false := by
  decide

def effectiveABA : List (Bool × Bool) :=
  [(false, false), (false, true), (false, false)]

/-- The effective answer returns to its original value after an intervening
change. Endpoint reuse of a pure translation does not certify that history. -/
theorem equal_endpoints_do_not_certify_history :
    effectiveABA.map (fun state => state.1 || state.2) = [false, true, false] ∧
    checkReads before (capture before caller).reads = true := by
  decide

end Controls
end Mettapedia.Machines.CallabilityTranslation
