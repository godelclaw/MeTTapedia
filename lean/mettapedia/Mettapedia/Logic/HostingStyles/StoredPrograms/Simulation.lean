import Mettapedia.Logic.HostingStyles.StoredPrograms.Translation

/-!
# The engine's value is reached by the table

The equation engine evaluates the arguments of a call first, takes the first
equation whose left side matches, and asks its host for the primitives.  A
table has rules without order, which fire at any position.

**For a program of the class, a value that the engine returns for a call is a
reduct of the call in every theory that holds the rules of the program and
computes its primitives** (`applies_reduces`).  For a program that calls no
primitive of its host, the theory of its own table is such a theory
(`stored_value_reached`).

The proof follows the evaluator, fuel by fuel (`eval_reduces`).  Two
properties of a theory are all it uses.

* `Dispatches`: a call that selects an equation reduces to the instance of its
  right side.  The rule of the equation gives this in one step, when no
  variable occurs twice in a left side (`dispatches_of_rules`): the match of
  the engine is then the instance of the rule (`inst_patterns`).
* `RealizesPrimitives`: a call of a primitive on data reduces to the datum of
  what the host returns.

**No condition on overlap is used.**  The engine takes the first equation that
matches; the rule of that equation is in the table and fires.  What an
overlap costs is not the engine's value: it is that the table reaches other
terms as well (`NormalForms.lean`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host Env Outcome ItemsOutcome Special LeftLinear patternVarsList matchTerm
    matchTerms eval evalStep evalItemsWith applyWith Applies CallsWithin)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule RootStep Step Reduces inst binderFree usesOnly)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (step_of_rule)
open Mettapedia.Logic.HostingStyles.AtomsReduce (RunnableEquations programTheory)

/-! ## The assignment of a match -/

/-- **The assignment of an environment**, at a list of names: the pattern
variable at a position is the datum that the environment binds to the name at
that position. -/
def assignment (N : Spelling) (names : List String) (environment : Env) : Nat → LF.Term :=
  fun index =>
    match names[index]? with
    | some name =>
        match environment.lookup name with
        | some value => datum N value
        | none => .con "unbound"
    | none => .con "unbound"

theorem assignment_idxOf (N : Spelling) {names : List String} {environment : Env} {name : String}
    {value : EngineTerm} (member : name ∈ names) (found : environment.lookup name = some value) :
    assignment N names environment (names.idxOf name) = datum N value := by
  simp only [assignment, List.getElem?_idxOf member, found]

/-- A name that an environment binds once is found with its value. -/
theorem lookup_of_mem {environment : Env} (distinct : (environment.map Prod.fst).Nodup)
    {name : String} {value : EngineTerm} (member : (name, value) ∈ environment) :
    environment.lookup name = some value := by
  induction environment with
  | nil => cases member
  | cons binding rest ih =>
      obtain ⟨key, stored⟩ := binding
      simp only [List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp member with same | later
      · cases same
        exact DeterministicEquations.Env.lookup_cons_self name value rest
      · have different : key ≠ name := fun same =>
          distinct.1 (same ▸ List.mem_map_of_mem (f := Prod.fst) later)
        rw [DeterministicEquations.Env.lookup_cons_ne stored rest different]
        exact ih distinct.2 later

/-- A name that an environment binds is one of its names. -/
theorem mem_keys_of_lookup {environment : Env} {name : String} {value : EngineTerm}
    (found : environment.lookup name = some value) : name ∈ environment.map Prod.fst := by
  unfold DeterministicEquations.Env.lookup at found
  cases search : List.find? (fun binding => binding.1 == name) environment with
  | none => rw [search] at found; cases found
  | some binding =>
      have member := List.mem_of_find?_eq_some search
      have isName := List.find?_some search
      simp only [beq_iff_eq] at isName
      exact isName ▸ List.mem_map_of_mem (f := Prod.fst) member

mutual

/-- **A match binds the variables of the pattern**, in order. -/
theorem matchTerm_keys : ∀ (term value : EngineTerm) (bindings : Env),
    matchTerm term value = some bindings →
      bindings.map Prod.fst = DeterministicEquations.patternVars term
  | .var _, _, _, matched => by
      rw [DeterministicEquations.matchTerm_var matched]
      simp [DeterministicEquations.patternVars]
  | .sym _, _, _, matched => by
      rw [(DeterministicEquations.matchTerm_sym matched).2]
      simp [DeterministicEquations.patternVars]
  | .lit _, _, _, matched => by
      rw [(DeterministicEquations.matchTerm_lit matched).2]
      simp [DeterministicEquations.patternVars]
  | .expr items, _, bindings, matched => by
      obtain ⟨values, -, inner⟩ := DeterministicEquations.matchTerm_expr matched
      simpa [DeterministicEquations.patternVars] using matchTerms_keys items values bindings inner
  | .list items, _, bindings, matched => by
      obtain ⟨values, -, inner⟩ := DeterministicEquations.matchTerm_list matched
      simpa [DeterministicEquations.patternVars] using matchTerms_keys items values bindings inner

theorem matchTerms_keys : ∀ (items values : List EngineTerm) (bindings : Env),
    matchTerms items values = some bindings → bindings.map Prod.fst = patternVarsList items
  | [], _, _, matched => by
      rw [(DeterministicEquations.matchTerms_nil matched).2]
      simp [patternVarsList]
  | first :: rest, _, _, matched => by
      obtain ⟨value, others, left, right, -, firstMatched, restMatched, rfl⟩ :=
        DeterministicEquations.matchTerms_cons matched
      simp [patternVarsList, matchTerm_keys first value left firstMatched,
        matchTerms_keys rest others right restMatched]

end

mutual

/-- **A match of the engine is an instance of the pattern**: under the
assignment of an environment that holds the bindings of the match, the
pattern is the datum of the matched value. -/
theorem inst_pattern (N : Spelling) (names : List String) (environment : Env) :
    ∀ (term value : EngineTerm) (bindings : Env), matchTerm term value = some bindings →
      (∀ binding ∈ bindings, binding.1 ∈ names ∧ environment.lookup binding.1 = some binding.2) →
        inst (assignment N names environment) (pattern N names term) = datum N value
  | .var name, value, _, matched, held => by
      rw [DeterministicEquations.matchTerm_var matched] at held
      obtain ⟨member, found⟩ := held (name, value) (List.mem_singleton.mpr rfl)
      simp only [pattern, Dedukti.inst_var]
      exact assignment_idxOf N member found
  | .sym _, _, _, matched, _ => by
      rw [(DeterministicEquations.matchTerm_sym matched).1]
      simp only [pattern, datum, inst_tag, inst_write]
  | .lit _, _, _, matched, _ => by
      rw [(DeterministicEquations.matchTerm_lit matched).1]
      simp only [pattern, datum, inst_literal]
  | .expr items, _, bindings, matched, held => by
      obtain ⟨values, rfl, inner⟩ := DeterministicEquations.matchTerm_expr matched
      simp only [pattern, datum, inst_tag, inst_cells]
      rw [inst_patterns N names environment items values bindings inner held]
  | .list items, _, bindings, matched, held => by
      obtain ⟨values, rfl, inner⟩ := DeterministicEquations.matchTerm_list matched
      simp only [pattern, datum, inst_tag, inst_cells]
      rw [inst_patterns N names environment items values bindings inner held]

theorem inst_patterns (N : Spelling) (names : List String) (environment : Env) :
    ∀ (items values : List EngineTerm) (bindings : Env), matchTerms items values = some bindings →
      (∀ binding ∈ bindings, binding.1 ∈ names ∧ environment.lookup binding.1 = some binding.2) →
        (patterns N names items).map (inst (assignment N names environment)) = data N values
  | [], _, _, matched, _ => by
      rw [(DeterministicEquations.matchTerms_nil matched).1]
      rfl
  | first :: rest, _, _, matched, held => by
      obtain ⟨value, others, left, right, rfl, firstMatched, restMatched, rfl⟩ :=
        DeterministicEquations.matchTerms_cons matched
      simp only [patterns, List.map_cons, data]
      rw [inst_pattern N names environment first value left firstMatched
          (fun binding member => held binding (List.mem_append_left _ member)),
        inst_patterns N names environment rest others right restMatched
          (fun binding member => held binding (List.mem_append_right _ member))]

end

/-- What a selected equation is: an equation of the program with the head of
the call, whose left side matches the arguments. -/
theorem select_spec {program : Program} {head : String} {arguments : List EngineTerm}
    {equation : Equation} {bindings : Env}
    (selected : program.select head arguments = some (equation, bindings)) :
    equation ∈ program ∧ equation.head = head ∧
      matchTerms equation.params arguments = some bindings := by
  obtain ⟨candidate, member, found⟩ := List.exists_of_findSome?_eq_some selected
  split at found
  · next condition =>
    cases matched : matchTerms candidate.params arguments with
    | none => simp [matched] at found
    | some result =>
        simp only [matched, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl⟩ := found
        exact ⟨member, condition.1, matched⟩
  · cases found

/-- A program defines the head of each of its equations. -/
theorem defines_of_mem {program : Program} {equation : Equation} (member : equation ∈ program) :
    program.defines equation.head = true :=
  List.any_eq_true.mpr ⟨equation, member, by simp⟩

/-- The slots of a selected equation, under its match: each binding of the
match is at a slot, and the match binds it to its value. -/
theorem selected_bindings {program : Program} (leftLinear : LeftLinear program) {head : String}
    {arguments : List EngineTerm} {equation : Equation} {bindings : Env}
    (selected : program.select head arguments = some (equation, bindings)) :
    ∀ binding ∈ bindings, binding.1 ∈ slots equation ∧ bindings.lookup binding.1 = some binding.2 := by
  obtain ⟨member, -, matched⟩ := select_spec selected
  have keys := matchTerms_keys _ _ _ matched
  have distinct : (bindings.map Prod.fst).Nodup := keys ▸ leftLinear equation member
  intro binding found
  exact ⟨by rw [slots, ← keys]; exact List.mem_map_of_mem found, lookup_of_mem distinct found⟩

/-- A name that the match of a selected equation binds is a slot of the
equation. -/
theorem selected_scoped {program : Program} {head : String} {arguments : List EngineTerm}
    {equation : Equation} {bindings : Env}
    (selected : program.select head arguments = some (equation, bindings)) :
    ∀ name value, bindings.lookup name = some value → name ∈ slots equation := by
  obtain ⟨-, -, matched⟩ := select_spec selected
  intro name value found
  rw [slots, ← matchTerms_keys _ _ _ matched]
  exact mem_keys_of_lookup found

/-! ## What a theory has to do -/

/-- **A theory dispatches a program**: a call that selects an equation
reduces to the instance of the right side of that equation under its match. -/
def Dispatches (N : Spelling) (theory : Theory) (program : Program) (primitives : List String) :
    Prop :=
  ∀ (head : String) (arguments : List EngineTerm) (equation : Equation) (bindings : Env),
    program.select head arguments = some (equation, bindings) →
      Reduces theory (callTerm head (data N arguments))
        (inst (assignment N (slots equation) bindings)
          (body N (isCalled program primitives) (slots equation) equation.body))

/-- **A theory realizes primitives of a host**: the call of a primitive on
data reduces to the datum of the value that the host returns. -/
def RealizesPrimitives (N : Spelling) (theory : Theory) (host : Host) (primitives : List String) :
    Prop :=
  ∀ head ∈ primitives, ∀ (arguments : List EngineTerm) (result : EngineTerm),
    host.primitive head arguments = .value result →
      Reduces theory (callTerm head (data N arguments)) (datum N result)

/-- **No primitive is realized by every theory.** -/
theorem realizesPrimitives_nil (N : Spelling) (theory : Theory) (host : Host) :
    RealizesPrimitives N theory host [] :=
  fun _ member => absurd member List.not_mem_nil

/-- **The rules of a program dispatch it**, when no variable occurs twice in
a left side: the selected equation's rule fires on the call, in one step. -/
theorem dispatches_of_rules (N : Spelling) {theory : Theory} {program : Program}
    {primitives : List String} (leftLinear : LeftLinear program)
    (stored : ∀ equation ∈ program, theory.rule (ruleOf N (isCalled program primitives) equation)) :
    Dispatches N theory program primitives := by
  intro head arguments equation bindings selected
  obtain ⟨member, rfl, matched⟩ := select_spec selected
  have left : inst (assignment N (slots equation) bindings)
      (ruleOf N (isCalled program primitives) equation).lhs =
        callTerm equation.head (data N arguments) := by
    simp only [ruleOf, inst_callTerm]
    rw [inst_patterns N (slots equation) bindings _ _ _ matched
      (selected_bindings leftLinear selected)]
  exact .single (step_of_rule (stored equation member) _ left rfl)

/-! ## Following the evaluator -/

theorem expression_of_called {called : String → Bool} {head : String} {rest : List EngineTerm}
    {readings : List LF.Term} (isCall : called head = true) :
    expression called (.sym head :: rest) readings = callTerm head readings.tail := by
  simp [expression, isCall]

theorem expression_of_constructor {called : String → Bool} {head : String} {rest : List EngineTerm}
    {readings : List LF.Term} (isData : called head = false) :
    expression called (.sym head :: rest) readings = tag "expr" (cells readings) := by
  simp [expression, isData]

theorem expression_of_headless {called : String → Bool} {items : List EngineTerm}
    {readings : List LF.Term} (headless : ∀ head rest, items ≠ .sym head :: rest) :
    expression called items readings = tag "expr" (cells readings) := by
  unfold expression
  split
  · next head rest => exact absurd rfl (headless head rest)
  · rfl

/-- **The evaluator, followed by reduction.**  With every fuel: a value of a
term of a right side, in an environment whose names are among the given ones,
is a reduct of the instance of the reading of the term. -/
theorem eval_reduces (N : Spelling) {theory : Theory} {program : Program} {host : Host}
    {primitives : List String} (storable : Storable program host primitives)
    (dispatches : Dispatches N theory program primitives)
    (realizes : RealizesPrimitives N theory host primitives) :
    ∀ (fuel : Nat) (names : List String) (environment : Env) (term result : EngineTerm),
      (∀ name value, environment.lookup name = some value → name ∈ names) →
      CallsWithin program.calledHeads term → ordinary term = true →
      eval program host fuel environment term = .value result →
        Reduces theory
          (inst (assignment N names environment)
            (body N (isCalled program primitives) names term))
          (datum N result) := by
  intro fuel
  induction fuel with
  | zero =>
      intro names environment term result _ _ _ evaluated
      cases evaluated
  | succ fuel ih =>
      intro names environment term result inScope confined plain evaluated
      have items : ∀ (sources values : List EngineTerm),
          (∀ source ∈ sources, CallsWithin program.calledHeads source ∧ ordinary source = true) →
          evalItemsWith (eval program host fuel) environment sources = .values values →
            List.Forall₂ (Reduces theory)
              ((bodies N (isCalled program primitives) names sources).map
                (inst (assignment N names environment)))
              (data N values) := by
        intro sources
        induction sources with
        | nil =>
            intro values _ computed
            simp only [evalItemsWith, ItemsOutcome.values.injEq] at computed
            subst computed
            exact .nil
        | cons first rest ihItems =>
            intro values each computed
            simp only [evalItemsWith] at computed
            split at computed
            · next value firstValue =>
              split at computed
              · next others restValues =>
                cases computed
                exact .cons
                  (ih names environment first value inScope (each first (List.mem_cons_self ..)).1
                    (each first (List.mem_cons_self ..)).2 firstValue)
                  (ihItems others (fun source member => each source (List.mem_cons_of_mem _ member))
                    restValues)
              · cases computed
            · cases computed
      rw [eval] at evaluated
      cases term with
      | var name =>
          simp only [evalStep] at evaluated
          split at evaluated
          · next value found =>
            obtain rfl : value = result := Outcome.value.inj evaluated
            simp only [body, Dedukti.inst_var]
            rw [assignment_idxOf N (inScope name value found) found]
          · cases evaluated
      | sym name =>
          simp only [evalStep] at evaluated
          cases evaluated
          simp only [body, datum, inst_tag, inst_write]
          exact .refl
      | lit spelling =>
          simp only [evalStep] at evaluated
          cases evaluated
          simp only [body, datum, inst_literal]
          exact .refl
      | list sources =>
          simp only [evalStep] at evaluated
          split at evaluated
          · next values computed =>
            cases evaluated
            have reduced := items sources values
              (fun source member => ⟨confined.list_child member, ordinary_list plain source member⟩)
              computed
            simp only [body, datum, inst_tag, inst_cells]
            exact reduces_tag "list" (reduces_cells reduced)
          · next outcome stopped =>
            exact absurd evaluated (DeterministicEquations.evalItemsWith_stop stopped result)
      | expr sources =>
          obtain ⟨plainHead, plainItems⟩ := ordinary_expr plain
          cases sources with
          | nil =>
              simp only [evalStep] at evaluated
              cases evaluated
              simp only [body, bodies, expression, datum, data, inst_tag, inst_cells, List.map_nil]
              exact .refl
          | cons first rest =>
              by_cases isSymbol : ∃ head, first = .sym head
              · obtain ⟨head, rfl⟩ := isSymbol
                have notSpecial : ¬ Special head rest := by
                  simpa [ordinaryHead] using plainHead
                rw [DeterministicEquations.evalStep_head notSpecial] at evaluated
                split at evaluated
                · next values computed =>
                  have reduced := items rest values
                    (fun source member => ⟨confined.expr_child (List.mem_cons_of_mem _ member),
                      plainItems source (List.mem_cons_of_mem _ member)⟩) computed
                  have inHeads : head ∈ program.calledHeads := confined.head
                  by_cases definedAt : program.definesAt head values.length = true
                  · rw [applyWith, if_pos definedAt] at evaluated
                    cases selected : program.select head values with
                    | none =>
                        rw [selected] at evaluated
                        cases evaluated
                    | some pair =>
                        obtain ⟨equation, bindings⟩ := pair
                        rw [selected] at evaluated
                        obtain ⟨member, sameHead, -⟩ := select_spec selected
                        have isCall : isCalled program primitives head = true := by
                          simp [isCalled, ← sameHead, defines_of_mem member]
                        have inner := ih (slots equation) bindings equation.body result
                          (selected_scoped selected)
                          (DeterministicEquations.Program.calledHeads_body member)
                          (storable.ordinary equation member) evaluated
                        simp only [body, bodies, expression_of_called isCall, List.tail_cons,
                          inst_callTerm]
                        exact ((reduces_callTerm head reduced).trans
                          (dispatches head values equation bindings selected)).trans inner
                  · have notAt : program.definesAt head values.length = false := by
                      simpa using definedAt
                    by_cases defined : program.defines head = true
                    · rw [applyWith, if_neg definedAt, if_pos defined] at evaluated
                      cases evaluated
                    · have undefined : program.defines head = false := by simpa using defined
                      rw [DeterministicEquations.applyWith_primitive notAt undefined] at evaluated
                      cases primitive : host.primitive head values with
                      | fault =>
                          rw [primitive] at evaluated
                          cases evaluated
                      | value returned =>
                          rw [primitive] at evaluated
                          obtain rfl : returned = result := Outcome.value.inj evaluated
                          have inPrimitives : head ∈ primitives := by
                            by_contra absent
                            have unhandled := storable.constructs head inHeads undefined absent values
                            rw [unhandled] at primitive
                            cases primitive
                          have isCall : isCalled program primitives head = true := by
                            simp [isCalled, inPrimitives]
                          simp only [body, bodies, expression_of_called isCall, List.tail_cons,
                            inst_callTerm]
                          exact (reduces_callTerm head reduced).trans
                            (realizes head inPrimitives values returned primitive)
                      | unhandled =>
                          rw [primitive] at evaluated
                          cases evaluated
                          have absent : head ∉ primitives := fun inPrimitives =>
                            storable.handled head inPrimitives values primitive
                          have isData : isCalled program primitives head = false := by
                            simp [isCalled, undefined, absent]
                          simp only [body, bodies, expression_of_constructor isData, datum, data,
                            inst_tag, inst_cells, List.map_cons, inst_write]
                          exact reduces_tag "expr" (reduces_cells (.cons .refl reduced))
                · next outcome stopped =>
                  exact absurd evaluated (DeterministicEquations.evalItemsWith_stop stopped result)
              · have headless : ∀ head, first ≠ .sym head := fun head same => isSymbol ⟨head, same⟩
                rw [DeterministicEquations.evalStep_items headless] at evaluated
                split at evaluated
                · next values computed =>
                  cases evaluated
                  have reduced := items (first :: rest) values
                    (fun source member => ⟨confined.expr_child member, plainItems source member⟩)
                    computed
                  have shape : ∀ head tail, first :: rest ≠ .sym head :: tail :=
                    fun head tail same => headless head (List.cons.inj same).1
                  simp only [body, expression_of_headless shape, datum, inst_tag, inst_cells]
                  exact reduces_tag "expr" (reduces_cells reduced)
                · next outcome stopped =>
                  exact absurd evaluated (DeterministicEquations.evalItemsWith_stop stopped result)

/-- **A value that the engine returns for a call is a reduct of the call**,
in every theory that dispatches the program and realizes its primitives. -/
theorem applies_reduces (N : Spelling) {theory : Theory} {program : Program} {host : Host}
    {primitives : List String} (storable : Storable program host primitives)
    (dispatches : Dispatches N theory program primitives)
    (realizes : RealizesPrimitives N theory host primitives) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) :
    Reduces theory (callTerm head (data N arguments)) (datum N result) := by
  obtain ⟨fuel, computed⟩ := applies
  rw [DeterministicEquations.apply, applyWith, if_pos defined] at computed
  cases selected : program.select head arguments with
  | none =>
      rw [selected] at computed
      cases computed
  | some pair =>
      obtain ⟨equation, bindings⟩ := pair
      rw [selected] at computed
      obtain ⟨member, -, -⟩ := select_spec selected
      exact (dispatches head arguments equation bindings selected).trans
        (eval_reduces N storable dispatches realizes fuel (slots equation) bindings equation.body
          result (selected_scoped selected)
          (DeterministicEquations.Program.calledHeads_body member)
          (storable.ordinary equation member) computed)

/-- **The engine's value is reached**: for a program of the class that calls
no primitive of its host, a value that the engine returns for a call is a
reduct of the call in the theory of the table of the program.  The equations
of one head may overlap. -/
theorem stored_value_reached (N : Spelling) {program : Program} {host : Host}
    (storable : Storable program host []) {head : String} {arguments : List EngineTerm}
    {result : EngineTerm} (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) :
    Reduces (programTheory (programRules N program [])) (callTerm head (data N arguments))
      (datum N result) :=
  applies_reduces N storable
    (dispatches_of_rules N storable.leftLinear fun _ member => ruleOf_mem member)
    (realizesPrimitives_nil N _ host) defined applies

#print axioms matchTerm_keys
#print axioms inst_pattern
#print axioms select_spec
#print axioms dispatches_of_rules
#print axioms eval_reduces
#print axioms applies_reduces
#print axioms stored_value_reached

end Mettapedia.Logic.HostingStyles.StoredPrograms
