import Mettapedia.Logic.HostingStyles.StoredPrograms.Simulation

/-!
# Nothing else is reached, and where the engine and the table part

A table **stores** a program (`Stores`) when it holds rules that dispatch the
program and compute its primitives, all its rules rewrite calls, and it is a
table that a space of the candidate runs.  The table of a program of the
class that calls no primitive stores it (`stores_of_storable`).

For a table that stores a program:

* a value that the engine returns for a call is a reduct of the call
  (`Stores.reduces`), and it is a normal form, as every datum
  (`Stores.value_normal`);
* **if the theory of the table is orthogonal, every normal form that the
  call reaches is that value** (`Stores.normalForm_unique`), so the call
  reaches the datum of a term exactly when the engine returns that term, for
  a call on which the engine returns a value (`Stores.reduces_iff`).

The order of evaluation does not enter: an orthogonal theory is confluent
(`Dedukti.confluent_of_orthogonal`).

## Where the two part, each with a witness

* **First match.**  With two equations for one left side the engine returns
  the value of the first, and the table reaches the values of both, two
  normal forms (`firstMatch_witness`).  The engine's value is among them: an
  overlap adds reducts and takes none away.
* **Arguments first.**  The engine evaluates an argument that the equation
  does not use; the table need not.  For `(main x) = (keep x (loop x))` the
  engine returns no value at any fuel, and the call reduces to the datum of
  its argument, its only normal form (`unusedArgument_witness`).  So the
  converse of `Stores.reduces` fails without a value from the engine.
* **A repeated variable.**  The engine binds a repeated variable at its
  first occurrence and does not compare the two values: `(same a b)` returns
  `a`.  The rule of `(same x x) = x` asks for two equal arguments, and the
  call of `same` on `a` and `b` has no step (`repeatedVariable_witness`).
  This is why the class asks that no variable occur twice.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host Env Outcome ItemsOutcome Special LeftLinear patternVarsList matchTerm
    matchTerms eval evalStep evalItemsWith applyWith Applies CallsWithin)
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.TypingExamples (noPrimitives)
open Mettapedia.GSLT.Dedukti
  (Theory RewriteRule RootStep Step Reduces inst binderFree usesOnly orthogonalCheck
    orthogonal_of_check normal_form_unique_of_orthogonal)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (step_of_rule not_confluent_of_fork)
open Mettapedia.Logic.Relation (IsNormal Confluent)
open Mettapedia.Logic.HostingStyles.AtomsReduce (RunnableEquations programTheory rootStep_program_inv)

/-! ## A table that stores a program -/

/-- The theory of a list of rules is contained in the theory of a larger
list. -/
theorem programTheory_extends {small large : List RewriteRule}
    (contained : ∀ rule ∈ small, rule ∈ large) :
    (programTheory small).Extends (programTheory large) :=
  ⟨fun _ _ same => same, fun _ _ same => same, contained⟩

/-- **A table stores a program**, for a host and the primitives of it that
the table computes: its theory dispatches the program and realizes the
primitives, its rules rewrite calls, and it is a table of first-order rules
with bound right sides. -/
structure Stores (N : Spelling) (rules : List RewriteRule) (program : Program) (host : Host)
    (primitives : List String) : Prop where
  /-- The program is of the class. -/
  storable : Storable program host primitives
  /-- A call that selects an equation reduces to the instance of its right side. -/
  dispatches : Dispatches N (programTheory rules) program primitives
  /-- The call of a primitive on data reduces to the datum of the host's value. -/
  realizes : RealizesPrimitives N (programTheory rules) host primitives
  /-- The rules are first-order with bound right sides. -/
  runnable : RunnableEquations rules
  /-- Every rule rewrites a call. -/
  rooted : ∀ rule ∈ rules, rewritesCall rule = true

/-- **The table of a program of the class that calls no primitive of its host
stores it.** -/
theorem stores_of_storable (N : Spelling) {program : Program} {host : Host}
    (storable : Storable program host []) :
    Stores N (programRules N program []) program host [] where
  storable := storable
  dispatches := dispatches_of_rules N storable.leftLinear fun _ member => ruleOf_mem member
  realizes := realizesPrimitives_nil N _ host
  runnable := storable.runnable N
  rooted := programRules_rewriteCalls N program []

namespace Stores

variable {N : Spelling} {rules : List RewriteRule} {program : Program} {host : Host}
  {primitives : List String}

/-- **The engine's value is reached.** -/
theorem reduces (stores : Stores N rules program host primitives) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) :
    Reduces (programTheory rules) (callTerm head (data N arguments)) (datum N result) :=
  applies_reduces N stores.storable stores.dispatches stores.realizes defined applies

/-- **A datum is a normal form** of the theory of the table. -/
theorem value_normal (stores : Stores N rules program host primitives) (value : EngineTerm) :
    IsNormal (Step (programTheory rules)) (datum N value) :=
  datum_normal (fun _ => rfl) stores.rooted N value

/-- **Nothing else is reached**: if the theory of the table is orthogonal and
the engine returns a value for a call, every normal form that the call
reaches is the datum of that value. -/
theorem normalForm_unique (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) {normalForm : LF.Term}
    (reaches : Reduces (programTheory rules) (callTerm head (data N arguments)) normalForm)
    (normal : IsNormal (Step (programTheory rules)) normalForm) : normalForm = datum N result :=
  normal_form_unique_of_orthogonal orthogonal reaches normal (stores.reduces defined applies)
    (stores.value_normal result)

/-- **The call reaches the datum of a term exactly when the engine returns
that term**, for a call on which the engine returns a value, in an orthogonal
table whose spelling identifies no two names. -/
theorem reduces_iff (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    {head : String} {arguments : List EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (total : ∃ value, Applies program host head arguments value) (result : EngineTerm) :
    Reduces (programTheory rules) (callTerm head (data N arguments)) (datum N result) ↔
      Applies program host head arguments result := by
  refine ⟨fun reaches => ?_, stores.reduces defined⟩
  obtain ⟨value, applies⟩ := total
  have same := stores.normalForm_unique orthogonal defined applies reaches (stores.value_normal result)
  rw [datum_injective injective same]
  exact applies

end Stores

/-- A table that passes the test for orthogonal rule lists has an orthogonal
theory. -/
theorem programTheory_orthogonal {rules : List RewriteRule} (checked : orthogonalCheck rules = true) :
    (programTheory rules).Orthogonal :=
  orthogonal_of_check rules (fun _ member => member) (fun _ => rfl) checked

/-- **Nothing else is reached**, for a program of the class that calls no
primitive of its host and whose table passes the test for orthogonal rule
lists: every normal form that a call reaches is the datum of the value that
the engine returns for it. -/
theorem stored_normalForm_unique (N : Spelling) {program : Program} {host : Host}
    (storable : Storable program host [])
    (checked : orthogonalCheck (programRules N program []) = true) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) {normalForm : LF.Term}
    (reaches : Reduces (programTheory (programRules N program []))
      (callTerm head (data N arguments)) normalForm)
    (normal : IsNormal (Step (programTheory (programRules N program []))) normalForm) :
    normalForm = datum N result :=
  (stores_of_storable N storable).normalForm_unique (programTheory_orthogonal checked) defined
    applies reaches normal

/-! ## Steps of a call on passive arguments -/

/-- **A call on passive arguments steps at its root only.** -/
theorem callTerm_step_root {theory : Theory} (undefined : ∀ name, theory.body name = none)
    (rooted : ∀ rule, theory.rule rule → rewritesCall rule = true) {head : String}
    {arguments : List LF.Term} (quiet : ∀ argument ∈ arguments, passive argument = true)
    {target : LF.Term} (step : Step theory (callTerm head arguments) target) :
    RootStep theory (callTerm head arguments) target := by
  rcases step.app_inv with root | ⟨_, inner, -⟩ | ⟨_, inner, -⟩
  · exact root
  · exact absurd inner (passive_normal undefined rooted _ rfl _)
  · exact absurd inner (passive_normal undefined rooted _ (passive_cells quiet) _)

/-! ## First match: two equations for one left side -/

/-- Two equations for one left side: `(pick x) = A` and `(pick x) = B`. -/
def firstOrSecond : Program := [
  ⟨"first", "pick", [.var "x"], .sym "A"⟩,
  ⟨"second", "pick", [.var "x"], .sym "B"⟩]

theorem firstOrSecond_storable : Storable firstOrSecond noPrimitives [] :=
  .of_text (by decide) (hostFree_noPrimitives _)

/-- The engine returns the value of the first equation, and no other. -/
theorem firstOrSecond_engine (argument result : EngineTerm) :
    Applies firstOrSecond noPrimitives "pick" [argument] result ↔ result = .sym "A" :=
  ⟨fun applies => applies.deterministic ⟨1, rfl⟩, fun same => same ▸ ⟨1, rfl⟩⟩

/-- The table of the two equations, with names written as constants. -/
abbrev firstOrSecondRules : List RewriteRule := programRules constantSpelling firstOrSecond []

/-- **First match and table differ.**  For the call of `pick` on `c`: the
engine returns `A` and nothing else; the table reduces the call to the data
of `A` and of `B`, which are two normal forms; so its theory is not
confluent, and its table does not pass the test for orthogonal rule lists. -/
theorem firstMatch_witness :
    (∀ result, Applies firstOrSecond noPrimitives "pick" [.sym "c"] result ↔ result = .sym "A") ∧
      Reduces (programTheory firstOrSecondRules)
        (callTerm "pick" (data constantSpelling [.sym "c"])) (datum constantSpelling (.sym "A")) ∧
      Reduces (programTheory firstOrSecondRules)
        (callTerm "pick" (data constantSpelling [.sym "c"])) (datum constantSpelling (.sym "B")) ∧
      IsNormal (Step (programTheory firstOrSecondRules)) (datum constantSpelling (.sym "A")) ∧
      IsNormal (Step (programTheory firstOrSecondRules)) (datum constantSpelling (.sym "B")) ∧
      datum constantSpelling (.sym "A") ≠ datum constantSpelling (.sym "B") ∧
      ¬ Confluent (Step (programTheory firstOrSecondRules)) ∧
      orthogonalCheck firstOrSecondRules = false := by
  have stores := stores_of_storable constantSpelling firstOrSecond_storable
  have first : Reduces (programTheory firstOrSecondRules)
      (callTerm "pick" (data constantSpelling [.sym "c"])) (datum constantSpelling (.sym "A")) :=
    stores.reduces (by decide) ((firstOrSecond_engine _ _).mpr rfl)
  have second : Reduces (programTheory firstOrSecondRules)
      (callTerm "pick" (data constantSpelling [.sym "c"])) (datum constantSpelling (.sym "B")) :=
    .single (step_of_rule
      (rule := ruleOf constantSpelling (isCalled firstOrSecond []) ⟨"second", "pick", [.var "x"], .sym "B"⟩)
      (show _ ∈ firstOrSecondRules by decide) (fun _ => datum constantSpelling (.sym "c"))
      (by decide) (by decide))
  have apart : datum constantSpelling (.sym "A") ≠ datum constantSpelling (.sym "B") := by decide
  exact ⟨fun result => firstOrSecond_engine _ result, first, second, stores.value_normal _,
    stores.value_normal _, apart,
    not_confluent_of_fork first second (stores.value_normal _) (stores.value_normal _) apart,
    by decide⟩

/-! ## Arguments first: an argument that does not end and is not used -/

/-- `(main x) = (keep x (loop x))`, `(keep x y) = x`, `(loop x) = (loop x)`. -/
def detour : Program := [
  ⟨"main", "main", [.var "x"], .expr [.sym "keep", .var "x", .expr [.sym "loop", .var "x"]]⟩,
  ⟨"keep", "keep", [.var "x", .var "y"], .var "x"⟩,
  ⟨"loop", "loop", [.var "x"], .expr [.sym "loop", .var "x"]⟩]

theorem detour_storable : Storable detour noPrimitives [] :=
  .of_text (by decide) (hostFree_noPrimitives _)

/-- The call of `loop` in the right side of `main` ends with no fuel. -/
theorem detour_loop_exhausted (argument : EngineTerm) :
    ∀ (fuel : Nat) (environment : Env), environment.lookup "x" = some argument →
      eval detour noPrimitives fuel environment (.expr [.sym "loop", .var "x"]) = .exhausted
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | fuel + 2, environment, found => by
      have item : evalItemsWith (eval detour noPrimitives (fuel + 1)) environment [.var "x"] =
          .values [argument] := by
        simp [evalItemsWith, eval, evalStep, found]
      rw [eval, DeterministicEquations.evalStep_head (by simp [Special]), item]
      exact detour_loop_exhausted argument (fuel + 1) [("x", argument)]
        (DeterministicEquations.Env.lookup_cons_self "x" argument [])

/-- **The engine returns no value for the call of `main`**: it runs out of
every fuel, evaluating the argument that `keep` does not use. -/
theorem detour_exhausted (argument : EngineTerm) :
    ∀ fuel : Nat, DeterministicEquations.apply detour noPrimitives fuel "main" [argument] =
      .exhausted
  | 0 => rfl
  | 1 => rfl
  | fuel + 2 => by
      have unfolded : DeterministicEquations.apply detour noPrimitives (fuel + 2) "main" [argument] =
          eval detour noPrimitives (fuel + 2) [("x", argument)]
            (.expr [.sym "keep", .var "x", .expr [.sym "loop", .var "x"]]) := rfl
      have items : evalItemsWith (eval detour noPrimitives (fuel + 1)) [("x", argument)]
          [.var "x", .expr [.sym "loop", .var "x"]] = .stop .exhausted := by
        have first : eval detour noPrimitives (fuel + 1) [("x", argument)] (.var "x") =
            .value argument := rfl
        simp only [evalItemsWith, first, detour_loop_exhausted argument (fuel + 1)
          [("x", argument)] (DeterministicEquations.Env.lookup_cons_self "x" argument [])]
      rw [unfolded, eval, DeterministicEquations.evalStep_head (by simp [Special]), items]

/-- The table of the three equations, with names written as constants. -/
abbrev detourRules : List RewriteRule := programRules constantSpelling detour []

/-- **Without a value from the engine the table may still reach one.**  For
the call of `main` on `a`: the program is of the class and its table passes
the test for orthogonal rule lists; the engine returns no value; the call
reduces to the datum of `a`; and that datum is the only normal form that the
call reaches. -/
theorem unusedArgument_witness :
    Storable detour noPrimitives [] ∧ orthogonalCheck detourRules = true ∧
      (∀ result, ¬ Applies detour noPrimitives "main" [.sym "a"] result) ∧
      Reduces (programTheory detourRules) (callTerm "main" (data constantSpelling [.sym "a"]))
        (datum constantSpelling (.sym "a")) ∧
      ∀ normalForm, Reduces (programTheory detourRules)
          (callTerm "main" (data constantSpelling [.sym "a"])) normalForm →
        IsNormal (Step (programTheory detourRules)) normalForm →
          normalForm = datum constantSpelling (.sym "a") := by
  have stores := stores_of_storable constantSpelling detour_storable
  have checked : orthogonalCheck detourRules = true := by decide
  have unfolds : Step (programTheory detourRules)
      (callTerm "main" (data constantSpelling [.sym "a"]))
      (callTerm "keep" [datum constantSpelling (.sym "a"),
        callTerm "loop" [datum constantSpelling (.sym "a")]]) :=
    step_of_rule (rule := ruleOf constantSpelling (isCalled detour []) ⟨"main", "main", [.var "x"],
        .expr [.sym "keep", .var "x", .expr [.sym "loop", .var "x"]]⟩)
      (show _ ∈ detourRules by decide) (fun _ => datum constantSpelling (.sym "a")) (by decide)
      (by decide)
  have keeps : Step (programTheory detourRules)
      (callTerm "keep" [datum constantSpelling (.sym "a"),
        callTerm "loop" [datum constantSpelling (.sym "a")]])
      (datum constantSpelling (.sym "a")) :=
    step_of_rule (rule := ruleOf constantSpelling (isCalled detour [])
        ⟨"keep", "keep", [.var "x", .var "y"], .var "x"⟩)
      (show _ ∈ detourRules by decide)
      (fun index => if index = 0 then datum constantSpelling (.sym "a")
        else callTerm "loop" [datum constantSpelling (.sym "a")])
      (by decide) (by decide)
  have reached : Reduces (programTheory detourRules)
      (callTerm "main" (data constantSpelling [.sym "a"])) (datum constantSpelling (.sym "a")) :=
    (Relation.ReflTransGen.single unfolds).tail keeps
  refine ⟨detour_storable, checked, fun result applies => ?_, reached, fun normalForm reaches normal =>
    normal_form_unique_of_orthogonal (programTheory_orthogonal checked) reaches normal reached
      (stores.value_normal _)⟩
  obtain ⟨fuel, computed⟩ := applies
  rw [detour_exhausted] at computed
  cases computed

/-! ## A repeated variable -/

/-- The table of `(same x x) = x`, with names written as constants. -/
abbrev repeatedRules : List RewriteRule := programRules constantSpelling repeated []

/-- **The engine does not compare the two values of a repeated variable, and
the rule does.**  The engine returns `a` for the call of `same` on `a` and
`b`; that call has no step in the theory of the table, so it does not reduce
to the datum of `a`. -/
theorem repeatedVariable_witness :
    Applies repeated noPrimitives "same" [.sym "a", .sym "b"] (.sym "a") ∧
      IsNormal (Step (programTheory repeatedRules))
        (callTerm "same" (data constantSpelling [.sym "a", .sym "b"])) ∧
      ¬ Reduces (programTheory repeatedRules)
        (callTerm "same" (data constantSpelling [.sym "a", .sym "b"]))
        (datum constantSpelling (.sym "a")) := by
  have normal : IsNormal (Step (programTheory repeatedRules))
      (callTerm "same" (data constantSpelling [.sym "a", .sym "b"])) := by
    intro target step
    have root := callTerm_step_root (theory := programTheory repeatedRules) (fun _ => rfl)
      (programRules_rewriteCalls constantSpelling repeated [])
      (passive_data constantSpelling [.sym "a", .sym "b"]) step
    rcases rootStep_program_inv root with ⟨domain, inner, argument, shape, -⟩ |
      ⟨rule, member, assignment, shape, -⟩
    · simp [callTerm] at shape
    · simp only [repeatedRules, programRules, repeated, List.map_cons, List.map_nil,
        List.mem_singleton] at member
      subst member
      have instance_ : inst assignment (callTerm "same" [.var 0, .var 0]) =
          callTerm "same" (data constantSpelling [.sym "a", .sym "b"]) := shape.symm
      rw [inst_callTerm] at instance_
      simp only [List.map_cons, List.map_nil, Dedukti.inst_var, callTerm, cells, data,
        LF.Term.app.injEq, true_and, and_true] at instance_
      have clash : datum constantSpelling (.sym "a") = datum constantSpelling (.sym "b") :=
        instance_.1.symm.trans instance_.2
      revert clash
      decide
  refine ⟨⟨1, rfl⟩, normal, fun reaches => ?_⟩
  have stuck := normal.reflTransGen_eq reaches
  revert stuck
  decide

#print axioms stores_of_storable
#print axioms Stores.reduces
#print axioms Stores.value_normal
#print axioms Stores.normalForm_unique
#print axioms Stores.reduces_iff
#print axioms stored_normalForm_unique
#print axioms callTerm_step_root
#print axioms firstOrSecond_engine
#print axioms firstMatch_witness
#print axioms detour_exhausted
#print axioms unusedArgument_witness
#print axioms repeatedVariable_witness

end Mettapedia.Logic.HostingStyles.StoredPrograms
