import Mettapedia.Logic.HostingStyles.SpacesAndRegions.Candidate
import Mettapedia.Logic.HostingStyles.StoredPrograms.Running

/-!
# The candidate of spaces and regions runs stored programs

An equation program of the shared engine is stored as a table of rules
(`Stores`).  The candidate with a run at the root and the member of the
ambient family run such a table.  This module carries that over to the
candidate of spaces and regions, whose root steps are headed.

* **The table of a stored program has no variable as a left side**
  (`stores_headed`; for the table of every program, `programRules_headed`):
  every rule rewrites a call.  So headed root steps lose nothing of it.
* **The plain atom of a call, at the ambient space of the table**
  (`callAtom`, `valueAtom`): it reaches the atom of the value that the engine
  returns (`callAtom_reaches`); the atom of a value has no transition
  (`valueAtom_normal`); if the theory of the table is orthogonal, every atom
  without transition that is reached is that one (`callAtom_unique`); so the
  atom of a call reaches the atom of a term exactly when the engine returns
  that term (`callAtom_reaches_iff`).
* **A call inside a contained run, at every ambient space** (`callRegion`,
  `valueRegion`): the same four statements (`callRegion_reaches`,
  `valueRegion_normal`, `callRegion_unique`, `callRegion_reaches_iff`).  The
  ambient space is in none of them.
* For a call that the engine answers with the encoding of what a function
  returns: `callAtom_result_iff`, `callRegion_result_iff`; for an authored
  computation: `authored_callAtom_iff`, `authored_callRegion_iff`.

Positive: unary addition, by a run of its table in Lean's kernel
(`addition_atom_reaches`, `addition_region_reaches`).  Negative: the atom of
that call reaches the atom of no other number (`addition_atom_not_two`); and
a call in a run in the empty space has no transition at the ambient space of
the table (`addition_call_contained`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Authored (AuthoredComputation)
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (Program Host Applies)
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.TypingExamples (noPrimitives)
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Reduces patternVars usesOnly)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles (runPattern)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory atomAt ruleSpace closedAtom atomInterface rootStep_program_inv
    atomAt_ne_apply)
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.AmbientRegions
open Mettapedia.Logic.HostingStyles.StoredPrograms

variable {admits : Pattern → Bool}

/-! ## The atom of a term and its run, as closed atoms of the candidate -/

/-- The atom of a λΠ term, as a closed atom of the candidate. -/
def termAtom (term : LF.Term) : Contexts.Term spacesAndRegions closedAtom :=
  atomTermIn (presentation := spacesAndRegionsPresentation) spacesAndRegions_carriesAtoms 0 term

/-- The run of the atom of a λΠ term in the space of a list of rules, as a
closed atom of the candidate. -/
def termRegion (rules : List RewriteRule) (term : LF.Term) :
    Contexts.Term spacesAndRegions closedAtom :=
  runAtomIn (presentation := spacesAndRegionsPresentation) spacesAndRegions_declaresRun
    spacesAndRegions_carriesAtoms rules 0 term

@[simp] theorem termAtom_val (term : LF.Term) : (termAtom term).1 = atomAt 0 term := rfl

@[simp] theorem termRegion_val (rules : List RewriteRule) (term : LF.Term) :
    (termRegion rules term).1 = runPattern (ruleSpace rules) (atomAt 0 term) :=
  rfl

theorem termAtom_injective : Function.Injective termAtom :=
  atomTermIn_injective (presentation := spacesAndRegionsPresentation)
    spacesAndRegions_carriesAtoms 0

theorem termRegion_injective (rules : List RewriteRule) : Function.Injective (termRegion rules) :=
  runAtomIn_injective (presentation := spacesAndRegionsPresentation) spacesAndRegions_declaresRun
    spacesAndRegions_carriesAtoms rules 0

/-- **Negative**: the atom of a term is the run of no term. -/
theorem termAtom_ne_termRegion (rules : List RewriteRule) (term other : LF.Term) :
    termAtom term ≠ termRegion rules other := by
  intro same
  have patterns : atomAt 0 term = runPattern (ruleSpace rules) (atomAt 0 other) :=
    congrArg Subtype.val same
  exact atomAt_ne_apply (by decide) 0 term _ patterns

/-- **The transitions of the atom of a term, at the ambient space of a list
of first-order rules with bound right sides none of whose left sides is a
variable**: the atoms of its steps by those rules. -/
theorem termAtom_termStep_iff (admitsAtoms : AdmitsAtoms admits) {rules : List RewriteRule}
    (runnable : RunnableEquations rules)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index) {source : LF.Term}
    {target : Contexts.Term spacesAndRegions closedAtom} :
    (spacesAndRegionsTheory admits (ruleSpace rules)).rewrites (termAtom source) target ↔
      ∃ next, Dedukti.Step (programTheory rules) source next ∧ target = termAtom next :=
  termStep_atomTermIn_iff (presentation := spacesAndRegionsPresentation)
    spacesAndRegions_carriesAtoms spacesAndRegions_quoteDropOnly spacesAndRegions_quoteDropSorted
    spacesAndRegions_namesOnlyDropped
    (spacesAndRegions_atom_step_iff admitsAtoms runnable.1 runnable.2 headed
      (theory := programTheory rules) (fun _ => Iff.rfl) (fun _ => rfl)) (depth := 0)

/-- **The transitions of the run of the atom of a term in the space of such a
list, at every ambient space**: the runs of the atoms of its steps by those
rules. -/
theorem termRegion_termStep_iff (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    {rules : List RewriteRule} (runnable : RunnableEquations rules)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index) {source : LF.Term}
    {target : Contexts.Term spacesAndRegions closedAtom} :
    (spacesAndRegionsTheory admits ambientSpace).rewrites (termRegion rules source) target ↔
      ∃ next, Dedukti.Step (programTheory rules) source next ∧ target = termRegion rules next :=
  termStep_runAtomIn_iff (presentation := spacesAndRegionsPresentation)
    spacesAndRegions_declaresRun spacesAndRegions_carriesAtoms spacesAndRegions_quoteDropOnly
    spacesAndRegions_quoteDropSorted spacesAndRegions_namesOnlyDropped
    (spacesAndRegions_runAtom_step_iff admitsAtoms ambientSpace runnable.1 runnable.2 headed
      (theory := programTheory rules) (fun _ => Iff.rfl) (fun _ => rfl)) (depth := 0)

/-- A reduction of the theory of a list of rules is a reduction of the member
at the space of the list, between the plain atoms. -/
theorem termAtom_reaches (admitsAtoms : AdmitsAtoms admits) {rules : List RewriteRule}
    (runnable : RunnableEquations rules)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index) {source target : LF.Term}
    (reduces : Reduces (programTheory rules) source target) :
    (spacesAndRegionsTheory admits (ruleSpace rules)).Reaches (termAtom source)
      (termAtom target) := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih =>
      exact ih.tail ((termAtom_termStep_iff admitsAtoms runnable headed).mpr ⟨_, step, rfl⟩)

/-- What the atom of a term reaches in the member at the space of a list of
rules is the atom of a reduct of the term. -/
theorem exists_reduces_of_termAtom_reaches (admitsAtoms : AdmitsAtoms admits)
    {rules : List RewriteRule} (runnable : RunnableEquations rules)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index) {source : LF.Term}
    {target : Contexts.Term spacesAndRegions closedAtom}
    (reaches : (spacesAndRegionsTheory admits (ruleSpace rules)).Reaches (termAtom source) target) :
    ∃ next, Reduces (programTheory rules) source next ∧ target = termAtom next := by
  induction reaches with
  | refl => exact ⟨source, .refl, rfl⟩
  | tail _ step ih =>
      obtain ⟨middle, reduces, rfl⟩ := ih
      obtain ⟨next, sourceStep, rfl⟩ :=
        (termAtom_termStep_iff admitsAtoms runnable headed).mp step
      exact ⟨next, reduces.tail sourceStep, rfl⟩

/-- A reduction of the theory of a list of rules is a reduction of every
member, between the runs in the space of the list. -/
theorem termRegion_reaches (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    {rules : List RewriteRule} (runnable : RunnableEquations rules)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index) {source target : LF.Term}
    (reduces : Reduces (programTheory rules) source target) :
    (spacesAndRegionsTheory admits ambientSpace).Reaches (termRegion rules source)
      (termRegion rules target) := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih =>
      exact ih.tail
        ((termRegion_termStep_iff admitsAtoms ambientSpace runnable headed).mpr ⟨_, step, rfl⟩)

/-- What the run of the atom of a term reaches, at any ambient space, is the
run of the atom of a reduct of the term. -/
theorem exists_reduces_of_termRegion_reaches (admitsAtoms : AdmitsAtoms admits)
    (ambientSpace : Pattern) {rules : List RewriteRule} (runnable : RunnableEquations rules)
    (headed : ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index) {source : LF.Term}
    {target : Contexts.Term spacesAndRegions closedAtom}
    (reaches : (spacesAndRegionsTheory admits ambientSpace).Reaches (termRegion rules source)
      target) :
    ∃ next, Reduces (programTheory rules) source next ∧ target = termRegion rules next := by
  induction reaches with
  | refl => exact ⟨source, .refl, rfl⟩
  | tail _ step ih =>
      obtain ⟨middle, reduces, rfl⟩ := ih
      obtain ⟨next, sourceStep, rfl⟩ :=
        (termRegion_termStep_iff admitsAtoms ambientSpace runnable headed).mp step
      exact ⟨next, reduces.tail sourceStep, rfl⟩

/-! ## The table of a stored program has no variable as a left side -/

/-- A rule that rewrites a call has no variable as its left side. -/
theorem lhs_ne_var_of_rewritesCall {rule : RewriteRule} (rooted : rewritesCall rule = true)
    (index : Nat) : rule.lhs ≠ .var index := by
  intro same
  obtain ⟨kind, head, argument, shape, -⟩ := rewritesCall_shape rooted
  rw [shape] at same
  cases same

/-- **The table of every equation program has no variable as a left side.** -/
theorem programRules_headed (N : Spelling) (program : Program) (primitives : List String) :
    ∀ rule ∈ programRules N program primitives, ∀ index : Nat, rule.lhs ≠ .var index :=
  fun rule member => lhs_ne_var_of_rewritesCall (programRules_rewriteCalls N program primitives
    rule member)

variable {N : Spelling} {rules : List RewriteRule} {program : Program} {host : Host}
  {primitives : List String}

/-- **A table that stores a program has no variable as a left side.** -/
theorem stores_headed (stores : Stores N rules program host primitives) :
    ∀ rule ∈ rules, ∀ index : Nat, rule.lhs ≠ .var index :=
  fun rule member => lhs_ne_var_of_rewritesCall (stores.rooted rule member)

/-- **Negative**: a rule whose left side is a variable rewrites no call. -/
theorem variableRule_not_rewritesCall (index : Nat) (right : LF.Term) :
    rewritesCall ⟨.var index, right⟩ = false :=
  rfl

/-! ## The plain atom of a call, at the ambient space of the table -/

/-- **The plain atom of a call**: a closed atom of the candidate, with no
run. -/
def callAtom (N : Spelling) (head : String) (arguments : List EngineTerm) :
    Contexts.Term spacesAndRegions closedAtom :=
  termAtom (callTerm head (data N arguments))

/-- **The atom of a value.** -/
def valueAtom (N : Spelling) (value : EngineTerm) : Contexts.Term spacesAndRegions closedAtom :=
  termAtom (datum N value)

/-- The atom of a value determines the value, when the spelling identifies no
two names. -/
theorem valueAtom_injective {N : Spelling} (injective : Function.Injective N.write) :
    Function.Injective (valueAtom N) :=
  fun _ _ same => datum_injective injective (termAtom_injective same)

/-- **Negative**: the atom of a call is the atom of no value. -/
theorem callAtom_ne_valueAtom (N : Spelling) (head : String) (arguments : List EngineTerm)
    (value : EngineTerm) : callAtom N head arguments ≠ valueAtom N value :=
  fun same => datum_ne_callTerm N value head _ (termAtom_injective same).symm

/-- **In the member at the space of the table, the atom of a call reaches the
atom of the value that the engine returns.** -/
theorem callAtom_reaches (admitsAtoms : AdmitsAtoms admits)
    (stores : Stores N rules program host primitives) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) :
    (spacesAndRegionsTheory admits (ruleSpace rules)).Reaches (callAtom N head arguments)
      (valueAtom N result) :=
  termAtom_reaches admitsAtoms stores.runnable (stores_headed stores)
    (stores.reduces defined applies)

/-- **The atom of a value has no transition** in the member at the space of
the table. -/
theorem valueAtom_normal (admitsAtoms : AdmitsAtoms admits)
    (stores : Stores N rules program host primitives) (value : EngineTerm)
    (target : Contexts.Term spacesAndRegions closedAtom) :
    ¬ (spacesAndRegionsTheory admits (ruleSpace rules)).rewrites (valueAtom N value) target := by
  intro step
  obtain ⟨next, sourceStep, -⟩ :=
    (termAtom_termStep_iff admitsAtoms stores.runnable (stores_headed stores)).mp step
  exact stores.value_normal value next sourceStep

/-- **Every atom without transition that the atom of a call reaches is the
atom of the value that the engine returns**, when the theory of the table is
orthogonal. -/
theorem callAtom_unique (admitsAtoms : AdmitsAtoms admits)
    (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result)
    {target : Contexts.Term spacesAndRegions closedAtom}
    (reaches : (spacesAndRegionsTheory admits (ruleSpace rules)).Reaches
      (callAtom N head arguments) target)
    (normal : ∀ next, ¬ (spacesAndRegionsTheory admits (ruleSpace rules)).rewrites target next) :
    target = valueAtom N result := by
  obtain ⟨normalForm, reduces, rfl⟩ :=
    exists_reduces_of_termAtom_reaches admitsAtoms stores.runnable (stores_headed stores) reaches
  have isNormal : IsNormal (Dedukti.Step (programTheory rules)) normalForm := fun next step =>
    normal (termAtom next)
      ((termAtom_termStep_iff admitsAtoms stores.runnable (stores_headed stores)).mpr
        ⟨next, step, rfl⟩)
  rw [stores.normalForm_unique orthogonal defined applies reduces isNormal]
  rfl

/-- **The atom of a call reaches the atom of a term exactly when the engine
returns that term**, for a call on which the engine returns a value. -/
theorem callAtom_reaches_iff (admitsAtoms : AdmitsAtoms admits)
    (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    {head : String} {arguments : List EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (total : ∃ value, Applies program host head arguments value) (result : EngineTerm) :
    (spacesAndRegionsTheory admits (ruleSpace rules)).Reaches (callAtom N head arguments)
        (valueAtom N result) ↔
      Applies program host head arguments result := by
  refine ⟨fun reaches => ?_, callAtom_reaches admitsAtoms stores defined⟩
  obtain ⟨value, applies⟩ := total
  have same := callAtom_unique admitsAtoms stores orthogonal defined applies reaches
    (valueAtom_normal admitsAtoms stores result)
  rw [valueAtom_injective injective same]
  exact applies

/-- **A call that the engine answers with the encoding of what a function
returns**: the atom of the call reaches the atom of an encoded result exactly
when the function returns that result. -/
theorem callAtom_result_iff (admitsAtoms : AdmitsAtoms admits)
    (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    {Result : Type} {encodeResult : Result → EngineTerm}
    (encodeInjective : Function.Injective encodeResult) {head : String}
    {arguments : List EngineTerm}
    (defined : program.definesAt head arguments.length = true) {returned : Result}
    (applies : Applies program host head arguments (encodeResult returned)) (result : Result) :
    (spacesAndRegionsTheory admits (ruleSpace rules)).Reaches (callAtom N head arguments)
        (valueAtom N (encodeResult result)) ↔
      returned = result := by
  constructor
  · intro reaches
    exact (encodeInjective (valueAtom_injective injective
      (callAtom_unique admitsAtoms stores orthogonal defined applies reaches
        (valueAtom_normal admitsAtoms stores _)))).symm
  · rintro rfl
    exact callAtom_reaches admitsAtoms stores defined applies

/-- **An authored computation, run by the member at the space of its table**:
the atom of the call of a query reaches the atom of an encoded answer exactly
when the relation holds of the query and the answer. -/
theorem authored_callAtom_iff (admitsAtoms : AdmitsAtoms admits) {Query Answer : Type}
    (C : AuthoredComputation Query Answer) (stores : Stores N rules C.program C.host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    (query : Query) (defined : C.program.definesAt C.head (C.encodeQuery query).length = true)
    (answer : Answer) :
    (spacesAndRegionsTheory admits (ruleSpace rules)).Reaches
        (callAtom N C.head (C.encodeQuery query)) (valueAtom N (C.encodeAnswer (some answer))) ↔
      C.relation query answer := by
  have total : ∃ value, Applies C.program C.host C.head (C.encodeQuery query) value := by
    by_cases related : ∃ found, C.relation query found
    · obtain ⟨found, holds⟩ := related
      exact ⟨_, (C.accepts query found).mpr holds⟩
    · exact ⟨_, (C.refuses query).mpr related⟩
  exact (callAtom_reaches_iff admitsAtoms stores orthogonal injective defined total _).trans
    (C.accepts query answer)

/-! ## A call inside a contained run, at every ambient space -/

/-- **A call inside a contained run**: the run of the atom of the call in the
space of the table. -/
def callRegion (N : Spelling) (rules : List RewriteRule) (head : String)
    (arguments : List EngineTerm) : Contexts.Term spacesAndRegions closedAtom :=
  termRegion rules (callTerm head (data N arguments))

/-- **A value inside a contained run.** -/
def valueRegion (N : Spelling) (rules : List RewriteRule) (value : EngineTerm) :
    Contexts.Term spacesAndRegions closedAtom :=
  termRegion rules (datum N value)

/-- The run of a value determines the value, when the spelling identifies no
two names. -/
theorem valueRegion_injective {N : Spelling} (injective : Function.Injective N.write)
    (rules : List RewriteRule) : Function.Injective (valueRegion N rules) :=
  fun _ _ same => datum_injective injective (termRegion_injective rules same)

/-- **Negative**: the run of a call is the run of no value. -/
theorem callRegion_ne_valueRegion (N : Spelling) (rules : List RewriteRule) (head : String)
    (arguments : List EngineTerm) (value : EngineTerm) :
    callRegion N rules head arguments ≠ valueRegion N rules value :=
  fun same => datum_ne_callTerm N value head _ (termRegion_injective rules same).symm

/-- **At every ambient space, the run of a call in the space of the table
reaches the run of the value that the engine returns.** -/
theorem callRegion_reaches (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    (stores : Stores N rules program host primitives) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) :
    (spacesAndRegionsTheory admits ambientSpace).Reaches (callRegion N rules head arguments)
      (valueRegion N rules result) :=
  termRegion_reaches admitsAtoms ambientSpace stores.runnable (stores_headed stores)
    (stores.reduces defined applies)

/-- **The run of a value has no transition**, at every ambient space. -/
theorem valueRegion_normal (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    (stores : Stores N rules program host primitives) (value : EngineTerm)
    (target : Contexts.Term spacesAndRegions closedAtom) :
    ¬ (spacesAndRegionsTheory admits ambientSpace).rewrites (valueRegion N rules value) target := by
  intro step
  obtain ⟨next, sourceStep, -⟩ := (termRegion_termStep_iff admitsAtoms ambientSpace
    stores.runnable (stores_headed stores)).mp step
  exact stores.value_normal value next sourceStep

/-- **Every term without transition that the run of a call reaches is the run
of the value that the engine returns**, at every ambient space, when the
theory of the table is orthogonal. -/
theorem callRegion_unique (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result)
    {target : Contexts.Term spacesAndRegions closedAtom}
    (reaches : (spacesAndRegionsTheory admits ambientSpace).Reaches
      (callRegion N rules head arguments) target)
    (normal : ∀ next, ¬ (spacesAndRegionsTheory admits ambientSpace).rewrites target next) :
    target = valueRegion N rules result := by
  obtain ⟨normalForm, reduces, rfl⟩ := exists_reduces_of_termRegion_reaches admitsAtoms
    ambientSpace stores.runnable (stores_headed stores) reaches
  have isNormal : IsNormal (Dedukti.Step (programTheory rules)) normalForm := fun next step =>
    normal (termRegion rules next)
      ((termRegion_termStep_iff admitsAtoms ambientSpace stores.runnable
        (stores_headed stores)).mpr ⟨next, step, rfl⟩)
  rw [stores.normalForm_unique orthogonal defined applies reduces isNormal]
  rfl

/-- **The run of a call reaches the run of a term exactly when the engine
returns that term**, at every ambient space, for a call on which the engine
returns a value. -/
theorem callRegion_reaches_iff (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    {head : String} {arguments : List EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (total : ∃ value, Applies program host head arguments value) (result : EngineTerm) :
    (spacesAndRegionsTheory admits ambientSpace).Reaches (callRegion N rules head arguments)
        (valueRegion N rules result) ↔
      Applies program host head arguments result := by
  refine ⟨fun reaches => ?_, callRegion_reaches admitsAtoms ambientSpace stores defined⟩
  obtain ⟨value, applies⟩ := total
  have same := callRegion_unique admitsAtoms ambientSpace stores orthogonal defined applies reaches
    (valueRegion_normal admitsAtoms ambientSpace stores result)
  rw [valueRegion_injective injective rules same]
  exact applies

/-- **A call that the engine answers with the encoding of what a function
returns, inside a contained run**: at every ambient space the run of the call
reaches the run of an encoded result exactly when the function returns that
result. -/
theorem callRegion_result_iff (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    {Result : Type} {encodeResult : Result → EngineTerm}
    (encodeInjective : Function.Injective encodeResult) {head : String}
    {arguments : List EngineTerm}
    (defined : program.definesAt head arguments.length = true) {returned : Result}
    (applies : Applies program host head arguments (encodeResult returned)) (result : Result) :
    (spacesAndRegionsTheory admits ambientSpace).Reaches (callRegion N rules head arguments)
        (valueRegion N rules (encodeResult result)) ↔
      returned = result := by
  constructor
  · intro reaches
    exact (encodeInjective (valueRegion_injective injective rules
      (callRegion_unique admitsAtoms ambientSpace stores orthogonal defined applies reaches
        (valueRegion_normal admitsAtoms ambientSpace stores _)))).symm
  · rintro rfl
    exact callRegion_reaches admitsAtoms ambientSpace stores defined applies

/-- **An authored computation, run inside a contained run**: at every ambient
space the run of the call of a query reaches the run of an encoded answer
exactly when the relation holds of the query and the answer. -/
theorem authored_callRegion_iff (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    {Query Answer : Type} (C : AuthoredComputation Query Answer)
    (stores : Stores N rules C.program C.host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    (query : Query) (defined : C.program.definesAt C.head (C.encodeQuery query).length = true)
    (answer : Answer) :
    (spacesAndRegionsTheory admits ambientSpace).Reaches
        (callRegion N rules C.head (C.encodeQuery query))
        (valueRegion N rules (C.encodeAnswer (some answer))) ↔
      C.relation query answer := by
  have total : ∃ value, Applies C.program C.host C.head (C.encodeQuery query) value := by
    by_cases related : ∃ found, C.relation query found
    · obtain ⟨found, holds⟩ := related
      exact ⟨_, (C.accepts query found).mpr holds⟩
    · exact ⟨_, (C.refuses query).mpr related⟩
  exact (callRegion_reaches_iff admitsAtoms ambientSpace stores orthogonal injective defined total
    _).trans (C.accepts query answer)

/-! ## Unary addition -/

/-- The table of unary addition, with names written as constants. -/
abbrev additionTable : List RewriteRule := programRules constantSpelling additionProgram []

/-- The two arguments of the call of `add` on two and one. -/
def twoAndOne : List EngineTerm :=
  [.expr [.sym "S", .expr [.sym "S", .sym "Z"]], .expr [.sym "S", .sym "Z"]]

/-- The number three, as a value of the engine. -/
def three : EngineTerm := .expr [.sym "S", .expr [.sym "S", .expr [.sym "S", .sym "Z"]]]

/-- **Positive**: at the ambient space of the table of addition, the plain
atom of the call of `add` on two and one reaches the atom of three, by the
three steps that the table takes in Lean's kernel. -/
theorem addition_atom_reaches :
    (spacesAndRegionsTheory anySubject (ruleSpace additionTable)).Reaches
      (callAtom constantSpelling "add" twoAndOne) (valueAtom constantSpelling three) :=
  termAtom_reaches anySubject_admitsAtoms (additionProgram_storable.runnable constantSpelling)
    (programRules_headed constantSpelling additionProgram []) (reduces_of_run addition_runs)

/-- **Positive**: and at every ambient space its run in the space of the
table reaches the run of three. -/
theorem addition_region_reaches (ambientSpace : Pattern) :
    (spacesAndRegionsTheory anySubject ambientSpace).Reaches
      (callRegion constantSpelling additionTable "add" twoAndOne)
      (valueRegion constantSpelling additionTable three) :=
  termRegion_reaches anySubject_admitsAtoms ambientSpace
    (additionProgram_storable.runnable constantSpelling)
    (programRules_headed constantSpelling additionProgram []) (reduces_of_run addition_runs)

/-- **Negative**: the atom of that call does not reach the atom of two. -/
theorem addition_atom_not_two :
    ¬ (spacesAndRegionsTheory anySubject (ruleSpace additionTable)).Reaches
      (callAtom constantSpelling "add" twoAndOne)
      (valueAtom constantSpelling (.expr [.sym "S", .expr [.sym "S", .sym "Z"]])) := by
  intro reaches
  have stores := stores_of_storable constantSpelling additionProgram_storable
  obtain ⟨normalForm, reduces, same⟩ := exists_reduces_of_termAtom_reaches anySubject_admitsAtoms
    stores.runnable (stores_headed stores) reaches
  have unique := Dedukti.normal_form_unique_of_orthogonal
    (programTheory_orthogonal additionProgram_orthogonal) reduces
    (termAtom_injective same ▸ stores.value_normal _) (reduces_of_run addition_runs)
    (stores.value_normal three)
  rw [← termAtom_injective same] at unique
  revert unique
  decide

/-- **Negative, containment**: at the ambient space of the table of addition
the run of that call in the empty space has no transition.  The ambient
table does not reach into a run. -/
theorem addition_call_contained (target : Contexts.Term spacesAndRegions closedAtom) :
    ¬ (spacesAndRegionsTheory anySubject (ruleSpace additionTable)).rewrites
      (callRegion constantSpelling [] "add" twoAndOne) target := by
  intro step
  obtain ⟨next, sourceStep, -⟩ := (termRegion_termStep_iff anySubject_admitsAtoms
    (ruleSpace additionTable) (rules := [])
    ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩
    (fun _ member => absurd member List.not_mem_nil)).mp step
  have root := callTerm_step_root (theory := programTheory []) (fun _ => rfl)
    (fun _ member => absurd member List.not_mem_nil) (passive_data constantSpelling twoAndOne)
    sourceStep
  rcases rootStep_program_inv root with ⟨domain, inner, argument, shape, -⟩ |
    ⟨rule, member, -⟩
  · simp [callTerm] at shape
  · exact absurd member List.not_mem_nil

#print axioms termAtom_termStep_iff
#print axioms termRegion_termStep_iff
#print axioms termAtom_reaches
#print axioms exists_reduces_of_termAtom_reaches
#print axioms termRegion_reaches
#print axioms exists_reduces_of_termRegion_reaches
#print axioms termAtom_ne_termRegion
#print axioms lhs_ne_var_of_rewritesCall
#print axioms programRules_headed
#print axioms stores_headed
#print axioms variableRule_not_rewritesCall
#print axioms valueAtom_injective
#print axioms callAtom_ne_valueAtom
#print axioms callAtom_reaches
#print axioms valueAtom_normal
#print axioms callAtom_unique
#print axioms callAtom_reaches_iff
#print axioms callAtom_result_iff
#print axioms authored_callAtom_iff
#print axioms valueRegion_injective
#print axioms callRegion_ne_valueRegion
#print axioms callRegion_reaches
#print axioms valueRegion_normal
#print axioms callRegion_unique
#print axioms callRegion_reaches_iff
#print axioms callRegion_result_iff
#print axioms authored_callRegion_iff
#print axioms addition_atom_reaches
#print axioms addition_region_reaches
#print axioms addition_atom_not_two
#print axioms addition_call_contained

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
