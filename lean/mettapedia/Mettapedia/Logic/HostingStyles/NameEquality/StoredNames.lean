import Mettapedia.Logic.HostingStyles.NameEquality.LibraryOver
import Mettapedia.Logic.HostingStyles.NameEquality.LocalTable

/-!
# Stored programs over the test of names

A table **stores a program over the test of names** (`StoresWithNames`) when,
with names written as constants and in the theory of the table with the family
of the equality of names, it dispatches the program and computes its
primitives; its rules are rules that a space runs, and it leaves the test to
the family.  It is the class `Stores` with the theory of a list of rules
replaced by the theory with the family.

* Every table that stores a program with names as constants stores it over
  the test, if it leaves the test to the family (`storesWithNames_of_stores`).
* The table of a program that calls the larger host, with names as constants,
  stores the part of the program over the test (`storesWithNames_partTable`):
  this is where the family is needed, for the equality of data and for the
  questions of the ordered heads.

## The statements of `Stores`, in the theory with the family

* a value that the engine returns for a call is a reduct of the call
  (`StoresWithNames.reduces`), and a normal form (`value_normal`);
* with an orthogonal table every normal form that the call reaches is that
  value (`normalForm_unique`), and the call reaches the datum of a term
  exactly when the engine returns it (`reduces_iff`).

## The candidate runs it, in a finite space

The family is no list, and a space stores a list.  The theory with the family
is locally a finite table: for a list of names that holds the fixed names of
the theory and those of the call, the run of the call **in the space that
stores the table and the rules of the family for those names**
(`localRun`) reaches the run of the value that the engine returns
(`StoresWithNames.run_reaches`); the run of a value has no transition
(`run_value_normal`); every run without transition that is reached is that
one (`run_unique`); and the run of the call reaches the run of a term exactly
when the engine returns that term (`run_reaches_iff`).  The same holds of the
member of the ambient family at that space, with plain atoms
(`member_reaches`, `member_unique`, `member_reaches_iff`).

The space depends on the call through its names only, and any larger list of
names serves as well.  In it the candidate answers the test of two of the
names in one transition (`nameTest_localRun_step`), and no test of a name that
the list does not hold (`nameTest_localRun_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host Applies dataEqualityHost)
open Mettapedia.GSLT.Dedukti
  (Theory RewriteRule Step Reduces inst patternVars usesOnly binderFree
    normal_form_unique_of_orthogonal)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (step_of_rule)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory atomsReduce atomsReduceTheory closedAtom runTermIn
    program_reaches program_rewrites program_normal exists_normal_of_reaches
    eq_runTermIn_of_related runTermIn_injective)
open Mettapedia.Logic.HostingStyles.AmbientSpace
  (ambient ambientTheory listSpace atomTerm termStep_atomTerm_iff atomTerm_injective)
open Mettapedia.Logic.HostingStyles.StoredPrograms

/-! ## The class -/

/-- **A table stores a program over the test of names**, for a host and the
primitives of it that the table computes, with names written as constants: in
the theory of the table with the family of the equality of names it dispatches
the program and realizes the primitives; it is a table of first-order rules
with bound right sides, and it leaves the test to the family. -/
structure StoresWithNames (rules : List RewriteRule) (program : Program) (host : Host)
    (primitives : List String) : Prop where
  /-- The program is of the class. -/
  storable : Storable program host primitives
  /-- A call that selects an equation reduces to the instance of its right side. -/
  dispatches : Dispatches constantSpelling (withNames rules) program primitives
  /-- The call of a primitive on data reduces to the datum of the host's value. -/
  realizes : RealizesPrimitives constantSpelling (withNames rules) host primitives
  /-- The rules are first-order with bound right sides. -/
  runnable : RunnableEquations rules
  /-- The table leaves the test of names to the family. -/
  leaves : LeavesNames rules

/-- **A table that stores a program with names as constants stores it over the
test**, when it leaves the test to the family. -/
theorem storesWithNames_of_stores {rules : List RewriteRule} {program : Program} {host : Host}
    {primitives : List String} (stores : Stores constantSpelling rules program host primitives)
    (leaves : LeavesNames rules) : StoresWithNames rules program host primitives where
  storable := stores.storable
  dispatches := fun head arguments equation bindings selected =>
    (stores.dispatches head arguments equation bindings selected).mono (withNames_extends rules)
  realizes := fun head member arguments result returned =>
    (stores.realizes head member arguments result returned).mono (withNames_extends rules)
  runnable := stores.runnable
  leaves := leaves

/-- **Positive**: the table of unary addition stores it over the test. -/
theorem additionProgram_storesWithNames :
    StoresWithNames (programRules constantSpelling additionProgram []) additionProgram
      DeterministicEquations.TypingExamples.noPrimitives [] :=
  storesWithNames_of_stores (stores_of_storable constantSpelling additionProgram_storable)
    additionRules_leavesNames

/-- **Negative**: a table that answers a test itself stores no program over
the test. -/
theorem answeringTable_not_storesWithNames (program : Program) (host : Host)
    (primitives : List String) : ¬ StoresWithNames answeringTable program host primitives :=
  fun stores => answeringTable_not_leavesNames stores.leaves

/-- **The table of a program that calls the larger host, with names as
constants, stores the part of the program over the test.** -/
theorem storesWithNames_partTable {program : Program} {heads ordered : List String}
    (text : storableText program = true)
    (calls : callsOnly program dataEqualityHandled largerPrimitives = true)
    (closed : closedUnderCalls program heads = true) (orderedIn : ∀ head ∈ ordered, head ∈ heads)
    (stored : StoredTable (partTableIn constantSpelling program heads ordered)) :
    StoresWithNames (partTableIn constantSpelling program heads ordered) (partAt program heads)
      dataEqualityHost largerPrimitives where
  storable := (storable_larger text calls).partAt closed
  dispatches := dispatches_partTable_in constantSpelling text calls closed orderedIn
    (fun _ member => Or.inl member) (withNames_comparesNames _)
  realizes := library_realized_over constantSpelling
    (holds_library_of_partTableIn fun _ member => Or.inl member) (withNames_comparesNames _)
  runnable := stored.runnable
  leaves := leavesNames_of_storedTable stored (partTableIn_roots libraryConstants_fit)

namespace StoresWithNames

variable {rules : List RewriteRule} {program : Program} {host : Host} {primitives : List String}

/-! ## In the theory with the family -/

/-- **The engine's value is reached.** -/
theorem reduces (stores : StoresWithNames rules program host primitives) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) :
    Reduces (withNames rules) (callTerm head (data constantSpelling arguments))
      (datum constantSpelling result) :=
  applies_reduces constantSpelling stores.storable stores.dispatches stores.realizes defined applies

/-- **A datum is a normal form** of the theory with the family. -/
theorem value_normal (stores : StoresWithNames rules program host primitives) (value : EngineTerm) :
    IsNormal (Step (withNames rules)) (datum constantSpelling value) :=
  withNames_normal_of_passive stores.leaves.rooted (passive_datum constantSpelling value)

/-- **Nothing else is reached**: if the theory of the table is orthogonal and
the engine returns a value for a call, every normal form that the call
reaches, in the theory with the family, is the datum of that value. -/
theorem normalForm_unique (stores : StoresWithNames rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) {normalForm : LF.Term}
    (reaches : Reduces (withNames rules) (callTerm head (data constantSpelling arguments))
      normalForm)
    (normal : IsNormal (Step (withNames rules)) normalForm) :
    normalForm = datum constantSpelling result :=
  normal_form_unique_of_orthogonal (withNames_orthogonal orthogonal stores.leaves) reaches normal
    (stores.reduces defined applies) (stores.value_normal result)

/-- **The call reaches the datum of a term exactly when the engine returns
that term**, for a call on which the engine returns a value. -/
theorem reduces_iff (stores : StoresWithNames rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) {head : String} {arguments : List EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (total : ∃ value, Applies program host head arguments value) (result : EngineTerm) :
    Reduces (withNames rules) (callTerm head (data constantSpelling arguments))
        (datum constantSpelling result) ↔
      Applies program host head arguments result := by
  refine ⟨fun reaches => ?_, stores.reduces defined⟩
  obtain ⟨value, applies⟩ := total
  have same := stores.normalForm_unique orthogonal defined applies reaches
    (stores.value_normal result)
  rw [datum_injective constantSpelling_injective same]
  exact applies

end StoresWithNames

/-! ## The space of a list of names -/

/-- The rules of the family for a list of names are rules that a space
runs. -/
theorem nameRulesOn_runnable (names : List String) : RunnableEquations (nameRulesOn names) := by
  constructor
  · intro rule member
    obtain ⟨first, -, second, -, rfl⟩ := mem_nameRulesOn.mp member
    exact ⟨rfl, binderFree_passive (passive_truth constantSpelling _)⟩
  · intro rule member
    obtain ⟨first, -, second, -, rfl⟩ := mem_nameRulesOn.mp member
    exact usesOnly_passive _ 0 (passive_truth constantSpelling _)

/-- The local table of a table that a space runs is one. -/
theorem localTable_runnable {rules : List RewriteRule} (runnable : RunnableEquations rules)
    (names : List String) : RunnableEquations (localTable rules names) :=
  runnable_append runnable (nameRulesOn_runnable names)

/-- The rules of a local table rewrite calls, when those of the table do. -/
theorem localTable_rooted {rules : List RewriteRule}
    (rooted : ∀ rule ∈ rules, rewritesCall rule = true) (names : List String) :
    ∀ rule ∈ localTable rules names, rewritesCall rule = true := fun rule member =>
  withNames_rooted rooted rule ((localTable_extends rules names).rule rule member)

/-- **The run of a term in the space that stores a table and the rules of the
family for a list of names**: a closed atom of the candidate. -/
def localRun (rules : List RewriteRule) (names : List String) (term : LF.Term) :
    Contexts.Term atomsReduce closedAtom :=
  runTermIn (localTable rules names) term

/-- The run of a term determines the term. -/
theorem localRun_injective (rules : List RewriteRule) (names : List String) :
    Function.Injective (localRun rules names) :=
  fun _ _ same => (runTermIn_injective same).2

/-- **In the space of a list that holds two names, the candidate answers their
test in one transition**: the run of the test has a transition to the run of
its answer. -/
theorem nameTest_localRun_step {rules : List RewriteRule} (runnable : RunnableEquations rules)
    {names : List String} {first second : String} (firstIn : first ∈ names)
    (secondIn : second ∈ names) :
    atomsReduceTheory.rewrites (localRun rules names (nameTest first second))
      (localRun rules names (truth constantSpelling (decide (first = second)))) :=
  program_rewrites (localTable_runnable runnable names)
    (step_of_rule (theory := programTheory (localTable rules names)) (rule := nameRule first second)
      (List.mem_append_right _ (mem_nameRulesOn.mpr ⟨first, firstIn, second, secondIn, rfl⟩))
      (fun _ => .con "unbound") rfl (inst_truth constantSpelling _ _))

/-- **Negative**: in the space of a list that does not hold one of the two
names the run of their test has no transition, over a table that leaves the
test to the family. -/
theorem nameTest_localRun_stuck {rules : List RewriteRule} (runnable : RunnableEquations rules)
    (leaves : LeavesNames rules) {names : List String} {first second : String}
    (outside : first ∉ names ∨ second ∉ names) (target : Contexts.Term atomsReduce closedAtom) :
    ¬ atomsReduceTheory.rewrites (localRun rules names (nameTest first second)) target :=
  program_normal (localTable_runnable runnable names) (localTable_test_stuck leaves outside) target

namespace StoresWithNames

variable {rules : List RewriteRule} {program : Program} {host : Host} {primitives : List String}

/-! ## The candidate with a run at the root -/

/-- **The run of a call reaches the run of the value that the engine
returns**, in the space of a list of names that holds the fixed names of the
theory and those of the call. -/
theorem run_reaches (stores : StoresWithNames rules program host primitives)
    {names : List String} (covers : ∀ name ∈ fixedNames rules, name ∈ names) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (within : NamesWithin names (callTerm head (data constantSpelling arguments)))
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) :
    atomsReduceTheory.Reaches
      (localRun rules names (callTerm head (data constantSpelling arguments)))
      (localRun rules names (datum constantSpelling result)) :=
  program_reaches (localTable_runnable stores.runnable names)
    ((reduces_withNames_iff_local stores.runnable.2 covers within).mp
      (stores.reduces defined applies))

/-- **The run of a value has no transition.** -/
theorem run_value_normal (stores : StoresWithNames rules program host primitives)
    (names : List String) (value : EngineTerm) (target : Contexts.Term atomsReduce closedAtom) :
    ¬ atomsReduceTheory.rewrites (localRun rules names (datum constantSpelling value)) target :=
  program_normal (localTable_runnable stores.runnable names)
    (datum_normal (fun _ => rfl) (localTable_rooted stores.leaves.rooted names) constantSpelling
      value) target

/-- **Every run without transition that the run of a call reaches is the run
of the value that the engine returns**, when the theory of the table is
orthogonal. -/
theorem run_unique (stores : StoresWithNames rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) {names : List String}
    (covers : ∀ name ∈ fixedNames rules, name ∈ names) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (within : NamesWithin names (callTerm head (data constantSpelling arguments)))
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result)
    {target : Contexts.Term atomsReduce closedAtom}
    (reaches : atomsReduceTheory.Reaches
      (localRun rules names (callTerm head (data constantSpelling arguments))) target)
    (normal : ∀ next, ¬ atomsReduceTheory.rewrites target next) :
    target = localRun rules names (datum constantSpelling result) := by
  obtain ⟨normalForm, reduces, isNormal, related⟩ :=
    exists_normal_of_reaches (localTable_runnable stores.runnable names) reaches normal
  have lifted : Reduces (withNames rules) (callTerm head (data constantSpelling arguments))
      normalForm := reduces.mono (localTable_extends rules names)
  have formWithin := (reduces_local stores.runnable.2 covers within lifted).2
  have liftedNormal := (normal_withNames_iff_local stores.runnable.2 covers formWithin).mpr isNormal
  rw [stores.normalForm_unique orthogonal defined applies lifted liftedNormal] at related
  exact eq_runTermIn_of_related ((atomsReduceTheory.equations closedAtom).iseqv.symm related)

/-- **The run of a call reaches the run of a term exactly when the engine
returns that term**, for a call on which the engine returns a value. -/
theorem run_reaches_iff (stores : StoresWithNames rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) {names : List String}
    (covers : ∀ name ∈ fixedNames rules, name ∈ names) {head : String}
    {arguments : List EngineTerm}
    (within : NamesWithin names (callTerm head (data constantSpelling arguments)))
    (defined : program.definesAt head arguments.length = true)
    (total : ∃ value, Applies program host head arguments value) (result : EngineTerm) :
    atomsReduceTheory.Reaches
        (localRun rules names (callTerm head (data constantSpelling arguments)))
        (localRun rules names (datum constantSpelling result)) ↔
      Applies program host head arguments result := by
  refine ⟨fun reaches => ?_, stores.run_reaches covers within defined⟩
  obtain ⟨value, applies⟩ := total
  have same := stores.run_unique orthogonal covers within defined applies reaches
    (stores.run_value_normal names result)
  rw [datum_injective constantSpelling_injective (localRun_injective rules names same)]
  exact applies

/-! ## The member of the ambient family at the space of the local table -/

/-- **In the member at the space of the local table, the atom of a call
reaches the atom of the value that the engine returns.** -/
theorem member_reaches (stores : StoresWithNames rules program host primitives)
    {names : List String} (covers : ∀ name ∈ fixedNames rules, name ∈ names) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (within : NamesWithin names (callTerm head (data constantSpelling arguments)))
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) :
    (ambientTheory (listSpace (localTable rules names))).Reaches
      (atomTerm 0 (callTerm head (data constantSpelling arguments)))
      (atomTerm 0 (datum constantSpelling result)) :=
  member_reaches_of_reduces (localTable_runnable stores.runnable names)
    ((reduces_withNames_iff_local stores.runnable.2 covers within).mp
      (stores.reduces defined applies))

/-- **Every atom without transition that the atom of a call reaches is the
atom of the value that the engine returns**, when the theory of the table is
orthogonal. -/
theorem member_unique (stores : StoresWithNames rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) {names : List String}
    (covers : ∀ name ∈ fixedNames rules, name ∈ names) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (within : NamesWithin names (callTerm head (data constantSpelling arguments)))
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result)
    {target : Contexts.Term ambient (AtomsReduce.atomInterface 0)}
    (reaches : (ambientTheory (listSpace (localTable rules names))).Reaches
      (atomTerm 0 (callTerm head (data constantSpelling arguments))) target)
    (normal : ∀ next, ¬ (ambientTheory (listSpace (localTable rules names))).rewrites target next) :
    target = atomTerm 0 (datum constantSpelling result) := by
  have runnable := localTable_runnable stores.runnable names
  obtain ⟨normalForm, reduces, rfl⟩ := exists_reduces_of_member_reaches runnable reaches
  have isNormal : IsNormal (Step (programTheory (localTable rules names))) normalForm :=
    fun next step => normal (atomTerm 0 next) ((termStep_atomTerm_iff runnable.1 runnable.2
      (theory := programTheory (localTable rules names)) (fun _ => Iff.rfl) (fun _ => rfl)
      (depth := 0)).mpr ⟨next, step, rfl⟩)
  have lifted : Reduces (withNames rules) (callTerm head (data constantSpelling arguments))
      normalForm := reduces.mono (localTable_extends rules names)
  have formWithin := (reduces_local stores.runnable.2 covers within lifted).2
  have liftedNormal := (normal_withNames_iff_local stores.runnable.2 covers formWithin).mpr isNormal
  rw [stores.normalForm_unique orthogonal defined applies lifted liftedNormal]

/-- **In the member, the atom of a call reaches the atom of a term exactly
when the engine returns that term**, for a call on which the engine returns a
value. -/
theorem member_reaches_iff (stores : StoresWithNames rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) {names : List String}
    (covers : ∀ name ∈ fixedNames rules, name ∈ names) {head : String}
    {arguments : List EngineTerm}
    (within : NamesWithin names (callTerm head (data constantSpelling arguments)))
    (defined : program.definesAt head arguments.length = true)
    (total : ∃ value, Applies program host head arguments value) (result : EngineTerm) :
    (ambientTheory (listSpace (localTable rules names))).Reaches
        (atomTerm 0 (callTerm head (data constantSpelling arguments)))
        (atomTerm 0 (datum constantSpelling result)) ↔
      Applies program host head arguments result := by
  refine ⟨fun reaches => ?_, stores.member_reaches covers within defined⟩
  obtain ⟨value, applies⟩ := total
  have runnable := localTable_runnable stores.runnable names
  have valueNormal : ∀ next, ¬ (ambientTheory (listSpace (localTable rules names))).rewrites
      (atomTerm 0 (datum constantSpelling result)) next := by
    intro next step
    obtain ⟨reduct, sourceStep, -⟩ := (termStep_atomTerm_iff runnable.1 runnable.2
      (theory := programTheory (localTable rules names)) (fun _ => Iff.rfl) (fun _ => rfl)
      (depth := 0)).mp step
    exact datum_normal (fun _ => rfl) (localTable_rooted stores.leaves.rooted names)
      constantSpelling result reduct sourceStep
  have same := stores.member_unique orthogonal covers within defined applies reaches valueNormal
  rw [datum_injective constantSpelling_injective (atomTerm_injective 0 same)]
  exact applies

end StoresWithNames

#print axioms storesWithNames_of_stores
#print axioms additionProgram_storesWithNames
#print axioms storesWithNames_partTable
#print axioms StoresWithNames.reduces
#print axioms StoresWithNames.value_normal
#print axioms StoresWithNames.normalForm_unique
#print axioms StoresWithNames.reduces_iff
#print axioms nameTest_localRun_step
#print axioms nameTest_localRun_stuck
#print axioms StoresWithNames.run_reaches
#print axioms StoresWithNames.run_value_normal
#print axioms StoresWithNames.run_unique
#print axioms StoresWithNames.run_reaches_iff
#print axioms StoresWithNames.member_reaches
#print axioms StoresWithNames.member_unique
#print axioms StoresWithNames.member_reaches_iff

end Mettapedia.Logic.HostingStyles.NameEquality
