import Mettapedia.Logic.HostingStyles.StoredPrograms.NormalForms
import Mettapedia.Logic.HostingStyles.AmbientSpace.Hosting
import Mettapedia.GSLT.LanguageDef.AuthoredComputation

/-!
# The candidate runs a stored program

The candidate in which atoms reduce runs the rules that its space stores
(`AtomsReduce.tableMap_hosting`): the transitions of the run of a term in the
space of a list of first-order rules with bound right sides are the runs of
the steps of the theory of the list.  So what the theory of a table does with
a call, the candidate does with the run of the call in the space of the
table.

For a table that stores a program (`Stores`), with the run of a call
(`callRun`) and the run of a value (`valueRun`):

* **the run of a call reaches the run of the value that the engine returns**
  (`Stores.run_reaches`);
* the run of a value has no transition (`Stores.run_value_normal`);
* **if the theory of the table is orthogonal, every run without transition
  that the run of the call reaches is the run of that value**
  (`Stores.run_unique`); it is that term, not only a term of its class;
* so the run of a call reaches the run of a term exactly when the engine
  returns that term, for a call on which the engine returns a value
  (`Stores.run_reaches_iff`).

For a program of the class that calls no primitive of its host these are
`stored_run_reaches`, `stored_run_value_normal` and `stored_run_unique`.

For an authored computation, whose program returns the encoded answer exactly
when its relation holds: the run of the call of a query reaches the run of an
encoded answer exactly when the relation holds of the query and the answer
(`Stores.authored_run_iff`), and the run of the refusal exactly when it holds
of no answer (`Stores.authored_run_refuses_iff`).

The member of the ambient family at the space of the table does the same with
the plain atom of the call, with no run (`Stores.member_reaches`,
`Stores.member_value_normal`, `Stores.member_unique`,
`Stores.member_reaches_iff`, `Stores.authored_member_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Authored (AuthoredComputation)
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (Program Equation Host Applies)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule Step Reduces orthogonalCheck)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory atomsReduce atomsReduceTheory closedAtom runTermIn program_reaches
    program_normal exists_normal_of_reaches eq_runTermIn_of_related runTermIn_injective)
open Mettapedia.Logic.HostingStyles.AmbientSpace
  (ambient ambientTheory listSpace atomTerm termStep_atomTerm_iff atomTerm_injective)

/-! ## The candidate with a run at the root -/

/-- **The run of a call in the space of a table**: a closed atom of the
candidate. -/
def callRun (N : Spelling) (rules : List RewriteRule) (head : String)
    (arguments : List EngineTerm) : Contexts.Term atomsReduce closedAtom :=
  runTermIn rules (callTerm head (data N arguments))

/-- **The run of a value in the space of a table.** -/
def valueRun (N : Spelling) (rules : List RewriteRule) (value : EngineTerm) :
    Contexts.Term atomsReduce closedAtom :=
  runTermIn rules (datum N value)

/-- The run of a value determines the value, when the spelling identifies no
two names. -/
theorem valueRun_injective {N : Spelling} (injective : Function.Injective N.write)
    (rules : List RewriteRule) : Function.Injective (valueRun N rules) :=
  fun _ _ same => datum_injective injective (runTermIn_injective same).2

/-- **Negative**: the run of a call is the run of no value. -/
theorem callRun_ne_valueRun (N : Spelling) (rules : List RewriteRule) (head : String)
    (arguments : List EngineTerm) (value : EngineTerm) :
    callRun N rules head arguments ≠ valueRun N rules value :=
  fun same => datum_ne_callTerm N value head _ (runTermIn_injective same).2.symm

namespace Stores

variable {N : Spelling} {rules : List RewriteRule} {program : Program} {host : Host}
  {primitives : List String}

/-- **The run of a call reaches the run of the value that the engine
returns.** -/
theorem run_reaches (stores : Stores N rules program host primitives) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) :
    atomsReduceTheory.Reaches (callRun N rules head arguments) (valueRun N rules result) :=
  program_reaches stores.runnable (stores.reduces defined applies)

/-- **The run of a value has no transition.** -/
theorem run_value_normal (stores : Stores N rules program host primitives) (value : EngineTerm)
    (target : Contexts.Term atomsReduce closedAtom) :
    ¬ atomsReduceTheory.rewrites (valueRun N rules value) target :=
  program_normal stores.runnable (stores.value_normal value) target

/-- **Every run without transition that the run of a call reaches is the run
of the value that the engine returns**, when the theory of the table is
orthogonal. -/
theorem run_unique (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result)
    {target : Contexts.Term atomsReduce closedAtom}
    (reaches : atomsReduceTheory.Reaches (callRun N rules head arguments) target)
    (normal : ∀ next, ¬ atomsReduceTheory.rewrites target next) :
    target = valueRun N rules result := by
  obtain ⟨normalForm, reduces, isNormal, related⟩ :=
    exists_normal_of_reaches stores.runnable reaches normal
  rw [stores.normalForm_unique orthogonal defined applies reduces isNormal] at related
  exact eq_runTermIn_of_related ((atomsReduceTheory.equations closedAtom).iseqv.symm related)

/-- **The run of a call reaches the run of a term exactly when the engine
returns that term**, for a call on which the engine returns a value. -/
theorem run_reaches_iff (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    {head : String} {arguments : List EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (total : ∃ value, Applies program host head arguments value) (result : EngineTerm) :
    atomsReduceTheory.Reaches (callRun N rules head arguments) (valueRun N rules result) ↔
      Applies program host head arguments result := by
  refine ⟨fun reaches => ?_, stores.run_reaches defined⟩
  obtain ⟨value, applies⟩ := total
  have same := stores.run_unique orthogonal defined applies reaches (stores.run_value_normal result)
  rw [valueRun_injective injective rules same]
  exact applies

/-- **An authored computation, run by the candidate**: the run of the call of
a query reaches the run of an encoded answer exactly when the relation of the
computation holds of the query and the answer. -/
theorem authored_run_iff {Query Answer : Type} (C : AuthoredComputation Query Answer)
    (stores : Stores N rules C.program C.host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    (query : Query) (defined : C.program.definesAt C.head (C.encodeQuery query).length = true)
    (answer : Answer) :
    atomsReduceTheory.Reaches (callRun N rules C.head (C.encodeQuery query))
        (valueRun N rules (C.encodeAnswer (some answer))) ↔
      C.relation query answer := by
  have total : ∃ value, Applies C.program C.host C.head (C.encodeQuery query) value := by
    by_cases related : ∃ found, C.relation query found
    · obtain ⟨found, holds⟩ := related
      exact ⟨_, (C.accepts query found).mpr holds⟩
    · exact ⟨_, (C.refuses query).mpr related⟩
  exact (stores.run_reaches_iff orthogonal injective defined total _).trans (C.accepts query answer)

/-- The run of the call of a query reaches the run of the encoded refusal
exactly when the relation holds of the query and no answer. -/
theorem authored_run_refuses_iff {Query Answer : Type} (C : AuthoredComputation Query Answer)
    (stores : Stores N rules C.program C.host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    (query : Query) (defined : C.program.definesAt C.head (C.encodeQuery query).length = true) :
    atomsReduceTheory.Reaches (callRun N rules C.head (C.encodeQuery query))
        (valueRun N rules (C.encodeAnswer none)) ↔
      ¬ ∃ answer, C.relation query answer := by
  have total : ∃ value, Applies C.program C.host C.head (C.encodeQuery query) value := by
    by_cases related : ∃ found, C.relation query found
    · obtain ⟨found, holds⟩ := related
      exact ⟨_, (C.accepts query found).mpr holds⟩
    · exact ⟨_, (C.refuses query).mpr related⟩
  exact (stores.run_reaches_iff orthogonal injective defined total _).trans (C.refuses query)

end Stores

/-! ## Programs of the class that call no primitive of their host -/

/-- **The candidate runs a program of the class**: the run of a call in the
space of the table of the program reaches the run of the value that the
engine returns for the call. -/
theorem stored_run_reaches (N : Spelling) {program : Program} {host : Host}
    (storable : Storable program host []) {head : String} {arguments : List EngineTerm}
    {result : EngineTerm} (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) :
    atomsReduceTheory.Reaches (callRun N (programRules N program []) head arguments)
      (valueRun N (programRules N program []) result) :=
  (stores_of_storable N storable).run_reaches defined applies

/-- The run of a value has no transition. -/
theorem stored_run_value_normal (N : Spelling) {program : Program} {host : Host}
    (storable : Storable program host []) (value : EngineTerm)
    (target : Contexts.Term atomsReduce closedAtom) :
    ¬ atomsReduceTheory.rewrites (valueRun N (programRules N program []) value) target :=
  (stores_of_storable N storable).run_value_normal value target

/-- **And every run without transition that is reached is that one**, when
the table of the program passes the test for orthogonal rule lists. -/
theorem stored_run_unique (N : Spelling) {program : Program} {host : Host}
    (storable : Storable program host [])
    (checked : orthogonalCheck (programRules N program []) = true) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result)
    {target : Contexts.Term atomsReduce closedAtom}
    (reaches : atomsReduceTheory.Reaches (callRun N (programRules N program []) head arguments)
      target)
    (normal : ∀ next, ¬ atomsReduceTheory.rewrites target next) :
    target = valueRun N (programRules N program []) result :=
  (stores_of_storable N storable).run_unique (programTheory_orthogonal checked) defined applies
    reaches normal

/-! ## The member of the ambient family at the space of the table -/

/-- A reduction of the theory of a list of rules is a reduction of the member
at the space of the list, between the plain atoms. -/
theorem member_reaches_of_reduces {rules : List RewriteRule} (runnable : RunnableEquations rules)
    {source target : LF.Term} (reduces : Reduces (programTheory rules) source target) :
    (ambientTheory (listSpace rules)).Reaches (atomTerm 0 source) (atomTerm 0 target) := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih =>
      exact ih.tail ((termStep_atomTerm_iff runnable.1 runnable.2 (theory := programTheory rules)
        (fun _ => Iff.rfl) (fun _ => rfl) (depth := 0)).mpr ⟨_, step, rfl⟩)

/-- What the atom of a term reaches in the member at the space of a list of
rules is the atom of a reduct of the term. -/
theorem exists_reduces_of_member_reaches {rules : List RewriteRule}
    (runnable : RunnableEquations rules) {source : LF.Term}
    {target : Contexts.Term ambient (AtomsReduce.atomInterface 0)}
    (reaches : (ambientTheory (listSpace rules)).Reaches (atomTerm 0 source) target) :
    ∃ next, Reduces (programTheory rules) source next ∧ target = atomTerm 0 next := by
  induction reaches with
  | refl => exact ⟨source, .refl, rfl⟩
  | tail _ step ih =>
      obtain ⟨middle, reduces, rfl⟩ := ih
      obtain ⟨next, sourceStep, rfl⟩ := (termStep_atomTerm_iff runnable.1 runnable.2
        (theory := programTheory rules) (fun _ => Iff.rfl) (fun _ => rfl) (depth := 0)).mp step
      exact ⟨next, reduces.tail sourceStep, rfl⟩

namespace Stores

variable {N : Spelling} {rules : List RewriteRule} {program : Program} {host : Host}
  {primitives : List String}

/-- **In the member at the space of the table, the atom of a call reaches the
atom of the value that the engine returns.**  No run: the space is not in the
term. -/
theorem member_reaches (stores : Stores N rules program host primitives) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) :
    (ambientTheory (listSpace rules)).Reaches (atomTerm 0 (callTerm head (data N arguments)))
      (atomTerm 0 (datum N result)) :=
  member_reaches_of_reduces stores.runnable (stores.reduces defined applies)

/-- The atom of a value has no transition in the member at the space of the
table. -/
theorem member_value_normal (stores : Stores N rules program host primitives) (value : EngineTerm)
    (target : Contexts.Term ambient (AtomsReduce.atomInterface 0)) :
    ¬ (ambientTheory (listSpace rules)).rewrites (atomTerm 0 (datum N value)) target := by
  intro step
  obtain ⟨next, sourceStep, -⟩ := (termStep_atomTerm_iff stores.runnable.1 stores.runnable.2
    (theory := programTheory rules) (fun _ => Iff.rfl) (fun _ => rfl) (depth := 0)).mp step
  exact stores.value_normal value next sourceStep

/-- **Every atom without transition that the atom of a call reaches is the
atom of the value that the engine returns**, when the theory of the table is
orthogonal. -/
theorem member_unique (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) {head : String}
    {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result)
    {target : Contexts.Term ambient (AtomsReduce.atomInterface 0)}
    (reaches : (ambientTheory (listSpace rules)).Reaches
      (atomTerm 0 (callTerm head (data N arguments))) target)
    (normal : ∀ next, ¬ (ambientTheory (listSpace rules)).rewrites target next) :
    target = atomTerm 0 (datum N result) := by
  obtain ⟨normalForm, reduces, rfl⟩ := exists_reduces_of_member_reaches stores.runnable reaches
  have isNormal : IsNormal (Step (programTheory rules)) normalForm := fun next step =>
    normal (atomTerm 0 next) ((termStep_atomTerm_iff stores.runnable.1 stores.runnable.2
      (theory := programTheory rules) (fun _ => Iff.rfl) (fun _ => rfl) (depth := 0)).mpr
      ⟨next, step, rfl⟩)
  rw [stores.normalForm_unique orthogonal defined applies reduces isNormal]

/-- **In the member, the atom of a call reaches the atom of a term exactly
when the engine returns that term**, for a call on which the engine returns a
value. -/
theorem member_reaches_iff (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    {head : String} {arguments : List EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (total : ∃ value, Applies program host head arguments value) (result : EngineTerm) :
    (ambientTheory (listSpace rules)).Reaches (atomTerm 0 (callTerm head (data N arguments)))
        (atomTerm 0 (datum N result)) ↔
      Applies program host head arguments result := by
  refine ⟨fun reaches => ?_, stores.member_reaches defined⟩
  obtain ⟨value, applies⟩ := total
  have same := stores.member_unique orthogonal defined applies reaches
    (stores.member_value_normal result)
  rw [datum_injective injective (atomTerm_injective 0 same)]
  exact applies

/-- **An authored computation, run by the member at the space of the table**:
the atom of the call of a query reaches the atom of an encoded answer exactly
when the relation holds of the query and the answer. -/
theorem authored_member_iff {Query Answer : Type} (C : AuthoredComputation Query Answer)
    (stores : Stores N rules C.program C.host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    (query : Query) (defined : C.program.definesAt C.head (C.encodeQuery query).length = true)
    (answer : Answer) :
    (ambientTheory (listSpace rules)).Reaches
        (atomTerm 0 (callTerm C.head (data N (C.encodeQuery query))))
        (atomTerm 0 (datum N (C.encodeAnswer (some answer)))) ↔
      C.relation query answer := by
  have total : ∃ value, Applies C.program C.host C.head (C.encodeQuery query) value := by
    by_cases related : ∃ found, C.relation query found
    · obtain ⟨found, holds⟩ := related
      exact ⟨_, (C.accepts query found).mpr holds⟩
    · exact ⟨_, (C.refuses query).mpr related⟩
  exact (stores.member_reaches_iff orthogonal injective defined total _).trans
    (C.accepts query answer)

end Stores

#print axioms valueRun_injective
#print axioms callRun_ne_valueRun
#print axioms Stores.run_reaches
#print axioms Stores.run_value_normal
#print axioms Stores.run_unique
#print axioms Stores.run_reaches_iff
#print axioms Stores.authored_run_iff
#print axioms Stores.authored_run_refuses_iff
#print axioms stored_run_reaches
#print axioms stored_run_value_normal
#print axioms stored_run_unique
#print axioms Stores.member_reaches
#print axioms Stores.member_value_normal
#print axioms Stores.member_unique
#print axioms Stores.member_reaches_iff
#print axioms Stores.authored_member_iff

end Mettapedia.Logic.HostingStyles.StoredPrograms
