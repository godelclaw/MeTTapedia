import Mettapedia.Logic.HostingStyles.StoredPrograms.Restriction
import Mettapedia.Logic.HostingStyles.StoredPrograms.Lookup
import Mettapedia.Logic.HostingStyles.StoredPrograms.TableCheck
import Mettapedia.Languages.MM0.Presentation.CalculusControls

/-!
# The second kernel operation, end to end: the instance of a theorem

The instance of a declared theorem at arguments, with MM0's check that the
substitution is admissible (`Calculus.instanceComputation`), is the head
`mm0:instantiate-theorem` of the proof program, 233 equations under the larger
host.

**What the operation reaches is smaller than its program**
(`instanceHeads`, `instanceProgram`): 66 heads and 130 equations, closed under
calls (`instanceHeads_closed`).  That part

* calls six primitives, all of the shared host: the list view and former, the
  zero test, the predecessor, the equality of numbers and the sum; it does
  **not** call the equality of data;
* has no `let`;
* has no two equations of one head with overlapping left sides
  (`instanceProgram_inventory`).  The one overlapping pair of the proof
  program is in the conversion, which the instance does not reach.

So its table (`instanceTable`), the 130 rules of its equations and the
nineteen rules of the shared host, stores it (`instance_stores`) and is
orthogonal (`instance_orthogonal`), with names written as constants: 149
stored rules, the same for every theory.

**The candidate runs the operation.**  The run of the call reaches the run of
an encoded instance exactly when MM0's kernel instantiates the declaration to
that instance (`theoremInstance_run_iff`), and the run of the refusal exactly
when the kernel instantiates it to nothing (`theoremInstance_run_refuses_iff`).

One instance is checked by running the table: the axiom of the control theory
at no argument, twenty-six steps (`instance_instance_runs`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Authored (AuthoredComputation)
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host natural boolean computationalHost dataEqualityHost Applies)
open Mettapedia.GSLT.Dedukti (RewriteRule Step Reduces orthogonalCheck)
open Mettapedia.Languages.MM0.Kernel (TheoremDecl TheoremInstance Preterm Context)
open Mettapedia.Languages.MM0.Presentation.Calculus (instanceComputation)
open Mettapedia.Languages.MM0.Presentation.ComputationalProof (proofProgram)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory atomsReduce atomsReduceTheory closedAtom program_reaches)

/-- **The heads that the instantiation of a theorem reaches** in the proof
program: what fifteen rounds of calls add to its head
(`instanceHeads_reached`). -/
def instanceHeads : List String :=
  ["mm0:instantiate-theorem", "mm0:theorem-admissible", "mm0:check-admissible",
    "mm0:admissible-typed", "mm0:check-arguments", "mm0:theorem-prepared",
    "mm0:substitution-values", "mm0:check-arguments-view", "mm0:admissible-entries", "mm0:entries",
    "mm0:substitution-values-view", "mm0:theorem-hypotheses", "mm0:subst-list",
    "mm0:check-arguments-next", "mm0:check-binder", "mm0:entries-view", "mm0:check-rows",
    "mm0:subst-list-view", "mm0:theorem-conclusion", "mm0:subst", "mm0:check-sort",
    "mm0:bound-sort", "mm0:check-type", "mm0:infer", "mm0:rows-view", "mm0:lookup",
    "mm0:subst-function", "mm0:subst-list-head", "mm0:infer-binder", "mm0:data-at",
    "mm0:infer-declaration", "mm0:declaration", "mm0:infer-function", "mm0:bound-binder",
    "mm0:check-saturated", "mm0:rows-next", "mm0:check-row", "mm0:subst-argument",
    "mm0:lookup-zero", "mm0:subst-list-tail", "mm0:at-view", "mm0:declaration-view",
    "mm0:infer-arguments", "mm0:check-pairs", "mm0:at-zero", "mm0:declaration-equal",
    "mm0:infer-bound-sort", "mm0:infer-regular-type", "mm0:pairs-view", "mm0:infer-sort-equal",
    "mm0:infer-saturated", "mm0:pairs-next", "mm0:check-pair", "mm0:pair-depends", "mm0:depends",
    "nik:nat-member", "mm0:support-disjoint", "mm0:support", "mm0:support-binder",
    "mm0:support-function", "nik:member-view", "mm0:dependency-not", "mm0:support-argument",
    "nik:member-equal", "nik:list-append", "nik:append-view"]

/-- **The part of the proof program that the instantiation reaches.** -/
def instanceProgram : Program := partAt proofProgram instanceHeads

set_option maxRecDepth 100000 in
/-- The heads are closed under the calls of the proof program. -/
theorem instanceHeads_closed : closedUnderCalls proofProgram instanceHeads = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- They are the heads that the head of the operation reaches. -/
theorem instanceHeads_reached :
    reachableHeads proofProgram 15 ["mm0:instantiate-theorem"] = instanceHeads := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Sixty-six heads and 130 of the 233 equations. -/
theorem instanceProgram_size :
    instanceHeads.length = 66 ∧ instanceProgram.length = 130 ∧ proofProgram.length = 233 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **What the part needs**: six primitives of the shared host, no special
form, no overlapping pair. -/
theorem instanceProgram_inventory :
    calledPrimitives instanceProgram dataEqualityHandled =
        ["nik:list-view", "nik:nat-zero", "nik:nat-pred", "nik:nat-eq", "nik:list-cons",
          "nik:nat-add"] ∧
      specialForms instanceProgram = [] ∧ overlappingPairs instanceProgram = [] := by
  decide +kernel

/-- So the order of its equations does not matter. -/
theorem instanceProgram_separated : Separated instanceProgram :=
  separated_of_no_overlappingPairs instanceProgram_inventory.2.2

/-- **The table that runs the instantiation of a theorem**: 149 rules, the
same for every theory. -/
abbrev instanceTable : List RewriteRule := sharedTable constantSpelling instanceProgram

set_option maxRecDepth 100000 in
theorem instance_text : storableText instanceProgram = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem instance_calls : callsOnly instanceProgram dataEqualityHandled sharedPrimitives = true := by
  decide +kernel

/-- **The table stores the part.** -/
theorem instance_stores :
    Stores constantSpelling instanceTable instanceProgram dataEqualityHost sharedPrimitives :=
  stores_sharedLarger constantSpelling instance_text instance_calls sharedRules_runnable
    sharedRules_rewriteCalls

set_option maxRecDepth 100000 in
/-- **The table passes the test for stored tables.** -/
theorem instance_checked : storedTableCheck instanceTable = true := by
  decide +kernel

/-- **The table is orthogonal.** -/
theorem instance_orthogonal : (programTheory instanceTable).Orthogonal :=
  orthogonal_of_storedTableCheck instance_checked

set_option maxRecDepth 100000 in
theorem instanceTable_length : instanceTable.length = 149 := by decide +kernel

set_option maxRecDepth 100000 in
theorem instance_defined :
    proofProgram.definesAt "mm0:instantiate-theorem" 4 = true ∧
      "mm0:instantiate-theorem" ∈ instanceHeads := by
  decide +kernel

/-- **The operation, with the part of its program that it reaches**: the same
relation, the instance that MM0's kernel computes. -/
def instancePart (T : Mettapedia.Languages.MM0.Kernel.Theory) :
    AuthoredComputation (Context × TheoremDecl × List Preterm) TheoremInstance :=
  restrictComputation (instanceComputation T) instanceHeads instanceHeads_closed instance_defined.2
    fun _ => instance_defined.1

/-- **The run of the instantiation** of a declaration at arguments, in a
context. -/
def theoremInstanceRun (T : Mettapedia.Languages.MM0.Kernel.Theory) (context : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) : Contexts.Term atomsReduce closedAtom :=
  callRun constantSpelling instanceTable "mm0:instantiate-theorem"
    ((instanceComputation T).encodeQuery (context, declaration, arguments))

/-- **The run of an answer of the instantiation**: an encoded instance, or the
refusal. -/
def instanceAnswerRun (T : Mettapedia.Languages.MM0.Kernel.Theory)
    (answer : Option TheoremInstance) : Contexts.Term atomsReduce closedAtom :=
  valueRun constantSpelling instanceTable ((instanceComputation T).encodeAnswer answer)

/-- **The candidate runs the instantiation of a theorem**: the run of the
call reaches the run of an encoded instance exactly when MM0's kernel
instantiates the declaration, at the arguments and in the context, to that
instance. -/
theorem theoremInstance_run_iff (T : Mettapedia.Languages.MM0.Kernel.Theory) (context : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) (result : TheoremInstance) :
    atomsReduceTheory.Reaches (theoremInstanceRun T context declaration arguments)
        (instanceAnswerRun T (some result)) ↔
      TheoremDecl.Instantiates T.termSignature context declaration arguments result :=
  instance_stores.authored_run_iff (instancePart T) instance_orthogonal
    constantSpelling_injective (context, declaration, arguments) instance_stores_defined result
where
  instance_stores_defined : instanceProgram.definesAt "mm0:instantiate-theorem" 4 = true :=
    (definesAt_partAt instance_defined.2 4).trans instance_defined.1

/-- The run of the call reaches the run of the refusal exactly when the kernel
instantiates the declaration to nothing. -/
theorem theoremInstance_run_refuses_iff (T : Mettapedia.Languages.MM0.Kernel.Theory)
    (context : Context) (declaration : TheoremDecl) (arguments : List Preterm) :
    atomsReduceTheory.Reaches (theoremInstanceRun T context declaration arguments)
        (instanceAnswerRun T none) ↔
      ¬ ∃ result, TheoremDecl.Instantiates T.termSignature context declaration arguments result :=
  instance_stores.authored_run_refuses_iff (instancePart T)
    instance_orthogonal constantSpelling_injective
    (context, declaration, arguments)
    ((definesAt_partAt instance_defined.2 4).trans instance_defined.1)

/-! ## One instance, checked by running the table -/

open Mettapedia.Languages.MM0.Presentation.Calculus.Controls (withAxiom axiomDecl constant)

/-- The arguments of the call for the axiom of the control theory at no
argument, written out: the term declarations, the empty context, the
encoded axiom and no argument. -/
theorem instance_instance_query :
    (instanceComputation withAxiom).encodeQuery ([], axiomDecl, []) =
      [.list [.list [natural 0, .list [.sym "MM0:TermDecl", .list [], natural 0, .list []]]],
        .list [],
        .list [.sym "MM0:Theorem", .list [], .list [], .expr [.sym "MM0:Term", natural 0]],
        .list []] := by
  simp [instanceComputation, withAxiom, axiomDecl, constant,
    Mettapedia.Languages.MM0.Presentation.ComputationalTyping.encodeTable,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDeclaration,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeContext,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDependencies,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeNaturals,
    Mettapedia.Languages.MM0.Presentation.ComputationalProof.encodeTheorem,
    Mettapedia.Languages.MM0.Presentation.ComputationalArguments.encodeExpressions,
    Mettapedia.Languages.MM0.Presentation.encode]

set_option maxRecDepth 100000 in
/-- **Running the table**: the function `run` takes the call of the
instantiation of the axiom of the control theory, at no argument, to the
reading of its encoded instance, in twenty-six steps. -/
theorem instance_instance_runs :
    run instanceTable 26
        (callTerm "mm0:instantiate-theorem"
          (data constantSpelling ((instanceComputation withAxiom).encodeQuery ([], axiomDecl, [])))) =
      datum constantSpelling ((instanceComputation withAxiom).encodeAnswer (some ⟨[], constant⟩)) := by
  rw [instance_instance_query]
  decide +kernel

/-- **So the candidate reaches that run**, by the computed reduction. -/
theorem instance_instance_reaches :
    atomsReduceTheory.Reaches (theoremInstanceRun withAxiom [] axiomDecl [])
      (instanceAnswerRun withAxiom (some ⟨[], constant⟩)) :=
  program_reaches instance_stores.runnable (reduces_of_run instance_instance_runs)

/-- And the kernel instantiates the axiom to that instance. -/
theorem instance_instance_kernel :
    TheoremDecl.Instantiates withAxiom.termSignature [] axiomDecl [] ⟨[], constant⟩ :=
  (theoremInstance_run_iff withAxiom [] axiomDecl [] ⟨[], constant⟩).mp instance_instance_reaches

#print axioms instanceHeads_closed
#print axioms instanceProgram_inventory
#print axioms instance_stores
#print axioms instance_checked
#print axioms instance_orthogonal
#print axioms theoremInstance_run_iff
#print axioms theoremInstance_run_refuses_iff
#print axioms instance_instance_runs
#print axioms instance_instance_reaches
#print axioms instance_instance_kernel

end Mettapedia.Logic.HostingStyles.StoredPrograms
