import Mettapedia.Logic.HostingStyles.StoredPrograms.LargerHost
import Mettapedia.Logic.HostingStyles.StoredPrograms.Running
import Mettapedia.Languages.MM0.Presentation.Calculus

/-!
# The third kernel operation, end to end: the conversion that a witness establishes

The conversion of two expressions by a submitted witness
(`Calculus.conversionComputation`) is the head `mm0:conversion` of the
conversion program, 193 equations under the larger host.  It reaches 83 heads
and 168 equations (`conversionHeads`, `conversionHeads_closed`).  Unlike the
two other operations it needs both things that a plain table does not give:

* it calls the **equality of data**, on expressions and on inferred types;
* one of its heads, `mm0:conversion-argument-checked`, has **two overlapping
  equations**: the first continues when the three checks of a converted
  argument are `True`, the second refuses in every other case.

So names are written in letters, and that head is ordered.  Its table
(`conversionTable`) has 252 rules: the 166 rules of the equations of the other
heads, the six ordered rules of that head, and the eighty rules of the
library.  It stores the part of the program (`conversion_stores`) and is a
stored table, hence orthogonal (`conversion_stored`).

**The candidate runs the operation.**  The run of the call reaches the run of
an encoded conversion exactly when MM0's kernel checks the witness for that
conversion (`conversion_run_iff`), and the run of the refusal exactly when the
kernel checks it for none (`conversion_run_refuses_iff`).

One instance is checked by replaying its trace in the table (`oneConstant`):
the reflexivity of the constant of a theory with one constant, twelve steps
(`conversion_instance_replays`), to the conversion that the kernel's function
returns (`conversion_instance_kernel`).  In the theory without the constant
the same call takes seven steps to the refusal (`conversion_instance_refuses`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Authored (AuthoredComputation)
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host dataEqualityHost Applies natural)
open Mettapedia.GSLT.Dedukti (RewriteRule Step Reduces)
open Mettapedia.Languages.MM0.Kernel (ConvWitness ConversionResult Context)
open Mettapedia.Languages.MM0.Presentation.Calculus (conversionComputation)
open Mettapedia.Languages.MM0.Presentation.ComputationalConversion (conversionProgram)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory atomsReduce atomsReduceTheory closedAtom program_reaches)

/-- **The heads that the conversion reaches** in the conversion program. -/
def conversionHeads : List String :=
  ["mm0:conversion", "mm0:conversion-refl-type", "mm0:infer", "mm0:conversion-swap",
    "mm0:conversion-first", "mm0:conversion-declaration", "mm0:declaration",
    "mm0:conversion-unfold-declaration", "mm0:declaration-view", "mm0:infer-binder", "mm0:data-at",
    "mm0:infer-declaration", "mm0:infer-function", "mm0:conversion-refl-saturated",
    "mm0:conversion-join", "mm0:conversion-congruent", "mm0:conversion-arguments",
    "mm0:conversion-unfold-result", "mm0:unfold", "mm0:at-view", "mm0:declaration-equal",
    "mm0:infer-arguments", "mm0:unfold-declaration", "mm0:conversion-joined", "mm0:apply-args",
    "mm0:conversion-unfold-typed", "mm0:conversion-arguments-view", "mm0:at-zero",
    "mm0:infer-bound-sort", "mm0:bound-sort", "mm0:infer-regular-type", "mm0:unfold-body",
    "nik:nat-table-get", "mm0:apply-args-view", "mm0:conversion-argument", "mm0:bound-binder",
    "mm0:infer-sort-equal", "mm0:infer-saturated", "nik:table-view", "mm0:unfold-arguments",
    "mm0:check-arguments", "mm0:conversion-argument-checked", "mm0:conversion-binder-sort",
    "mm0:check-binder", "mm0:check-sort", "mm0:check-type", "mm0:check-arguments-view",
    "nik:table-equal", "mm0:unfold-dummies", "mm0:check-dummies", "mm0:conversion-argument-tail",
    "mm0:check-saturated", "mm0:check-arguments-next", "mm0:dummies-view", "mm0:subst",
    "mm0:substitution-values", "nik:list-append", "mm0:variable-images", "nik:append-view",
    "mm0:lookup", "mm0:subst-function", "mm0:substitution-values-view", "mm0:dummy-sort",
    "mm0:variable-images-view", "mm0:subst-argument", "mm0:lookup-zero", "mm0:dummy-fresh",
    "mm0:fresh-all", "mm0:fresh-all-view", "mm0:fresh-all-next", "mm0:fresh-for", "mm0:check-pair",
    "mm0:pair-depends", "mm0:depends", "nik:nat-member", "mm0:support-disjoint", "mm0:support",
    "mm0:support-binder", "mm0:support-function", "nik:member-view", "mm0:dependency-not",
    "mm0:support-argument", "nik:member-equal"]

/-- **The head whose equations are tried in order.** -/
def conversionOrdered : List String := ["mm0:conversion-argument-checked"]

/-- **The table that runs the conversion**: 252 rules, the same for every
theory. -/
abbrev conversionTable : List RewriteRule :=
  partTable conversionProgram conversionHeads conversionOrdered

set_option maxRecDepth 100000 in
/-- The text of the conversion program is of the class. -/
theorem conversion_text : storableText conversionProgram = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- It calls only what the library computes. -/
theorem conversion_calls :
    callsOnly conversionProgram dataEqualityHandled largerPrimitives = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The heads are closed under the calls of the program. -/
theorem conversionHeads_closed : closedUnderCalls conversionProgram conversionHeads = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The equations of the other heads are separated.** -/
theorem conversion_separated :
    Separated (conversionProgram.filter fun equation =>
      !conversionOrdered.contains equation.head) :=
  separated_of_no_overlappingPairs (by decide +kernel)

set_option maxRecDepth 100000 in
/-- No equation has a primitive as its head. -/
theorem conversion_noPrimitive : ∀ equation ∈ conversionProgram,
    equation.head ∉ largerPrimitives := by
  have checked : (conversionProgram.all fun equation =>
      !largerPrimitives.contains equation.head) = true := by decide +kernel
  intro equation member
  simpa using List.all_eq_true.mp checked equation member

set_option maxRecDepth 100000 in
/-- The six ordered rules are a stored table. -/
theorem conversion_ordered_stored : StoredTable (orderedPart conversionProgram conversionOrdered) :=
  storedTable_of_check (by decide +kernel)

/-- **The table is a stored table**, hence orthogonal. -/
theorem conversion_stored : StoredTable conversionTable :=
  storedTable_partTable conversion_text conversion_separated conversion_noPrimitive
    conversion_ordered_stored

/-- **The table stores the part of the program.** -/
theorem conversion_stores :
    Stores letterSpelling conversionTable (partAt conversionProgram conversionHeads)
      dataEqualityHost largerPrimitives :=
  stores_partTable conversion_text conversion_calls conversionHeads_closed (by decide)
    conversion_stored

set_option maxRecDepth 100000 in
/-- 83 heads, 168 of the 193 equations, 252 rules. -/
theorem conversion_size :
    conversionHeads.length = 83 ∧ (partAt conversionProgram conversionHeads).length = 168 ∧
      conversionTable.length = 252 := by
  have counted : ((partAt conversionProgram conversionHeads).filter fun equation =>
      !conversionOrdered.contains equation.head).length = 166 ∧
      (orderedPart conversionProgram conversionOrdered).length = 6 ∧
      (partAt conversionProgram conversionHeads).length = 168 := by decide +kernel
  refine ⟨by decide, counted.2.2, ?_⟩
  rw [partTable_length, counted.1, counted.2.1]

set_option maxRecDepth 100000 in
/-- **What the part needs**: six primitives, among them the equality of data
and not the sum; no special form; the one overlapping pair. -/
theorem conversionPart_inventory :
    calledPrimitives (partAt conversionProgram conversionHeads) dataEqualityHandled =
        ["nik:list-view", "nik:nat-zero", "nik:nat-pred", "nik:nat-eq", "nik:list-cons",
          "nik:data-eq"] ∧
      specialForms (partAt conversionProgram conversionHeads) = [] ∧
      overlappingPairs (partAt conversionProgram conversionHeads) =
        [("conversion-argument-checked", "conversion-argument-refused")] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conversion_defined :
    conversionProgram.definesAt "mm0:conversion" 4 = true ∧
      "mm0:conversion" ∈ conversionHeads := by
  decide +kernel

/-- **The operation, with the part of its program that it reaches.** -/
def conversionPart (T : Mettapedia.Languages.MM0.Kernel.Theory) :
    AuthoredComputation (Context × ConvWitness) ConversionResult :=
  restrictComputation (conversionComputation T) conversionHeads conversionHeads_closed
    conversion_defined.2 fun _ => conversion_defined.1

/-- **The run of the conversion** by a witness, in a context. -/
def conversionRun (T : Mettapedia.Languages.MM0.Kernel.Theory) (context : Context)
    (witness : ConvWitness) : Contexts.Term atomsReduce closedAtom :=
  callRun letterSpelling conversionTable "mm0:conversion"
    ((conversionComputation T).encodeQuery (context, witness))

/-- **The run of an answer of the conversion**: an encoded conversion, or the
refusal. -/
def conversionAnswerRun (T : Mettapedia.Languages.MM0.Kernel.Theory)
    (answer : Option ConversionResult) : Contexts.Term atomsReduce closedAtom :=
  valueRun letterSpelling conversionTable ((conversionComputation T).encodeAnswer answer)

theorem conversionPart_defined :
    (partAt conversionProgram conversionHeads).definesAt "mm0:conversion" 4 = true :=
  (definesAt_partAt conversion_defined.2 4).trans conversion_defined.1

/-- **The candidate runs the conversion**: the run of the call reaches the run
of an encoded conversion exactly when MM0's kernel checks the witness, in the
context, for that conversion. -/
theorem conversion_run_iff (T : Mettapedia.Languages.MM0.Kernel.Theory) (context : Context)
    (witness : ConvWitness) (result : ConversionResult) :
    atomsReduceTheory.Reaches (conversionRun T context witness)
        (conversionAnswerRun T (some result)) ↔
      ConvWitness.Checks T.termSignature T.definitionSignature context witness result.left
        result.right result.sort :=
  conversion_stores.authored_run_iff (conversionPart T) conversion_stored.orthogonal
    letterSpelling_injective (context, witness) conversionPart_defined result

/-- The run of the call reaches the run of the refusal exactly when the kernel
checks the witness for no conversion. -/
theorem conversion_run_refuses_iff (T : Mettapedia.Languages.MM0.Kernel.Theory)
    (context : Context) (witness : ConvWitness) :
    atomsReduceTheory.Reaches (conversionRun T context witness) (conversionAnswerRun T none) ↔
      ¬ ∃ result : ConversionResult,
        ConvWitness.Checks T.termSignature T.definitionSignature context witness result.left
          result.right result.sort :=
  conversion_stores.authored_run_refuses_iff (conversionPart T) conversion_stored.orthogonal
    letterSpelling_injective (context, witness) conversionPart_defined

/-! ## One instance, checked by replaying its trace in the table -/

/-- A theory with one constant, of sort zero and without argument. -/
def oneConstant : Mettapedia.Languages.MM0.Kernel.Theory := { terms := [(0, ⟨[], 0, ∅⟩)] }

/-- The arguments of the call for the reflexivity of the constant, written
out: the term declarations, no definition, the empty context and the encoded
witness. -/
theorem conversion_instance_query :
    (conversionComputation oneConstant).encodeQuery ([], .refl (.term 0)) =
      [.list [.list [natural 0, .list [.sym "MM0:TermDecl", .list [], natural 0, .list []]]],
        .list [], .list [],
        .list [.sym "MM0:ConvRefl", .expr [.sym "MM0:Term", natural 0]]] := by
  simp [conversionComputation, oneConstant,
    Mettapedia.Languages.MM0.Presentation.ComputationalTyping.encodeTable,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDeclaration,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeContext,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeDependencies,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeNaturals,
    Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions.encodeDefinitions,
    Mettapedia.GSLT.LanguageDef.DeterministicEquations.encodeNaturalTable,
    Mettapedia.Languages.MM0.Presentation.ComputationalConversion.encodeWitness,
    Mettapedia.Languages.MM0.Presentation.encode]

/-- The same call in the theory without the constant. -/
theorem conversion_refusal_query :
    (conversionComputation {}).encodeQuery ([], .refl (.term 0)) =
      [.list [], .list [], .list [],
        .list [.sym "MM0:ConvRefl", .expr [.sym "MM0:Term", natural 0]]] := by
  simp [conversionComputation,
    Mettapedia.Languages.MM0.Presentation.ComputationalTyping.encodeTable,
    Mettapedia.Languages.MM0.Presentation.ComputationalContext.encodeContext,
    Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions.encodeDefinitions,
    Mettapedia.GSLT.LanguageDef.DeterministicEquations.encodeNaturalTable,
    Mettapedia.Languages.MM0.Presentation.ComputationalConversion.encodeWitness,
    Mettapedia.Languages.MM0.Presentation.encode]

/-- **The kernel's function** returns the conversion of the constant with
itself at sort zero, and nothing in the theory without the constant. -/
theorem conversion_instance_kernel :
    (ConvWitness.refl (.term 0)).conversion? oneConstant.termSignature
        oneConstant.definitionSignature [] = some ⟨.term 0, .term 0, 0⟩ ∧
      (ConvWitness.refl (.term 0)).conversion?
        (Mettapedia.Languages.MM0.Kernel.Theory.termSignature {})
        (Mettapedia.Languages.MM0.Kernel.Theory.definitionSignature {}) [] = none := by
  decide +kernel

/-- **The trace of the run**: the conversion; the inference of the type of
the expression, which looks the declaration of the constant up in the list of
the term declarations, comparing its index; the type of a reflexivity; and the
check that the expression is saturated. -/
def conversionTrace : List (List Bool × Nat) :=
  [([], 128), ([true, false, true], 11), ([true, false, true, true, false, true], 5),
    ([true, false, true, true, false, true, true, false, true], 173),
    ([true, false, true, true, false, true], 7),
    ([true, false, true, true, false, true, true, false, true], 179),
    ([true, false, true, true, false, true, true, false, true], 180),
    ([true, false, true, true, false, true], 8), ([true, false, true], 17), ([], 130),
    ([true, false, true], 172), ([], 131)]

/-- The trace of the run in the theory without the constant: the lookup of
the declaration finds nothing. -/
def refusalTrace : List (List Bool × Nat) :=
  [([], 128), ([true, false, true], 11), ([true, false, true, true, false, true], 5),
    ([true, false, true, true, false, true, true, false, true], 172),
    ([true, false, true, true, false, true], 6), ([true, false, true], 16), ([], 129)]

set_option maxRecDepth 100000 in
/-- **Replaying the trace in the table**: twelve steps take the call of the
conversion to the reading of the encoded conversion. -/
theorem conversion_instance_replays :
    replay conversionTable conversionTrace
        (callTerm "mm0:conversion"
          (data letterSpelling
            ((conversionComputation oneConstant).encodeQuery ([], .refl (.term 0))))) =
      some (datum letterSpelling
        ((conversionComputation oneConstant).encodeAnswer (some ⟨.term 0, .term 0, 0⟩))) := by
  rw [conversion_instance_query]
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Negative**: in the theory without the constant, seven steps take the
same call to the reading of the refusal. -/
theorem conversion_instance_refuses :
    replay conversionTable refusalTrace
        (callTerm "mm0:conversion"
          (data letterSpelling ((conversionComputation {}).encodeQuery ([], .refl (.term 0))))) =
      some (datum letterSpelling ((conversionComputation {}).encodeAnswer none)) := by
  rw [conversion_refusal_query]
  decide +kernel

/-- **So the candidate reaches that run**, by the replayed reduction and
without the general theorem. -/
theorem conversion_instance_reaches :
    atomsReduceTheory.Reaches (conversionRun oneConstant [] (.refl (.term 0)))
      (conversionAnswerRun oneConstant (some ⟨.term 0, .term 0, 0⟩)) :=
  program_reaches conversion_stores.runnable (replay_reduces _ conversion_instance_replays)

/-- And the kernel checks the witness for that conversion. -/
theorem conversion_instance_checks :
    ConvWitness.Checks oneConstant.termSignature oneConstant.definitionSignature []
      (.refl (.term 0)) (.term 0) (.term 0) 0 :=
  (conversion_run_iff oneConstant [] (.refl (.term 0)) ⟨.term 0, .term 0, 0⟩).mp
    conversion_instance_reaches

#print axioms conversionHeads_closed
#print axioms conversion_separated
#print axioms conversion_ordered_stored
#print axioms conversion_stored
#print axioms conversion_stores
#print axioms conversion_size
#print axioms conversionPart_inventory
#print axioms conversion_run_iff
#print axioms conversion_run_refuses_iff
#print axioms conversion_instance_kernel
#print axioms conversion_instance_replays
#print axioms conversion_instance_refuses
#print axioms conversion_instance_reaches
#print axioms conversion_instance_checks

end Mettapedia.Logic.HostingStyles.StoredPrograms
