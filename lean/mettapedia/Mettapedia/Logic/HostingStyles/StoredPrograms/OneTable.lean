import Mettapedia.Logic.HostingStyles.StoredPrograms.Check
import Mettapedia.Logic.HostingStyles.StoredPrograms.Conversion
import Mettapedia.Logic.HostingStyles.StoredPrograms.Instantiation

/-!
# One table for the three operations and the check

The check of a certificate calls the three kernel operations at its leaves,
so the table of the check holds their rules.  **The 390 rules of
`checkTable`, stored in one space, run each operation as well.**

For a head that the check reaches, a call that the program of the check
answers runs, in the space of that table, to the run of its value, and to no
other run without transition (`RunsInCheckTable`, `checkTable_runs`).  The
program of the check computes each operation as MM0's kernel does, so, with
the kernel's own functions:

* the lookup of an index runs to the encoding of `T.theoremSignature index`
  (`oneTable_lookup`);
* the instantiation of a declaration runs to the encoding of
  `declaration.instantiate? …` (`oneTable_instance`);
* the conversion by a witness runs to the encoding of
  `witness.conversion? …` (`oneTable_conversion`).

So **the run of a call reaches the run of an encoded result exactly when the
kernel's function returns that result** (`oneTable_lookup_iff`,
`oneTable_instance_iff`, `oneTable_conversion_iff`), by the injectivity of the
encodings (`RunsInCheckTable.reaches_iff`).

Each operation is checked once by replaying its trace in the table of the
check: the lookup of the theorem at five, twenty steps
(`oneTable_lookup_replays`); the instantiation of the axiom of the control
theory, twenty-six steps (`oneTable_instance_replays`); the reflexivity of a
constant, twelve steps (`oneTable_conversion_replays`).

Negative: a call does not run to two values (`RunsInCheckTable.unique`), and
the lookup of five does not reach the run of the declaration at three
(`oneTable_lookup_not_first`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host dataEqualityHost Applies natural encodeLookupResult
    encodeLookupResult_injective)
open Mettapedia.Languages.MM0.Kernel
  (TheoremDecl TheoremInstance ConvWitness ConversionResult Context Preterm)
open Mettapedia.Languages.MM0.Presentation.Calculus
  (lookupComputation instanceComputation conversionComputation)
open Mettapedia.Languages.MM0.Presentation.Calculus.Controls (withAxiom axiomDecl constant)
open Mettapedia.Languages.MM0.Presentation.ComputationalTyping (encodeTable)
open Mettapedia.Languages.MM0.Presentation.ComputationalContext (encodeContext)
open Mettapedia.Languages.MM0.Presentation.ComputationalArguments (encodeExpressions)
open Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions (encodeDefinitions)
open Mettapedia.Languages.MM0.Presentation.ComputationalConversion
  (encodeWitness encodeConversion encodeConversion_injective)
open Mettapedia.Languages.MM0.Presentation.ComputationalProof
  (encodeTheorem encodeTheorems encodeInstance encodeInstance_injective)
open Mettapedia.Languages.MM0.Presentation.ComputationalAdmission (encodeTheorem_injective)
open Mettapedia.Languages.MM0.Presentation.ComputationalCalculus
  (calculusProgram theory_lookup_computes theory_instance_computes theory_convert_computes)
open Mettapedia.Logic.HostingStyles.AtomsReduce (atomsReduce atomsReduceTheory closedAtom)

/-- **What the candidate does with a call in the space of the table of the
check**: the run of the call reaches the run of the value, and every run
without transition that it reaches is that one. -/
def RunsInCheckTable (head : String) (arguments : List EngineTerm) (value : EngineTerm) : Prop :=
  atomsReduceTheory.Reaches (callRun letterSpelling checkTable head arguments)
      (valueRun letterSpelling checkTable value) ∧
    ∀ target : Contexts.Term atomsReduce closedAtom,
      atomsReduceTheory.Reaches (callRun letterSpelling checkTable head arguments) target →
      (∀ next, ¬ atomsReduceTheory.rewrites target next) →
        target = valueRun letterSpelling checkTable value

/-- **A call of a head that the check reaches, answered by the program of the
check, runs to its value in the space of the table of the check.** -/
theorem checkTable_runs {head : String} {arguments : List EngineTerm} {value : EngineTerm}
    (inHeads : head ∈ certificateHeads)
    (defined : calculusProgram.definesAt head arguments.length = true)
    (applies : Applies calculusProgram dataEqualityHost head arguments value) :
    RunsInCheckTable head arguments value := by
  have partDefined := (definesAt_partAt inHeads arguments.length).trans defined
  have partApplies := (applies_partAt_iff certificateHeads_closed dataEqualityHost inHeads
    arguments defined value).mpr applies
  exact ⟨check_stores.run_reaches partDefined partApplies, fun target reaches normal =>
    check_stores.run_unique check_stored.orthogonal partDefined partApplies reaches normal⟩

namespace RunsInCheckTable

variable {head : String} {arguments : List EngineTerm}

/-- **Negative**: a call does not run to two values. -/
theorem unique {first second : EngineTerm} (toFirst : RunsInCheckTable head arguments first)
    (toSecond : RunsInCheckTable head arguments second) : first = second :=
  valueRun_injective letterSpelling_injective checkTable
    (toSecond.2 _ toFirst.1 (check_stores.run_value_normal first))

/-- A call that runs to the encoding of what a function returns reaches the
run of an encoded result exactly when the function returns that result, for
an encoding that identifies no two results. -/
theorem reaches_iff {Result : Type} {encodeResult : Result → EngineTerm}
    (injective : Function.Injective encodeResult) {returned : Result}
    (runs : RunsInCheckTable head arguments (encodeResult returned)) (result : Result) :
    atomsReduceTheory.Reaches (callRun letterSpelling checkTable head arguments)
        (valueRun letterSpelling checkTable (encodeResult result)) ↔
      returned = result := by
  constructor
  · intro reaches
    exact (injective (valueRun_injective letterSpelling_injective checkTable
      (runs.2 _ reaches (check_stores.run_value_normal _)))).symm
  · rintro rfl
    exact runs.1

end RunsInCheckTable

set_option maxRecDepth 100000 in
/-- The check reaches the three operations, each at its arity. -/
theorem operations_in_check :
    ("nik:nat-table-get" ∈ certificateHeads ∧
        calculusProgram.definesAt "nik:nat-table-get" 2 = true) ∧
      ("mm0:instantiate-theorem" ∈ certificateHeads ∧
        calculusProgram.definesAt "mm0:instantiate-theorem" 4 = true) ∧
      ("mm0:conversion" ∈ certificateHeads ∧
        calculusProgram.definesAt "mm0:conversion" 4 = true) := by
  decide +kernel

/-! ## The three operations, with the kernel's functions -/

/-- **The table of the check runs the lookup of a theorem**, to the encoding
of what the kernel's function returns. -/
theorem oneTable_lookup (T : Mettapedia.Languages.MM0.Kernel.Theory) (index : Nat) :
    RunsInCheckTable "nik:nat-table-get" [encodeTheorems T.theorems, natural index]
      (encodeLookupResult ((T.theoremSignature index).map encodeTheorem)) :=
  checkTable_runs operations_in_check.1.1 operations_in_check.1.2 (theory_lookup_computes T index)

/-- **The table of the check runs the instantiation of a theorem**, to the
encoding of what the kernel's function returns. -/
theorem oneTable_instance (T : Mettapedia.Languages.MM0.Kernel.Theory) (context : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) :
    RunsInCheckTable "mm0:instantiate-theorem"
      [encodeTable T.terms, encodeContext context, encodeTheorem declaration,
        encodeExpressions arguments]
      (encodeInstance (declaration.instantiate? T.termSignature context arguments)) :=
  checkTable_runs operations_in_check.2.1.1 operations_in_check.2.1.2
    (theory_instance_computes T context declaration arguments)

/-- **The table of the check runs the conversion by a witness**, to the
encoding of what the kernel's function returns. -/
theorem oneTable_conversion (T : Mettapedia.Languages.MM0.Kernel.Theory) (context : Context)
    (witness : ConvWitness) :
    RunsInCheckTable "mm0:conversion"
      [encodeTable T.terms, encodeDefinitions T.definitions, encodeContext context,
        encodeWitness witness]
      (encodeConversion (witness.conversion? T.termSignature T.definitionSignature context)) :=
  checkTable_runs operations_in_check.2.2.1 operations_in_check.2.2.2
    (theory_convert_computes T context witness)

/-- **The run of the lookup reaches the run of an encoded result exactly when
the kernel's function returns that result.** -/
theorem oneTable_lookup_iff (T : Mettapedia.Languages.MM0.Kernel.Theory) (index : Nat)
    (result : Option TheoremDecl) :
    atomsReduceTheory.Reaches
        (callRun letterSpelling checkTable "nik:nat-table-get"
          [encodeTheorems T.theorems, natural index])
        (valueRun letterSpelling checkTable (encodeLookupResult (result.map encodeTheorem))) ↔
      T.theoremSignature index = result :=
  RunsInCheckTable.reaches_iff
    (encodeResult := fun found : Option TheoremDecl => encodeLookupResult (found.map encodeTheorem))
    (fun _ _ same => Option.map_injective encodeTheorem_injective
      (encodeLookupResult_injective same))
    (oneTable_lookup T index) result

/-- **The run of the instantiation reaches the run of an encoded result
exactly when the kernel's function returns that result.** -/
theorem oneTable_instance_iff (T : Mettapedia.Languages.MM0.Kernel.Theory) (context : Context)
    (declaration : TheoremDecl) (arguments : List Preterm) (result : Option TheoremInstance) :
    atomsReduceTheory.Reaches
        (callRun letterSpelling checkTable "mm0:instantiate-theorem"
          [encodeTable T.terms, encodeContext context, encodeTheorem declaration,
            encodeExpressions arguments])
        (valueRun letterSpelling checkTable (encodeInstance result)) ↔
      declaration.instantiate? T.termSignature context arguments = result :=
  RunsInCheckTable.reaches_iff (encodeResult := encodeInstance) encodeInstance_injective
    (oneTable_instance T context declaration arguments) result

/-- **The run of the conversion reaches the run of an encoded result exactly
when the kernel's function returns that result.** -/
theorem oneTable_conversion_iff (T : Mettapedia.Languages.MM0.Kernel.Theory) (context : Context)
    (witness : ConvWitness) (result : Option ConversionResult) :
    atomsReduceTheory.Reaches
        (callRun letterSpelling checkTable "mm0:conversion"
          [encodeTable T.terms, encodeDefinitions T.definitions, encodeContext context,
            encodeWitness witness])
        (valueRun letterSpelling checkTable (encodeConversion result)) ↔
      witness.conversion? T.termSignature T.definitionSignature context = result :=
  RunsInCheckTable.reaches_iff (encodeResult := encodeConversion) encodeConversion_injective
    (oneTable_conversion T context witness) result

/-- **Negative**: in the theory with theorems at three and five, the run of
the lookup of five does not reach the run of the declaration at three. -/
theorem oneTable_lookup_not_first :
    ¬ atomsReduceTheory.Reaches
        (callRun letterSpelling checkTable "nik:nat-table-get"
          [encodeTheorems twoTheorems.theorems, natural 5])
        (valueRun letterSpelling checkTable
          (encodeLookupResult (some (encodeTheorem ⟨[], [], .term 0⟩)))) := by
  intro reaches
  have found := (oneTable_lookup_iff twoTheorems 5 (some ⟨[], [], .term 0⟩)).mp reaches
  revert found
  decide

/-! ## Each operation once, replayed in the table of the check -/

set_option maxRecDepth 100000 in
/-- **The lookup, replayed**: twenty steps take the call of the lookup of
five, in the theory with theorems at three and five, to the reading of the
encoded second declaration.  Two entries of the list are viewed, and the
index is compared with three and with five. -/
theorem oneTable_lookup_replays :
    replay checkTable
        [([], 130), ([true, false, true], 311), ([], 132), ([true, false, true], 317),
          ([true, false, true], 321), ([true, false, true], 321), ([true, false, true], 321),
          ([true, false, true], 320), ([], 134), ([], 130), ([true, false, true], 311),
          ([], 132), ([true, false, true], 317), ([true, false, true], 321),
          ([true, false, true], 321), ([true, false, true], 321), ([true, false, true], 321),
          ([true, false, true], 321), ([true, false, true], 318), ([], 133)]
        (callTerm "nik:nat-table-get"
          (data letterSpelling ((lookupComputation twoTheorems).encodeQuery 5))) =
      some (datum letterSpelling
        ((lookupComputation twoTheorems).encodeAnswer (some ⟨[], [.term 0], .term 1⟩))) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The instantiation, replayed**: twenty-six steps take the call of the
instantiation of the axiom of the control theory, at no argument, to the
reading of its encoded instance. -/
theorem oneTable_instance_replays :
    replay checkTable
        [([], 195), ([true, false, true], 97), ([true, false, true, true, false, true], 72),
          ([true, false, true, true, false, true, true, false, true], 310),
          ([true, false, true, true, false, true, true, true, false, true], 310),
          ([true, false, true, true, false, true], 73), ([true, false, true], 99),
          ([true, false, true, true, true, false, true], 79),
          ([true, false, true, true, true, false, true, true, false, true], 310),
          ([true, false, true, true, true, false, true, true, true, false, true], 310),
          ([true, false, true, true, true, false, true], 80), ([true, false, true], 100),
          ([true, false, true], 92), ([true, false, true, true, false, true], 310),
          ([true, false, true], 93), ([], 197), ([true, true, true, false, true], 112),
          ([true, true, true, false, true, true, false, true], 310),
          ([true, true, true, false, true], 113), ([], 198), ([true, false, true], 188),
          ([true, false, true, true, false, true], 310), ([true, false, true], 189), ([], 200),
          ([true, false, true], 102), ([], 202)]
        (callTerm "mm0:instantiate-theorem"
          (data letterSpelling
            ((instanceComputation withAxiom).encodeQuery ([], axiomDecl, [])))) =
      some (datum letterSpelling
        ((instanceComputation withAxiom).encodeAnswer (some ⟨[], constant⟩))) := by
  rw [instance_instance_query]
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The conversion, replayed**: twelve steps take the call of the
reflexivity of the constant, in the theory with one constant, to the reading
of the encoded conversion. -/
theorem oneTable_conversion_replays :
    replay checkTable
        [([], 150), ([true, false, true], 11), ([true, false, true, true, false, true], 5),
          ([true, false, true, true, false, true, true, false, true], 311),
          ([true, false, true, true, false, true], 7),
          ([true, false, true, true, false, true, true, false, true], 317),
          ([true, false, true, true, false, true, true, false, true], 318),
          ([true, false, true, true, false, true], 8), ([true, false, true], 17), ([], 152),
          ([true, false, true], 310), ([], 153)]
        (callTerm "mm0:conversion"
          (data letterSpelling
            ((conversionComputation oneConstant).encodeQuery ([], .refl (.term 0))))) =
      some (datum letterSpelling
        ((conversionComputation oneConstant).encodeAnswer (some ⟨.term 0, .term 0, 0⟩))) := by
  rw [conversion_instance_query]
  decide +kernel

#print axioms checkTable_runs
#print axioms RunsInCheckTable.unique
#print axioms RunsInCheckTable.reaches_iff
#print axioms oneTable_lookup
#print axioms oneTable_instance
#print axioms oneTable_conversion
#print axioms oneTable_lookup_iff
#print axioms oneTable_instance_iff
#print axioms oneTable_conversion_iff
#print axioms oneTable_lookup_not_first
#print axioms oneTable_lookup_replays
#print axioms oneTable_instance_replays
#print axioms oneTable_conversion_replays

end Mettapedia.Logic.HostingStyles.StoredPrograms
