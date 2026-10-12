import Mettapedia.Logic.HostingStyles.NameEquality.RunningNames
import Mettapedia.Logic.HostingStyles.StoredPrograms.Verification

/-!
# MM0's kernel on whole developments, with names as constants

The kernel admits the declarations of a development in order, and its public
entry does so against a specification.  Both are equation programs, and with
names in letters their tables have 453 and 497 rules.  Here they are read with
every name one constant, over the test of names, as the check of a certificate
is.

| | admission of a development | verification against a specification |
|---|---|---|
| table | `admissionTableNames`, 440 rules (`admissionNames_size`) | `verificationTableNames`, 484 rules (`verificationNames_size`) |
| rules of equations, ordered rules | 367 and 6 (`admissionNames_partSizes`) | 384 and 33 (`verificationNames_partSizes`) |
| stored table | `admissionNames_stored` | `verificationNames_stored` |
| stores the part over the test | `admissionNames_stores` | `verificationNames_stores` |
| run by the candidate, with the kernel's function | `admissionNames_run_iff` | `verificationNames_run_iff` |

In each case the run of the call, in the space that stores the table and the
rules of the family for the names of the call, reaches the run of an encoded
result exactly when the kernel's function returns that result.  The facts
about the two programs are those of the tables with letters; only the ordered
rules are tested again.

Positive and negative: the development of four declarations is verified
against its specification, and the development with a second axiom is refused
(`verificationNames_instance_verified`, `verificationNames_instance_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host dataEqualityHost Applies)
open Mettapedia.GSLT.Dedukti (RewriteRule Step Reduces)
open Mettapedia.Languages.MM0.Kernel (Admission SpecificationEntry ProofDeclaration)
open Mettapedia.Languages.MM0.Presentation.ComputationalAdmission
  (admissionProgram encodeAdmissions encodeTheoryResult encodeTheoryResult_injective
    start_computes)
open Mettapedia.Languages.MM0.Presentation.ComputationalSpecification
  (specificationProgram encodeEntries encodeProofDeclarations verify_computes)
open Mettapedia.Languages.MM0.Presentation.ComputationalSpecification.Controls
  (public_theorem_has_checked_proof specification_rejects_that_extra_axiom)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (RunnableEquations programTheory atomsReduce atomsReduceTheory closedAtom)
open Mettapedia.Logic.HostingStyles.StoredPrograms

namespace StoresWithNames

variable {rules : List RewriteRule} {program : Program} {host : Host} {primitives : List String}

/-- **A call that the engine answers with the encoding of what a function
returns**: the run of the call, in the space of a list of names that holds the
fixed names of the theory and those of the call, reaches the run of an encoded
result exactly when the function returns that result, for an encoding that
identifies no two results. -/
theorem run_result_iff (stores : StoresWithNames rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) {names : List String}
    (covers : ∀ name ∈ fixedNames rules, name ∈ names) {Result : Type}
    {encodeResult : Result → EngineTerm} (encodeInjective : Function.Injective encodeResult)
    {head : String} {arguments : List EngineTerm}
    (within : NamesWithin names (callTerm head (data constantSpelling arguments)))
    (defined : program.definesAt head arguments.length = true) {returned : Result}
    (applies : Applies program host head arguments (encodeResult returned)) (result : Result) :
    atomsReduceTheory.Reaches
        (localRun rules names (callTerm head (data constantSpelling arguments)))
        (localRun rules names (datum constantSpelling (encodeResult result))) ↔
      returned = result := by
  constructor
  · intro reaches
    have same := stores.run_unique orthogonal covers within defined applies reaches
      (stores.run_value_normal names _)
    exact (encodeInjective (datum_injective constantSpelling_injective
      (localRun_injective rules names same))).symm
  · rintro rfl
    exact stores.run_reaches covers within defined applies

end StoresWithNames

/-! ## The admission of a development -/

/-- **The table that runs the admission with names as constants**: 440
rules. -/
abbrev admissionTableNames : List RewriteRule :=
  partTableIn constantSpelling admissionProgram admissionHeads admissionOrdered

set_option maxRecDepth 100000 in
/-- The ordered rules of its one ordered head are a stored table. -/
theorem admissionNames_ordered_stored :
    StoredTable (orderedPartIn constantSpelling admissionProgram admissionOrdered) :=
  storedTable_of_check (by decide +kernel)

/-- **The table is a stored table**, hence orthogonal. -/
theorem admissionNames_stored : StoredTable admissionTableNames :=
  storedTable_partTableIn constantSpelling_apart admission_text admission_separated
    admission_noPrimitive admissionNames_ordered_stored libraryConstants_fit

set_option maxRecDepth 100000 in
/-- **The table stores the part of the program over the test of names.** -/
theorem admissionNames_stores :
    StoresWithNames admissionTableNames (partAt admissionProgram admissionHeads)
      dataEqualityHost largerPrimitives :=
  storesWithNames_partTable admission_text admission_calls admissionHeads_closed
    (by decide +kernel) admissionNames_stored

set_option maxRecDepth 100000 in
/-- **The sizes of the first two parts of the table**: 367 rules of equations
of the unordered heads and six ordered rules. -/
theorem admissionNames_partSizes :
    (partRules constantSpelling admissionProgram admissionHeads admissionOrdered
        .equations).length = 367 ∧
      (partRules constantSpelling admissionProgram admissionHeads admissionOrdered
        .ordered).length = 6 := by
  refine ⟨?_, ?_⟩
  · rw [partRules, List.length_map]
    decide +kernel
  · decide +kernel

/-- 367 rules of equations, six ordered rules and the sixty-seven of the
library: 440 rules, beside the 453 with names in letters. -/
theorem admissionNames_size : admissionTableNames.length = 440 := by
  have sizes := admissionNames_partSizes
  simp only [partRules, List.length_map] at sizes
  rw [partTableIn_length, sizes.1, sizes.2]

/-- The call of the admission of a list of declarations, as a term. -/
def admissionCall (admissions : List Admission) : LF.Term :=
  callTerm "mm0:admission-start" (data constantSpelling [encodeAdmissions admissions])

/-- **The run of the admission** of a list of declarations, in the space that
stores the table and the rules of the family for the names of the call. -/
def admissionRunNames (admissions : List Admission) : Contexts.Term atomsReduce closedAtom :=
  localRun admissionTableNames (namesFor admissionTableNames (admissionCall admissions))
    (admissionCall admissions)

/-- **The run of a result of the admission**, in the space of a call: an
encoded theory, or the refusal. -/
def admittedRunNames (admissions : List Admission)
    (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    Contexts.Term atomsReduce closedAtom :=
  localRun admissionTableNames (namesFor admissionTableNames (admissionCall admissions))
    (datum constantSpelling (encodeTheoryResult result))

/-- **The candidate runs the kernel on a whole development, with names as
constants**: the run of the admission of a list of declarations reaches the
run of an encoded result exactly when the kernel's function returns that
result. -/
theorem admissionNames_run_iff (admissions : List Admission)
    (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    atomsReduceTheory.Reaches (admissionRunNames admissions)
        (admittedRunNames admissions result) ↔
      Mettapedia.Languages.MM0.Kernel.Theory.run? {} admissions = result :=
  admissionNames_stores.run_result_iff admissionNames_stored.orthogonal (namesFor_covers _ _)
    encodeTheoryResult_injective (namesFor_within _ _) (admissionPart_defined admissions)
    ((admissionPart_applies_iff admissions _).mpr (start_computes admissions)) result

/-! ## The verification against a specification -/

/-- **The table that runs the verification with names as constants**: 484
rules. -/
abbrev verificationTableNames : List RewriteRule :=
  partTableIn constantSpelling specificationProgram verificationHeads verificationOrdered

set_option maxRecDepth 100000 in
/-- The ordered rules of its three ordered heads are a stored table. -/
theorem verificationNames_ordered_stored :
    StoredTable (orderedPartIn constantSpelling specificationProgram verificationOrdered) :=
  storedTable_of_check (by decide +kernel)

/-- **The table is a stored table**, hence orthogonal. -/
theorem verificationNames_stored : StoredTable verificationTableNames :=
  storedTable_partTableIn constantSpelling_apart verification_text verification_separated
    verification_noPrimitive verificationNames_ordered_stored libraryConstants_fit

set_option maxRecDepth 100000 in
/-- **The table stores the part of the program over the test of names.** -/
theorem verificationNames_stores :
    StoresWithNames verificationTableNames (partAt specificationProgram verificationHeads)
      dataEqualityHost largerPrimitives :=
  storesWithNames_partTable verification_text verification_calls verificationHeads_closed
    (by decide +kernel) verificationNames_stored

set_option maxRecDepth 100000 in
/-- **The sizes of the first two parts of the table**: 384 rules of equations
of the unordered heads and thirty-three ordered rules. -/
theorem verificationNames_partSizes :
    (partRules constantSpelling specificationProgram verificationHeads verificationOrdered
        .equations).length = 384 ∧
      (partRules constantSpelling specificationProgram verificationHeads verificationOrdered
        .ordered).length = 33 := by
  refine ⟨?_, ?_⟩
  · rw [partRules, List.length_map]
    decide +kernel
  · decide +kernel

/-- 384 rules of equations, thirty-three ordered rules and the sixty-seven of
the library: 484 rules, beside the 497 with names in letters. -/
theorem verificationNames_size : verificationTableNames.length = 484 := by
  have sizes := verificationNames_partSizes
  simp only [partRules, List.length_map] at sizes
  rw [partTableIn_length, sizes.1, sizes.2]

/-- The call of the verification of the declarations of a development against
a specification, as a term. -/
def verificationCall (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) : LF.Term :=
  callTerm "mm0:spec-verify" (data constantSpelling
    [encodeEntries specification, encodeProofDeclarations declarations])

/-- **The run of the verification**, in the space that stores the table and
the rules of the family for the names of the call. -/
def verificationRunNames (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) : Contexts.Term atomsReduce closedAtom :=
  localRun verificationTableNames
    (namesFor verificationTableNames (verificationCall specification declarations))
    (verificationCall specification declarations)

/-- **The run of a result of the verification**, in the space of a call. -/
def verifiedRunNames (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration)
    (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    Contexts.Term atomsReduce closedAtom :=
  localRun verificationTableNames
    (namesFor verificationTableNames (verificationCall specification declarations))
    (datum constantSpelling (encodeTheoryResult result))

/-- **The candidate verifies a development against a specification, with names
as constants**: the run of the verification reaches the run of an encoded
result exactly when the kernel's function returns that result. -/
theorem verificationNames_run_iff (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration)
    (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    atomsReduceTheory.Reaches (verificationRunNames specification declarations)
        (verifiedRunNames specification declarations result) ↔
      Mettapedia.Languages.MM0.Kernel.SpecificationAdmission.verify? specification declarations =
        result :=
  verificationNames_stores.run_result_iff verificationNames_stored.orthogonal
    (namesFor_covers _ _) encodeTheoryResult_injective (namesFor_within _ _)
    (verificationPart_defined specification declarations)
    ((verificationPart_applies_iff specification declarations _).mpr
      (verify_computes specification declarations)) result

/-- **Positive**: the run of the verification of the development of four
declarations against its specification reaches the run of its theory. -/
theorem verificationNames_instance_verified :
    atomsReduceTheory.Reaches (verificationRunNames restatedSpecification restatedDeclarations)
      (verifiedRunNames restatedSpecification restatedDeclarations (some restatedTheory)) :=
  verificationNames_stores.run_reaches (namesFor_covers _ _) (namesFor_within _ _)
    (verificationPart_defined restatedSpecification restatedDeclarations)
    ((verificationPart_applies_iff restatedSpecification restatedDeclarations _).mpr
      public_theorem_has_checked_proof)

/-- **Negative**: a second axiom is not in the specification: the run of the
verification reaches the run of the refusal, and the run of no theory. -/
theorem verificationNames_instance_refused :
    atomsReduceTheory.Reaches
        (verificationRunNames axiomSpecification secondAxiomDeclarations)
        (verifiedRunNames axiomSpecification secondAxiomDeclarations none) ∧
      ∀ theory : Mettapedia.Languages.MM0.Kernel.Theory,
        ¬ atomsReduceTheory.Reaches
          (verificationRunNames axiomSpecification secondAxiomDeclarations)
          (verifiedRunNames axiomSpecification secondAxiomDeclarations (some theory)) := by
  have refused : atomsReduceTheory.Reaches
      (verificationRunNames axiomSpecification secondAxiomDeclarations)
      (verifiedRunNames axiomSpecification secondAxiomDeclarations none) :=
    verificationNames_stores.run_reaches (namesFor_covers _ _) (namesFor_within _ _)
      (verificationPart_defined axiomSpecification secondAxiomDeclarations)
      ((verificationPart_applies_iff axiomSpecification secondAxiomDeclarations _).mpr
        specification_rejects_that_extra_axiom)
  refine ⟨refused, fun theory reaches => ?_⟩
  have none_ := (verificationNames_run_iff axiomSpecification secondAxiomDeclarations none).mp
    refused
  have some_ := (verificationNames_run_iff axiomSpecification secondAxiomDeclarations
    (some theory)).mp reaches
  rw [none_] at some_
  cases some_

#print axioms StoresWithNames.run_result_iff
#print axioms admissionNames_stored
#print axioms admissionNames_stores
#print axioms admissionNames_partSizes
#print axioms admissionNames_size
#print axioms admissionNames_run_iff
#print axioms verificationNames_stored
#print axioms verificationNames_stores
#print axioms verificationNames_partSizes
#print axioms verificationNames_size
#print axioms verificationNames_run_iff
#print axioms verificationNames_instance_verified
#print axioms verificationNames_instance_refused

end Mettapedia.Logic.HostingStyles.NameEquality
