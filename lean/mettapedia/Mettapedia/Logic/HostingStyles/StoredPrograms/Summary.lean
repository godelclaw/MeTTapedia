import Mettapedia.Logic.HostingStyles.StoredPrograms.Instantiation
import Mettapedia.Logic.HostingStyles.StoredPrograms.Conversion
import Mettapedia.Logic.HostingStyles.StoredPrograms.Check
import Mettapedia.Logic.HostingStyles.StoredPrograms.Inventory
import Mettapedia.Logic.HostingStyles.StoredPrograms.Obstruction
import Mettapedia.Logic.HostingStyles.StoredPrograms.OneTable
import Mettapedia.Logic.HostingStyles.StoredPrograms.Verification

/-!
# The candidate runs stored programs: the table

The candidate in which atoms reduce runs the rules that its space stores.  An
equation program of the shared engine is read as such rules, and the engine's
value for a call is what the candidate's reduction reaches from the run of the
call.  This module holds the table of the results, and the same statements
for the member of the ambient family at the space of the table.

## The kernel of MM0, run by the candidate's own reduction

| | theorem at an index | instance of a theorem | conversion by a witness | check of a certificate |
|---|---|---|---|---|
| head | `nik:nat-table-get` | `mm0:instantiate-theorem` | `mm0:conversion` | `mm0:certificate` |
| program, equations | 5 | 233, of which it reaches 130 | 193, of which it reaches 168 | 280, of which it reaches 252 |
| host primitives called | list view, equality of numbers | list view and former, zero test, predecessor, equality of numbers, sum | list view and former, zero test, predecessor, equality of numbers, **equality of data** | those, the sum and the strict order |
| host primitives that it reaches | the two | six, without the equality of data (`instanceProgram_inventory`) | six, with the equality of data and without the sum (`conversionPart_inventory`) | the eight (`checkPart_inventory`) |
| free of host primitives | no | no | no | no |
| `let` | none | none | none | none |
| overlapping pairs reached | none | none | 1 | 15 |
| names written as | constants | constants | letters | letters |
| heads tried in order | none | none | 1 | 6 |
| translated | `lookup_stores` | `instance_stores` | `conversion_stores` | `check_stores` |
| stored rules | 24 | 149 | 252 | 390 |
| table orthogonal | `lookup_orthogonal` | `instance_orthogonal` | `conversion_stored` | `check_stored` |
| run by the candidate | `theoremLookup_run_iff` | `theoremInstance_run_iff` | `conversion_run_iff` | `check_run_iff_derives`, `check_run_accepts_iff`, `witness_run_iff` |
| run by the ambient member | `theoremLookup_member_iff` | `theoremInstance_member_iff` | `conversion_member_iff` | `check_member_iff_derives` |
| one instance by running the table | `lookup_instance_runs`, 20 steps | `instance_instance_runs`, 26 steps | `conversion_instance_replays`, 12 steps, and `conversion_instance_refuses`, 7 steps | not run |
| run by the table of the check, with the kernel's function | `oneTable_lookup_iff` | `oneTable_instance_iff` | `oneTable_conversion_iff` | the check itself |
| one instance replayed in the table of the check | `oneTable_lookup_replays`, 20 steps | `oneTable_instance_replays`, 26 steps | `oneTable_conversion_replays`, 12 steps | not run |

The inventory of the programs and of their fourteen parts is
`kernelParts_inventory`.  The 390 rules of the check run the three operations
as well, each to the encoding of what the kernel's function returns
(`RunsInCheckTable`, `checkTable_runs`).  Of the check itself one accepted
and one refused instance are stated (`check_axiom_accepted`,
`check_missing_axiom_refused`); they follow from the general theorem and are
not runs of the table.

## The kernel on whole developments

MM0's kernel admits the declarations of a development in order, each checked
against the theory admitted so far, a theorem only with its checked proof;
its public entry does so against a specification.  Both are equation programs
of the class, and their tables are built as the table of the check.

| | admission of a development | verification against a specification |
|---|---|---|
| head | `mm0:admission-start` | `mm0:spec-verify` |
| program, equations | 372, of which it reaches 369 | 404, of which it reaches 395 |
| host primitives called | seven, the equality of data among them (`admission_primitives`) | the same seven (`verification_primitives`) |
| `let` | none | none |
| overlapping pairs | 1 (`admission_overlaps`) | 8 (`verification_overlaps`) |
| heads tried in order | 1 | 3 |
| translated | `admission_stores` | `verification_stores` |
| stored rules | 453 (`admission_size`) | 497 (`verification_size`) |
| table orthogonal | `admission_stored` | `verification_stored` |
| run by the candidate, with the kernel's function | `admission_run_iff`, `admission_run_unique` | `verification_run_iff`, `verification_run_unique` |
| run by the ambient member | `admission_member_iff` | `verification_member_iff` |
| one instance accepted, one refused | `admission_instance_admitted`, `admission_instance_refused` | `verification_instance_verified`, `verification_instance_refused` |
| one instance replayed in the table | `admission_instance_replays`, 343 steps, and `admission_refusal_replays`, 26 steps | not run |

The instances of the admission are replayed in its table: four declarations,
one of them a theorem with its proof, in 343 steps.  The instances of the
verification follow from the general theorem and the kernel's controls; they
are not runs of the table.

## The three separations

| | positive | negative |
|---|---|---|
| **First match.** The engine takes the first matching equation; a table has no order. | The engine's value is a reduct of the call for every program of the class, overlapping or not (`stored_value_reached`).  For a separated program the order does not matter (`Separated.select_of_matches`) and the table is orthogonal (`separated_orthogonal`).  For the others the order is put into rules, one question for each equation tried (`dispatches_of_tables`, `chain_reduces`). | With two equations for one left side the table reaches both values (`firstMatch_witness`).  The conversion has such a pair (`conversionEquations_not_separated`). |
| **Arguments first.** The engine evaluates arguments first; the candidate steps at any position. | In an orthogonal table every normal form that a call reaches is the engine's value (`Stores.normalForm_unique`); every datum is a normal form (`datum_normal`). | Without a value from the engine the table may reach one: an argument that does not end and is not used (`unusedArgument_witness`). |
| **Primitives.** The programs call primitives of a host. | Nineteen rules for the seven primitives of the shared host, numbers in unary and lists as cells (`shared_realized`); sixty-one rules for the equality of data, names in letters (`dataEquality_realized`).  They agree with the host on all data. | With a name written as a constant no finite table decides the equality of two symbols (`no_table_decides_constants`). |

A fourth separation was found: **a repeated variable**.  The engine binds it
at its first occurrence and does not compare; a rule compares
(`repeatedVariable_witness`).  The class asks that no variable occur twice.

## The class

`Storable program host primitives`: no variable twice in a left side, no
special form in a right side (`let` on three arguments, `metta-nullary` on
one), right sides bound, and the host handles a head that a right side calls
exactly when the head is one of the primitives that the table computes.  One
arity for a head is not asked: a call carries its arguments in cells.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves (CompactProof)
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (Applies boolean dataEqualityHost)
open Mettapedia.Languages.MM0.Kernel
  (TheoremDecl TheoremInstance ConvWitness ConversionResult Context Preterm)
open Mettapedia.Languages.MM0.Presentation.Calculus
  (lookupComputation instanceComputation conversionComputation family derivesJ)
open Mettapedia.Languages.MM0.Presentation.ComputationalCalculus
  (calculusProgram request certificate_computes derives_of_returned returned_of_derives)
open Mettapedia.Languages.MM0.Kernel (Admission SpecificationEntry ProofDeclaration)
open Mettapedia.Languages.MM0.Presentation.ComputationalAdmission
  (admissionProgram encodeAdmissions encodeTheoryResult encodeTheoryResult_injective
    start_computes start_result_exact)
open Mettapedia.Languages.MM0.Presentation.ComputationalSpecification
  (specificationProgram encodeEntries encodeProofDeclarations verify_computes
    verify_result_exact)
open Mettapedia.Logic.HostingStyles.AmbientSpace (ambientTheory listSpace atomTerm)

/-- **The member at the space of the lookup table runs the lookup of a
theorem**: the atom of the call reaches the atom of an encoded declaration
exactly when the theory declares that theorem at the index. -/
theorem theoremLookup_member_iff (T : Mettapedia.Languages.MM0.Kernel.Theory) (index : Nat)
    (declaration : TheoremDecl) :
    (ambientTheory (listSpace lookupTable)).Reaches
        (atomTerm 0 (callTerm "nik:nat-table-get"
          (data constantSpelling ((lookupComputation T).encodeQuery index))))
        (atomTerm 0 (datum constantSpelling
          ((lookupComputation T).encodeAnswer (some declaration)))) ↔
      T.theoremSignature index = some declaration :=
  lookup_stores.authored_member_iff (lookupComputation T)
    (programTheory_orthogonal lookup_orthogonal) constantSpelling_injective index
    (theoremLookup_defined T index) declaration

/-- **The member at the space of the instance table runs the instantiation of
a theorem.** -/
theorem theoremInstance_member_iff (T : Mettapedia.Languages.MM0.Kernel.Theory)
    (context : Context) (declaration : TheoremDecl) (arguments : List Preterm)
    (result : TheoremInstance) :
    (ambientTheory (listSpace instanceTable)).Reaches
        (atomTerm 0 (callTerm "mm0:instantiate-theorem"
          (data constantSpelling
            ((instanceComputation T).encodeQuery (context, declaration, arguments)))))
        (atomTerm 0 (datum constantSpelling ((instanceComputation T).encodeAnswer (some result)))) ↔
      TheoremDecl.Instantiates T.termSignature context declaration arguments result :=
  instance_stores.authored_member_iff (instancePart T) instance_orthogonal
    constantSpelling_injective (context, declaration, arguments)
    ((definesAt_partAt instance_defined.2 4).trans instance_defined.1) result

/-- **The member at the space of the conversion table runs the conversion.** -/
theorem conversion_member_iff (T : Mettapedia.Languages.MM0.Kernel.Theory) (context : Context)
    (witness : ConvWitness) (result : ConversionResult) :
    (ambientTheory (listSpace conversionTable)).Reaches
        (atomTerm 0 (callTerm "mm0:conversion"
          (data letterSpelling ((conversionComputation T).encodeQuery (context, witness)))))
        (atomTerm 0 (datum letterSpelling ((conversionComputation T).encodeAnswer (some result)))) ↔
      ConvWitness.Checks T.termSignature T.definitionSignature context witness result.left
        result.right result.sort :=
  conversion_stores.authored_member_iff (conversionPart T) conversion_stored.orthogonal
    letterSpelling_injective (context, witness) conversionPart_defined result

/-- **The member at the space of the table of the check checks MM0 proofs**:
for some certificate, the atom of its check for the judgment reaches the atom
of `True`, exactly when MM0's kernel derives the judgment. -/
theorem check_member_iff_derives (T : Mettapedia.Languages.MM0.Kernel.Theory) (context : Context)
    (hypotheses : List Preterm) (expression : Preterm) :
    (∃ proof : CompactProof (family T).Leaf,
        (ambientTheory (listSpace checkTable)).Reaches
          (atomTerm 0 (callTerm "mm0:certificate"
            (data letterSpelling (request T (derivesJ context hypotheses expression) proof))))
          (atomTerm 0 (datum letterSpelling (boolean true)))) ↔
      Mettapedia.Languages.MM0.Kernel.Derives T.termSignature T.definitionSignature
        T.theoremSignature context hypotheses expression := by
  have total : ∀ proof, ∃ value, Applies (partAt calculusProgram certificateHeads)
      dataEqualityHost "mm0:certificate"
      (request T (derivesJ context hypotheses expression) proof) value :=
    fun proof => ⟨_, (checkPart_applies_iff T _ proof _).mpr (certificate_computes T _ proof)⟩
  constructor
  · rintro ⟨proof, reaches⟩
    exact derives_of_returned T ((checkPart_applies_iff T _ proof _).mp
      ((check_stores.member_reaches_iff check_stored.orthogonal letterSpelling_injective
        (checkPart_defined T _ proof) (total proof) (boolean true)).mp reaches))
  · intro derived
    obtain ⟨proof, returned⟩ := returned_of_derives T derived
    exact ⟨proof, check_stores.member_reaches (checkPart_defined T _ proof)
      ((checkPart_applies_iff T _ proof _).mpr returned)⟩

/-- **The member at the space of the admission table runs the kernel on a
whole development**: the atom of the call reaches the atom of an encoded
result exactly when the kernel's function returns that result. -/
theorem admission_member_iff (admissions : List Admission)
    (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    (ambientTheory (listSpace admissionTable)).Reaches
        (atomTerm 0 (callTerm "mm0:admission-start"
          (data letterSpelling [encodeAdmissions admissions])))
        (atomTerm 0 (datum letterSpelling (encodeTheoryResult result))) ↔
      Mettapedia.Languages.MM0.Kernel.Theory.run? {} admissions = result := by
  have total : ∃ value, Applies (partAt admissionProgram admissionHeads) dataEqualityHost
      "mm0:admission-start" [encodeAdmissions admissions] value :=
    ⟨_, (admissionPart_applies_iff admissions _).mpr (start_computes admissions)⟩
  exact (((admission_stores.member_reaches_iff admission_stored.orthogonal
    letterSpelling_injective (admissionPart_defined admissions) total _).trans
    (admissionPart_applies_iff admissions _)).trans (start_result_exact admissions _)).trans
    ⟨fun same => (encodeTheoryResult_injective same).symm, fun same => by rw [same]⟩

/-- **The member at the space of the verification table verifies a development
against a specification.** -/
theorem verification_member_iff (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration)
    (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    (ambientTheory (listSpace verificationTable)).Reaches
        (atomTerm 0 (callTerm "mm0:spec-verify"
          (data letterSpelling
            [encodeEntries specification, encodeProofDeclarations declarations])))
        (atomTerm 0 (datum letterSpelling (encodeTheoryResult result))) ↔
      Mettapedia.Languages.MM0.Kernel.SpecificationAdmission.verify? specification declarations =
        result := by
  have total : ∃ value, Applies (partAt specificationProgram verificationHeads) dataEqualityHost
      "mm0:spec-verify" [encodeEntries specification, encodeProofDeclarations declarations]
      value :=
    ⟨_, (verificationPart_applies_iff specification declarations _).mpr
      (verify_computes specification declarations)⟩
  exact (((verification_stores.member_reaches_iff verification_stored.orthogonal
    letterSpelling_injective (verificationPart_defined specification declarations) total _).trans
    (verificationPart_applies_iff specification declarations _)).trans
    (verify_result_exact specification declarations _)).trans
    ⟨fun same => (encodeTheoryResult_injective same).symm, fun same => by rw [same]⟩

#print axioms theoremLookup_member_iff
#print axioms theoremInstance_member_iff
#print axioms conversion_member_iff
#print axioms check_member_iff_derives
#print axioms admission_member_iff
#print axioms verification_member_iff

end Mettapedia.Logic.HostingStyles.StoredPrograms
