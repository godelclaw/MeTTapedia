import Mettapedia.Logic.HostingStyles.SpacesAndRegions.Stored
import Mettapedia.Logic.HostingStyles.StoredPrograms.Check
import Mettapedia.Logic.HostingStyles.StoredPrograms.Admission
import Mettapedia.Logic.HostingStyles.StoredPrograms.Verification

/-!
# The candidate of spaces and regions runs MM0's kernel

The three tables that run MM0's kernel as stored rules (the check of a
certificate, the admission of a development, the verification of a
development against a specification) store their programs, so none of their
rules has a variable as a left side (`stores_headed`), and the candidate of
spaces and regions runs them.  "MM0's kernel" is the model of the kernel in
this library with the equation programs that are proved to compute it.

For each table, in two forms: the **plain atom** of the call at the ambient
space of the table, and the **call inside a contained run** in the space of
the table, at every ambient space.

| | plain atom, at the space of the table | inside a contained run, at every ambient space |
|---|---|---|
| check of a certificate | `check_atom_iff_derives`, `check_atom_unique` | `check_region_iff_derives`, `check_region_unique` |
| admission of a development | `admission_atom_iff`, `admission_atom_unique` | `admission_region_iff`, `admission_region_unique` |
| verification against a specification | `verification_atom_iff`, `verification_atom_unique` | `verification_region_iff`, `verification_region_unique` |

One development is carried through by its replayed reduction and without the
general theorem: the admission of a sort, a constant, an axiom and a theorem
with its proof, whose 343 steps are replayed in Lean's kernel
(`admission_instance_replays`), is a reduction of the candidate in both forms
(`admission_instance_atom`, `admission_instance_region`).  Negative: a term
whose sort is not declared reaches the refusal and no theory
(`admission_refusal_atom`, `admission_refusal_atom_no_theory`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves (CompactProof check)
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (Applies boolean dataEqualityHost)
open Mettapedia.Languages.MM0.Kernel (Context Preterm Admission SpecificationEntry ProofDeclaration)
open Mettapedia.Languages.MM0.Presentation.Calculus (family derivesJ kernelCalculus)
open Mettapedia.Languages.MM0.Presentation.ComputationalCalculus
  (calculusProgram request certificate_computes derives_of_returned returned_of_derives
    settledEvaluate)
open Mettapedia.Languages.MM0.Presentation.ComputationalAdmission
  (admissionProgram encodeAdmissions encodeTheoryResult encodeTheoryResult_injective
    start_computes)
open Mettapedia.Languages.MM0.Presentation.ComputationalSpecification
  (specificationProgram encodeEntries encodeProofDeclarations verify_computes)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Logic.HostingStyles.AtomsReduce (ruleSpace closedAtom)
open Mettapedia.Logic.HostingStyles.AmbientRegions
open Mettapedia.Logic.HostingStyles.StoredPrograms

variable {admits : Pattern → Bool}

/-! ## The check of a certificate -/

/-- **The candidate checks MM0 proofs, by the plain atom of the check.**  At
the ambient space of the table of the check: for some certificate, the atom
of its check for the judgment reaches the atom of `True`, exactly when MM0's
kernel derives the judgment. -/
theorem check_atom_iff_derives (admitsAtoms : AdmitsAtoms admits)
    (T : Mettapedia.Languages.MM0.Kernel.Theory) (context : Context) (hypotheses : List Preterm)
    (expression : Preterm) :
    (∃ proof : CompactProof (family T).Leaf,
        (spacesAndRegionsTheory admits (ruleSpace checkTable)).Reaches
          (callAtom letterSpelling "mm0:certificate"
            (request T (derivesJ context hypotheses expression) proof))
          (valueAtom letterSpelling (boolean true))) ↔
      Mettapedia.Languages.MM0.Kernel.Derives T.termSignature T.definitionSignature
        T.theoremSignature context hypotheses expression := by
  have total : ∀ proof, ∃ value, Applies (partAt calculusProgram certificateHeads)
      dataEqualityHost "mm0:certificate"
      (request T (derivesJ context hypotheses expression) proof) value :=
    fun proof => ⟨_, (checkPart_applies_iff T _ proof _).mpr (certificate_computes T _ proof)⟩
  constructor
  · rintro ⟨proof, reaches⟩
    exact derives_of_returned T ((checkPart_applies_iff T _ proof _).mp
      ((callAtom_reaches_iff admitsAtoms check_stores check_stored.orthogonal
        letterSpelling_injective (checkPart_defined T _ proof) (total proof) (boolean true)).mp
        reaches))
  · intro derived
    obtain ⟨proof, returned⟩ := returned_of_derives T derived
    exact ⟨proof, callAtom_reaches admitsAtoms check_stores (checkPart_defined T _ proof)
      ((checkPart_applies_iff T _ proof _).mpr returned)⟩

/-- **Every atom without transition that the atom of a check reaches is the
atom of the verdict of the checker.** -/
theorem check_atom_unique (admitsAtoms : AdmitsAtoms admits)
    (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) {target : Contexts.Term spacesAndRegions closedAtom}
    (reaches : (spacesAndRegionsTheory admits (ruleSpace checkTable)).Reaches
      (callAtom letterSpelling "mm0:certificate" (request T goal proof)) target)
    (normal : ∀ next,
      ¬ (spacesAndRegionsTheory admits (ruleSpace checkTable)).rewrites target next) :
    target = valueAtom letterSpelling
      (boolean (check kernelCalculus (settledEvaluate T) goal proof)) :=
  callAtom_unique admitsAtoms check_stores check_stored.orthogonal (checkPart_defined T goal proof)
    ((checkPart_applies_iff T goal proof _).mpr (certificate_computes T goal proof)) reaches normal

/-- **The candidate checks MM0 proofs inside a contained run**, at every
ambient space: for some certificate, the run of its check in the space of the
table of the check reaches the run of `True`, exactly when MM0's kernel
derives the judgment. -/
theorem check_region_iff_derives (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    (T : Mettapedia.Languages.MM0.Kernel.Theory) (context : Context) (hypotheses : List Preterm)
    (expression : Preterm) :
    (∃ proof : CompactProof (family T).Leaf,
        (spacesAndRegionsTheory admits ambientSpace).Reaches
          (callRegion letterSpelling checkTable "mm0:certificate"
            (request T (derivesJ context hypotheses expression) proof))
          (valueRegion letterSpelling checkTable (boolean true))) ↔
      Mettapedia.Languages.MM0.Kernel.Derives T.termSignature T.definitionSignature
        T.theoremSignature context hypotheses expression := by
  have total : ∀ proof, ∃ value, Applies (partAt calculusProgram certificateHeads)
      dataEqualityHost "mm0:certificate"
      (request T (derivesJ context hypotheses expression) proof) value :=
    fun proof => ⟨_, (checkPart_applies_iff T _ proof _).mpr (certificate_computes T _ proof)⟩
  constructor
  · rintro ⟨proof, reaches⟩
    exact derives_of_returned T ((checkPart_applies_iff T _ proof _).mp
      ((callRegion_reaches_iff admitsAtoms ambientSpace check_stores check_stored.orthogonal
        letterSpelling_injective (checkPart_defined T _ proof) (total proof) (boolean true)).mp
        reaches))
  · intro derived
    obtain ⟨proof, returned⟩ := returned_of_derives T derived
    exact ⟨proof, callRegion_reaches admitsAtoms ambientSpace check_stores
      (checkPart_defined T _ proof) ((checkPart_applies_iff T _ proof _).mpr returned)⟩

/-- **Every term without transition that the run of a check reaches is the
run of the verdict of the checker**, at every ambient space. -/
theorem check_region_unique (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    (T : Mettapedia.Languages.MM0.Kernel.Theory) (goal : Pattern)
    (proof : CompactProof (family T).Leaf) {target : Contexts.Term spacesAndRegions closedAtom}
    (reaches : (spacesAndRegionsTheory admits ambientSpace).Reaches
      (callRegion letterSpelling checkTable "mm0:certificate" (request T goal proof)) target)
    (normal : ∀ next, ¬ (spacesAndRegionsTheory admits ambientSpace).rewrites target next) :
    target = valueRegion letterSpelling checkTable
      (boolean (check kernelCalculus (settledEvaluate T) goal proof)) :=
  callRegion_unique admitsAtoms ambientSpace check_stores check_stored.orthogonal
    (checkPart_defined T goal proof)
    ((checkPart_applies_iff T goal proof _).mpr (certificate_computes T goal proof)) reaches normal

/-! ## The admission of a development -/

/-- **The candidate runs the kernel on a whole development, by the plain atom
of the call.**  At the ambient space of the admission table, the atom of the
admission of a list of declarations reaches the atom of an encoded result
exactly when the kernel's function returns that result. -/
theorem admission_atom_iff (admitsAtoms : AdmitsAtoms admits) (admissions : List Admission)
    (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    (spacesAndRegionsTheory admits (ruleSpace admissionTable)).Reaches
        (callAtom letterSpelling "mm0:admission-start" [encodeAdmissions admissions])
        (valueAtom letterSpelling (encodeTheoryResult result)) ↔
      Mettapedia.Languages.MM0.Kernel.Theory.run? {} admissions = result :=
  callAtom_result_iff admitsAtoms admission_stores admission_stored.orthogonal
    letterSpelling_injective encodeTheoryResult_injective (admissionPart_defined admissions)
    ((admissionPart_applies_iff admissions _).mpr (start_computes admissions)) result

/-- **Every atom without transition that the atom of an admission reaches is
the atom of what the kernel's function returns.** -/
theorem admission_atom_unique (admitsAtoms : AdmitsAtoms admits) (admissions : List Admission)
    {target : Contexts.Term spacesAndRegions closedAtom}
    (reaches : (spacesAndRegionsTheory admits (ruleSpace admissionTable)).Reaches
      (callAtom letterSpelling "mm0:admission-start" [encodeAdmissions admissions]) target)
    (normal : ∀ next,
      ¬ (spacesAndRegionsTheory admits (ruleSpace admissionTable)).rewrites target next) :
    target = valueAtom letterSpelling
      (encodeTheoryResult (Mettapedia.Languages.MM0.Kernel.Theory.run? {} admissions)) :=
  callAtom_unique admitsAtoms admission_stores admission_stored.orthogonal
    (admissionPart_defined admissions)
    ((admissionPart_applies_iff admissions _).mpr (start_computes admissions)) reaches normal

/-- **The candidate runs the kernel on a whole development inside a contained
run**, at every ambient space. -/
theorem admission_region_iff (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    (admissions : List Admission) (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    (spacesAndRegionsTheory admits ambientSpace).Reaches
        (callRegion letterSpelling admissionTable "mm0:admission-start"
          [encodeAdmissions admissions])
        (valueRegion letterSpelling admissionTable (encodeTheoryResult result)) ↔
      Mettapedia.Languages.MM0.Kernel.Theory.run? {} admissions = result :=
  callRegion_result_iff admitsAtoms ambientSpace admission_stores admission_stored.orthogonal
    letterSpelling_injective encodeTheoryResult_injective (admissionPart_defined admissions)
    ((admissionPart_applies_iff admissions _).mpr (start_computes admissions)) result

/-- **Every term without transition that the run of an admission reaches is
the run of what the kernel's function returns**, at every ambient space. -/
theorem admission_region_unique (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    (admissions : List Admission) {target : Contexts.Term spacesAndRegions closedAtom}
    (reaches : (spacesAndRegionsTheory admits ambientSpace).Reaches
      (callRegion letterSpelling admissionTable "mm0:admission-start"
        [encodeAdmissions admissions]) target)
    (normal : ∀ next, ¬ (spacesAndRegionsTheory admits ambientSpace).rewrites target next) :
    target = valueRegion letterSpelling admissionTable
      (encodeTheoryResult (Mettapedia.Languages.MM0.Kernel.Theory.run? {} admissions)) :=
  callRegion_unique admitsAtoms ambientSpace admission_stores admission_stored.orthogonal
    (admissionPart_defined admissions)
    ((admissionPart_applies_iff admissions _).mpr (start_computes admissions)) reaches normal

/-! ## The verification against a specification -/

/-- **The candidate verifies a development against a specification, by the
plain atom of the call.**  At the ambient space of the verification table,
the atom of the verification reaches the atom of an encoded result exactly
when the kernel's function returns that result. -/
theorem verification_atom_iff (admitsAtoms : AdmitsAtoms admits)
    (specification : List SpecificationEntry) (declarations : List ProofDeclaration)
    (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    (spacesAndRegionsTheory admits (ruleSpace verificationTable)).Reaches
        (callAtom letterSpelling "mm0:spec-verify"
          [encodeEntries specification, encodeProofDeclarations declarations])
        (valueAtom letterSpelling (encodeTheoryResult result)) ↔
      Mettapedia.Languages.MM0.Kernel.SpecificationAdmission.verify? specification declarations =
        result :=
  callAtom_result_iff admitsAtoms verification_stores verification_stored.orthogonal
    letterSpelling_injective encodeTheoryResult_injective
    (verificationPart_defined specification declarations)
    ((verificationPart_applies_iff specification declarations _).mpr
      (verify_computes specification declarations)) result

/-- **Every atom without transition that the atom of a verification reaches is
the atom of what the kernel's function returns.** -/
theorem verification_atom_unique (admitsAtoms : AdmitsAtoms admits)
    (specification : List SpecificationEntry) (declarations : List ProofDeclaration)
    {target : Contexts.Term spacesAndRegions closedAtom}
    (reaches : (spacesAndRegionsTheory admits (ruleSpace verificationTable)).Reaches
      (callAtom letterSpelling "mm0:spec-verify"
        [encodeEntries specification, encodeProofDeclarations declarations]) target)
    (normal : ∀ next,
      ¬ (spacesAndRegionsTheory admits (ruleSpace verificationTable)).rewrites target next) :
    target = valueAtom letterSpelling (encodeTheoryResult
      (Mettapedia.Languages.MM0.Kernel.SpecificationAdmission.verify? specification
        declarations)) :=
  callAtom_unique admitsAtoms verification_stores verification_stored.orthogonal
    (verificationPart_defined specification declarations)
    ((verificationPart_applies_iff specification declarations _).mpr
      (verify_computes specification declarations)) reaches normal

/-- **The candidate verifies a development against a specification inside a
contained run**, at every ambient space. -/
theorem verification_region_iff (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    (specification : List SpecificationEntry) (declarations : List ProofDeclaration)
    (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    (spacesAndRegionsTheory admits ambientSpace).Reaches
        (callRegion letterSpelling verificationTable "mm0:spec-verify"
          [encodeEntries specification, encodeProofDeclarations declarations])
        (valueRegion letterSpelling verificationTable (encodeTheoryResult result)) ↔
      Mettapedia.Languages.MM0.Kernel.SpecificationAdmission.verify? specification declarations =
        result :=
  callRegion_result_iff admitsAtoms ambientSpace verification_stores
    verification_stored.orthogonal letterSpelling_injective encodeTheoryResult_injective
    (verificationPart_defined specification declarations)
    ((verificationPart_applies_iff specification declarations _).mpr
      (verify_computes specification declarations)) result

/-- **Every term without transition that the run of a verification reaches is
the run of what the kernel's function returns**, at every ambient space. -/
theorem verification_region_unique (admitsAtoms : AdmitsAtoms admits) (ambientSpace : Pattern)
    (specification : List SpecificationEntry) (declarations : List ProofDeclaration)
    {target : Contexts.Term spacesAndRegions closedAtom}
    (reaches : (spacesAndRegionsTheory admits ambientSpace).Reaches
      (callRegion letterSpelling verificationTable "mm0:spec-verify"
        [encodeEntries specification, encodeProofDeclarations declarations]) target)
    (normal : ∀ next, ¬ (spacesAndRegionsTheory admits ambientSpace).rewrites target next) :
    target = valueRegion letterSpelling verificationTable (encodeTheoryResult
      (Mettapedia.Languages.MM0.Kernel.SpecificationAdmission.verify? specification
        declarations)) :=
  callRegion_unique admitsAtoms ambientSpace verification_stores verification_stored.orthogonal
    (verificationPart_defined specification declarations)
    ((verificationPart_applies_iff specification declarations _).mpr
      (verify_computes specification declarations)) reaches normal

/-! ## One development, by its replayed reduction -/

/-- **Positive**: the admission of a sort, a constant, an axiom and a theorem
with its proof.  The 343 steps of its trace, replayed in Lean's kernel, are a
reduction of the candidate from the plain atom of the call to the atom of the
encoded theory, at the ambient space of the admission table and without a
guard.  The general theorem is not used. -/
theorem admission_instance_atom :
    (spacesAndRegionsTheory anySubject (ruleSpace admissionTable)).Reaches
      (callAtom letterSpelling "mm0:admission-start" [encodeAdmissions restatedDevelopment])
      (valueAtom letterSpelling (encodeTheoryResult (some restatedTheory))) :=
  termAtom_reaches anySubject_admitsAtoms admission_stores.runnable
    (stores_headed admission_stores)
    (admission_stored.replayCoded_reduces admission_instance_replays)

/-- **Positive**: the same reduction inside a contained run, at every ambient
space. -/
theorem admission_instance_region (ambientSpace : Pattern) :
    (spacesAndRegionsTheory anySubject ambientSpace).Reaches
      (callRegion letterSpelling admissionTable "mm0:admission-start"
        [encodeAdmissions restatedDevelopment])
      (valueRegion letterSpelling admissionTable (encodeTheoryResult (some restatedTheory))) :=
  termRegion_reaches anySubject_admitsAtoms ambientSpace admission_stores.runnable
    (stores_headed admission_stores)
    (admission_stored.replayCoded_reduces admission_instance_replays)

/-- **Negative**: a term whose sort is not declared is refused: the atom of
its admission reaches the atom of the refusal, by the replayed reduction of
twenty-six steps. -/
theorem admission_refusal_atom :
    (spacesAndRegionsTheory anySubject (ruleSpace admissionTable)).Reaches
      (callAtom letterSpelling "mm0:admission-start" [encodeAdmissions [.term 0 ⟨[], 0, ∅⟩]])
      (valueAtom letterSpelling (encodeTheoryResult none)) :=
  termAtom_reaches anySubject_admitsAtoms admission_stores.runnable
    (stores_headed admission_stores)
    (admission_stored.replayCoded_reduces admission_refusal_replays)

/-- **Negative**: and it reaches the atom of no theory. -/
theorem admission_refusal_atom_no_theory (after : Mettapedia.Languages.MM0.Kernel.Theory) :
    ¬ (spacesAndRegionsTheory anySubject (ruleSpace admissionTable)).Reaches
      (callAtom letterSpelling "mm0:admission-start" [encodeAdmissions [.term 0 ⟨[], 0, ∅⟩]])
      (valueAtom letterSpelling (encodeTheoryResult (some after))) := by
  intro reaches
  have refused := (admission_atom_iff anySubject_admitsAtoms [.term 0 ⟨[], 0, ∅⟩] none).mp
    admission_refusal_atom
  have admitted := (admission_atom_iff anySubject_admitsAtoms [.term 0 ⟨[], 0, ∅⟩]
    (some after)).mp reaches
  rw [refused] at admitted
  cases admitted

#print axioms check_atom_iff_derives
#print axioms check_atom_unique
#print axioms check_region_iff_derives
#print axioms check_region_unique
#print axioms admission_atom_iff
#print axioms admission_atom_unique
#print axioms admission_region_iff
#print axioms admission_region_unique
#print axioms verification_atom_iff
#print axioms verification_atom_unique
#print axioms verification_region_iff
#print axioms verification_region_unique
#print axioms admission_instance_atom
#print axioms admission_instance_region
#print axioms admission_refusal_atom
#print axioms admission_refusal_atom_no_theory

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
