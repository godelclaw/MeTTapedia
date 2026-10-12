import Mettapedia.Logic.HostingStyles.SpacesAndRegions.Kernel
import Mettapedia.Logic.HostingStyles.SpacesAndRegions.SealedPart

/-!
# Stored programs and MM0's kernel inside the sealed part

The atom of a λΠ term has no quotation and no run, and the space of a list
of rules is plain.  So the atom of a call, the atom of a value, and their
runs in the space of a table are sealed terms (`sealedTerm_termAtom`,
`sealedTerm_termRegion`), and a stored program runs inside the sealed part:
what the candidate reaches from them, the sealed part reaches
(`sealedPart_reaches_iff`).

* **A stored program** (`sealedPart_callAtom_reaches_iff`,
  `sealedPart_callRegion_reaches_iff`): in the sealed part, the atom of a
  call at the ambient space of the table, and its run in the space of the
  table at every ambient space whose contraction quotes only what was quoted,
  reach the value exactly when the engine returns it.
* **MM0**, by the plain atom at the space of each table: the check of a
  certificate (`sealedPart_check_iff_derives`), the admission of a
  development (`sealedPart_admission_iff`) and the verification against a
  specification (`sealedPart_verification_iff`).
* **Negative**: at the space of the rule `$0 ⟶ *@$0` there is no sealed part
  in this sense: its sealed terms are not closed under transitions
  (`sealedTerm_not_kept_at_quotingSpace`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves (CompactProof)
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (Program Host Applies boolean)
open Mettapedia.Languages.MM0.Kernel (Context Preterm Admission SpecificationEntry ProofDeclaration)
open Mettapedia.Languages.MM0.Presentation.Calculus (family derivesJ)
open Mettapedia.Languages.MM0.Presentation.ComputationalCalculus (request)
open Mettapedia.Languages.MM0.Presentation.ComputationalAdmission
  (encodeAdmissions encodeTheoryResult)
open Mettapedia.Languages.MM0.Presentation.ComputationalSpecification
  (encodeEntries encodeProofDeclarations)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Logic.HostingStyles.PrimeCandidate (contract runPattern)
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (ruleSpace closedAtom atomAt contract_ruleSpace contract_atomAt programTheory)
open Mettapedia.Logic.HostingStyles.AmbientRegions
open Mettapedia.Logic.HostingStyles.StoredPrograms

variable {admits : Pattern → Bool}

/-! ## The atoms of calls and of values are sealed -/

/-- The contraction of the space of a list of rules is plain, so it quotes
only what was quoted. -/
theorem quotesOnlyQuoted_contract_ruleSpace (rules : List Dedukti.RewriteRule) :
    QuotesOnlyQuoted (contract (ruleSpace rules)) := by
  rw [contract_ruleSpace]
  exact quotesOnlyQuoted_of_plainSpace (plainSpace_ruleSpace rules)

/-- **The atom of a λΠ term is a sealed term.** -/
theorem sealedTerm_termAtom (term : LF.Term) : SealedTerm (termAtom term) :=
  sealedTerm_atom 0 term

/-- **The run of the atom of a λΠ term in the space of a list of rules is a
sealed term.** -/
theorem sealedTerm_termRegion (rules : List Dedukti.RewriteRule) (term : LF.Term) :
    SealedTerm (termRegion rules term) :=
  sealedTerm_runAtom rules 0 term

/-! ## A stored program runs inside the sealed part -/

variable {N : Spelling} {rules : List Dedukti.RewriteRule} {program : Program} {host : Host}
  {primitives : List String}

/-- **In the sealed part, at the ambient space of the table, the atom of a
call reaches the atom of a value exactly when the engine returns the
value.** -/
theorem sealedPart_callAtom_reaches_iff (admitsAtoms : AdmitsAtoms admits)
    (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    {head : String} {arguments : List EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (total : ∃ value, Applies program host head arguments value) (result : EngineTerm) :
    (sealedPart admits (ruleSpace rules) (quotesOnlyQuoted_contract_ruleSpace rules)).Reaches
        (interface := closedAtom) ⟨callAtom N head arguments, sealedTerm_termAtom _⟩
        ⟨valueAtom N result, sealedTerm_termAtom _⟩ ↔
      Applies program host head arguments result := by
  rw [← callAtom_reaches_iff admitsAtoms stores orthogonal injective defined total result]
  constructor
  · intro reaches
    exact (sealedPart_reaches_iff admits (ruleSpace rules)
      (quotesOnlyQuoted_contract_ruleSpace rules)
      ⟨callAtom N head arguments, sealedTerm_termAtom _⟩ (valueAtom N result)).mpr
      ⟨sealedTerm_termAtom _, reaches⟩
  · intro reaches
    obtain ⟨kept, reached⟩ := (sealedPart_reaches_iff admits (ruleSpace rules)
      (quotesOnlyQuoted_contract_ruleSpace rules) ⟨callAtom N head arguments, sealedTerm_termAtom _⟩
      (valueAtom N result)).mp reaches
    exact reached

/-- **In the sealed part, at every ambient space whose contraction quotes
only what was quoted, the run of a call in the space of the table reaches the
run of a value exactly when the engine returns the value.** -/
theorem sealedPart_callRegion_reaches_iff (admitsAtoms : AdmitsAtoms admits)
    (ambientSpace : Pattern) (safe : QuotesOnlyQuoted (contract ambientSpace))
    (stores : Stores N rules program host primitives)
    (orthogonal : (programTheory rules).Orthogonal) (injective : Function.Injective N.write)
    {head : String} {arguments : List EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (total : ∃ value, Applies program host head arguments value) (result : EngineTerm) :
    (sealedPart admits ambientSpace safe).Reaches (interface := closedAtom)
        ⟨callRegion N rules head arguments, sealedTerm_termRegion rules _⟩
        ⟨valueRegion N rules result, sealedTerm_termRegion rules _⟩ ↔
      Applies program host head arguments result := by
  rw [← callRegion_reaches_iff admitsAtoms ambientSpace stores orthogonal injective defined total
    result]
  constructor
  · intro reaches
    exact (sealedPart_reaches_iff admits ambientSpace safe
      ⟨callRegion N rules head arguments, sealedTerm_termRegion rules _⟩
      (valueRegion N rules result)).mpr ⟨sealedTerm_termRegion rules _, reaches⟩
  · intro reaches
    obtain ⟨kept, reached⟩ := (sealedPart_reaches_iff admits ambientSpace safe
      ⟨callRegion N rules head arguments, sealedTerm_termRegion rules _⟩
      (valueRegion N rules result)).mp reaches
    exact reached

/-! ## MM0's kernel inside the sealed part -/

/-- **The sealed part checks MM0 proofs.**  At the ambient space of the table
of the check: for some certificate, the atom of its check for the judgment
reaches the atom of `True` in the sealed part, exactly when MM0's kernel
derives the judgment. -/
theorem sealedPart_check_iff_derives (admitsAtoms : AdmitsAtoms admits)
    (T : Mettapedia.Languages.MM0.Kernel.Theory) (context : Context) (hypotheses : List Preterm)
    (expression : Preterm) :
    (∃ proof : CompactProof (family T).Leaf,
        (sealedPart admits (ruleSpace checkTable) (quotesOnlyQuoted_contract_ruleSpace _)).Reaches
          (interface := closedAtom)
          ⟨callAtom letterSpelling "mm0:certificate"
            (request T (derivesJ context hypotheses expression) proof), sealedTerm_termAtom _⟩
          ⟨valueAtom letterSpelling (boolean true), sealedTerm_termAtom _⟩) ↔
      Mettapedia.Languages.MM0.Kernel.Derives T.termSignature T.definitionSignature
        T.theoremSignature context hypotheses expression := by
  rw [← check_atom_iff_derives admitsAtoms T context hypotheses expression]
  constructor
  · rintro ⟨proof, reaches⟩
    exact ⟨proof, (sealedPart_reaches_iff admits (ruleSpace checkTable)
      (quotesOnlyQuoted_contract_ruleSpace _) ⟨_, sealedTerm_termAtom _⟩ _).mpr
      ⟨sealedTerm_termAtom _, reaches⟩⟩
  · rintro ⟨proof, reaches⟩
    obtain ⟨kept, reached⟩ := (sealedPart_reaches_iff admits (ruleSpace checkTable)
      (quotesOnlyQuoted_contract_ruleSpace _) ⟨callAtom letterSpelling "mm0:certificate"
        (request T (derivesJ context hypotheses expression) proof), sealedTerm_termAtom _⟩
      (valueAtom letterSpelling (boolean true))).mp reaches
    exact ⟨proof, reached⟩

/-- **The sealed part admits a development.**  At the ambient space of the
table of the admission the atom of the admission reaches the atom of a result
in the sealed part exactly when the result is what MM0's kernel returns for
the development. -/
theorem sealedPart_admission_iff (admitsAtoms : AdmitsAtoms admits) (admissions : List Admission)
    (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    (sealedPart admits (ruleSpace admissionTable) (quotesOnlyQuoted_contract_ruleSpace _)).Reaches
        (interface := closedAtom)
        ⟨callAtom letterSpelling "mm0:admission-start" [encodeAdmissions admissions],
          sealedTerm_termAtom _⟩
        ⟨valueAtom letterSpelling (encodeTheoryResult result), sealedTerm_termAtom _⟩ ↔
      Mettapedia.Languages.MM0.Kernel.Theory.run? {} admissions = result := by
  rw [← admission_atom_iff admitsAtoms admissions result]
  constructor
  · intro reaches
    exact (sealedPart_reaches_iff admits (ruleSpace admissionTable)
      (quotesOnlyQuoted_contract_ruleSpace _) ⟨_, sealedTerm_termAtom _⟩ _).mpr
      ⟨sealedTerm_termAtom _, reaches⟩
  · intro reaches
    obtain ⟨kept, reached⟩ := (sealedPart_reaches_iff admits (ruleSpace admissionTable)
      (quotesOnlyQuoted_contract_ruleSpace _)
      ⟨callAtom letterSpelling "mm0:admission-start" [encodeAdmissions admissions],
        sealedTerm_termAtom _⟩
      (valueAtom letterSpelling (encodeTheoryResult result))).mp reaches
    exact reached

/-- **The sealed part verifies a development against a specification.**  At
the ambient space of the table of the verification the atom of the
verification reaches the atom of a result in the sealed part exactly when the
result is what MM0's kernel returns. -/
theorem sealedPart_verification_iff (admitsAtoms : AdmitsAtoms admits)
    (specification : List SpecificationEntry) (declarations : List ProofDeclaration)
    (result : Option Mettapedia.Languages.MM0.Kernel.Theory) :
    (sealedPart admits (ruleSpace verificationTable)
        (quotesOnlyQuoted_contract_ruleSpace _)).Reaches (interface := closedAtom)
        ⟨callAtom letterSpelling "mm0:spec-verify"
          [encodeEntries specification, encodeProofDeclarations declarations],
          sealedTerm_termAtom _⟩
        ⟨valueAtom letterSpelling (encodeTheoryResult result), sealedTerm_termAtom _⟩ ↔
      Mettapedia.Languages.MM0.Kernel.SpecificationAdmission.verify? specification declarations =
        result := by
  rw [← verification_atom_iff admitsAtoms specification declarations result]
  constructor
  · intro reaches
    exact (sealedPart_reaches_iff admits (ruleSpace verificationTable)
      (quotesOnlyQuoted_contract_ruleSpace _) ⟨_, sealedTerm_termAtom _⟩ _).mpr
      ⟨sealedTerm_termAtom _, reaches⟩
  · intro reaches
    obtain ⟨kept, reached⟩ := (sealedPart_reaches_iff admits (ruleSpace verificationTable)
      (quotesOnlyQuoted_contract_ruleSpace _)
      ⟨callAtom letterSpelling "mm0:spec-verify"
        [encodeEntries specification, encodeProofDeclarations declarations],
        sealedTerm_termAtom _⟩
      (valueAtom letterSpelling (encodeTheoryResult result))).mp reaches
    exact reached

#print axioms sealedTerm_termAtom
#print axioms sealedTerm_termRegion
#print axioms sealedPart_callAtom_reaches_iff
#print axioms sealedPart_callRegion_reaches_iff
#print axioms sealedPart_check_iff_derives
#print axioms sealedPart_admission_iff
#print axioms sealedPart_verification_iff

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
