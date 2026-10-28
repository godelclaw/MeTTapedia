import Mettapedia.GSLT.LanguageDef.CertificateGSLTRawSubstitution
import Mettapedia.GSLT.LanguageDef.CertificateGSLTSemantics

/-!
# Checked application of open rule programs

A submitted rule program is the existing raw open proof, with its ordered
premise context and conclusion. Application checks that program and every
supplied premise, then uses the existing raw substitution. The result is
accepted without a second proof search. Exact reconstruction ties the output
to open-derivation plugging; the model law retains the actual supplied values.

This is the generic proof-calculus judgment. A source language's additional
context and term-formation obligations remain with its source interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

variable {definition : ValidatedCalculusLanguageDef}
  {premises ambient finalContext : List Pattern} {goal : Pattern}
  {program result : RawOpenProof} {arguments : List RawOpenProof}

/-- Apply an open rule only after its exact premise vector has been checked.
Unused premise positions are checked too; missing and extra arguments fail. -/
def applyOpen? (definition : ValidatedCalculusLanguageDef)
    (premises ambient : List Pattern) (goal : Pattern)
    (program : RawOpenProof) (arguments : List RawOpenProof) : Option RawOpenProof :=
  if checkOpenRaw definition premises goal program &&
      checkOpenRawChildren definition ambient premises arguments then
    some (program.substitute arguments)
  else none

theorem applyOpen?_eq_some_iff :
    applyOpen? definition premises ambient goal program arguments = some result ↔
      checkOpenRaw definition premises goal program = true ∧
      checkOpenRawChildren definition ambient premises arguments = true ∧
      program.substitute arguments = result := by
  simp only [applyOpen?]
  split
  · rename_i accepted
    simp only [Bool.and_eq_true] at accepted
    simp [accepted.1, accepted.2]
  · rename_i refused
    simp only [Bool.and_eq_true] at refused
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨first, second, _⟩
      exact False.elim (refused ⟨first, second⟩)

/-- Success reconstructs the original rule and arguments with their exact
erasures, and the output is the erasure of their genuine composition. -/
theorem applyOpen?_exact
    (accepted : applyOpen? definition premises ambient goal program arguments = some result) :
    ∃ rule : OpenDerivation definition premises goal,
      ∃ supplied : OpenDerivationList definition ambient premises,
        rule.eraseOpen = program ∧ supplied.eraseOpen = arguments ∧
          (rule.bind supplied).eraseOpen = result := by
  obtain ⟨ruleChecked, argumentsChecked, output⟩ := applyOpen?_eq_some_iff.mp accepted
  obtain ⟨rule, ruleErases⟩ := checkOpenRaw_exact_derivation ruleChecked
  obtain ⟨supplied, suppliedErases⟩ := checkOpenRawChildren_exact_derivations argumentsChecked
  refine ⟨rule, supplied, ruleErases, suppliedErases, ?_⟩
  rw [OpenDerivation.eraseOpen_bind, ruleErases, suppliedErases, output]

theorem applyOpen?_checked
    (accepted : applyOpen? definition premises ambient goal program arguments = some result) :
    checkOpenRaw definition ambient goal result = true := by
  obtain ⟨rule, supplied, _, _, output⟩ := applyOpen?_exact accepted
  rw [← output]
  exact checkOpenRaw_erase (rule.bind supplied)

/-- Checking the arguments once suffices for raw proof substitution. -/
theorem checkOpenRaw_substitute
    (ruleChecked : checkOpenRaw definition premises goal program = true)
    (argumentsChecked : checkOpenRawChildren definition ambient premises arguments = true) :
    checkOpenRaw definition ambient goal (program.substitute arguments) = true :=
  applyOpen?_checked (applyOpen?_eq_some_iff.mpr ⟨ruleChecked, argumentsChecked, rfl⟩)

theorem checkOpenRawChildren_length {goals : List Pattern} {proofs : List RawOpenProof}
    (checked : checkOpenRawChildren definition ambient goals proofs = true) :
    proofs.length = goals.length := by
  induction goals generalizing proofs with
  | nil => cases proofs <;> simp_all [checkOpenRawChildren]
  | cons first rest ih =>
      cases proofs with
      | nil => simp [checkOpenRawChildren] at checked
      | cons proof proofs =>
          simp only [checkOpenRawChildren, Bool.and_eq_true] at checked
          simpa only [List.length_cons] using congrArg Nat.succ (ih checked.2)

theorem applyOpen?_argument_count
    (accepted : applyOpen? definition premises ambient goal program arguments = some result) :
    arguments.length = premises.length :=
  checkOpenRawChildren_length (applyOpen?_eq_some_iff.mp accepted).2.1

/-- Associativity concerns the actual emitted trees. The premises exclude
the out-of-range citations that the total raw substitution leaves intact. -/
theorem checked_substitute_assoc {second : List RawOpenProof}
    (ruleChecked : checkOpenRaw definition premises goal program = true)
    (firstChecked : checkOpenRawChildren definition ambient premises arguments = true)
    (secondChecked : checkOpenRawChildren definition finalContext ambient second = true) :
    (program.substitute arguments).substitute second =
      program.substitute (RawOpenProof.substituteList second arguments) := by
  obtain ⟨rule, ruleErases⟩ := checkOpenRaw_exact_derivation ruleChecked
  obtain ⟨first, firstErases⟩ := checkOpenRawChildren_exact_derivations firstChecked
  obtain ⟨last, lastErases⟩ := checkOpenRawChildren_exact_derivations secondChecked
  rw [← ruleErases, ← firstErases, ← lastErases,
    ← OpenDerivation.eraseOpen_bind, ← OpenDerivation.eraseOpen_bind,
    ← OpenDerivationList.eraseOpen_bind, ← OpenDerivation.eraseOpen_bind]
  exact congrArg OpenDerivation.eraseOpen (OpenDerivation.bind_assoc rule first last)

/-- Semantic application follows from the model's individual rule operations
and the checked reconstruction, without an assumed whole-program meaning. -/
theorem applyOpen?_interprets {object : Object} (model : Model object)
    (accepted : applyOpen? object.definition premises ambient goal program arguments = some result)
    (values : RealizationList model.carrier ambient) :
    ∃ rule : OpenDerivation object.definition premises goal,
      ∃ supplied : OpenDerivationList object.definition ambient premises,
        rule.eraseOpen = program ∧ supplied.eraseOpen = arguments ∧
          (rule.bind supplied).eraseOpen = result ∧
          model.denoteOpen (rule.bind supplied) values =
            model.denoteOpen rule (model.denoteOpenList supplied values) := by
  obtain ⟨rule, supplied, ruleErases, suppliedErases, output⟩ := applyOpen?_exact accepted
  exact ⟨rule, supplied, ruleErases, suppliedErases, output,
    model.denoteOpen_bind rule supplied values⟩

#print axioms applyOpen?_exact
#print axioms applyOpen?_checked
#print axioms checked_substitute_assoc
#print axioms applyOpen?_interprets

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
