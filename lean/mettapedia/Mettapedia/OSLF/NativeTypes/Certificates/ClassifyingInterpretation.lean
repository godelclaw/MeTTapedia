import Mettapedia.OSLF.NativeTypes.Certificates.Interpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementClassifyingEvidence

/-!
# Computational native certificates and actual classifying sections

A raw accepted certificate reconstructs its exact independent derivation.
The existing classifying model maps that derivation's complete term class to
its native section. The independent native evaluator fixes the same section,
and program-interface substitution preserves the value-section readout.
Distinct certificate origins remain distinct even when sections coincide.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.Refinement

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi
open Mettapedia.TypeTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension

universe u

variable {C : Type u} [Category.{u} C]
variable {S : NativeDependent.Refinement.Symbols.{u}}
variable {D : NativeDependent.Refinement.Signature S}
variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]
variable {n : Nat} {context : NativeDependent.Refinement.ContextExpr S n}
variable {term : NativeDependent.Refinement.TermExpr S n}
variable {type : NativeDependent.Refinement.TypeExpr S n}
variable {P Q : Face.{u,u,u} C}
variable (interpretation : NativeDependent.RefinementPresheafCertificates.Interpretation D context term type P)
variable (headers : NativeDependent.Refinement.HeaderFormation D)
variable (certificate : Certificate D)
variable (accepted : check certificate (.term context term type) = true)

noncomputable def checkedClassifyingSection : interpretation.decodedFamily.sections :=
  interpretation.classifyingSection headers (reconstruct certificate (.term context term type) accepted)

theorem checkedClassifyingSection_eq_checkedSection :
    checkedClassifyingSection interpretation headers certificate accepted =
      checkedSection interpretation certificate accepted :=
  interpretation.classifyingSection_eq_nativeSection headers
    (reconstruct certificate (.term context term type) accepted)

theorem checkedClassifyingSection_readout :
    interpretation.model.evaluateTerm interpretation.semanticContext term =
      some ⟨interpretation.semanticType,
        checkedClassifyingSection interpretation headers certificate accepted⟩ := by
  rw [checkedClassifyingSection_eq_checkedSection]
  exact checkedSection_readout interpretation certificate accepted

noncomputable def checkedClassifyingValueSection : interpretation.valueFamily.sections :=
  interpretation.classifyingValueSection headers (reconstruct certificate (.term context term type) accepted)

theorem checkedClassifyingValueSection_readout (point : P.Elements) :
    (checkedClassifyingValueSection interpretation headers certificate accepted).val point =
      (checkedClassifyingSection interpretation headers certificate accepted).val
        (interpretation.interface.mapElements.obj point) := by
  rw [checkedClassifyingValueSection,
    interpretation.classifyingValueSection_eq_valueSection headers
      (reconstruct certificate (.term context term type) accepted)]
  exact interpretation.classifying_value_readout headers
    (reconstruct certificate (.term context term type) accepted) point

theorem checkedClassifyingValueSection_substitution (substitution : Q ⟶ P) :
    checkedClassifyingValueSection
      (NativeDependent.RefinementPresheafCertificateSubstitution.reindex interpretation substitution)
      headers certificate accepted =
      reindexDisplayedSection substitution interpretation.valueFamily
        (checkedClassifyingValueSection interpretation headers certificate accepted) :=
  interpretation.classifyingValueSection_substitution headers
    (reconstruct certificate (.term context term type) accepted) substitution

theorem checkedClassifyingSection_derivation_independent (other : Certificate D)
    (otherAccepted : check other (.term context term type) = true) :
    checkedClassifyingSection interpretation headers certificate accepted =
      checkedClassifyingSection interpretation headers other otherAccepted :=
  interpretation.classifyingSection_derivation_independent headers
    (reconstruct certificate (.term context term type) accepted)
    (reconstruct other (.term context term type) otherAccepted)

theorem unequal_certificates_retain_origins (other : Certificate D)
    (otherAccepted : check other (.term context term type) = true) (different : certificate ≠ other) :
    reconstruct certificate (.term context term type) accepted ≠
      reconstruct other (.term context term type) otherAccepted := by
  intro same
  apply different
  exact (erase_reconstruct certificate (.term context term type) accepted).symm.trans
    ((congrArg erase same).trans (erase_reconstruct other (.term context term type) otherAccepted))

end Mettapedia.OSLF.NativeTypes.Certificates.Refinement
