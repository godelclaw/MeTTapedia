import Mettapedia.OSLF.NativeTypes.Certificates.RefinementChecking
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPresheafCertificates

/-!
# Checked raw certificates and their native presheaf evidence

Acceptance by the computational checker reconstructs the independently
generated dependent derivation. Its existing full-rule interpreter then earns
the native meaning and value-section readout. Primitive declaration meanings
remain the independent interpretation inputs; whole-tree soundness is proved.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.Refinement

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi
open Mettapedia.TypeTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Computability.ComputationalTrinity

universe u v

variable {S : NativeDependent.Refinement.Symbols.{v}}
variable {D : NativeDependent.Refinement.Signature S}
variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol]
  [DecidableEq S.PredicateSymbol]
variable {C : Type u} [Category.{u} C]

theorem checked_native_sound
    (model : NativeDependent.Refinement.ModelData S C)
    (realization : NativeDependent.Refinement.SignatureRealization model D)
    (certificate : Certificate D) (judgment : NativeDependent.Refinement.Judgment S)
    (accepted : check certificate judgment = true) :
    NativeDependent.Refinement.Interprets model judgment :=
  (reconstruct certificate judgment accepted).native_sound model realization

section ValueReadout

variable {S : NativeDependent.Refinement.Symbols.{u}}
variable {D : NativeDependent.Refinement.Signature S}
variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol]
  [DecidableEq S.PredicateSymbol]
variable {n : Nat} {context : NativeDependent.Refinement.ContextExpr S n}
variable {term : NativeDependent.Refinement.TermExpr S n}
variable {type : NativeDependent.Refinement.TypeExpr S n}
variable {P : Face.{u, u, u} C}

/-- The value is evaluated from the actual supplied native term, and its
dependent type is the interpretation's decoded family. -/
noncomputable def checkedSection
    (interpretation : NativeDependent.RefinementPresheafCertificates.Interpretation D context term type P)
    (certificate : Certificate D)
    (accepted : check certificate (.term context term type) = true) :=
  interpretation.nativeSection (reconstruct certificate (.term context term type) accepted)

theorem checkedSection_readout
    (interpretation : NativeDependent.RefinementPresheafCertificates.Interpretation D context term type P)
    (certificate : Certificate D)
    (accepted : check certificate (.term context term type) = true) :
    interpretation.model.evaluateTerm interpretation.semanticContext term =
      some ⟨interpretation.semanticType, checkedSection interpretation certificate accepted⟩ :=
  interpretation.nativeSection_readout (reconstruct certificate (.term context term type) accepted)

end ValueReadout

end Mettapedia.OSLF.NativeTypes.Certificates.Refinement
