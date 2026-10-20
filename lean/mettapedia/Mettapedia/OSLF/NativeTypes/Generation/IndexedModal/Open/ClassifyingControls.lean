import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.Classifying
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.LambdaEvents
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SharedChecking

/-!
# Curried declaration formation and complete-classification controls

The selected lambda declaration has a genuine nonempty local binder prefix.
Its ambient focus header is formed by the full rank-sensitive classifying
installation and checked using the existing certificate checker. The same
well-formed declaration rejects a certificate for an unrelated context rule.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ClassifyingControls

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

variable (installed : Joined.Installed)

def judgment (index : installed.Index) : Judgment installed.symbols :=
  .type ((SourceModel.signature installed).termParameters (installed.modalSymbol index))
    ((SourceModel.signature installed).termResult (installed.modalSymbol index))

def tree (index : installed.Index) :
    Derivation (SourceModel.signature installed) (judgment installed index) :=
  (Classifying.headers installed).termResult (installed.modalSymbol index)

/-- Computed local formation, rather than a caller's semantic admission,
supplies a certificate accepted in the full vocabulary. -/
theorem formed (index : installed.Index) :
    NativeLogic.check (D := SourceModel.signature installed) NativeLogic.full (Certificates.Refinement.erase (tree installed index))
      (judgment installed index) = .accepted :=
  (NativeLogic.check_exact (D := SourceModel.signature installed) _ _ _).mpr
    ⟨NativeLogic.full_permits _, NativeLogic.full_certificatePermitted _, tree installed index, rfl⟩

/-- Rejection concerns this supplied certificate, not the declaration's
inhabitance or semantic validity. -/
theorem wrong_certificate (index : installed.Index) :
    NativeLogic.check (D := SourceModel.signature installed) NativeLogic.full (.node .contextNil Fin.elim0)
      (judgment installed index) = .certificateRejected := by
  rw [NativeLogic.check_vocabulary_exact (D := SourceModel.signature installed)]
  simp only [NativeLogic.checkedVocabulary, NativeLogic.full_accepts,
    NativeLogic.full_certificateAllowed, Bool.true_and, if_true]
  rfl

/-- Exercise the dependent ambient header at a binder-local source site. -/
def control : IO Unit := do
  let .ok installed := Consumers.generate BindingPipeline.Controls.originalLambda
    | throw (IO.userError "Lambda installation refused")
  let some index := (List.finRange installed.indexed.headers.length).find? (fun index =>
      !(CurriedInterfaces.header installed.indexed index).focusBinders.isEmpty)
    | throw (IO.userError "No binder-local modal declaration")
  let certificate := SharedChecking.emit (SourceModel.signature installed) (tree installed index)
  if SharedChecking.check (SourceModel.signature installed) NativeLogic.full certificate
      (judgment installed index) != .accepted then
    throw (IO.userError "Curried binder-local result formation rejected")
  if NativeLogic.check (D := SourceModel.signature installed) NativeLogic.full (.node .contextNil Fin.elim0)
      (judgment installed index) != .certificateRejected then
    throw (IO.userError "Unrelated context certificate accepted as a dependent result")
  IO.println "Classifying: binder-local full header accepted; wrong certificate rejected"

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ClassifyingControls
