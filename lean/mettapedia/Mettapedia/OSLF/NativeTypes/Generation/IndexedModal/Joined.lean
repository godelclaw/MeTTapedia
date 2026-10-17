import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SourceInjection
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SemanticReceipts
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FocusChecking

/-!
# One installation for full modal formation, source values and native receipts

Classifier codes and original program values have distinct carriers linked
by a typed injection. Full modal parameters and their focus projections use
the original certificate checker. Operational receipts enter the existing
independent native event interpretation without erasing source indices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Joined

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Modal
open NativeReceiptRechecking
open NativeBindingEventAction (bound)

structure Installed where
  indexed : Pipeline.Installed
  semantic : SemanticReceipts.Companion indexed

inductive Issue where
  | indexed (reason : Pipeline.Issue)
  | semanticProfile
  deriving Repr

def generate (snapshot : Snapshot) (language : LanguageFragment) (logic : BindingPipeline.Logic)
    (vertex : SortProfiles.DisplayedGraph.Vertex (selectedSnapshot snapshot language).language)
    (matching : List (SortProfiles.DisplayedGraph.EquationMatching (selectedSnapshot snapshot language).language)) :
    Except Issue Installed := do
  let indexed ← (Pipeline.generate snapshot language logic vertex matching).mapError Issue.indexed
  match SemanticReceipts.admit? indexed with
  | none => .error .semanticProfile
  | some semantic => .ok ⟨indexed, semantic⟩

namespace Installed

variable (installed : Installed)

abbrev Index := Fin installed.indexed.headers.length
abbrev symbols := SourceInjection.symbols installed.indexed
abbrev signature := SourceInjection.signature installed.indexed

def formation : HeaderFormation installed.signature := SourceInjection.computedHeaders installed.indexed

def check (certificate : Certificates.Refinement.Certificate installed.signature)
    (judgment : Judgment installed.symbols) :=
  NativeLogic.check installed.indexed.operational.logic certificate judgment

theorem check_exact (certificate : Certificates.Refinement.Certificate installed.signature)
    (judgment : Judgment installed.symbols) :
    installed.check certificate judgment = .accepted ↔
      installed.indexed.operational.logic.permits judgment ∧
      NativeLogic.CertificatePermitted installed.indexed.operational.logic certificate ∧
      ∃ derivation : Derivation installed.signature judgment,
        Certificates.Refinement.erase derivation = certificate :=
  NativeLogic.check_exact _ _ _

abbrev modalSymbol (index : installed.Index) : installed.symbols.TermSymbol :=
  .inl (.inr (.inr index))

abbrev modalParameters (index : installed.Index) := installed.signature.termParameters (installed.modalSymbol index)
abbrev modalResult (index : installed.Index) := installed.signature.termResult (installed.modalSymbol index)

/-- The supplied substitution is a genuine independently checked native
judgment, including index membership and the dependent target continuation. -/
def m_form_at (index : installed.Index) {n : Nat} (context : ContextExpr installed.symbols n)
    (arguments : Substitution installed.symbols (installed.symbols.termArity (installed.modalSymbol index)) n)
    (formed : Derivation installed.signature (.context context))
    (typed : Derivation installed.signature (.substitution context (installed.modalParameters index) arguments)) :
    Derivation installed.signature (.term context (.primitive (installed.modalSymbol index) arguments)
      ((installed.modalResult index).substitute arguments)) :=
  deriveList (.primitive context (installed.modalSymbol index) arguments)
    (.cons formed (.cons (installed.formation.termHeader (installed.modalSymbol index))
      (.cons (installed.formation.termResult (installed.modalSymbol index)) (.cons typed .nil))))

def m_form (index : installed.Index) :=
  SourceInjection.classifierDerivation installed.indexed (installed.indexed.m_form index)

theorem m_form_checked (index : installed.Index) :
    Certificates.Refinement.check (Certificates.Refinement.erase (installed.m_form index))
      (SignatureSum.judgmentLeft (SignatureSum.judgmentRight
        (.term (SignatureSum.contextLeft (parameters (D := Pipeline.classifierSignature installed.indexed.operational)
          (installed.indexed.interfaces index)))
          (Declarations.modalCode (D := Pipeline.classifierSignature installed.indexed.operational)
            installed.indexed.interfaces index)
          (SignatureSum.typeLeft (result (D := Pipeline.classifierSignature installed.indexed.operational)
            (installed.indexed.interfaces index)))))) = true :=
  Certificates.Refinement.check_erase _

def focusClassifier (index : installed.Index) :=
  SourceInjection.classifierDerivation installed.indexed
    (SignatureSum.derivationRight installed.indexed.operational.signature installed.indexed.classifiers
      (Declarations.focusCodeFormed installed.indexed.classifierVertex installed.indexed.interfaces index))

abbrev programSort (index : installed.Index) := SemanticReceipts.programSort installed.indexed installed.semantic index

structure Receipt (index : installed.Index) (ambient : List String) (pattern : Pattern) where
  firing : Pipeline.Installed.Receipt installed.indexed index (bound ambient)
    (.base (installed.programSort index)) pattern
  frame : SemanticReceipts.Frame installed.indexed installed.semantic index ambient
  same : read frame.point.val.receipt = read firing.answer

def checkReceipt (index : installed.Index) (ambient : List String) (pattern : Pattern) (payload : Payload) :
    Option (Receipt installed index ambient pattern) :=
  match _found : installed.indexed.checkReceipt index (bound ambient) (.base (installed.programSort index)) pattern payload with
  | none => none
  | some firing =>
      match checked : SemanticReceipts.frame? installed.indexed installed.semantic index firing with
      | none => none
      | some frame => some ⟨firing, frame, SemanticReceipts.frame_read _ _ _ _ checked⟩

theorem checkReceipt_read {index : installed.Index} {ambient : List String} {pattern : Pattern}
    {payload : Payload} {receipt : Receipt installed index ambient pattern}
    (checked : installed.checkReceipt index ambient pattern payload = some receipt) :
    read receipt.frame.point.val.receipt = payload := by
  unfold checkReceipt at checked
  split at checked
  · cases checked
  · rename_i firing found
    split at checked
    · cases checked
    · cases Option.some.inj checked
      exact (SemanticReceipts.frame_read _ _ _ _ (by assumption)).trans
        (installed.indexed.checkReceipt_read found)

theorem checkReceipt_sound {index : installed.Index} {ambient : List String} {pattern : Pattern}
    {payload : Payload} {receipt : Receipt installed index ambient pattern}
    (checked : installed.checkReceipt index ambient pattern payload = some receipt) :
    Valid installed.indexed.operational.Environment (bound ambient) (.base (installed.programSort index)) pattern payload ∧
      payload.index = (installed.indexed.schema index).ordinal := by
  have same := receipt.same.symm.trans (installed.checkReceipt_read checked)
  refine ⟨?_, ?_⟩
  · rw [← same]
    exact receipt.firing.answer.valid
  · exact (congrArg Payload.index same).symm.trans receipt.firing.selected

theorem checkReceipt_complete (index : installed.Index) (ambient : List String) (pattern : Pattern) (payload : Payload)
    (valid : Valid installed.indexed.operational.Environment (bound ambient)
      (.base (installed.programSort index)) pattern payload)
    (selected : payload.index = (installed.indexed.schema index).ordinal) :
    ∃ receipt, installed.checkReceipt index ambient pattern payload = some receipt ∧
      read receipt.frame.point.val.receipt = payload := by
  obtain ⟨firing, found, same⟩ := installed.indexed.checkReceipt_complete valid selected
  obtain ⟨frame, checked, frameRead⟩ := SemanticReceipts.frame_complete installed.indexed installed.semantic index firing
  refine ⟨⟨firing, frame, frameRead⟩, ?_, frameRead.trans same⟩
  unfold checkReceipt
  split
  · rename_i absent
    rw [found] at absent
    cases absent
  · rename_i actual foundAgain
    cases Option.some.inj (foundAgain.symm.trans found)
    split
    · rename_i absent
      rw [checked] at absent
      cases absent
    · rename_i actualFrame checkedAgain
      cases Option.some.inj (checkedAgain.symm.trans checked)
      rfl

theorem checkReceipt_exact (index : installed.Index) (ambient : List String) (pattern : Pattern) (payload : Payload) :
    (installed.checkReceipt index ambient pattern payload).isSome = true ↔
      Valid installed.indexed.operational.Environment (bound ambient) (.base (installed.programSort index)) pattern payload ∧
        payload.index = (installed.indexed.schema index).ordinal := by
  constructor
  · intro accepted
    cases checked : installed.checkReceipt index ambient pattern payload with
    | none => rw [checked] at accepted; cases accepted
    | some receipt => exact installed.checkReceipt_sound checked
  · rintro ⟨valid, selected⟩
    obtain ⟨receipt, checked, _⟩ := installed.checkReceipt_complete index ambient pattern payload valid selected
    rw [checked]
    rfl

end Installed

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Joined
