import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SourceInterfaces
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Checking
import Mettapedia.OSLF.NativeTypes.Generation.Displayed
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.InstallationLaws

/-!
# Authored indexed modal formation and operational declarations in one checker

The displayed profile, scoped interface decoder and constructor slots are
checked before installation. The operational signature remains on the left;
the target-premised classifier signature is on the right. No equation-stable
profile is identified with finite displayed matching.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Pipeline

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open Mettapedia.OSLF.NativeTypes.SortProfiles
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

variable (operational : BindingPipeline.Installed)

abbrev classifierSignature : CubeEnrichment.Signature where
  Carrier := NativeSignature.Carrier (NativeCubeProfile.language operational)
  Former := {constructor : operational.declarations.Constructor //
    operational.generated.logicFragment.core.structural = true}
  arity constructor := (operational.declarations.parameters constructor.val).length
  input constructor position := (operational.declarations.parameters constructor.val)[position]
  output constructor := operational.declarations.result constructor.val

/-- Constructor coordinates are read from their authored slots. No modal
free-code former is inserted into this classifier alphabet. -/
def classifierVertex? : Option (CubeEnrichment.Vertex (classifierSignature operational)) :=
  if complete : ∀ constructor, (NativeCubeProfile.slots? operational (.inl constructor.val)).isSome then
    some (fun constructor => (NativeCubeProfile.slots? operational (.inl constructor.val)).get (complete constructor))
  else none

def selectedHeaders? :=
  if operational.generated.logicFragment.core.modal then SourceInterfaces.decodeAll? operational else some []

inductive Issue where
  | operational (issue : BindingPipeline.GenerationIssue)
  | profile
  | interface
  | constructorSlots
  deriving Repr

structure Installed where
  operational : BindingPipeline.Installed
  vertex : DisplayedGraph.Vertex (NativeCubeProfile.language operational)
  matching : List (DisplayedGraph.EquationMatching (NativeCubeProfile.language operational))
  admitted : DisplayedGraph.admit? (NativeCubeProfile.language operational) matching vertex = some true
  headers : List (SourceInterfaces.Header operational)
  decoded : selectedHeaders? operational = some headers
  interfaceTable : List (Interface (NativeSignature.Carrier (NativeCubeProfile.language operational)))
  interfacesDerived : interfaceTable = headers.map (fun header => header.interface vertex)
  classifierVertex : CubeEnrichment.Vertex (classifierSignature operational)
  classifierDecoded : classifierVertex? operational = some classifierVertex

def install (vertex : DisplayedGraph.Vertex (NativeCubeProfile.language operational))
    (matching : List (DisplayedGraph.EquationMatching (NativeCubeProfile.language operational))) :
    Except Issue Installed :=
  if admitted : DisplayedGraph.admit? (NativeCubeProfile.language operational) matching vertex = some true then
    match decoded : selectedHeaders? operational with
    | none => .error .interface
    | some headers =>
        match classifierDecoded : classifierVertex? operational with
        | none => .error .constructorSlots
        | some classifierVertex =>
            let interfaceTable := headers.map (fun header => header.interface vertex)
            .ok ⟨operational, vertex, matching, admitted, headers, decoded, interfaceTable, rfl,
              classifierVertex, classifierDecoded⟩
  else .error .profile

def generate (snapshot : Snapshot) (language : LanguageFragment) (logic : BindingPipeline.Logic)
    (vertex : DisplayedGraph.Vertex (selectedSnapshot snapshot language).language)
    (matching : List (DisplayedGraph.EquationMatching (selectedSnapshot snapshot language).language)) :
    Except Issue Installed :=
  let displayed := Displayed.generate snapshot language logic.observations vertex matching
  match checked : BindingPipeline.installGenerated snapshot.language displayed.generated logic.native with
  | .error issue => .error (.operational issue)
  | .ok operational =>
      have same : NativeCubeProfile.language operational = displayed.generated.snapshot.language :=
        (NativeCubeProfile.language_preserved operational).trans
          (congrArg (fun generated => generated.snapshot.language) (installed_generated checked))
      let fullVertex := cast (congrArg DisplayedGraph.Vertex same.symm) displayed.fullVertex
      let matching := cast (congrArg (fun source => List (DisplayedGraph.EquationMatching source)) same.symm)
        displayed.matching
      install operational fullVertex matching

namespace Installed

variable (installed : Installed)

def interfaces (index : Fin installed.headers.length) :=
  installed.interfaceTable[index.val]'(by
    rw [installed.interfacesDerived, List.length_map]
    exact index.isLt)

theorem interfaces_source (index : Fin installed.headers.length) :
    installed.interfaces index = installed.headers[index].interface installed.vertex := by
  unfold interfaces
  simp only [installed.interfacesDerived, List.getElem_map, Fin.getElem_fin]

abbrev classifiers := Declarations.signature installed.classifierVertex installed.interfaces

abbrev signature := SignatureSum.signature installed.operational.signature installed.classifiers

abbrev symbols := SignatureSum.symbols installed.operational.symbols
  (Declarations.symbols (D := classifierSignature installed.operational) installed.interfaces)

def formation : HeaderFormation installed.signature :=
  SignatureSum.headers installed.operational.signature installed.classifiers
    installed.operational.formation (Declarations.headerFormation installed.classifierVertex installed.interfaces)

def check (certificate : Certificates.Refinement.Certificate installed.signature)
    (judgment : Judgment installed.symbols) : NativeLogic.CheckResult :=
  NativeLogic.check installed.operational.logic certificate judgment

theorem check_exact (certificate : Certificates.Refinement.Certificate installed.signature)
    (judgment : Judgment installed.symbols) :
    installed.check certificate judgment = .accepted ↔
      installed.operational.logic.permits judgment ∧ NativeLogic.CertificatePermitted installed.operational.logic certificate ∧
      ∃ derivation : Derivation installed.signature judgment,
        Certificates.Refinement.erase derivation = certificate :=
  NativeLogic.check_exact installed.operational.logic certificate judgment

def m_form (index : Fin installed.headers.length) :=
  SignatureSum.derivationRight installed.operational.signature installed.classifiers
    (Declarations.m_form installed.classifierVertex installed.interfaces index)

/-- Existing certificates retain all source symbols and source occurrence
indices under the genuine rule-by-rule embedding into the joined checker. -/
def sourceDerivation {judgment : Judgment installed.operational.symbols}
    (tree : Derivation installed.operational.signature judgment) :
    Derivation installed.signature (SignatureSum.judgmentLeft judgment) :=
  SignatureSum.derivationLeft installed.operational.signature installed.classifiers tree

theorem source_certificate_checked {judgment : Judgment installed.operational.symbols}
    (tree : Derivation installed.operational.signature judgment) :
    Certificates.Refinement.check (Certificates.Refinement.erase (installed.sourceDerivation tree))
      (SignatureSum.judgmentLeft judgment) = true :=
  Certificates.Refinement.check_erase (installed.sourceDerivation tree)

theorem origins_complete : installed.headers.map (·.origin) =
    (if installed.operational.generated.logicFragment.core.modal then List.finRange installed.operational.modal.length else []) := by
  have decoded := installed.decoded
  unfold selectedHeaders? at decoded
  split at decoded <;> split
  · exact SourceInterfaces.decodeAll_origins installed.operational decoded
  · contradiction
  · contradiction
  · rw [← Option.some.inj decoded]
    rfl

theorem origins_distinct : (installed.headers.map (·.origin)).Nodup := by
  rw [installed.origins_complete]
  split
  · exact List.nodup_finRange _
  · exact List.nodup_nil

theorem m_form_checked (index : Fin installed.headers.length) :
    Certificates.Refinement.check (Certificates.Refinement.erase (installed.m_form index))
      (SignatureSum.judgmentRight
        (.term (SignatureSum.contextLeft (parameters (D := classifierSignature installed.operational)
          (installed.interfaces index)))
          (Declarations.modalCode (D := classifierSignature installed.operational) installed.interfaces index)
          (SignatureSum.typeLeft (result (D := classifierSignature installed.operational)
            (installed.interfaces index))))) = true :=
  Certificates.Refinement.check_erase (installed.m_form index)

end Installed

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Pipeline
