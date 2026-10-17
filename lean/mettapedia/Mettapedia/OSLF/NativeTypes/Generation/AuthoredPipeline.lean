import Mettapedia.OSLF.NativeTypes.Generation.NativeCubeProfile
import Mettapedia.OSLF.NativeTypes.Certificates.DeferredSeededSearch
import Mettapedia.OSLF.NativeTypes.Generation.BindingNativeSearch
import Mettapedia.OSLF.NativeTypes.Generation.ConstructorOrigins
import Mettapedia.OSLF.NativeTypes.Generation.NativeStructuralTypes
import Mettapedia.OSLF.NativeTypes.Generation.NativeModalContinuation
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeKindSearch
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingModalAdmission
import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingTreeAdmission

/-!
# Authored execution and cube-enriched native judgments

One installation consumes the authored presentation and the three selection
inputs. The checked cube slots change actual native declaration contexts and
result types. The common finite checker and fair search consume this enriched
signature; the operational scheduler retains its independently checked scoped
semantics.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

inductive Issue where
  | installation (reason : BindingPipeline.GenerationIssue)
  | cubeSlots
  | freeContext
  | nativeOperational
  | modalMeaning
  | modalSourceTree
  deriving DecidableEq, Repr

structure Installed where
  operational : BindingPipeline.Installed
  vertex : CubeEnrichment.Vertex (NativeCubeProfile.signature operational)
  decoded : NativeCubeProfile.vertex? operational = some vertex
  freeEmpty : (BindingPipeline.plan operational.generated).snapshot.free =
    Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
  operationalMeaning : Modal.NativeOperationalProfile.check operational.Environment = true
  modalMeanings : ∀ index : Fin operational.modal.length,
    Modal.NativeBindingModalAdmission.Admitted operational.modal[index]
  sourceTrees : Modal.NativeBindingTreeAdmission.check (BindingPipeline.plan operational.generated) = true

def generate (snapshot : Snapshot) (language : LanguageFragment) (logic : BindingPipeline.Logic)
    (vertex : SortProfiles.Derived.CubeVertex (selectedSnapshot snapshot language).language) :
    Except Issue Installed := do
  let operational ← (BindingPipeline.generate snapshot language logic vertex).mapError Issue.installation
  if freeTypesEmpty : (BindingPipeline.plan operational.generated).snapshot.freeTypes = [] then
    have freeEmpty : (BindingPipeline.plan operational.generated).snapshot.free =
        Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty := by
      funext name
      change ((BindingPipeline.plan operational.generated).snapshot.freeTypes.find?
        (fun entry => entry.1 == name)).map Prod.snd = none
      rw [freeTypesEmpty]
      rfl
    if operationalMeaning : Modal.NativeOperationalProfile.check operational.Environment = true then
      let meanings : Option (∀ index : Fin operational.modal.length,
          Modal.NativeBindingModalAdmission.Admitted operational.modal[index]) :=
        Modal.NativeBindingModalAdmission.allFin?
          (fun index : Fin operational.modal.length =>
            Modal.NativeBindingModalAdmission.check? operational.modal[index])
      match meanings with
      | none => .error .modalMeaning
      | some modalMeanings =>
          if sourceTrees : Modal.NativeBindingTreeAdmission.check (BindingPipeline.plan operational.generated) = true then
            match decoded : NativeCubeProfile.vertex? operational with
            | none => .error .cubeSlots
            | some decodedVertex =>
                .ok ⟨operational, decodedVertex, decoded, freeEmpty, operationalMeaning, modalMeanings, sourceTrees⟩
          else .error .modalSourceTree
    else .error .nativeOperational
  else .error .freeContext

namespace Installed

variable (installed : Installed)

abbrev signature := NativeCubeProfile.enrichedSignature installed.operational installed.vertex
abbrev symbols := CubeNativeExtension.symbols installed.operational.symbols
  (NativeCubeProfile.signature installed.operational)

def formation : HeaderFormation installed.signature :=
  NativeCubeProfile.enrichedFormation installed.operational installed.vertex

def operationalDerivation {judgment : Judgment installed.operational.symbols}
    (tree : Derivation installed.operational.signature judgment) :
    Derivation installed.signature (SignatureSum.judgmentLeft (SignatureSum.judgmentLeft judgment)) :=
  CubeNativeExtension.sourceDerivation installed.operational.signature installed.vertex 4
    (NativeCubeProfile.sourceCarriers installed.operational) (by decide) tree

def cubeDerivation {judgment : Judgment (CubeNativeDeclarations.symbols
      (NativeCubeProfile.signature installed.operational))}
    (tree : Derivation (CubeNativeDeclarations.signature installed.vertex) judgment) :
    Derivation installed.signature (SignatureSum.judgmentLeft (SignatureSum.judgmentRight judgment)) :=
  CubeNativeExtension.carry installed.operational.signature installed.vertex 4
    (NativeCubeProfile.sourceCarriers installed.operational) (by decide)
    (SignatureSum.derivationRight installed.operational.signature
      (CubeNativeDeclarations.signature installed.vertex) tree)

/-- Independent cube inference constructs a checked full-native tree, whose
complete evidence is then carried into this installation's shared alphabet. -/
def cubeFormation? {carrier : (NativeCubeProfile.signature installed.operational).Carrier}
    (code : CubeNativeKindEncoding.PureCode carrier) (kind : Mettapedia.OSLF.Framework.ModalHypercube.HSort) :
    Option (TermExpr installed.symbols 0 × Certificates.Refinement.Certificate installed.signature) :=
  match emitted : CubeNativeKindSearch.nativeFormation? installed.vertex code kind with
  | none => none
  | some (term, certificate) =>
      let judgment := Judgment.term .nil term
        (CubeNativeDeclarations.typingType carrier (CubeNativeKindEncoding.encode code)
          (CubeNativeDeclarations.sortCode carrier kind 0))
      let tree := Certificates.Refinement.reconstruct certificate judgment
        (CubeNativeKindSearch.nativeFormation?_checked installed.vertex code kind term certificate emitted)
      some (SignatureSum.termLeft (SignatureSum.termRight term),
        Certificates.Refinement.erase (installed.cubeDerivation tree))

def cubeJudgment {carrier : (NativeCubeProfile.signature installed.operational).Carrier}
    (code : CubeNativeKindEncoding.PureCode carrier) (kind : Mettapedia.OSLF.Framework.ModalHypercube.HSort)
    (term : TermExpr installed.symbols 0) : Judgment installed.symbols :=
  .term .nil term (SignatureSum.typeLeft (SignatureSum.typeRight
    (CubeNativeDeclarations.typingType carrier (CubeNativeKindEncoding.encode code)
      (CubeNativeDeclarations.sortCode carrier kind 0))))

theorem cubeFormation?_checked {carrier : (NativeCubeProfile.signature installed.operational).Carrier}
    (code : CubeNativeKindEncoding.PureCode carrier) (kind : Mettapedia.OSLF.Framework.ModalHypercube.HSort)
    (term : TermExpr installed.symbols 0) (certificate : Certificates.Refinement.Certificate installed.signature)
    (emitted : installed.cubeFormation? code kind = some (term, certificate)) :
    Certificates.Refinement.check certificate (installed.cubeJudgment code kind term) = true := by
  unfold cubeFormation? at emitted
  split at emitted
  · cases emitted
  · cases emitted
    exact Certificates.Refinement.check_erase _

theorem cubeFormation?_exact {carrier : (NativeCubeProfile.signature installed.operational).Carrier}
    (code : CubeNativeKindEncoding.PureCode carrier) (kind : Mettapedia.OSLF.Framework.ModalHypercube.HSort) :
    (installed.cubeFormation? code kind).isSome = true ↔
      Nonempty (CubeEnrichment.Kinded installed.vertex code kind) := by
  have same : (installed.cubeFormation? code kind).isSome =
      (CubeNativeKindSearch.nativeFormation? installed.vertex code kind).isSome := by
    unfold cubeFormation?
    split <;> simp_all
  rw [same]
  exact CubeNativeKindSearch.nativeFormation?_exact _ _ _

def check (certificate : Certificates.Refinement.Certificate installed.signature)
    (judgment : Judgment installed.symbols) : NativeLogic.CheckResult :=
  NativeLogic.check installed.operational.logic certificate judgment

theorem check_exact (certificate : Certificates.Refinement.Certificate installed.signature)
    (judgment : Judgment installed.symbols) :
    installed.check certificate judgment = .accepted ↔
      installed.operational.logic.permits judgment ∧
      NativeLogic.CertificatePermitted installed.operational.logic certificate ∧
      ∃ derivation : Derivation installed.signature judgment,
        Certificates.Refinement.erase derivation = certificate := NativeLogic.check_exact _ _ _

/-- Priority certificates are rechecked in their original signature before
their complete derivations are transported. This retains ordered subtrees. -/
def liftOperational? (certificate : Certificates.Refinement.Certificate installed.operational.signature) :
    Option (Certificates.Refinement.Certificate installed.signature) :=
  let judgment := certificate.root.conclusion
  if checked : Certificates.Refinement.check certificate judgment = true then
    some (Certificates.Refinement.erase (installed.operationalDerivation
      (Certificates.Refinement.reconstruct certificate judgment checked)))
  else none

def rawSeeds : List (Certificates.Refinement.Certificate installed.signature) :=
  installed.operational.derivationSeeds.map (fun named =>
    Certificates.Refinement.erase (installed.operationalDerivation named.2)) ++
    (List.finRange installed.operational.declarations.headers.length).map (fun constructor =>
      Certificates.Refinement.erase (installed.operationalDerivation
        (installed.operational.constructorDerivation
          (installed.operational.declarations.structuralFormation constructor)))) ++
    (List.finRange installed.operational.modal.length).map (fun index =>
      Certificates.Refinement.erase (installed.operationalDerivation
        (NativeModalContinuation.genericResponseFormation (BindingPipeline.plan installed.operational.generated)
          installed.operational.declarations installed.operational.modal index))) ++
    ((List.finRange installed.operational.declarations.headers.length).map Sum.inl ++
      (List.finRange installed.operational.modal.length).map Sum.inr).flatMap fun former =>
      [Certificates.Refinement.erase (installed.cubeDerivation
        (CubeNativeClosedFormation.primitiveFormation installed.vertex (.former former))),
       Certificates.Refinement.erase (installed.cubeDerivation
        (CubeNativeClosedFormation.primitiveFormation installed.vertex (.formation former)))]

/-- Structural judgments precede the operational declaration catalogue.
Each family retains its declaration order and complete certificate. -/
def rawSeedFactories : List (Unit → Certificates.Refinement.Certificate installed.signature) :=
  (List.finRange installed.operational.declarations.headers.length).map (fun constructor _ =>
      Certificates.Refinement.erase (installed.operationalDerivation
        (installed.operational.constructorDerivation
          (installed.operational.declarations.structuralFormation constructor)))) ++
    installed.operational.derivationSeedFactories.map (fun factory _ =>
      Certificates.Refinement.erase (installed.operationalDerivation (factory ()).2)) ++
    (List.finRange installed.operational.modal.length).map (fun index _ =>
      Certificates.Refinement.erase (installed.operationalDerivation
        (NativeModalContinuation.genericResponseFormation (BindingPipeline.plan installed.operational.generated)
          installed.operational.declarations installed.operational.modal index))) ++
    ((List.finRange installed.operational.declarations.headers.length).map Sum.inl ++
      (List.finRange installed.operational.modal.length).map Sum.inr).flatMap fun former =>
      [fun _ => Certificates.Refinement.erase (installed.cubeDerivation
        (CubeNativeClosedFormation.primitiveFormation installed.vertex (.former former))),
       fun _ => Certificates.Refinement.erase (installed.cubeDerivation
        (CubeNativeClosedFormation.primitiveFormation installed.vertex (.formation former)))]

theorem rawSeedFactories_perm :
    (installed.rawSeedFactories.map (fun factory => factory ())).Perm installed.rawSeeds := by
  have operational := List.Perm.map
    (fun named : Σ judgment, Derivation installed.operational.signature judgment =>
      Certificates.Refinement.erase (installed.operationalDerivation named.2))
    installed.operational.derivationSeedFactories_perm
  simp only [List.map_map, Function.comp_def] at operational
  simp only [rawSeedFactories, rawSeeds, List.map_append, List.map_map,
    List.map_flatMap, List.map_cons, List.map_nil, Function.comp_def]
  apply List.Perm.append_right
  apply List.Perm.append_right
  exact List.perm_append_comm.trans (List.Perm.append_right _ operational)

theorem rawSeedFactories_length : installed.rawSeedFactories.length = installed.rawSeeds.length := by
  simpa only [List.length_map] using installed.rawSeedFactories_perm.length_eq

def nativeSeeds : List (Tree (NativeLogic.presentation installed.operational.logic installed.signature)) :=
  installed.rawSeeds.filterMap fun certificate =>
    if selected : NativeLogic.certificateAllowedFast installed.operational.logic certificate = true then
      some (NativeLogic.restrict installed.operational.logic certificate
        ((NativeLogic.certificateAllowedFast_exact _ _).mp selected))
    else none

/-- Refused vocabulary keeps an explicit empty scheduled position. It is not
counted as a refutation and does not collapse later occurrence identities. -/
def nativeSeedFactories : List (Unit → Option
    (Tree (NativeLogic.presentation installed.operational.logic installed.signature))) :=
  installed.rawSeedFactories.map fun factory _ =>
    let certificate := factory ()
    if selected : NativeLogic.certificateAllowedFast installed.operational.logic certificate = true then
      some (NativeLogic.restrict installed.operational.logic certificate
        ((NativeLogic.certificateAllowedFast_exact _ _).mp selected))
    else none

abbrev SearchState := Search.State (NativeLogic.presentation installed.operational.logic installed.signature)

def search (judgment : Judgment installed.symbols) (budget : Nat) : installed.SearchState :=
  NativeLogic.searchWithDeferred installed.operational.logic installed.nativeSeedFactories judgment budget

def resume (judgment : Judgment installed.symbols) (budget : Nat)
    (state : installed.SearchState) : installed.SearchState :=
  NativeLogic.resumeWithDeferred installed.operational.logic installed.nativeSeedFactories judgment budget state

theorem resume_add (judgment : Judgment installed.symbols) (first second : Nat) :
    installed.search judgment (first + second) =
      installed.resume judgment second (installed.search judgment first) := by
  exact NativeLogic.deferred_resume installed.operational.logic installed.nativeSeedFactories judgment first second

theorem stable (judgment : Judgment installed.symbols) (budget extra : Nat)
    (tree : Tree (NativeLogic.presentation installed.operational.logic installed.signature))
    (found : (installed.search judgment budget).found = some tree) :
    installed.search judgment (budget + extra) = installed.search judgment budget :=
  NativeLogic.deferred_stable _ _ _ _ _ _ found

theorem sound (judgment : Judgment installed.symbols) (budget : Nat)
    (tree : Tree (NativeLogic.presentation installed.operational.logic installed.signature))
    (found : (installed.search judgment budget).found = some tree) :
    installed.operational.logic.permits judgment ∧
      NativeLogic.CertificatePermitted installed.operational.logic (NativeLogic.embed _ tree) ∧
      ∃ derivation : Derivation installed.signature judgment,
        Certificates.Refinement.erase derivation = NativeLogic.embed _ tree :=
  NativeLogic.deferred_sound _ _ _ _ _ found

theorem discovery (judgment : Judgment installed.symbols)
    (certificate : Certificates.Refinement.Certificate installed.signature)
    (selected : NativeLogic.CertificatePermitted installed.operational.logic certificate)
    (accepted : Certificates.Refinement.check certificate judgment = true) :
    ∃ found, (installed.search judgment
      (DeferredSeededSearch.discoveryBound installed.nativeSeedFactories.length
        (Tree.wireSize (NativeLogic.restrict installed.operational.logic certificate selected)))).found = some found := by
  apply NativeLogic.deferred_discovery installed.operational.logic installed.nativeSeedFactories judgment
    (NativeLogic.restrict installed.operational.logic certificate selected)
  have comparison := NativeLogic.embed_check installed.operational.logic
    (NativeLogic.restrict installed.operational.logic certificate selected) judgment
  rw [NativeLogic.embed_restrict] at comparison
  exact comparison.trans accepted

end Installed

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline
