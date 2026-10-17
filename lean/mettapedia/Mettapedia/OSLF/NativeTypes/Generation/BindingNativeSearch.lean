import Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline
import Mettapedia.OSLF.NativeTypes.Generation.NativeLogicSearch
import Mettapedia.OSLF.NativeTypes.Generation.NativeModalDeclarations

/-!
# Native proof search for an authored installation

The finite priority prefix is computed from generated declaration formation
trees and the ordinary empty-context logical rules. Vocabulary selection is
checked on every intermediate judgment before a candidate enters the prefix.
The complete earned native enumeration follows the prefix, retaining fairness.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Installed

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates

variable (installed : BindingPipeline.Installed)

/-- The priority prefix is built from actual generated derivations. Keeping
their judgments avoids validating and reconstructing trusted formation trees
merely to transport them into another generated signature. -/
def derivationSeeds : List (Σ judgment, Derivation installed.signature judgment) :=
  let empty := NativeModalSignature.emptyFormed (plan installed.generated) installed.declarations installed.modal
  [⟨_, empty⟩] ++
    (List.finRange installed.declarations.headers.length).flatMap (fun constructor =>
      [⟨_, installed.formation.termHeader (.inl constructor)⟩,
       ⟨_, installed.formation.termResult (.inl constructor)⟩]) ++
    (List.finRange installed.modal.length).flatMap (fun index =>
      [⟨_, installed.formation.typeHeader (.inr (.input index))⟩,
       ⟨_, installed.formation.typeHeader (.inr (.event index))⟩,
       ⟨_, NativeModalSignature.eventFormed (plan installed.generated) installed.declarations installed.modal index⟩]) ++
    (NativeModalSignature.projections (plan installed.generated) installed.modal).flatMap (fun projection =>
      [⟨_, installed.formation.termResult (.inr projection)⟩,
       ⟨_, NativeModalSignature.projectionFormation (plan installed.generated)
         installed.declarations installed.modal projection⟩]) ++
    [⟨_, deriveList (.truthIntroduction .nil) (.cons empty .nil)⟩,
     ⟨_, deriveList (.truthFormation .nil) (.cons empty .nil)⟩,
     ⟨_, deriveList (.falsehoodFormation .nil) (.cons empty .nil)⟩]

/-- Certificate construction is deferred until its search position is visited.
The empty context and three logical certificates precede the generated
declaration certificates. Every original candidate and occurrence is retained. -/
def derivationSeedFactories : List (Unit → Σ judgment, Derivation installed.signature judgment) :=
  let empty := NativeModalSignature.emptyFormed (plan installed.generated) installed.declarations installed.modal
  [fun _ => ⟨_, empty⟩] ++
    [fun _ => ⟨_, deriveList (.truthIntroduction .nil) (.cons empty .nil)⟩,
     fun _ => ⟨_, deriveList (.truthFormation .nil) (.cons empty .nil)⟩,
     fun _ => ⟨_, deriveList (.falsehoodFormation .nil) (.cons empty .nil)⟩] ++
    (List.finRange installed.declarations.headers.length).flatMap (fun constructor =>
      [fun _ => ⟨_, installed.formation.termHeader (.inl constructor)⟩,
       fun _ => ⟨_, installed.formation.termResult (.inl constructor)⟩]) ++
    (List.finRange installed.modal.length).flatMap (fun index =>
      [fun _ => ⟨_, installed.formation.typeHeader (.inr (.input index))⟩,
       fun _ => ⟨_, installed.formation.typeHeader (.inr (.event index))⟩,
       fun _ => ⟨_, NativeModalSignature.eventFormed (plan installed.generated) installed.declarations installed.modal index⟩]) ++
    (NativeModalSignature.projections (plan installed.generated) installed.modal).flatMap (fun projection =>
      [fun _ => ⟨_, installed.formation.termResult (.inr projection)⟩,
       fun _ => ⟨_, NativeModalSignature.projectionFormation (plan installed.generated)
         installed.declarations installed.modal projection⟩])

private theorem logicalPriority_perm {α : Type _}
    (initial logical constructors modalities projections : List α) :
    List.Perm (initial ++ logical ++ constructors ++ modalities ++ projections)
      (initial ++ constructors ++ modalities ++ projections ++ logical) := by
  simpa only [List.append_assoc] using
    List.Perm.append_left initial
      (List.perm_append_comm (l₁ := logical) (l₂ := constructors ++ modalities ++ projections))

theorem derivationSeedFactories_perm :
    List.Perm (installed.derivationSeedFactories.map (fun factory => factory ()))
      installed.derivationSeeds := by
  simp only [derivationSeedFactories, derivationSeeds, List.map_append, List.map_flatMap,
    List.map_cons, List.map_nil]
  exact logicalPriority_perm _ _ _ _ _

theorem derivationSeedFactories_length :
    installed.derivationSeedFactories.length = installed.derivationSeeds.length := by
  simpa only [List.length_map] using (installed.derivationSeedFactories_perm).length_eq

def rawSeeds : List (Certificates.Refinement.Certificate installed.signature) :=
  installed.derivationSeeds.map fun named => Certificates.Refinement.erase named.2

def nativeSeeds : List (Tree (NativeLogic.presentation installed.logic installed.signature)) :=
  installed.rawSeeds.filterMap fun certificate =>
    if selected : NativeLogic.certificateAllowedFast installed.logic certificate = true then
      some (NativeLogic.restrict installed.logic certificate
        ((NativeLogic.certificateAllowedFast_exact _ _).mp selected))
    else none

abbrev NativeSearchState := Search.State (NativeLogic.presentation installed.logic installed.signature)

def searchNative (judgment : Judgment installed.symbols) (budget : Nat) : installed.NativeSearchState :=
  NativeLogic.searchWithSeeds installed.logic installed.nativeSeeds judgment budget

def resumeNative (judgment : Judgment installed.symbols) (budget : Nat)
    (state : installed.NativeSearchState) : installed.NativeSearchState :=
  SeededSearch.run installed.nativeSeeds judgment budget state

theorem native_resume_add (judgment : Judgment installed.symbols) (first second : Nat) :
    installed.searchNative judgment (first + second) =
      installed.resumeNative judgment second (installed.searchNative judgment first) :=
  NativeLogic.seeded_resume _ _ _ _ _

theorem native_stable (judgment : Judgment installed.symbols) (budget extra : Nat)
    (tree : Tree (NativeLogic.presentation installed.logic installed.signature))
    (found : (installed.searchNative judgment budget).found = some tree) :
    installed.searchNative judgment (budget + extra) = installed.searchNative judgment budget :=
  NativeLogic.seeded_stable _ _ _ _ _ _ found

theorem native_sound (judgment : Judgment installed.symbols) (budget : Nat)
    (tree : Tree (NativeLogic.presentation installed.logic installed.signature))
    (found : (installed.searchNative judgment budget).found = some tree) :
    installed.logic.permits judgment ∧ NativeLogic.CertificatePermitted installed.logic (NativeLogic.embed _ tree) ∧
      ∃ derivation : Derivation installed.signature judgment,
        Certificates.Refinement.erase derivation = NativeLogic.embed _ tree :=
  NativeLogic.seeded_sound _ _ _ _ _ found

theorem native_discovery (judgment : Judgment installed.symbols)
    (certificate : Certificates.Refinement.Certificate installed.signature)
    (selected : NativeLogic.CertificatePermitted installed.logic certificate)
    (accepted : Certificates.Refinement.check certificate judgment = true) :
    ∃ found, (installed.searchNative judgment
      (SeededSearch.discoveryBound installed.nativeSeeds.length
        (Tree.wireSize (NativeLogic.restrict installed.logic certificate selected)))).found = some found := by
  apply NativeLogic.seeded_discovery installed.logic installed.nativeSeeds judgment
    (NativeLogic.restrict installed.logic certificate selected)
  have comparison := NativeLogic.embed_check installed.logic
    (NativeLogic.restrict installed.logic certificate selected) judgment
  rw [NativeLogic.embed_restrict] at comparison
  exact comparison.trans accepted

/-- A generated catalogue is retained across queries. Its equality field is
earned by preparation, rather than supplied as a search completeness oracle. -/
structure PreparedNativeSearch where
  seeds : List (Tree (NativeLogic.presentation installed.logic installed.signature))
  generatedSeeds : seeds = installed.nativeSeeds

def prepareNativeSearch : installed.PreparedNativeSearch :=
  ⟨installed.nativeSeeds, rfl⟩

namespace PreparedNativeSearch

variable {installed} (prepared : installed.PreparedNativeSearch)

def search (judgment : Judgment installed.symbols) (budget : Nat) : installed.NativeSearchState :=
  NativeLogic.searchWithSeeds installed.logic prepared.seeds judgment budget

def resume (judgment : Judgment installed.symbols) (budget : Nat)
    (state : installed.NativeSearchState) : installed.NativeSearchState :=
  SeededSearch.run prepared.seeds judgment budget state

theorem search_exact (judgment : Judgment installed.symbols) (budget : Nat) :
    prepared.search judgment budget = installed.searchNative judgment budget := by
  simp only [search, searchNative, prepared.generatedSeeds]

theorem resume_exact (judgment : Judgment installed.symbols) (budget : Nat)
    (state : installed.NativeSearchState) :
    prepared.resume judgment budget state = installed.resumeNative judgment budget state := by
  simp only [resume, resumeNative, prepared.generatedSeeds]

theorem resume_add (judgment : Judgment installed.symbols) (first second : Nat) :
    prepared.search judgment (first + second) =
      prepared.resume judgment second (prepared.search judgment first) :=
  NativeLogic.seeded_resume _ _ _ _ _

theorem sound (judgment : Judgment installed.symbols) (budget : Nat)
    (tree : Tree (NativeLogic.presentation installed.logic installed.signature))
    (found : (prepared.search judgment budget).found = some tree) :
    installed.logic.permits judgment ∧ NativeLogic.CertificatePermitted installed.logic (NativeLogic.embed _ tree) ∧
      ∃ derivation : Derivation installed.signature judgment,
        Certificates.Refinement.erase derivation = NativeLogic.embed _ tree := by
  rw [prepared.search_exact] at found
  exact installed.native_sound judgment budget tree found

theorem discovery (judgment : Judgment installed.symbols)
    (certificate : Certificates.Refinement.Certificate installed.signature)
    (selected : NativeLogic.CertificatePermitted installed.logic certificate)
    (accepted : Certificates.Refinement.check certificate judgment = true) :
    ∃ found, (prepared.search judgment
      (SeededSearch.discoveryBound prepared.seeds.length
        (Tree.wireSize (NativeLogic.restrict installed.logic certificate selected)))).found = some found := by
  rw [prepared.search_exact, prepared.generatedSeeds]
  exact installed.native_discovery judgment certificate selected accepted

end PreparedNativeSearch

inductive NativeAnswer where
  | vocabularyRefused
  | unknown
  | proved
  deriving DecidableEq, Repr

def queryNative (judgment : Judgment installed.symbols) (budget : Nat) : NativeAnswer :=
  if installed.logic.accepts judgment then
    if (installed.searchNative judgment budget).found.isSome then .proved else .unknown
  else .vocabularyRefused

theorem queryNative_proved (judgment : Judgment installed.symbols) (budget : Nat)
    (proved : installed.queryNative judgment budget = .proved) :
    installed.logic.permits judgment ∧
      ∃ certificate, NativeLogic.CertificatePermitted installed.logic certificate ∧
        ∃ derivation : Derivation installed.signature judgment,
          Certificates.Refinement.erase derivation = certificate := by
  unfold queryNative at proved
  split at proved
  · split at proved
    · rename_i found
      obtain ⟨tree, found⟩ := Option.isSome_iff_exists.mp found
      obtain ⟨permitted, selected, derivation, erased⟩ :=
        installed.native_sound judgment budget tree found
      exact ⟨permitted, _, selected, derivation, erased⟩
    · cases proved
  · cases proved

theorem queryNative_refused (judgment : Judgment installed.symbols) (budget : Nat) :
    installed.queryNative judgment budget = .vocabularyRefused ↔
      ¬ installed.logic.permits judgment := by
  simp only [queryNative, NativeLogic.accepts_exact]
  split
  · split <;> simp_all
  · simp_all

theorem queryNative_zero (judgment : Judgment installed.symbols)
    (selected : installed.logic.permits judgment) :
    installed.queryNative judgment 0 = .unknown := by
  have accepted := (NativeLogic.accepts_exact installed.logic judgment).mpr selected
  simp [queryNative, accepted, searchNative, NativeLogic.searchWithSeeds,
    SeededSearch.search, SeededSearch.run, Search.initial]

end Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Installed
