import Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline

/-!
# Retained search catalogues for generated native judgments

Preparation keeps the generated factories across queries. The fair wire search
continues after those factories, and budget exhaustion retains unknown. Search
certifies derivability in the selected native grammar, not all semantic truth.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates

variable (installed : AuthoredPipeline.Installed)

/-- Each forced priority candidate is retained across queries on the same
immutable installation. Caching does not change a candidate or its slot. -/
def cachePrefix (factories : DeferredSeededSearch.Prefix
    (NativeLogic.presentation installed.operational.logic installed.signature)) :
    DeferredSeededSearch.Prefix
      (NativeLogic.presentation installed.operational.logic installed.signature) :=
  factories.map fun factory =>
    let cached := Thunk.mk factory
    fun _ => cached.get

theorem cachePrefix_exact (factories : DeferredSeededSearch.Prefix
    (NativeLogic.presentation installed.operational.logic installed.signature)) :
    installed.cachePrefix factories = factories := by
  unfold cachePrefix
  have same : (fun factory : Unit → Option
      (Tree (NativeLogic.presentation installed.operational.logic installed.signature)) =>
      let cached := Thunk.mk factory
      fun _ => cached.get) = id := by
    funext factory argument
    cases argument
    rfl
  rw [same, List.map_id]

structure Prepared where
  factories : DeferredSeededSearch.Prefix
    (NativeLogic.presentation installed.operational.logic installed.signature)
  generatedPrefix : factories = installed.nativeSeedFactories

def prepare : installed.Prepared :=
  ⟨installed.cachePrefix installed.nativeSeedFactories,
    installed.cachePrefix_exact installed.nativeSeedFactories⟩

namespace Prepared

variable {installed} (prepared : installed.Prepared)

def search (judgment : Judgment installed.symbols) (budget : Nat) : installed.SearchState :=
  NativeLogic.searchWithDeferred installed.operational.logic prepared.factories judgment budget

def resume (judgment : Judgment installed.symbols) (budget : Nat)
    (state : installed.SearchState) : installed.SearchState :=
  NativeLogic.resumeWithDeferred installed.operational.logic prepared.factories judgment budget state

theorem search_exact (judgment : Judgment installed.symbols) (budget : Nat) :
    prepared.search judgment budget = installed.search judgment budget := by
  simp only [search, Installed.search, prepared.generatedPrefix]

theorem resume_exact (judgment : Judgment installed.symbols) (budget : Nat)
    (state : installed.SearchState) :
    prepared.resume judgment budget state = installed.resume judgment budget state := by
  simp only [resume, Installed.resume, prepared.generatedPrefix]

theorem resume_add (judgment : Judgment installed.symbols) (first second : Nat) :
    prepared.search judgment (first + second) =
      prepared.resume judgment second (prepared.search judgment first) := by
  simp only [prepared.search_exact, prepared.resume_exact]
  exact installed.resume_add judgment first second

theorem stable (judgment : Judgment installed.symbols) (budget extra : Nat)
    (tree : Tree (NativeLogic.presentation installed.operational.logic installed.signature))
    (found : (prepared.search judgment budget).found = some tree) :
    prepared.search judgment (budget + extra) = prepared.search judgment budget := by
  rw [prepared.search_exact] at found ⊢
  rw [prepared.search_exact]
  exact installed.stable judgment budget extra tree found

theorem sound (judgment : Judgment installed.symbols) (budget : Nat)
    (tree : Tree (NativeLogic.presentation installed.operational.logic installed.signature))
    (found : (prepared.search judgment budget).found = some tree) :
    installed.operational.logic.permits judgment ∧
      NativeLogic.CertificatePermitted installed.operational.logic (NativeLogic.embed _ tree) ∧
      ∃ derivation : Derivation installed.signature judgment,
        Certificates.Refinement.erase derivation = NativeLogic.embed _ tree :=
  by
    apply installed.sound judgment budget tree
    rwa [prepared.search_exact] at found

theorem discovery (judgment : Judgment installed.symbols)
    (certificate : Certificates.Refinement.Certificate installed.signature)
    (selected : NativeLogic.CertificatePermitted installed.operational.logic certificate)
    (accepted : Certificates.Refinement.check certificate judgment = true) :
    ∃ found, (prepared.search judgment
      (DeferredSeededSearch.discoveryBound prepared.factories.length
        (Tree.wireSize (NativeLogic.restrict installed.operational.logic certificate selected)))).found = some found := by
  rw [prepared.search_exact, prepared.generatedPrefix]
  exact installed.discovery judgment certificate selected accepted

def query (judgment : Judgment installed.symbols) (budget : Nat) : BindingPipeline.Installed.NativeAnswer :=
  if installed.operational.logic.accepts judgment then
    if (prepared.search judgment budget).found.isSome then .proved else .unknown
  else .vocabularyRefused

theorem query_proved (judgment : Judgment installed.symbols) (budget : Nat)
    (proved : prepared.query judgment budget = .proved) :
    installed.operational.logic.permits judgment ∧
      ∃ certificate, NativeLogic.CertificatePermitted installed.operational.logic certificate ∧
        ∃ derivation : Derivation installed.signature judgment,
          Certificates.Refinement.erase derivation = certificate := by
  unfold query at proved
  split at proved
  · split at proved
    · rename_i found
      obtain ⟨tree, found⟩ := Option.isSome_iff_exists.mp found
      obtain ⟨permitted, selected, derivation, erased⟩ := prepared.sound judgment budget tree found
      exact ⟨permitted, _, selected, derivation, erased⟩
    · cases proved
  · cases proved

theorem query_refused (judgment : Judgment installed.symbols) (budget : Nat) :
    prepared.query judgment budget = .vocabularyRefused ↔
      ¬ installed.operational.logic.permits judgment := by
  simp only [query, NativeLogic.accepts_exact]
  split
  · split <;> simp_all
  · simp_all

theorem query_zero (judgment : Judgment installed.symbols)
    (selected : installed.operational.logic.permits judgment) :
    prepared.query judgment 0 = .unknown := by
  have accepted := (NativeLogic.accepts_exact installed.operational.logic judgment).mpr selected
  simp [query, accepted, search, NativeLogic.searchWithDeferred, DeferredSeededSearch.search,
    DeferredSeededSearch.run, Search.initial]

end Prepared

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed
