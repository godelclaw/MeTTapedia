import Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline

/-!
# Retained search catalogues for generated native judgments

Preparation keeps the generated prefix across queries. The fair wire search
continues after that prefix, and budget exhaustion retains unknown. Search
certifies derivability in the selected native grammar, not all semantic truth.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates

variable (installed : AuthoredPipeline.Installed)

structure Prepared where
  seeds : List (Tree (NativeLogic.presentation installed.operational.logic installed.signature))
  generatedSeeds : seeds = installed.nativeSeeds

def prepare : installed.Prepared := ⟨installed.nativeSeeds, rfl⟩

namespace Prepared

variable {installed} (prepared : installed.Prepared)

def search (judgment : Judgment installed.symbols) (budget : Nat) : installed.SearchState :=
  NativeLogic.searchWithSeeds installed.operational.logic prepared.seeds judgment budget

def resume (judgment : Judgment installed.symbols) (budget : Nat)
    (state : installed.SearchState) : installed.SearchState :=
  NativeLogic.resumeWithSeeds installed.operational.logic prepared.seeds judgment budget state

theorem search_exact (judgment : Judgment installed.symbols) (budget : Nat) :
    prepared.search judgment budget = installed.search judgment budget := by
  simp only [search, Installed.search, prepared.generatedSeeds]

theorem resume_exact (judgment : Judgment installed.symbols) (budget : Nat)
    (state : installed.SearchState) :
    prepared.resume judgment budget state = installed.resume judgment budget state := by
  simp only [resume, Installed.resume, prepared.generatedSeeds]

theorem resume_add (judgment : Judgment installed.symbols) (first second : Nat) :
    prepared.search judgment (first + second) =
      prepared.resume judgment second (prepared.search judgment first) :=
  NativeLogic.seeded_resume (D := installed.signature) installed.operational.logic
    prepared.seeds judgment first second

theorem stable (judgment : Judgment installed.symbols) (budget extra : Nat)
    (tree : Tree (NativeLogic.presentation installed.operational.logic installed.signature))
    (found : (prepared.search judgment budget).found = some tree) :
    prepared.search judgment (budget + extra) = prepared.search judgment budget :=
  NativeLogic.seeded_stable _ _ _ _ _ _ found

theorem sound (judgment : Judgment installed.symbols) (budget : Nat)
    (tree : Tree (NativeLogic.presentation installed.operational.logic installed.signature))
    (found : (prepared.search judgment budget).found = some tree) :
    installed.operational.logic.permits judgment ∧
      NativeLogic.CertificatePermitted installed.operational.logic (NativeLogic.embed _ tree) ∧
      ∃ derivation : Derivation installed.signature judgment,
        Certificates.Refinement.erase derivation = NativeLogic.embed _ tree :=
  NativeLogic.seeded_sound _ _ _ _ _ found

theorem discovery (judgment : Judgment installed.symbols)
    (certificate : Certificates.Refinement.Certificate installed.signature)
    (selected : NativeLogic.CertificatePermitted installed.operational.logic certificate)
    (accepted : Certificates.Refinement.check certificate judgment = true) :
    ∃ found, (prepared.search judgment
      (SeededSearch.discoveryBound prepared.seeds.length
        (Tree.wireSize (NativeLogic.restrict installed.operational.logic certificate selected)))).found = some found := by
  rw [prepared.search_exact, prepared.generatedSeeds]
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
  simp [query, accepted, search, NativeLogic.searchWithSeeds,
    SeededSearch.search, SeededSearch.run, Search.initial]

end Prepared

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed
