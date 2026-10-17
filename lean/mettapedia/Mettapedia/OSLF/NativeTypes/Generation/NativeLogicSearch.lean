import Mettapedia.OSLF.NativeTypes.Generation.NativeLogicFragment
import Mettapedia.OSLF.NativeTypes.Certificates.NativeEnumeration
import Mettapedia.OSLF.NativeTypes.Certificates.SeededSearch
import Mettapedia.OSLF.NativeTypes.Certificates.DeferredSeededSearch

/-!
# Fair certificate search within a selected native vocabulary

Rules are selected by the actual feature occurrences in their conclusions.
Every premise certificate is independently selected and checked. The search
enumerates these complete rule payloads with the earned native encoding.
Embedding retains all original ordered native rule occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeLogic

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates

variable {S : Symbols} {D : Signature S}

instance permitsDecidable (fragment : Fragment) (judgment : Judgment S) :
    Decidable (fragment.permits judgment) :=
  decidable_of_iff (fragment.accepts judgment = true) (accepts_exact fragment judgment)

abbrev presentation (fragment : Fragment) (D : Signature S) : Certificates.Presentation where
  Judgment := Judgment S
  Rule := {rule : RuleCode D // fragment.permits rule.conclusion}
  conclusion rule := rule.val.conclusion
  premises rule := rule.val.premises

def embed (fragment : Fragment) : Tree (presentation fragment D) → Certificates.Refinement.Certificate D
  | .node rule children => .node rule.val (fun i => embed fragment (children i))

theorem embed_permitted (fragment : Fragment) (tree : Tree (presentation fragment D)) :
    CertificatePermitted fragment (embed fragment tree) := by
  induction tree with
  | node rule children ih => exact .node rule.val _ rule.property ih

theorem permitted_root (fragment : Fragment) (rule : RuleCode D)
    (children : Fin rule.premises.length → Certificates.Refinement.Certificate D)
    (permitted : CertificatePermitted fragment (.node rule children)) :
    fragment.permits rule.conclusion := by
  cases permitted with
  | node _ _ root _ => exact root

theorem permitted_children (fragment : Fragment) (rule : RuleCode D)
    (children : Fin rule.premises.length → Certificates.Refinement.Certificate D)
    (permitted : CertificatePermitted fragment (.node rule children)) (i : Fin rule.premises.length) :
    CertificatePermitted fragment (children i) := by
  cases permitted with
  | node _ _ _ premises => exact premises i

def restrict (fragment : Fragment) : (tree : Certificates.Refinement.Certificate D) →
    CertificatePermitted fragment tree → Tree (presentation fragment D)
  | .node rule children, permitted =>
      .node ⟨rule, permitted_root fragment rule children permitted⟩
        (fun i => restrict fragment (children i) (permitted_children fragment rule children permitted i))

theorem embed_restrict (fragment : Fragment) (tree : Certificates.Refinement.Certificate D)
    (permitted : CertificatePermitted fragment tree) :
    embed fragment (restrict fragment tree permitted) = tree := by
  induction tree with
  | node rule children ih =>
      simp only [restrict, embed]
      congr 1
      funext i
      exact ih i _

variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]

theorem embed_check (fragment : Fragment) (tree : Tree (presentation fragment D))
    (judgment : Judgment S) :
    tree.check judgment = Certificates.Refinement.check (embed fragment tree) judgment := by
  induction tree generalizing judgment with
  | node rule children ih =>
      simp only [Tree.check, embed, Certificates.Refinement.check, presentation,
        Certificates.Refinement.presentation]
      simp only [ih, Certificates.Refinement.check]

theorem checked_tree_sound (fragment : Fragment) (judgment : Judgment S)
    (tree : Tree (presentation fragment D)) (accepted : tree.check judgment = true) :
    fragment.permits judgment ∧ CertificatePermitted fragment (embed fragment tree) ∧
      ∃ derivation : Derivation D judgment, Certificates.Refinement.erase derivation = embed fragment tree := by
  have checked := (embed_check fragment tree judgment).symm.trans accepted
  have rootPermitted : fragment.permits judgment := by
    cases tree with
    | node rule children =>
        have rootEqual : rule.val.conclusion = judgment := by
          have accepted : (Tree.node rule children).check judgment = true := by
            rw [embed_check]
            exact checked
          have clauses : decide (rule.val.conclusion = judgment) = true ∧
              decide (∀ i, (children i).check (rule.val.premises.get i) = true) = true := by
            simpa only [Tree.check, Bool.and_eq_true] using accepted
          exact of_decide_eq_true clauses.1
        simpa only [← rootEqual] using rule.property
  exact ⟨rootPermitted, embed_permitted fragment tree, (Certificates.Refinement.check_exact _ _).mp checked⟩

variable [Encodable S.TypeSymbol] [Encodable S.TermSymbol] [Encodable S.PredicateSymbol]

def search (fragment : Fragment) (judgment : Judgment S) (budget : Nat) :
    Search.State (presentation fragment D) :=
  Search.search (P := presentation fragment D) judgment budget

theorem search_sound (fragment : Fragment) (judgment : Judgment S) (budget : Nat)
    (tree : Tree (presentation fragment D))
    (found : (search fragment judgment budget).found = some tree) :
    fragment.permits judgment ∧ CertificatePermitted fragment (embed fragment tree) ∧
      ∃ derivation : Derivation D judgment, Certificates.Refinement.erase derivation = embed fragment tree := by
  obtain ⟨derived, erased⟩ := Search.search_sound (P := presentation fragment D) judgment budget tree found
  apply checked_tree_sound fragment judgment tree
  simpa only [erased] using Tree.check_erase derived

theorem discover_permitted (fragment : Fragment) (judgment : Judgment S)
    (tree : Certificates.Refinement.Certificate D) (permitted : CertificatePermitted fragment tree)
    (checked : Certificates.Refinement.check tree judgment = true) :
    ∃ found, (search (D := D) fragment judgment
      (Tree.discoveryBound (Tree.wireSize (restrict fragment tree permitted)))).found = some found := by
  apply Search.discover_within_wire_bound (P := presentation fragment D) judgment (restrict fragment tree permitted)
  rw [embed_check, embed_restrict]
  exact checked

theorem search_resume (fragment : Fragment) (judgment : Judgment S) (first second : Nat) :
    search (D := D) fragment judgment (first + second) =
      Search.run judgment second (search fragment judgment first) :=
  Search.run_add (P := presentation fragment D) judgment first second Search.initial

theorem search_stable (fragment : Fragment) (judgment : Judgment S) (budget extra : Nat)
    (tree : Tree (presentation fragment D))
    (found : (search fragment judgment budget).found = some tree) :
    search (D := D) fragment judgment (budget + extra) = search fragment judgment budget :=
  Search.stable_conclusion (P := presentation fragment D) judgment budget extra tree found

def searchWithSeeds (fragment : Fragment) (seeds : List (Tree (presentation fragment D)))
    (judgment : Judgment S) (budget : Nat) : Search.State (presentation fragment D) :=
  SeededSearch.search seeds judgment budget

def resumeWithSeeds (fragment : Fragment) (seeds : List (Tree (presentation fragment D)))
    (judgment : Judgment S) (budget : Nat) (state : Search.State (presentation fragment D)) :
    Search.State (presentation fragment D) :=
  SeededSearch.run seeds judgment budget state

theorem seeded_sound (fragment : Fragment) (seeds : List (Tree (presentation fragment D)))
    (judgment : Judgment S) (budget : Nat) (tree : Tree (presentation fragment D))
    (found : (searchWithSeeds fragment seeds judgment budget).found = some tree) :
    fragment.permits judgment ∧ CertificatePermitted fragment (embed fragment tree) ∧
      ∃ derivation : Derivation D judgment, Certificates.Refinement.erase derivation = embed fragment tree := by
  obtain ⟨derived, erased⟩ := SeededSearch.search_sound seeds judgment budget tree found
  apply checked_tree_sound fragment judgment tree
  simpa only [erased] using Tree.check_erase derived

theorem seeded_discovery (fragment : Fragment) (seeds : List (Tree (presentation fragment D)))
    (judgment : Judgment S) (tree : Tree (presentation fragment D)) (accepted : tree.check judgment = true) :
    ∃ found, (searchWithSeeds fragment seeds judgment
      (SeededSearch.discoveryBound seeds.length (Tree.wireSize tree))).found = some found :=
  SeededSearch.discover_within_wire_bound seeds judgment tree accepted

theorem seeded_resume (fragment : Fragment) (seeds : List (Tree (presentation fragment D)))
    (judgment : Judgment S) (first second : Nat) :
    searchWithSeeds fragment seeds judgment (first + second) =
      SeededSearch.run seeds judgment second (searchWithSeeds fragment seeds judgment first) :=
  SeededSearch.run_add seeds judgment first second Search.initial

theorem seeded_stable (fragment : Fragment) (seeds : List (Tree (presentation fragment D)))
    (judgment : Judgment S) (budget extra : Nat) (tree : Tree (presentation fragment D))
    (found : (searchWithSeeds fragment seeds judgment budget).found = some tree) :
    searchWithSeeds fragment seeds judgment (budget + extra) = searchWithSeeds fragment seeds judgment budget :=
  SeededSearch.stable_conclusion seeds judgment budget extra tree found

def searchWithDeferred (fragment : Fragment) (factories : DeferredSeededSearch.Prefix (presentation fragment D))
    (judgment : Judgment S) (budget : Nat) : Search.State (presentation fragment D) :=
  DeferredSeededSearch.search factories judgment budget

def resumeWithDeferred (fragment : Fragment) (factories : DeferredSeededSearch.Prefix (presentation fragment D))
    (judgment : Judgment S) (budget : Nat) (state : Search.State (presentation fragment D)) :
    Search.State (presentation fragment D) :=
  DeferredSeededSearch.run factories judgment budget state

theorem deferred_sound (fragment : Fragment) (factories : DeferredSeededSearch.Prefix (presentation fragment D))
    (judgment : Judgment S) (budget : Nat) (tree : Tree (presentation fragment D))
    (found : (searchWithDeferred fragment factories judgment budget).found = some tree) :
    fragment.permits judgment ∧ CertificatePermitted fragment (embed fragment tree) ∧
      ∃ derivation : Derivation D judgment, Certificates.Refinement.erase derivation = embed fragment tree := by
  obtain ⟨derived, erased⟩ := DeferredSeededSearch.search_sound factories judgment budget tree found
  apply checked_tree_sound fragment judgment tree
  simpa only [erased] using Tree.check_erase derived

theorem deferred_discovery (fragment : Fragment) (factories : DeferredSeededSearch.Prefix (presentation fragment D))
    (judgment : Judgment S) (tree : Tree (presentation fragment D)) (accepted : tree.check judgment = true) :
    ∃ found, (searchWithDeferred fragment factories judgment
      (DeferredSeededSearch.discoveryBound factories.length (Tree.wireSize tree))).found = some found :=
  DeferredSeededSearch.discover_within_wire_bound factories judgment tree accepted

theorem deferred_resume (fragment : Fragment) (factories : DeferredSeededSearch.Prefix (presentation fragment D))
    (judgment : Judgment S) (first second : Nat) :
    searchWithDeferred fragment factories judgment (first + second) =
      resumeWithDeferred fragment factories judgment second (searchWithDeferred fragment factories judgment first) :=
  DeferredSeededSearch.run_add factories judgment first second Search.initial

theorem deferred_stable (fragment : Fragment) (factories : DeferredSeededSearch.Prefix (presentation fragment D))
    (judgment : Judgment S) (budget extra : Nat) (tree : Tree (presentation fragment D))
    (found : (searchWithDeferred fragment factories judgment budget).found = some tree) :
    searchWithDeferred fragment factories judgment (budget + extra) = searchWithDeferred fragment factories judgment budget :=
  DeferredSeededSearch.stable_conclusion factories judgment budget extra tree found

end Mettapedia.OSLF.NativeTypes.Generation.NativeLogic
