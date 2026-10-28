import Mathlib.Data.Set.Lattice
import Mathlib.Data.Real.Basic

/-!
# Composable context views over shared memory identities

Workspace expressions select identities. Their interpretation is independent
of stored evidence and attention balances. Union is set union, rather than an
ordered overlay; exclusions belong to the view in which they are declared.
These contracts do not certify the MeTTa evaluator, persistence, floating point,
or retrieval quality; the native implementation has separate integration tests.
-/

namespace Mettapedia.CognitiveArchitecture.Memory.ContextViews

variable {Id Evidence : Type*}

structure Workspace (Id : Type*) where
  included : Set Id
  excluded : Set Id

def selected (w : Workspace Id) : Set Id := w.included \ w.excluded

def visible (source : Set Id) (w : Workspace Id) : Set Id := source ∩ selected w

def combine (a b : Workspace Id) : Workspace Id :=
  ⟨selected a ∪ selected b, ∅⟩

theorem selected_combine (a b : Workspace Id) :
    selected (combine a b) = selected a ∪ selected b := by
  simp [selected, combine]

theorem combine_idempotent (a : Workspace Id) :
    selected (combine a a) = selected a := by simp [selected_combine]

theorem combine_commutative (a b : Workspace Id) :
    selected (combine a b) = selected (combine b a) := by
  simp only [selected_combine, Set.union_comm]

theorem combine_associative (a b c : Workspace Id) :
    selected (combine (combine a b) c) = selected (combine a (combine b c)) := by
  simp only [selected_combine, Set.union_assoc]

theorem visible_subset_source (source : Set Id) (w : Workspace Id) :
    visible source w ⊆ source := Set.inter_subset_left

theorem excluded_not_visible (source : Set Id) (w : Workspace Id) (i : Id)
    (h : i ∈ w.excluded) : i ∉ visible source w := by
  intro hi
  exact hi.2.2 h

theorem include_monotone (source extra : Set Id) (w : Workspace Id) :
    visible source w ⊆ visible source { w with included := w.included ∪ extra } := by
  intro i hi
  exact ⟨hi.1, Or.inl hi.2.1, hi.2.2⟩

theorem exclude_antitone (source extra : Set Id) (w : Workspace Id) :
    visible source { w with excluded := w.excluded ∪ extra } ⊆ visible source w := by
  intro i hi
  exact ⟨hi.1, hi.2.1, fun h => hi.2.2 (Or.inl h)⟩

theorem visible_combine (source : Set Id) (a b : Workspace Id) :
    visible source (combine a b) = visible source a ∪ visible source b := by
  simp only [visible, selected_combine, Set.inter_union_distrib_left]

structure ContextState (Id Evidence : Type*) where
  source : Id → Option Evidence
  attention : Id → ℝ
  workspace : Workspace Id

def choose (m : ContextState Id Evidence) (w : Workspace Id) : ContextState Id Evidence :=
  { m with workspace := w }

theorem choose_preserves_evidence (m : ContextState Id Evidence) (w : Workspace Id) :
    (choose m w).source = m.source := rfl

theorem choose_preserves_attention (m : ContextState Id Evidence) (w : Workspace Id) :
    (choose m w).attention = m.attention := rfl

theorem restore_workspace (m : ContextState Id Evidence) (w : Workspace Id) :
    choose (choose m w) m.workspace = m := by cases m; rfl

end Mettapedia.CognitiveArchitecture.Memory.ContextViews
