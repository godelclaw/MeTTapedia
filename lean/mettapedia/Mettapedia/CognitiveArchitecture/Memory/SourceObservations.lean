import Mettapedia.CognitiveArchitecture.Memory.EventSourcedMemory
import Mathlib.Data.Finset.Image

/-!
# Source observations and their interpretations

Delivery identity, source identity and interpretation identity serve different
purposes. A source key must include its origin and revision; equal text is not
an identity rule. Different interpretations of one source are retained, while
the source support contains that observation only once. Distinct source keys
are not a proof of statistical independence.
-/

namespace Mettapedia.CognitiveArchitecture.Memory.SourceObservations

variable {Source Interpretation : Type*} [DecidableEq Source] [DecidableEq Interpretation]

abbrev Observations (Source Interpretation : Type*) := Finset (Source × Interpretation)

def observe (s : Observations Source Interpretation) (source : Source)
    (interpretation : Interpretation) : Observations Source Interpretation :=
  insert (source, interpretation) s

def support (s : Observations Source Interpretation) : Finset Source := s.image Prod.fst

theorem observe_idempotent (s : Observations Source Interpretation) (source : Source)
    (interpretation : Interpretation) :
    observe (observe s source interpretation) source interpretation = observe s source interpretation := by
  simp [observe]

theorem support_observe (s : Observations Source Interpretation) (source : Source)
    (interpretation : Interpretation) :
    support (observe s source interpretation) = insert source (support s) := by
  simp [support, observe]

theorem another_interpretation_preserves_source_support
    (s : Observations Source Interpretation) (source : Source) (a b : Interpretation) :
    support (observe (observe s source a) source b) = support (observe s source a) := by
  simp [support_observe]

theorem interpretations_remain_available
    (s : Observations Source Interpretation) (source : Source) (a b : Interpretation) :
    (source, a) ∈ observe (observe s source a) source b ∧
      (source, b) ∈ observe (observe s source a) source b := by
  simp [observe]

theorem two_interpretations_are_one_source :
    let s : Observations Nat Nat := observe (observe ∅ 7 1) 7 2
    s.card = 2 ∧ (support s).card = 1 := by decide

/-- With fresh storage IDs, operation idempotence alone cannot identify a
re-observation of the same source. Both records survive. -/
theorem fresh_delivery_ids_can_duplicate_content :
    let first : EventSourcedMemory.Op Nat Nat := ⟨0, .add 0 7⟩
    let second : EventSourcedMemory.Op Nat Nat := ⟨1, .add 1 7⟩
    let s := EventSourcedMemory.apply
      (EventSourcedMemory.apply EventSourcedMemory.Store.empty first) second
    EventSourcedMemory.active s 0 = some 7 ∧ EventSourcedMemory.active s 1 = some 7 := by
  decide

end Mettapedia.CognitiveArchitecture.Memory.SourceObservations
