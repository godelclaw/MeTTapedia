import Mettapedia.Logic.WorldModel.Indexed.SourceExample
import Mettapedia.Logic.WorldModel.Indexed.Quantifiers

/-!
# Quantifiers on the source worlds

For two worlds of sources, the square of inclusions through their intersection
and their union is a weak pullback of questions (`interUnion_weakPullback`), so
existential quantification commutes with restriction around it
(`beckChevalley_interUnion`).
-/

set_option autoImplicit false
open CategoryTheory Opposite

namespace Mettapedia.Logic.WorldModel.Indexed.Sources

variable {Src : Type} [DecidableEq Src]

/-- The intersection–union square of two source worlds has a weak pullback of
questions. -/
theorem interUnion_weakPullback (W V : Finset Src) :
    Quantifiers.WeakPullback
      ((questions (Src := Src)).map (homOfLE (Finset.inter_subset_left : W ∩ V ⊆ W)))
      ((questions (Src := Src)).map (homOfLE (Finset.inter_subset_right : W ∩ V ⊆ V)))
      ((questions (Src := Src)).map (homOfLE (Finset.subset_union_left : W ⊆ W ∪ V)))
      ((questions (Src := Src)).map (homOfLE (Finset.subset_union_right : V ⊆ W ∪ V))) := by
  intro c b h
  change Question.widen _ c = Question.widen _ b at h
  cases c with
  | aggregate s =>
      cases b with
      | aggregate t =>
          cases h
          exact ⟨.aggregate s, rfl, rfl⟩
      | perSource _ _ _ => cases h
  | perSource a ha s =>
      cases b with
      | aggregate _ => cases h
      | perSource a' ha' s' =>
          simp only [Question.widen, Question.perSource.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨.perSource a (Finset.mem_inter.2 ⟨ha, ha'⟩) s, rfl, rfl⟩

/-- **Beck–Chevalley on the source worlds.** For counts with joins, restricting
an existential image from `V` to `W ∪ V` and back to `W` is the existential
image along the intersection. -/
theorem beckChevalley_interUnion {L : Type} [CompleteLattice L] (W V : Finset Src)
    (p : Question V → L) :
    Quantifiers.existsAlong ((questions (Src := Src)).map (homOfLE Finset.subset_union_right)) p ∘
        (questions (Src := Src)).map (homOfLE (Finset.subset_union_left : W ⊆ W ∪ V)) =
      Quantifiers.existsAlong ((questions (Src := Src)).map (homOfLE Finset.inter_subset_left))
        (p ∘ (questions (Src := Src)).map (homOfLE (Finset.inter_subset_right : W ∩ V ⊆ V))) :=
  Quantifiers.beckChevalley_exists_doctrine questions (Subsingleton.elim _ _)
    (interUnion_weakPullback W V) p

end Mettapedia.Logic.WorldModel.Indexed.Sources
