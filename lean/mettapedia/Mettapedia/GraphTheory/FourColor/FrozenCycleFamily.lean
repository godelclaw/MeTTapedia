import Mettapedia.GraphTheory.Kempe.BlockChoices
import Mettapedia.GraphTheory.FourColor.FrozenBoundaryObserver

/-!
# Independently frozen blocks require many physical classes

One proper alternative per separated block generates every Boolean combination
as a genuine full colouring with the same exterior. A protected frozen observer
in each block distinguishes choices along every physical history. Consequently
an exact summary with connected fibres needs at least `2 ^ number of blocks`
states. This does not give a lower bound on symbolic description or proof size:
the construction itself is factored and uniform. It makes no global geometric
supply claim and does not rule out summaries preserving only successful choices.
-/

namespace Mettapedia.GraphTheory.FourColor.FrozenCycleFamily

open SimpleGraph Relation KempePairBlocks KempeBlockChoices

variable {V ι : Type*} {G : SimpleGraph V}

/-- Per-block data: a base colouring, one alternative per separated block,
and one frozen observer per block. No table of joint colourings is supplied. -/
structure Witnesses (G : SimpleGraph V) (S : Set V) (label : V → ι) where
  separated : Separated G S label
  initial : G.Coloring (Fin 4)
  alternative : ι → G.Coloring (Fin 4)
  outside : ∀ i x, x ∉ block S label i → alternative i x = initial x
  observer : ι → AdjacentHiddenObstruction.graph →g G
  palette : ι → Equiv.Perm (Fin 4)
  owned : ∀ i v, observer i v ∈ S → label (observer i v) = i
  kept : ∀ i, AdjacentHiddenObstruction.boundary ⊆ observer i ⁻¹' Sᶜ
  observed : ∀ i v, initial (observer i v) = palette i (AdjacentHiddenObstruction.state 0 v)
  core : ∀ i, observer i 2 ∈ block S label i
  changed : ∀ i, alternative i (observer i 2) ≠ palette i 1

namespace Witnesses

variable {S : Set V} {label : V → ι}

noncomputable def state (w : Witnesses G S label) (bits : ι → Bool) :
    G.Coloring (Fin 4) :=
  combine S label w.separated w.initial w.alternative w.outside bits

theorem same_exterior (w : Witnesses G S label) (bits : ι → Bool) (x : V) (hx : x ∉ S) :
    w.state bits x = w.initial x :=
  combine_exterior S label w.separated w.initial w.alternative w.outside bits x hx

/-- Changing any bit crosses physical classes. All other blocks may make
arbitrary independent choices in both endpoints. -/
theorem no_path [Fintype V] (w : Witnesses G S label) (s t : ι → Bool) (hne : s ≠ t) :
    ¬ ReflTransGen (G.KempeStepAvoiding Sᶜ) (w.state s) (w.state t) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ t i := by
    by_contra! all
    exact hne (funext all)
  have forbid (a b : ι → Bool) (ha : a i = false) (hb : b i = true) :
      ¬ ReflTransGen (G.KempeStepAvoiding Sᶜ) (w.state a) (w.state b) := by
    apply FrozenBoundaryObserver.no_lift_renamed (w.palette i) (w.observer i) Sᶜ
      (w.kept i) (w.state a) (w.state b)
    · intro v
      have inactive : ¬ (w.observer i v ∈ S ∧ a (label (w.observer i v)) = true) := by
        rintro ⟨hs, hbit⟩
        rw [w.owned i v hs, ha] at hbit
        cases hbit
      rw [state, combine_off S label w.separated w.initial w.alternative w.outside a _ inactive]
      exact w.observed i v
    · have active : w.observer i 2 ∈ S ∧ b (label (w.observer i 2)) = true :=
        ⟨(w.core i).1, by rw [(w.core i).2, hb]⟩
      rw [state, combine_on S label w.separated w.initial w.alternative w.outside b _ active,
        (w.core i).2]
      exact w.changed i
  cases hs : s i <;> cases ht : t i
  · exact (hi (hs.trans ht.symm)).elim
  · exact forbid s t hs ht
  · exact fun path => forbid t s ht hs (reflTransGen_kempeStepAvoiding_symm path)
  · exact (hi (hs.trans ht.symm)).elim

/-- Any finite summary that identifies only physically connected full
colourings needs exponentially many states on this family. This does not
require explicitly storing them or prohibit a compact factored representation. -/
theorem summary_card_lower_bound [Fintype V] [Fintype ι] {Q : Type*} [Fintype Q]
    (w : Witnesses G S label) (summary : G.Coloring (Fin 4) → Q)
    (connected : ∀ C D, summary C = summary D →
      ReflTransGen (G.KempeStepAvoiding Sᶜ) C D) :
    2 ^ Fintype.card ι ≤ Fintype.card Q := by
  classical
  have inject : Function.Injective (fun bits => summary (w.state bits)) := by
    intro s t equal
    by_contra different
    exact w.no_path s t different (connected _ _ equal)
  simpa using Fintype.card_le_of_injective _ inject

end Witnesses
end Mettapedia.GraphTheory.FourColor.FrozenCycleFamily
