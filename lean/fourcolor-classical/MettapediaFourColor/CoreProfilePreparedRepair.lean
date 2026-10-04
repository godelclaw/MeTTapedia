import MettapediaFourColor.CoreProfileSwitchObstruction

/-! # A component-preserving preparation repairs the two concrete colourings

The second initial colouring has a 1/3-component on vertices 4, 5 and 6.
Switching it yields the first initial colouring. Composing that physical
step with the successful 0/3 switch gives an actual reconstruction history.
The core-list profile agrees before and after preparation, even though the
next rooted operation behaves differently.
-/

namespace FourColor.CoreProfilePreparedRepair

open SimpleGraph CoreProfileSwitchGeometry CoreProfileSwitchObstruction
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def vertices : Set (Fin 11) := {v | v = 4 ∨ v = 5 ∨ v = 6}
instance (v : Fin 11) : Decidable (v ∈ vertices) :=
  inferInstanceAs (Decidable (v = 4 ∨ v = 5 ∨ v = 6))

theorem active : (4 : Fin 11) ∈ (initial true).bicoloredSet 1 3 := Or.inl rfl

def component : ((initial true).bicoloredSubgraph 1 3).ConnectedComponent :=
  ((initial true).bicoloredSubgraph 1 3).connectedComponentMk ⟨4, active⟩

theorem actual_component : (initial true).kempeComponentSet 1 3 component = vertices := by
  apply Set.Subset.antisymm
  · apply (initial true).kempeComponentSet_subset_of_closed active (Or.inl rfl)
    have closed : ∀ u v, u ∈ vertices → exterior.Adj u v →
        (word true v = 1 ∨ word true v = 3) → v ∈ vertices := by decide +kernel
    exact closed
  · intro v hv
    have h4 : (4 : Fin 11) ∈ (initial true).kempeComponentSet 1 3 component :=
      (initial true).mem_kempeComponentSet_self active
    have h5 : (5 : Fin 11) ∈ (initial true).kempeComponentSet 1 3 component :=
      (initial true).mem_kempeComponentSet_of_adj h4 (by decide +kernel) (Or.inr rfl)
    rcases hv with rfl | rfl | rfl
    · exact h4
    · exact h5
    · exact (initial true).mem_kempeComponentSet_of_adj h5 (by decide +kernel) (Or.inl rfl)

theorem prepared : (initial true).swapOnKempeComponent 1 3 component = initial false := by
  have finite : ∀ v,
      (if v ∈ vertices then Equiv.swap (1 : Palette) 3 (word true v)
       else word true v) = word false v := by decide +kernel
  apply DFunLike.ext
  intro v
  by_cases hv : v ∈ vertices
  · have hm : v ∈ (initial true).kempeComponentSet 1 3 component := by
      rw [actual_component]; exact hv
    rw [Coloring.swapOnKempeComponent_apply_of_mem _ hm]
    exact (ite_eq_left hv).symm.trans (finite v)
  · have hm : v ∉ (initial true).kempeComponentSet 1 3 component := by
      rw [actual_component]; exact hv
    rw [Coloring.swapOnKempeComponent_apply_of_not_mem _ hm]
    exact (ite_eq_right hv).symm.trans (finite v)

noncomputable def preparationStep : Step (initial true) (initial false) :=
  prepared ▸ Step.switch (initial true) 1 3 component

/-- One physical step for the first input, two for the second. These are
explicit routes retaining each selected component, with no search on reuse. -/
noncomputable def history (b : Bool) : History (initial b) (switched false) :=
  let last : History (initial false) (switched false) :=
    .cons (.switch (initial false) 0 3 (CoreProfileSwitchObstruction.component false)) (.refl _)
  match b with
  | false => last
  | true => .cons preparationStep last

theorem repaired_boundary (j : Fin 11) : repaired (j.castAdd 7) = switched false j := by
  rw [switched_word]
  have fixed : ∀ j : Fin 11, repaired (j.castAdd 7) = afterWord false j := by decide +kernel
  exact fixed j

/-- Both initial exterior colourings now have a retained physical route to
an exterior which reconstructs the same genuine ambient colouring. -/
theorem reconstruction (b : Bool) :
    Nonempty (History (initial b) (switched false)) ∧
    ∃ K : graph.Coloring Palette, ∀ j : Fin 11, K (j.castAdd 7) = switched false j :=
  ⟨⟨history b⟩, repaired, repaired_boundary⟩

end FourColor.CoreProfilePreparedRepair
