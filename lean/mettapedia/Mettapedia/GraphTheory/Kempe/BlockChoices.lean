import Mettapedia.GraphTheory.Kempe.CycleAnchors
import Mettapedia.GraphTheory.Kempe.PairBlocks

/-!
# Compatible choices and factored histories for separated hidden blocks

Alternative proper colourings supported in separate blocks combine without
enumerating their product. Blocks may share retained neighbours, whose
colours remain shared observations. After retaining a cycle-breaking set,
the existing local guard factorization and forest reconstruction yield exact
physical history transport, with no bound on block sizes or their number.
-/

namespace SimpleGraph.KempeBlockChoices

open Relation KempePairBlocks

variable {V α ι : Type*} {G : SimpleGraph V}

/-- Choose either the initial or the alternative colouring in each block.
Only one alternative per block is supplied; all combinations are constructed. -/
noncomputable def combine (S : Set V) (label : V → ι)
    (sep : Separated G S label) (C : G.Coloring α) (D : ι → G.Coloring α)
    (outside : ∀ i x, x ∉ block S label i → D i x = C x)
    (bits : ι → Bool) : G.Coloring α := by
  classical
  refine .mk (fun x => if x ∈ S ∧ bits (label x) = true then D (label x) x else C x) ?_
  intro x y hxy
  by_cases hx : x ∈ S ∧ bits (label x) = true
  · by_cases hy : y ∈ S ∧ bits (label y) = true
    · have same := sep x hx.1 y hy.1 hxy
      simpa [hx, hy, same] using (D (label y)).valid hxy
    · have hyBlock : y ∉ block S label (label x) := by
        rintro ⟨hyS, same⟩
        exact hy ⟨hyS, same ▸ hx.2⟩
      simpa [hx, hy, outside (label x) y hyBlock] using (D (label x)).valid hxy
  · by_cases hy : y ∈ S ∧ bits (label y) = true
    · have hxBlock : x ∉ block S label (label y) := by
        rintro ⟨hxS, same⟩
        exact hx ⟨hxS, same ▸ hy.2⟩
      simpa [hx, hy, outside (label y) x hxBlock] using (D (label y)).valid hxy
    · simpa [hx, hy] using C.valid hxy

theorem combine_on (S : Set V) (label : V → ι)
    (sep : Separated G S label) (C : G.Coloring α) (D : ι → G.Coloring α)
    (outside : ∀ i x, x ∉ block S label i → D i x = C x)
    (bits : ι → Bool) (x : V) (active : x ∈ S ∧ bits (label x) = true) :
    combine S label sep C D outside bits x = D (label x) x := by
  classical
  exact ite_eq_left active

theorem combine_off (S : Set V) (label : V → ι)
    (sep : Separated G S label) (C : G.Coloring α) (D : ι → G.Coloring α)
    (outside : ∀ i x, x ∉ block S label i → D i x = C x)
    (bits : ι → Bool) (x : V) (inactive : ¬ (x ∈ S ∧ bits (label x) = true)) :
    combine S label sep C D outside bits x = C x := by
  classical
  exact ite_eq_right inactive

theorem combine_exterior (S : Set V) (label : V → ι)
    (sep : Separated G S label) (C : G.Coloring α) (D : ι → G.Coloring α)
    (outside : ∀ i x, x ∉ block S label i → D i x = C x)
    (bits : ι → Bool) (x : V) (hx : x ∉ S) :
    combine S label sep C D outside bits x = C x := by
  exact combine_off S label sep C D outside bits x (fun h => hx h.1)

/-- Exact factored history transport after retaining cycle-breaking vertices.
Every local guard receives the same retained endpoints and transposition. -/
theorem anchored_history_iff [Fintype V] [DecidableEq α] (S K : Set V)
    (label : V → ι) (sep : Separated G S label)
    (forest : (G.induce (S \ K)).IsAcyclic) (C D : G.Coloring α) :
    ReflTransGen (KempePairBlocks.Step (S \ K) label Sᶜ)
      (C.restrictInduce (S \ K)ᶜ) (D.restrictInduce (S \ K)ᶜ) ↔
      ReflTransGen (G.KempeStepAvoiding Sᶜ) C D := by
  have sep' : Separated G (S \ K) label := fun x hx y hy hxy => sep x hx.1 y hy.1 hxy
  have steps : KempePairBlocks.Step (G := G) (α := α) (S \ K) label Sᶜ =
      KempeGuardedLift.Step (S \ K) Sᶜ :=
    funext fun E => funext fun F => propext (step_iff (S \ K) label sep' Sᶜ E F)
  rw [steps]
  exact KempeCycleAnchors.history_iff S K forest C D

end SimpleGraph.KempeBlockChoices
