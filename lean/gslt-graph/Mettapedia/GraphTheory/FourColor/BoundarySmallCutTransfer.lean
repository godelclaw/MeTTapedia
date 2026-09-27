import Mettapedia.GraphTheory.FourColor.BoundarySmallCutProfile

/-!
# Exact open-to-open small-cut transfer

Sew the middle ports and keep the two outer interfaces. Composing the
realized cut-state sets computes the entire realized profile of the
literal result, not just its final closed acceptance test. Internal
costs are capped at two; this cap commutes with nonnegative addition.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundarySmallCutTransfer

open GoertzelV24BoundaryEssentialGluing BoundarySmallCutProfile

variable {L P R : Type*} [Fintype P]

/-- The finite transition on individual records; no graph is inspected. -/
def composeState (a : State (L ⊕ P)) (b : State (P ⊕ R)) : State (L ⊕ R) where
  boundary := Sum.elim (fun l => a.boundary (.inl l)) (fun r => b.boundary (.inr r))
  selected := a.selected || b.selected
  omitted := a.omitted || b.omitted
  cost := ⟨min 2 (a.cost.val + b.cost.val +
    ∑ p, if a.boundary (.inr p) = b.boundary (.inl p) then 0 else 1), by omega⟩

def composeProfile (a : Set (State (L ⊕ P))) (b : Set (State (P ⊕ R))) :
    Set (State (L ⊕ R)) := Set.image2 composeState a b

theorem cap_add (a b c : Nat) :
    min 2 (min 2 a + min 2 b + c) = min 2 (a + b + c) := by omega

theorem composeState_assoc {Q : Type*} [Fintype Q]
    (a : State (L ⊕ P)) (b : State (P ⊕ Q)) (c : State (Q ⊕ R)) :
    composeState (composeState a b) c = composeState a (composeState b c) := by
  unfold composeState
  congr 1
  · exact Bool.or_assoc _ _ _
  · exact Bool.or_assoc _ _ _
  · apply Fin.ext
    change min 2 (min 2 (a.cost.val + b.cost.val +
      ∑ p, if a.boundary (.inr p) = b.boundary (.inl p) then 0 else 1) + c.cost.val +
      ∑ q, if b.boundary (.inr q) = c.boundary (.inl q) then 0 else 1) =
      min 2 (a.cost.val + min 2 (b.cost.val + c.cost.val +
      ∑ q, if b.boundary (.inr q) = c.boundary (.inl q) then 0 else 1) +
      ∑ p, if a.boundary (.inr p) = b.boundary (.inl p) then 0 else 1)
    omega

theorem composeProfile_assoc {Q : Type*} [Fintype Q]
    (a : Set (State (L ⊕ P))) (b : Set (State (P ⊕ Q))) (c : Set (State (Q ⊕ R))) :
    composeProfile (composeProfile a b) c = composeProfile a (composeProfile b c) := by
  ext s
  constructor
  · rintro ⟨ab, ⟨x, hx, y, hy, rfl⟩, z, hz, rfl⟩
    exact ⟨x, hx, composeState y z, ⟨y, hy, z, hz, rfl⟩,
      (composeState_assoc x y z).symm⟩
  · rintro ⟨x, hx, yz, ⟨y, hy, z, hz, rfl⟩, rfl⟩
    exact ⟨composeState x y, ⟨x, hx, y, hy, rfl⟩, z, hz, composeState_assoc x y z⟩

variable {V W E F : Type*} [Fintype E] [Fintype F]
  (H : Multigraph V E) (K : Multigraph W F)
  (lH : L → V) (pH : P → V) (pK : P → W) (rK : R → W)

/-- Remaining port vertices of the actual partially sewn graph. -/
def outsidePorts : L ⊕ R → V ⊕ W := Sum.elim (Sum.inl ∘ lH) (Sum.inr ∘ rK)

theorem state_glue (s : V → Bool) (t : W → Bool) :
    state (glue H K pH pK) (outsidePorts lH rK) (Sum.elim s t) =
      composeState (state H (Sum.elim lH pH) s) (state K (Sum.elim pK rK) t) := by
  classical
  unfold state composeState
  congr 1
  · funext p; cases p <;> rfl
  · simp only [Sum.exists, Sum.elim_inl, Sum.elim_inr, Bool.decide_or]
  · simp only [Sum.exists, Sum.elim_inl, Sum.elim_inr, Bool.decide_or]
  · apply Fin.ext
    dsimp
    rw [cutSize_glue]
    exact (cap_add _ _ _).symm

/-- All output states are realized, and every realized output state is
produced. No connectivity or visibility conditions are needed. -/
theorem profile_glue :
    profile (glue H K pH pK) (outsidePorts lH rK) =
      composeProfile (profile H (Sum.elim lH pH)) (profile K (Sum.elim pK rK)) := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨state H (Sum.elim lH pH) (s ∘ Sum.inl), ⟨_, rfl⟩,
      state K (Sum.elim pK rK) (s ∘ Sum.inr), ⟨_, rfl⟩, ?_⟩
    rw [← state_glue]
    congr 1
    funext v; cases v <;> rfl
  · rintro ⟨a, ⟨s, rfl⟩, b, ⟨t, rfl⟩, rfl⟩
    exact ⟨Sum.elim s t, state_glue H K lH pH pK rK s t⟩

end Mettapedia.GraphTheory.FourColor.BoundarySmallCutTransfer
