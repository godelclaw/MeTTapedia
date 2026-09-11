import Mettapedia.GraphTheory.FourColor.BoundarySmallCutProfile
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Low-cut signatures preserve connectedness and bridge-freeness

A multigraph is connected and bridgeless exactly when it has no
nontrivial zero- or one-edge cut. Combine this path/cut correspondence
with the finite boundary-profile composition law. The conclusion applies
to arbitrary multigraph pieces, not just connected or port-visible ones.
-/

namespace Mettapedia.GraphTheory.FourColor.SmallCutConnectedBridgeless

open GoertzelV24BoundaryEssentialGluing
open GoertzelV24BoundaryEssentialGluing.Multigraph BoundarySmallCutProfile

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} (G : Multigraph V E)

theorem constant_on_path (s : V → Bool) (avoid : E → Prop)
    (hedge : ∀ e, ¬ avoid e → s (G.fst e) = s (G.snd e)) {u v : V}
    (h : Relation.ReflTransGen (G.StepAvoiding avoid) u v) : s u = s v := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨e, he, hd⟩ := hs
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ih.trans (hedge e he)
    · exact ih.trans (hedge e he).symm

variable [Fintype E]

theorem cutSize_zero (s : V → Bool) (h : ∀ e, s (G.fst e) = s (G.snd e)) :
    cutSize G s = 0 := by simp [cutSize, h]

theorem cutSize_le_one_of_unique (s : V → Bool) (e : E)
    (h : ∀ f, f ≠ e → s (G.fst f) = s (G.snd f)) : cutSize G s ≤ 1 := by
  classical
  have hc : cutSize G s = if s (G.fst e) = s (G.snd e) then 0 else 1 := by
    apply Finset.sum_eq_single e
    · intro f _ hfe; simp only [h f hfe, if_true]
    · simp
  rw [hc]
  split <;> omega

theorem unique_of_small_cut (s : V → Bool) (h : cutSize G s ≤ 1) (e : E)
    (he : s (G.fst e) ≠ s (G.snd e)) (f : E) (hfe : f ≠ e) :
    s (G.fst f) = s (G.snd f) := by
  by_contra hf
  have hh := Finset.add_le_sum (s := Finset.univ)
    (f := fun x => if s (G.fst x) = s (G.snd x) then 0 else (1 : Nat))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ e) (Finset.mem_univ f) hfe.symm
  simp only [if_neg he, if_neg hf] at hh
  change 1 + 1 ≤ cutSize G s at hh
  omega

theorem connected_of_no_small_cut (h : ¬ HasSmallCut G) : G.Connected := by
  intro u v
  by_contra huv
  let s : V → Bool := fun w => decide (G.Reach u w)
  apply h
  refine ⟨s, ⟨u, ?_⟩, ⟨v, ?_⟩, ?_⟩
  · simp only [s, decide_eq_true_eq]; exact .refl
  · simp only [s, decide_eq_false_iff_not]; exact huv
  · have hc : ∀ e, s (G.fst e) = s (G.snd e) := by
      intro e
      have he : G.Reach u (G.fst e) ↔ G.Reach u (G.snd e) :=
        ⟨fun p => p.tail ⟨e, not_false, .inl ⟨rfl, rfl⟩⟩,
          fun p => p.tail ⟨e, not_false, .inr ⟨rfl, rfl⟩⟩⟩
      change decide (G.Reach u (G.fst e)) = decide (G.Reach u (G.snd e))
      simp only [propext he]
    rw [cutSize_zero G s hc]
    omega

theorem bridgeless_of_no_small_cut (h : ¬ HasSmallCut G) : G.Bridgeless := by
  intro e he
  let s : V → Bool := fun w => decide (G.ReachAvoiding e (G.fst e) w)
  apply h
  refine ⟨s, ⟨G.fst e, ?_⟩, ⟨G.snd e, ?_⟩, cutSize_le_one_of_unique G s e ?_⟩
  · simp only [s, decide_eq_true_eq]; exact .refl
  · simp only [s, decide_eq_false_iff_not]; exact he
  · intro f hfe
    have hf : G.ReachAvoiding e (G.fst e) (G.fst f) ↔
        G.ReachAvoiding e (G.fst e) (G.snd f) :=
      ⟨fun p => p.tail ⟨f, hfe, .inl ⟨rfl, rfl⟩⟩,
        fun p => p.tail ⟨f, hfe, .inr ⟨rfl, rfl⟩⟩⟩
    change decide (G.ReachAvoiding e (G.fst e) (G.fst f)) =
      decide (G.ReachAvoiding e (G.fst e) (G.snd f))
    simp only [propext hf]

theorem no_small_cut_of_connected_bridgeless (hc : G.Connected) (hb : G.Bridgeless) :
    ¬ HasSmallCut G := by
  rintro ⟨s, ⟨u, hu⟩, ⟨v, hv⟩, hsize⟩
  have hx : ∃ e, s (G.fst e) ≠ s (G.snd e) := by
    by_contra! he
    have hp := constant_on_path G s (fun _ => False) (fun e _ => he e) (hc u v)
    simp only [hu, hv, Bool.true_eq_false] at hp
  obtain ⟨e, he⟩ := hx
  have hp : G.ReachAvoiding e (G.fst e) (G.snd e) := not_not.mp (hb e)
  exact he (constant_on_path G s (· = e) (unique_of_small_cut G s hsize e he) hp)

/-- The empty multigraph obeys the same reflexive connectedness convention
as the underlying generic multigraph API. No vertices are postulated. -/
theorem no_small_cut_iff : ¬ HasSmallCut G ↔ G.Connected ∧ G.Bridgeless :=
  ⟨fun h => ⟨connected_of_no_small_cut G h, bridgeless_of_no_small_cut G h⟩,
    fun h => no_small_cut_of_connected_bridgeless G h.1 h.2⟩

variable {W F W' F' P : Type*} [Fintype F] [Fintype F'] [Fintype P]
  (K : Multigraph W F) (K' : Multigraph W' F')
  (pG : P → V) (pK : P → W) (pK' : P → W')

/-- The low-cut boundary profile is a context congruence for the two
graph conditions, without any restrictions on the exterior. -/
theorem replacement_connected_bridgeless (h : profile K pK = profile K' pK') :
    ((glue G K pG pK).Connected ∧ (glue G K pG pK).Bridgeless) ↔
      ((glue G K' pG pK').Connected ∧ (glue G K' pG pK').Bridgeless) := by
  rw [← no_small_cut_iff, ← no_small_cut_iff]
  exact not_congr (replacement_hasSmallCut G K pG pK K' pK' h)

end
end Mettapedia.GraphTheory.FourColor.SmallCutConnectedBridgeless
