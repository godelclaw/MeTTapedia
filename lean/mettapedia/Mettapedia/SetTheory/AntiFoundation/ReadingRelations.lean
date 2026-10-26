import Mettapedia.SetTheory.AntiFoundation.ReadingFixedPoints

/-!
# The child-class step on every relation

On an arbitrary relation the same step has least fixed point the pairs of nodes that are
bisimilar and accessible along children. Every reading agrees with that relation on
accessible nodes. A graph whose child relation is well-founded has one reading.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.AntiFoundation

open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

variable {α : Type u}

/-- Bisimilarity of nodes from which every child-chain is finite. -/
def accessibleBisimilar (edge : Edge α) (a b : α) : Prop :=
  Acc (flip edge) a ∧ Acc (flip edge) b ∧ Bisimilar edge edge a b

theorem relStep_gfp_eq_bisimilar (edge : Edge α) :
    (relStep edge).gfp = Bisimilar edge edge := by
  apply le_antisymm
  · have bisimulation : IsBisimulation edge edge (relStep edge).gfp := by
      intro a b related
      rw [← (relStep edge).map_gfp] at related
      exact related
    exact fun _ _ related => bisimulation.bisimilar related
  · exact (relStep edge).le_gfp isBisimulation_bisimilar

theorem relStep_accessible_le (edge : Edge α) :
    relStep edge (accessibleBisimilar edge) ≤ accessibleBisimilar edge := by
  intro a b hab
  refine ⟨?_, ?_, ?_⟩
  · refine Acc.intro a fun c hc => ?_
    obtain ⟨_, _, hT⟩ := hab.1 c hc
    exact hT.1
  · refine Acc.intro b fun c hc => ?_
    obtain ⟨_, _, hT⟩ := hab.2 c hc
    exact hT.2.1
  · have hsc : SameChildren edge (Bisimilar edge edge) a b :=
      sameChildren_mono (fun _ _ h => h.2.2) hab
    have fixed : relStep edge (Bisimilar edge edge) = Bisimilar edge edge := by
      rw [← relStep_gfp_eq_bisimilar, (relStep edge).map_gfp]
    change relStep edge (Bisimilar edge edge) a b at hsc
    rwa [fixed] at hsc

/-- A reading, seen as a relation, is a fixed point of the relation step. -/
theorem relStep_coe_of_fixed (edge : Edge α) {R : Setoid α} (hR : step edge R = R) :
    relStep edge (⇑R) = ⇑R := by
  exact congrArg (fun S : Setoid α => (⇑S : α → α → Prop)) hR

theorem accessibleBisimilar_le_of_preFixed (edge : Edge α) {S : α → α → Prop}
    (hS : relStep edge S ≤ S) {a b : α} (h : accessibleBisimilar edge a b) : S a b := by
  have key : ∀ a, Acc (flip edge) a → ∀ b, Acc (flip edge) b →
      Bisimilar edge edge a b → S a b := by
    intro a ha
    induction ha with
    | intro a _ ih =>
      intro b hb hab
      apply hS
      constructor
      · intro a' ha'
        obtain ⟨b', hb', hab'⟩ := hab.exists_child_left ha'
        exact ⟨b', hb', ih a' ha' b' (hb.inv hb') hab'⟩
      · intro b' hb'
        obtain ⟨a', ha', hab'⟩ := hab.exists_child_right hb'
        exact ⟨a', ha', ih a' ha' b' (hb.inv hb') hab'⟩
  exact key a h.1 b h.2.1 h.2.2

theorem relStep_lfp_eq_accessibleBisimilar (edge : Edge α) :
    (relStep edge).lfp = accessibleBisimilar edge := by
  apply le_antisymm
  · exact (relStep edge).lfp_le (relStep_accessible_le edge)
  · apply OrderHom.le_lfp
    intro S hS _ _ h
    exact accessibleBisimilar_le_of_preFixed edge hS h

theorem reading_agrees_accessible (edge : Edge α) (R : Setoid α) (hR : step edge R = R)
    {a b : α} (ha : Acc (flip edge) a) (hb : Acc (flip edge) b) :
    R a b ↔ (relStep edge).lfp a b := by
  rw [relStep_lfp_eq_accessibleBisimilar]
  exact ⟨fun hab => ⟨ha, hb,
    ((le_step_iff_isBisimulation edge R).mp hR.symm.le).bisimilar hab⟩,
    accessibleBisimilar_le_of_preFixed edge (relStep_coe_of_fixed edge hR).le⟩

theorem unique_reading_of_wellFounded (edge : Edge α) (hwf : WellFounded (flip edge)) :
    ∃! R : Setoid α, step edge R = R := by
  have greatest : step edge (bisimilarSetoid edge) = bisimilarSetoid edge := by
    rw [← gfp_eq_bisimilar]; exact (step edge).isFixedPt_gfp
  refine ⟨bisimilarSetoid edge, greatest, ?_⟩
  intro R hR
  ext a b
  exact (reading_agrees_accessible edge R hR (hwf.apply a) (hwf.apply b)).trans
    (reading_agrees_accessible edge _ greatest (hwf.apply a) (hwf.apply b)).symm

end Mettapedia.SetTheory.AntiFoundation
