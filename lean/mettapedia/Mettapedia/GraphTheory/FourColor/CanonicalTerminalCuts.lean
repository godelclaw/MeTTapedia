import Mettapedia.GraphTheory.FourColor.GoertzelV24MeshIsoperimetry
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Canonical minimum cuts for advancing terminals

Minimize the complete edge boundary among vertex sides containing `A` and
avoiding `B`, then minimize the side cardinality. Such a side exists whenever
the finite terminal sets are disjoint. Submodularity makes it the unique
inclusion-smallest minimum cut. These canonical sides nest when sources grow
and sinks shrink; a terminal passing from sink to source forces strictness.

This constructs the optimum cuts, rather than assuming a cut supplier. It
does not assert a uniform upper bound on their widths, connectivity, cyclic
order, or a long target-forced chain. Those are separate geometric facts.
-/

namespace Mettapedia.GraphTheory.FourColor.CanonicalTerminalCuts

open GoertzelV24BoundaryEssentialGluing GoertzelV24MeshIsoperimetry

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] [DecidableEq E] in
/-- Complete cut cardinality is submodular. -/
theorem boundary_card_submodular (g : Multigraph V E) (S T : Finset V) :
    (boundaryEdges g (S ∩ T)).card + (boundaryEdges g (S ∪ T)).card ≤
      (boundaryEdges g S).card + (boundaryEdges g T).card := by
  classical
  simp only [boundaryEdges, Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  by_cases h₁ : g.fst e ∈ S <;> by_cases h₂ : g.snd e ∈ S <;>
    by_cases h₃ : g.fst e ∈ T <;> by_cases h₄ : g.snd e ∈ T <;>
    simp [IsBoundaryEdge, h₁, h₂, h₃, h₄]

def Feasible (A B S : Finset V) : Prop := A ⊆ S ∧ Disjoint S B

/-- Minimum complete width, with minimum cardinality breaking ties. -/
structure IsCanonical (g : Multigraph V E) (A B S : Finset V) : Prop where
  feasible : Feasible A B S
  width_min : ∀ T, Feasible A B T → (boundaryEdges g S).card ≤ (boundaryEdges g T).card
  card_min : ∀ T, Feasible A B T → (boundaryEdges g T).card = (boundaryEdges g S).card →
    S.card ≤ T.card

omit [DecidableEq E] in
theorem exists_canonical (g : Multigraph V E) (A B : Finset V) (hAB : Disjoint A B) :
    ∃ S, IsCanonical g A B S := by
  classical
  let candidates : Finset (Finset V) := Finset.univ.filter (Feasible A B)
  let N := Fintype.card V
  let cost := fun S : Finset V => (boundaryEdges g S).card * (N + 1) + S.card
  have hmem : A ∈ candidates := by simp [candidates, Feasible, hAB]
  obtain ⟨S, hS, hmin⟩ := candidates.exists_min_image cost ⟨A, hmem⟩
  have hf : Feasible A B S := (Finset.mem_filter.mp hS).2
  refine ⟨S, hf, ?_, ?_⟩
  · intro T hT
    have hcost := hmin T (by simp [candidates, hT])
    have hcard : T.card ≤ N := Finset.card_le_univ T
    dsimp [cost] at hcost
    by_contra h
    have hwidth : (boundaryEdges g T).card + 1 ≤ (boundaryEdges g S).card := by omega
    have hmul := Nat.mul_le_mul_right (N + 1) hwidth
    nlinarith
  · intro T hT hwidth
    have hcost := hmin T (by simp [candidates, hT])
    dsimp [cost] at hcost
    rw [hwidth] at hcost
    omega

/-- Canonical cuts are monotone even though arbitrary optimal cuts can cross. -/
theorem IsCanonical.mono {g : Multigraph V E} {A B A' B' S T : Finset V}
    (hS : IsCanonical g A B S) (hT : IsCanonical g A' B' T)
    (hA : A ⊆ A') (hB : B' ⊆ B) : S ⊆ T := by
  have hi : Feasible A B (S ∩ T) := by
    refine ⟨?_, hS.feasible.2.mono_left Finset.inter_subset_left⟩
    intro v hv
    exact Finset.mem_inter.mpr ⟨hS.feasible.1 hv, hT.feasible.1 (hA hv)⟩
  have hu : Feasible A' B' (S ∪ T) := by
    refine ⟨fun v hv => Finset.mem_union_right S (hT.feasible.1 hv), ?_⟩
    exact Finset.disjoint_union_left.mpr ⟨hS.feasible.2.mono_right hB, hT.feasible.2⟩
  have hsi := hS.width_min _ hi
  have htu := hT.width_min _ hu
  have hsub := boundary_card_submodular g S T
  have heq : (boundaryEdges g (S ∩ T)).card = (boundaryEdges g S).card := by omega
  have hcard := hS.card_min _ hi heq
  have heqSet : S ∩ T = S := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard
  exact Finset.inter_eq_left.mp heqSet

theorem IsCanonical.unique {g : Multigraph V E} {A B S T : Finset V}
    (hS : IsCanonical g A B S) (hT : IsCanonical g A B T) : S = T :=
  Finset.Subset.antisymm (hS.mono hT (fun _ h => h) (fun _ h => h))
    (hT.mono hS (fun _ h => h) (fun _ h => h))

/-- Choose an actual canonical cut using finite minimization. -/
noncomputable def canonical (g : Multigraph V E) (A B : Finset V) (hAB : Disjoint A B) : Finset V :=
  (exists_canonical g A B hAB).choose

theorem canonical_spec (g : Multigraph V E) (A B : Finset V) (hAB : Disjoint A B) :
    IsCanonical g A B (canonical g A B hAB) :=
  (exists_canonical g A B hAB).choose_spec

theorem canonical_mono (g : Multigraph V E) {A B A' B' : Finset V}
    (hAB : Disjoint A B) (hAB' : Disjoint A' B') (hA : A ⊆ A') (hB : B' ⊆ B) :
    canonical g A B hAB ⊆ canonical g A' B' hAB' :=
  (canonical_spec g A B hAB).mono (canonical_spec g A' B' hAB') hA hB

/-- Terminal movement supplies strict progress, independently of width. -/
theorem canonical_ssubset (g : Multigraph V E) {A B A' B' : Finset V}
    (hAB : Disjoint A B) (hAB' : Disjoint A' B') (hA : A ⊆ A') (hB : B' ⊆ B)
    (hmove : ∃ v, v ∈ B ∧ v ∈ A') :
    canonical g A B hAB ⊂ canonical g A' B' hAB' := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨canonical_mono g hAB hAB' hA hB, ?_⟩
  obtain ⟨v, hvB, hvA⟩ := hmove
  intro heq
  have hv := (canonical_spec g A' B' hAB').feasible.1 hvA
  rw [← heq] at hv
  exact Finset.disjoint_left.mp (canonical_spec g A B hAB).feasible.2 hv hvB

omit [Fintype V] in
/-- Edge-disjoint terminal paths certify a lower bound for EVERY feasible cut. -/
theorem paths_le_boundary (g : Multigraph V E) {ι : Type*} [Fintype ι]
    (paths : ι → MeshPath g) (A B S : Finset V)
    (hin : ∀ i, ∃ t, (paths i).vert t ∈ A)
    (hout : ∀ i, ∃ t, (paths i).vert t ∈ B)
    (hdisjoint : ∀ i j, i ≠ j → ∀ t u, (paths i).edge t ≠ (paths j).edge u)
    (hS : Feasible A B S) : Fintype.card ι ≤ (boundaryEdges g S).card := by
  classical
  have hex : ∀ i, ∃ e : {e // e ∈ boundaryEdges g S}, ∃ t, (paths i).edge t = e := by
    intro i
    obtain ⟨a, ha⟩ := hin i
    obtain ⟨b, hb⟩ := hout i
    have hbS : (paths i).vert b ∉ S := fun h => Finset.disjoint_left.mp hS.2 h hb
    obtain ⟨t, ht⟩ := (paths i).exists_boundary_edge S (hS.1 ha) hbS
    exact ⟨⟨(paths i).edge t, by simp [boundaryEdges, ht]⟩, t, rfl⟩
  choose edge idx heq using hex
  have hinj : Function.Injective edge := by
    intro i j hij
    by_contra hne
    exact hdisjoint i j hne (idx i) (idx j) ((heq i).trans ((congrArg Subtype.val hij).trans (heq j).symm))
  simpa using Fintype.card_le_of_injective edge hinj

end Mettapedia.GraphTheory.FourColor.CanonicalTerminalCuts
