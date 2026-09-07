import Mettapedia.GraphTheory.FourColor.MeshRegionOrderChecks
import Mettapedia.GraphTheory.FourColor.RankedRegionComponent
import Mettapedia.GraphTheory.FourColor.FaceRegionHull
import Mettapedia.GraphTheory.FourColor.GoertzelV24MeshIsoperimetry

/-!
# Reordering the repaired cells cannot avoid an intermediate-width cost

The numbered GP(3,0) band has eight cells. Every union of six cells has
filled boundary at least sixteen, although each singleton and the whole
band have filled boundary at most fifteen. Ranked spanning witnesses
identify the complete outside components in the original ambient graph.

The result concerns these eight cell vertex sets and all their orders.
It is not a lower bound on arbitrary branch decompositions. The lab checks
the rotation and face-cell extraction; this module checks the finite graph,
the actual hull operation and its complete edge boundary.
-/

namespace Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction

open SimpleGraph GoertzelV24BoundaryEssentialGluing GoertzelV24MeshIsoperimetry
open MeshRegionOrderData VertexSeparatorBond RankedRegionComponent

set_option maxRecDepth 100000

theorem testBit_foldl_or (xs : List Nat) (a i : Nat) :
    (xs.foldl Nat.lor a).testBit i = (a.testBit i || xs.any (fun x => x.testBit i)) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih, Nat.testBit_or, Bool.or_assoc]

/-- The encoded raw side is precisely the union of the selected cell vertex
sets, not an independently supplied subset of the ambient graph. -/
theorem mem_rawMask_iff (s : Finset (Fin 8)) (v : Fin 180) :
    v ∈ marked (rawMask s) ↔ ∃ i ∈ s, v ∈ marked (cellMasks.getD i.val 0) := by
  change (rawMask s).testBit v.val = true ↔ _
  rw [rawMask, testBit_foldl_or]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, List.mem_ofFn]
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, hx⟩
    by_cases hi : i ∈ s
    · exact ⟨i, hi, by simpa only [marked, Set.mem_setOf_eq, if_pos hi] using hx⟩
    · simp [hi] at hx
  · rintro ⟨i, hi, hv⟩
    exact ⟨cellMasks.getD i.val 0, ⟨i, if_pos hi⟩, hv⟩

theorem case_spec (t : Cases) :
    rawMask (selected t) = raw t ∧ componentCheck t = true ∧
    ((selected t).card = 6 → 16 ≤ (computedBoundary t).card) ∧
    ((selected t).card = 1 → (computedBoundary t).card ≤ 15) :=
  of_decide_eq_true (cases_checked t)

theorem raw_eq (t : Cases) : rawMask (selected t) = raw t := (case_spec t).1
theorem components_checked (t : Cases) : componentCheck t = true := (case_spec t).2.1

theorem component_exact (t : Cases) :
    flood graph (marked (raw t))ᶜ {anchor} = marked (component t) := by
  have hc := components_checked t
  unfold componentCheck at hc
  have h := of_decide_eq_true hc
  rcases h with ⟨hb, hdis, hp, he⟩
  apply flood_eq_of_rank graph hb hdis (parent t) (rank t) ?_ ?_
  · intro v hv hne
    obtain ⟨hpc, hvp, hr⟩ := hp v hv hne
    refine ⟨hpc, ⟨parentEdge t v, ?_⟩, hr⟩
    by_cases hfst : ambient.fst (parentEdge t v) = v
    · right
      exact ⟨hfst, by simp only [parent, hfst, if_true]⟩
    · left
      exact ⟨by simp only [parent, hfst, if_false], hvp.resolve_left hfst⟩
  · rintro v hv w ⟨e, h | h⟩ hw
    · rcases h with ⟨rfl, rfl⟩
      exact (he e).1 hv hw
    · rcases h with ⟨rfl, rfl⟩
      exact (he e).2 hv hw

noncomputable def physicalBoundary (s : Finset (Fin 8)) : Finset (Fin 270) :=
  boundaryEdges ambient (FaceRegionHull.filled (G := graph) (marked (rawMask s)) anchor).toFinset

theorem boundary_exact (t : Cases) : physicalBoundary (selected t) = computedBoundary t := by
  classical
  have hside : FaceRegionHull.filled (G := graph) (marked (rawMask (selected t))) anchor =
      (marked (component t))ᶜ := by
    rw [raw_eq]
    exact congrArg Set.compl (component_exact t)
  have hfin : (marked (component t))ᶜ.toFinset =
      Finset.univ.filter (fun v => (component t).testBit v.val = false) := by
    ext v
    simp [marked]
  unfold physicalBoundary
  rw [hside, hfin]
  exact (computedBoundary_eq t).symm

theorem six_covered : ∀ s : Finset (Fin 8), s.card = 6 → ∃ t : Cases, selected t = s := by
  have cover : (Finset.univ : Finset (Fin 8)).powersetCard 6 ⊆
      (Finset.univ : Finset Cases).image selected := by decide +kernel
  intro s hs
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp
    (cover (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, hs⟩))
  exact ⟨t, ht⟩

theorem six_checked (t : Cases) : (selected t).card = 6 → 16 ≤ (computedBoundary t).card :=
  (case_spec t).2.2.1

/-- Every six-cell choice incurs the intermediate cost, regardless of order
or whether that choice is face-connected. -/
theorem six_cells_width (s : Finset (Fin 8)) (hs : s.card = 6) :
    16 ≤ (physicalBoundary s).card := by
  obtain ⟨t, rfl⟩ := six_covered s hs
  rw [boundary_exact]
  exact six_checked t hs

theorem singleton_covered : ∀ i : Fin 8, ∃ t : Cases, selected t = {i} := by decide +kernel
theorem singletons_checked (t : Cases) : (selected t).card = 1 → (computedBoundary t).card ≤ 15 :=
  (case_spec t).2.2.2
theorem full_selected : selected fullIndex = Finset.univ := by decide +kernel
theorem full_checked : (computedBoundary fullIndex).card = 15 := by decide +kernel

theorem local_and_final_width :
    (∀ i : Fin 8, (physicalBoundary {i}).card ≤ 15) ∧
      (physicalBoundary Finset.univ).card = 15 := by
  constructor
  · intro i
    obtain ⟨t, ht⟩ := singleton_covered i
    rw [← ht, boundary_exact]
    exact singletons_checked t (by rw [ht]; simp)
  · rw [← full_selected, boundary_exact]
    exact full_checked

/-- No permutation of these eight cells keeps all filled prefixes at width
fifteen: its six-cell prefix already crosses at least sixteen edges. -/
theorem every_order_exceeds_fifteen (order : Fin 8 ≃ Fin 8) :
    15 < (physicalBoundary ((Finset.univ.filter fun i : Fin 8 => i.val < 6).image order)).card := by
  have hcard : ((Finset.univ.filter fun i : Fin 8 => i.val < 6).image order).card = 6 := by
    rw [Finset.card_image_of_injective _ order.injective]
    decide
  have h := six_cells_width _ hcard
  omega

/-- The lab's order, in the local numbering of the eight cells. -/
noncomputable def optimalOrder : Fin 8 ≃ Fin 8 :=
  Equiv.ofBijective
    (fun i => (⟨([1, 2, 3, 4, 5, 7, 0, 6].getD i.val 0) % 8,
      Nat.mod_lt _ (by decide)⟩ : Fin 8)) (by decide +kernel)

def orderedPrefix (order : Fin 8 ≃ Fin 8) (i : Fin 8) : Finset (Fin 8) :=
  (Finset.univ.filter fun j : Fin 8 => j.val ≤ i.val).image order

def optimalCase (i : Fin 8) : Cases :=
  ⟨(optimalIndices.getD i.val 0) % 42, Nat.mod_lt _ (by decide)⟩

theorem optimal_selected : ∀ i, selected (optimalCase i) = orderedPrefix optimalOrder i := by
  decide +kernel

theorem optimal_width_checked : ∀ i, (computedBoundary (optimalCase i)).card ≤ 16 := by
  decide +kernel

/-- An explicit order attains the lower bound on the peak full-interface
width. Neither direction of this optimality claim trusts the optimizer. -/
theorem optimal_order_width_at_most_sixteen (i : Fin 8) :
    (physicalBoundary (orderedPrefix optimalOrder i)).card ≤ 16 := by
  rw [← optimal_selected, boundary_exact]
  exact optimal_width_checked i

end Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction
