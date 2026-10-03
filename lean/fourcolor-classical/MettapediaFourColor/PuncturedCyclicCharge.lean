import MettapediaFourColor.ExactCyclicCharge

/-!
# Exact low-neighbour charge with the high boundary retained

The cyclic five-and-tip formula extends to receivers with high neighbours
by retaining the low-degree guard at both ends of each wedge. Transfers
across high edges remain signed boundary observations. No independent
choice of neighbouring rule matches is introduced.
-/

namespace FourColor.PuncturedCyclicCharge

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData NearLinearCharge CyclicCharge CyclicFanContinuation
open RuleFanCharge RulePairBudget RulePairCharge ExceptionalCoreOrientation ExceptionalOverlap
open ExactCyclicCharge (smallRules extraRules extraEdge outside_zero)
open LocalCyclicRules (basic_iff)
open scoped BigOperators

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] [G.LocallyFinite] (rotation : Data G)

/-- The exact low-edge contribution; each tip keeps its other endpoint's
low-degree condition. The eight remaining rule checks stay joint observations. -/
def edgeBudget {v : V} (d : Star (G := G) v) : ℤ :=
  2 * five (G := G) d.val.snd + five (G := G) (step rotation v d).val.snd +
    five (G := G) ((step rotation v).symm d).val.snd +
    (if 5 ≤ G.degree (step rotation v d).val.snd ∧
        G.degree (step rotation v d).val.snd ≤ 6 then five (G := G) (tip rotation d) else 0) +
    (if 5 ≤ G.degree ((step rotation v).symm d).val.snd ∧
        G.degree ((step rotation v).symm d).val.snd ≤ 6 then
      five (G := G) (tip rotation ((step rotation v).symm d)) else 0) +
    extraEdge rotation d.val

theorem edge_exact (tri : Triangular rotation) (v : V)
    (high : 7 ≤ G.degree v) (d : Star (G := G) v)
    (low : 5 ≤ G.degree d.val.snd ∧ G.degree d.val.snd ≤ 6) :
    sent rotation d.val.snd v = edgeBudget rotation d := by
  classical
  obtain ⟨h0,h1,h2,h3,h4⟩ := basic_iff rotation tri v high d low
  have cut : sent rotation d.val.snd v =
      ∑ r ∈ smallRules, if Applies rotation r d.val.snd v then (amount r : ℤ) else 0 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro r _ hr
    simp only [ite_eq_right (outside_zero rotation _ _ low.2 r hr)]
  have checked (r : Fin 84) : RuleMatcher.check rotation r d.val.symm = true ↔
      Applies rotation r d.val.snd v := by
    have h := RuleMatcher.check_iff rotation (r := r) d.val.symm
    change RuleMatcher.check rotation r d.val.symm = true ↔
      Applies rotation r d.val.snd d.val.fst at h
    rwa [d.property] at h
  rw [cut]
  have a0 : amount 0 = 2 := by decide +kernel
  have a1 : amount 1 = 1 := by decide +kernel
  have a2 : amount 2 = 1 := by decide +kernel
  have a3 : amount 3 = 1 := by decide +kernel
  have a4 : amount 4 = 1 := by decide +kernel
  have a5 : amount 5 = 1 := by decide +kernel
  have a6 : amount 6 = 1 := by decide +kernel
  have a7 : amount 7 = 1 := by decide +kernel
  have a8 : amount 8 = 1 := by decide +kernel
  have a9 : amount 9 = 1 := by decide +kernel
  have a10 : amount 10 = 1 := by decide +kernel
  have a11 : amount 11 = 1 := by decide +kernel
  have a12 : amount 12 = 1 := by decide +kernel
  simp [edgeBudget, smallRules, extraEdge, extraRules, checked, h0,h1,h2,h3,h4,
    five, a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12, mul_ite, ite_and, -Finset.sum_boole]
  ring

/-- Sum only the actual low neighbours, retaining their marked rule readings. -/
def lowBudget (v : V) : ℤ :=
  ∑ d : Star (G := G) v, if G.degree d.val.snd ≤ 6 then edgeBudget rotation d else 0

/-- Signed exchange with the high neighbours. This boundary term is not discarded. -/
noncomputable def highBoundary (v : V) : ℤ := by
  classical
  exact ∑ d : Star (G := G) v,
    if 6 < G.degree d.val.snd then net rotation d.val.snd v else 0

variable [Fintype V]

/-- Exact elimination of the low-neighbour interior, with all high-edge
feedback retained as a signed boundary observation. -/
theorem exact_charge (tri : Triangular rotation) (v : V)
    (high : 7 ≤ G.degree v) (lower : ∀ w, G.Adj v w → 5 ≤ G.degree w) :
    finalCharge rotation v = 10 * (6 - (G.degree v : ℤ)) +
      lowBudget rotation v + highBoundary rotation v := by
  classical
  let ns := Finset.univ.image (fun d : Star (G := G) v => d.val.snd)
  have outside (w : V) (hw : w ∉ ns) : net rotation w v = 0 := by
    have no : ¬ G.Adj v w := by
      intro adj
      apply hw
      exact Finset.mem_image.mpr ⟨⟨⟨(v,w),adj⟩,rfl⟩,Finset.mem_univ _,rfl⟩
    rw [net, sent_eq_zero_of_not_adj rotation (fun h => no h.symm),
      sent_eq_zero_of_not_adj rotation no, sub_self]
  have restricted : (∑ w ∈ ns, net rotation w v) = ∑ w : V, net rotation w v :=
    Finset.sum_subset (Finset.subset_univ _) (fun w _ hw => outside w hw)
  have same : (∑ w ∈ ns, net rotation w v) =
      ∑ d : Star (G := G) v, net rotation d.val.snd v :=
    Finset.sum_image (fun a _ b _ h => star_snd_injective v h)
  rw [same] at restricted
  have each (d : Star (G := G) v) : net rotation d.val.snd v =
      (if G.degree d.val.snd ≤ 6 then edgeBudget rotation d else 0) +
      (if 6 < G.degree d.val.snd then net rotation d.val.snd v else 0) := by
    by_cases low : G.degree d.val.snd ≤ 6
    · have adj : G.Adj v d.val.snd := by simpa only [d.property] using d.val.adj
      have localEq := edge_exact rotation tri v high d ⟨lower _ adj,low⟩
      rw [ite_eq_left low, ite_eq_right (by omega), add_zero, net,
        high_to_low_zero (rotation := rotation) high low, sub_zero, localEq]
    · simp only [ite_eq_right low, ite_eq_left (by omega : 6 < G.degree d.val.snd), zero_add]
  have all := Finset.sum_congr (s₁ := Finset.univ) rfl (fun d _ => each d)
  rw [Finset.sum_add_distrib] at all
  rw [finalCharge, ← restricted, all]
  simp only [lowBudget, highBoundary, add_assoc]

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- One high neighbour leaves one exact signed transfer, rather than an
independently bounded input and output. -/
theorem unique_boundary (v q : V) (adj : G.Adj v q) (high : 7 ≤ G.degree q)
    (others : ∀ w, G.Adj v w → w ≠ q → G.degree w ≤ 6) :
    highBoundary rotation v = net rotation q v := by
  classical
  let a : Star (G := G) v := ⟨⟨(v,q),adj⟩,rfl⟩
  unfold highBoundary
  rw [Finset.sum_eq_single a]
  · simp only [a, ite_eq_left (by omega : 6 < G.degree q)]
  · intro b _ ne
    have adjb : G.Adj v b.val.snd := by simpa only [b.property] using b.val.adj
    have bq : b.val.snd ≠ q := fun h => ne (star_snd_injective v h)
    exact ite_eq_right (by have := others _ adjb bq; omega)
  · simp

/-- A flat seven pays its entire ten-unit deficit from the retained low
contributions and the signed transfer on the same exceptional high edge. -/
theorem flat_unique_seven (tri : Triangular rotation) (v q : V)
    (seven : G.degree v = 7) (adj : G.Adj v q) (high : 7 ≤ G.degree q)
    (lower : ∀ w, G.Adj v w → 5 ≤ G.degree w)
    (others : ∀ w, G.Adj v w → w ≠ q → G.degree w ≤ 6)
    (flat : finalCharge rotation v = 0) :
    lowBudget rotation v + net rotation q v = 10 := by
  have h := exact_charge rotation tri v (by omega) lower
  rw [flat, seven, unique_boundary rotation v q adj high others] at h
  norm_num at h
  omega

end FourColor.PuncturedCyclicCharge
