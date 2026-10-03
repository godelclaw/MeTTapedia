import MettapediaFourColor.LocalCyclicRules

/-!
# Exact cyclic charge with retained extra transfers

For a high-degree receiver with only five- and six-valent neighbours, the
first five source rules are exactly the cyclic five-and-tip contribution.
Only eight additional oriented rules can contribute. Their actual marked
edges remain in the remainder; no independent boundary choices are made.
-/

namespace FourColor.ExactCyclicCharge

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData NearLinearCharge CyclicCharge CyclicFanContinuation
open RuleFanCharge RulePairBudget RulePairCharge ExceptionalCoreOrientation ExceptionalOverlap
open scoped BigOperators

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] [G.LocallyFinite] (rotation : Data G)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The first five source rules are precisely the five retained observations. -/
theorem basic_iff (tri : Triangular rotation) (v : V)
    (low : ∀ w, G.Adj v w → 5 ≤ G.degree w ∧ G.degree w ≤ 6)
    (high : 7 ≤ G.degree v) (d : Star (G := G) v) :
    (Applies rotation 0 d.val.snd v ↔ G.degree d.val.snd = 5) ∧
    (Applies rotation 1 d.val.snd v ↔ G.degree (step rotation v d).val.snd = 5) ∧
    (Applies rotation 2 d.val.snd v ↔ G.degree ((step rotation v).symm d).val.snd = 5) ∧
    (Applies rotation 3 d.val.snd v ↔ G.degree (tip rotation ((step rotation v).symm d)) = 5) ∧
    (Applies rotation 4 d.val.snd v ↔ G.degree (tip rotation d) = 5) := by
  have lowAt (e : Star (G := G) v) :
      5 ≤ G.degree e.val.snd ∧ G.degree e.val.snd ≤ 6 :=
    low _ (by simpa only [e.property] using e.val.adj)
  have h := LocalCyclicRules.basic_iff rotation tri v high d (lowAt d)
  simpa only [lowAt (step rotation v d), lowAt ((step rotation v).symm d), true_and] using h

/-- All remaining source identifiers that can have a sender of degree at most six. -/
def extraRules : Finset (Fin 84) := {5,6,7,8,9,10,11,12}
def smallRules : Finset (Fin 84) := {0,1,2,3,4,5,6,7,8,9,10,11,12}

/-- This checks the pinned degree requirements, not a neighbourhood catalogue. -/
theorem low_sender_rules : ∀ r : Fin 84, lower r (sender r) ≤ 6 → r ∈ smallRules := by
  decide +kernel

/-- Count actual extra rule-edge matches, once per oriented source rule. -/
def extraEdge (d : G.Dart) : ℤ :=
  ∑ r ∈ extraRules, if RuleMatcher.check rotation r d.symm then 1 else 0

def extraCount (v : V) : ℤ := ∑ d : Star (G := G) v, extraEdge rotation d.val

theorem extra_nonneg (v : V) : 0 ≤ extraCount rotation v := by
  apply Finset.sum_nonneg
  intro d _
  apply Finset.sum_nonneg
  intro r _
  split <;> norm_num

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem outside_zero (u v : V) (low : G.degree u ≤ 6) (r : Fin 84)
    (outside : r ∉ smallRules) : ¬ Applies rotation r u v := by
  rintro ⟨x,hu,_⟩
  have h := (x.degree (sender r)).1
  rw [hu] at h
  exact outside (low_sender_rules r (h.trans low))

theorem edge_exact (tri : Triangular rotation) (v : V)
    (low : ∀ w, G.Adj v w → 5 ≤ G.degree w ∧ G.degree w ≤ 6)
    (high : 7 ≤ G.degree v) (d : Star (G := G) v) :
    sent rotation d.val.snd v =
      2 * five (G := G) d.val.snd + five (G := G) (step rotation v d).val.snd +
      five (G := G) ((step rotation v).symm d).val.snd + five (G := G) (tip rotation d) +
      five (G := G) (tip rotation ((step rotation v).symm d)) + extraEdge rotation d.val := by
  classical
  obtain ⟨h0,h1,h2,h3,h4⟩ := basic_iff rotation tri v low high d
  have hd : G.Adj v d.val.snd := by simpa only [d.property] using d.val.adj
  have cut : sent rotation d.val.snd v =
      ∑ r ∈ smallRules, if Applies rotation r d.val.snd v then (amount r : ℤ) else 0 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro r _ hr
    simp only [ite_eq_right (outside_zero rotation _ _ (low _ hd).2 r hr)]
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
  simp [smallRules, extraEdge, extraRules, checked, h0,h1,h2,h3,h4,
    five, a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12, mul_ite, -Finset.sum_boole]
  ring

variable [Fintype V]

/-- Exact signed charge: each shared five contributes four, each marked
outer five-tip contributes two, and every extra oriented match is retained. -/
theorem exact_charge (tri : Triangular rotation) (v : V)
    (high : 7 ≤ G.degree v)
    (low : ∀ w, G.Adj v w → 5 ≤ G.degree w ∧ G.degree w ≤ 6) :
    finalCharge rotation v = 10 * (6 - (G.degree v : ℤ)) +
      4 * fiveCount (G := G) v + 2 * tipCount rotation v + extraCount rotation v := by
  classical
  have zero (w : V) : sent rotation v w = 0 := by
    by_cases hw : G.Adj v w
    · exact high_to_low_zero high (low w hw).2
    · exact sent_eq_zero_of_not_adj rotation hw
  let ns := Finset.univ.image (fun d : Star (G := G) v => d.val.snd)
  have outside (w : V) (hw : w ∉ ns) : sent rotation w v = 0 := by
    apply sent_eq_zero_of_not_adj rotation
    intro adj
    apply hw
    exact Finset.mem_image.mpr ⟨⟨⟨(v,w),adj.symm⟩,rfl⟩,Finset.mem_univ _,rfl⟩
  have restricted : (∑ w ∈ ns, sent rotation w v) = ∑ w : V, sent rotation w v :=
    Finset.sum_subset (Finset.subset_univ _) (fun w _ hw => outside w hw)
  have same : (∑ w ∈ ns, sent rotation w v) =
      ∑ d : Star (G := G) v, sent rotation d.val.snd v :=
    Finset.sum_image (fun a _ b _ h => star_snd_injective v h)
  rw [same] at restricted
  have all := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun d _ => edge_exact rotation tri v low high d)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at all
  have forward := Equiv.sum_comp (step rotation v) (fun d => five (G := G) d.val.snd)
  have backward := Equiv.sum_comp (step rotation v).symm (fun d => five (G := G) d.val.snd)
  have tips := Equiv.sum_comp (step rotation v).symm (fun d => five (G := G) (tip rotation d))
  rw [forward, backward, tips] at all
  unfold finalCharge
  simp only [net, zero, sub_zero]
  rw [← restricted, all]
  unfold fiveCount tipCount extraCount
  ring

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- Rules 006_1 and 006_2 preserve two distinct five-neighbours of the
same receiver. Their edge prevents identifying these witnesses. -/
theorem two_fives (r : Fin 84) (hr : r = 9 ∨ r = 10) (x : Occurrence rotation r) :
    ∃ u w, G.Adj (x.vertex (receiver r)) u ∧ G.Adj (x.vertex (receiver r)) w ∧
      G.degree u = 5 ∧ G.degree w = 5 ∧ u ≠ w := by
  rcases hr with rfl | rfl
  all_goals
    refine ⟨x.vertex 3,x.vertex 4,x.edge _ _ (by decide +kernel),
      x.edge _ _ (by decide +kernel),?_,?_,(x.edge 3 4 (by decide +kernel)).ne⟩
    · have h := x.degree 3
      change 5 ≤ G.degree (x.vertex 3) ∧ (5 = 0 ∨ G.degree (x.vertex 3) ≤ 5) at h
      omega
    · have h := x.degree 4
      change 5 ≤ G.degree (x.vertex 4) ∧ (5 = 0 ∨ G.degree (x.vertex 4) ≤ 5) at h
      omega

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- No such match survives a genuine single-five neighbourhood. -/
theorem no_two_fives (v : V)
    (unique : ∀ u w, G.Adj v u → G.Adj v w → G.degree u = 5 → G.degree w = 5 → u = w)
    (r : Fin 84) (hr : r = 9 ∨ r = 10) (u : V) : ¬ Applies rotation r u v := by
  rintro ⟨x,_,xt⟩
  obtain ⟨a,b,ha,hb,fa,fb,ne⟩ := two_fives rotation r hr x
  rw [xt] at ha hb
  exact ne (unique a b ha hb fa fb)

/-- The residual keeps six oriented rule types; it does not assert that
any one of their independent matches can be selected arbitrarily. -/
def residualRules : Finset (Fin 84) := {5,6,7,8,11,12}

def residualCount (v : V) : ℤ :=
  ∑ d : Star (G := G) v, ∑ r ∈ residualRules,
    if RuleMatcher.check rotation r d.val.symm then 1 else 0

omit [Fintype V] in
theorem residual_eq (v : V)
    (unique : ∀ u w, G.Adj v u → G.Adj v w → G.degree u = 5 → G.degree w = 5 → u = w) :
    extraCount rotation v = residualCount rotation v := by
  classical
  apply Finset.sum_congr rfl
  intro d _
  have no (r : Fin 84) (hr : r = 9 ∨ r = 10) :
      RuleMatcher.check rotation r d.val.symm = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have apply := (RuleMatcher.check_iff rotation d.val.symm).mp h
    change Applies rotation r d.val.snd d.val.fst at apply
    rw [d.property] at apply
    exact no_two_fives rotation v unique r hr _ apply
  simp [extraEdge, extraRules, residualRules, no 9 (Or.inl rfl),
    no 10 (Or.inr rfl), -Finset.sum_boole]

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- A unique marked five has count one, with no quotient of its identity. -/
theorem five_count_one (v q : V) (adj : G.Adj v q) (hq : G.degree q = 5)
    (residual : ∀ w, G.Adj v w → w ≠ q → G.degree w = 6) :
    fiveCount (G := G) v = 1 := by
  classical
  let a : Star (G := G) v := ⟨⟨(v,q),adj⟩,rfl⟩
  unfold fiveCount
  rw [Finset.sum_eq_single a]
  · simp [a, five, hq]
  · intro b _ ne
    have hb : G.Adj v b.val.snd := by simpa only [b.property] using b.val.adj
    have bq : b.val.snd ≠ q := fun h => ne (star_snd_injective v h)
    simp [five, residual _ hb bq]
  · simp

/-- A flat seven with one five and at least two retained tips has only
two exact budgets. This is a classification, not a reducibility assertion. -/
theorem flat_seven_cases (tri : Triangular rotation) (v q : V)
    (seven : G.degree v = 7) (adj : G.Adj v q) (hq : G.degree q = 5)
    (residual : ∀ w, G.Adj v w → w ≠ q → G.degree w = 6)
    (tips : 2 ≤ tipCount rotation v) (flat : finalCharge rotation v = 0) :
    (tipCount rotation v = 2 ∧ residualCount rotation v = 2) ∨
    (tipCount rotation v = 3 ∧ residualCount rotation v = 0) := by
  have low (w : V) (hw : G.Adj v w) : 5 ≤ G.degree w ∧ G.degree w ≤ 6 := by
    by_cases h : w = q
    · subst w; omega
    · rw [residual w hw h]; omega
  have unique : ∀ u w, G.Adj v u → G.Adj v w → G.degree u = 5 → G.degree w = 5 → u = w := by
    intro u w hu hw fu fw
    have uq : u = q := by by_contra h; have := residual u hu h; omega
    have wq : w = q := by by_contra h; have := residual w hw h; omega
    exact uq.trans wq.symm
  have h := exact_charge rotation tri v (by omega) low
  have nonneg := extra_nonneg rotation v
  rw [flat, seven, five_count_one v q adj hq residual, residual_eq rotation v unique] at h
  rw [residual_eq rotation v unique] at nonneg
  omega

omit [Fintype V] in
/-- Zero remaining charge means every retained source-rule observation is
false. This conclusion concerns the whole joint neighbourhood. -/
theorem residual_zero_iff (v : V) : residualCount rotation v = 0 ↔
    ∀ d : Star (G := G) v, ∀ r ∈ residualRules,
      RuleMatcher.check rotation r d.val.symm = false := by
  constructor
  · intro zero d r hr
    have single : (if RuleMatcher.check rotation r d.val.symm then (1 : ℤ) else 0) ≤
        ∑ i ∈ residualRules, if RuleMatcher.check rotation i d.val.symm then (1 : ℤ) else 0 := by
      apply Finset.single_le_sum (f := fun i : Fin 84 =>
        if RuleMatcher.check rotation i d.val.symm then (1 : ℤ) else 0)
      · intro i _
        split <;> norm_num
      · exact hr
    have whole : (∑ i ∈ residualRules,
        if RuleMatcher.check rotation i d.val.symm then (1 : ℤ) else 0) ≤
        residualCount rotation v := by
      apply Finset.single_le_sum (f := fun e : Star (G := G) v =>
        ∑ i ∈ residualRules, if RuleMatcher.check rotation i e.val.symm then (1 : ℤ) else 0)
      · intro e _
        apply Finset.sum_nonneg
        intro i _
        split <;> norm_num
      · exact Finset.mem_univ d
    rw [zero] at whole
    apply Bool.eq_false_iff.mpr
    intro yes
    have positive : (1 : ℤ) ≤ (0 : ℤ) := by
      simpa only [yes, ↓reduceIte] using single.trans whole
    norm_num at positive
  · intro no
    apply Finset.sum_eq_zero
    intro d _
    apply Finset.sum_eq_zero
    intro r hr
    simp only [no d r hr, Bool.false_eq_true, ↓reduceIte]

end FourColor.ExactCyclicCharge
