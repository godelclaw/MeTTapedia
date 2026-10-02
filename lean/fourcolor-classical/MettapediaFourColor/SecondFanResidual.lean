import MettapediaFourColor.D3009RepairGeometry

/-!
# The second side of a shared charge fan

The second free centre retains one outer five-tip, rather than the two
available at the first centre. Its exact flat charge therefore permits
one or two five-neighbours. The single-five branch consumes the same wheel
repair contract; the two-five branch retains its actual marked vertices
and has no extra incoming charge. No repair of that last branch is assumed.
-/

namespace FourColor.SecondFanResidual

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open RuleFanSupply CyclicCharge CyclicFanContinuation ExactCyclicCharge
open ChainFanRecognition (walk walk_fst walk_next)

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (rotation : Data G)

/-- The backward outer tip at the second free position is the same second
five in the original sender star. -/
theorem second_tip (tri : ExceptionalOverlap.Triangular rotation)
    (d : G.Dart) (fixed : Fixed rotation d) :
    1 ≤ tipCount rotation (secondFree rotation d) := by
  classical
  let e := walk rotation d 4
  let a : Star (G := G) e.snd := ⟨e.symm,rfl⟩
  let b := (step rotation e.snd).symm a
  have pred (n : ℕ) : rotation.vertexRotation.symm (walk rotation d (n+1)) =
      walk rotation d n := by rw [← walk_next, Equiv.symm_apply_apply]
  have tip5 : G.degree (tip rotation b) = 5 := by
    rw [tip_reverse rotation tri]
    change G.degree (rotation.vertexRotation.symm
      (rotation.vertexRotation.symm (walk rotation d 4))).snd = 5
    rw [pred,pred]
    exact fixed.second
  have h := Finset.single_le_sum
    (f := fun x : Star (G := G) e.snd => five (G := G) (tip rotation x))
    (fun x _ => five_nonneg _) (Finset.mem_univ b)
  change 1 ≤ tipCount rotation e.snd
  simpa only [tipCount, five, tip5, ite_eq_left] using h

/-- Two marked fives exhaust a budget of two. This preserves their joint
identity and leaves every other low neighbour of degree six. -/
theorem two_fives_exhaust (v p q : V) (hp : G.Adj v p) (hq : G.Adj v q)
    (fp : G.degree p = 5) (fq : G.degree q = 5) (pq : p ≠ q)
    (low : ∀ w, G.Adj v w → 5 ≤ G.degree w ∧ G.degree w ≤ 6)
    (budget : fiveCount (G := G) v ≤ 2) :
    fiveCount (G := G) v = 2 ∧
      ∀ w, G.Adj v w → w ≠ p → w ≠ q → G.degree w = 6 := by
  classical
  let a : Star (G := G) v := ⟨⟨(v,p),hp⟩,rfl⟩
  let b : Star (G := G) v := ⟨⟨(v,q),hq⟩,rfl⟩
  have ab : a ≠ b := fun he => pq (congrArg (fun x : Star (G := G) v => x.val.snd) he)
  have lower := Finset.sum_le_univ_sum_of_nonneg (s := {a,b})
    (f := fun x : Star (G := G) v => five (G := G) x.val.snd)
    (fun x => five_nonneg _)
  have count : fiveCount (G := G) v = 2 := by
    have : 2 ≤ fiveCount (G := G) v := by
      simpa [fiveCount, Finset.sum_pair ab, a,b,five,fp,fq] using lower
    omega
  refine ⟨count,?_⟩
  intro w hw wp wq
  have bounds := low w hw
  by_contra hn
  have fw : G.degree w = 5 := by omega
  let c : Star (G := G) v := ⟨⟨(v,w),hw⟩,rfl⟩
  have ca : c ≠ a := fun he => wp (congrArg (fun x : Star (G := G) v => x.val.snd) he)
  have cb : c ≠ b := fun he => wq (congrArg (fun x : Star (G := G) v => x.val.snd) he)
  have lower := Finset.sum_le_univ_sum_of_nonneg (s := {c,a,b})
    (f := fun x : Star (G := G) v => five (G := G) x.val.snd)
    (fun x => five_nonneg _)
  have : 3 ≤ fiveCount (G := G) v := by
    simpa [fiveCount, Finset.sum_insert, ca,cb,ab, a,b,c,five,fp,fq,fw,
      -Finset.sum_boole] using lower
  omega

variable [DecidableEq V] [DecidableRel G.Adj]

/-- A zero extra budget excludes every extra oriented rule on every
actual incident edge, including correlations between different edges. -/
theorem extra_zero (v : V) (zero : extraCount rotation v = 0)
    (d : Star (G := G) v) (r : Fin 84) (hr : r ∈ extraRules) :
    RuleMatcher.check rotation r d.val.symm = false := by
  have nonneg (e : Star (G := G) v) : 0 ≤ extraEdge rotation e.val := by
    apply Finset.sum_nonneg
    intro i _
    split <;> norm_num
  have edgezero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun e (_ : e ∈ (Finset.univ : Finset (Star (G := G) v))) => nonneg e)).mp zero
    d (Finset.mem_univ d)
  have each := (Finset.sum_eq_zero_iff_of_nonneg
    (f := fun i : Fin 84 => if RuleMatcher.check rotation i d.val.symm then (1 : ℤ) else 0)
    (s := extraRules) (by intro i _; split <;> norm_num)).mp edgezero r hr
  apply Bool.eq_false_iff.mpr
  intro yes
  rw [yes] at each
  norm_num at each

end FourColor.SecondFanResidual

namespace FourColor.ActualSecondFanResidual

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality
open ActualRulePairDiamond (graph rotation)
open RuleFanSupply CyclicCharge CyclicFanContinuation ExactCyclicCharge SecondFanResidual
open ChainFanRecognition (walk walk_fst walk_next)

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- Every nonconsecutive pair in this six-star is nonadjacent. A chord
would form a triangle contradicting its actual facial rotation. -/
theorem star_nonadjacent (d : (graph original minimal).Dart)
    (six : (graph original minimal).degree d.fst = 6)
    (n : ℕ) (lower : 2 ≤ n) (upper : n ≤ 4) :
    ¬ (graph original minimal).Adj d.snd (walk (rotation original minimal) d n).snd := by
  let r := rotation original minimal
  let e := walk r d n
  have es : e.fst = d.fst := walk_fst _ _ _
  have adjacent : (graph original minimal).Adj d.fst e.snd := by
    simpa only [es] using e.adj
  have other := walk_ne_receiver r (MinimalExceptionalEmbedding.cyclic original minimal) d six
  intro chord
  rcases MinimalExceptionalEmbedding.triangle_facial original minimal d.adj chord adjacent.symm with
    first | second
  · obtain ⟨_,he,turn⟩ := first
    have ee : (⟨(d.fst,e.snd),he⟩ : (graph original minimal).Dart) = e := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext es.symm rfl
    rw [ee] at turn
    have eq : r.vertexRotation d = e := turn
    have pred : r.vertexRotation.symm e = walk r d (n-1) := by
      have hn : n = (n-1)+1 := by omega
      change r.vertexRotation.symm (walk r d n) = _
      conv_lhs => rw [hn]
      rw [← walk_next, Equiv.symm_apply_apply]
    have same := congrArg (fun x => (r.vertexRotation.symm x).snd) eq
    rw [Equiv.symm_apply_apply,pred] at same
    exact other (n-1) (by omega) (by omega) same.symm
  · obtain ⟨he,_,turn⟩ := second
    have ee : (⟨(d.fst,e.snd),he⟩ : (graph original minimal).Dart) = e := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext es.symm rfl
    rw [ee] at turn
    have eq : r.vertexRotation (walk r d n) = d := turn
    rw [walk_next] at eq
    exact other (n+1) (by omega) (by omega) (congrArg (fun x => x.snd) eq)

/-- The second centre either continues to a genuinely new high neighbour,
has only the retained last five, or has precisely one further five.
The two-five branch exhausts the charge budget: one tip and no extra transfers.
No wheel repair is assumed in this geometric classification. -/
theorem profile_alternatives
    (d : (graph original minimal).Dart) (fixed : Fixed (rotation original minimal) d)
    (seven : (graph original minimal).degree (secondFree (rotation original minimal) d) = 7)
    (flat : NearLinearCharge.finalCharge (rotation original minimal)
      (secondFree (rotation original minimal) d) = 0) :
    (∃ w, w ≠ d.snd ∧ w ≠ secondFree (rotation original minimal) d ∧
      (graph original minimal).Adj (secondFree (rotation original minimal) d) w ∧
      w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 3 ∧
      7 ≤ (graph original minimal).degree w) ∨
    (∀ w, (graph original minimal).Adj (secondFree (rotation original minimal) d) w →
      w ≠ (walk (rotation original minimal) d 5).snd → (graph original minimal).degree w = 6) ∨
    (∃ q, (graph original minimal).Adj (secondFree (rotation original minimal) d) q ∧
      q ≠ (walk (rotation original minimal) d 5).snd ∧
      (graph original minimal).degree q = 5 ∧
      (∀ w, (graph original minimal).Adj (secondFree (rotation original minimal) d) w →
        w ≠ (walk (rotation original minimal) d 5).snd → w ≠ q →
        (graph original minimal).degree w = 6) ∧
      fiveCount (G := graph original minimal) (secondFree (rotation original minimal) d) = 2 ∧
      tipCount (rotation original minimal) (secondFree (rotation original minimal) d) = 1 ∧
      extraCount (rotation original minimal) (secondFree (rotation original minimal) d) = 0 ∧
      (∀ e : Star (G := graph original minimal) (secondFree (rotation original minimal) d),
        ∀ j ∈ extraRules, RuleMatcher.check (rotation original minimal) j e.val.symm = false)) := by
  let r := rotation original minimal
  let b := secondFree r d
  let p := (walk r d 5).snd
  change (graph original minimal).degree b = 7 at seven
  change NearLinearCharge.finalCharge r b = 0 at flat
  have tri := MinimalExceptionalEmbedding.triangular original minimal
  have bp : (graph original minimal).Adj b p := by
    have h := ExceptionalOverlap.consecutive_adjacent r tri (walk r d 4)
    rw [walk_next] at h
    exact h
  by_cases hh : ∃ w, (graph original minimal).Adj b w ∧ 7 ≤ (graph original minimal).degree w
  · obtain ⟨w,hw,high⟩ := hh
    refine Or.inl ⟨w,?_,hw.ne.symm,hw,?_,high⟩
    · intro same; subst w
      exact star_nonadjacent original minimal d fixed.center 4 (by decide) (by decide) hw.symm
    · have sb : (graph original minimal).Adj d.fst b := by
        simpa only [b,secondFree,walk_fst] using (walk r d 4).adj
      let path : (graph original minimal).Walk d.snd w :=
        .cons d.adj.symm (.cons sb (.cons hw .nil))
      simpa [LocalCoverageAssembly.closedBall,path] using path.edist_le
  · have low (w : _) (hw : (graph original minimal).Adj b w) :
        5 ≤ (graph original minimal).degree w ∧ (graph original minimal).degree w ≤ 6 := by
      have hm := ActualRuleFanSupply.degree_five original minimal ⟨(w,b),hw.symm⟩
      exact ⟨hm,by by_contra hn; exact hh ⟨w,hw,by omega⟩⟩
    have tips := second_tip r tri d fixed
    change 1 ≤ tipCount r b at tips
    have budget := CyclicCharge.flat_budget r tri b (Nat.le_of_eq seven.symm) low flat
    rw [seven] at budget
    have atmost : fiveCount (G := graph original minimal) b ≤ 2 := by omega
    by_cases another : ∃ q, (graph original minimal).Adj b q ∧ q ≠ p ∧
        (graph original minimal).degree q = 5
    · obtain ⟨q,hq,qp,fq⟩ := another
      obtain ⟨count,residual⟩ := two_fives_exhaust b p q bp hq fixed.last fq qp.symm low atmost
      have exact := exact_charge r tri b (Nat.le_of_eq seven.symm) low
      have nonneg := extra_nonneg r b
      rw [flat,seven,count] at exact
      have tipone : tipCount r b = 1 := by omega
      have extras : extraCount r b = 0 := by omega
      exact Or.inr (Or.inr ⟨q,hq,qp,fq,residual,count,tipone,extras,
        fun e j hj => extra_zero r b extras e j hj⟩)
    · apply Or.inr ∘ Or.inl
      intro w hw ne
      have h := low w hw
      have notfive : (graph original minimal).degree w ≠ 5 := fun hf => another ⟨w,hw,ne,hf⟩
      omega

/-- The second centre either continues to a genuinely new high neighbour,
or has exactly one further five besides the retained last sender neighbour.
The latter exhausts the charge budget: one tip and no extra transfers.
The single-five case is excluded only through the explicit wheel repair. -/
theorem alternatives (repair : D3009RepairGeometry.SourceRepair)
    (d : (graph original minimal).Dart) (fixed : Fixed (rotation original minimal) d)
    (seven : (graph original minimal).degree (secondFree (rotation original minimal) d) = 7)
    (flat : NearLinearCharge.finalCharge (rotation original minimal)
      (secondFree (rotation original minimal) d) = 0) :
    (∃ w, w ≠ d.snd ∧ w ≠ secondFree (rotation original minimal) d ∧
      (graph original minimal).Adj (secondFree (rotation original minimal) d) w ∧
      w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 3 ∧
      7 ≤ (graph original minimal).degree w) ∨
    (∃ q, (graph original minimal).Adj (secondFree (rotation original minimal) d) q ∧
      q ≠ (walk (rotation original minimal) d 5).snd ∧
      (graph original minimal).degree q = 5 ∧
      (∀ w, (graph original minimal).Adj (secondFree (rotation original minimal) d) w →
        w ≠ (walk (rotation original minimal) d 5).snd → w ≠ q →
        (graph original minimal).degree w = 6) ∧
      fiveCount (G := graph original minimal) (secondFree (rotation original minimal) d) = 2 ∧
      tipCount (rotation original minimal) (secondFree (rotation original minimal) d) = 1 ∧
      extraCount (rotation original minimal) (secondFree (rotation original minimal) d) = 0 ∧
      (∀ e : Star (G := graph original minimal) (secondFree (rotation original minimal) d),
        ∀ j ∈ extraRules, RuleMatcher.check (rotation original minimal) j e.val.symm = false)) := by
  rcases profile_alternatives original minimal d fixed seven flat with high | single | pair
  · exact Or.inl high
  · have tri := MinimalExceptionalEmbedding.triangular original minimal
    have bp : (graph original minimal).Adj (secondFree (rotation original minimal) d)
        (walk (rotation original minimal) d 5).snd := by
      have h := ExceptionalOverlap.consecutive_adjacent (rotation original minimal) tri
        (walk (rotation original minimal) d 4)
      rw [walk_next] at h
      exact h
    exact False.elim (D3009RepairGeometry.profile_excluded original minimal repair
      ⟨(secondFree (rotation original minimal) d,(walk (rotation original minimal) d 5).snd),bp⟩
      seven fixed.last single)
  · exact Or.inr pair

end
end FourColor.ActualSecondFanResidual
