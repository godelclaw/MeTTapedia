import MettapediaFourColor.RulePairCharge

/-!
# Joint charge budget for an aligned rule pair

Both possible degrees of the second sender contribute to one lower bound.
The degree-six branch uses the shared occurrence of rule 006_1; the degree-five
branch uses rule 001 instead. Actual cyclic order distinguishes the senders
before their contributions are removed from the receiver's signed budget.
-/

namespace FourColor.RulePairBudget

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData NearLinearCharge RuleMatcher RulePairDiamond RulePairCharge
open scoped BigOperators

set_option maxRecDepth 65536

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

/-- A subpattern preserves all its edges and oriented turns. Its degree
requirements are checked against the same actual vertex reading. -/
structure Subpattern (r s : Fin 84) (m : Vertex r → Vertex s) : Prop where
  edge : ∀ i j, (graph r).Adj i j → (graph s).Adj (m i) (m j)
  turn : ∀ i j k, Turn r i j k → Turn s (m i) (m j) (m k)

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] [G.LocallyFinite] {rotation : Data G}

def restrict {r s : Fin 84} {m : Vertex r → Vertex s}
    (h : Subpattern r s m) (x : Occurrence rotation s)
    (degree : ∀ i, lower r i ≤ G.degree (x.vertex (m i)) ∧
      (upper r i = 0 ∨ G.degree (x.vertex (m i)) ≤ upper r i)) : Occurrence rotation r where
  vertex i := x.vertex (m i)
  edge i j hij := x.edge _ _ (h.edge i j hij)
  degree := degree
  turn i j k hij hik ht := x.turn _ _ _ (h.edge i j hij) (h.edge i k hik) (h.turn i j k ht)

def leftTriangleMap : Vertex 1 → Vertex 4 := ![0, 1, 2]
def rightTriangleMap : Vertex 2 → Vertex 5 := ![0, 1, 2]

theorem left_triangle_pattern : Subpattern 1 4 leftTriangleMap := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

theorem right_triangle_pattern : Subpattern 2 5 rightTriangleMap := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

/-- A five-valent sender supplies the two-unit rule on any edge whose
receiver has degree at least five. The source rule has no specified turns. -/
theorem zero_of_five (d : G.Dart) (five : G.degree d.fst = 5)
    (receiver : 5 ≤ G.degree d.snd) : check rotation 0 d = true := by
  have noTurns : ∀ i j k : Vertex 0, ¬ Turn 0 i j k := by decide +kernel
  let x : Occurrence rotation 0 := {
    vertex := ![d.fst, d.snd]
    edge := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact False.elim ((by decide +kernel : ¬ (graph 0).Adj 0 0) hij)
      · exact d.adj
      · exact d.adj.symm
      · exact False.elim ((by decide +kernel : ¬ (graph 0).Adj 1 1) hij)
    degree := by
      intro i
      fin_cases i
      · change 5 ≤ G.degree d.fst ∧ (5 = 0 ∨ G.degree d.fst ≤ 5)
        omega
      · change 5 ≤ G.degree d.snd ∧ (0 = 0 ∨ G.degree d.snd ≤ 0)
        exact ⟨receiver, Or.inl rfl⟩
    turn := fun i j k _ _ ht => (noTurns i j k ht).elim }
  exact (check_iff rotation d).mpr ⟨x, rfl, rfl⟩

theorem one_of_left (d : G.Dart) (h4 : check rotation 4 d = true)
    (five : G.degree (candidate rotation 4 d 2) = 5)
    (receiver : 7 ≤ G.degree d.snd) : check rotation 1 d = true := by
  obtain ⟨x, xs, xt⟩ := (check_iff rotation d).mp h4
  rw [candidate_eq rotation d x xs xt] at five
  let y := restrict left_triangle_pattern x (by
    intro i
    fin_cases i
    · have h := x.degree 0
      rw [show lower 4 0 = 5 from by decide +kernel,
        show upper 4 0 = 6 from by decide +kernel] at h
      exact h
    · change 7 ≤ G.degree (x.vertex 1) ∧ (0 = 0 ∨ G.degree (x.vertex 1) ≤ 0)
      exact ⟨xt ▸ receiver, Or.inl rfl⟩
    · change 5 ≤ G.degree (x.vertex 2) ∧ (5 = 0 ∨ G.degree (x.vertex 2) ≤ 5)
      omega)
  exact (check_iff rotation d).mpr ⟨y, xs, xt⟩

theorem two_of_right (d : G.Dart) (h5 : check rotation 5 d = true)
    (five : G.degree (candidate rotation 5 d 2) = 5)
    (receiver : 7 ≤ G.degree d.snd) : check rotation 2 d = true := by
  obtain ⟨x, xs, xt⟩ := (check_iff rotation d).mp h5
  rw [candidate_eq rotation d x xs xt] at five
  let y := restrict right_triangle_pattern x (by
    intro i
    fin_cases i
    · have h := x.degree 0
      rw [show lower 5 0 = 5 from by decide +kernel,
        show upper 5 0 = 6 from by decide +kernel] at h
      exact h
    · change 7 ≤ G.degree (x.vertex 1) ∧ (0 = 0 ∨ G.degree (x.vertex 1) ≤ 0)
      exact ⟨xt ▸ receiver, Or.inl rfl⟩
    · change 5 ≤ G.degree (x.vertex 2) ∧ (5 = 0 ∨ G.degree (x.vertex 2) ≤ 5)
      omega)
  exact (check_iff rotation d).mpr ⟨y, xs, xt⟩

theorem first_four (d : G.Dart) (h4 : check rotation 4 d = true)
    (sender : G.degree d.fst = 5)
    (five : G.degree (candidate rotation 4 d 2) = 5)
    (receiver : 7 ≤ G.degree d.snd) : 4 ≤ net rotation d.fst d.snd := by
  have h0 := zero_of_five (rotation := rotation) d sender (by omega)
  have h1 := one_of_left d h4 five receiver
  have h := charge_lower d {0, 1, 4} (by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h4)
  have total : (∑ r ∈ ({0, 1, 4} : Finset (Fin 84)), (amount r : ℤ)) = 4 := by
    decide +kernel
  rw [total, sentAt_eq] at h
  have hz := high_to_low_zero (rotation := rotation) receiver (by omega : G.degree d.fst ≤ 6)
  simpa only [net, hz, sub_zero] using h

theorem second_four (d : G.Dart) (h5 : check rotation 5 d = true)
    (sender : G.degree d.fst = 5)
    (five : G.degree (candidate rotation 5 d 2) = 5)
    (receiver : 7 ≤ G.degree d.snd) : 4 ≤ net rotation d.fst d.snd := by
  have h0 := zero_of_five (rotation := rotation) d sender (by omega)
  have h2 := two_of_right d h5 five receiver
  have h := charge_lower d {0, 2, 5} (by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact h0
    · exact h2
    · exact h5)
  have total : (∑ r ∈ ({0, 2, 5} : Finset (Fin 84)), (amount r : ℤ)) = 4 := by
    decide +kernel
  rw [total, sentAt_eq] at h
  have hz := high_to_low_zero (rotation := rotation) receiver (by omega : G.degree d.fst ≤ 6)
  simpa only [net, hz, sub_zero] using h

variable [Finite V]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Two backward receiver turns cannot return to the same incoming edge
when the actual cyclic star has more than two darts. -/
theorem distinct_senders (cyclic : rotation.IsVertexwiseCyclic) (d : G.Dart)
    (degree : 2 < G.degree d.snd) : d.fst ≠ (secondRoot (rotation := rotation) d).fst := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let fiber : Finset G.Dart := Finset.univ.filter fun e => e.fst = d.snd
  have hc : rotation.vertexRotation.IsCycleOn (fiber : Set G.Dart) := by
    simpa [fiber] using cyclic d.snd
  have card : fiber.card = G.degree d.snd := by
    change ({e : G.Dart | e.fst = d.snd} : Finset G.Dart).card = _
    rw [G.dart_fst_fiber_card_eq_degree]
    exact (SimpleGraph.degree_instance_independent d.snd _ _).symm
  intro same
  have hd : secondRoot (rotation := rotation) d = d := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext same.symm (second_receiver d)
  have back : rotation.vertexRotation.symm (rotation.vertexRotation.symm d.symm) = d.symm :=
    congrArg SimpleGraph.Dart.symm hd
  have twice : (rotation.vertexRotation ^ 2) d.symm = d.symm := by
    have h := congrArg (fun e => rotation.vertexRotation (rotation.vertexRotation e)) back
    simpa only [Equiv.apply_symm_apply, pow_succ', pow_zero,
      Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h.symm
  have divides := (hc.pow_apply_eq (show d.symm ∈ fiber by simp [fiber])).mp twice
  rw [card] at divides
  have := Nat.le_of_dvd (by decide : 0 < 2) divides
  omega

omit [Finite V] in
/-- Both rule readings retain the same shared vertex in their exact
executable candidates. -/
theorem shared_candidates (d : G.Dart) (left : check rotation 4 d = true)
    (right : check rotation 5 (secondRoot (rotation := rotation) d) = true) :
    candidate rotation 4 d 2 = candidate rotation 5 (secondRoot (rotation := rotation) d) 2 := by
  obtain ⟨x, xs, xt⟩ := (check_iff rotation d).mp left
  obtain ⟨y, ys, yt⟩ := (check_iff rotation _).mp right
  rw [candidate_eq rotation d x xs xt, candidate_eq rotation _ y ys yt]
  exact (aligned x y d xs xt ys yt).2

/-- Retain the stronger eight-unit bound when the second sender has degree
five; the degree-six branch supplies seven. No degree is chosen in advance. -/
theorem joint_bound (cyclic : rotation.IsVertexwiseCyclic) (d : G.Dart)
    (left : check rotation 4 d = true)
    (right : check rotation 5 (secondRoot (rotation := rotation) d) = true)
    (sender : G.degree d.fst = 5)
    (five : G.degree (candidate rotation 4 d 2) = 5)
    (outer : G.degree (candidate rotation 5 (secondRoot (rotation := rotation) d) 3) = 6)
    (receiver : 7 ≤ G.degree d.snd) :
    d.fst ≠ (secondRoot (rotation := rotation) d).fst ∧
    (if G.degree (secondRoot (rotation := rotation) d).fst = 5 then 8 else 7 : ℤ) ≤
      net rotation d.fst d.snd +
      net rotation (secondRoot (rotation := rotation) d).fst d.snd := by
  refine ⟨distinct_senders cyclic d (by omega), ?_⟩
  have hfirst := first_four d left sender five receiver
  obtain ⟨y, ys, yt⟩ := (check_iff rotation _).mp right
  have hd := y.degree 0
  rw [show lower 5 0 = 5 from by decide +kernel,
    show upper 5 0 = 6 from by decide +kernel] at hd
  change y.vertex 0 = (secondRoot (rotation := rotation) d).fst at ys
  rw [ys] at hd
  have he := second_receiver (rotation := rotation) d
  by_cases second : G.degree (secondRoot (rotation := rotation) d).fst = 5
  · have hw : G.degree (candidate rotation 5 (secondRoot (rotation := rotation) d) 2) = 5 :=
      (shared_candidates d left right) ▸ five
    have hsecond := second_four _ right second hw (he ▸ receiver)
    rw [he] at hsecond
    rw [if_pos second]
    omega
  · have six : G.degree (secondRoot (rotation := rotation) d).fst = 6 := by omega
    have h9 := third_of_checks cyclic d left right sender five outer six receiver
    have hsecond := net_three _ right h9
    rw [he] at hsecond
    rw [if_neg second]
    omega

/-- Both degree branches supply a common seven-unit bound. -/
theorem joint_seven (cyclic : rotation.IsVertexwiseCyclic) (d : G.Dart)
    (left : check rotation 4 d = true)
    (right : check rotation 5 (secondRoot (rotation := rotation) d) = true)
    (sender : G.degree d.fst = 5)
    (five : G.degree (candidate rotation 4 d 2) = 5)
    (outer : G.degree (candidate rotation 5 (secondRoot (rotation := rotation) d) 3) = 6)
    (receiver : 7 ≤ G.degree d.snd) :
    d.fst ≠ (secondRoot (rotation := rotation) d).fst ∧
    7 ≤ net rotation d.fst d.snd +
      net rotation (secondRoot (rotation := rotation) d).fst d.snd := by
  obtain ⟨hne, h⟩ := joint_bound cyclic d left right sender five outer receiver
  refine ⟨hne, ?_⟩
  split_ifs at h <;> omega

section Star
variable [Fintype V]

noncomputable def pairRemainder (u w v : V) : ℤ :=
  ∑ z ∈ ((Finset.univ : Finset V).erase u).erase w, net rotation z v

omit [Finite V] [DecidableRel G.Adj] in
/-- Remove two distinct incoming contributions from the exact signed sum. -/
theorem remainder_balance {u w v : V} (hne : u ≠ w) :
    pairRemainder (rotation := rotation) u w v + net rotation u v + net rotation w v =
      ∑ z : V, net rotation z v := by
  have h := Finset.sum_erase_add (Finset.univ : Finset V)
    (fun z => net rotation z v) (Finset.mem_univ u)
  have h' := Finset.sum_erase_add ((Finset.univ : Finset V).erase u)
    (fun z => net rotation z v) (show w ∈ (Finset.univ : Finset V).erase u by simp [hne.symm])
  unfold pairRemainder
  omega

omit [Finite V] in
/-- The paired seven-unit bound leaves at most thirteen units elsewhere
at a flat degree-eight receiver. -/
theorem flat_pair_remainder (cyclic : rotation.IsVertexwiseCyclic) (d : G.Dart)
    (left : check rotation 4 d = true)
    (right : check rotation 5 (secondRoot (rotation := rotation) d) = true)
    (sender : G.degree d.fst = 5)
    (five : G.degree (candidate rotation 4 d 2) = 5)
    (outer : G.degree (candidate rotation 5 (secondRoot (rotation := rotation) d) 3) = 6)
    (eight : G.degree d.snd = 8) (flat : finalCharge rotation d.snd = 0) :
    pairRemainder (rotation := rotation) d.fst
      (secondRoot (rotation := rotation) d).fst d.snd ≤ 13 := by
  obtain ⟨hne, hseven⟩ := joint_seven cyclic d left right sender five outer (by omega)
  have hs := remainder_balance (rotation := rotation) (v := d.snd) hne
  have total : (∑ z : V, net rotation z d.snd) = 20 := by
    unfold finalCharge at flat
    rw [eight] at flat
    norm_num at flat
    omega
  rw [total] at hs
  omega

end Star
end FourColor.RulePairBudget
