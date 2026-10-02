import MettapediaFourColor.RulePairDiamond

/-!
# Gluing rule occurrences forces additional charge

The shared-five/outer-six branch of rules 003_2 and 004_1 carries more
information than two independent positive checks. When the second sender
has degree six and the receiver has degree at least seven, their union is
the entire oriented rule 006_1. Its witness keeps the actual shared vertices,
including the corner identified by cyclic closure.
-/

namespace FourColor.RulePairCharge

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData NearLinearCharge RuleMatcher RulePairDiamond
open scoped BigOperators

set_option maxRecDepth 65536

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

/-- Every edge and turn of the target is supplied by one of the two
source patterns. Degree conditions and agreement of actual readings are
separate obligations; this certificate never assumes independent choices. -/
structure GeometryCover (r s t : Fin 84)
    (l : Vertex r → Vertex t) (q : Vertex s → Vertex t) : Prop where
  edge : ∀ i j, (graph t).Adj i j →
    (∃ a b, l a = i ∧ l b = j ∧ (graph r).Adj a b) ∨
    (∃ a b, q a = i ∧ q b = j ∧ (graph s).Adj a b)
  turn : ∀ i j k, (graph t).Adj i j → (graph t).Adj i k → Turn t i j k →
    (∃ a b c, l a = i ∧ l b = j ∧ l c = k ∧
      (graph r).Adj a b ∧ (graph r).Adj a c ∧ Turn r a b c) ∨
    (∃ a b c, q a = i ∧ q b = j ∧ q c = k ∧
      (graph s).Adj a b ∧ (graph s).Adj a c ∧ Turn s a b c)

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] [G.LocallyFinite] {rotation : Data G}

/-- Glue full occurrences along agreeing vertex readings, with exact
target degrees. This retains genuine edge and rotation witnesses. -/
def glue {r s t : Fin 84} {l : Vertex r → Vertex t} {q : Vertex s → Vertex t}
    (cover : GeometryCover r s t l q) (x : Occurrence rotation r)
    (y : Occurrence rotation s) (f : Vertex t → V)
    (hl : ∀ i, f (l i) = x.vertex i) (hq : ∀ i, f (q i) = y.vertex i)
    (hd : ∀ i, lower t i ≤ G.degree (f i) ∧
      (upper t i = 0 ∨ G.degree (f i) ≤ upper t i)) : Occurrence rotation t :=
  occurrenceOfFits rotation f ⟨by
    intro i j hij
    rcases cover.edge i j hij with ⟨a, b, rfl, rfl, hab⟩ | ⟨a, b, rfl, rfl, hab⟩
    · simpa only [hl] using x.edge a b hab
    · simpa only [hq] using y.edge a b hab,
    hd, by
    intro i j k hij hik ht
    rcases cover.turn i j k hij hik ht with
      ⟨a, b, c, rfl, rfl, rfl, hab, hac, h⟩ |
      ⟨a, b, c, rfl, rfl, rfl, hab, hac, h⟩
    · simpa only [hl] using (fits_of_occurrence rotation x).2.2 a b c hab hac h
    · simpa only [hq] using (fits_of_occurrence rotation y).2.2 a b c hab hac h⟩

def leftMap (i : Vertex 4) : Vertex 9 := (![4, 1, 3, 5] : Fin 4 → Fin 6) i
def rightMap (i : Vertex 5) : Vertex 9 := (![0, 1, 3, 2, 5] : Fin 5 → Fin 6) i

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
-- Check every target edge and cyclic turn against the two small source patterns.
theorem pair_cover : GeometryCover 4 5 9 leftMap rightMap := by
  constructor <;> decide +kernel

def joinedVertices (x : Left rotation) (y : Right rotation) : Vertex 9 → V :=
  ![y.vertex 0, y.vertex 1, y.vertex 3, y.vertex 2, x.vertex 0, y.vertex 4]

/-- A full third occurrence is reconstructed from the two shared readings.
No ambient injectivity or upper bound on the receiver's degree is required. -/
def joined (x : Left rotation) (y : Right rotation)
    (centre : x.vertex 1 = y.vertex 1) (shared : x.vertex 2 = y.vertex 2)
    (corner : y.vertex 4 = x.vertex 3)
    (sender : G.degree (x.vertex 0) = 5) (five : G.degree (x.vertex 2) = 5)
    (outer : G.degree (y.vertex 3) = 6) (second : G.degree (y.vertex 0) = 6)
    (receiver : 7 ≤ G.degree (y.vertex 1)) : Occurrence rotation 9 := by
  apply glue pair_cover x y (joinedVertices x y)
  · intro i
    fin_cases i
    · exact rfl
    · exact centre.symm
    · exact shared.symm
    · exact corner
  · intro i
    fin_cases i <;> rfl
  · have tip := y.degree 4
    rw [show lower 5 4 = 5 from by decide +kernel,
      show upper 5 4 = 5 from by decide +kernel] at tip
    have sharedFive : G.degree (y.vertex 2) = 5 := shared ▸ five
    intro i
    fin_cases i
    · change 6 ≤ G.degree (y.vertex 0) ∧ (6 = 0 ∨ G.degree (y.vertex 0) ≤ 6)
      omega
    · change 7 ≤ G.degree (y.vertex 1) ∧ (0 = 0 ∨ G.degree (y.vertex 1) ≤ 0)
      exact ⟨receiver, Or.inl rfl⟩
    · change 6 ≤ G.degree (y.vertex 3) ∧ (6 = 0 ∨ G.degree (y.vertex 3) ≤ 6)
      omega
    · change 5 ≤ G.degree (y.vertex 2) ∧ (5 = 0 ∨ G.degree (y.vertex 2) ≤ 5)
      omega
    · change 5 ≤ G.degree (x.vertex 0) ∧ (5 = 0 ∨ G.degree (x.vertex 0) ≤ 5)
      omega
    · change 5 ≤ G.degree (y.vertex 4) ∧ (6 = 0 ∨ G.degree (y.vertex 4) ≤ 6)
      omega

variable [Finite V]

omit [Finite V] [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] in
theorem second_receiver (d : G.Dart) :
    (secondRoot (rotation := rotation) d).snd = d.snd := by
  have fst (e : G.Dart) : (rotation.vertexRotation.symm e).fst = e.fst := by
    have h := rotation.vertexRotation_fst (rotation.vertexRotation.symm e)
    simpa only [Equiv.apply_symm_apply] using h.symm
  change (rotation.vertexRotation.symm (rotation.vertexRotation.symm d.symm)).fst = d.snd
  rw [fst, fst]
  rfl

/-- The two executable checks force a third executable check on exactly
the second rooted edge. The third witness is assembled, not searched for. -/
theorem third_of_checks (cyclic : rotation.IsVertexwiseCyclic) (d : G.Dart)
    (left : check rotation 4 d = true)
    (right : check rotation 5 (secondRoot (rotation := rotation) d) = true)
    (sender : G.degree d.fst = 5)
    (five : G.degree (candidate rotation 4 d 2) = 5)
    (outer : G.degree (candidate rotation 5 (secondRoot (rotation := rotation) d) 3) = 6)
    (second : G.degree (secondRoot (rotation := rotation) d).fst = 6)
    (receiver : 7 ≤ G.degree d.snd) :
    check rotation 9 (secondRoot (rotation := rotation) d) = true := by
  obtain ⟨x, xs, xt⟩ := (check_iff rotation d).mp left
  obtain ⟨y, ys, yt⟩ := (check_iff rotation _).mp right
  obtain ⟨hc, hw⟩ := aligned x y d xs xt ys yt
  rw [candidate_eq rotation d x xs xt] at five
  rw [candidate_eq rotation _ y ys yt] at outer
  let z := joined x y hc hw (identified_corner x y cyclic hc hw five)
    (xs ▸ sender) five outer (ys ▸ second) (by rw [← hc]; exact xt ▸ receiver)
  exact (check_iff rotation _).mpr ⟨z, ys, yt⟩

set_option maxHeartbeats 1000000 in
-- Transport the small subpattern through the pinned rule decoder.
omit [Finite V] in
/-- Rule 006_1 contains rule 002_2 at the same marked edge. -/
theorem two_of_nine (d : G.Dart) (h : check rotation 9 d = true) :
    check rotation 2 d = true := by
  obtain ⟨z, zs, zt⟩ := (check_iff rotation d).mp h
  let m : Vertex 2 → Vertex 9 := ![0, 1, 3]
  have edges : ∀ i j, (graph 2).Adj i j → (graph 9).Adj (m i) (m j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have turns : ∀ i j k, Turn 2 i j k → Turn 9 (m i) (m j) (m k) := by
    intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel
  let w : Occurrence rotation 2 := {
    vertex := fun i => z.vertex (m i)
    edge := fun i j hij => z.edge _ _ (edges i j hij)
    turn := fun i j k hij hik ht => z.turn _ _ _
      (edges i j hij) (edges i k hik) (turns i j k ht)
    degree := by
      intro i
      fin_cases i
      · have h := z.degree 0
        change 6 ≤ G.degree (z.vertex 0) ∧ (6 = 0 ∨ G.degree (z.vertex 0) ≤ 6) at h
        change 5 ≤ G.degree (z.vertex 0) ∧ (6 = 0 ∨ G.degree (z.vertex 0) ≤ 6)
        omega
      · have h := z.degree 1
        rw [show lower 9 1 = 7 from by decide +kernel] at h
        change 7 ≤ G.degree (z.vertex 1) ∧ (0 = 0 ∨ G.degree (z.vertex 1) ≤ 0)
        exact ⟨h.1, Or.inl rfl⟩
      · have h := z.degree 3
        rw [show lower 9 3 = 5 from by decide +kernel,
          show upper 9 3 = 5 from by decide +kernel] at h
        change 5 ≤ G.degree (z.vertex 3) ∧ (5 = 0 ∨ G.degree (z.vertex 3) ≤ 5)
        exact h }
  exact (check_iff rotation d).mpr ⟨w, zs, zt⟩

omit [Finite V] in
/-- Sum only distinct certified source rules; other contributions are
nonnegative. Witness multiplicities do not multiply a rule's charge. -/
theorem charge_lower (d : G.Dart) (s : Finset (Fin 84))
    (h : ∀ r ∈ s, check rotation r d = true) :
    (∑ r ∈ s, (amount r : ℤ)) ≤ sentAt rotation d := by
  have hs : (∑ r ∈ s, (amount r : ℤ)) =
      ∑ r ∈ s, if check rotation r d then (amount r : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [h r hr, ite_true]
  rw [hs]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
  intro r _ _
  split <;> positivity

omit [Finite V] in
/-- The full joined occurrence and the original right rule contribute
three distinct units on the second edge. -/
theorem three_of_checks (d : G.Dart) (h5 : check rotation 5 d = true)
    (h9 : check rotation 9 d = true) : 3 ≤ sentAt rotation d := by
  have h2 := two_of_nine d h9
  have h := charge_lower d {2, 5, 9} (by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact h2
    · exact h5
    · exact h9)
  have total : (∑ r ∈ ({2, 5, 9} : Finset (Fin 84)), (amount r : ℤ)) = 3 := by
    decide +kernel
  rw [total] at h
  exact h

set_option maxHeartbeats 0 in
-- Exhaust the 84 pinned rules, checking only their endpoint degree intervals.
theorem endpoint_separation : ∀ r : Fin 84,
    upper r (NearLinearRuleData.sender r) ≤ 6 ∨
    7 ≤ lower r (NearLinearRuleData.receiver r) := by
  intro r
  fin_cases r <;> decide +kernel

omit [Finite V] [DecidableEq V] [DecidableRel G.Adj] in
/-- No pinned rule sends charge from a degree-at-least-seven vertex to
a degree-at-most-six vertex. This controls the reverse transfer. -/
theorem high_to_low_zero {u v : V} (hu : 7 ≤ G.degree u) (hv : G.degree v ≤ 6) :
    sent rotation u v = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro r _
  have hn : ¬ Applies rotation r u v := by
    rintro ⟨x, xs, xt⟩
    have hs := x.degree (NearLinearRuleData.sender r)
    have ht := x.degree (NearLinearRuleData.receiver r)
    rw [xs] at hs
    rw [xt] at ht
    have hb := (sender_bound r).1
    rcases endpoint_separation r with h | h <;> omega
  exact ite_eq_right hn

omit [Finite V] in
/-- The three units are net incoming charge: the reverse direction has
zero contribution under the actual endpoint degrees of rule 006_1. -/
theorem net_three (d : G.Dart) (h5 : check rotation 5 d = true)
    (h9 : check rotation 9 d = true) : 3 ≤ net rotation d.fst d.snd := by
  obtain ⟨z, zs, zt⟩ := (check_iff rotation d).mp h9
  have hs := z.degree 0
  have ht := z.degree 1
  rw [show upper 9 0 = 6 from by decide +kernel] at hs
  rw [show lower 9 1 = 7 from by decide +kernel] at ht
  have hz := high_to_low_zero (rotation := rotation)
    (u := d.snd) (v := d.fst) (zt ▸ ht.1) (zs ▸ (by omega : G.degree (z.vertex 0) ≤ 6))
  have h := three_of_checks d h5 h9
  rw [sentAt_eq] at h
  simpa only [net, hz, sub_zero] using h

/-- One structural law covers both reducible branches and supplies a
quantitative alternative in the residual branch. -/
theorem reduction_or_charge (cyclic : rotation.IsVertexwiseCyclic)
    (tri : ExceptionalOverlap.Triangular rotation) (d : G.Dart)
    (left : check rotation 4 d = true)
    (right : check rotation 5 (secondRoot (rotation := rotation) d) = true)
    (sender : G.degree d.fst = 5)
    (second : G.degree (secondRoot (rotation := rotation) d).fst = 6)
    (receiver : 7 ≤ G.degree d.snd) :
    (∃ e : G.Dart, MixedAt rotation e) ∨
    (∃ e : G.Dart, PentagonalAt rotation e) ∨
    (check rotation 9 (secondRoot (rotation := rotation) d) = true ∧
      3 ≤ sentAt rotation (secondRoot (rotation := rotation) d)) := by
  rcases pair_alternatives cyclic tri d left right sender with hm | hp | ⟨hf, ho⟩
  · exact Or.inl hm
  · exact Or.inr (Or.inl hp)
  · have h9 := third_of_checks cyclic d left right sender hf ho second receiver
    exact Or.inr (Or.inr ⟨h9, three_of_checks _ right h9⟩)

section Star

variable [Fintype V]

/-- Net supply from every vertex except the specified sender. All other
positive and negative transfers remain in this exact remainder. -/
noncomputable def remainingSupply (u v : V) : ℤ :=
  ∑ w ∈ (Finset.univ : Finset V).erase u, net rotation w v

omit [Finite V] in
/-- A flat degree-eight receiver needs twenty units in total. The
certified three-unit edge leaves at most seventeen for the rest of its star. -/
theorem flat_remainder (d : G.Dart) (eight : G.degree d.snd = 8)
    (flat : finalCharge rotation d.snd = 0)
    (h5 : check rotation 5 d = true) (h9 : check rotation 9 d = true) :
    remainingSupply (rotation := rotation) d.fst d.snd ≤ 17 := by
  have h := net_three d h5 h9
  have split := Finset.sum_erase_add (Finset.univ : Finset V)
    (fun w => net rotation w d.snd) (Finset.mem_univ d.fst)
  have total : (∑ w : V, net rotation w d.snd) = 20 := by
    unfold finalCharge at flat
    rw [eight] at flat
    norm_num at flat
    omega
  rw [total] at split
  change (∑ w ∈ (Finset.univ : Finset V).erase d.fst, net rotation w d.snd) ≤ 17
  omega

end Star

end FourColor.RulePairCharge
