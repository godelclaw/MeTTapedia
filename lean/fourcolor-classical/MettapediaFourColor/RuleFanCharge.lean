import MettapediaFourColor.RuleFanSupply
import MettapediaFourColor.RulePairBudget

/-!
# Charge forced by two sides of a six-valent fan

Two consecutive degree-five neighbours on each side of a marked edge
force compatible occurrences of the two orientations of rule 003.
The adjacent five-valent senders retain these same facial witnesses.
The resulting signed budget will be used at the second centre of a fan.
-/

namespace FourColor.RuleFanCharge

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData NearLinearCharge RuleMatcher RulePairCharge RulePairBudget
open ExceptionalCoreOrientation ExceptionalOverlap
open ChainFanRecognition (walk walk_fst walk_next)
open scoped BigOperators

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

def swapSide : Vertex 3 → Vertex 4 := ![2, 1, 0, 3]

theorem swap_pattern : Subpattern 3 4 swapSide := by
  constructor <;> decide +kernel

theorem four_edges : ∀ i j : Vertex 4, (graph 4).Adj i j →
    (i, j) ∈ ([(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0),
      (1, 2), (2, 1), (2, 3), (3, 2)] : List (Vertex 4 × Vertex 4)) := by
  decide +kernel

theorem four_turns : ∀ i j k : Vertex 4, Turn 4 i j k →
    (i, j, k) ∈ ([(0, 1, 2), (1, 2, 0), (2, 0, 1),
      (0, 2, 3), (2, 3, 0), (3, 0, 2)] : List (Vertex 4 × Vertex 4 × Vertex 4)) := by
  decide +kernel

theorem one_edges : ∀ i j : Vertex 1, (graph 1).Adj i j →
    (i, j) ∈ ([(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)] :
      List (Vertex 1 × Vertex 1)) := by decide +kernel

theorem one_turns : ∀ i j k : Vertex 1, Turn 1 i j k →
    (i, j, k) ∈ ([(0, 1, 2), (1, 2, 0), (2, 0, 1)] :
      List (Vertex 1 × Vertex 1 × Vertex 1)) := by decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] [G.LocallyFinite] {rotation : Data G}

/-- Read the entire oriented source rule from two actual facial triangles. -/
def ofTwoFaces (tri : Triangular rotation) {a b c e : V}
    (abc : Corner rotation a b c) (ace : Corner rotation a c e)
    (ha : 5 ≤ G.degree a ∧ G.degree a ≤ 6) (hb : 5 ≤ G.degree b)
    (hc : 5 ≤ G.degree c ∧ G.degree c ≤ 6) (he : G.degree e = 5) :
    Occurrence rotation 4 := by
  have bca := Corner.rotate rotation tri abc
  have cab := Corner.rotate rotation tri bca
  have cea := Corner.rotate rotation tri ace
  have eac := Corner.rotate rotation tri cea
  let f : Vertex 4 → V := ![a, b, c, e]
  refine occurrenceOfFits rotation f ⟨?_, ?_, ?_⟩
  · intro i j hij
    have h := four_edges i j hij
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact abc.choose
    · exact abc.choose.symm
    · exact ace.choose
    · exact ace.choose.symm
    · exact ace.choose_spec.choose
    · exact ace.choose_spec.choose.symm
    · exact bca.choose
    · exact bca.choose.symm
    · exact cea.choose
    · exact cea.choose.symm
  · intro i
    fin_cases i
    · change 5 ≤ G.degree a ∧ (6 = 0 ∨ G.degree a ≤ 6); omega
    · change 5 ≤ G.degree b ∧ (0 = 0 ∨ G.degree b ≤ 0); omega
    · change 5 ≤ G.degree c ∧ (6 = 0 ∨ G.degree c ≤ 6); omega
    · change 5 ≤ G.degree e ∧ (5 = 0 ∨ G.degree e ≤ 5); omega
  · intro i j k _ _ ht
    have h := four_turns i j k ht
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
      ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    all_goals apply goodTurn_of
    · exact abc.choose_spec.choose_spec
    · exact bca.choose_spec.choose_spec
    · exact cab.choose_spec.choose_spec
    · exact ace.choose_spec.choose_spec
    · exact cea.choose_spec.choose_spec
    · exact eac.choose_spec.choose_spec

/-- The one-unit triangle rule also keeps all three cyclic turns. -/
def ofFace (tri : Triangular rotation) {a b c : V}
    (abc : Corner rotation a b c) (ha : 5 ≤ G.degree a ∧ G.degree a ≤ 6)
    (hb : 7 ≤ G.degree b) (hc : G.degree c = 5) : Occurrence rotation 1 := by
  have bca := Corner.rotate rotation tri abc
  have cab := Corner.rotate rotation tri bca
  let f : Vertex 1 → V := ![a, b, c]
  refine occurrenceOfFits rotation f ⟨?_, ?_, ?_⟩
  · intro i j hij
    have h := one_edges i j hij
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact abc.choose
    · exact abc.choose.symm
    · exact abc.choose_spec.choose
    · exact abc.choose_spec.choose.symm
    · exact bca.choose
    · exact bca.choose.symm
  · intro i
    fin_cases i
    · change 5 ≤ G.degree a ∧ (6 = 0 ∨ G.degree a ≤ 6); omega
    · change 7 ≤ G.degree b ∧ (0 = 0 ∨ G.degree b ≤ 0); omega
    · change 5 ≤ G.degree c ∧ (5 = 0 ∨ G.degree c ≤ 5); omega
  · intro i j k _ _ ht
    have h := one_turns i j k ht
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    all_goals apply goodTurn_of
    · exact abc.choose_spec.choose_spec
    · exact bca.choose_spec.choose_spec
    · exact cab.choose_spec.choose_spec

/-- The reflected triangle uses the same actual vertices, in reverse order. -/
def ofReverseFace (tri : Triangular rotation) {a b c : V}
    (acb : Corner rotation a c b) (ha : 5 ≤ G.degree a ∧ G.degree a ≤ 6)
    (hb : 7 ≤ G.degree b) (hc : G.degree c = 5) : Occurrence rotation 2 := by
  have cba := Corner.rotate rotation tri acb
  have bac := Corner.rotate rotation tri cba
  let f : Vertex 2 → V := ![a, b, c]
  have edges : ∀ i j : Vertex 2, (graph 2).Adj i j →
      (i,j) ∈ ([(0,1),(1,0),(0,2),(2,0),(1,2),(2,1)] : List (Vertex 2 × Vertex 2)) := by
    decide +kernel
  have turns : ∀ i j k : Vertex 2, Turn 2 i j k →
      (i,j,k) ∈ ([(0,2,1),(2,1,0),(1,0,2)] : List (Vertex 2 × Vertex 2 × Vertex 2)) := by
    decide +kernel
  refine occurrenceOfFits rotation f ⟨?_, ?_, ?_⟩
  · intro i j hij
    have h := edges i j hij
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact acb.choose_spec.choose
    · exact acb.choose_spec.choose.symm
    · exact acb.choose
    · exact acb.choose.symm
    · exact cba.choose.symm
    · exact cba.choose
  · intro i
    fin_cases i
    · change 5 ≤ G.degree a ∧ (6 = 0 ∨ G.degree a ≤ 6); omega
    · change 7 ≤ G.degree b ∧ (0 = 0 ∨ G.degree b ≤ 0); omega
    · change 5 ≤ G.degree c ∧ (5 = 0 ∨ G.degree c ≤ 5); omega
  · intro i j k _ _ ht
    have h := turns i j k ht
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    all_goals apply goodTurn_of
    · exact acb.choose_spec.choose_spec
    · exact cba.choose_spec.choose_spec
    · exact bac.choose_spec.choose_spec

/-- Swapping the two low-degree ends of the common diagonal exchanges
the two oriented source rules, without changing the shared boundary. -/
def swapped (x : Occurrence rotation 4) : Occurrence rotation 3 :=
  restrict swap_pattern x (by
    intro i
    fin_cases i
    · have h := x.degree 2
      rw [show lower 4 2 = 5 from by decide +kernel,
        show upper 4 2 = 6 from by decide +kernel] at h
      change 5 ≤ G.degree (x.vertex 2) ∧ (6 = 0 ∨ G.degree (x.vertex 2) ≤ 6)
      exact h
    · have h := x.degree 1
      rw [show lower 4 1 = 5 from by decide +kernel,
        show upper 4 1 = 0 from by decide +kernel] at h
      change 5 ≤ G.degree (x.vertex 1) ∧ (0 = 0 ∨ G.degree (x.vertex 1) ≤ 0)
      exact h
    · have h := x.degree 0
      rw [show lower 4 0 = 5 from by decide +kernel,
        show upper 4 0 = 6 from by decide +kernel] at h
      change 5 ≤ G.degree (x.vertex 0) ∧ (6 = 0 ∨ G.degree (x.vertex 0) ≤ 6)
      exact h
    · have h := x.degree 3
      rw [show lower 4 3 = 5 from by decide +kernel,
        show upper 4 3 = 5 from by decide +kernel] at h
      change 5 ≤ G.degree (x.vertex 3) ∧ (5 = 0 ∨ G.degree (x.vertex 3) ≤ 5)
      exact h)

omit [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] in
/-- Every consecutive pair of actual outgoing darts supplies a face corner. -/
theorem walk_corner (d : G.Dart) (n : ℕ) :
    Corner rotation d.fst (walk rotation d n).snd (walk rotation d (n+1)).snd := by
  have adj (m : ℕ) : G.Adj d.fst (walk rotation d m).snd := by
    simpa only [walk_fst] using (walk rotation d m).adj
  have eq (m : ℕ) : (⟨(d.fst, (walk rotation d m).snd), adj m⟩ : G.Dart) =
      walk rotation d m := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext (walk_fst rotation d m).symm rfl
  refine ⟨adj _, adj _, ?_⟩
  rw [eq, eq, walk_next]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Construct rules 003_2 on the central edge and 003_1 on its adjacent
edge from the same two triangles. Both readings are used in the charge sum. -/
theorem face_checks (tri : Triangular rotation) {a b c e : V}
    (abc : Corner rotation a b c) (ace : Corner rotation a c e)
    (ha : 5 ≤ G.degree a ∧ G.degree a ≤ 6) (hb : 5 ≤ G.degree b)
    (hc : 5 ≤ G.degree c ∧ G.degree c ≤ 6) (he : G.degree e = 5) :
    Applies rotation 4 a b ∧ Applies rotation 3 c b := by
  classical
  let x := ofTwoFaces tri abc ace ha hb hc he
  exact ⟨⟨x, rfl, rfl⟩, ⟨swapped x, rfl, rfl⟩⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A list of distinct source rules gives a lower bound on actual sent charge. -/
theorem sent_lower {u v : V} (s : Finset (Fin 84))
    (h : ∀ r ∈ s, Applies rotation r u v) :
    (∑ r ∈ s, (amount r : ℤ)) ≤ sent rotation u v := by
  classical
  have hs : (∑ r ∈ s, (amount r : ℤ)) =
      ∑ r ∈ s, if Applies rotation r u v then (amount r : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [h r hr, ite_true]
  rw [hs]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
  intro r _ _
  split <;> positivity

omit [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite] in
theorem prev_fst (d : G.Dart) : (rotation.vertexRotation.symm d).fst = d.fst := by
  have h := rotation.vertexRotation_fst (rotation.vertexRotation.symm d)
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- Four observed fives around the same actual sender. No independent
occurrences or independently selected boundary labels are supplied. -/
structure Wings (d : G.Dart) : Prop where
  six : G.degree d.fst = 6
  next : G.degree (rotation.vertexRotation d).snd = 5
  nextNext : G.degree (rotation.vertexRotation (rotation.vertexRotation d)).snd = 5
  prev : G.degree (rotation.vertexRotation.symm d).snd = 5
  prevPrev : G.degree (rotation.vertexRotation.symm (rotation.vertexRotation.symm d)).snd = 5

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Three incoming edges receive at least 3,4,3 units from one shared fan. -/
theorem three_senders (tri : Triangular rotation) (d : G.Dart) (h : Wings (rotation := rotation) d)
    (high : 7 ≤ G.degree d.snd) :
    3 ≤ sent rotation (rotation.vertexRotation d).snd d.snd ∧
    4 ≤ sent rotation d.fst d.snd ∧
    3 ≤ sent rotation (rotation.vertexRotation.symm d).snd d.snd := by
  classical
  have six := h.six
  have next := h.next
  have prev := h.prev
  let p := rotation.vertexRotation.symm d
  let q := rotation.vertexRotation.symm p
  have c0 : Corner rotation d.fst d.snd (rotation.vertexRotation d).snd := walk_corner d 0
  have c1 : Corner rotation d.fst (rotation.vertexRotation d).snd
      (rotation.vertexRotation (rotation.vertexRotation d)).snd := walk_corner d 1
  have cp : Corner rotation d.fst p.snd d.snd := by
    simpa only [walk, Nat.zero_add, pow_zero, pow_one, Equiv.Perm.one_apply,
      p, prev_fst, Equiv.apply_symm_apply] using walk_corner (rotation := rotation) p 0
  have cq : Corner rotation d.fst q.snd p.snd := by
    simpa only [walk, Nat.zero_add, pow_zero, pow_one, Equiv.Perm.one_apply,
      q, p, prev_fst, Equiv.apply_symm_apply] using walk_corner (rotation := rotation) q 0
  have hl := face_checks tri c0 c1 ⟨by omega, by omega⟩ (by omega) ⟨by omega, by omega⟩ h.nextNext
  have rightPair := face_checks tri (Corner.rotate rotation tri cp)
    (Corner.rotate rotation tri (Corner.rotate rotation tri cq))
    ⟨le_of_eq h.prev.symm,
      by change G.degree (rotation.vertexRotation.symm d).snd ≤ 6; omega⟩
    (by omega) ⟨by omega, by omega⟩ (by exact h.prevPrev)
  have h1 : Applies rotation 1 d.fst d.snd :=
    ⟨ofFace tri c0 ⟨by omega, by omega⟩ high h.next, rfl, rfl⟩
  have h2 : Applies rotation 2 d.fst d.snd :=
    ⟨ofReverseFace tri cp ⟨by omega, by omega⟩ high h.prev, rfl, rfl⟩
  have z (v : V) (hv : G.degree v = 5) (adj : G.Adj v d.snd) :
      Applies rotation 0 v d.snd :=
    (check_iff rotation ⟨(v,d.snd),adj⟩).mp
      (zero_of_five _ hv (by change 5 ≤ G.degree d.snd; omega))
  have zl := z _ h.next (Corner.rotate rotation tri c0).choose.symm
  have zr := z _ h.prev (Corner.rotate rotation tri cp).choose
  have l := sent_lower {0,3} (by
    intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact zl
    · exact hl.2)
  have m := sent_lower {1,2,3,4} (by
    intro r hr; simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact rightPair.2
    · exact hl.1)
  have r := sent_lower {0,4} (by
    intro r hr'; simp only [Finset.mem_insert, Finset.mem_singleton] at hr'
    rcases hr' with rfl | rfl
    · exact zr
    · exact rightPair.1)
  have suml : (∑ r ∈ ({0,3} : Finset (Fin 84)), (amount r : ℤ)) = 3 := by decide +kernel
  have summ : (∑ r ∈ ({1,2,3,4} : Finset (Fin 84)), (amount r : ℤ)) = 4 := by decide +kernel
  have sumr : (∑ r ∈ ({0,4} : Finset (Fin 84)), (amount r : ℤ)) = 3 := by decide +kernel
  rw [suml] at l
  rw [summ] at m
  rw [sumr] at r
  exact ⟨l,m,r⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The surviving first free position has two five-valent neighbours
on each side when the other free position is five. -/
theorem wings_at_first_free (d : G.Dart) (h : RuleFanSupply.Fixed rotation d)
    (five : G.degree (RuleFanSupply.secondFree rotation d) = 5) :
    Wings (rotation := rotation) (walk rotation d 3) := by
  have prev (n : ℕ) : rotation.vertexRotation.symm (walk rotation d (n+1)) =
      walk rotation d n := by rw [← walk_next, Equiv.symm_apply_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [walk_fst]; exact h.center
  · rw [walk_next]; exact five
  · rw [walk_next, walk_next]; exact h.last
  · rw [prev]; exact h.second
  · rw [prev, prev]; exact h.first

variable [Fintype V]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Complete the 3,4,3 budget by the two neighbouring facial triangles.
All other signed transfers are nonnegative under the stated degree guard. -/
theorem window_positive (cyclic : rotation.IsVertexwiseCyclic) (tri : Triangular rotation)
    (e : G.Dart) (seven : G.degree e.fst = 7)
    (low : ∀ v, G.Adj e.fst v → 5 ≤ G.degree v ∧ G.degree v ≤ 6)
    (five1 : G.degree (walk rotation e 1).snd = 5)
    (five3 : G.degree (walk rotation e 3).snd = 5)
    (left : 3 ≤ sent rotation (walk rotation e 1).snd e.fst)
    (middle : 4 ≤ sent rotation (walk rotation e 2).snd e.fst)
    (right : 3 ≤ sent rotation (walk rotation e 3).snd e.fst) :
    2 ≤ finalCharge rotation e.fst := by
  classical
  let ns (i : Fin 5) := (walk rotation e i.val).snd
  have adj (i : Fin 5) : G.Adj e.fst (ns i) := by
    simpa only [ns, walk_fst] using (walk rotation e i.val).adj
  have inj : Function.Injective ns := by
    apply ExceptionalCoreLocalInjectivity.corner_chain_injective rotation cyclic e.fst
      (by decide) ns adj
    · intro i hi
      exact walk_corner e i
    · omega
  have c0 := Corner.rotate rotation tri (walk_corner e 0)
  have c3 := Corner.rotate rotation tri (Corner.rotate rotation tri (walk_corner e 3))
  have a0 : Applies rotation 2 (ns 0) e.fst :=
    ⟨ofReverseFace tri c0 (low _ (adj 0)) (by omega) five1, rfl, rfl⟩
  have a4 : Applies rotation 1 (ns 4) e.fst :=
    ⟨ofFace tri c3 (low _ (adj 4)) (by omega) five3, rfl, rfl⟩
  have h0 : 1 ≤ sent rotation (ns 0) e.fst := by
    have h := sent_lower {2} (by intro r hr; simpa using (Finset.mem_singleton.mp hr) ▸ a0)
    have hs : (∑ r ∈ ({2} : Finset (Fin 84)), (amount r : ℤ)) = 1 := by decide +kernel
    rwa [hs] at h
  have h4 : 1 ≤ sent rotation (ns 4) e.fst := by
    have h := sent_lower {1} (by intro r hr; simpa using (Finset.mem_singleton.mp hr) ▸ a4)
    have hs : (∑ r ∈ ({1} : Finset (Fin 84)), (amount r : ℤ)) = 1 := by decide +kernel
    rwa [hs] at h
  have zero (v : V) : sent rotation e.fst v = 0 := by
    by_cases hv : G.Adj e.fst v
    · exact high_to_low_zero (by omega) (low v hv).2
    · exact sent_eq_zero_of_not_adj rotation hv
  have nonneg (v : V) : 0 ≤ net rotation v e.fst := by
    simpa only [net, zero, sub_zero] using sent_nonneg rotation v e.fst
  have bounds (i : Fin 5) : (![1,3,4,3,1] : Fin 5 → ℤ) i ≤ net rotation (ns i) e.fst := by
    rw [net, zero, sub_zero]
    fin_cases i
    · exact h0
    · exact left
    · exact middle
    · exact right
    · exact h4
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => bounds i)
  have total : (∑ i : Fin 5, (![1,3,4,3,1] : Fin 5 → ℤ) i) = 12 := by decide +kernel
  rw [total] at hs
  have same : (∑ v ∈ Finset.univ.image ns, net rotation v e.fst) =
      ∑ i : Fin 5, net rotation (ns i) e.fst :=
    Finset.sum_image (fun i _ j _ h => inj h)
  have le := Finset.sum_le_univ_sum_of_nonneg (s := Finset.univ.image ns)
    (f := fun v => net rotation v e.fst) nonneg
  rw [same] at le
  unfold finalCharge
  rw [seven]
  norm_num
  omega

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The fan gives strictly positive charge when every receiver neighbour is low. -/
theorem positive_of_low (cyclic : rotation.IsVertexwiseCyclic)
    (tri : Triangular rotation) (d : G.Dart) (h : Wings (rotation := rotation) d)
    (seven : G.degree d.snd = 7)
    (low : ∀ v, G.Adj d.snd v → 5 ≤ G.degree v ∧ G.degree v ≤ 6) :
    2 ≤ finalCharge rotation d.snd := by
  classical
  let e := rotation.vertexRotation.symm (rotation.vertexRotation.symm d.symm)
  have ef : e.fst = d.snd := by simp only [e, prev_fst]; rfl
  have e1 : walk rotation e 1 = rotation.vertexRotation.symm d.symm := by
    simp only [walk, e, pow_one, Equiv.apply_symm_apply]
  have e2 : walk rotation e 2 = d.symm := by
    simp only [walk, e, pow_succ', pow_zero, Equiv.Perm.mul_apply,
      Equiv.Perm.one_apply, Equiv.apply_symm_apply]
  have e3 : walk rotation e 3 = rotation.vertexRotation d.symm := by
    rw [← walk_next, e2]
  have el : (walk rotation e 1).snd = (rotation.vertexRotation d).snd := by
    rw [e1, FacialStarCompletion.across_edge rotation tri, SimpleGraph.Dart.symm_symm]
  have er : (walk rotation e 3).snd = (rotation.vertexRotation.symm d).snd := by
    rw [e3, ← FacialStarCompletion.across_edge rotation tri]
  obtain ⟨left, middle, right⟩ := three_senders tri d h (by omega)
  have positive := window_positive cyclic tri e (ef ▸ seven) (by simpa only [ef] using low)
    (el ▸ h.next) (er ▸ h.prev)
    (by simpa only [ef, el] using left)
    (by rw [ef, e2]; exact middle)
    (by simpa only [ef, er] using right)
  simpa only [ef] using positive

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A flat degree-seven receiver of the fan has a high-degree neighbour.
This replaces an unchecked centre-walk step by an actual charge constraint. -/
theorem flat_has_high_neighbor (cyclic : rotation.IsVertexwiseCyclic)
    (tri : Triangular rotation) (d : G.Dart) (h : Wings (rotation := rotation) d)
    (seven : G.degree d.snd = 7) (flat : finalCharge rotation d.snd = 0)
    (minimum : ∀ v, G.Adj d.snd v → 5 ≤ G.degree v) :
    ∃ v, G.Adj d.snd v ∧ 7 ≤ G.degree v := by
  classical
  by_contra hn
  push Not at hn
  have low (v : V) (hv : G.Adj d.snd v) : 5 ≤ G.degree v ∧ G.degree v ≤ 6 :=
    ⟨minimum v hv, by have := hn v hv; omega⟩
  have hpos := positive_of_low cyclic tri d h seven low
  rw [flat] at hpos
  omega

end FourColor.RuleFanCharge
