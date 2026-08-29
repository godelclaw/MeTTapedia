import KrennFactorization

open SimpleGraph

namespace Krenn

namespace K4

abbrev Graph : SimpleGraph (Fin 4) := ⊤

def edge (u v : Fin 4) (h : u ≠ v) : Graph.edgeSet :=
  ⟨s(u, v), by simpa using h⟩

def M0 : Finset Graph.edgeSet :=
  {edge 0 1 (by decide), edge 2 3 (by decide)}

def M1 : Finset Graph.edgeSet :=
  {edge 0 2 (by decide), edge 1 3 (by decide)}

def M2 : Finset Graph.edgeSet :=
  {edge 0 3 (by decide), edge 1 2 (by decide)}

instance : DecidablePred (IsPMFinset Graph) := decidableIsPMFinset

theorem perfect_matchings_computable :
    Finset.univ.filter (IsPMFinset Graph) = {M0, M1, M2} := by
  decide

open scoped Classical in
theorem perfect_matchings :
    Finset.univ.filter (IsPMFinset Graph) = {M0, M1, M2} := by
  ext M
  have h := Finset.ext_iff.mp perfect_matchings_computable M
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem isPMFinset_iff (M : Finset Graph.edgeSet) :
    IsPMFinset Graph M ↔
      M ∈ ({M0, M1, M2} : Finset (Finset Graph.edgeSet)) := by
  have h := Finset.ext_iff.mp perfect_matchings_computable M
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h

def witness : WeightSystem Graph 3 := fun e i j =>
  if i = j ∧
      ((i = 0 ∧ e ∈ M0) ∨ (i = 1 ∧ e ∈ M1) ∨ (i = 2 ∧ e ∈ M2))
  then 1 else 0

theorem disjoint_M0_M1 : Disjoint M0 M1 := by decide
theorem disjoint_M0_M2 : Disjoint M0 M2 := by decide
theorem disjoint_M1_M2 : Disjoint M1 M2 := by decide
theorem M0_ne_M1 : M0 ≠ M1 := by decide
theorem M0_ne_M2 : M0 ≠ M2 := by decide
theorem M1_ne_M2 : M1 ≠ M2 := by decide

theorem isPM_M0 : IsPMFinset Graph M0 := by decide
theorem isPM_M1 : IsPMFinset Graph M1 := by decide
theorem isPM_M2 : IsPMFinset Graph M2 := by decide

private theorem constant_of_product_ne_zero
    (M : Finset Graph.edgeSet) (hPM : IsPMFinset Graph M) (c : Fin 3)
    (ι : Fin 4 → Fin 3)
    (hedge : ∀ e ∈ M, edgeWeight witness ι e ≠ 0 →
      ι (e : Sym2 (Fin 4)).inf = c ∧ ι (e : Sym2 (Fin 4)).sup = c)
    (hprod : ∏ e ∈ M, edgeWeight witness ι e ≠ 0) :
    ι = fun _ => c := by
  funext v
  obtain ⟨e, ⟨heM, hve⟩, _⟩ := hPM v
  have hweight := Finset.prod_ne_zero_iff.mp hprod e heM
  rcases mem_iff_eq_inf_or_sup.mp hve with rfl | rfl
  · exact (hedge e heM hweight).1
  · exact (hedge e heM hweight).2

private theorem constant_zero_of_M0_product_ne_zero (ι : Fin 4 → Fin 3)
    (hprod : ∏ e ∈ M0, edgeWeight witness ι e ≠ 0) :
    ι = fun _ => 0 := by
  apply constant_of_product_ne_zero M0 isPM_M0 0 ι _ hprod
  intro e heM hweight
  have hn1 : e ∉ M1 := Finset.disjoint_left.mp disjoint_M0_M1 heM
  have hn2 : e ∉ M2 := Finset.disjoint_left.mp disjoint_M0_M2 heM
  simp [edgeWeight, witness, heM, hn1, hn2] at hweight
  exact ⟨hweight.2, hweight.1.symm.trans hweight.2⟩

private theorem constant_one_of_M1_product_ne_zero (ι : Fin 4 → Fin 3)
    (hprod : ∏ e ∈ M1, edgeWeight witness ι e ≠ 0) :
    ι = fun _ => 1 := by
  apply constant_of_product_ne_zero M1 isPM_M1 1 ι _ hprod
  intro e heM hweight
  have hn0 : e ∉ M0 := fun he0 =>
    Finset.disjoint_left.mp disjoint_M0_M1 he0 heM
  have hn2 : e ∉ M2 := Finset.disjoint_left.mp disjoint_M1_M2 heM
  simp [edgeWeight, witness, heM, hn0, hn2] at hweight
  exact ⟨hweight.2, hweight.1.symm.trans hweight.2⟩

private theorem constant_two_of_M2_product_ne_zero (ι : Fin 4 → Fin 3)
    (hprod : ∏ e ∈ M2, edgeWeight witness ι e ≠ 0) :
    ι = fun _ => 2 := by
  apply constant_of_product_ne_zero M2 isPM_M2 2 ι _ hprod
  intro e heM hweight
  have hn0 : e ∉ M0 := fun he0 =>
    Finset.disjoint_left.mp disjoint_M0_M2 he0 heM
  have hn1 : e ∉ M1 := fun he1 =>
    Finset.disjoint_left.mp disjoint_M1_M2 he1 heM
  simp [edgeWeight, witness, heM, hn0, hn1] at hweight
  exact ⟨hweight.2, hweight.1.symm.trans hweight.2⟩

private theorem product_M0 (ι : Fin 4 → Fin 3) :
    (∏ e ∈ M0, edgeWeight witness ι e) = if ι = fun _ => 0 then 1 else 0 := by
  by_cases h : ι = fun _ => 0
  · subst ι
    rw [if_pos rfl]
    exact Finset.prod_eq_one fun e he => by simp [edgeWeight, witness, he]
  · have hz : (∏ e ∈ M0, edgeWeight witness ι e) = 0 := by
      by_contra hn
      exact h (constant_zero_of_M0_product_ne_zero ι hn)
    simp [h, hz]

private theorem product_M1 (ι : Fin 4 → Fin 3) :
    (∏ e ∈ M1, edgeWeight witness ι e) = if ι = fun _ => 1 then 1 else 0 := by
  by_cases h : ι = fun _ => 1
  · subst ι
    rw [if_pos rfl]
    exact Finset.prod_eq_one fun e he => by simp [edgeWeight, witness, he]
  · have hz : (∏ e ∈ M1, edgeWeight witness ι e) = 0 := by
      by_contra hn
      exact h (constant_one_of_M1_product_ne_zero ι hn)
    simp [h, hz]

private theorem product_M2 (ι : Fin 4 → Fin 3) :
    (∏ e ∈ M2, edgeWeight witness ι e) = if ι = fun _ => 2 then 1 else 0 := by
  by_cases h : ι = fun _ => 2
  · subst ι
    rw [if_pos rfl]
    exact Finset.prod_eq_one fun e he => by simp [edgeWeight, witness, he]
  · have hz : (∏ e ∈ M2, edgeWeight witness ι e) = 0 := by
      by_contra hn
      exact h (constant_two_of_M2_product_ne_zero ι hn)
    simp [h, hz]

theorem pmSum_witness (ι : Fin 4 → Fin 3) :
    pmSum witness ι =
      (if ι = fun _ => 0 then 1 else 0) +
      (if ι = fun _ => 1 then 1 else 0) +
      (if ι = fun _ => 2 then 1 else 0) := by
  rw [pmSum_eq_sum_over witness ι {M0, M1, M2} isPMFinset_iff]
  rw [Finset.sum_insert (by simp [M0_ne_M1, M0_ne_M2])]
  rw [Finset.sum_insert (by simp [M1_ne_M2])]
  simp [product_M0, product_M1, product_M2]
  ring

@[simp] private theorem constant_eq_iff (a b : Fin 3) :
    ((fun _ : Fin 4 => a) = fun _ => b) ↔ a = b := by
  constructor
  · exact fun h => congrFun h 0
  · exact fun h => by subst b; rfl

theorem witness_serves : Serves witness Finset.univ := by
  classical
  constructor
  · intro c _
    rw [pmSum_witness]
    fin_cases c <;> simp
  · intro ι hι
    rw [pmSum_witness]
    have h0 : ι ≠ fun _ => 0 := fun h => hι ⟨0, Finset.mem_univ _, h⟩
    have h1 : ι ≠ fun _ => 1 := fun h => hι ⟨1, Finset.mem_univ _, h⟩
    have h2 : ι ≠ fun _ => 2 := fun h => hι ⟨2, Finset.mem_univ _, h⟩
    simp [h0, h1, h2]

/-- K4 is a concrete counterexample to any unrestricted `servableRank ≤ 2`
statement: all three colours are served. -/
theorem three_colours_servable :
    ∃ W : WeightSystem Graph 3, Serves W Finset.univ :=
  ⟨witness, witness_serves⟩

/-- Exact regression against the former unrestricted cap theorem. -/
theorem not_servableRank_le_two : ¬ servableRank Graph 3 ≤ 2 := by
  intro hcap
  have hbounded : BddAbove {n : ℕ | ∃ W : WeightSystem Graph 3,
      ∃ C : Finset (Fin 3), C.card = n ∧ Serves W C} := by
    refine ⟨3, ?_⟩
    rintro n ⟨W, C, rfl, _⟩
    simpa using Finset.card_le_card (Finset.subset_univ C)
  have hmember : 3 ∈ {n : ℕ | ∃ W : WeightSystem Graph 3,
      ∃ C : Finset (Fin 3), C.card = n ∧ Serves W C} := by
    exact ⟨witness, Finset.univ, by decide, witness_serves⟩
  have hthree : 3 ≤ servableRank Graph 3 :=
    le_csSup hbounded hmember
  omega

end K4

namespace TwoC4

/-- The disjoint union of two four-cycles, on vertices `0..3` and `4..7`. -/
def Graph : SimpleGraph (Fin 8) := SimpleGraph.fromRel fun u v =>
  (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨
  (u = 2 ∧ v = 3) ∨ (u = 0 ∧ v = 3) ∨
  (u = 4 ∧ v = 5) ∨ (u = 5 ∧ v = 6) ∨
  (u = 6 ∧ v = 7) ∨ (u = 4 ∧ v = 7)

instance : DecidableRel Graph.Adj := fun _ _ => by
  unfold Graph
  infer_instance

def e01 : Graph.edgeSet := ⟨s(0, 1), by decide⟩
def e12 : Graph.edgeSet := ⟨s(1, 2), by decide⟩
def e23 : Graph.edgeSet := ⟨s(2, 3), by decide⟩
def e03 : Graph.edgeSet := ⟨s(0, 3), by decide⟩
def e45 : Graph.edgeSet := ⟨s(4, 5), by decide⟩
def e56 : Graph.edgeSet := ⟨s(5, 6), by decide⟩
def e67 : Graph.edgeSet := ⟨s(6, 7), by decide⟩
def e47 : Graph.edgeSet := ⟨s(4, 7), by decide⟩

def A0 : Finset Graph.edgeSet := {e01, e23}
def B0 : Finset Graph.edgeSet := {e12, e03}
def A1 : Finset Graph.edgeSet := {e45, e67}
def B1 : Finset Graph.edgeSet := {e56, e47}

def F00 : Finset Graph.edgeSet := A0 ∪ A1
def F01 : Finset Graph.edgeSet := A0 ∪ B1
def F10 : Finset Graph.edgeSet := B0 ∪ A1
def F11 : Finset Graph.edgeSet := B0 ∪ B1

instance : DecidablePred (IsPMFinset Graph) := decidableIsPMFinset

theorem perfect_matchings_computable :
    Finset.univ.filter (IsPMFinset Graph) = {F00, F01, F10, F11} := by
  decide

theorem isPMFinset_iff (M : Finset Graph.edgeSet) :
    IsPMFinset Graph M ↔
      M ∈ ({F00, F01, F10, F11} : Finset (Finset Graph.edgeSet)) := by
  have h := Finset.ext_iff.mp perfect_matchings_computable M
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h

/-- The graph visibly has two edge-disjoint perfect matchings. -/
theorem disjoint_perfect_matching_finsets :
    IsPMFinset Graph F00 ∧ IsPMFinset Graph F11 ∧ Disjoint F00 F11 := by
  decide

theorem disjoint_A0_A1 : Disjoint A0 A1 := by decide
theorem disjoint_A0_B1 : Disjoint A0 B1 := by decide
theorem disjoint_B0_A1 : Disjoint B0 A1 := by decide
theorem disjoint_B0_B1 : Disjoint B0 B1 := by decide

theorem F00_ne_F01 : F00 ≠ F01 := by decide
theorem F00_ne_F10 : F00 ≠ F10 := by decide
theorem F00_ne_F11 : F00 ≠ F11 := by decide
theorem F01_ne_F10 : F01 ≠ F10 := by decide
theorem F01_ne_F11 : F01 ≠ F11 := by decide
theorem F10_ne_F11 : F10 ≠ F11 := by decide

theorem left_endpoints : ∀ e ∈ A0 ∪ B0,
    (e : Sym2 (Fin 8)).inf.val < 4 ∧ (e : Sym2 (Fin 8)).sup.val < 4 := by
  decide

theorem right_endpoints : ∀ e ∈ A1 ∪ B1,
    ¬ (e : Sym2 (Fin 8)).inf.val < 4 ∧ ¬ (e : Sym2 (Fin 8)).sup.val < 4 := by
  decide

def componentColor {D : ℕ} (a b : Fin D) (v : Fin 8) : Fin D :=
  if v.val < 4 then a else b

@[simp] theorem componentColor_self {D : ℕ} (c : Fin D) :
    componentColor c c = fun _ => c := by
  funext v
  simp [componentColor]

def leftFactor {D : ℕ} (W : WeightSystem Graph D) (c : Fin D) : ℂ :=
  (∏ e ∈ A0, W e c c) + ∏ e ∈ B0, W e c c

def rightFactor {D : ℕ} (W : WeightSystem Graph D) (c : Fin D) : ℂ :=
  (∏ e ∈ A1, W e c c) + ∏ e ∈ B1, W e c c

private theorem edgeWeight_component_left {D : ℕ} (W : WeightSystem Graph D)
    (a b : Fin D) (e : Graph.edgeSet) (he : e ∈ A0 ∪ B0) :
    edgeWeight W (componentColor a b) e = W e a a := by
  have h := left_endpoints e he
  simp [edgeWeight, componentColor, h.1, h.2]

private theorem edgeWeight_component_right {D : ℕ} (W : WeightSystem Graph D)
    (a b : Fin D) (e : Graph.edgeSet) (he : e ∈ A1 ∪ B1) :
    edgeWeight W (componentColor a b) e = W e b b := by
  have h := right_endpoints e he
  simp [edgeWeight, componentColor, h.1, h.2]

/-- The four matching terms form a `2 × 2` distributive product. -/
theorem pmSum_componentColor {D : ℕ} (W : WeightSystem Graph D) (a b : Fin D) :
    pmSum W (componentColor a b) = leftFactor W a * rightFactor W b := by
  rw [pmSum_eq_sum_over W (componentColor a b) {F00, F01, F10, F11}
    isPMFinset_iff]
  rw [Finset.sum_insert (by
    simp [F00_ne_F01, F00_ne_F10, F00_ne_F11])]
  rw [Finset.sum_insert (by simp [F01_ne_F10, F01_ne_F11])]
  rw [Finset.sum_insert (by simp [F10_ne_F11])]
  simp only [Finset.sum_singleton]
  rw [F00, Finset.prod_union disjoint_A0_A1]
  rw [F01, Finset.prod_union disjoint_A0_B1]
  rw [F10, Finset.prod_union disjoint_B0_A1]
  rw [F11, Finset.prod_union disjoint_B0_B1]
  have hA0 : (∏ e ∈ A0, edgeWeight W (componentColor a b) e) =
      ∏ e ∈ A0, W e a a := Finset.prod_congr rfl fun e he =>
    edgeWeight_component_left W a b e (Finset.mem_union_left B0 he)
  have hB0 : (∏ e ∈ B0, edgeWeight W (componentColor a b) e) =
      ∏ e ∈ B0, W e a a := Finset.prod_congr rfl fun e he =>
    edgeWeight_component_left W a b e (Finset.mem_union_right A0 he)
  have hA1 : (∏ e ∈ A1, edgeWeight W (componentColor a b) e) =
      ∏ e ∈ A1, W e b b := Finset.prod_congr rfl fun e he =>
    edgeWeight_component_right W a b e (Finset.mem_union_left B1 he)
  have hB1 : (∏ e ∈ B1, edgeWeight W (componentColor a b) e) =
      ∏ e ∈ B1, W e b b := Finset.prod_congr rfl fun e he =>
    edgeWeight_component_right W a b e (Finset.mem_union_right A1 he)
  rw [hA0, hB0, hA1, hB1]
  unfold leftFactor rightFactor
  ring

/-- Two colours cannot be served on two disjoint four-cycles. The mixed
component colouring forces a product of two already-nonzero factors to be
zero. -/
theorem not_serves_card_two {D : ℕ} (W : WeightSystem Graph D)
    (C : Finset (Fin D)) (hC : C.card = 2) : ¬ Serves W C := by
  intro hS
  obtain ⟨a, b, hab, hCeq⟩ := Finset.card_eq_two.mp hC
  have haC : a ∈ C := by rw [hCeq]; simp
  have hbC : b ∈ C := by rw [hCeq]; simp
  have ha := hS.1 a haC
  have hb := hS.1 b hbC
  rw [← componentColor_self a, pmSum_componentColor] at ha
  rw [← componentColor_self b, pmSum_componentColor] at hb
  have hla : leftFactor W a ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at ha
    exact zero_ne_one ha
  have hrb : rightFactor W b ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hb
    exact zero_ne_one hb
  have hmixed : ¬ ∃ c ∈ C, componentColor a b = fun _ => c := by
    rintro ⟨c, _, heq⟩
    have h0 := congrFun heq (0 : Fin 8)
    have h4 := congrFun heq (4 : Fin 8)
    simp [componentColor] at h0 h4
    exact hab (h0.trans h4.symm)
  have hzero := hS.2 (componentColor a b) hmixed
  rw [pmSum_componentColor] at hzero
  exact (mul_ne_zero hla hrb) hzero

def M00 : Graph.Subgraph := subgraphOfFinset F00
def M11 : Graph.Subgraph := subgraphOfFinset F11

theorem disjoint_perfect_matching_subgraphs :
    M00.IsPerfectMatching ∧ M11.IsPerfectMatching ∧
      Disjoint M00.edgeSet M11.edgeSet := by
  obtain ⟨h00, h11, hd⟩ := disjoint_perfect_matching_finsets
  exact ⟨isPerfectMatching_subgraphOfFinset h00,
    isPerfectMatching_subgraphOfFinset h11,
    disjoint_edgeSet_subgraphOfFinset hd⟩

/-- Regression theorem for the false lower-bound statement: this graph has
two edge-disjoint perfect matchings but no weight system serves two colours. -/
theorem refutes_disjoint_matchings_lower_bound :
    (∃ M₁ M₂ : Graph.Subgraph,
      M₁.IsPerfectMatching ∧ M₂.IsPerfectMatching ∧
        Disjoint M₁.edgeSet M₂.edgeSet) ∧
    ¬ ∃ D : ℕ, ∃ W : WeightSystem Graph D, ∃ C : Finset (Fin D),
      C.card = 2 ∧ Serves W C := by
  constructor
  · exact ⟨M00, M11, disjoint_perfect_matching_subgraphs⟩
  · rintro ⟨D, W, C, hC, hS⟩
    exact not_serves_card_two W C hC hS

end TwoC4

end Krenn
