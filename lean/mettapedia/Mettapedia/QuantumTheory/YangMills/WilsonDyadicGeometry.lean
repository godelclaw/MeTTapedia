import Mettapedia.QuantumTheory.YangMills.StrongCouplingCrossing

/-!
# Nested separators and scale-two Wilson geometry

At mesh `s`, retain links lying in a coordinate face of the mesh: a transverse
coordinate is divisible by `s`. All other links are internal. Any internal
links in one plaquette have the same cell index. Thus distinct cells share
only retained links, and a plaquette cannot directly couple their interiors.

Scale-two blocking has a different target lattice: its side is half the
fine side, and a coarse link is the ordered product of two fine links.
After `j` changes the fine period and even-anchor distances are multiplied
by exactly `2^j`.
-/
set_option autoImplicit false
noncomputable section
open Finset
open scoped Classical
namespace Mettapedia.QuantumTheory.YangMills.WilsonDyadicGeometry
open StrongCouplingCrossing
variable {d n : ℕ}

/-- A positive link is retained precisely when it lies in a transverse mesh
face; the full link, including both endpoints, then lies in that face. -/
def Retained (s : ℕ) (l : Link d n) : Prop :=
  ∃ i : Fin d, i ≠ l.2 ∧ s ∣ (l.1 i).val

/-- Index of the cell containing the origin, in ordinary integer coordinates. -/
def cell (s : ℕ) (x : Site d n) : Fin d → ℕ := fun i => (x i).val / s

theorem retained_of_dvd {s t : ℕ} (hst : s ∣ t) (l : Link d n)
    (h : Retained t l) : Retained s l := by
  obtain ⟨i, hi, hd⟩ := h
  exact ⟨i, hi, hst.trans hd⟩

theorem coarse_retained_fine (l : Link d n) (h : Retained 4 l) : Retained 2 l :=
  retained_of_dvd (by decide : 2 ∣ 4) l h

/-- An internal shifted link cannot have crossed a mesh face or the periodic
seam, since the shifted transverse coordinate would then be divisible by `s`. -/
theorem div_val_add_one {s : ℕ} (x : ZMod (n + 3))
    (h : ¬s ∣ (x + 1).val) : (x + 1).val / s = x.val / s := by
  have hval : (x + 1).val = (x.val + 1) % (n + 3) := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod,
      Nat.mod_eq_of_lt (by omega : 1 < n + 3)]
  have hx := x.val_lt
  have hlt : x.val + 1 < n + 3 := by
    by_contra hnot
    have heq : x.val + 1 = n + 3 := by omega
    rw [hval, heq, Nat.mod_self] at h
    exact h (dvd_zero _)
  rw [hval, Nat.mod_eq_of_lt hlt] at h ⊢
  exact Nat.succ_div_of_not_dvd h

theorem cell_step_eq {s : ℕ} (x : Site d n) (μ : Fin d)
    (h : ¬s ∣ (x μ + 1).val) : cell s (x + step μ) = cell s x := by
  funext i
  by_cases hi : i = μ
  · subst i
    simpa [cell, step] using div_val_add_one (n := n) (s := s) (x μ) h
  · simp [cell, step, hi]

/-- Every internal boundary link of a plaquette belongs to its base cell.
This is the geometric separation needed for exact conditional factorization. -/
theorem internal_link_cell (s : ℕ) (p : Plaquette d n) (i : Fin 4)
    (h : ¬Retained s (linkAt p i)) : cell s (linkAt p i).1 = cell s p.1 := by
  fin_cases i
  · rfl
  · apply cell_step_eq
    intro hd
    apply h
    refine ⟨p.2.1.1, ne_of_lt p.2.2, ?_⟩
    simpa [linkAt, step] using hd
  · apply cell_step_eq
    intro hd
    apply h
    refine ⟨p.2.1.2, ne_of_gt p.2.2, ?_⟩
    simpa [linkAt, step] using hd
  · rfl

/-- Distinct cell interiors never meet the same elementary plaquette. -/
theorem internal_support_same_cell (s : ℕ) (p : Plaquette d n)
    {l k : Link d n} (hl : l ∈ support p) (hk : k ∈ support p)
    (hil : ¬Retained s l) (hik : ¬Retained s k) : cell s l.1 = cell s k.1 := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hl
  obtain ⟨j, _, rfl⟩ := mem_image.mp hk
  exact (internal_link_cell s p i hil).trans (internal_link_cell s p j hik).symm

/-! ## Genuine scale-two links -/

/-- A coarse torus of side `n+3` is blocked from side `2(n+3)`. -/
abbrev doubleIndex (n : ℕ) := 2 * n + 3

/-- Fine index for a prescribed finite number of genuine lattice rescalings. -/
def scaleIndex (n : ℕ) : ℕ → ℕ
  | 0 => n
  | j + 1 => doubleIndex (scaleIndex n j)

theorem scaleIndex_side (n j : ℕ) : scaleIndex n j + 3 = 2^j * (n+3) := by
  induction j with
  | zero => simp [scaleIndex]
  | succ j ih =>
    simp only [scaleIndex, doubleIndex, pow_succ]
    nlinarith


/-- Doubling a cyclic coordinate is an injective additive map into the
torus with twice the period. -/
def doubleCoordinate (n : ℕ) : ZMod (n + 3) →+ ZMod (doubleIndex n + 3) :=
  ZMod.lift (n + 3)
    ⟨AddMonoidHom.mk' (fun j : ℤ ↦ (2 : ZMod (doubleIndex n + 3)) * j)
      (by intro a b; simp [mul_add]), by
        change (2 : ZMod (doubleIndex n + 3)) * ((n + 3 : ℕ) : ZMod (doubleIndex n + 3)) = 0
        calc
          _ = ((doubleIndex n + 3 : ℕ) : ZMod (doubleIndex n + 3)) := by
            simp only [doubleIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
            ring
          _ = 0 := ZMod.natCast_self _⟩

@[simp] theorem doubleCoordinate_intCast (n : ℕ) (j : ℤ) :
    doubleCoordinate n (j : ZMod (n + 3)) = (2 * j : ℤ) := by
  simp [doubleCoordinate]

theorem doubleCoordinate_apply (n : ℕ) (z : ZMod (n + 3)) :
    doubleCoordinate n z = ((2 * z.val : ℕ) : ZMod (doubleIndex n + 3)) := by
  simpa using doubleCoordinate_intCast n (z.val : ℤ)

@[simp] theorem val_doubleCoordinate (n : ℕ) (z : ZMod (n + 3)) :
    (doubleCoordinate n z).val = 2 * z.val := by
  rw [doubleCoordinate_apply, ZMod.val_natCast,
    Nat.mod_eq_of_lt (by have h := z.val_lt; dsimp [doubleIndex]; omega)]

theorem doubleCoordinate_injective (n : ℕ) : Function.Injective (doubleCoordinate n) := by
  intro x y h
  have hv := congrArg ZMod.val h
  simp only [val_doubleCoordinate] at hv
  exact ZMod.val_injective (n + 3) (by omega)

/-- Coarse sites sit at the even sites of the fine lattice. -/
def doubleSite (x : Site d n) : Site d (doubleIndex n) := fun i ↦ doubleCoordinate n (x i)

@[simp] theorem doubleSite_add (x y : Site d n) :
    doubleSite (x + y) = doubleSite x + doubleSite y := by
  funext i
  exact map_add _ _ _

theorem doubleSite_injective : Function.Injective (doubleSite (d := d) (n := n)) := by
  intro x y h
  funext i
  exact doubleCoordinate_injective n (congrFun h i)

@[simp] theorem doubleSite_step (μ : Fin d) :
    doubleSite (step (n := n) μ) = step μ + step μ := by
  funext i
  by_cases h : i = μ
  · subst i
    simpa [doubleSite, step, one_add_one_eq_two] using doubleCoordinate_intCast n 1
  · simp [doubleSite, step, h]

/-- The two consecutive positively oriented fine links in a coarse link. -/
def blockEdge (l : Link d n) (b : Fin 2) : Link d (doubleIndex n) :=
  (doubleSite l.1 + b.val • step l.2, l.2)

@[simp] theorem blockEdge_zero (l : Link d n) :
    blockEdge l 0 = (doubleSite l.1, l.2) := by simp [blockEdge]

@[simp] theorem blockEdge_one (l : Link d n) :
    blockEdge l 1 = (doubleSite l.1 + step l.2, l.2) := by simp [blockEdge]

theorem blockEdge_endpoint (l : Link d n) :
    (blockEdge l 1).1 + step l.2 = doubleSite (l.1 + step l.2) := by
  simp [add_assoc]

theorem val_blockEdge_direction (l : Link d n) (b : Fin 2) :
    ((blockEdge l b).1 l.2).val = 2 * (l.1 l.2).val + b.val := by
  have he : (blockEdge l b).1 l.2 =
      ((2 * (l.1 l.2).val + b.val : ℕ) : ZMod (doubleIndex n + 3)) := by
    simp [blockEdge, doubleSite, step, doubleCoordinate_apply, nsmul_eq_mul]
  rw [he, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have hz := (l.1 l.2).val_lt
  have hb := b.isLt
  dsimp [doubleIndex]
  omega

/-- No fine edge is reused by two coarse paths, including across the
periodic seam. This supplies independent product-Haar block coordinates. -/
theorem blockEdge_injective : Function.Injective
    (fun p : Link d n × Fin 2 ↦ blockEdge p.1 p.2) := by
  rintro ⟨⟨x, μ⟩, b⟩ ⟨⟨y, ν⟩, c⟩ h
  have hdir : μ = ν := congrArg Prod.snd h
  subst ν
  have hv := congrArg (fun l : Link d (doubleIndex n) ↦ (l.1 μ).val) h
  change ((blockEdge (x, μ) b).1 μ).val = ((blockEdge (y, μ) c).1 μ).val at hv
  rw [val_blockEdge_direction, val_blockEdge_direction] at hv
  have hbc : b = c := Fin.ext (by have hb := b.isLt; have hc := c.isLt; omega)
  subst c
  have hx := congrArg Prod.fst h
  change doubleSite x + b.val • step μ = doubleSite y + b.val • step μ at hx
  have hxy := doubleSite_injective (add_right_cancel hx)
  subst y
  rfl

/-- The first and second halves as two disjoint copies of the coarse links. -/
def blockPair : Link d n ⊕ Link d n → Link d (doubleIndex n) :=
  Sum.elim (fun l ↦ blockEdge l 0) (fun l ↦ blockEdge l 1)

theorem blockPair_injective : Function.Injective (blockPair (d := d) (n := n)) := by
  intro a b h
  cases a with
  | inl l =>
    cases b with
    | inl k => exact congrArg Sum.inl (congrArg Prod.fst (@blockEdge_injective d n (l, 0) (k, 0) h))
    | inr k =>
      have hh : (0 : Fin 2) = 1 := congrArg Prod.snd (@blockEdge_injective d n (l, 0) (k, 1) h)
      exact (by decide : (0 : Fin 2) ≠ 1) hh |>.elim
  | inr l =>
    cases b with
    | inl k =>
      have hh : (1 : Fin 2) = 0 := congrArg Prod.snd (@blockEdge_injective d n (l, 1) (k, 0) h)
      exact (by decide : (1 : Fin 2) ≠ 0) hh |>.elim
    | inr k => exact congrArg Sum.inr (congrArg Prod.fst (@blockEdge_injective d n (l, 1) (k, 1) h))

/-- Fine links that occur in no coarse two-link path remain fluctuation
coordinates; they are integrated rather than deleted. -/
abbrev UnusedLink (d n : ℕ) :=
  {l : Link d (doubleIndex n) // l ∉ Set.range (blockPair (d := d) (n := n))}

/-- Every fine link is uniquely a first half, a second half, or an unused
edge. This finite equivalence is the index map of the Haar block chart. -/
def blockIndexEquiv (d n : ℕ) :
    ((Link d n ⊕ Link d n) ⊕ UnusedLink d n) ≃ Link d (doubleIndex n) :=
  ((Equiv.ofInjective (blockPair (d := d) (n := n)) blockPair_injective).sumCongr
    (Equiv.refl (UnusedLink d n))).trans
    (@Equiv.Set.sumCompl _ (Set.range blockPair) (Classical.decPred _))

@[simp] theorem blockIndexEquiv_first (l : Link d n) :
    blockIndexEquiv d n (.inl (.inl l)) = blockEdge l 0 := rfl

@[simp] theorem blockIndexEquiv_second (l : Link d n) :
    blockIndexEquiv d n (.inl (.inr l)) = blockEdge l 1 := rfl

@[simp] theorem blockIndexEquiv_unused (l : UnusedLink d n) :
    blockIndexEquiv d n (.inr l) = l.val := rfl

/-- Circle distances scale exactly with the lattice spacing and period. -/
theorem norm_doubleCoordinate (z : ZMod (n + 3)) :
    ‖coordinateCircle (doubleIndex n) (doubleCoordinate n z)‖ =
      2 * ‖coordinateCircle n z‖ := by
  have hp : (doubleIndex n : ℝ) + 3 = 2 * ((n : ℝ) + 3) := by
    simp only [doubleIndex, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [coordinateCircle_apply, val_doubleCoordinate, coordinateCircle_apply, hp]
  simpa only [Nat.cast_mul, Nat.cast_ofNat, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    using AddCircle.norm_coe_mul (n + 3 : ℝ) (z.val : ℝ) 2

/-- The original sup-circle metric becomes twice the coarse metric on
even base points. Link directions retain their zero-distance multiplicity. -/
theorem dist_blockEdge_zero (l k : Link d n) :
    dist (blockEdge l 0) (blockEdge k 0) = 2 * dist l k := by
  have hc (i : Fin d) :
      dist (position (blockEdge l 0) i) (position (blockEdge k 0) i) =
        2 * dist (position l i) (position k i) := by
    simpa only [position, blockEdge_zero, doubleSite, dist_eq_norm, ← map_sub]
      using norm_doubleCoordinate (l.1 i - k.1 i)
  rw [dist_link_eq, dist_link_eq]
  apply le_antisymm
  · apply (dist_pi_le_iff (by positivity : 0 ≤ 2 * dist (position l) (position k))).mpr
    intro i
    rw [hc]
    exact mul_le_mul_of_nonneg_left (dist_le_pi_dist (position l) (position k) i) (by norm_num)
  · have h : dist (position l) (position k) ≤
        dist (position (blockEdge l 0)) (position (blockEdge k 0)) / 2 := by
      apply (dist_pi_le_iff (by positivity)).mpr
      intro i
      have hi := dist_le_pi_dist (position (blockEdge l 0)) (position (blockEdge k 0)) i
      rw [hc] at hi
      linarith
    linarith

/-- Noncommutative link multiplication keeps path order. -/
def blockField {E : Type*} [Mul E] (U : Link d (doubleIndex n) → E) : Link d n → E :=
  fun l ↦ U (blockEdge l 0) * U (blockEdge l 1)

/-- The lattice gauge action at the initial and final vertices of a link. -/
def gaugeAct {E : Type*} [Group E] (g : Site d n → E) (U : Link d n → E) : Link d n → E :=
  fun l ↦ g l.1 * U l * (g (l.1 + step l.2))⁻¹

/-- Gauge factors at the intermediate fine vertex cancel without commuting
any group elements. The retained gauge is restriction to the even sites. -/
theorem blockField_gaugeAct {E : Type*} [Group E]
    (g : Site d (doubleIndex n) → E) (U : Link d (doubleIndex n) → E) :
    blockField (gaugeAct g U) = gaugeAct (fun x ↦ g (doubleSite x)) (blockField U) := by
  funext l
  simp only [blockField, gaugeAct, blockEdge_zero, blockEdge_one]
  rw [← blockEdge_endpoint l]
  simp only [blockEdge_one]
  group

/-- Gauge factors telescope around the plaquette in its original noncommutative order. -/
theorem holonomy_gaugeAct {E : Type*} [Group E]
    (g : Site d n → E) (U : Link d n → E) (p : Plaquette d n) :
    holonomy (fun i ↦ gaugeAct g U (linkAt p i)) =
      g p.1 * holonomy (fun i ↦ U (linkAt p i)) * (g p.1)⁻¹ := by
  dsimp [holonomy, linkAt, gaugeAct]
  rw [show p.1 + step p.2.1.1 + step p.2.1.2 =
    p.1 + step p.2.1.2 + step p.2.1.1 by abel]
  group

/-- The lifted rotation sites lie within one fine step of their even anchors. -/
theorem dist_blockEdge_halves_le (l : Link d n) : dist (blockEdge l 0) (blockEdge l 1) ≤ 1 := by
  rw [dist_link_eq]
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  apply dist_coordinateCircle_le_one (x := doubleSite l.1 i)
  · simp [blockEdge_zero]
  · by_cases hi : i = l.2
    · simp [blockEdge_one, step, hi]
    · simp [blockEdge_one, step, hi]

theorem dist_coarse_le_second (l k : Link d n) :
    2 * dist l k ≤ dist (blockEdge l 1) (blockEdge k 1) + 2 := by
  have h := dist_triangle4 (blockEdge l 0) (blockEdge l 1) (blockEdge k 1) (blockEdge k 0)
  rw [dist_blockEdge_zero, dist_comm (blockEdge k 1)] at h
  have hl := dist_blockEdge_halves_le l
  have hk := dist_blockEdge_halves_le k
  linarith


/-- No elementary plaquette contains both consecutive halves of a coarse
link. Parallel sides differ only in a transverse coordinate. -/
theorem no_blockPair_in_support (p : Plaquette d (doubleIndex n)) (l : Link d n) :
    ¬(blockEdge l 0 ∈ support p ∧ blockEdge l 1 ∈ support p) := by
  rintro ⟨h0, h1⟩
  have he0 := support_parallel_coordinate p (blockEdge l 0) h0
  have he1 := support_parallel_coordinate p (blockEdge l 1) h1
  have hd0 : (blockEdge l 0).2 = l.2 := rfl
  have hd1 : (blockEdge l 1).2 = l.2 := rfl
  rw [hd0] at he0
  rw [hd1] at he1
  have he := congrArg ZMod.val (he0.trans he1.symm)
  rw [val_blockEdge_direction, val_blockEdge_direction] at he
  norm_num at he

/-- The even-anchor embedding after a prescribed number of scale changes. -/
def scaleAnchor : (j : ℕ) → Link d n → Link d (scaleIndex n j)
  | 0, l => l
  | j + 1, l => blockEdge (scaleAnchor j l) 0

theorem dist_scaleAnchor (j : ℕ) (l k : Link d n) :
    dist (scaleAnchor j l) (scaleAnchor j k) = (2 : ℝ)^j * dist l k := by
  induction j with
  | zero =>
    change dist l k = (2 : ℝ)^0 * dist l k
    rw [pow_zero, one_mul]
  | succ j ih =>
    change dist (blockEdge (scaleAnchor j l) 0) (blockEdge (scaleAnchor j k) 0) = _
    rw [dist_blockEdge_zero, ih, pow_succ]
    ring


#print axioms coarse_retained_fine
#print axioms internal_link_cell
#print axioms internal_support_same_cell
end Mettapedia.QuantumTheory.YangMills.WilsonDyadicGeometry
