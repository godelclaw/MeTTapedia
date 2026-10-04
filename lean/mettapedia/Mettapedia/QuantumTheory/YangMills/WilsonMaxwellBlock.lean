import Mettapedia.QuantumTheory.YangMills.WilsonDyadicGeometry
import Mettapedia.QuantumTheory.YangMills.SU2WilsonBlockIntegration
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Maxwell fluctuations inside the scale-two Wilson integration fiber

The linear block map is the derivative of the existing ordered two-link
product at the identity. Gauge directions preserving this block must be
removed before asking for a fluctuation gap. A local coordinate-path gauge
expresses the remaining fine links through nearby plaquette curls.

The quadratic theory here is at the trivial background. Its estimates do
not assert nonlinear weak-coupling entrance or a continuum mass gap.
-/
set_option autoImplicit false
noncomputable section
open Finset Filter
open scoped Classical BigOperators Topology Matrix.Norms.Elementwise

namespace Mettapedia.QuantumTheory.YangMills.WilsonMaxwellBlock
open StrongCouplingCrossing WilsonDyadicGeometry SU2WilsonBlockPilot

variable {d n : ℕ}

/-- The derivative of ordered multiplication at the trivial connection. -/
def linearBlock {V : Type*} [Add V] (A : Link d (doubleIndex n) → V) : Link d n → V :=
  fun l => A (blockEdge l 0) + A (blockEdge l 1)

def gradient {V : Type*} [AddCommGroup V] (φ : Site d n → V) : Link d n → V :=
  fun l => φ (l.1 + step l.2) - φ l.1

def curlAt {V : Type*} [AddCommGroup V] (A : Link d n → V)
    (x : Site d n) (μ ν : Fin d) : V :=
  A (x, μ) + A (x + step μ, ν) - A (x + step ν, μ) - A (x, ν)

def curl {V : Type*} [AddCommGroup V] (A : Link d n → V) (p : Plaquette d n) : V :=
  curlAt A p.1 p.2.1.1 p.2.1.2

theorem linearBlock_gradient {V : Type*} [AddCommGroup V]
    (φ : Site d (doubleIndex n) → V) :
    linearBlock (gradient φ) = gradient (fun x => φ (doubleSite x)) := by
  funext l
  simp only [linearBlock, gradient, blockEdge_zero, blockEdge_one]
  rw [← blockEdge_endpoint l]
  simp only [blockEdge_one]
  abel

theorem curlAt_gradient {V : Type*} [AddCommGroup V]
    (φ : Site d n → V) (x : Site d n) (μ ν : Fin d) :
    curlAt (gradient φ) x μ ν = 0 := by
  unfold curlAt gradient
  simp only [add_right_comm x (step μ) (step ν)]
  abel

theorem curl_gradient {V : Type*} [AddCommGroup V] (φ : Site d n → V) :
    curl (gradient φ) = 0 := by
  funext p
  exact curlAt_gradient φ p.1 p.2.1.1 p.2.1.2

/-- The derivative statement uses the actual SU(2) matrix paths and block map. -/
theorem hasDerivAt_blockField (U : ℝ → Link d (doubleIndex n) → SU2)
    (A : Link d (doubleIndex n) → Matrix (Fin 2) (Fin 2) ℂ)
    (hzero : ∀ l, U 0 l = 1)
    (hderiv : ∀ l, HasDerivAt (fun t => (U t l).val) (A l) 0) (l : Link d n) :
    HasDerivAt (fun t => (blockField (U t) l).val) (linearBlock A l) 0 := by
  simpa only [blockField, linearBlock, Submonoid.coe_mul, hzero, Submonoid.coe_one,
    mul_one, one_mul] using
    hasDerivAt_matrix_mul (hderiv (blockEdge l 0)) (hderiv (blockEdge l 1))

/-- A path in the exact identity block fiber necessarily has derivative in ker Q. -/
theorem linearBlock_eq_zero_of_constant_block (U : ℝ → Link d (doubleIndex n) → SU2)
    (A : Link d (doubleIndex n) → Matrix (Fin 2) (Fin 2) ℂ)
    (hzero : ∀ l, U 0 l = 1)
    (hderiv : ∀ l, HasDerivAt (fun t => (U t l).val) (A l) 0)
    (hblock : ∀ t, blockField (U t) = 1) : linearBlock A = 0 := by
  funext l
  have h := hasDerivAt_blockField U A hzero hderiv l
  have hf : (fun t => (blockField (U t) l).val) =
      (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    funext t
    rw [hblock]
    rfl
  rw [hf] at h
  exact h.unique (hasDerivAt_const_matrix 1 0)

/-- Infinitesimal gauge motions which leave the retained links fixed. -/
def FiberGauge (n : ℕ) (φ : Site 4 (doubleIndex n) → ℝ) : Prop :=
  linearBlock (gradient φ) = 0

namespace Cell

abbrev Corner := Fin 4 → Fin 2
abbrev Field := BlockVertex → Fin 4 → ℝ

def zero : BlockVertex := ![0, 0, 0, 0]

def corner (b : Corner) : BlockVertex :=
  ![⟨(b 0).val, by omega⟩, ⟨(b 1).val, by omega⟩,
    ⟨(b 2).val, by omega⟩, ⟨(b 3).val, by omega⟩]

def next (v : BlockVertex) (μ : Fin 4) : BlockVertex :=
  ![if μ = 0 then v 0 + 1 else v 0, if μ = 1 then v 1 + 1 else v 1,
    if μ = 2 then v 2 + 1 else v 2, if μ = 3 then v 3 + 1 else v 3]

def pathOrigin (v : BlockVertex) (μ : Fin 4) : BlockVertex :=
  ![if 0 < μ then v 0 else if v 0 = 2 then 2 else 0,
    if 1 < μ then v 1 else if v 1 = 2 then 2 else 0,
    if 2 < μ then v 2 else if v 2 = 2 then 2 else 0,
    if 3 < μ then v 3 else if v 3 = 2 then 2 else 0]

/-- Integrate the coordinate path from the even corner to v. -/
def potential (F : Field) (v : BlockVertex) : ℝ :=
  ∑ μ : Fin 4, if v μ = 1 then F (pathOrigin v μ) μ else 0

def block (F : Field) (μ : Fin 4) : ℝ := F zero μ + F (next zero μ) μ

def curl (F : Field) (v : BlockVertex) (μ ν : Fin 4) : ℝ :=
  F v μ + F (next v μ) ν - F (next v ν) μ - F v ν

def pathPrefix (b : Corner) (ν : Fin 4) : BlockVertex :=
  ![if 0 < ν then corner b 0 else 0, if 1 < ν then corner b 1 else 0,
    if 2 < ν then corner b 2 else 0, if 3 < ν then corner b 3 else 0]

def shiftedPrefix (b : Corner) (ν μ : Fin 4) (j : Fin 2) : BlockVertex :=
  ![if μ = 0 then ⟨j.val, by omega⟩ else pathPrefix b ν 0,
    if μ = 1 then ⟨j.val, by omega⟩ else pathPrefix b ν 1,
    if μ = 2 then ⟨j.val, by omega⟩ else pathPrefix b ν 2,
    if μ = 3 then ⟨j.val, by omega⟩ else pathPrefix b ν 3]

/-- The small coordinate rectangles swept out when reordering the path.
There are at most eight slots; unused slots are exactly zero. -/
def term (F : Field) (b : Corner) (μ ν : Fin 4) (j : Fin 2) : ℝ :=
  if b ν = 0 then 0 else
  if μ < ν then if j = 0 then -curl F (pathPrefix b ν) μ ν else 0 else
  if ν < μ ∧ b μ = 1 then curl F (shiftedPrefix b ν μ j) ν μ else 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Finite Stokes identity on the existing 3^4 pilot cell. -/
theorem path_identity (F : Field) (b : Corner) (μ : Fin 4) :
    F (corner b) μ - (potential F (next (corner b) μ) - potential F (corner b)) =
      (if b μ = 1 then block F μ else 0) + ∑ ν : Fin 4, ∑ j : Fin 2, term F b μ ν j := by
  have hb : b = ![b 0, b 1, b 2, b 3] := by ext i; fin_cases i <;> rfl
  rw [hb]
  generalize b 0 = a, b 1 = c, b 2 = e, b 3 = f
  fin_cases a <;> fin_cases c <;> fin_cases e <;> fin_cases f <;> fin_cases μ <;>
    norm_num [corner, potential, next, pathOrigin, term, block, zero, curl, pathPrefix,
      shiftedPrefix, Fin.sum_univ_four, Fin.sum_univ_two] <;>
    norm_num only [Fin.ext_iff, Fin.lt_def, Fin.val_add, Fin.coe_ofNat_eq_mod,
      Fin.val_zero, Fin.val_one, ite_true, ite_false, Matrix.vecCons, Matrix.vecHead,
      Matrix.vecTail] <;> norm_num <;> ring!

@[simp] theorem corner_apply (b : Corner) (i : Fin 4) :
    (corner b i).val = (b i).val := by fin_cases i <;> rfl
@[simp] theorem next_apply (v : BlockVertex) (μ i : Fin 4) :
    next v μ i = if μ = i then v i + 1 else v i := by fin_cases i <;> rfl
@[simp] theorem pathOrigin_apply (v : BlockVertex) (μ i : Fin 4) :
    pathOrigin v μ i = if i < μ then v i else if v i = 2 then 2 else 0 := by
  fin_cases i <;> rfl
@[simp] theorem pathPrefix_apply (b : Corner) (ν i : Fin 4) :
    pathPrefix b ν i = if i < ν then corner b i else 0 := by fin_cases i <;> rfl
@[simp] theorem shiftedPrefix_apply (b : Corner) (ν μ i : Fin 4) (j : Fin 2) :
    shiftedPrefix b ν μ j i = if μ = i then ⟨j.val, by omega⟩ else pathPrefix b ν i := by
  fin_cases i <;> rfl
end Cell

/-- Embed the closed pilot cell at a coarse site, including the periodic seam. -/
def embed (y : Site 4 n) (v : BlockVertex) : Site 4 (doubleIndex n) :=
  fun i => doubleCoordinate n (y i) + (v i).val

/-- The unique parity corner of a fine vertex. -/
def parity (x : Site 4 (doubleIndex n)) : Cell.Corner :=
  fun i => ⟨(x i).val % 2, Nat.mod_lt _ (by decide)⟩

def lowerSite (x : Site 4 (doubleIndex n)) : Site 4 n :=
  fun i => halfCoordinate n (x i)

theorem parity_embed (y : Site 4 n) (v : BlockVertex) (i : Fin 4) :
    (parity (embed y v) i).val = (v i).val % 2 := by
  change (doubleCoordinate n (y i) + ((v i).val : ZMod (doubleIndex n + 3))).val % 2 = _
  rw [doubleCoordinate_apply, ← Nat.cast_add, ZMod.val_natCast,
    Nat.mod_mod_of_dvd _ (by dsimp [doubleIndex]; omega : 2 ∣ doubleIndex n + 3)]
  omega

theorem embed_corner_parity (y : Site 4 n) (b : Cell.Corner) :
    parity (embed y (Cell.corner b)) = b := by
  funext i
  apply Fin.ext
  rw [parity_embed, Cell.corner_apply, Nat.mod_eq_of_lt (b i).isLt]

theorem embed_corner_lowerSite (y : Site 4 n) (b : Cell.Corner) :
    lowerSite (embed y (Cell.corner b)) = y := by
  funext i
  apply ZMod.val_injective
  change (halfCoordinate n _).val = _
  rw [val_halfCoordinate]
  change (doubleCoordinate n (y i) + ((Cell.corner b i).val : ZMod (doubleIndex n + 3))).val / 2 = _
  rw [doubleCoordinate_apply, Cell.corner_apply, ← Nat.cast_add, ZMod.val_natCast,
    Nat.mod_eq_of_lt (by have hy := (y i).val_lt; have hb := (b i).isLt; dsimp [doubleIndex]; omega)]
  have hb := (b i).isLt
  omega

theorem embed_lowerSite_parity (x : Site 4 (doubleIndex n)) :
    embed (lowerSite x) (Cell.corner (parity x)) = x := by
  funext i
  simp only [embed, lowerSite, doubleCoordinate_apply, val_halfCoordinate, Cell.corner_apply,
    parity]
  rw [← Nat.cast_add, Nat.div_add_mod]
  exact ZMod.natCast_zmod_val (x i)

/-- Disjoint parity cells partition every fine torus, uniformly in its size. -/
def siteEquiv (n : ℕ) : Site 4 n × Cell.Corner ≃ Site 4 (doubleIndex n) where
  toFun p := embed p.1 (Cell.corner p.2)
  invFun x := (lowerSite x, parity x)
  left_inv p := by simp [embed_corner_lowerSite, embed_corner_parity]
  right_inv := embed_lowerSite_parity

theorem embed_injective (v : BlockVertex) : Function.Injective (fun y : Site 4 n => embed y v) := by
  intro x y h
  apply doubleSite_injective
  funext i
  exact add_right_cancel (congrFun h i)

theorem embed_next (y : Site 4 n) (v : BlockVertex) (μ : Fin 4) (h : (v μ).val < 2) :
    embed y (Cell.next v μ) = embed y v + step μ := by
  funext i
  simp only [embed, Cell.next_apply, Pi.add_apply, step]
  by_cases hi : μ = i
  · subst i
    rw [if_pos rfl, if_pos rfl, Fin.val_add_one_of_lt' (by omega)]
    push_cast
    ring
  · simp [hi, Ne.symm hi]

/-- Coordinate-path gauge potential, based at the even corner of each cell. -/
def gaugePotential (A : Link 4 (doubleIndex n) → ℝ) (x : Site 4 (doubleIndex n)) : ℝ :=
  ∑ μ : Fin 4, if parity x μ = 1 then
    A ((fun i => x i - (parity x i).val +
      if i < μ then ((parity x i).val : ZMod (doubleIndex n + 3)) else 0), μ) else 0

/-- The global gauge agrees on cell faces with the local coordinate path. -/
theorem gaugePotential_embed (A : Link 4 (doubleIndex n) → ℝ)
    (y : Site 4 n) (v : BlockVertex) :
    gaugePotential A (embed y v) = Cell.potential (fun w μ => A (embed y w, μ)) v := by
  unfold gaugePotential Cell.potential
  apply Finset.sum_congr rfl
  intro μ _
  have hbit (i : Fin 4) : parity (embed y v) i =
      ⟨(v i).val % 2, Nat.mod_lt _ (by decide)⟩ := Fin.ext (parity_embed y v i)
  have hone : parity (embed y v) μ = 1 ↔ v μ = 1 := by
    rw [hbit]
    have hv := (v μ).isLt
    rw [Fin.ext_iff, Fin.ext_iff]
    norm_num
    omega
  simp only [hone]
  split_ifs with h
  · congr 1
    apply Prod.ext
    · change (fun i => embed y v i - (parity (embed y v) i).val +
        if i < μ then ((parity (embed y v) i).val : ZMod (doubleIndex n + 3)) else 0) =
        embed y (Cell.pathOrigin v μ)
      funext i
      rw [hbit]
      simp only [embed, Cell.pathOrigin_apply]
      by_cases hi : i < μ
      · simp [hi]
      · simp only [hi, ↓reduceIte, add_zero]
        generalize v i = a
        fin_cases a <;> norm_num [Fin.ext_iff]
    · rfl
  · rfl

@[simp] theorem gaugePotential_doubleSite (A : Link 4 (doubleIndex n) → ℝ) (y : Site 4 n) :
    gaugePotential A (doubleSite y) = 0 := by
  have he : embed y Cell.zero = doubleSite y := by ext i; fin_cases i <;> simp [embed, Cell.zero, doubleSite]
  rw [← he, gaugePotential_embed]
  simp [Cell.potential, Cell.zero, Fin.sum_univ_four]

theorem gaugePotential_fiberGauge (A : Link 4 (doubleIndex n) → ℝ) :
    FiberGauge n (gaugePotential A) := by
  rw [FiberGauge, linearBlock_gradient]
  funext l
  change gaugePotential A (doubleSite (l.1 + step l.2)) - gaugePotential A (doubleSite l.1) = 0
  rw [gaugePotential_doubleSite, gaugePotential_doubleSite, sub_self]


/-- Maxwell action without the conventional coefficient beta/2. -/
def curlEnergy (A : Link 4 (doubleIndex n) → ℝ) : ℝ :=
  ∑ p : Plaquette 4 (doubleIndex n), (curl A p) ^ 2

theorem curlEnergy_nonneg (A : Link 4 (doubleIndex n) → ℝ) : 0 ≤ curlEnergy A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

def cellField (A : Link 4 (doubleIndex n) → ℝ) (y : Site 4 n) : Cell.Field :=
  fun v μ => A (embed y v, μ)

theorem cellField_curl (A : Link 4 (doubleIndex n) → ℝ) (y : Site 4 n)
    (v : BlockVertex) (μ ν : Fin 4) (hμ : (v μ).val < 2) (hν : (v ν).val < 2) :
    Cell.curl (cellField A y) v μ ν = curlAt A (embed y v) μ ν := by
  simp only [Cell.curl, cellField, curlAt, embed_next y v μ hμ, embed_next y v ν hν]

theorem cellField_block (A : Link 4 (doubleIndex n) → ℝ) (y : Site 4 n) (μ : Fin 4) :
    Cell.block (cellField A y) μ = linearBlock A (y, μ) := by
  have hz : embed y Cell.zero = doubleSite y := by
    ext i; fin_cases i <;> simp [embed, Cell.zero, doubleSite]
  have hlt : (Cell.zero μ).val < 2 := by fin_cases μ <;> decide
  simp only [Cell.block, cellField, embed_next y Cell.zero μ hlt, hz, linearBlock,
    blockEdge_zero, blockEdge_one]

theorem gaugeResidual_cell (A : Link 4 (doubleIndex n) → ℝ) (hQ : linearBlock A = 0)
    (y : Site 4 n) (b : Cell.Corner) (μ : Fin 4) :
    A (embed y (Cell.corner b), μ) - gradient (gaugePotential A) (embed y (Cell.corner b), μ) =
      ∑ ν : Fin 4, ∑ j : Fin 2, Cell.term (cellField A y) b μ ν j := by
  have hlt : (Cell.corner b μ).val < 2 := by rw [Cell.corner_apply]; exact (b μ).isLt
  have h := Cell.path_identity (cellField A y) b μ
  rw [cellField_block, show linearBlock A (y, μ) = 0 from congrFun hQ (y, μ)] at h
  simp only [gradient, ← embed_next y (Cell.corner b) μ hlt, gaugePotential_embed]
  have hf : cellField A y = (fun v μ => A (embed y v, μ)) := rfl
  rw [hf] at h ⊢
  simpa only [ite_self, zero_add] using h

theorem pathPrefix_lt_two (b : Cell.Corner) (ν i : Fin 4) :
    (Cell.pathPrefix b ν i).val < 2 := by
  rw [Cell.pathPrefix_apply]
  split_ifs
  · rw [Cell.corner_apply]; exact (b i).isLt
  · decide

theorem shiftedPrefix_lt_two (b : Cell.Corner) (ν μ i : Fin 4) (j : Fin 2) :
    (Cell.shiftedPrefix b ν μ j i).val < 2 := by
  rw [Cell.shiftedPrefix_apply]
  split_ifs
  · exact j.isLt
  · exact pathPrefix_lt_two b ν i

/-- A fixed translated local face appears at most once per coarse cell index. -/
theorem sum_cellCurl_sq_le (A : Link 4 (doubleIndex n) → ℝ) (v : BlockVertex)
    (μ ν : Fin 4) (hμν : μ < ν) (hμ : (v μ).val < 2) (hν : (v ν).val < 2) :
    (∑ y : Site 4 n, (Cell.curl (cellField A y) v μ ν)^2) ≤ curlEnergy A := by
  simp_rw [cellField_curl A _ v μ ν hμ hν]
  let e : Site 4 n → Plaquette 4 (doubleIndex n) := fun y => (embed y v, ⟨(μ, ν), hμν⟩)
  apply Finset.sum_le_sum_of_injOn e
  · intro x _ y _ h
    exact embed_injective v (congrArg Prod.fst h)
  · exact Finset.subset_univ _
  · intro y _
    exact le_rfl
  · intro p _ _
    exact sq_nonneg _

theorem sum_term_sq_le (A : Link 4 (doubleIndex n) → ℝ)
    (b : Cell.Corner) (μ ν : Fin 4) (j : Fin 2) :
    (∑ y : Site 4 n, (Cell.term (cellField A y) b μ ν j)^2) ≤ curlEnergy A := by
  unfold Cell.term
  split_ifs with hb hμν hj hνμ
  · simpa using curlEnergy_nonneg A
  · simp only [neg_sq]
    exact sum_cellCurl_sq_le A _ μ ν hμν (pathPrefix_lt_two b ν μ) (pathPrefix_lt_two b ν ν)
  · simpa using curlEnergy_nonneg A
  · exact sum_cellCurl_sq_le A _ ν μ hνμ.1
      (shiftedPrefix_lt_two b ν μ ν j) (shiftedPrefix_lt_two b ν μ μ j)
  · simpa using curlEnergy_nonneg A

/-- Cauchy--Schwarz pays only the eight slots in the finite Stokes identity. -/
theorem gaugeResidual_sq_le (A : Link 4 (doubleIndex n) → ℝ) (hQ : linearBlock A = 0)
    (y : Site 4 n) (b : Cell.Corner) (μ : Fin 4) :
    (A (embed y (Cell.corner b), μ) - gradient (gaugePotential A) (embed y (Cell.corner b), μ))^2 ≤
      8 * ∑ ν : Fin 4, ∑ j : Fin 2, (Cell.term (cellField A y) b μ ν j)^2 := by
  rw [gaugeResidual_cell A hQ]
  simpa only [Fintype.sum_prod_type, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat, show (4:ℝ)*2=8 by norm_num] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun p : Fin 4 × Fin 2 => Cell.term (cellField A y) b μ p.1 p.2))

theorem sum_gaugeResidual_cell_sq_le (A : Link 4 (doubleIndex n) → ℝ)
    (hQ : linearBlock A = 0) (b : Cell.Corner) (μ : Fin 4) :
    (∑ y : Site 4 n,
      (A (embed y (Cell.corner b), μ) - gradient (gaugePotential A) (embed y (Cell.corner b), μ))^2) ≤
      64 * curlEnergy A := by
  calc
    _ ≤ ∑ y : Site 4 n, 8 * ∑ ν : Fin 4, ∑ j : Fin 2,
        (Cell.term (cellField A y) b μ ν j)^2 :=
      Finset.sum_le_sum fun y _ => gaugeResidual_sq_le A hQ y b μ
    _ = 8 * ∑ ν : Fin 4, ∑ j : Fin 2, ∑ y : Site 4 n,
        (Cell.term (cellField A y) b μ ν j)^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro ν _
      rw [Finset.sum_comm]
    _ ≤ 8 * ∑ _ν : Fin 4, ∑ _j : Fin 2, curlEnergy A := by
      gcongr with ν _ j _
      exact sum_term_sq_le A b μ ν j
    _ = 64 * curlEnergy A := by simp; ring

/-- A constructive volume-independent gauge estimate for the actual block fiber.
The constant 4096 is conservative: eight Stokes slots, eight faces per link,
and 64 parity/direction choices. -/
theorem gaugeResidual_energy_le (A : Link 4 (doubleIndex n) → ℝ) (hQ : linearBlock A = 0) :
    (∑ l : Link 4 (doubleIndex n), (A l - gradient (gaugePotential A) l)^2) ≤
      4096 * curlEnergy A := by
  rw [Fintype.sum_prod_type]
  rw [← Equiv.sum_comp (siteEquiv n)]
  simp only [Fintype.sum_prod_type, siteEquiv, Equiv.coe_fn_mk]
  rw [Finset.sum_comm]
  calc
    _ = ∑ b : Cell.Corner, ∑ μ : Fin 4, ∑ y : Site 4 n,
        (A (embed y (Cell.corner b), μ) - gradient (gaugePotential A) (embed y (Cell.corner b), μ))^2 := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ ≤ ∑ _b : Cell.Corner, ∑ _μ : Fin 4, 64 * curlEnergy A := by
      gcongr with b _ μ _
      exact sum_gaugeResidual_cell_sq_le A hQ b μ
    _ = 4096 * curlEnergy A := by norm_num [Fintype.card_fun]; ring


abbrev LinkSpace (n : ℕ) := EuclideanSpace ℝ (Link 4 (doubleIndex n))
abbrev SiteSpace (n : ℕ) := EuclideanSpace ℝ (Site 4 (doubleIndex n))
abbrev CurlSpace (n : ℕ) := EuclideanSpace ℝ (Plaquette 4 (doubleIndex n))

def blockLinearMap (n : ℕ) : LinkSpace n →ₗ[ℝ] EuclideanSpace ℝ (Link 4 n) where
  toFun A := WithLp.toLp 2 (linearBlock A)
  map_add' A B := by ext l; simp [linearBlock, add_assoc, add_left_comm, add_comm]
  map_smul' r A := by ext l; simp [linearBlock, mul_add]

def gradientLinearMap (n : ℕ) : SiteSpace n →ₗ[ℝ] LinkSpace n where
  toFun φ := WithLp.toLp 2 (gradient φ)
  map_add' φ ψ := by ext l; simp [gradient]; ring
  map_smul' r φ := by ext l; simp [gradient, mul_sub]

def curlLinearMap (n : ℕ) : LinkSpace n →ₗ[ℝ] CurlSpace n where
  toFun A := WithLp.toLp 2 (curl A)
  map_add' A B := by ext p; simp [curl, curlAt]; ring
  map_smul' r A := by ext p; simp [curl, curlAt, mul_sub, mul_add]

/-- All gradients preserving the coarse field, rather than all gradients. -/
def gaugeSubspace (n : ℕ) : Submodule ℝ (LinkSpace n) :=
  (gradientLinearMap n).range ⊓ (blockLinearMap n).ker

theorem gradient_mem_gaugeSubspace (φ : Site 4 (doubleIndex n) → ℝ) (hφ : FiberGauge n φ) :
    WithLp.toLp 2 (gradient φ) ∈ gaugeSubspace n := by
  constructor
  · exact ⟨WithLp.toLp 2 φ, rfl⟩
  · change WithLp.toLp 2 (linearBlock (gradient φ)) = 0
    rw [show linearBlock (gradient φ) = 0 from hφ]
    rfl

theorem mem_gaugeSubspace_iff (v : LinkSpace n) :
    v ∈ gaugeSubspace n ↔ ∃ φ : Site 4 (doubleIndex n) → ℝ,
      FiberGauge n φ ∧ v = WithLp.toLp 2 (gradient φ) := by
  constructor
  · rintro ⟨⟨φ, hφ⟩, hQ⟩
    refine ⟨φ, ?_, hφ.symm⟩
    change FiberGauge n (fun x => φ x)
    rw [FiberGauge]
    have hz : blockLinearMap n v = 0 := hQ
    rw [← hφ] at hz
    exact congrArg (WithLp.ofLp) hz
  · rintro ⟨φ, hφ, rfl⟩
    exact gradient_mem_gaugeSubspace φ hφ

/-- The physical part of the eliminated sector, in ordinary fine-link L2. -/
def physicalSubspace (n : ℕ) : Submodule ℝ (LinkSpace n) :=
  (blockLinearMap n).ker ⊓ (gaugeSubspace n)ᗮ

theorem norm_curl_sq (A : LinkSpace n) : ‖curlLinearMap n A‖^2 = curlEnergy A := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- The gauge-quotient gap; its positive constant is chosen before n. -/
theorem uniform_fluctuation_gap (A : Link 4 (doubleIndex n) → ℝ) (hQ : linearBlock A = 0) :
    (1 / 4096 : ℝ) * (Metric.infDist (WithLp.toLp 2 A) (gaugeSubspace n : Set (LinkSpace n)))^2 ≤
      curlEnergy A := by
  let g : LinkSpace n := WithLp.toLp 2 (gradient (gaugePotential A))
  have hg : g ∈ gaugeSubspace n :=
    gradient_mem_gaugeSubspace _ (gaugePotential_fiberGauge A)
  have hd : Metric.infDist (WithLp.toLp 2 A) (gaugeSubspace n : Set (LinkSpace n)) ≤
      ‖WithLp.toLp 2 A - g‖ := by
    simpa only [dist_eq_norm] using (Metric.infDist_le_dist_of_mem (x := WithLp.toLp 2 A) hg)
  have hs := (sq_le_sq₀ Metric.infDist_nonneg (norm_nonneg _)).2 hd
  have hn : ‖WithLp.toLp 2 A - g‖^2 =
      ∑ l : Link 4 (doubleIndex n), (A l - gradient (gaugePotential A) l)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [hn] at hs
  have he := gaugeResidual_energy_le A hQ
  nlinarith

/-- On the orthogonal physical sector the quotient distance is the full norm. -/
theorem physical_energy_bound (A : physicalSubspace n) :
    ‖A‖^2 ≤ 4096 * curlEnergy (A : LinkSpace n) := by
  let g : LinkSpace n := WithLp.toLp 2 (gradient (gaugePotential (A : LinkSpace n)))
  have hg : g ∈ gaugeSubspace n :=
    gradient_mem_gaugeSubspace _ (gaugePotential_fiberGauge (A : LinkSpace n))
  have hi : inner ℝ (A : LinkSpace n) g = 0 :=
    Submodule.inner_left_of_mem_orthogonal hg A.property.2
  have hQ : linearBlock (A : LinkSpace n) = 0 :=
    congrArg WithLp.ofLp A.property.1
  have he := gaugeResidual_energy_le (A : LinkSpace n) hQ
  have hn : ‖(A : LinkSpace n) - g‖^2 =
      ∑ l : Link 4 (doubleIndex n), ((A : LinkSpace n) l - gradient (gaugePotential (A : LinkSpace n)) l)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [← hn, norm_sub_sq_real, hi] at he
  have hg0 := sq_nonneg ‖g‖
  change ‖(A : LinkSpace n)‖^2 ≤ _
  nlinarith

/-! ## Actual SU(2) quadratic response -/

/-- The ordinary, unnormalized Hilbert--Schmidt square. -/
def matrixSquare (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖^2

theorem potential_eq_matrixSquare (U : SU2) :
    SU2WilsonBlockIntegration.potential U = (1/4:ℝ) * matrixSquare (U.val - 1) := by
  have hu := Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup U.property)
  have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 0).re) hu
  have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 1 1).re) hu
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Complex.star_def, Complex.add_re, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Matrix.one_apply, ite_true, Complex.one_re] at h0 h1
  simp [SU2WilsonBlockIntegration.potential, specialUnitaryWilsonPotential, matrixSquare,
    Matrix.trace, Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply, Matrix.sub_apply,
    Matrix.one_apply, Complex.sub_re, Complex.sub_im]
  nlinarith

/-- Unitarity forces every derivative at the identity to be anti-Hermitian. -/
theorem tangent_star_eq_neg {U : ℝ → SU2} {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hzero : U 0 = 1) (h : HasDerivAt (fun t => (U t).val) A 0) : star A = -A := by
  have hp := hasDerivAt_matrix_mul h h.star
  have hc : (fun t => (U t).val * star (U t).val) = (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    funext t
    exact Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup (U t).property)
  rw [hc] at hp
  have he := hp.unique (hasDerivAt_const_matrix 1 0)
  simp only [hzero, Submonoid.coe_one, star_one, mul_one, one_mul] at he
  exact eq_neg_of_add_eq_zero_right he

theorem hasDerivAt_holonomy_identity (U : ℝ → Link d n → SU2)
    (A : Link d n → Matrix (Fin 2) (Fin 2) ℂ)
    (hzero : ∀ l, U 0 l = 1)
    (hderiv : ∀ l, HasDerivAt (fun t => (U t l).val) (A l) 0) (p : Plaquette d n) :
    HasDerivAt (fun t => (holonomy (fun i => U t (linkAt p i))).val) (curl A p) 0 := by
  have h01 := hasDerivAt_matrix_mul (hderiv (linkAt p 0)) (hderiv (linkAt p 1))
  have h012 := hasDerivAt_matrix_mul h01 (hderiv (linkAt p 2)).star
  have h0123 := hasDerivAt_matrix_mul h012 (hderiv (linkAt p 3)).star
  simpa [holonomy, Submonoid.coe_mul, ← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star, hzero,
    Submonoid.coe_one, star_one, mul_one, one_mul,
    tangent_star_eq_neg (hzero _) (hderiv _), curl, curlAt, linkAt, sub_eq_add_neg] using h0123

/-- The genuine Wilson leading term, with its normalization and no linear term. -/
theorem tendsto_potential_quadratic {U : ℝ → SU2} {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hzero : U 0 = 1) (h : HasDerivAt (fun t => (U t).val) A 0) :
    Tendsto (fun t => SU2WilsonBlockIntegration.potential (U t) / t^2) (𝓝[≠] 0)
      (𝓝 ((1/4:ℝ) * matrixSquare A)) := by
  have hs := h.tendsto_slope_zero
  simp only [zero_add, hzero, Submonoid.coe_one] at hs
  have hc : Continuous matrixSquare := by unfold matrixSquare; fun_prop
  have hl := (hc.tendsto A).comp hs
  have he (t : ℝ) : matrixSquare (t⁻¹ • ((U t).val - 1)) = matrixSquare ((U t).val - 1) / t^2 := by
    simp only [matrixSquare, Matrix.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, inv_pow]
    norm_num only [Fin.sum_univ_two, div_eq_mul_inv]
    ring!
  have hm := (tendsto_const_nhds (x := (1/4:ℝ))).mul hl
  convert hm using 1
  funext t
  change SU2WilsonBlockIntegration.potential (U t) / t^2 =
    (1/4:ℝ) * matrixSquare (t⁻¹ • ((U t).val - 1))
  rw [he t, potential_eq_matrixSquare]
  ring

/-- The Pauli normalization A=i(a_1 sigma_1+a_2 sigma_2+a_3 sigma_3). -/
def pauliTangent (a : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I * a 2, a 1 + Complex.I * a 0;
    -a 1 + Complex.I * a 0, -Complex.I * a 2]

theorem matrixSquare_pauliTangent (a : Fin 3 → ℝ) :
    matrixSquare (pauliTangent a) = 2 * ∑ i : Fin 3, (a i)^2 := by
  simp [matrixSquare, pauliTangent, Fin.sum_univ_two, Fin.sum_univ_three,
    Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring


/-- Gauge motion of the actual group-valued links has the expected linearization. -/
theorem hasDerivAt_gaugeAct_identity (U : ℝ → Link d n → SU2)
    (g : ℝ → Site d n → SU2)
    (A : Link d n → Matrix (Fin 2) (Fin 2) ℂ)
    (B : Site d n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ l, U 0 l = 1) (hg : ∀ x, g 0 x = 1)
    (hdU : ∀ l, HasDerivAt (fun t => (U t l).val) (A l) 0)
    (hdg : ∀ x, HasDerivAt (fun t => (g t x).val) (B x) 0) (l : Link d n) :
    HasDerivAt (fun t => (WilsonDyadicGeometry.gaugeAct (g t) (U t) l).val)
      (A l - gradient B l) 0 := by
  have h := hasDerivAt_matrix_mul (hasDerivAt_matrix_mul (hdg l.1) (hdU l))
    (hdg (l.1 + step l.2)).star
  have hd : HasDerivAt (fun t => (WilsonDyadicGeometry.gaugeAct (g t) (U t) l).val)
      (B l.1 + A l - B (l.1 + step l.2)) 0 := by
    simpa [WilsonDyadicGeometry.gaugeAct, ← Matrix.star_eq_inv, Submonoid.coe_mul,
      Matrix.specialUnitaryGroup.coe_star, hU, hg,
      tangent_star_eq_neg (hg _) (hdg _), sub_eq_add_neg] using h
  convert hd using 1
  unfold gradient
  abel

theorem curl_pauliTangent (A : Link d n → Fin 3 → ℝ) (p : Plaquette d n) :
    curl (fun l => pauliTangent (A l)) p = pauliTangent (fun i => curl (fun l => A l i) p) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [curl, curlAt, pauliTangent] <;> ring

/-- Three-color Maxwell action is exactly the leading Wilson plaquette term. -/
theorem tendsto_wilsonPlaquette_quadratic (U : ℝ → Link d n → SU2)
    (A : Link d n → Fin 3 → ℝ) (hzero : ∀ l, U 0 l = 1)
    (hderiv : ∀ l, HasDerivAt (fun t => (U t l).val) (pauliTangent (A l)) 0)
    (p : Plaquette d n) :
    Tendsto (fun t => SU2WilsonBlockIntegration.potential
      (holonomy (fun i => U t (linkAt p i))) / t^2) (𝓝[≠] 0)
      (𝓝 ((1/2:ℝ) * ∑ i : Fin 3, (curl (fun l => A l i) p)^2)) := by
  have h := tendsto_potential_quadratic
    (show holonomy (fun i => U 0 (linkAt p i)) = 1 by simp [holonomy, hzero])
    (hasDerivAt_holonomy_identity U (fun l => pauliTangent (A l)) hzero hderiv p)
  rw [curl_pauliTangent, matrixSquare_pauliTangent] at h
  convert h using 1 <;> ring

/-- The same coercivity constant applies to every finite number of colors. -/
theorem color_gaugeResidual_energy_le {ι : Type*} [Fintype ι]
    (A : ι → Link 4 (doubleIndex n) → ℝ) (hQ : ∀ i, linearBlock (A i) = 0) :
    (∑ i : ι, ∑ l : Link 4 (doubleIndex n),
      (A i l - gradient (gaugePotential (A i)) l)^2) ≤ 4096 * ∑ i : ι, curlEnergy (A i) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => gaugeResidual_energy_le (A i) (hQ i)

/-- A concrete eliminated fluctuation with nonzero curvature. -/
def transverseField (n : ℕ) : Link 4 (doubleIndex n) → ℝ :=
  fun l => if l.2 = 0 then (parity l.1 1).val else 0

theorem transverseField_eliminated (n : ℕ) : linearBlock (transverseField n) = 0 := by
  funext l
  by_cases h : l.2 = 0
  · simp [linearBlock, transverseField, h, parity, doubleSite, step, val_doubleCoordinate,
      Nat.mul_mod]
  · simp [linearBlock, transverseField, h]

theorem transverseField_curl (n : ℕ) : curlAt (transverseField n) 0 0 1 = -1 := by
  have hL : 1 < doubleIndex n + 3 := by dsimp [doubleIndex]; omega
  simp [curlAt, transverseField, parity, step, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hL]

theorem transverseField_not_gauge (n : ℕ) :
    WithLp.toLp 2 (transverseField n) ∉ gaugeSubspace n := by
  intro h
  obtain ⟨φ, _, hφ⟩ := (mem_gaugeSubspace_iff _).1 h
  have he : transverseField n = gradient φ := congrArg WithLp.ofLp hφ
  have hc := transverseField_curl n
  rw [he, curlAt_gradient] at hc
  norm_num at hc


/-- The orthogonal physical fiber itself contains a nonzero vector at every volume. -/
theorem physicalSubspace_nontrivial (n : ℕ) : Nontrivial (physicalSubspace n) := by
  let a : LinkSpace n := WithLp.toLp 2 (transverseField n)
  let g := (gaugeSubspace n).starProjection a
  have hg : g ∈ gaugeSubspace n := (gaugeSubspace n).starProjection_apply_mem a
  have ha : a ∈ (blockLinearMap n).ker := by
    change WithLp.toLp 2 (linearBlock (transverseField n)) = 0
    rw [transverseField_eliminated]
    rfl
  have hv : a - g ∈ physicalSubspace n :=
    ⟨(blockLinearMap n).ker.sub_mem ha hg.2,
      Submodule.sub_starProjection_mem_orthogonal a⟩
  have hn : (⟨a-g, hv⟩ : physicalSubspace n) ≠ 0 := by
    intro h
    have he : a - g = 0 := congrArg Subtype.val h
    have hag : a = g := sub_eq_zero.mp he
    apply transverseField_not_gauge n
    change a ∈ gaugeSubspace n
    rw [hag]
    exact hg
  exact ⟨⟨⟨a-g,hv⟩, 0, hn⟩⟩

/-! ## Normalized quadratic fluctuation covariance -/

namespace Gaussian
open MeasureTheory ProbabilityTheory

/-- Curl restricted to the physical integration fiber. -/
def physicalCurl (n : ℕ) : physicalSubspace n →L[ℝ] CurlSpace n :=
  (curlLinearMap n).toContinuousLinearMap.comp (physicalSubspace n).subtypeL

/-- The Maxwell precision before multiplication by beta. -/
def precision (n : ℕ) : physicalSubspace n →L[ℝ] physicalSubspace n :=
  (physicalCurl n).adjoint.comp (physicalCurl n)

theorem precision_symmetric (n : ℕ) : (precision n).toLinearMap.IsSymmetric := by
  intro A B
  change inner ℝ ((physicalCurl n).adjoint (physicalCurl n A)) B =
    inner ℝ A ((physicalCurl n).adjoint (physicalCurl n B))
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

theorem inner_precision (A : physicalSubspace n) :
    inner ℝ A (precision n A) = curlEnergy (A : LinkSpace n) := by
  change inner ℝ A ((physicalCurl n).adjoint (physicalCurl n A)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  exact norm_curl_sq (A : LinkSpace n)

abbrev Mode (n : ℕ) := Fin (Module.finrank ℝ (physicalSubspace n))

def eigenvalue (n : ℕ) : Mode n → ℝ := (precision_symmetric n).eigenvalues rfl

def eigenbasis (n : ℕ) : OrthonormalBasis (Mode n) ℝ (physicalSubspace n) :=
  (precision_symmetric n).eigenvectorBasis rfl

theorem eigenvalue_lower (n : ℕ) (i : Mode n) : (1/4096:ℝ) ≤ eigenvalue n i := by
  have he := physical_energy_bound (eigenbasis n i)
  rw [← inner_precision, show precision n (eigenbasis n i) =
      eigenvalue n i • eigenbasis n i from
      (precision_symmetric n).apply_eigenvectorBasis rfl i,
    real_inner_smul_right (eigenbasis n i) (eigenbasis n i) (eigenvalue n i),
    real_inner_self_eq_norm_sq, (eigenbasis n).norm_eq_one] at he
  norm_num at he
  linarith

theorem eigenvalue_pos (n : ℕ) (i : Mode n) : 0 < eigenvalue n i :=
  lt_of_lt_of_le (by norm_num) (eigenvalue_lower n i)

/-- Inverse precision in the actual physical eigenbasis. -/
def covarianceMatrix (n : ℕ) (β : ℝ) : Matrix (Mode n) (Mode n) ℝ :=
  Matrix.diagonal (fun i => (β * eigenvalue n i)⁻¹)

theorem covarianceMatrix_posSemidef {β : ℝ} (hβ : 0 < β) :
    (covarianceMatrix n β).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  exact inv_nonneg.mpr (mul_pos hβ (eigenvalue_pos n i)).le

/-- Normalized centered quadratic fluctuation law on the block fiber modulo gauge.
For beta > 0 it has precision beta times curl-adjoint-curl. This definition does not
condition an unnormalized massless measure on an event of probability zero. -/
def law (n : ℕ) (β : ℝ) : Measure (physicalSubspace n) :=
  (multivariateGaussian 0 (covarianceMatrix n β)).map (eigenbasis n).repr.symm

instance (n : ℕ) (β : ℝ) : IsProbabilityMeasure (law n β) := by
  unfold law
  exact Measure.isProbabilityMeasure_map (by fun_prop)

instance (n : ℕ) (β : ℝ) : IsGaussian (law n β) := by
  change IsGaussian ((multivariateGaussian 0 (covarianceMatrix n β)).map
    ((eigenbasis n).repr.symm : EuclideanSpace ℝ (Mode n) →L[ℝ] physicalSubspace n))
  infer_instance

theorem covariance_eq {β : ℝ} (hβ : 0 < β) (u v : physicalSubspace n) :
    ProbabilityTheory.covariance (fun A => inner ℝ u A) (fun A => inner ℝ v A) (law n β) =
      ∑ i : Mode n, (eigenbasis n).repr u i * (eigenbasis n).repr v i / (β * eigenvalue n i) := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]
  change covarianceBilin ((multivariateGaussian 0 (covarianceMatrix n β)).map
    ((eigenbasis n).repr.symm : EuclideanSpace ℝ (Mode n) →L[ℝ] physicalSubspace n)) u v = _
  rw [covarianceBilin_map IsGaussian.memLp_two_id, LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.symm_symm, covarianceBilin_multivariateGaussian (covarianceMatrix_posSemidef hβ)]
  simp only [covarianceMatrix, Matrix.mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv]
  ring!

/-- Uniform covariance-operator bound in fine-link L2 normalization. -/
theorem variance_le {β : ℝ} (hβ : 0 < β) (u : physicalSubspace n) :
    ProbabilityTheory.variance (fun A => inner ℝ u A) (law n β) ≤ (4096 / β) * ‖u‖^2 := by
  rw [← covariance_self (by fun_prop), covariance_eq hβ]
  have hinv (i : Mode n) : (β * eigenvalue n i)⁻¹ ≤ 4096 / β := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (mul_pos hβ (eigenvalue_pos n i)) hβ).2
    have hi := eigenvalue_lower n i
    have hm := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ 4096 * eigenvalue n i by linarith) hβ.le
    nlinarith
  calc
    _ ≤ ∑ i : Mode n, (4096 / β) * ((eigenbasis n).repr u i)^2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [div_eq_mul_inv, pow_two, mul_comm] using
        mul_le_mul_of_nonneg_left (hinv i) (sq_nonneg ((eigenbasis n).repr u i))
    _ = (4096 / β) * ‖u‖^2 := by
      rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq, (eigenbasis n).repr.norm_map]

/-- Every nonzero physical test has positive quadratic variance. -/
theorem variance_pos {β : ℝ} (hβ : 0 < β) {u : physicalSubspace n} (hu : u ≠ 0) :
    0 < ProbabilityTheory.variance (fun A => inner ℝ u A) (law n β) := by
  rw [← covariance_self (by fun_prop), covariance_eq hβ]
  have hx : ∃ i : Mode n, (eigenbasis n).repr u i ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    apply (eigenbasis n).repr.injective
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := hx
  apply Finset.sum_pos'
  · intro j _
    exact div_nonneg (mul_self_nonneg _) (mul_pos hβ (eigenvalue_pos n j)).le
  · exact ⟨i, Finset.mem_univ _, div_pos (mul_self_pos.mpr hi) (mul_pos hβ (eigenvalue_pos n i))⟩

/-- The covariance is the inverse of beta times the physical Maxwell precision. -/
theorem covariance_precision {β : ℝ} (hβ : 0 < β) (u v : physicalSubspace n) :
    ProbabilityTheory.covariance (fun A => inner ℝ (β • precision n u) A)
      (fun A => inner ℝ v A) (law n β) = inner ℝ u v := by
  rw [covariance_eq hβ, ← (eigenbasis n).repr.inner_map_map u v]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, map_smul, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (eigenbasis n).repr (precision n u) i =
      eigenvalue n i * (eigenbasis n).repr u i :=
    (precision_symmetric n).eigenvectorBasis_apply_self_apply rfl u i
  rw [hi]
  field_simp [ne_of_gt hβ, ne_of_gt (eigenvalue_pos n i)]


/-- Test vector for one actual lattice curvature component. -/
def curvatureVector (n : ℕ) (p : Plaquette 4 (doubleIndex n)) : physicalSubspace n :=
  (physicalCurl n).adjoint (EuclideanSpace.basisFun _ ℝ p)

theorem curvatureVector_inner (p : Plaquette 4 (doubleIndex n)) (A : physicalSubspace n) :
    inner ℝ (curvatureVector n p) A = curl (A : LinkSpace n) p := by
  rw [curvatureVector, ContinuousLinearMap.adjoint_inner_left, EuclideanSpace.basisFun_inner]
  rfl

theorem abs_curvature_le (p : Plaquette 4 (doubleIndex n)) (A : physicalSubspace n) :
    |curl (A : LinkSpace n) p| ≤ 4 * ‖A‖ := by
  have h (l : Link 4 (doubleIndex n)) : |(A : LinkSpace n) l| ≤ ‖A‖ := by
    exact_mod_cast PiLp.norm_apply_le (A : LinkSpace n) l
  unfold curl curlAt
  have h1 := abs_add_le ((A : LinkSpace n) (p.1, p.2.1.1))
    ((A : LinkSpace n) (p.1 + step p.2.1.1, p.2.1.2))
  have h2 := norm_sub_le ((A : LinkSpace n) (p.1, p.2.1.1) +
    (A : LinkSpace n) (p.1 + step p.2.1.1, p.2.1.2))
    ((A : LinkSpace n) (p.1 + step p.2.1.2, p.2.1.1))
  have h3 := norm_sub_le ((A : LinkSpace n) (p.1, p.2.1.1) +
    (A : LinkSpace n) (p.1 + step p.2.1.1, p.2.1.2) -
    (A : LinkSpace n) (p.1 + step p.2.1.2, p.2.1.1)) ((A : LinkSpace n) (p.1, p.2.1.2))
  simp only [Real.norm_eq_abs] at h2 h3
  linarith [h (p.1, p.2.1.1), h (p.1 + step p.2.1.1, p.2.1.2),
    h (p.1 + step p.2.1.2, p.2.1.1), h (p.1, p.2.1.2)]

theorem norm_curvatureVector_le (p : Plaquette 4 (doubleIndex n)) : ‖curvatureVector n p‖ ≤ 4 := by
  have h := abs_curvature_le p (curvatureVector n p)
  rw [← curvatureVector_inner, real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h
  nlinarith [norm_nonneg (curvatureVector n p)]

theorem curvature_covariance_eq {β : ℝ} (hβ : 0 < β) (p q : Plaquette 4 (doubleIndex n)) :
    ProbabilityTheory.covariance (fun A : physicalSubspace n => curl (A : LinkSpace n) p)
      (fun A : physicalSubspace n => curl (A : LinkSpace n) q) (law n β) =
      ∑ i : Mode n, (eigenbasis n).repr (curvatureVector n p) i *
        (eigenbasis n).repr (curvatureVector n q) i / (β * eigenvalue n i) := by
  simpa only [curvatureVector_inner] using covariance_eq hβ (curvatureVector n p) (curvatureVector n q)

/-- A conservative volume-independent bound for a local field-strength mark. -/
theorem curvature_variance_le {β : ℝ} (hβ : 0 < β) (p : Plaquette 4 (doubleIndex n)) :
    ProbabilityTheory.variance (fun A : physicalSubspace n => curl (A : LinkSpace n) p) (law n β) ≤
      65536 / β := by
  have h := variance_le hβ (curvatureVector n p)
  simp only [curvatureVector_inner] at h
  have hn := norm_curvatureVector_le p
  have hs : ‖curvatureVector n p‖^2 ≤ 16 := by nlinarith [norm_nonneg (curvatureVector n p)]
  calc
    _ ≤ (4096 / β) * ‖curvatureVector n p‖^2 := h
    _ ≤ (4096 / β) * 16 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 65536 / β := by ring

end Gaussian


end Mettapedia.QuantumTheory.YangMills.WilsonMaxwellBlock
