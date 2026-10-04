import Mettapedia.QuantumTheory.YangMills.WilsonDyadicGeometry
import Mettapedia.QuantumTheory.YangMills.SU2WilsonBlockIntegration
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.MetricSpace.HausdorffDistance

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
open Finset
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

end Cell

namespace Cell
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

/-- The requested gauge-quotient gap; its positive constant is chosen before n. -/
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

end Mettapedia.QuantumTheory.YangMills.WilsonMaxwellBlock
