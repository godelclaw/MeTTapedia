import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mettapedia.QuantumTheory.YangMills.FiniteOSReconstruction

/-!
# Finite `Q₈` non-abelian strong-coupling lattice gap

A fully explicit *non-abelian* finite lattice gauge canary: the one-link
transfer matrix for the quaternion group `Q₈ = {±1, ±i, ±j, ±k} ⊂ SU(2)`,
with heat-kernel-type class-function weights.

* The group is realized by an explicit multiplication table
  (`q8Mul`, encoding `0 ↦ 1, 1 ↦ -1, 2 ↦ i, 3 ↦ -i, 4 ↦ j, 5 ↦ -j,
  6 ↦ k, 7 ↦ -k`); associativity, identity, inverses, and a
  non-commutativity witness (`ij = k ≠ -k = ji`) are machine-checked.
* The kernel is written in explicit spectral (character) form and proven
  equal to the convolution kernel `k(x · y⁻¹)` of a class function built
  from the character table of `Q₈`
  (`q8StrongCouplingKernel_eq_heat_convolution`): eigenvalue `1` on the
  trivial character, `e⁻²` on the three sign characters (the abelianized
  `Z₂ × Z₂` sector), and `e⁻¹` on the four-dimensional isotypic component
  of the two-dimensional spin representation — the restriction of the
  fundamental `SU(2)` representation.  The slowest decay, hence the gap,
  is carried by the genuinely non-abelian two-dimensional irreducible.
* The complete transfer eigensystem is explicit: the four characters and
  the four spin matrix-coefficient vectors; every observable decomposes in
  this eigenbasis (`q8Observable_eigenbasis`).
* Reflection positivity follows from the spectral form of the self-pairing
  (`q8StrongCouplingKernel_self_pairing`), and the dimensionless transfer
  gap is `-log (e⁻¹) = 1`.

The theorems are finite-lattice only.  The continuum Yang-Mills mass gap is
not claimed.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

universe u

/-! ## Generic finite OS helpers -/

/-- A pointwise-symmetric kernel yields a symmetric OS pairing. -/
theorem osSymmetric_of_kernel_symm {Ω : Type u} [Fintype Ω]
    {K : Ω → Ω → ℝ} (hK : ∀ x y, K x y = K y x) :
    OSSymmetric K := by
  intro f g
  unfold osBilinearForm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hK y x]
  ring

/-- The transfer operator induced by a pointwise-symmetric kernel is
self-adjoint for the OS pairing of the same kernel. -/
theorem osTransferSelfAdjoint_of_kernel_symm {Ω : Type u} [Fintype Ω]
    {K : Ω → Ω → ℝ} (hK : ∀ x y, K x y = K y x) :
    OSTransferSelfAdjoint K (fun f x => ∑ y : Ω, K x y * f y) := by
  intro f g
  unfold osBilinearForm
  have hL : (∑ x : Ω, ∑ y : Ω,
        (∑ z : Ω, K x z * f z) * K x y * g y)
      = ∑ x : Ω, ∑ z : Ω, ∑ y : Ω, K x z * f z * K x y * g y := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
  have hR : (∑ x : Ω, ∑ y : Ω,
        f x * K x y * ∑ z : Ω, K y z * g z)
      = ∑ x : Ω, ∑ y : Ω, ∑ z : Ω, f x * K x y * (K y z * g z) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  rw [hK b a]
  ring

/-- Scaling the kernel scales the OS pairing. -/
theorem osBilinearForm_kernel_div {Ω : Type u} [Fintype Ω]
    (K : Ω → Ω → ℝ) (c : ℝ) (f g : FiniteObservable Ω) :
    osBilinearForm (fun x y => K x y / c) f g
      = osBilinearForm K f g / c := by
  unfold osBilinearForm
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-! ## The quaternion group `Q₈` -/

/-- One-link `Q₈` lattice gauge configurations, encoded as
`0 ↦ 1, 1 ↦ -1, 2 ↦ i, 3 ↦ -i, 4 ↦ j, 5 ↦ -j, 6 ↦ k, 7 ↦ -k`. -/
abbrev Q8OneLinkConfig := Fin 8

/-- The multiplication table of `Q₈` in the fixed encoding. -/
def q8Mul : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7],
    ![1, 0, 3, 2, 5, 4, 7, 6],
    ![2, 3, 1, 0, 6, 7, 5, 4],
    ![3, 2, 0, 1, 7, 6, 4, 5],
    ![4, 5, 7, 6, 1, 0, 2, 3],
    ![5, 4, 6, 7, 0, 1, 3, 2],
    ![6, 7, 4, 5, 3, 2, 1, 0],
    ![7, 6, 5, 4, 2, 3, 0, 1]]

/-- Inverses in `Q₈`: `±1` are self-inverse up to sign, `u⁻¹ = -u` for
`u ∈ {i, j, k}`. -/
def q8Inv : Fin 8 → Fin 8 :=
  ![0, 1, 3, 2, 5, 4, 7, 6]

theorem q8Mul_assoc :
    ∀ a b c : Fin 8, q8Mul (q8Mul a b) c = q8Mul a (q8Mul b c) := by
  decide

theorem q8_one_mul : ∀ a : Fin 8, q8Mul 0 a = a := by decide

theorem q8_mul_one : ∀ a : Fin 8, q8Mul a 0 = a := by decide

theorem q8_inv_mul : ∀ a : Fin 8, q8Mul (q8Inv a) a = 0 := by decide

theorem q8_mul_inv : ∀ a : Fin 8, q8Mul a (q8Inv a) = 0 := by decide

/-- `Q₈` is non-abelian: `i * j = k` but `j * i = -k`. -/
theorem q8_noncommutative : q8Mul 2 4 ≠ q8Mul 4 2 := by decide

theorem q8_ij_eq_k : q8Mul 2 4 = 6 := by decide

theorem q8_ji_eq_neg_k : q8Mul 4 2 = 7 := by decide

/-! ## Characters and eigenvectors -/

/-- Constant transfer eigenvector (the trivial character). -/
def q8ConstantObservable : FiniteObservable Q8OneLinkConfig :=
  fun _ => 1

/-- Sign character with kernel `{±1, ±i}`. -/
def q8SignI : FiniteObservable Q8OneLinkConfig :=
  fun x => if x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 then 1 else -1

/-- Sign character with kernel `{±1, ±j}`. -/
def q8SignJ : FiniteObservable Q8OneLinkConfig :=
  fun x => if x = 0 ∨ x = 1 ∨ x = 4 ∨ x = 5 then 1 else -1

/-- Sign character with kernel `{±1, ±k}`. -/
def q8SignK : FiniteObservable Q8OneLinkConfig :=
  fun x => if x = 0 ∨ x = 1 ∨ x = 6 ∨ x = 7 then 1 else -1

/-- Spin matrix-coefficient vector supported on `{1, -1}`. -/
def q8SpinR : FiniteObservable Q8OneLinkConfig :=
  fun x => if x = 0 then 1 else if x = 1 then -1 else 0

/-- Spin matrix-coefficient vector supported on `{i, -i}`. -/
def q8SpinI : FiniteObservable Q8OneLinkConfig :=
  fun x => if x = 2 then 1 else if x = 3 then -1 else 0

/-- Spin matrix-coefficient vector supported on `{j, -j}`. -/
def q8SpinJ : FiniteObservable Q8OneLinkConfig :=
  fun x => if x = 4 then 1 else if x = 5 then -1 else 0

/-- Spin matrix-coefficient vector supported on `{k, -k}`. -/
def q8SpinK : FiniteObservable Q8OneLinkConfig :=
  fun x => if x = 6 then 1 else if x = 7 then -1 else 0

/-- Character of the two-dimensional spin representation (the restriction
of the fundamental `SU(2)` representation to `Q₈`). -/
def q8SpinCharacter (x : Q8OneLinkConfig) : ℝ :=
  if x = 0 then 2 else if x = 1 then -2 else 0

/-- Transfer eigenvalue on the spin (two-dimensional irreducible) sector. -/
def q8SpinRatio : ℝ := Real.exp (-1)

/-- Transfer eigenvalue on the three sign-character sectors. -/
def q8SignRatio : ℝ := Real.exp (-2)

theorem q8SpinRatio_pos : 0 < q8SpinRatio := Real.exp_pos _

theorem q8SignRatio_pos : 0 < q8SignRatio := Real.exp_pos _

/-- The sign sector decays faster than the spin sector: the gap is carried
by the non-abelian two-dimensional irreducible. -/
theorem q8SignRatio_le_spinRatio : q8SignRatio ≤ q8SpinRatio :=
  Real.exp_le_exp.mpr (by norm_num)

/-! ## The heat-kernel transfer matrix -/

/-- The one-link `Q₈` heat-kernel transfer matrix in explicit spectral
(character) form.  It equals the convolution kernel of the heat-kernel class
function (`q8StrongCouplingKernel_eq_heat_convolution`). -/
def q8StrongCouplingKernel (x y : Q8OneLinkConfig) : ℝ :=
  (1 + q8SignRatio *
        (q8SignI x * q8SignI y + q8SignJ x * q8SignJ y +
          q8SignK x * q8SignK y)
      + 4 * q8SpinRatio *
        (q8SpinR x * q8SpinR y + q8SpinI x * q8SpinI y +
          q8SpinJ x * q8SpinJ y + q8SpinK x * q8SpinK y)) / 8

/-- The heat-kernel class function on `Q₈`: Fourier series over the five
irreducible characters with weights `1`, `e⁻²` (three sign characters), and
`e⁻¹` (spin character, dimension two). -/
def q8HeatClassFunction (g : Q8OneLinkConfig) : ℝ :=
  (1 + q8SignRatio * (q8SignI g + q8SignJ g + q8SignK g)
      + 2 * q8SpinRatio * q8SpinCharacter g) / 8

/-- **Group-theoretic grounding.**  The kernel is the convolution kernel
`k(x · y⁻¹)` of the heat-kernel class function, with `x · y⁻¹` computed by
the genuine `Q₈` multiplication table. -/
theorem q8StrongCouplingKernel_eq_heat_convolution
    (x y : Q8OneLinkConfig) :
    q8StrongCouplingKernel x y = q8HeatClassFunction (q8Mul x (q8Inv y)) := by
  fin_cases x <;> fin_cases y <;>
    (simp +decide [q8StrongCouplingKernel, q8HeatClassFunction,
      q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ, q8SpinK,
      q8SpinCharacter]
     try ring)

/-- The kernel is pointwise symmetric. -/
theorem q8StrongCouplingKernel_symm (x y : Q8OneLinkConfig) :
    q8StrongCouplingKernel x y = q8StrongCouplingKernel y x := by
  unfold q8StrongCouplingKernel
  ring

theorem q8StrongCouplingKernel_symmetric :
    OSSymmetric q8StrongCouplingKernel :=
  osSymmetric_of_kernel_symm q8StrongCouplingKernel_symm

/-- The transfer operator induced by the finite heat kernel. -/
def q8StrongCouplingTransfer
    (f : FiniteObservable Q8OneLinkConfig) :
    FiniteObservable Q8OneLinkConfig :=
  fun x => ∑ y : Q8OneLinkConfig, q8StrongCouplingKernel x y * f y

theorem q8StrongCouplingTransfer_selfAdjoint :
    OSTransferSelfAdjoint q8StrongCouplingKernel q8StrongCouplingTransfer :=
  osTransferSelfAdjoint_of_kernel_symm q8StrongCouplingKernel_symm

/-! ## Spectral coefficient functionals -/

/-- Trivial-character coefficient functional (`8 ×` the vacuum component). -/
def q8S0 (f : FiniteObservable Q8OneLinkConfig) : ℝ :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7

/-- Sign-character coefficient functionals. -/
def q8Si (f : FiniteObservable Q8OneLinkConfig) : ℝ :=
  f 0 + f 1 + f 2 + f 3 - f 4 - f 5 - f 6 - f 7

def q8Sj (f : FiniteObservable Q8OneLinkConfig) : ℝ :=
  f 0 + f 1 - f 2 - f 3 + f 4 + f 5 - f 6 - f 7

def q8Sk (f : FiniteObservable Q8OneLinkConfig) : ℝ :=
  f 0 + f 1 - f 2 - f 3 - f 4 - f 5 + f 6 + f 7

/-- Spin-sector coefficient functionals. -/
def q8DR (f : FiniteObservable Q8OneLinkConfig) : ℝ := f 0 - f 1

def q8DI (f : FiniteObservable Q8OneLinkConfig) : ℝ := f 2 - f 3

def q8DJ (f : FiniteObservable Q8OneLinkConfig) : ℝ := f 4 - f 5

def q8DK (f : FiniteObservable Q8OneLinkConfig) : ℝ := f 6 - f 7

/-- **Spectral form of the self-pairing.**  The OS self-pairing diagonalizes
over the character/matrix-coefficient decomposition, with weight `e⁻²` on
the sign sector and `e⁻¹` on the spin sector. -/
theorem q8StrongCouplingKernel_self_pairing
    (f : FiniteObservable Q8OneLinkConfig) :
    osBilinearForm q8StrongCouplingKernel f f
      = (q8S0 f ^ 2
          + q8SignRatio * (q8Si f ^ 2 + q8Sj f ^ 2 + q8Sk f ^ 2)
          + 4 * q8SpinRatio *
            (q8DR f ^ 2 + q8DI f ^ 2 + q8DJ f ^ 2 + q8DK f ^ 2)) / 8 := by
  unfold osBilinearForm q8StrongCouplingKernel
    q8S0 q8Si q8Sj q8Sk q8DR q8DI q8DJ q8DK
  simp only [Fin.sum_univ_eight]
  simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ, q8SpinK]
  ring

theorem q8StrongCouplingKernel_reflectionPositive :
    OSReflectionPositive q8StrongCouplingKernel := by
  intro f
  rw [q8StrongCouplingKernel_self_pairing f]
  have hs := q8SignRatio_pos
  have hr := q8SpinRatio_pos
  have h1 : 0 ≤ q8Si f ^ 2 + q8Sj f ^ 2 + q8Sk f ^ 2 := by positivity
  have h2 : 0 ≤ q8DR f ^ 2 + q8DI f ^ 2 + q8DJ f ^ 2 + q8DK f ^ 2 := by
    positivity
  have h0 : 0 ≤ q8S0 f ^ 2 := sq_nonneg _
  nlinarith

/-! ## Transfer action on the spectral coefficients -/

theorem q8S0_transfer (f : FiniteObservable Q8OneLinkConfig) :
    q8S0 (q8StrongCouplingTransfer f) = q8S0 f := by
  unfold q8S0 q8StrongCouplingTransfer q8StrongCouplingKernel
  simp only [Fin.sum_univ_eight]
  simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ, q8SpinK]
  ring

theorem q8Si_transfer (f : FiniteObservable Q8OneLinkConfig) :
    q8Si (q8StrongCouplingTransfer f) = q8SignRatio * q8Si f := by
  unfold q8Si q8StrongCouplingTransfer q8StrongCouplingKernel
  simp only [Fin.sum_univ_eight]
  simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ, q8SpinK]
  ring

theorem q8Sj_transfer (f : FiniteObservable Q8OneLinkConfig) :
    q8Sj (q8StrongCouplingTransfer f) = q8SignRatio * q8Sj f := by
  unfold q8Sj q8StrongCouplingTransfer q8StrongCouplingKernel
  simp only [Fin.sum_univ_eight]
  simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ, q8SpinK]
  ring

theorem q8Sk_transfer (f : FiniteObservable Q8OneLinkConfig) :
    q8Sk (q8StrongCouplingTransfer f) = q8SignRatio * q8Sk f := by
  unfold q8Sk q8StrongCouplingTransfer q8StrongCouplingKernel
  simp only [Fin.sum_univ_eight]
  simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ, q8SpinK]
  ring

theorem q8DR_transfer (f : FiniteObservable Q8OneLinkConfig) :
    q8DR (q8StrongCouplingTransfer f) = q8SpinRatio * q8DR f := by
  unfold q8DR q8StrongCouplingTransfer q8StrongCouplingKernel
  simp only [Fin.sum_univ_eight]
  simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ, q8SpinK]
  ring

theorem q8DI_transfer (f : FiniteObservable Q8OneLinkConfig) :
    q8DI (q8StrongCouplingTransfer f) = q8SpinRatio * q8DI f := by
  unfold q8DI q8StrongCouplingTransfer q8StrongCouplingKernel
  simp only [Fin.sum_univ_eight]
  simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ, q8SpinK]
  ring

theorem q8DJ_transfer (f : FiniteObservable Q8OneLinkConfig) :
    q8DJ (q8StrongCouplingTransfer f) = q8SpinRatio * q8DJ f := by
  unfold q8DJ q8StrongCouplingTransfer q8StrongCouplingKernel
  simp only [Fin.sum_univ_eight]
  simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ, q8SpinK]
  ring

theorem q8DK_transfer (f : FiniteObservable Q8OneLinkConfig) :
    q8DK (q8StrongCouplingTransfer f) = q8SpinRatio * q8DK f := by
  unfold q8DK q8StrongCouplingTransfer q8StrongCouplingKernel
  simp only [Fin.sum_univ_eight]
  simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ, q8SpinK]
  ring

/-! ## The explicit eigensystem -/

theorem q8StrongCouplingTransfer_constant_eigen :
    q8StrongCouplingTransfer q8ConstantObservable = q8ConstantObservable := by
  funext x
  fin_cases x <;>
    (unfold q8StrongCouplingTransfer q8StrongCouplingKernel
      q8ConstantObservable
     simp only [Fin.sum_univ_eight]
     simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ,
       q8SpinK]
     try ring)

theorem q8StrongCouplingTransfer_signI_eigen :
    q8StrongCouplingTransfer q8SignI = fun x => q8SignRatio * q8SignI x := by
  funext x
  fin_cases x <;>
    (unfold q8StrongCouplingTransfer q8StrongCouplingKernel
     simp only [Fin.sum_univ_eight]
     simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ,
       q8SpinK]
     try ring)

theorem q8StrongCouplingTransfer_signJ_eigen :
    q8StrongCouplingTransfer q8SignJ = fun x => q8SignRatio * q8SignJ x := by
  funext x
  fin_cases x <;>
    (unfold q8StrongCouplingTransfer q8StrongCouplingKernel
     simp only [Fin.sum_univ_eight]
     simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ,
       q8SpinK]
     try ring)

theorem q8StrongCouplingTransfer_signK_eigen :
    q8StrongCouplingTransfer q8SignK = fun x => q8SignRatio * q8SignK x := by
  funext x
  fin_cases x <;>
    (unfold q8StrongCouplingTransfer q8StrongCouplingKernel
     simp only [Fin.sum_univ_eight]
     simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ,
       q8SpinK]
     try ring)

theorem q8StrongCouplingTransfer_spinR_eigen :
    q8StrongCouplingTransfer q8SpinR = fun x => q8SpinRatio * q8SpinR x := by
  funext x
  fin_cases x <;>
    (unfold q8StrongCouplingTransfer q8StrongCouplingKernel
     simp only [Fin.sum_univ_eight]
     simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ,
       q8SpinK]
     try ring)

theorem q8StrongCouplingTransfer_spinI_eigen :
    q8StrongCouplingTransfer q8SpinI = fun x => q8SpinRatio * q8SpinI x := by
  funext x
  fin_cases x <;>
    (unfold q8StrongCouplingTransfer q8StrongCouplingKernel
     simp only [Fin.sum_univ_eight]
     simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ,
       q8SpinK]
     try ring)

theorem q8StrongCouplingTransfer_spinJ_eigen :
    q8StrongCouplingTransfer q8SpinJ = fun x => q8SpinRatio * q8SpinJ x := by
  funext x
  fin_cases x <;>
    (unfold q8StrongCouplingTransfer q8StrongCouplingKernel
     simp only [Fin.sum_univ_eight]
     simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ,
       q8SpinK]
     try ring)

theorem q8StrongCouplingTransfer_spinK_eigen :
    q8StrongCouplingTransfer q8SpinK = fun x => q8SpinRatio * q8SpinK x := by
  funext x
  fin_cases x <;>
    (unfold q8StrongCouplingTransfer q8StrongCouplingKernel
     simp only [Fin.sum_univ_eight]
     simp +decide [q8SignI, q8SignJ, q8SignK, q8SpinR, q8SpinI, q8SpinJ,
       q8SpinK]
     try ring)

/-- Every observable decomposes in the explicit transfer eigenbasis. -/
theorem q8Observable_eigenbasis
    (f : FiniteObservable Q8OneLinkConfig) :
    f = fun x =>
      (q8S0 f / 8) * q8ConstantObservable x
        + (q8Si f / 8) * q8SignI x
        + (q8Sj f / 8) * q8SignJ x
        + (q8Sk f / 8) * q8SignK x
        + (q8DR f / 2) * q8SpinR x
        + (q8DI f / 2) * q8SpinI x
        + (q8DJ f / 2) * q8SpinJ x
        + (q8DK f / 2) * q8SpinK x := by
  funext x
  fin_cases x <;>
    (simp +decide [q8S0, q8Si, q8Sj, q8Sk, q8DR, q8DI, q8DJ, q8DK,
      q8ConstantObservable, q8SignI, q8SignJ, q8SignK,
      q8SpinR, q8SpinI, q8SpinJ, q8SpinK]
     try ring)

/-! ## The gap -/

/-- The largest transfer eigenvalue. -/
def q8StrongCouplingLambdaOne : ℝ := 1

/-- The slowest-decaying nontrivial eigenvalue: the spin-sector ratio. -/
def q8StrongCouplingLambdaTwo : ℝ := q8SpinRatio

/-- The dimensionless transfer spectral gap. -/
def q8StrongCouplingGap : ℝ :=
  -Real.log (q8StrongCouplingLambdaTwo / q8StrongCouplingLambdaOne)

theorem q8StrongCouplingGap_eq_one : q8StrongCouplingGap = 1 := by
  simp [q8StrongCouplingGap, q8StrongCouplingLambdaTwo,
    q8StrongCouplingLambdaOne, q8SpinRatio, Real.log_exp]

theorem q8StrongCouplingGap_positive : 0 < q8StrongCouplingGap := by
  rw [q8StrongCouplingGap_eq_one]
  norm_num

/-! ## The canary packet -/

/-- A concrete non-abelian finite-lattice mass-gap canary: genuine `Q₈`
group structure, reflection positivity, OS reconstruction, the complete
explicit eigensystem, and the numeric gap `1` carried by the spin sector. -/
structure Q8StrongCouplingGapCanary where
  nonabelian : q8Mul 2 4 ≠ q8Mul 4 2
  groupAssoc : ∀ a b c : Fin 8, q8Mul (q8Mul a b) c = q8Mul a (q8Mul b c)
  kernelIsConvolution :
    ∀ x y : Q8OneLinkConfig,
      q8StrongCouplingKernel x y = q8HeatClassFunction (q8Mul x (q8Inv y))
  reflectionPositive : OSReflectionPositive q8StrongCouplingKernel
  osReconstruction :
    FiniteOSReconstruction q8StrongCouplingKernel q8StrongCouplingTransfer
  constantEigen :
    q8StrongCouplingTransfer q8ConstantObservable = q8ConstantObservable
  signEigen :
    q8StrongCouplingTransfer q8SignI = fun x => q8SignRatio * q8SignI x
  spinEigen :
    q8StrongCouplingTransfer q8SpinR = fun x => q8SpinRatio * q8SpinR x
  signFasterThanSpin : q8SignRatio ≤ q8SpinRatio
  lambdaTwoPositive : 0 < q8StrongCouplingLambdaTwo
  gapEqualsOne : q8StrongCouplingGap = 1

/-- The explicit positive non-abelian canary. -/
def q8StrongCouplingPositiveCanary : Q8StrongCouplingGapCanary where
  nonabelian := q8_noncommutative
  groupAssoc := q8Mul_assoc
  kernelIsConvolution := q8StrongCouplingKernel_eq_heat_convolution
  reflectionPositive := q8StrongCouplingKernel_reflectionPositive
  osReconstruction :=
    finiteOSReconstruction_of_reflectionPositive_selfAdjoint
      q8StrongCouplingKernel_reflectionPositive
      q8StrongCouplingKernel_symmetric
      q8StrongCouplingTransfer_selfAdjoint
  constantEigen := q8StrongCouplingTransfer_constant_eigen
  signEigen := q8StrongCouplingTransfer_signI_eigen
  spinEigen := q8StrongCouplingTransfer_spinR_eigen
  signFasterThanSpin := q8SignRatio_le_spinRatio
  lambdaTwoPositive := q8SpinRatio_pos
  gapEqualsOne := q8StrongCouplingGap_eq_one

/-- End-to-end finite lattice theorem: the explicit `Q₈` strong-coupling
model is genuinely non-abelian, reflection positive, has a self-adjoint OS
transfer operator, and has dimensionless transfer gap `1` carried by the
two-dimensional spin representation.  Finite-lattice only. -/
theorem q8StrongCoupling_nonabelian_massGap_landmark :
    ∃ _ : Q8StrongCouplingGapCanary,
      q8Mul 2 4 ≠ q8Mul 4 2 ∧
        OSReflectionPositive q8StrongCouplingKernel ∧
        q8StrongCouplingGap = 1 ∧
        0 < q8StrongCouplingGap := by
  exact
    ⟨q8StrongCouplingPositiveCanary,
      q8_noncommutative,
      q8StrongCouplingKernel_reflectionPositive,
      q8StrongCouplingGap_eq_one,
      q8StrongCouplingGap_positive⟩

end YangMills
end QuantumTheory
end Mettapedia
