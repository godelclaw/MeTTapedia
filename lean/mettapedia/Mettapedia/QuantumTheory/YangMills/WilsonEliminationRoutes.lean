import Mettapedia.QuantumTheory.YangMills.WilsonBoundaryResponse
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Compositional weighted elimination with marked observables

A state carries its actual positive density and reference probability law.
An admissible elimination is a linear operator on marked observables that
preserves normalized expectation and contracts uniform bounds. The existing
GSLT route syntax composes these operators. Its two-observable defect is kept
as a function on the final boundary, with an exact concatenation law. The
third-order remainder also composes exactly, with three covariance
corrections between projected marks and pairwise remainders.

Raw moment data carry a separate quantitative boundary contract. Projection
preserves weighted budgets with factor one, and composition charges the new
conditional moments and each mixed correction. Concrete product integrations
generate an abstract GSLT whose OSLF predicates express these contracts.

Retaining a coordinate is deterministic and need not have a continuous kernel
with respect to product Haar measure. The operator semantics therefore does
not impose such a kernel on exact boundary elimination.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Topology

namespace Mettapedia.QuantumTheory.YangMills.WilsonEliminationRoutes
open WilsonBlockElimination WilsonSeparator CompactTransferGap
open Mettapedia.GSLT.Ultrainfinite

export WilsonBlockElimination (projectLinear)

/-- A concrete weighted configuration space. -/
structure State where
  X : Type
  topology : TopologicalSpace X
  compact : CompactSpace X
  measurable : MeasurableSpace X
  borel : BorelSpace X
  μ : Measure X
  probability : IsProbabilityMeasure μ
  W : C(X, ℝ)
  positive : ∀ x, 0 < W x

attribute [instance] State.topology State.compact State.measurable State.borel State.probability

/-- The density is part of the state; expectation preservation is a proved
admissibility condition on the map between its observables. -/
structure Step (a b : State) where
  project : C(a.X, ℝ) →ₗ[ℝ] C(b.X, ℝ)
  expectation : ∀ F, expectation b.μ b.W (project F) = expectation a.μ a.W F
  contract : ∀ F C, (∀ x, |F x| ≤ C) → ∀ y, |project F y| ≤ C

/-- Forward transport of marks along the existing finite GSLT routes. -/
def action {a b : State} : Route Step a b → C(a.X, ℝ) →ₗ[ℝ] C(b.X, ℝ)
  | .refl _ => LinearMap.id
  | .cons e r => (action r).comp e.project

@[simp] theorem action_refl (a : State) (F : C(a.X, ℝ)) : action (.refl a) F = F := rfl

@[simp] theorem action_cons {a b c : State} (e : Step a b) (r : Route Step b c)
    (F : C(a.X, ℝ)) : action (.cons e r) F = action r (e.project F) := rfl

theorem action_append {a b c : State} (r : Route Step a b) (s : Route Step b c)
    (F : C(a.X, ℝ)) : action (r.append s) F = action s (action r F) := by
  induction r with
  | refl => rfl
  | cons e r ih => exact ih s (e.project F)

/-- Every finite chain preserves the original weighted expectation. -/
theorem expectation_action {a b : State} (r : Route Step a b) (F : C(a.X, ℝ)) :
    expectation b.μ b.W (action r F) = expectation a.μ a.W F := by
  induction r with
  | refl => rfl
  | cons e r ih => rw [action_cons, ih, e.expectation]

/-- Every finite chain preserves the original uniform observable bound. -/
theorem action_contract {a b : State} (r : Route Step a b)
    (F : C(a.X, ℝ)) (C : ℝ) (hF : ∀ x, |F x| ≤ C) :
    ∀ y, |action r F y| ≤ C := by
  induction r with
  | refl => exact hF
  | cons e r ih => exact ih _ (e.contract F C hF)

/-- A scalar contraction also preserves a uniform sum of absolute marked
responses. The signs are chosen at the output point and then held fixed
through the linear projection. No sum of separate suprema is substituted. -/
theorem sum_abs_action_le {ι : Type*} {a b : State} (r : Route Step a b)
    (s : Finset ι) (F : ι → C(a.X, ℝ)) {C : ℝ}
    (hF : ∀ x, ∑ i ∈ s, |F i x| ≤ C) :
    ∀ y, ∑ i ∈ s, |action r (F i) y| ≤ C := by
  classical
  intro y
  let ε : ι → ℝ := fun i ↦ if action r (F i) y < 0 then -1 else 1
  have hε (i : ι) : |ε i| = 1 := by dsimp [ε]; split_ifs <;> norm_num
  have hg : ∀ x, |(∑ i ∈ s, ε i • F i) x| ≤ C := by
    intro x
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [abs_mul, hε, one_mul] using hF x
  have h := action_contract r _ C hg y
  have heq : action r (∑ i ∈ s, ε i • F i) y = ∑ i ∈ s, |action r (F i) y| := by
    simp only [map_sum, map_smul, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [ε]
    split_ifs with hi
    · simp [abs_of_neg hi]
    · simp [abs_of_nonneg (le_of_not_gt hi)]
  rw [heq, abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))] at h
  exact h

/-- Weighted row budgets survive projection of every entry under the same
normalized integration map, with contraction factor one. -/
theorem weightedResponse_action_le {ι : Type*} [Fintype ι] [PseudoMetricSpace ι]
    {a b : State} (r : Route Step a b) (η : ℝ) (A : ι → ι → C(a.X, ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ x, WilsonBoundaryResponse.weightedResponseSeminorm η
      (fun i j ↦ A i j x) ≤ C) :
    ∀ y, WilsonBoundaryResponse.weightedResponseSeminorm η
      (fun i j ↦ action r (A i j) y) ≤ C := by
  intro y
  apply WilsonBoundaryResponse.weightedResponseSeminorm_le η _ hC
  intro i
  have h := sum_abs_action_le r Finset.univ
    (fun j ↦ Real.exp (η * dist i j) • A i j) (C := C) (fun x ↦ by
      simpa only [ContinuousMap.smul_apply, smul_eq_mul, abs_mul,
        Real.abs_exp, WilsonBoundaryResponse.weightedResponseRow_apply] using
        (WilsonBoundaryResponse.weightedResponseRow_le η i (fun i j ↦ A i j x)).trans (hA x)) y
  simpa only [map_smul, ContinuousMap.smul_apply, smul_eq_mul, abs_mul,
    Real.abs_exp, WilsonBoundaryResponse.weightedResponseRow_apply] using h

/-- The same contraction applies to the full tree-weighted third-response
budget. It is uniform in the number of boundary coordinates. -/
theorem weightedThird_action_le {ι : Type*} [Fintype ι] [PseudoMetricSpace ι]
    {a b : State} (r : Route Step a b) (η : ℝ) (A : ι → ι → ι → C(a.X, ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ x, WilsonBoundaryResponse.weightedThirdSeminorm η
      (fun i j k ↦ A i j k x) ≤ C) :
    ∀ y, WilsonBoundaryResponse.weightedThirdSeminorm η
      (fun i j k ↦ action r (A i j k) y) ≤ C := by
  intro y
  apply WilsonBoundaryResponse.weightedThirdSeminorm_le η _ hC
  intro i
  have h := sum_abs_action_le r Finset.univ
    (fun p : ι × ι ↦ Real.exp (η * WilsonBoundaryResponse.threeTreeLength i p.1 p.2) •
      A i p.1 p.2) (C := C) (fun x ↦ by
      simpa only [Fintype.sum_prod_type, ContinuousMap.smul_apply, smul_eq_mul, abs_mul,
        Real.abs_exp, WilsonBoundaryResponse.weightedThirdRow_apply] using
        (WilsonBoundaryResponse.weightedThirdRow_le η i (fun i j k ↦ A i j k x)).trans (hA x)) y
  simpa only [Fintype.sum_prod_type, map_smul, ContinuousMap.smul_apply, smul_eq_mul,
    abs_mul, Real.abs_exp, WilsonBoundaryResponse.weightedThirdRow_apply] using h

/-- The full transported covariance remainder, still an observable. -/
def remainder {a b : State} (r : Route Step a b) (F G : C(a.X, ℝ)) : C(b.X, ℝ) :=
  action r (F * G) - action r F * action r G

theorem abs_remainder_le {a b : State} (r : Route Step a b) (F G : C(a.X, ℝ))
    {CF CG : ℝ} (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hF : ∀ x, |F x| ≤ CF) (hG : ∀ x, |G x| ≤ CG) (y : b.X) :
    |remainder r F G y| ≤ 2 * CF * CG := by
  have hp := action_contract r (F * G) (CF * CG) (fun x ↦ by
    rw [ContinuousMap.mul_apply, abs_mul]
    exact mul_le_mul (hF x) (hG x) (abs_nonneg _) hCF) y
  have hq : |action r F y * action r G y| ≤ CF * CG := by
    rw [abs_mul]
    exact mul_le_mul (action_contract r F CF hF y) (action_contract r G CG hG y)
      (abs_nonneg _) hCF
  change |action r (F * G) y - action r F y * action r G y| ≤ _
  exact (abs_sub _ _).trans (by nlinarith)

@[simp] theorem remainder_refl (a : State) (F G : C(a.X, ℝ)) :
    remainder (.refl a) F G = 0 := by simp [remainder]

/-- Earlier remainders are transported through later eliminations and added
to the later remainder. Neither term is dropped. -/
theorem remainder_append {a b c : State} (r : Route Step a b) (s : Route Step b c)
    (F G : C(a.X, ℝ)) :
    remainder (r.append s) F G =
      action s (remainder r F G) + remainder s (action r F) (action r G) := by
  simp only [remainder, action_append, map_sub]
  abel

/-- Exact finite-chain two-observable transport against the actual densities. -/
theorem covariance_action {a b : State} (r : Route Step a b) (F G : C(a.X, ℝ)) :
    covariance a.μ a.W F G =
      covariance b.μ b.W (action r F) (action r G) +
        expectation b.μ b.W (remainder r F G) := by
  rw [remainder, expectation_sub]
  simp only [covariance, expectation_action]
  ring

/-- Any pointwise estimate on the retained remainder gives the precise
correlation error for the whole chain. -/
theorem covariance_action_error {a b : State} (r : Route Step a b)
    (F G : C(a.X, ℝ)) {ε : ℝ} (h : ∀ y, |remainder r F G y| ≤ ε) :
    |covariance a.μ a.W F G - covariance b.μ b.W (action r F) (action r G)| ≤ ε := by
  rw [covariance_action, add_sub_cancel_left]
  exact abs_expectation_le b.μ b.W _ b.positive h

/-- Bounds for two consecutive route remainders add, because subsequent
conditional expectations contract the first remainder. -/
theorem remainder_append_bound {a b c : State} (r : Route Step a b) (s : Route Step b c)
    (F G : C(a.X, ℝ)) {ε₁ ε₂ : ℝ}
    (h₁ : ∀ y, |remainder r F G y| ≤ ε₁)
    (h₂ : ∀ z, |remainder s (action r F) (action r G) z| ≤ ε₂) :
    ∀ z, |remainder (r.append s) F G z| ≤ ε₁ + ε₂ := by
  intro z
  rw [remainder_append]
  exact (abs_add_le _ _).trans (add_le_add (action_contract s _ ε₁ h₁ z) (h₂ z))

/-- The third-order transport remainder retained by a whole elimination route. -/
def thirdRemainder {a b : State} (r : Route Step a b) (F G H : C(a.X, ℝ)) : C(b.X, ℝ) :=
  thirdMoment (action r) F G H

theorem thirdRemainder_eq_remainders {a b : State} (r : Route Step a b)
    (F G H : C(a.X, ℝ)) :
    thirdRemainder r F G H = remainder r F (G * H) -
      action r G * remainder r F H - action r H * remainder r F G := by
  simp only [thirdRemainder, thirdMoment, remainder, two_smul ℝ, mul_assoc F G H]
  ring

/-- All conditional third cumulants have a volume-independent absolute
bound before any spatial estimate is used. -/
theorem abs_thirdRemainder_le {a b : State} (r : Route Step a b)
    (F G H : C(a.X, ℝ)) {CF CG CH : ℝ} (hCF : 0 ≤ CF) (hCG : 0 ≤ CG) (hCH : 0 ≤ CH)
    (hF : ∀ x, |F x| ≤ CF) (hG : ∀ x, |G x| ≤ CG) (hH : ∀ x, |H x| ≤ CH)
    (y : b.X) : |thirdRemainder r F G H y| ≤ 6 * CF * CG * CH := by
  have hFGH := abs_remainder_le r F (G * H) hCF (mul_nonneg hCG hCH) hF
    (fun x ↦ by
      rw [ContinuousMap.mul_apply, abs_mul]
      exact mul_le_mul (hG x) (hH x) (abs_nonneg _) hCG) y
  have hFH := abs_remainder_le r F H hCF hCH hF hH y
  have hFG := abs_remainder_le r F G hCF hCG hF hG y
  have hp : |action r G y * remainder r F H y| ≤ CG * (2 * CF * CH) := by
    rw [abs_mul]
    exact mul_le_mul (action_contract r G CG hG y) hFH (abs_nonneg _) hCG
  have hq : |action r H y * remainder r F G y| ≤ CH * (2 * CF * CG) := by
    rw [abs_mul]
    exact mul_le_mul (action_contract r H CH hH y) hFG (abs_nonneg _) hCH
  rw [thirdRemainder_eq_remainders]
  simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply]
  have htri (u v w : ℝ) : |u - v - w| ≤ |u| + |v| + |w| := by
    linarith [abs_sub (u - v) w, abs_sub u v]
  exact (htri _ _ _).trans ((add_le_add (add_le_add hFGH hp) hq).trans_eq (by ring))

/-- Concatenation transports the first third-order remainder and retains
three mixed corrections coupling projected means to pairwise remainders. -/
theorem thirdRemainder_append {a b c : State} (r : Route Step a b) (s : Route Step b c)
    (F G H : C(a.X, ℝ)) :
    thirdRemainder (r.append s) F G H =
      thirdRemainder s (action r F) (action r G) (action r H) +
      action s (thirdRemainder r F G H) +
      remainder s (action r F) (remainder r G H) +
      remainder s (action r G) (remainder r F H) +
      remainder s (action r H) (remainder r F G) := by
  have ht : action (r.append s) = (action s).comp (action r) := by
    apply LinearMap.ext
    intro U
    exact action_append r s U
  simp only [thirdRemainder, ht]
  exact thirdMoment_comp (action r) (action s) F G H

/-- A scalar composition budget retaining all three mixed corrections.
The old means contract with factor one and each mixed covariance costs at
most `2 * B * ε₂`; hence their combined contribution is `6 * B * ε₂`. -/
theorem thirdRemainder_append_bound {a b c : State}
    (r : Route Step a b) (s : Route Step b c) (F G H : C(a.X, ℝ))
    {B ε₂ ε₃ δ₃ : ℝ} (hB : 0 ≤ B) (hε₂ : 0 ≤ ε₂)
    (hF : ∀ x, |F x| ≤ B) (hG : ∀ x, |G x| ≤ B) (hH : ∀ x, |H x| ≤ B)
    (hFG : ∀ y, |remainder r F G y| ≤ ε₂)
    (hFH : ∀ y, |remainder r F H y| ≤ ε₂)
    (hGH : ∀ y, |remainder r G H y| ≤ ε₂)
    (h₃ : ∀ y, |thirdRemainder r F G H y| ≤ ε₃)
    (hδ : ∀ z, |thirdRemainder s (action r F) (action r G) (action r H) z| ≤ δ₃)
    (z : c.X) :
    |thirdRemainder (r.append s) F G H z| ≤ ε₃ + δ₃ + 6 * B * ε₂ := by
  have h₁ := abs_remainder_le s (action r F) (remainder r G H) hB hε₂
    (action_contract r F B hF) hGH z
  have h₂ := abs_remainder_le s (action r G) (remainder r F H) hB hε₂
    (action_contract r G B hG) hFH z
  have h₃' := abs_remainder_le s (action r H) (remainder r F G) hB hε₂
    (action_contract r H B hH) hFG z
  have hprior := action_contract s (thirdRemainder r F G H) ε₃ h₃ z
  have htri (a b c d e : ℝ) : |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
    linarith [abs_add_le a b, abs_add_le (a + b) c, abs_add_le (a + b + c) d,
      abs_add_le (a + b + c + d) e]
  rw [thirdRemainder_append]
  simp only [ContinuousMap.add_apply]
  exact (htri _ _ _ _ _).trans (by linarith [hδ z])

/-- Total third cumulance under the route's original and generated laws. -/
theorem thirdCumulant_action {a b : State} (r : Route Step a b) (F G H : C(a.X, ℝ)) :
    thirdCumulant a.μ a.W F G H =
      thirdCumulant b.μ b.W (action r F) (action r G) (action r H) +
      expectation b.μ b.W (thirdRemainder r F G H) +
      covariance b.μ b.W (action r F) (remainder r G H) +
      covariance b.μ b.W (action r G) (remainder r F H) +
      covariance b.μ b.W (action r H) (remainder r F G) := by
  have ht : expectation a.μ a.W = (expectationLinear b.μ b.W).comp (action r) := by
    funext U
    exact (expectation_action r U).symm
  change thirdMoment (expectation a.μ a.W) F G H = _
  rw [ht]
  exact thirdMoment_comp (action r) (expectationLinear b.μ b.W) F G H

section Concrete
variable {B I : Type} [TopologicalSpace B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
  [TopologicalSpace I] [CompactSpace I] [MeasurableSpace I]
  [BorelSpace I] [SecondCountableTopology I]
  (μ : Measure B) (ν : Measure I) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p)

def source : State :=
  ⟨B × I, inferInstance, inferInstance, inferInstance, inferInstance,
    μ.prod ν, inferInstance, W, hW⟩

def target : State :=
  ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    μ, inferInstance, marginal ν W, marginal_pos ν W hW⟩

/-- The admissibility obligations are discharged for the original weighted
Haar/product integral, rather than postulated for an abstract RG map. -/
def elimination : Step (source μ ν W hW) (target μ ν W hW) where
  project := projectLinear ν W hW
  expectation := expectation_project μ ν W hW
  contract := fun F _ hF => abs_project_le ν W hW F hF

theorem elimination_remainder (F G : C(B × I, ℝ)) :
    remainder (.cons (elimination μ ν W hW) (.refl _)) F G =
      fiberCovariance ν W hW F G := rfl

end Concrete

/-! ## Quantitative boundary data

Raw first, second and third moments remain continuous boundary observables.
Transport projects all of them under the generated density. Keeping only the
first moments would lose both conditional covariance and third cumulance.
The spatial contract is a predicate on this data, separate from admissible
integration transitions.
-/

/-- The actual partition normalization belongs to the weighted state. -/
def State.partition (a : State) : ℝ := ∫ x, a.W x ∂a.μ

theorem State.partition_pos (a : State) : 0 < a.partition :=
  WilsonBlockElimination.partition_pos a.μ a.W a.positive

/-- Three orders of normalized moments on the retained boundary. -/
structure ResponseData (a : State) (ι : Type*) where
  first : ι → C(a.X, ℝ)
  second : ι → ι → C(a.X, ℝ)
  third : ι → ι → ι → C(a.X, ℝ)

namespace ResponseData
variable {ι : Type*} {a b c : State}

/-- Before integrating any variables, moments are ordinary products. -/
def initial (F : ι → C(a.X, ℝ)) : ResponseData a ι where
  first := F
  second := fun i j ↦ F i * F j
  third := fun i j k ↦ F i * F j * F k

def transport (r : Route Step a b) (D : ResponseData a ι) : ResponseData b ι where
  first := fun i ↦ action r (D.first i)
  second := fun i j ↦ action r (D.second i j)
  third := fun i j k ↦ action r (D.third i j k)

theorem transport_append (r : Route Step a b) (s : Route Step b c)
    (D : ResponseData a ι) :
    transport (r.append s) D = transport s (transport r D) := by
  cases D
  simp only [transport, action_append]

def pair (D : ResponseData a ι) (i j : ι) : C(a.X, ℝ) :=
  D.second i j - D.first i * D.first j

def triple (D : ResponseData a ι) (i j k : ι) : C(a.X, ℝ) :=
  D.third i j k - D.second i j * D.first k - D.second i k * D.first j -
    D.second j k * D.first i + 2 * (D.first i * D.first j * D.first k)

@[simp] theorem pair_initial (F : ι → C(a.X, ℝ)) (i j : ι) :
    (initial F).pair i j = 0 := by simp [pair, initial]

@[simp] theorem triple_initial (F : ι → C(a.X, ℝ)) (i j k : ι) :
    (initial F).triple i j k = 0 := by
  simp only [triple, initial]
  ring

theorem pair_transport_initial (r : Route Step a b) (F : ι → C(a.X, ℝ)) (i j : ι) :
    (transport r (initial F)).pair i j = remainder r (F i) (F j) := rfl

theorem triple_transport_initial (r : Route Step a b) (F : ι → C(a.X, ℝ)) (i j k : ι) :
    (transport r (initial F)).triple i j k = thirdRemainder r (F i) (F j) (F k) := by
  simp only [triple, transport, initial, thirdRemainder, thirdMoment, two_smul ℝ]
  ring

/-- The pointwise covariance budget contains the old covariance transported
under the new law and the new covariance of the projected first moments. -/
theorem pair_transport (r : Route Step a b) (D : ResponseData a ι) (i j : ι) :
    (transport r D).pair i j = action r (D.pair i j) +
      remainder r (D.first i) (D.first j) := by
  simp only [pair, transport, remainder, map_sub]
  abel

/-- Transport of moment data retains the old third cumulant and all three
covariances between a first moment and a pairwise remainder. -/
theorem triple_transport (r : Route Step a b) (D : ResponseData a ι) (i j k : ι) :
    (transport r D).triple i j k =
      action r (D.triple i j k) + thirdRemainder r (D.first i) (D.first j) (D.first k) +
      remainder r (D.first i) (D.pair j k) +
      remainder r (D.first j) (D.pair i k) +
      remainder r (D.first k) (D.pair i j) := by
  simp only [triple, pair, transport, thirdRemainder, thirdMoment, remainder,
    mul_sub, map_sub, map_add, two_mul, two_smul ℝ]
  ring

/-- A quantitative contract for the actual normalized boundary moments.
The coordinates and their metric remain parameters of the predicate. -/
structure Contract [Fintype ι] [PseudoMetricSpace ι]
    (η M C₂ C₃ : ℝ) (D : ResponseData a ι) : Prop where
  rate_pos : 0 < η
  mean_nonneg : 0 ≤ M
  pair_nonneg : 0 ≤ C₂
  triple_nonneg : 0 ≤ C₃
  first_bound : ∀ i x, |D.first i x| ≤ M
  pair_bound : ∀ x, WilsonBoundaryResponse.weightedResponseSeminorm η
    (fun i j ↦ D.pair i j x) ≤ C₂
  triple_bound : ∀ x, WilsonBoundaryResponse.weightedThirdSeminorm η
    (fun i j k ↦ D.triple i j k x) ≤ C₃

theorem initial_contract [Fintype ι] [PseudoMetricSpace ι]
    (F : ι → C(a.X, ℝ)) {η M : ℝ} (hη : 0 < η) (hM : 0 ≤ M)
    (hF : ∀ i x, |F i x| ≤ M) : Contract η M 0 0 (initial F) := by
  refine ⟨hη, hM, le_rfl, le_rfl, hF, ?_, ?_⟩
  · intro x
    simp only [pair_initial, ContinuousMap.zero_apply]
    exact le_of_eq (map_zero _)
  · intro x
    simp only [triple_initial, ContinuousMap.zero_apply]
    exact le_of_eq (map_zero _)

/-- The quantitative composition rule. Old budgets survive with factor
one; new conditional moments and all three mixed corrections are charged
separately. These hypotheses specify the estimates a repeated integration
must discharge on its actual generated density. -/
theorem Contract.transport [Fintype ι] [PseudoMetricSpace ι]
    (r : Route Step a b) (D : ResponseData a ι) {η M C₂ C₃ D₂ D₃ E₁ E₂ E₃ : ℝ}
    (hD : Contract η M C₂ C₃ D)
    (h₂ : 0 ≤ D₂) (h₃ : 0 ≤ D₃) (h₁₂ : 0 ≤ E₁) (h₁₃ : 0 ≤ E₂) (h₂₃ : 0 ≤ E₃)
    (hpair : ∀ y, WilsonBoundaryResponse.weightedResponseSeminorm η
      (fun i j ↦ remainder r (D.first i) (D.first j) y) ≤ D₂)
    (hthird : ∀ y, WilsonBoundaryResponse.weightedThirdSeminorm η
      (fun i j k ↦ thirdRemainder r (D.first i) (D.first j) (D.first k) y) ≤ D₃)
    (hmix₁ : ∀ y, WilsonBoundaryResponse.weightedThirdSeminorm η
      (fun i j k ↦ remainder r (D.first i) (D.pair j k) y) ≤ E₁)
    (hmix₂ : ∀ y, WilsonBoundaryResponse.weightedThirdSeminorm η
      (fun i j k ↦ remainder r (D.first j) (D.pair i k) y) ≤ E₂)
    (hmix₃ : ∀ y, WilsonBoundaryResponse.weightedThirdSeminorm η
      (fun i j k ↦ remainder r (D.first k) (D.pair i j) y) ≤ E₃) :
    Contract η M (C₂ + D₂) (C₃ + D₃ + E₁ + E₂ + E₃) (transport r D) := by
  refine ⟨hD.rate_pos, hD.mean_nonneg, add_nonneg hD.pair_nonneg h₂,
    by linarith [hD.triple_nonneg], ?_, ?_, ?_⟩
  · intro i y
    exact action_contract r (D.first i) M (hD.first_bound i) y
  · intro y
    simp_rw [pair_transport, ContinuousMap.add_apply]
    exact (map_add_le_add _ _ _).trans (add_le_add
      (weightedResponse_action_le r η D.pair hD.pair_nonneg hD.pair_bound y) (hpair y))
  · intro y
    simp_rw [triple_transport, ContinuousMap.add_apply]
    exact (map_add_le_add _ _ _).trans (add_le_add
      ((map_add_le_add _ _ _).trans (add_le_add
        ((map_add_le_add _ _ _).trans (add_le_add
          ((map_add_le_add _ _ _).trans (add_le_add
            (weightedThird_action_le r η D.triple hD.triple_nonneg hD.triple_bound y)
            (hthird y))) (hmix₁ y))) (hmix₂ y))) (hmix₃ y))

end ResponseData

/-- Weighted boundary states together with their transported moment data. -/
abbrev BoundaryState (ι : Type) := Σ a : State, ResponseData a ι

/-- Concrete product integrations generate transitions. No spatial estimate
or response contract occurs in the transition's definition. -/
inductive HaarTransition (ι : Type) : BoundaryState ι → BoundaryState ι → Prop where
  | integrate {B I : Type} [TopologicalSpace B] [CompactSpace B]
      [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
      [TopologicalSpace I] [CompactSpace I] [MeasurableSpace I] [BorelSpace I]
      [SecondCountableTopology I]
      (μ : Measure B) (ν : Measure I) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      (W : C(B × I, ℝ)) (hW : ∀ p, 0 < W p)
      (D : ResponseData (source μ ν W hW) ι) :
      HaarTransition ι ⟨source μ ν W hW, D⟩
        ⟨target μ ν W hW, D.transport (.cons (elimination μ ν W hW) (.refl _))⟩

/-- The rewrite relation consists exactly of the concrete Haar/product
integration constructors, while analytic contracts remain native predicates. -/
def haarTheory (ι : Type) : Mettapedia.GSLT.GSLT where
  Term := BoundaryState ι
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := HaarTransition ι
  rewrites_resp_left := by
    intro a b c h e
    cases h
    exact ⟨c, e, rfl⟩
  rewrites_resp_right := by
    intro a b c e h
    cases h
    exact e

def boundaryContract {ι : Type} [Fintype ι] [PseudoMetricSpace ι]
    (η M C₂ C₃ : ℝ) (s : BoundaryState ι) : Prop :=
  s.2.Contract η M C₂ C₃

/-- OSLF diamond asks for an actual next integration state satisfying the
quantitative contract. It does not assert that every state has such a step. -/
theorem haarDiamond_contract_iff {ι : Type} [Fintype ι] [PseudoMetricSpace ι]
    (η M C₂ C₃ : ℝ) (s : BoundaryState ι) :
    Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond (haarTheory ι)
      (boundaryContract η M C₂ C₃) s ↔
      ∃ t, HaarTransition ι s t ∧ boundaryContract η M C₂ C₃ t :=
  Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond_spec _ _ _

/-- The right adjoint in the existing OSLF convention quantifies over
predecessors, so it must not be interpreted as a forward safety condition. -/
theorem haarBox_contract_iff {ι : Type} [Fintype ι] [PseudoMetricSpace ι]
    (η M C₂ C₃ : ℝ) (t : BoundaryState ι) :
    Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltBox (haarTheory ι)
      (boundaryContract η M C₂ C₃) t ↔
      ∀ s, HaarTransition ι s t → boundaryContract η M C₂ C₃ s :=
  Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltBox_spec _ _ _

#print axioms expectation_action
#print axioms remainder_append
#print axioms covariance_action
#print axioms remainder_append_bound
#print axioms elimination
#print axioms thirdRemainder_append
#print axioms thirdCumulant_action

end Mettapedia.QuantumTheory.YangMills.WilsonEliminationRoutes
