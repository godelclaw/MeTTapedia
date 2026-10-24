import Mettapedia.InformationTheory.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite probability, prediction and observation

The probability carrier is `Prob`, Mathlib's standard simplex. Elementary
pushforward and expectation laws live here, below the information-theoretic
divergence results. `bind` combines a prior with stochastic kernel rows;
`coarsen` pushes a distribution through a deterministic observation.

Prediction is associative and point masses are its identities. Coarsening
agrees with Mathlib's simplex map and with prediction by point-mass rows.
These laws concern complete normalized distributions, not lists of sampled
outcomes or sums of possibly overlapping explanations.
-/

namespace Mettapedia.InformationTheory.FiniteRV

open Finset

variable {Ω α β : Type*} [Fintype Ω] [DecidableEq α] [DecidableEq β]

/-- The law of the random variable `φ` under the weights `p`. -/
noncomputable def pushforward (p : Ω → ℝ) (φ : Ω → α) (a : α) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => φ ω = a), p ω

theorem pushforward_eq_sum_ite (p : Ω → ℝ) (φ : Ω → α) (a : α) :
    pushforward p φ a = ∑ ω, if φ ω = a then p ω else 0 := by
  unfold pushforward
  rw [Finset.sum_filter]

theorem pushforward_nonneg (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (φ : Ω → α) (a : α) :
    0 ≤ pushforward p φ a :=
  Finset.sum_nonneg fun ω _ => hp ω

theorem sum_pushforward [Fintype α] (p : Ω → ℝ) (φ : Ω → α) :
    ∑ a, pushforward p φ a = ∑ ω, p ω := by
  unfold pushforward
  exact Finset.sum_fiberwise Finset.univ φ p

/-- Expectation of a function of `φ` may be computed on `Ω` or on the law of `φ`. -/
theorem sum_pushforward_mul [Fintype α] (p : Ω → ℝ) (φ : Ω → α) (L : α → ℝ) :
    ∑ a, pushforward p φ a * L a = ∑ ω, p ω * L (φ ω) := by
  unfold pushforward
  simp only [Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ φ (fun ω => p ω * L (φ ω))]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ω hω => ?_
  rw [Finset.mem_filter] at hω
  rw [hω.2]

theorem le_pushforward (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (φ : Ω → α) (ω : Ω) :
    p ω ≤ pushforward p φ (φ ω) := by
  unfold pushforward
  exact Finset.single_le_sum (f := p) (fun ω' _ => hp ω') (by simp)

theorem pushforward_pos_of_pos (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (φ : Ω → α) {ω : Ω}
    (h : 0 < p ω) : 0 < pushforward p φ (φ ω) :=
  lt_of_lt_of_le h (le_pushforward p hp φ ω)

/-- Two maps with the same fibre at `ω` give the same law value there. -/
theorem pushforward_congr_fiber (p : Ω → ℝ) (φ : Ω → α) (ψ : Ω → β) (ω : Ω)
    (h : ∀ ω', φ ω' = φ ω ↔ ψ ω' = ψ ω) :
    pushforward p φ (φ ω) = pushforward p ψ (ψ ω) := by
  unfold pushforward
  congr 1
  ext ω'
  simp [h ω']

theorem pushforward_of_injective (p : Ω → ℝ) (φ : Ω → α) (hφ : Function.Injective φ) (ω : Ω) :
    pushforward p φ (φ ω) = p ω := by
  unfold pushforward
  rw [Finset.sum_eq_single ω]
  · intro ω' hω' hne
    exact (hne (hφ (Finset.mem_filter.1 hω').2)).elim
  · intro h
    exact (h (by simp)).elim

theorem pushforward_pushforward [Fintype α] (p : Ω → ℝ) (φ : Ω → α) (ψ : α → β) (b : β) :
    pushforward (pushforward p φ) ψ b = pushforward p (ψ ∘ φ) b := by
  rw [pushforward_eq_sum_ite (pushforward p φ) ψ b]
  have : ∀ a, (if ψ a = b then pushforward p φ a else 0) =
      pushforward p φ a * (if ψ a = b then 1 else 0) := by
    intro a; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun a _ => this a,
    sum_pushforward_mul p φ (fun a => if ψ a = b then 1 else 0)]
  rw [pushforward_eq_sum_ite]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [Function.comp]
  split_ifs <;> simp

/-- Finite pushforward cannot increase the ℓ¹ distance between arbitrary
real-valued weightings. Normalization is not needed for this inequality. -/
theorem l1_pushforward_le [Fintype α] (p q : Ω → ℝ) (φ : Ω → α) :
    (∑ a, |pushforward p φ a - pushforward q φ a|) ≤ ∑ ω, |p ω - q ω| := by
  classical
  have fiber (a : α) :
      |pushforward p φ a - pushforward q φ a| ≤
        ∑ ω, if φ ω = a then |p ω - q ω| else 0 := by
    rw [pushforward_eq_sum_ite, pushforward_eq_sum_ite]
    have difference :
        (∑ ω, if φ ω = a then p ω else 0) - (∑ ω, if φ ω = a then q ω else 0) =
          ∑ ω, if φ ω = a then p ω - q ω else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases same : φ ω = a <;> simp [same]
    rw [difference]
    calc
      |∑ ω, if φ ω = a then p ω - q ω else 0| ≤
          ∑ ω, |if φ ω = a then p ω - q ω else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ ω, if φ ω = a then |p ω - q ω| else 0 := by
        apply Finset.sum_congr rfl
        intro ω _
        by_cases same : φ ω = a <;> simp [same]
  calc
    (∑ a, |pushforward p φ a - pushforward q φ a|) ≤
        ∑ a, ∑ ω, if φ ω = a then |p ω - q ω| else 0 :=
      Finset.sum_le_sum fun a _ => fiber a
    _ = ∑ ω, |p ω - q ω| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω _
      simp

end Mettapedia.InformationTheory.FiniteRV

namespace Mettapedia.InformationTheory.Prob

open Finset
open Mettapedia.InformationTheory.FiniteRV

variable {S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
/-- A point mass on an arbitrary finite carrier. -/
def dirac [DecidableEq S] (state : S) : Prob S :=
  ⟨fun s => if s = state then 1 else 0, by
    constructor
    · intro s
      change 0 ≤ if s = state then (1 : ℝ) else 0
      split_ifs <;> norm_num
    · simp⟩

omit [Fintype C] [DecidableEq C] in
@[simp] theorem dirac_apply [DecidableEq S] (state s : S) :
    (dirac state).1 s = if s = state then 1 else 0 := rfl

omit [Fintype C] [DecidableEq C] in
theorem expectation_dirac [DecidableEq S] (state : S) (consumer : S → ℝ) :
    ∑ s, (dirac state).1 s * consumer s = consumer state := by
  simp [dirac, ite_mul]

omit [DecidableEq C] in
/-- Apply a finite stochastic kernel to a probability distribution. -/
noncomputable def bind (prior : Prob S) (kernel : S → Prob C) : Prob C :=
  ⟨fun c => ∑ s, prior.1 s * (kernel s).1 c,
    (fun c => Finset.sum_nonneg (fun s _ => mul_nonneg (prior.2.1 s) ((kernel s).2.1 c))), by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, fun s => (kernel s).2.2, mul_one]
      exact prior.2.2⟩

omit [DecidableEq C] in
@[simp] theorem bind_apply (prior : Prob S) (kernel : S → Prob C) (c : C) :
    (bind prior kernel).1 c = ∑ s, prior.1 s * (kernel s).1 c := rfl

omit [DecidableEq C] in
theorem expectation_bind (prior : Prob S) (kernel : S → Prob C) (consumer : C → ℝ) :
    ∑ c, (bind prior kernel).1 c * consumer c =
      ∑ s, prior.1 s * (∑ c, (kernel s).1 c * consumer c) := by
  simp only [bind_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

omit [DecidableEq C] in
/-- A point-mass prior selects exactly one row of a stochastic kernel. -/
@[simp] theorem bind_dirac [DecidableEq S] (state : S) (kernel : S → Prob C) :
    bind (dirac state) kernel = kernel state := by
  apply Subtype.ext
  funext outcome
  exact expectation_dirac state fun source => (kernel source).1 outcome

omit [Fintype C] [DecidableEq C] in
/-- The deterministic identity kernel preserves every prior. -/
@[simp] theorem bind_dirac_right [DecidableEq S] (prior : Prob S) :
    bind prior dirac = prior := by
  apply Subtype.ext
  funext state
  simp [bind_apply, dirac_apply, mul_ite]

omit [DecidableEq C] in
/-- Sequential stochastic prediction is associative; kernel order is retained. -/
theorem bind_assoc {D : Type*} [Fintype D] (prior : Prob S)
    (first : S → Prob C) (second : C → Prob D) :
    bind (bind prior first) second = bind prior (fun s => bind (first s) second) := by
  apply Subtype.ext
  funext outcome
  exact expectation_bind prior first fun c => (second c).1 outcome

omit [DecidableEq C] in
/-- A constant kernel discards its input distribution. -/
@[simp] theorem bind_const (prior : Prob S) (result : Prob C) :
    bind prior (fun _ => result) = result := by
  apply Subtype.ext
  funext outcome
  simp [bind_apply, ← Finset.sum_mul, prior.2.2]

/-- Coarsen a finite distribution along an observation map. -/
noncomputable def coarsen (prior : Prob S) (view : S → C) : Prob C :=
  ⟨pushforward prior.1 view,
    (fun c => pushforward_nonneg prior.1 prior.2.1 view c), by
      rw [sum_pushforward]
      exact prior.2.2⟩

@[simp] theorem coarsen_apply (prior : Prob S) (view : S → C) (c : C) :
    (coarsen prior view).1 c = pushforward prior.1 view c := rfl

/-- The finite fibre-sum implementation is Mathlib's simplex map. -/
theorem coarsen_eq_simplex_map (prior : Prob S) (view : S → C) :
    coarsen prior view = stdSimplex.map view prior := by
  apply Subtype.ext
  funext outcome
  simp only [coarsen_apply, pushforward, stdSimplex.map, FunOnFinite.linearMap_apply_apply]
  rfl

omit [Fintype C] [DecidableEq C] in
@[simp] theorem coarsen_id [DecidableEq S] (prior : Prob S) :
    coarsen prior id = prior := by
  rw [coarsen_eq_simplex_map, stdSimplex.map_id_apply]

/-- Successive observations are their composite observation. -/
theorem coarsen_comp {D : Type*} [Fintype D] [DecidableEq D]
    (prior : Prob S) (view : S → C) (next : C → D) :
    coarsen (coarsen prior view) next = coarsen prior (next ∘ view) := by
  simp only [coarsen_eq_simplex_map, stdSimplex.map_comp_apply]

/-- A deterministic observation is a kernel of point masses. -/
theorem coarsen_eq_bind_dirac (prior : Prob S) (view : S → C) :
    coarsen prior view = bind prior (fun s => dirac (view s)) := by
  apply Subtype.ext
  funext outcome
  simp [coarsen_apply, pushforward_eq_sum_ite, bind_apply, dirac_apply, mul_ite, eq_comm]

theorem coarsen_dirac [DecidableEq S] (state : S) (view : S → C) :
    coarsen (dirac state) view = dirac (view state) := by
  apply Subtype.ext
  funext c
  simp [coarsen_apply, pushforward, dirac, eq_comm]

/-- A consumer of the observation has the same expectation on either carrier. -/
theorem coarsen_expectation (prior : Prob S) (view : S → C) (consumer : C → ℝ) :
    ∑ c, (coarsen prior view).1 c * consumer c =
      ∑ s, prior.1 s * consumer (view s) :=
  sum_pushforward_mul prior.1 view consumer

/-- A kernel depending only on an observation acts on its pushforward prior. -/
theorem bind_of_coarsen {D : Type*} [Fintype D]
    (prior : Prob S) (view : S → C) (kernel : C → Prob D) :
    bind prior (kernel ∘ view) = bind (coarsen prior view) kernel := by
  apply Subtype.ext
  funext outcome
  exact (coarsen_expectation prior view (fun c => (kernel c).1 outcome)).symm

theorem coarsen_bind {O : Type*} [Fintype O] (prior : Prob S) (kernel : S → Prob O)
    (view : O → C) :
    coarsen (bind prior kernel) view = bind prior (fun s => coarsen (kernel s) view) := by
  apply Subtype.ext
  funext c
  simp only [coarsen_apply, pushforward, bind_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]

omit [Fintype C] [DecidableEq C] in
/-- ℓ¹ distance on finite normalized distributions. Its normalization is
deliberately not divided by two, so one-step error budgets add directly. -/
def l1Distance (first second : Prob S) : ℝ :=
  ∑ state, |first.1 state - second.1 state|

omit [Fintype C] [DecidableEq C] in
theorem l1Distance_nonneg (first second : Prob S) : 0 ≤ l1Distance first second :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [Fintype C] [DecidableEq C] in
@[simp] theorem l1Distance_self (law : Prob S) : l1Distance law law = 0 := by
  simp [l1Distance]

omit [Fintype C] [DecidableEq C] in
theorem l1Distance_symm (first second : Prob S) :
    l1Distance first second = l1Distance second first := by
  apply Finset.sum_congr rfl
  intro state _
  exact abs_sub_comm _ _

omit [Fintype C] [DecidableEq C] in
theorem l1Distance_triangle (first middle last : Prob S) :
    l1Distance first last ≤ l1Distance first middle + l1Distance middle last := by
  simp only [l1Distance, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun state _ => abs_sub_le _ _ _

omit [Fintype C] [DecidableEq C] in
theorem l1Distance_eq_zero_iff (first second : Prob S) :
    l1Distance first second = 0 ↔ first = second := by
  constructor
  · intro zero
    have pointwise := (Finset.sum_eq_zero_iff_of_nonneg
      (fun state _ => abs_nonneg (first.1 state - second.1 state))).mp zero
    apply Subtype.ext
    funext state
    exact sub_eq_zero.mp (abs_eq_zero.mp (pointwise state (Finset.mem_univ state)))
  · rintro rfl
    exact l1Distance_self first

/-- Deterministic observation is nonexpansive in finite ℓ¹ distance. -/
theorem l1Distance_coarsen_le (first second : Prob S) (view : S → C) :
    l1Distance (coarsen first view) (coarsen second view) ≤ l1Distance first second := by
  exact FiniteRV.l1_pushforward_le first.1 second.1 view

omit [DecidableEq C] in
/-- Mixing rowwise perturbations averages their ℓ¹ errors under the prior. -/
theorem l1Distance_bind_le_expectation (prior : Prob S) (first second : S → Prob C) :
    l1Distance (bind prior first) (bind prior second) ≤
      ∑ state, prior.1 state * l1Distance (first state) (second state) := by
  unfold l1Distance
  calc
    (∑ outcome, |(bind prior first).1 outcome - (bind prior second).1 outcome|) =
        ∑ outcome, |∑ state, prior.1 state *
          ((first state).1 outcome - (second state).1 outcome)| := by
      apply Finset.sum_congr rfl
      intro outcome _
      rw [bind_apply, bind_apply, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro state _
      ring
    _ ≤ ∑ outcome, ∑ state, prior.1 state *
          |(first state).1 outcome - (second state).1 outcome| := by
      apply Finset.sum_le_sum
      intro outcome _
      calc
        |∑ state, prior.1 state *
            ((first state).1 outcome - (second state).1 outcome)| ≤
            ∑ state, |prior.1 state *
              ((first state).1 outcome - (second state).1 outcome)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ state, prior.1 state *
              |(first state).1 outcome - (second state).1 outcome| := by
          apply Finset.sum_congr rfl
          intro state _
          rw [abs_mul, abs_of_nonneg (prior.2.1 state)]
    _ = ∑ state, prior.1 state * l1Distance (first state) (second state) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro state _
      rw [← Finset.mul_sum]
      rfl

omit [DecidableEq C] in
/-- A uniform row budget is also a budget for every mixture of those rows. -/
theorem l1Distance_bind_rows_le (prior : Prob S) (first second : S → Prob C) (δ : ℝ)
    (rows : ∀ state, l1Distance (first state) (second state) ≤ δ) :
    l1Distance (bind prior first) (bind prior second) ≤ δ := by
  apply (l1Distance_bind_le_expectation prior first second).trans
  calc
    (∑ state, prior.1 state * l1Distance (first state) (second state)) ≤
        ∑ state, prior.1 state * δ :=
      Finset.sum_le_sum fun state _ =>
        mul_le_mul_of_nonneg_left (rows state) (prior.2.1 state)
    _ = δ := by rw [← Finset.sum_mul, prior.2.2, one_mul]

omit [DecidableEq C] in
/-- Applying one stochastic kernel is nonexpansive in finite ℓ¹ distance. -/
theorem l1Distance_bind_le (first second : Prob S) (kernel : S → Prob C) :
    l1Distance (bind first kernel) (bind second kernel) ≤ l1Distance first second := by
  unfold l1Distance
  calc
    (∑ outcome, |(bind first kernel).1 outcome - (bind second kernel).1 outcome|) =
        ∑ outcome, |∑ state, (first.1 state - second.1 state) *
          (kernel state).1 outcome| := by
      apply Finset.sum_congr rfl
      intro outcome _
      rw [bind_apply, bind_apply, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro state _
      ring
    _ ≤ ∑ outcome, ∑ state, |first.1 state - second.1 state| *
          (kernel state).1 outcome := by
      apply Finset.sum_le_sum
      intro outcome _
      calc
        |∑ state, (first.1 state - second.1 state) * (kernel state).1 outcome| ≤
            ∑ state, |(first.1 state - second.1 state) *
              (kernel state).1 outcome| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ state, |first.1 state - second.1 state| *
              (kernel state).1 outcome := by
          apply Finset.sum_congr rfl
          intro state _
          rw [abs_mul, abs_of_nonneg ((kernel state).2.1 outcome)]
    _ = ∑ state, |first.1 state - second.1 state| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro state _
      rw [← Finset.mul_sum, (kernel state).2.2, mul_one]

omit [Fintype C] [DecidableEq C] in
/-- ℓ¹ error controls every bounded real-valued observer. This general bound
does not use the sharper half-ℓ¹ constant available for indicators. -/
theorem abs_expectation_sub_le_l1 (first second : Prob S) (observer : S → ℝ)
    (bound : ℝ) (bounded : ∀ state, |observer state| ≤ bound) :
    |(∑ state, first.1 state * observer state) -
        ∑ state, second.1 state * observer state| ≤
      bound * l1Distance first second := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ state, (first.1 state * observer state - second.1 state * observer state)| ≤
        ∑ state, |first.1 state * observer state - second.1 state * observer state| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ state, |first.1 state - second.1 state| * |observer state| := by
      apply Finset.sum_congr rfl
      intro state _
      rw [← sub_mul, abs_mul]
    _ ≤ ∑ state, |first.1 state - second.1 state| * bound :=
      Finset.sum_le_sum fun state _ =>
        mul_le_mul_of_nonneg_left (bounded state) (abs_nonneg _)
    _ = bound * l1Distance first second := by
      rw [← Finset.sum_mul, mul_comm]
      rfl

omit [Fintype C] [DecidableEq C] in
/-- Execute a finite action sequence in its supplied order. -/
noncomputable def predict {A : Type*} (kernel : A → S → Prob S)
    (actions : List A) (prior : Prob S) : Prob S :=
  actions.foldl (fun law action => bind law (kernel action)) prior

omit [Fintype C] [DecidableEq C] in
@[simp] theorem predict_nil {A : Type*} (kernel : A → S → Prob S) (prior : Prob S) :
    predict kernel [] prior = prior := rfl

omit [Fintype C] [DecidableEq C] in
@[simp] theorem predict_cons {A : Type*} (kernel : A → S → Prob S)
    (action : A) (actions : List A) (prior : Prob S) :
    predict kernel (action :: actions) prior = predict kernel actions (bind prior (kernel action)) :=
  rfl

omit [Fintype C] [DecidableEq C] in
theorem predict_append {A : Type*} (kernel : A → S → Prob S)
    (first second : List A) (prior : Prob S) :
    predict kernel (first ++ second) prior = predict kernel second (predict kernel first prior) :=
  List.foldl_append

end Mettapedia.InformationTheory.Prob
