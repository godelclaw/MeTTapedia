import Mettapedia.InformationTheory.FiniteProbability

/-!
# Strong lumpability of finite controlled stochastic kernels

A state observation admits an exact stochastic dynamics when states with the
same observation have the same total transition mass into each observation
class. The quotient kernel is constructed by aggregation and is independent
of the chosen representatives. Probability prediction commutes with the
observation. For an independently supplied coarse kernel, row compatibility
is equivalent to prediction compatibility for every prior, without a choice
of representatives or a surjectivity hypothesis. Those squares compose over
kernels, observations and finite action sequences. This is a law about future
updates, stronger than agreement of the current readout.
-/

namespace Mettapedia.ProbabilityTheory.FiniteLumpability

open Finset
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob

variable {S C A : Type*} [Fintype S] [Fintype C] [DecidableEq C]

/-! ## Prediction with independently supplied kernels -/

/-- Compatible rows give a prediction square. The two observations may have
different source and target carriers; neither needs to be surjective. -/
theorem coarsen_bind_of_rows {T D : Type*} [Fintype T] [Fintype D] [DecidableEq D]
    (sourceView : S → C) (targetView : T → D)
    (fine : S → Prob T) (coarse : C → Prob D)
    (rows : ∀ s, coarsen (fine s) targetView = coarse (sourceView s)) (prior : Prob S) :
    coarsen (bind prior fine) targetView = bind (coarsen prior sourceView) coarse := by
  rw [coarsen_bind]
  simp_rw [rows]
  exact bind_of_coarsen prior sourceView coarse

/-- Exact prediction for every prior is equivalent to agreement at every
kernel row. Point-mass priors establish necessity. -/
theorem coarsen_bind_iff_rows {T D : Type*} [Fintype T] [Fintype D] [DecidableEq D]
    (sourceView : S → C) (targetView : T → D)
    (fine : S → Prob T) (coarse : C → Prob D) :
    (∀ prior : Prob S,
      coarsen (bind prior fine) targetView = bind (coarsen prior sourceView) coarse) ↔
      ∀ s, coarsen (fine s) targetView = coarse (sourceView s) := by
  classical
  constructor
  · intro agrees s
    simpa only [bind_dirac, coarsen_dirac] using agrees (dirac s)
  · intro rows prior
    exact coarsen_bind_of_rows sourceView targetView fine coarse rows prior

omit [Fintype S] [Fintype C] [DecidableEq C] in
/-- Sequential kernel composition preserves compatible prediction rows. -/
theorem prediction_rows_comp {T U D E : Type*}
    [Fintype T] [Fintype U] [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E]
    (sourceView : S → C) (middleView : T → D) (targetView : U → E)
    (first : S → Prob T) (firstCoarse : C → Prob D)
    (second : T → Prob U) (secondCoarse : D → Prob E)
    (firstRows : ∀ s, coarsen (first s) middleView = firstCoarse (sourceView s))
    (secondRows : ∀ t, coarsen (second t) targetView = secondCoarse (middleView t)) (s : S) :
    coarsen (bind (first s) second) targetView =
      bind (firstCoarse (sourceView s)) secondCoarse := by
  rw [coarsen_bind_of_rows middleView targetView second secondCoarse secondRows, firstRows s]

/-- Changing observations twice composes the corresponding prediction squares. -/
theorem prediction_rows_coarsen_comp {D : Type*} [Fintype D] [DecidableEq D]
    (view : S → C) (next : C → D)
    (fine : S → Prob S) (middle : C → Prob C) (coarse : D → Prob D)
    (firstRows : ∀ s, coarsen (fine s) view = middle (view s))
    (secondRows : ∀ c, coarsen (middle c) next = coarse (next c)) (s : S) :
    coarsen (fine s) (next ∘ view) = coarse ((next ∘ view) s) := by
  rw [← coarsen_comp, firstRows s, secondRows (view s)]
  rfl

/-- Row compatibility preserves the observed law after every finite action sequence. -/
theorem coarsen_predict_of_rows (view : S → C)
    (fine : A → S → Prob S) (coarse : A → C → Prob C)
    (rows : ∀ a s, coarsen (fine a s) view = coarse a (view s))
    (actions : List A) (prior : Prob S) :
    coarsen (predict fine actions prior) view = predict coarse actions (coarsen prior view) := by
  induction actions generalizing prior with
  | nil => rfl
  | cons action actions ih =>
      rw [predict_cons, predict_cons, ih,
        coarsen_bind_of_rows view view (fine action) (coarse action) (rows action)]

/-- Agreement of supplied models identifies coarse rows on the observation's
image. It makes no assertion about unreachable coarse states. -/
theorem supplied_rows_unique_on_image (view : S → C) (fine : S → Prob S)
    (first second : C → Prob C)
    (firstRows : ∀ s, coarsen (fine s) view = first (view s))
    (secondRows : ∀ s, coarsen (fine s) view = second (view s)) (s : S) :
    first (view s) = second (view s) := (firstRows s).symm.trans (secondRows s)

/-! ## Constructing a quotient from representatives -/

/-- The controlled kernel cannot distinguish states inside an observation fibre. -/
def StrongLumpability (view : S → C) (kernel : A → S → Prob S) : Prop :=
  ∀ a s t, view s = view t → coarsen (kernel a s) view = coarsen (kernel a t) view

/-- Compatibility with a supplied coarse dynamics implies strong lumpability. -/
theorem lumpable_of_transition (view : S → C)
    (fine : A → S → Prob S) (coarse : A → C → Prob C)
    (rows : ∀ a s, coarsen (fine a s) view = coarse a (view s)) :
    StrongLumpability view fine := by
  intro a s t same
  rw [rows a s, rows a t, same]

/-- The aggregated stochastic kernel, computed from representatives of observation classes. -/
noncomputable def lumpedKernel (view : S → C) (kernel : A → S → Prob S)
    (representative : C → S) : A → C → Prob C :=
  fun a c => coarsen (kernel a (representative c)) view

/-- With a right inverse and lumpability, the aggregate of every source state is the quotient row. -/
theorem lumpedKernel_correct (view : S → C) (kernel : A → S → Prob S)
    (representative : C → S) (sectionLaw : Function.RightInverse representative view)
    (lumpable : StrongLumpability view kernel) (a : A) (s : S) :
    lumpedKernel view kernel representative a (view s) = coarsen (kernel a s) view :=
  lumpable a (representative (view s)) s (sectionLaw (view s))

theorem lumpedKernel_independent (view : S → C) (kernel : A → S → Prob S)
    (first second : C → S) (firstLaw : Function.RightInverse first view)
    (secondLaw : Function.RightInverse second view)
    (lumpable : StrongLumpability view kernel) :
    lumpedKernel view kernel first = lumpedKernel view kernel second := by
  funext a c
  exact lumpable a (first c) (second c) ((firstLaw c).trans (secondLaw c).symm)

/-- Predicting and then observing equals predicting with the genuinely aggregated kernel. -/
theorem coarsen_predict (view : S → C) (kernel : A → S → Prob S)
    (representative : C → S) (sectionLaw : Function.RightInverse representative view)
    (lumpable : StrongLumpability view kernel) (prior : Prob S) (a : A) :
    coarsen (Prob.bind prior (kernel a)) view =
      Prob.bind (coarsen prior view) (lumpedKernel view kernel representative a) := by
  exact coarsen_bind_of_rows view view (kernel a) (lumpedKernel view kernel representative a)
    (fun s => (lumpedKernel_correct view kernel representative sectionLaw lumpable a s).symm) prior

/-- Every reward of the observed state has the same expected next-state value. -/
theorem next_reward_preserved (view : S → C) (kernel : A → S → Prob S)
    (representative : C → S) (sectionLaw : Function.RightInverse representative view)
    (lumpable : StrongLumpability view kernel) (prior : Prob S) (a : A) (reward : C → ℝ) :
    (∑ s, (Prob.bind prior (kernel a)).1 s * reward (view s)) =
      ∑ c, (Prob.bind (coarsen prior view) (lumpedKernel view kernel representative a)).1 c * reward c := by
  rw [← coarsen_expectation, coarsen_predict view kernel representative sectionLaw lumpable]

/-- With representatives available, strong lumpability is exactly the
existence of a coarse dynamics preserving prediction for every prior. -/
theorem strongLumpability_iff_prediction (view : S → C) (kernel : A → S → Prob S)
    (representative : C → S) (sectionLaw : Function.RightInverse representative view) :
    StrongLumpability view kernel ↔ ∃ coarse : A → C → Prob C,
      ∀ a prior, coarsen (bind prior (kernel a)) view = bind (coarsen prior view) (coarse a) := by
  constructor
  · intro lumpable
    exact ⟨lumpedKernel view kernel representative,
      fun a prior => coarsen_predict view kernel representative sectionLaw lumpable prior a⟩
  · rintro ⟨coarse, square⟩
    exact lumpable_of_transition view kernel coarse
      (fun a => (coarsen_bind_iff_rows view view (kernel a) (coarse a)).mp (square a))

namespace Controls

/-- Exact thirds provide a stochastic fixture with both outcomes in support. -/
noncomputable def thirds : Prob Bool :=
  ⟨fun b => if b then 1 / 3 else 2 / 3,
    (by intro b; cases b <;> norm_num), by norm_num [Fintype.sum_bool]⟩

noncomputable def reversedThirds : Prob Bool :=
  ⟨fun b => if b then 2 / 3 else 1 / 3,
    (by intro b; cases b <;> norm_num), by norm_num [Fintype.sum_bool]⟩

theorem stochastic_prediction_flips_thirds :
    bind thirds (fun b => dirac (!b)) = reversedThirds := by
  apply Subtype.ext
  funext b
  cases b <;> norm_num [bind_apply, thirds, reversedThirds, dirac_apply, Fintype.sum_bool]

/-- Support equivalence forgets probability weights. -/
theorem same_support_different_probabilities :
    (∀ b, 0 < thirds.1 b ∧ 0 < reversedThirds.1 b) ∧ thirds ≠ reversedThirds := by
  constructor
  · intro b; cases b <;> norm_num [thirds, reversedThirds]
  · intro same
    have := congrArg (fun law : Prob Bool => law.1 true) same
    norm_num [thirds, reversedThirds] at this

/-- Reassociating a plan is lawful, whereas reversing its actions can change the law. -/
theorem action_order_matters :
    predict (fun action (_ : Bool) => dirac action) [false, true] thirds = dirac true ∧
      predict (fun action (_ : Bool) => dirac action) [true, false] thirds = dirac false ∧
      (dirac true : Prob Bool) ≠ dirac false := by
  refine ⟨by simp, by simp, ?_⟩
  intro same
  have := congrArg (fun law : Prob Bool => law.1 true) same
  simp [dirac_apply] at this

/-- Agreement for one prior does not certify agreement at every row. -/
theorem one_prior_is_insufficient :
    bind (dirac false) (dirac (S := Bool)) = bind (dirac false) (fun _ => dirac false) ∧
      ¬ (∀ prior : Prob Bool,
        coarsen (bind prior dirac) id = bind (coarsen prior id) (fun _ => dirac false)) := by
  constructor
  · simp
  · intro allPriors
    have same := allPriors (dirac true)
    have points : (dirac true : Prob Bool) = dirac false := by simpa using same
    have := congrArg (fun law : Prob Bool => law.1 true) points
    simp [dirac_apply] at this

/-- A non-surjective view admits exact prediction. Coarse rows outside its
image can still differ, so all-prior agreement does not imply global uniqueness. -/
theorem nonsurjective_view_exact_with_nonunique_extension :
    (¬ Function.Surjective (fun _ : Unit => false)) ∧
    (∀ prior : Prob Unit,
      coarsen (bind prior dirac) (fun _ => false) =
        bind (coarsen prior (fun _ => false)) (dirac (S := Bool))) ∧
    (∀ prior : Prob Unit,
      coarsen (bind prior dirac) (fun _ => false) =
        bind (coarsen prior (fun _ => false)) (fun _ => dirac false)) ∧
    (dirac (S := Bool)) ≠ (fun _ => dirac false) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro onto
    obtain ⟨_, impossible⟩ := onto true
    cases impossible
  · intro prior
    simp
  · apply coarsen_bind_of_rows (fun _ : Unit => false) (fun _ : Unit => false)
      dirac (fun _ => dirac false)
    intro s
    exact coarsen_dirac s (fun _ => false)
  · intro same
    have points := congrFun same true
    have := congrArg (fun law : Prob Bool => law.1 true) points
    simp [dirac_apply] at this

end Controls

end Mettapedia.ProbabilityTheory.FiniteLumpability
