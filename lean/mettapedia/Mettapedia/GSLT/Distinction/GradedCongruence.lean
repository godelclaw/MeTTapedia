import Mettapedia.GSLT.Distinction.BehaviouralMetric
import Mettapedia.GSLT.Logic.SaturatedRelativeBisimilarity
import Mettapedia.Cybernetics.DistinctionCalculus.GradedCongruence
import Mettapedia.GSLT.Core.StepFree
import Mettapedia.GSLT.Logic.ProbeDial

/-!
# Graded congruences over a GSLT are behavioural distances

The distinction calculus calls a metric tolerance a **graded congruence** when
every context is nonexpansive for it
(`Cybernetics.DistinctionCalculus.Tolerance.GradedCongruence`).  Over a GSLT
the contexts plug terms and the steps rewrite them; this module connects the
two.

* **Context-stable systems** (`ContextStable`).  A graded system is stable
  under a map of terms when reading an observation after the map is itself an
  observation and stepping after the map is itself a labelled step.  Formulas
  then translate along the map (`ContextStable.eval_translate`), so the map is
  nonexpansive for the logical distance (`ContextStable.logicalDistance_le`).
* **The saturated graded system of an admissible class** (`saturatedGraded`):
  its labels are the admissible contexts, a step under a label is a reduction
  of the filled context, and the base graded observations are read through
  every admissible context.  It is stable under every admissible context
  (`saturatedGraded_contextStable`), so its logical distance is a **graded
  congruence**: a pseudometric (`saturatedGraded_toTolerance_metric`) under
  which every admissible context is nonexpansive
  (`saturatedGraded_logicalDistance_plug_le`).  Under finite branching the
  same holds of the behavioural distance.
* **Crisp observations** (`saturatedCrisp_logicalDistance_eq_zero_iff`): for
  the indicator readings of a crisp observation set, the zero kernel of the
  saturated distance is the `A`-relative equivalence `A.RelEquiv`, under finite
  branching and a positive discount; the saturated crisp system is also stable
  under every admissible context (`saturatedCrisp_logicalDistance_plug_le`).
* **The order of observer classes** (`Refinement`): a larger admissible class
  gives a larger logical distance (`saturatedGraded_logicalDistance_mono`), the
  graded form of `AdmissibleClass.relEquiv_antitone`.
* **The deterministic case is the distinction calculus's observational end**
  (`contextGraded_behaviouralDistance`).  For a monoid of contexts acting on a
  finite fragment, read as deterministic labelled steps, with declared
  consumers as observations and no discount, the behavioural distance is the
  all-continuation discrepancy `continuationDistance` of
  `Cybernetics.DistinctionCalculus.GradedCongruence`, so the greatest graded
  congruence protecting the consumers is `1 −` a behavioural distance, and by
  the quantitative Hennessy–Milner theorem it is also the logical distance
  (`contextGraded_logicalDistance`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence

universe uS uAtom uLabel uObs uContext uRule

namespace GradedSystem

variable {S : GSLT.{uS}} (Q : GradedSystem.{uS, uAtom, uLabel, uObs} S)

/-! ## Context-stable systems -/

/-- A graded system is **stable under a map of terms** when an observation
read after the map is an observation, and a labelled step taken after the map
is, up to the equations, a labelled step. -/
structure ContextStable (plug : S.Term → S.Term) where
  /-- The observation read after the map. -/
  atom : Q.observations.Atom → Q.observations.Atom
  value_atom : ∀ observation term,
    Q.observations.value (atom observation) term = Q.observations.value observation (plug term)
  /-- The label stepped after the map. -/
  label : Q.dynamics.Label → Q.dynamics.Label
  act_label : ∀ step term target, Q.dynamics.act step (plug term) target →
    ∃ target', Q.dynamics.act (label step) term target' ∧ S.Equiv target target'
  label_act : ∀ step term target, Q.dynamics.act (label step) term target →
    ∃ target', Q.dynamics.act step (plug term) target' ∧ S.Equiv target target'

namespace ContextStable

variable {Q} {plug : S.Term → S.Term} (stable : Q.ContextStable plug)

/-- Translate a formula along the map: atoms and outermost labels are composed
with it; the formulas under a diamond are untouched. -/
def translate : Q.Formula → Q.Formula
  | .top => .top
  | .atom observation => .atom (stable.atom observation)
  | .neg inner => .neg (translate inner)
  | .conj left right => .conj (translate left) (translate right)
  | .shift threshold inner => .shift threshold (translate inner)
  | .dia step inner => .dia (stable.label step) inner

/-- The translated formula at a term is the formula after the map. -/
theorem eval_translate : ∀ (formula : Q.Formula) (term : S.Term),
    Q.eval (stable.translate formula) term = Q.eval formula (plug term)
  | .top, _ => rfl
  | .atom observation, term => stable.value_atom observation term
  | .neg inner, term => by
      simp only [translate, eval_neg, eval_translate inner term]
  | .conj left right, term => by
      simp only [translate, eval_conj, eval_translate left term, eval_translate right term]
  | .shift threshold inner, term => by
      simp only [translate, eval_shift, eval_translate inner term]
  | .dia step inner, term => by
      simp only [translate, eval_dia]
      congr 2
      ext value
      constructor
      · rintro ⟨target, targetStep, rfl⟩
        obtain ⟨target', step', equivalent⟩ := stable.label_act step term target targetStep
        exact ⟨target', step', (Q.eval_resp inner equivalent).symm⟩
      · rintro ⟨target, targetStep, rfl⟩
        obtain ⟨target', step', equivalent⟩ := stable.act_label step term target targetStep
        exact ⟨target', step', (Q.eval_resp inner equivalent).symm⟩

/-- **The map is nonexpansive for the logical distance.** -/
theorem logicalDistance_le (stable : Q.ContextStable plug) (left right : S.Term) :
    Q.logicalDistance (plug left) (plug right) ≤ Q.logicalDistance left right :=
  Q.logicalDistance_le_iff.mpr fun formula => by
    rw [← stable.eval_translate formula left, ← stable.eval_translate formula right]
    exact Q.abs_eval_sub_le_logicalDistance _ left right

/-- Under finite branching the map is nonexpansive for the behavioural
distance. -/
theorem behaviouralDistance_le (stable : Q.ContextStable plug)
    (finite : Q.dynamics.ImageFiniteModulo) (left right : S.Term) :
    Q.behaviouralDistance (plug left) (plug right) ≤ Q.behaviouralDistance left right := by
  rw [Q.behaviouralDistance_eq_logicalDistance finite, Q.behaviouralDistance_eq_logicalDistance finite]
  exact stable.logicalDistance_le left right

end ContextStable

/-! ## Refinement of observer families -/

/-- A **refinement** of one graded system by another on the same GSLT: every
observation and every labelled step of the first is one of the second, with
the same discount. -/
structure Refinement (R : GradedSystem.{uS, uAtom, uLabel, uObs} S) where
  discount_eq : Q.discount = R.discount
  atom : Q.observations.Atom → R.observations.Atom
  value_atom : ∀ observation term,
    R.observations.value (atom observation) term = Q.observations.value observation term
  label : Q.dynamics.Label → R.dynamics.Label
  act_iff : ∀ step term target,
    R.dynamics.act (label step) term target ↔ Q.dynamics.act step term target

namespace Refinement

variable {Q} {R : GradedSystem.{uS, uAtom, uLabel, uObs} S} (refinement : Q.Refinement R)

/-- Translate a formula into the finer system. -/
def translate : Q.Formula → R.Formula
  | .top => .top
  | .atom observation => .atom (refinement.atom observation)
  | .neg inner => .neg (translate inner)
  | .conj left right => .conj (translate left) (translate right)
  | .shift threshold inner => .shift threshold (translate inner)
  | .dia step inner => .dia (refinement.label step) (translate inner)

theorem eval_translate : ∀ (formula : Q.Formula) (term : S.Term),
    R.eval (refinement.translate formula) term = Q.eval formula term
  | .top, _ => rfl
  | .atom observation, term => refinement.value_atom observation term
  | .neg inner, term => by
      simp only [translate, eval_neg, eval_translate inner term]
  | .conj left right, term => by
      simp only [translate, eval_conj, eval_translate left term, eval_translate right term]
  | .shift threshold inner, term => by
      simp only [translate, eval_shift, eval_translate inner term]
  | .dia step inner, term => by
      simp only [translate, eval_dia, refinement.discount_eq]
      congr 2
      ext value
      constructor
      · rintro ⟨target, targetStep, rfl⟩
        exact ⟨target, (refinement.act_iff step term target).mp targetStep,
          (eval_translate inner target).symm⟩
      · rintro ⟨target, targetStep, rfl⟩
        exact ⟨target, (refinement.act_iff step term target).mpr targetStep,
          eval_translate inner target⟩

/-- **A finer observer family separates more.** -/
theorem logicalDistance_le (refinement : Q.Refinement R) (left right : S.Term) :
    Q.logicalDistance left right ≤ R.logicalDistance left right :=
  Q.logicalDistance_le_iff.mpr fun formula => by
    rw [← refinement.eval_translate formula left, ← refinement.eval_translate formula right]
    exact R.abs_eval_sub_le_logicalDistance _ left right

end Refinement

end GradedSystem

/-! ## The saturated graded system of an admissible class -/

section Saturated

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
  (A : AdmissibleClass rules)

/-- No crisp observations: the saturated dynamics without crisp atoms. -/
def noCrispObservations (S : GSLT.{uS}) : ContextualRules.Observations.{0} S where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim

/-- Base graded observations read through every admissible context. -/
def GradedObservations.throughClass (base : GradedObservations.{uS, uObs} S) :
    GradedObservations.{uS, max uObs uContext} S where
  Atom := base.Atom × {context : rules.Context // A.Admissible context}
  value observation term := base.value observation.1 (rules.plug observation.2.1 term)
  value_nonneg _ _ := base.value_nonneg _ _
  value_le_one _ _ := base.value_le_one _ _
  value_resp observation _ _ equivalent :=
    base.value_resp observation.1 (rules.plug_resp observation.2.1 equivalent)

/-- **The saturated graded system** of an admissible class. -/
noncomputable def saturatedGraded (base : GradedObservations.{uS, uObs} S) (discount : ℝ)
    (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1) :
    GradedSystem.{uS, uContext, uContext, max uObs uContext} S where
  dynamics := A.saturated (noCrispObservations S)
  observations := GradedObservations.throughClass A base
  discount := discount
  discount_nonneg := discount_nonneg
  discount_le_one := discount_le_one

variable {base : GradedObservations.{uS, uObs} S} {discount : ℝ}
  {discount_nonneg : 0 ≤ discount} {discount_le_one : discount ≤ 1}

/-- The saturated graded system is stable under every admissible context. -/
def saturatedGraded_contextStable {context : rules.Context} (admissible : A.Admissible context) :
    (saturatedGraded A base discount discount_nonneg discount_le_one).ContextStable
      (rules.plug context) where
  atom observation := (observation.1, ⟨rules.compose observation.2.1 context,
    A.compose_mem observation.2.2 admissible⟩)
  value_atom observation term :=
    base.value_resp observation.1 (rules.plug_compose observation.2.1 context term)
  label step := ⟨rules.compose step.1 context, A.compose_mem step.2 admissible⟩
  act_label _ _ _ targetStep :=
    AdmissibleClass.step_plug_to_compose (rules := rules) targetStep
  label_act _ _ _ targetStep :=
    AdmissibleClass.step_compose_to_plug (rules := rules) targetStep

/-- **Every admissible context is nonexpansive for the saturated logical
distance.** -/
theorem saturatedGraded_logicalDistance_plug_le {context : rules.Context}
    (admissible : A.Admissible context) (left right : S.Term) :
    (saturatedGraded A base discount discount_nonneg discount_le_one).logicalDistance
        (rules.plug context left) (rules.plug context right) ≤
      (saturatedGraded A base discount discount_nonneg discount_le_one).logicalDistance left right :=
  (saturatedGraded_contextStable A admissible).logicalDistance_le left right

open Mettapedia.Cybernetics.DistinctionCalculus in
/-- **The saturated observer is a graded congruence**: it satisfies the metric
law and every admissible context is nonexpansive for it. -/
theorem saturatedGraded_toTolerance_gradedCongruence :
    (saturatedGraded A base discount discount_nonneg discount_le_one).toTolerance.Metric ∧
      ∀ ⦃context : rules.Context⦄, A.Admissible context → ∀ left right,
        (saturatedGraded A base discount discount_nonneg discount_le_one).toTolerance.similarity
            left right ≤
          (saturatedGraded A base discount discount_nonneg discount_le_one).toTolerance.similarity
            (rules.plug context left) (rules.plug context right) := by
  refine ⟨GradedSystem.toTolerance_metric _, fun context admissible left right => ?_⟩
  change 1 - _ ≤ 1 - _
  linarith [saturatedGraded_logicalDistance_plug_le (base := base)
    (discount_nonneg := discount_nonneg) (discount_le_one := discount_le_one) A admissible left right]

/-- The zero kernel of the saturated distance is closed under the class. -/
theorem saturatedGraded_zero_closedUnder :
    A.ClosedUnder fun left right =>
      (saturatedGraded A base discount discount_nonneg discount_le_one).logicalDistance
        left right = 0 := by
  intro context left right admissible zero
  exact le_antisymm ((saturatedGraded_logicalDistance_plug_le (base := base)
    (discount_nonneg := discount_nonneg) (discount_le_one := discount_le_one) A admissible
      left right).trans_eq zero)
    (GradedSystem.logicalDistance_nonneg _ _ _)

/-- **A larger admissible class separates more**: the saturated logical
distance is monotone in the class. -/
def saturatedGraded_refinement {B : AdmissibleClass rules} (le : A ≤ B) :
    (saturatedGraded A base discount discount_nonneg discount_le_one).Refinement
      (saturatedGraded B base discount discount_nonneg discount_le_one) where
  discount_eq := rfl
  atom observation := (observation.1, ⟨observation.2.1, le _ observation.2.2⟩)
  value_atom _ _ := rfl
  label step := ⟨step.1, le _ step.2⟩
  act_iff _ _ _ := Iff.rfl

theorem saturatedGraded_logicalDistance_mono {B : AdmissibleClass rules} (le : A ≤ B)
    (left right : S.Term) :
    (saturatedGraded A base discount discount_nonneg discount_le_one).logicalDistance left right ≤
      (saturatedGraded B base discount discount_nonneg discount_le_one).logicalDistance left right :=
  (saturatedGraded_refinement A le).logicalDistance_le left right

/-! ### Crisp observations -/

variable (observations : ContextualRules.Observations.{uAtom} S)

/-- The saturated system of a crisp observation set, with indicator
readings. -/
noncomputable def saturatedCrisp (discount : ℝ) (discount_nonneg : 0 ≤ discount)
    (discount_le_one : discount ≤ 1) :
    GradedSystem.{uS, max uAtom uContext, uContext, max uAtom uContext} S :=
  GradedSystem.ofSystem (A.saturated observations) discount discount_nonneg discount_le_one

/-- The saturated crisp system is stable under every admissible context. -/
noncomputable def saturatedCrisp_contextStable {context : rules.Context}
    (admissible : A.Admissible context) :
    (saturatedCrisp A observations discount discount_nonneg discount_le_one).ContextStable
      (rules.plug context) where
  atom observation := (observation.1, ⟨rules.compose observation.2.1 context,
    A.compose_mem observation.2.2 admissible⟩)
  value_atom observation term := by
    classical
    change (if observations.observes observation.1
        (rules.plug (rules.compose observation.2.1 context) term) then (1 : ℝ) else 0) =
      (if observations.observes observation.1
        (rules.plug observation.2.1 (rules.plug context term)) then (1 : ℝ) else 0)
    rw [observations.observes_resp observation.1
      (rules.plug_compose observation.2.1 context term)]
  label step := ⟨rules.compose step.1 context, A.compose_mem step.2 admissible⟩
  act_label _ _ _ targetStep :=
    AdmissibleClass.step_plug_to_compose (rules := rules) targetStep
  label_act _ _ _ targetStep :=
    AdmissibleClass.step_compose_to_plug (rules := rules) targetStep

theorem saturatedCrisp_logicalDistance_plug_le {context : rules.Context}
    (admissible : A.Admissible context) (left right : S.Term) :
    (saturatedCrisp A observations discount discount_nonneg discount_le_one).logicalDistance
        (rules.plug context left) (rules.plug context right) ≤
      (saturatedCrisp A observations discount discount_nonneg discount_le_one).logicalDistance
        left right :=
  (saturatedCrisp_contextStable A observations admissible).logicalDistance_le left right

/-- **The zero kernel of the saturated crisp distance is the `A`-relative
equivalence**, under finite branching and a positive discount. -/
theorem saturatedCrisp_logicalDistance_eq_zero_iff
    (finite : (A.saturated observations).ImageFiniteModulo) (positive : 0 < discount)
    (left right : S.Term) :
    (saturatedCrisp A observations discount discount_nonneg discount_le_one).logicalDistance
        left right = 0 ↔ A.RelEquiv observations left right :=
  GradedSystem.logicalDistance_ofSystem_eq_zero_iff (A.saturated observations)
    discount_nonneg discount_le_one finite positive left right

end Saturated

/-! ## The deterministic case: the distinction calculus's observational end -/

section Deterministic

open Mettapedia.Cybernetics.DistinctionCalculus

universe u v w

variable {C : Type v} {V : Type u}

/-- The GSLT of a fragment with a monoid of contexts: terms are equal only when
identical, and a step applies one context. -/
abbrev contextGSLT (M : ContextMonoid C V) : GSLT.{u} where
  Term := V
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := ∃ context, target = M.act context source
  rewrites_resp_left := by
    intro _ _ target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ step equal
    exact equal ▸ step

/-- Each context is a deterministic labelled step. -/
abbrev contextSystem (M : ContextMonoid C V) : System.{0, v} (contextGSLT M) where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := C
  act context source target := target = M.act context source
  act_resp_left := by
    intro _ _ _ target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  act_resp_right := by
    intro _ _ _ _ step equal
    exact equal ▸ step

/-- Declared consumers as graded observations. -/
abbrev consumerObservations (M : ContextMonoid C V) {J : Type w} (F : ConsumerFamily J V) :
    GradedObservations.{u, w} (contextGSLT M) where
  Atom := J
  value consumer term := (F.value consumer term : ℝ)
  value_nonneg consumer term := by exact_mod_cast F.nonneg consumer term
  value_le_one consumer term := by exact_mod_cast F.le_one consumer term
  value_resp consumer _ _ equal := by rw [show _ = _ from equal]

/-- The undiscounted graded system of contexts and consumers. -/
noncomputable abbrev contextGraded (M : ContextMonoid C V) {J : Type w} (F : ConsumerFamily J V) :
    GradedSystem.{u, 0, v, w} (contextGSLT M) where
  dynamics := contextSystem M
  observations := consumerObservations M F
  discount := 1
  discount_nonneg := zero_le_one
  discount_le_one := le_rfl

variable [Fintype C] {J : Type w} [Fintype J] [Nonempty J] (M : ContextMonoid C V)
  (F : ConsumerFamily J V)

/-- Each context is nonexpansive for the all-continuation discrepancy. -/
theorem continuationDistance_act_le (context : C) (left right : V) :
    continuationDistance M F (M.act context left) (M.act context right) ≤
      continuationDistance M F left right := by
  rw [continuationDistance_le_iff]
  intro other
  have := distance_act_le_continuation M F (M.mul other context) left right
  rwa [M.act_mul, M.act_mul] at this

/-- The all-continuation discrepancy is a bisimulation metric of the context
system. -/
theorem isBisimMetric_continuationDistance :
    (contextGraded M F).IsBisimMetric fun left right =>
      (continuationDistance M F left right : ℝ) where
  nonneg left right := by
    exact_mod_cast (F.distance_nonneg left right).trans (distance_le_continuation M F left right)
  observes consumer left right := by
    change |(F.value consumer left : ℝ) - F.value consumer right| ≤ _
    have bound := (F.abs_le_distance consumer left right).trans
      (distance_le_continuation M F left right)
    exact_mod_cast bound
  forth context left right left' step := by
    right
    intro ε positive
    refine ⟨M.act context right, rfl, ?_⟩
    change left' = M.act context left at step
    subst step
    have bound := continuationDistance_act_le M F context left right
    have cast : (continuationDistance M F (M.act context left) (M.act context right) : ℝ) ≤
        continuationDistance M F left right := by exact_mod_cast bound
    change 1 * (continuationDistance M F (M.act context left) (M.act context right) : ℝ) ≤ _
    linarith
  back context left right right' step := by
    right
    intro ε positive
    refine ⟨M.act context left, rfl, ?_⟩
    change right' = M.act context right at step
    subst step
    have bound := continuationDistance_act_le M F context left right
    have cast : (continuationDistance M F (M.act context left) (M.act context right) : ℝ) ≤
        continuationDistance M F left right := by exact_mod_cast bound
    change 1 * (continuationDistance M F (M.act context left) (M.act context right) : ℝ) ≤ _
    linarith

/-- Every bisimulation metric of the context system dominates the
all-continuation discrepancy. -/
theorem continuationDistance_le_of_isBisimMetric {distance : V → V → ℝ}
    (bisim : (contextGraded M F).IsBisimMetric distance) (left right : V) :
    (continuationDistance M F left right : ℝ) ≤ distance left right := by
  obtain ⟨context, -, attained⟩ := Finset.exists_mem_eq_sup' M.univ_nonempty
    fun context => F.distance (M.act context left) (M.act context right)
  obtain ⟨consumer, -, attainedConsumer⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    fun consumer => |F.value consumer (M.act context left) - F.value consumer (M.act context right)|
  have value : continuationDistance M F left right =
      |F.value consumer (M.act context left) - F.value consumer (M.act context right)| := by
    rw [continuationDistance, attained]
    exact attainedConsumer
  have observed : (continuationDistance M F left right : ℝ) ≤
      distance (M.act context left) (M.act context right) := by
    rw [value]
    have := bisim.observes consumer (M.act context left) (M.act context right)
    push_cast
    exact this
  have bounded : (continuationDistance M F left right : ℝ) ≤ 1 := by
    exact_mod_cast (continuationDistance_le_iff M F).mpr fun _ => F.distance_le_one _ _
  rcases bisim.forth context left right (M.act context left) rfl with large | matched
  · exact bounded.trans large
  · refine observed.trans (le_of_forall_pos_le_add fun ε positive => ?_)
    obtain ⟨right', step, close⟩ := matched ε positive
    change right' = M.act context right at step
    subst step
    change 1 * distance (M.act context left) (M.act context right) ≤ _ at close
    linarith

/-- **The observational end of the distinction calculus is a behavioural
distance.** For a finite monoid of contexts and declared consumers, the
behavioural distance of the undiscounted context system is the
all-continuation discrepancy. -/
theorem contextGraded_behaviouralDistance (left right : V) :
    (contextGraded M F).behaviouralDistance left right =
      (continuationDistance M F left right : ℝ) :=
  le_antisymm ((contextGraded M F).behaviouralDistance_le (isBisimMetric_continuationDistance M F)
      left right)
    ((contextGraded M F).le_behaviouralDistance fun _ bisim =>
      continuationDistance_le_of_isBisimMetric M F bisim left right)

omit [Fintype C] in
/-- The context system has one successor per label. -/
theorem contextSystem_imageFinite : (contextSystem M).ImageFiniteModulo := by
  intro context source
  refine ⟨{M.act context source}, Set.finite_singleton _, ?_⟩
  intro target step
  exact ⟨M.act context source, rfl, step⟩

/-- By the quantitative Hennessy–Milner theorem the all-continuation
discrepancy is also the logical distance. -/
theorem contextGraded_logicalDistance (left right : V) :
    (contextGraded M F).logicalDistance left right =
      (continuationDistance M F left right : ℝ) := by
  rw [← (contextGraded M F).behaviouralDistance_eq_logicalDistance (contextSystem_imageFinite M)]
  exact contextGraded_behaviouralDistance M F left right

/-- The greatest graded congruence protecting the consumers, read in the
reals, is the behavioural observer of the context system. -/
theorem contextGraded_toTolerance_similarity (left right : V) :
    (contextGraded M F).toTolerance.similarity left right =
      ((continuationTolerance M F).similarity left right : ℝ) := by
  change 1 - (contextGraded M F).logicalDistance left right = _
  rw [contextGraded_logicalDistance]
  change _ = ((1 - continuationDistance M F left right : ℚ) : ℝ)
  push_cast
  rfl

end Deterministic

/-! ## The observational end as a relative equivalence

The same contexts can be read as admissible probes on the static fragment
instead of as steps.  The relative equivalence of the full class is then
agreement of every consumer after every context
(`relEquiv_probe_iff_forall_context`), for any monoid of contexts, finite or
not.  With finitely many contexts it is the zero kernel of the
all-continuation tolerance (`relEquiv_probe_iff_continuationTolerance`) and the
zero set of the logical distance of the context system
(`relEquiv_probe_iff_logicalDistance_eq_zero`): reading contexts as probes or
as steps gives one observational end.  Identifications stipulated one by one
generate only related pairs when each is observationally valid
(`congGen_le_relEquiv_probe`), with no finiteness assumption; this is the
soundness obligation discharged for each merge of states.

The controls exhibit a hidden coordinate.  Two states that the consumer cannot
tell apart under the identity are separated once a revealing context is
admissible, so a merge licensed by the smaller class is refuted by the larger
one, and a store that kept only the merged class cannot serve the refined
observer. -/

section Probes

open Mettapedia.Cybernetics.DistinctionCalculus

universe u v w

variable {C : Type v} {V : Type u}

/-- The contexts of a context monoid as admissible probes on the step-free
fragment. -/
def probeRules (M : ContextMonoid C V) : ContextualRules.{v, 0} (GSLT.stepFree V) where
  Context := C
  identity := M.unit
  compose := M.mul
  plug := M.act
  plug_identity := M.act_unit
  plug_compose := M.act_mul
  plug_resp context := by
    intro left right equal
    exact congrArg (M.act context) (show left = right from equal)
  Rule := Empty
  fires _ _ _ := False
  fires_resp_left := fun _ impossible => impossible.elim
  fires_resp_right := fun impossible _ => impossible.elim
  fires_step := fun impossible => impossible.elim

/-- An atom asserts that one consumer reads one value. -/
def probeObservations {J : Type w} (F : ConsumerFamily J V) :
    ContextualRules.Observations.{w} (GSLT.stepFree V) :=
  valueObservations (S := GSLT.stepFree V) F.value
    (fun _ _ _ equal => congrArg _ (show _ = _ from equal))

variable (M : ContextMonoid C V) {J : Type w} (F : ConsumerFamily J V)

/-- **Every consumer under every context.** -/
theorem relEquiv_probe_iff_forall_context {left right : V} :
    (⊤ : AdmissibleClass (probeRules M)).RelEquiv (probeObservations F) left right ↔
      ∀ c j, F.value j (M.act c left) = F.value j (M.act c right) :=
  ((⊤ : AdmissibleClass (probeRules M)).relEquiv_valueObservations_iff_of_stepFree _ _
    (GSLT.stepFree_not_step V)).trans
    ⟨fun agree c => agree c (AdmissibleClass.top_admissible _),
      fun agree c _ => agree c⟩

/-- **The graded end on finite fragments.** -/
theorem relEquiv_probe_iff_continuationTolerance [Fintype C] [Fintype J] [Nonempty J]
    {left right : V} :
    (⊤ : AdmissibleClass (probeRules M)).RelEquiv (probeObservations F) left right ↔
      (continuationTolerance M F).Indistinguishable left right :=
  (relEquiv_probe_iff_forall_context M F).trans
    (continuationTolerance_indistinguishable_iff M F).symm

/-- **Probes and steps give one observational end.**  The relative equivalence
of the probes is the zero set of the logical distance of the context system. -/
theorem relEquiv_probe_iff_logicalDistance_eq_zero [Fintype C] [Fintype J] [Nonempty J]
    {left right : V} :
    (⊤ : AdmissibleClass (probeRules M)).RelEquiv (probeObservations F) left right ↔
      (contextGraded M F).logicalDistance left right = 0 := by
  rw [relEquiv_probe_iff_continuationTolerance, contextGraded_logicalDistance M F left right]
  unfold Tolerance.Indistinguishable
  rw [continuationTolerance_distance]
  exact Rat.cast_eq_zero.symm

/-- **Soundness of stipulated merges.** -/
theorem congGen_le_relEquiv_probe (R : V → V → Prop)
    (valid : ∀ {x y : V}, R x y → ∀ c j, F.value j (M.act c x) = F.value j (M.act c y))
    {left right : V} (generated : CongGen M R left right) :
    (⊤ : AdmissibleClass (probeRules M)).RelEquiv (probeObservations F) left right := by
  let related : Setoid V :=
    ⟨(⊤ : AdmissibleClass (probeRules M)).RelEquiv (probeObservations F),
      AdmissibleClass.relEquiv_equivalence _ _⟩
  exact congGen_le (E := related)
    (fun stipulated => (relEquiv_probe_iff_forall_context M F).mpr (valid stipulated))
    (fun c _ _ pair =>
      AdmissibleClass.relEquiv_closedUnder _ _ (AdmissibleClass.top_admissible _) pair)
    generated

namespace HiddenCoordinate

/-- A visible coordinate and a hidden one. -/
abbrev State := Bool × Bool

/-- The single consumer reads the visible coordinate. -/
def visible : ConsumerFamily Unit State where
  value _ state := if state.1 then 1 else 0
  nonneg _ state := by split <;> norm_num
  le_one _ state := by split <;> norm_num

/-- Contexts that may swap the two coordinates. -/
def revealing : ContextMonoid Bool State where
  act swap state := if swap then (state.2, state.1) else state
  unit := false
  mul first second := first != second
  act_unit _ := rfl
  act_mul first second state := by cases first <;> cases second <;> rfl

/-- Only the identity context. -/
abbrev quiet : ContextMonoid Unit State := ContextMonoid.trivial State

/-- Under the identity alone the hidden coordinate is invisible. -/
theorem quiet_identifies :
    (⊤ : AdmissibleClass (probeRules quiet)).RelEquiv (probeObservations visible)
      (false, false) (false, true) :=
  (relEquiv_probe_iff_forall_context quiet visible).mpr fun _ _ => rfl

/-- A revealing context separates the same pair. -/
theorem revealing_separates :
    ¬ (⊤ : AdmissibleClass (probeRules revealing)).RelEquiv (probeObservations visible)
      (false, false) (false, true) := by
  rw [relEquiv_probe_iff_forall_context]
  intro agree
  have swapped := agree true ()
  norm_num [revealing, visible] at swapped

/-- The graded end gives the same verdict for the revealing contexts. -/
theorem revealing_separates_graded :
    ¬ (continuationTolerance revealing visible).Indistinguishable (false, false) (false, true) :=
  fun indistinguishable =>
    revealing_separates ((relEquiv_probe_iff_continuationTolerance revealing visible).mpr
      indistinguishable)

/-- Merging states that share the visible coordinate is sound when only the
identity acts. -/
theorem quiet_merge_sound {left right : State} (sameVisible : left.1 = right.1) :
    (⊤ : AdmissibleClass (probeRules quiet)).RelEquiv (probeObservations visible) left right :=
  congGen_le_relEquiv_probe quiet visible (fun first second => first.1 = second.1)
    (fun {x y} stipulated _ _ => by
      show (if x.1 then (1 : ℚ) else 0) = if y.1 then 1 else 0
      rw [stipulated])
    (CongGen.rel sameVisible)

/-- The same stipulation is not observationally valid once swapping is
admissible: the merge licensed by the identity alone is refuted. -/
theorem revealing_merge_invalid :
    ¬ ∀ {x y : State}, x.1 = y.1 →
        ∀ c j, visible.value j (revealing.act c x) = visible.value j (revealing.act c y) := by
  intro valid
  have swapped := valid (x := (false, false)) (y := (false, true)) rfl true ()
  norm_num [revealing, visible] at swapped

/-- With no probes adjoined, the only admissible context is the identity. -/
theorem generatedBy_empty_identity {context : (probeRules revealing).Context}
    (generated : AdmissibleClass.GeneratedBy (rules := probeRules revealing) ∅ context) :
    context = (probeRules revealing).identity := by
  induction generated with
  | identity => rfl
  | generator member => exact member.elim
  | compose _ _ outer inner => rw [outer, inner]; rfl

/-- The class with no probes identifies the pair. -/
theorem unprobed_identifies :
    (AdmissibleClass.generatedBy (rules := probeRules revealing) ∅).RelEquiv
      (probeObservations visible) (false, false) (false, true) := by
  rw [AdmissibleClass.relEquiv_iff_of_stepFree _ _ (GSLT.stepFree_not_step State)]
  intro context admissible atom
  have identity := generatedBy_empty_identity admissible
  subst identity
  exact Iff.rfl

/-- **Zooming in cannot be served by the merged state.**  Adjoining the
revealing probe separates the pair that the unprobed class merged. -/
theorem revealing_probe_separates :
    ¬ ((AdmissibleClass.generatedBy (rules := probeRules revealing) ∅).dial {true}).RelEquiv
      (probeObservations visible) (false, false) (false, true) := by
  apply AdmissibleClass.not_relEquiv_dial_of_not_preserved _ _ (Set.mem_singleton true)
  rw [AdmissibleClass.relEquiv_iff_of_stepFree _ _ (GSLT.stepFree_not_step State)]
  intro agree
  have opened : visible.value () (revealing.act false (revealing.act true (false, true))) = 0 :=
    (agree false AdmissibleClass.GeneratedBy.identity ((), 0)).mp rfl
  simp [revealing, visible] at opened

end HiddenCoordinate

end Probes

end Mettapedia.GSLT.Distinction
