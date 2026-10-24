import Mettapedia.Logic.HOL.EtaNormalization
import Mettapedia.Logic.HOL.CoreReduction

/-!
# Eta contraction and parallel beta reduction

The interaction laws use the existing typed eta relation and parallel beta
reduction. Renaming, substitution and reflexive-transitive paths retain their
original context indices. The parallel formulation follows the classical
eta-postponement argument; it does not identify normalization histories.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.EtaPostponement

open EtaConversion
open BetaNormalization (Par)

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {gamma delta : Ctx Base} {type domain result : Ty Base}

abbrev Star {gamma : Ctx Base} {type : Ty Base} :
    Term Const gamma type → Term Const gamma type → Prop :=
  Relation.ReflTransGen EtaStep

theorem star_subst (theta : Subst Const gamma delta) {source target : Term Const gamma type}
    (steps : Star source target) : Star (subst theta source) (subst theta target) :=
  steps.lift (subst theta) (fun _ _ step => EtaNormalization.subst_step theta step)

theorem star_rename (rho : Rename Base gamma delta) {source target : Term Const gamma type}
    (steps : Star source target) : Star (rename rho source) (rename rho target) :=
  steps.lift (rename rho) (fun _ _ step => EtaNormalization.rename_step rho step)

theorem star_two {first second output : Ty Base}
    (make : Term Const delta first → Term Const delta second → Term Const delta output)
    (moveFirst : ∀ {source target} right, EtaStep source target →
      EtaStep (make source right) (make target right))
    (moveSecond : ∀ {source target} left, EtaStep source target →
      EtaStep (make left source) (make left target))
    {left left' : Term Const delta first} {right right' : Term Const delta second}
    (leftSteps : Star left left') (rightSteps : Star right right') :
    Star (make left right) (make left' right') :=
  (leftSteps.lift (fun term => make term right) (fun _ _ step => moveFirst right step)).trans
    (rightSteps.lift (make left') (fun _ _ step => moveSecond left' step))

theorem subst_pointwise (term : Term Const gamma type)
    {theta other : Subst Const gamma delta}
    (pointwise : ∀ {type} (index : Var gamma type), Star (theta index) (other index)) :
    Star (subst theta term) (subst other term) := by
  have lifted {gamma delta : Ctx Base} {bound : Ty Base}
      {theta other : Subst Const gamma delta}
      (pointwise : ∀ {type} (index : Var gamma type), Star (theta index) (other index)) :
      ∀ {type} (index : Var (bound :: gamma) type),
        Star (Subst.lift theta index) (Subst.lift other index) := by
    intro type index
    cases index with
    | vz => exact .refl
    | vs index => exact star_rename Rename.weaken (pointwise index)
  induction term generalizing delta with
  | var index => exact pointwise index
  | const | top | bot => exact .refl
  | app first second ihf ihs =>
      exact star_two Term.app (fun _ step => .appFun _ step)
        (fun _ step => .appArg _ step) (ihf pointwise) (ihs pointwise)
  | and first second ihf ihs =>
      exact star_two Term.and (fun _ step => .andLeft _ step)
        (fun _ step => .andRight _ step) (ihf pointwise) (ihs pointwise)
  | or first second ihf ihs =>
      exact star_two Term.or (fun _ step => .orLeft _ step)
        (fun _ step => .orRight _ step) (ihf pointwise) (ihs pointwise)
  | imp first second ihf ihs =>
      exact star_two Term.imp (fun _ step => .impLeft _ step)
        (fun _ step => .impRight _ step) (ihf pointwise) (ihs pointwise)
  | eq first second ihf ihs =>
      exact star_two Term.eq (fun _ step => .eqLeft _ step)
        (fun _ step => .eqRight _ step) (ihf pointwise) (ihs pointwise)
  | not _ ih => exact (ih pointwise).lift Term.not (fun _ _ step => .not step)
  | lam _ ih => exact (ih (lifted pointwise)).lift Term.lam (fun _ _ step => .lam step)
  | all _ ih => exact (ih (lifted pointwise)).lift Term.all (fun _ _ step => .all step)
  | ex _ ih => exact (ih (lifted pointwise)).lift Term.ex (fun _ _ step => .ex step)

theorem instantiate_argument (body : Term Const (domain :: gamma) result)
    {first second : Term Const gamma domain} (steps : Star first second) :
    Star (instantiate first body) (instantiate second body) := by
  apply subst_pointwise body
  intro type index
  cases index with
  | vz => exact steps
  | vs => exact .refl

theorem eta_expansion_parallel {source target : Term Const gamma (domain ⇒ result)}
    (parallel : Par source target) :
    ∃ next, Par (.lam (.app (weaken (σ := domain) source) (.var .vz))) next ∧
      Star next target :=
  ⟨.lam (.app (weaken target) (.var .vz)),
    .lam (.app (parallel.rename Rename.weaken) (.var .vz)), .single (.eta target)⟩

private theorem no_beta_cycle (term : Term Const gamma type) :
    ¬ Relation.TransGen BetaNormalization.Reduces term term := by
  have accessible := BetaNormalization.stronglyNormalizing term
  induction accessible with
  | intro source _ ih =>
      intro cycle
      obtain ⟨next, step, back⟩ := Relation.TransGen.head'_iff.mp cycle
      exact ih next step (Relation.TransGen.tail' back step)

private theorem parallel_beta_ne
    {body body' : Term Const (domain :: gamma) result}
    {argument argument' : Term Const gamma domain}
    (bodies : Par body body') (arguments : Par argument argument') :
    (.app (.lam body) argument : Term Const gamma result) ≠ instantiate argument' body' := by
  intro same
  have before := BetaNormalization.star_two Term.app
    (fun right ⟨step⟩ => ⟨.appFun right step⟩)
    (fun left _ _ ⟨step⟩ => ⟨.appArg left step⟩)
    (BetaNormalization.star_map Term.lam (fun ⟨step⟩ => ⟨.lam step⟩) bodies.to_star)
    arguments.to_star
  have strict := Relation.TransGen.tail' before
    (⟨ContextualTrinity.BetaStep.beta body' argument'⟩ :
      BetaNormalization.Reduces (.app (.lam body') argument') (instantiate argument' body'))
  rw [← same] at strict
  exact no_beta_cycle _ strict

theorem eta_expansion_parallel_strict {source target : Term Const gamma (domain ⇒ result)}
    (parallel : Par source target) :
    ∃ next, Par (.lam (.app (weaken (σ := domain) source) (.var .vz))) next ∧
      Star next target ∧
        ((.lam (.app (weaken (σ := domain) source) (.var .vz)) : Term Const gamma (domain ⇒ result)) =
          next → source = target) := by
  refine ⟨.lam (.app (weaken target) (.var .vz)),
    .lam (.app (parallel.rename Rename.weaken) (.var .vz)), .single (.eta target), ?_⟩
  intro same
  have functions := eq_of_heq (Term.app.inj (Term.lam.inj same)).2.1
  exact rename_injective Rename.weaken
    (fun _ _ equal => Var.vs.inj equal) source target functions

/-- The commuting parallel step retains beta progress: if its source did not
change, neither did the original parallel step. -/
theorem eta_parallel_strict {source middle target : Term Const gamma type}
    (eta : EtaStep source middle) (parallel : Par middle target) :
    ∃ next, Par source next ∧ Star next target ∧ (source = next → middle = target) := by
  induction parallel with
  | var | const | top | bot => exact ⟨source, Par.refl source, .single eta, fun _ => rfl⟩
  | lam bodyParallel ih =>
      cases eta with
      | eta => exact eta_expansion_parallel_strict (.lam bodyParallel)
      | lam inner =>
          obtain ⟨next, first, last, preserves⟩ := ih inner
          exact ⟨.lam next, .lam first, last.lift Term.lam (fun _ _ step => .lam step),
            fun same => congrArg Term.lam (preserves (Term.lam.inj same))⟩
  | app functionParallel argumentParallel ihf iha =>
      cases eta with
      | eta => exact eta_expansion_parallel_strict (.app functionParallel argumentParallel)
      | appFun _ inner =>
          obtain ⟨next, first, last, preserves⟩ := ihf inner
          refine ⟨.app next _, .app first argumentParallel,
            last.lift (fun term => Term.app term _) (fun _ _ step => EtaStep.appFun _ step), ?_⟩
          intro same
          have parts := Term.app.inj same
          exact congrArg₂ Term.app (preserves (eq_of_heq parts.2.1)) (eq_of_heq parts.2.2)
      | appArg _ inner =>
          obtain ⟨next, first, last, preserves⟩ := iha inner
          refine ⟨.app _ next, .app functionParallel first,
            last.lift (fun term => Term.app _ term) (fun _ _ step => EtaStep.appArg _ step), ?_⟩
          intro same
          have parts := Term.app.inj same
          exact congrArg₂ Term.app (eq_of_heq parts.2.1) (preserves (eq_of_heq parts.2.2))
  | @beta gamma sigma tau body body' argument argument' bodyParallel argumentParallel ihb iha =>
      cases eta with
      | eta => exact eta_expansion_parallel_strict (.beta bodyParallel argumentParallel)
      | appFun _ inner =>
          cases inner with
          | eta =>
              have inner : Par (.app (weaken (.lam body)) (.var .vz)) body' := by
                simpa only [weaken, rename, ContextualTrinity.instantiate_vz_rename_lift_weaken] using
                  (Par.beta (bodyParallel.rename (Rename.lift (Rename.weaken (σ := sigma))))
                    (Par.var (.vz : Var (sigma :: gamma) sigma)))
              exact ⟨_, .beta inner argumentParallel, .refl,
                fun same => False.elim (parallel_beta_ne inner argumentParallel same)⟩
          | lam inner =>
              obtain ⟨next, first, last, _⟩ := ihb inner
              exact ⟨instantiate argument' next, .beta first argumentParallel,
                star_subst (Subst.single argument') last,
                fun same => False.elim (parallel_beta_ne first argumentParallel same)⟩
      | appArg _ inner =>
          obtain ⟨next, first, last, _⟩ := iha inner
          exact ⟨instantiate next body', .beta bodyParallel first,
            instantiate_argument body' last,
            fun same => False.elim (parallel_beta_ne bodyParallel first same)⟩
  | and leftParallel rightParallel ihl ihr =>
      cases eta with
      | andLeft _ inner =>
          obtain ⟨next, first, last, preserves⟩ := ihl inner
          refine ⟨.and next _, .and first rightParallel,
            last.lift (fun term => Term.and term _) (fun _ _ step => EtaStep.andLeft _ step), ?_⟩
          intro same
          have parts := Term.and.inj same
          exact congrArg₂ Term.and (preserves (parts.1)) (parts.2)
      | andRight _ inner =>
          obtain ⟨next, first, last, preserves⟩ := ihr inner
          refine ⟨.and _ next, .and leftParallel first,
            last.lift (fun term => Term.and _ term) (fun _ _ step => EtaStep.andRight _ step), ?_⟩
          intro same
          have parts := Term.and.inj same
          exact congrArg₂ Term.and (parts.1) (preserves (parts.2))
  | or leftParallel rightParallel ihl ihr =>
      cases eta with
      | orLeft _ inner =>
          obtain ⟨next, first, last, preserves⟩ := ihl inner
          refine ⟨.or next _, .or first rightParallel,
            last.lift (fun term => Term.or term _) (fun _ _ step => EtaStep.orLeft _ step), ?_⟩
          intro same
          have parts := Term.or.inj same
          exact congrArg₂ Term.or (preserves (parts.1)) (parts.2)
      | orRight _ inner =>
          obtain ⟨next, first, last, preserves⟩ := ihr inner
          refine ⟨.or _ next, .or leftParallel first,
            last.lift (fun term => Term.or _ term) (fun _ _ step => EtaStep.orRight _ step), ?_⟩
          intro same
          have parts := Term.or.inj same
          exact congrArg₂ Term.or (parts.1) (preserves (parts.2))
  | imp leftParallel rightParallel ihl ihr =>
      cases eta with
      | impLeft _ inner =>
          obtain ⟨next, first, last, preserves⟩ := ihl inner
          refine ⟨.imp next _, .imp first rightParallel,
            last.lift (fun term => Term.imp term _) (fun _ _ step => EtaStep.impLeft _ step), ?_⟩
          intro same
          have parts := Term.imp.inj same
          exact congrArg₂ Term.imp (preserves (parts.1)) (parts.2)
      | impRight _ inner =>
          obtain ⟨next, first, last, preserves⟩ := ihr inner
          refine ⟨.imp _ next, .imp leftParallel first,
            last.lift (fun term => Term.imp _ term) (fun _ _ step => EtaStep.impRight _ step), ?_⟩
          intro same
          have parts := Term.imp.inj same
          exact congrArg₂ Term.imp (parts.1) (preserves (parts.2))
  | eq leftParallel rightParallel ihl ihr =>
      cases eta with
      | eqLeft _ inner =>
          obtain ⟨next, first, last, preserves⟩ := ihl inner
          refine ⟨.eq next _, .eq first rightParallel,
            last.lift (fun term => Term.eq term _) (fun _ _ step => EtaStep.eqLeft _ step), ?_⟩
          intro same
          have parts := Term.eq.inj same
          exact congrArg₂ Term.eq (preserves (eq_of_heq parts.2.1)) (eq_of_heq parts.2.2)
      | eqRight _ inner =>
          obtain ⟨next, first, last, preserves⟩ := ihr inner
          refine ⟨.eq _ next, .eq leftParallel first,
            last.lift (fun term => Term.eq _ term) (fun _ _ step => EtaStep.eqRight _ step), ?_⟩
          intro same
          have parts := Term.eq.inj same
          exact congrArg₂ Term.eq (eq_of_heq parts.2.1) (preserves (eq_of_heq parts.2.2))
  | not bodyParallel ih =>
      cases eta with
      | not inner =>
          obtain ⟨next, first, last, preserves⟩ := ih inner
          exact ⟨.not next, .not first,
            last.lift Term.not (fun _ _ step => .not step),
            fun same => congrArg Term.not (preserves (Term.not.inj same))⟩
  | all bodyParallel ih =>
      cases eta with
      | all inner =>
          obtain ⟨next, first, last, preserves⟩ := ih inner
          exact ⟨.all next, .all first,
            last.lift Term.all (fun _ _ step => .all step),
            fun same => congrArg Term.all (preserves (eq_of_heq (Term.all.inj same).2))⟩
  | ex bodyParallel ih =>
      cases eta with
      | ex inner =>
          obtain ⟨next, first, last, preserves⟩ := ih inner
          exact ⟨.ex next, .ex first,
            last.lift Term.ex (fun _ _ step => .ex step),
            fun same => congrArg Term.ex (preserves (eq_of_heq (Term.ex.inj same).2))⟩

/-- A single eta contraction can be moved past parallel beta reduction,
retaining the typed intermediate term and an actual eta path. -/
theorem eta_parallel {source middle target : Term Const gamma type}
    (eta : EtaStep source middle) (parallel : Par middle target) :
    ∃ next, Par source next ∧ Star next target := by
  obtain ⟨next, first, last, _⟩ := eta_parallel_strict eta parallel
  exact ⟨next, first, last⟩

theorem star_parallel {source middle target : Term Const gamma type}
    (eta : Star source middle) (parallel : Par middle target) :
    ∃ next, Par source next ∧ Star next target := by
  induction eta generalizing target with
  | refl => exact ⟨target, parallel, .refl⟩
  | tail _ step ih =>
      obtain ⟨intermediate, moved, last⟩ := eta_parallel step parallel
      obtain ⟨next, first, rest⟩ := ih moved
      exact ⟨next, first, rest.trans last⟩

theorem star_beta_star {source middle target : Term Const gamma type}
    (eta : Star source middle) (beta : BetaNormalization.ReducesStar middle target) :
    ∃ next, BetaNormalization.ReducesStar source next ∧ Star next target := by
  induction beta with
  | refl => exact ⟨source, .refl, eta⟩
  | tail _ step ih =>
      obtain ⟨intermediate, first, rest⟩ := ih
      obtain ⟨one⟩ := step
      obtain ⟨next, moved, last⟩ := star_parallel rest (Par.of_step one)
      exact ⟨next, first.trans moved.to_star, last⟩

/-- Every finite beta/eta reduction can perform its beta steps first and its
eta contractions afterward, with the original endpoints and context intact. -/
theorem postponement {source target : Term Const gamma type}
    (steps : Relation.ReflTransGen BetaEtaStep source target) :
    ∃ middle, BetaNormalization.ReducesStar source middle ∧ Star middle target := by
  induction steps with
  | refl => exact ⟨source, .refl, .refl⟩
  | tail _ step ih =>
      obtain ⟨middle, first, last⟩ := ih
      rcases step with beta | eta
      · obtain ⟨one⟩ := beta
        obtain ⟨next, moved, rest⟩ := star_parallel last (Par.of_step one)
        exact ⟨next, first.trans moved.to_star, rest⟩
      · exact ⟨middle, first, .tail last eta⟩

/-- Moving one genuine beta step before eta preserves genuine beta progress. -/
theorem eta_beta_step {source middle target : Term Const gamma type}
    (eta : EtaStep source middle) (beta : BetaNormalization.Reduces middle target) :
    ∃ next, Relation.TransGen BetaNormalization.Reduces source next ∧ Star next target := by
  obtain ⟨one⟩ := beta
  obtain ⟨next, parallel, last, preserves⟩ := eta_parallel_strict eta (Par.of_step one)
  have different : middle ≠ target := by
    intro same
    subst target
    exact no_beta_cycle middle (.single ⟨one⟩)
  have sourceDifferent : source ≠ next := fun same => different (preserves same)
  rcases parallel.to_star.cases_head with same | ⟨first, step, rest⟩
  · exact False.elim (sourceDifferent same)
  · exact ⟨next, Relation.TransGen.head' step rest, last⟩

theorem eta_beta_trans {source middle target : Term Const gamma type}
    (eta : EtaStep source middle)
    (beta : Relation.TransGen BetaNormalization.Reduces middle target) :
    ∃ next, Relation.TransGen BetaNormalization.Reduces source next ∧ Star next target := by
  obtain ⟨first, step, rest⟩ := Relation.TransGen.head'_iff.mp beta
  obtain ⟨intermediate, moved, last⟩ := eta_beta_step eta step
  obtain ⟨next, after, ending⟩ := star_beta_star last rest
  exact ⟨next, moved.trans_left after, ending⟩

#print axioms eta_expansion_parallel
#print axioms eta_parallel
#print axioms postponement
#print axioms eta_parallel_strict
#print axioms eta_beta_trans

end Mettapedia.Logic.HOL.EtaPostponement
