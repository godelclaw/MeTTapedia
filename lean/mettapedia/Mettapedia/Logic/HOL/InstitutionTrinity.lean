import Mettapedia.Logic.HOL.ContextualTrinity
import Mettapedia.Logic.HOL.ConversionTiers
import Mettapedia.Logic.HOL.ProofSyntaxConstantSubstitution
import Mettapedia.Logic.HOL.HenkinInstitution
import Mettapedia.Computability.OpenComputationalTrinity

/-!
# Signature extension as a map of computational trinities

A morphism of typed constant signatures translates every constant without
changing its type. Along it, the HOL kernel's trinity over the smaller
signature maps into the trinity over the larger one, restricted to the smaller
signature's contexts and substitutions (`extensionMap`):

* contexts and substitutions move by translating the constants of the
  substituted terms (`extendContexts`, a functor of context categories);
* executions and retained proofs move by translating every constant they
  contain, and the moves commute with substitution (`Execution.mapConst_subst_heq`,
  `ProofSyntax.subst_mapConst_heq`);
* semantic sequents of the reduct model are semantic sequents of the larger
  model, unchanged: the reduct has the same carriers, the same admissible
  values and the same extensional equality.

The two squares commute: elaborating a translated execution is translating
its elaboration, and soundness in the larger model of a translated proof is
soundness of the proof in the reduct (`denote_reduct` of the institution).

Translating along an injective signature morphism keeps executions apart
(`extensionMap_program_injective`), and the extensional component is injective
for every morphism (`extensionMap_space_injective`). This is the precise sense
in which extending a module's signature is safe here: no operational or
semantic distinction of the smaller signature is lost. It is not a
conservativity theorem; whether a translated sentence provable over the larger
signature is provable over the smaller one is a separate question.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.InstitutionTrinity

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.OpenComputationalTrinity
open Mettapedia.Logic.HOL.ContextualTrinity
open Mettapedia.Logic.HOL.HenkinInstitution

universe u

variable {Base : Type u}

/-! ## Contexts -/

/-- Translate the constants of every substituted term. -/
def extendContexts {source target : Signature Base} (translation : source ⟶ target) :
    SubstContext Base source.Const ⥤ SubstContext Base target.Const where
  obj context := ⟨context.ctx⟩
  map θ := fun index => mapConst translation.map (θ index)
  map_id _ := rfl
  map_comp first second := by
    funext τ index
    exact mapConst_subst translation.map first (second index)

/-! ## Executions -/

namespace BetaStep

variable {source target : Signature Base}

/-- Translate the constants of a step. -/
def mapConst (translation : source ⟶ target) :
    {Γ : Ctx Base} → {τ : Ty Base} → {before after : Term source.Const Γ τ} →
      ContextualTrinity.BetaStep before after →
        ContextualTrinity.BetaStep (HOL.mapConst translation.map before)
          (HOL.mapConst translation.map after)
  | _, _, _, _, .beta body argument =>
      (congrArg (ContextualTrinity.BetaStep (Const := target.Const) _)
        (HOL.mapConst_instantiate translation.map argument body)).mpr
        (.beta (HOL.mapConst translation.map body) (HOL.mapConst translation.map argument))
  | _, _, _, _, .appFun argument step =>
      .appFun (HOL.mapConst translation.map argument) (mapConst translation step)
  | _, _, _, _, .appArg function step =>
      .appArg (HOL.mapConst translation.map function) (mapConst translation step)
  | _, _, _, _, .lam step => .lam (mapConst translation step)
  | _, _, _, _, .andLeft right step => .andLeft (HOL.mapConst translation.map right) (mapConst translation step)
  | _, _, _, _, .orLeft right step => .orLeft (HOL.mapConst translation.map right) (mapConst translation step)
  | _, _, _, _, .impLeft right step => .impLeft (HOL.mapConst translation.map right) (mapConst translation step)
  | _, _, _, _, .eqLeft right step => .eqLeft (HOL.mapConst translation.map right) (mapConst translation step)
  | _, _, _, _, .andRight left step => .andRight (HOL.mapConst translation.map left) (mapConst translation step)
  | _, _, _, _, .orRight left step => .orRight (HOL.mapConst translation.map left) (mapConst translation step)
  | _, _, _, _, .impRight left step => .impRight (HOL.mapConst translation.map left) (mapConst translation step)
  | _, _, _, _, .eqRight left step => .eqRight (HOL.mapConst translation.map left) (mapConst translation step)
  | _, _, _, _, .not step => .not (mapConst translation step)
  | _, _, _, _, .all step => .all (mapConst translation step)
  | _, _, _, _, .ex step => .ex (mapConst translation step)

theorem mapConst_heq_of_heq (translation : source ⟶ target) {Γ : Ctx Base} {τ : Ty Base}
    {before₁ before₂ after₁ after₂ : Term source.Const Γ τ}
    (befores : before₁ = before₂) (afters : after₁ = after₂)
    {first : ContextualTrinity.BetaStep before₁ after₁}
    {second : ContextualTrinity.BetaStep before₂ after₂}
    (same : HEq first second) : HEq (mapConst translation first) (mapConst translation second) := by
  subst befores afters
  cases same
  rfl

theorem lift_mapConst (translation : source ⟶ target) {Γ Γ' : Ctx Base} {σ : Ty Base}
    {θ : Subst source.Const Γ Γ'} {θ' : Subst target.Const Γ Γ'}
    (pointwise : ∀ {τ : Ty Base} (index : Var Γ τ), θ' index = HOL.mapConst translation.map (θ index)) :
    ∀ {τ : Ty Base} (index : Var (σ :: Γ) τ),
      Subst.lift (σ := σ) θ' index = HOL.mapConst translation.map (Subst.lift θ index) := by
  intro τ index
  cases index with
  | vz => rfl
  | vs index =>
      simp only [Subst.lift, pointwise index]
      exact (HOL.mapConst_rename translation.map _ _).symm

theorem term_mapConst (translation : source ⟶ target) {Γ Γ' : Ctx Base}
    {θ : Subst source.Const Γ Γ'} {θ' : Subst target.Const Γ Γ'}
    (pointwise : ∀ {τ : Ty Base} (index : Var Γ τ), θ' index = HOL.mapConst translation.map (θ index))
    {τ : Ty Base} (term : Term source.Const Γ τ) :
    HOL.subst θ' (HOL.mapConst translation.map term) =
      HOL.mapConst translation.map (HOL.subst θ term) := by
  rw [HOL.mapConst_subst]
  exact subst_ext (fun index => pointwise index) _

/-- Translation commutes with substitution, step by step. -/
theorem mapConst_subst_heq (translation : source ⟶ target) {Γ Γ' : Ctx Base}
    (θ : Subst source.Const Γ Γ') (θ' : Subst target.Const Γ Γ')
    (pointwise : ∀ {τ : Ty Base} (index : Var Γ τ), θ' index = HOL.mapConst translation.map (θ index))
    {τ : Ty Base} {before after : Term source.Const Γ τ}
    (step : ContextualTrinity.BetaStep before after) :
    HEq ((mapConst translation step).subst θ') (mapConst translation (step.subst θ)) := by
  induction step generalizing Γ' with
  | beta body argument =>
      simp only [mapConst, ContextualTrinity.BetaStep.subst]
      refine HEq.trans (ContextualTrinity.BetaStep.subst_heq_of_heq _ rfl
        (HOL.mapConst_instantiate translation.map argument body) (ProofSyntax.mpr_heq _ _)) ?_
      refine HEq.trans ?_ (mapConst_heq_of_heq translation rfl
        (ProofSyntax.subst_instantiate θ argument body) (ProofSyntax.mpr_heq _ _)).symm
      simp only [ContextualTrinity.BetaStep.subst, mapConst]
      refine (ProofSyntax.mpr_heq _ _).trans ?_
      refine HEq.trans ?_ (ProofSyntax.mpr_heq _ _).symm
      congr 1
      · exact term_mapConst translation (lift_mapConst translation pointwise) body
      · exact term_mapConst translation pointwise argument
  | appFun argument step ih =>
      simp only [mapConst, ContextualTrinity.BetaStep.subst]
      congr 1
      all_goals first
        | exact term_mapConst translation pointwise _
        | exact ih θ θ' pointwise
  | appArg function step ih =>
      simp only [mapConst, ContextualTrinity.BetaStep.subst]
      congr 1
      all_goals first
        | exact term_mapConst translation pointwise _
        | exact ih θ θ' pointwise
  | lam step ih =>
      simp only [mapConst, ContextualTrinity.BetaStep.subst]
      congr 1
      all_goals first
        | exact term_mapConst translation (lift_mapConst translation pointwise) _
        | exact ih _ _ (lift_mapConst translation pointwise)
  | all step ih =>
      simp only [mapConst, ContextualTrinity.BetaStep.subst]
      congr 1
      all_goals first
        | exact term_mapConst translation (lift_mapConst translation pointwise) _
        | exact ih _ _ (lift_mapConst translation pointwise)
  | ex step ih =>
      simp only [mapConst, ContextualTrinity.BetaStep.subst]
      congr 1
      all_goals first
        | exact term_mapConst translation (lift_mapConst translation pointwise) _
        | exact ih _ _ (lift_mapConst translation pointwise)
  | _ =>
      simp only [mapConst, ContextualTrinity.BetaStep.subst]
      congr 1
      all_goals first
        | exact term_mapConst translation pointwise _
        | solve_by_elim (maxDepth := 3)

end BetaStep

namespace Execution

variable {source target : Signature Base}

/-- Translate the constants of every step of an execution. -/
def mapConst (translation : source ⟶ target) {Γ : Ctx Base} {τ : Ty Base} :
    {before after : Term source.Const Γ τ} →
      ContextualTrinity.Execution before after →
        ContextualTrinity.Execution (HOL.mapConst translation.map before)
          (HOL.mapConst translation.map after)
  | _, _, .done term => .done _
  | _, _, .step first rest => .step (BetaStep.mapConst translation first) (mapConst translation rest)

theorem mapConst_subst_heq (translation : source ⟶ target) {Γ Γ' : Ctx Base}
    (θ : Subst source.Const Γ Γ') (θ' : Subst target.Const Γ Γ')
    (pointwise : ∀ {τ : Ty Base} (index : Var Γ τ), θ' index = HOL.mapConst translation.map (θ index))
    {τ : Ty Base} {before after : Term source.Const Γ τ}
    (execution : ContextualTrinity.Execution before after) :
    HEq ((mapConst translation execution).subst θ') (mapConst translation (execution.subst θ)) := by
  induction execution with
  | done term =>
      simp only [mapConst, ContextualTrinity.Execution.subst]
      congr 1
      all_goals exact BetaStep.term_mapConst translation pointwise term
  | step first rest ih =>
      simp only [mapConst, ContextualTrinity.Execution.subst]
      congr 1
      all_goals first
        | exact BetaStep.term_mapConst translation pointwise _
        | exact BetaStep.mapConst_subst_heq translation θ θ' pointwise first

end Execution

/-! ## Elaboration commutes with translation -/

section Elaboration

variable {source target : Signature Base}

theorem stepProof_heq_of_heq {Γ : Ctx Base} {Δ₁ Δ₂ : List (Formula target.Const Γ)}
    (hypotheses : Δ₁ = Δ₂) {τ : Ty Base} {before₁ before₂ after₁ after₂ : Term target.Const Γ τ}
    (befores : before₁ = before₂) (afters : after₁ = after₂)
    {first : ContextualTrinity.BetaStep before₁ after₁}
    {second : ContextualTrinity.BetaStep before₂ after₂}
    (same : HEq first second) : HEq (first.proof Δ₁) (second.proof Δ₂) := by
  subst hypotheses befores afters
  cases same
  rfl

theorem terms_mapConst_eq (translation : source ⟶ target) {Γ : Ctx Base} {τ : Ty Base}
    (terms : List (Term source.Const Γ τ)) :
    terms.map (HOL.substConst fun constant => .const (translation.map constant)) =
      terms.map (HOL.mapConst translation.map) :=
  List.map_congr_left (fun term _ => HOL.substConst_constant_images translation.map term)

section ConstantCongruence

variable {source target : Signature Base} (translation : source ⟶ target)

set_option backward.isDefEq.respectTransparency false in
theorem substConst_castConclusion_heq {Γ : Ctx Base} {Δ : List (Formula source.Const Γ)}
    {φ ψ : Formula source.Const Γ} (same : φ = ψ) (proof : ProofSyntax source.Const Δ φ) :
    HEq (ProofSyntax.substConst (fun constant => .const (translation.map constant)) (castConclusion same proof))
      (ProofSyntax.substConst (fun constant => .const (translation.map constant)) proof) := by
  subst same
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem substConst_holeCongr_heq {Γ : Ctx Base} {Δ : List (Formula source.Const Γ)} {σ τ : Ty Base}
    (body : Term source.Const (σ :: Γ) τ) {hole hole' : Term source.Const Γ σ}
    (proof : ProofSyntax source.Const Δ (.eq hole hole')) :
    HEq (ProofSyntax.substConst (fun constant => .const (translation.map constant)) (holeCongr body proof))
      (holeCongr (HOL.substConst (fun constant => .const (translation.map constant)) body)
        (ProofSyntax.substConst (fun constant => .const (translation.map constant)) proof :
          ProofSyntax target.Const (Δ.map (HOL.substConst (fun constant => .const (translation.map constant))))
            (.eq (HOL.substConst (fun constant => .const (translation.map constant)) hole) (HOL.substConst (fun constant => .const (translation.map constant)) hole')))) := by
  dsimp only [holeCongr, ProofSyntax.substConst]
  congr 1
  all_goals first
    | (rw [HOL.substConst_instantiate])
    | (congr 1
       all_goals first
        | (rw [HOL.substConst_instantiate])
        | exact ProofSyntax.castIndices_heq _ _ _)

/-- One step of peeling a heterogeneous equality between a constant-substituted
composite proof and its expected form. -/
local macro "const_heq_step" : tactic => `(tactic| first
    | (with_reducible rfl)
    | assumption
    | (exact (ExtDerivation.substConst_weakenHyps _ _).symm)
    | (exact congrArg (List.cons _) (ExtDerivation.substConst_weakenHyps _ _).symm)
    | (exact fin_heq_of_val (by simp [weakenHyps]) _ _ rfl)
    | (refine (ProofSyntax.castIndices_heq _ _ _).trans ?_)
    | (refine (substConst_castConclusion_heq _ _ _).trans ?_)
    | (refine HEq.trans ?_ (castConclusion_heq _ _).symm)
    | (apply eq_of_heq; refine (ProofSyntax.castIndices_heq _ _ _).trans ?_)
    | (apply eq_of_heq; refine (substConst_castConclusion_heq _ _ _).trans ?_)
    | (apply eq_of_heq; refine HEq.trans ?_ (castConclusion_heq _ _).symm)
    | (show @HEq (ProofSyntax _ _ _) _ (ProofSyntax _ _ _) _; dsimp only [ProofSyntax.substConst])
    | (show @Eq (ProofSyntax _ _ _) _ _; dsimp only [ProofSyntax.substConst])
    | (show @HEq (ProofSyntax _ _ _) _ (ProofSyntax _ _ _) _; congr 1)
    | (show @Eq (ProofSyntax _ _ _) _ _; congr 1)
    | (rw [HOL.substConst_rename])
    | (simp [HOL.substConst_rename, HOL.substConst, rename]; done))

set_option backward.isDefEq.respectTransparency false in
theorem substConst_allCongr_heq {Γ : Ctx Base} {Δ : List (Formula source.Const Γ)} {σ : Ty Base}
    {φ φ' : Formula source.Const (σ :: Γ)}
    (proof : ProofSyntax source.Const (weakenHyps (σ := σ) Δ) (.eq φ φ'))
    {proof' : ProofSyntax target.Const (weakenHyps (σ := σ) (Δ.map (HOL.substConst (fun constant => .const (translation.map constant)))))
      (.eq (HOL.substConst (fun constant => .const (translation.map constant)) φ) (HOL.substConst (fun constant => .const (translation.map constant)) φ'))}
    (same : HEq (ProofSyntax.substConst (fun constant => .const (translation.map constant)) proof) proof') :
    HEq (ProofSyntax.substConst (fun constant => .const (translation.map constant)) (allCongr proof)) (allCongr proof') := by
  dsimp only [allCongr, allImp, instantiateFresh, ProofSyntax.substConst]
  congr 1
  repeat' const_heq_step

set_option backward.isDefEq.respectTransparency false in
theorem substConst_exCongr_heq {Γ : Ctx Base} {Δ : List (Formula source.Const Γ)} {σ : Ty Base}
    {φ φ' : Formula source.Const (σ :: Γ)}
    (proof : ProofSyntax source.Const (weakenHyps (σ := σ) Δ) (.eq φ φ'))
    {proof' : ProofSyntax target.Const (weakenHyps (σ := σ) (Δ.map (HOL.substConst (fun constant => .const (translation.map constant)))))
      (.eq (HOL.substConst (fun constant => .const (translation.map constant)) φ) (HOL.substConst (fun constant => .const (translation.map constant)) φ'))}
    (same : HEq (ProofSyntax.substConst (fun constant => .const (translation.map constant)) proof) proof') :
    HEq (ProofSyntax.substConst (fun constant => .const (translation.map constant)) (exCongr proof)) (exCongr proof') := by
  dsimp only [exCongr, exImp, instantiateFresh, ProofSyntax.substConst]
  congr 1
  repeat' const_heq_step

end ConstantCongruence

set_option backward.isDefEq.respectTransparency false in
/-- Translating the elaborated proof of a step is elaborating the translated
step. -/
theorem stepProof_mapConst_heq (translation : source ⟶ target) {Γ : Ctx Base}
    (Δ : List (Formula source.Const Γ)) {τ : Ty Base} {before after : Term source.Const Γ τ}
    (step : ContextualTrinity.BetaStep before after) :
    HEq (ProofSyntax.substConst (fun constant => .const (translation.map constant)) (step.proof Δ))
      ((BetaStep.mapConst translation step).proof (Δ.map (HOL.mapConst translation.map))) := by
  induction step with
  | beta body argument =>
      dsimp only [ContextualTrinity.BetaStep.proof, ProofSyntax.substConst, BetaStep.mapConst]
      refine (ProofSyntax.castIndices_heq _ _ _).trans ?_
      refine HEq.trans ?_ (stepProof_heq_of_heq rfl rfl
        (HOL.mapConst_instantiate translation.map argument body)
        (ProofSyntax.mpr_heq _ _)).symm
      dsimp only [ContextualTrinity.BetaStep.proof]
      congr 1
      · exact terms_mapConst_eq translation Δ
      · exact HOL.substConst_constant_images translation.map argument
      · exact HOL.substConst_constant_images translation.map body
  | appFun argument step ih =>
      dsimp only [ContextualTrinity.BetaStep.proof, ProofSyntax.substConst, BetaStep.mapConst]
      congr 1
      · exact terms_mapConst_eq translation Δ
      · exact HOL.substConst_constant_images translation.map _
      · exact HOL.substConst_constant_images translation.map _
      · exact HOL.substConst_constant_images translation.map _
      · exact ih Δ
  | appArg function step ih =>
      dsimp only [ContextualTrinity.BetaStep.proof, ProofSyntax.substConst, BetaStep.mapConst]
      congr 1
      · exact terms_mapConst_eq translation Δ
      · exact HOL.substConst_constant_images translation.map _
      · exact HOL.substConst_constant_images translation.map _
      · exact HOL.substConst_constant_images translation.map _
      · exact ih Δ
  | lam step ih =>
      dsimp only [ContextualTrinity.BetaStep.proof, ProofSyntax.substConst, BetaStep.mapConst]
      congr 1
      · exact terms_mapConst_eq translation Δ
      · exact HOL.substConst_constant_images translation.map _
      · exact HOL.substConst_constant_images translation.map _
      · refine (ProofSyntax.castIndices_heq _ _ _).trans ?_
        refine (ih (weakenHyps Δ)).trans ?_
        exact ContextualTrinity.BetaStep.proof_heq_of_hypotheses
          (by simp [weakenHyps, List.map_map, Function.comp_def, HOL.mapConst_weaken]) _
  | andLeft right step ih =>
      dsimp only [ContextualTrinity.BetaStep.proof, BetaStep.mapConst, castEq]
      refine (substConst_castConclusion_heq translation _ _).trans ?_
      refine (substConst_holeCongr_heq translation _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact ContextualTrinity.BetaStep.holeCongr_heq (terms_mapConst_eq translation Δ)
        (by simp [HOL.substConst, HOL.substConst_constant_images])
        (HOL.substConst_constant_images translation.map _)
        (HOL.substConst_constant_images translation.map _) (ih Δ)
  | orLeft right step ih =>
      dsimp only [ContextualTrinity.BetaStep.proof, BetaStep.mapConst, castEq]
      refine (substConst_castConclusion_heq translation _ _).trans ?_
      refine (substConst_holeCongr_heq translation _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact ContextualTrinity.BetaStep.holeCongr_heq (terms_mapConst_eq translation Δ)
        (by simp [HOL.substConst, HOL.substConst_constant_images])
        (HOL.substConst_constant_images translation.map _)
        (HOL.substConst_constant_images translation.map _) (ih Δ)
  | impLeft right step ih =>
      dsimp only [ContextualTrinity.BetaStep.proof, BetaStep.mapConst, castEq]
      refine (substConst_castConclusion_heq translation _ _).trans ?_
      refine (substConst_holeCongr_heq translation _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact ContextualTrinity.BetaStep.holeCongr_heq (terms_mapConst_eq translation Δ)
        (by simp [HOL.substConst, HOL.substConst_constant_images])
        (HOL.substConst_constant_images translation.map _)
        (HOL.substConst_constant_images translation.map _) (ih Δ)
  | eqLeft right step ih =>
      dsimp only [ContextualTrinity.BetaStep.proof, BetaStep.mapConst, castEq]
      refine (substConst_castConclusion_heq translation _ _).trans ?_
      refine (substConst_holeCongr_heq translation _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact ContextualTrinity.BetaStep.holeCongr_heq (terms_mapConst_eq translation Δ)
        (by simp [HOL.substConst, HOL.substConst_constant_images])
        (HOL.substConst_constant_images translation.map _)
        (HOL.substConst_constant_images translation.map _) (ih Δ)
  | andRight left step ih =>
      dsimp only [ContextualTrinity.BetaStep.proof, BetaStep.mapConst, castEq]
      refine (substConst_castConclusion_heq translation _ _).trans ?_
      refine (substConst_holeCongr_heq translation _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact ContextualTrinity.BetaStep.holeCongr_heq (terms_mapConst_eq translation Δ)
        (by simp [HOL.substConst, HOL.substConst_constant_images])
        (HOL.substConst_constant_images translation.map _)
        (HOL.substConst_constant_images translation.map _) (ih Δ)
  | orRight left step ih =>
      dsimp only [ContextualTrinity.BetaStep.proof, BetaStep.mapConst, castEq]
      refine (substConst_castConclusion_heq translation _ _).trans ?_
      refine (substConst_holeCongr_heq translation _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact ContextualTrinity.BetaStep.holeCongr_heq (terms_mapConst_eq translation Δ)
        (by simp [HOL.substConst, HOL.substConst_constant_images])
        (HOL.substConst_constant_images translation.map _)
        (HOL.substConst_constant_images translation.map _) (ih Δ)
  | impRight left step ih =>
      dsimp only [ContextualTrinity.BetaStep.proof, BetaStep.mapConst, castEq]
      refine (substConst_castConclusion_heq translation _ _).trans ?_
      refine (substConst_holeCongr_heq translation _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact ContextualTrinity.BetaStep.holeCongr_heq (terms_mapConst_eq translation Δ)
        (by simp [HOL.substConst, HOL.substConst_constant_images])
        (HOL.substConst_constant_images translation.map _)
        (HOL.substConst_constant_images translation.map _) (ih Δ)
  | eqRight left step ih =>
      dsimp only [ContextualTrinity.BetaStep.proof, BetaStep.mapConst, castEq]
      refine (substConst_castConclusion_heq translation _ _).trans ?_
      refine (substConst_holeCongr_heq translation _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact ContextualTrinity.BetaStep.holeCongr_heq (terms_mapConst_eq translation Δ)
        (by simp [HOL.substConst, HOL.substConst_constant_images])
        (HOL.substConst_constant_images translation.map _)
        (HOL.substConst_constant_images translation.map _) (ih Δ)
  | not step ih =>
      dsimp only [ContextualTrinity.BetaStep.proof, BetaStep.mapConst, castEq]
      refine (substConst_castConclusion_heq translation _ _).trans ?_
      refine (substConst_holeCongr_heq translation _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact ContextualTrinity.BetaStep.holeCongr_heq (terms_mapConst_eq translation Δ)
        (by simp [HOL.substConst])
        (HOL.substConst_constant_images translation.map _)
        (HOL.substConst_constant_images translation.map _) (ih Δ)
  | all step ih =>
      dsimp only [ContextualTrinity.BetaStep.proof, BetaStep.mapConst]
      refine (substConst_allCongr_heq translation _
        (proof' := ProofSyntax.castIndices
          (ExtDerivation.substConst_weakenHyps _ _).symm rfl
          (ProofSyntax.substConst _ (ContextualTrinity.BetaStep.proof (weakenHyps Δ) step)))
        (ProofSyntax.castIndices_heq _ _ _).symm).trans ?_
      exact allCongr_heq (terms_mapConst_eq translation Δ)
        (HOL.substConst_constant_images translation.map _)
        (HOL.substConst_constant_images translation.map _)
        ((ProofSyntax.castIndices_heq _ _ _).trans ((ih (weakenHyps Δ)).trans
          (ContextualTrinity.BetaStep.proof_heq_of_hypotheses
            (by simp [weakenHyps, List.map_map, Function.comp_def, HOL.mapConst_weaken]) _)))
  | ex step ih =>
      dsimp only [ContextualTrinity.BetaStep.proof, BetaStep.mapConst]
      refine (substConst_exCongr_heq translation _
        (proof' := ProofSyntax.castIndices
          (ExtDerivation.substConst_weakenHyps _ _).symm rfl
          (ProofSyntax.substConst _ (ContextualTrinity.BetaStep.proof (weakenHyps Δ) step)))
        (ProofSyntax.castIndices_heq _ _ _).symm).trans ?_
      exact exCongr_heq (terms_mapConst_eq translation Δ)
        (HOL.substConst_constant_images translation.map _)
        (HOL.substConst_constant_images translation.map _)
        ((ProofSyntax.castIndices_heq _ _ _).trans ((ih (weakenHyps Δ)).trans
          (ContextualTrinity.BetaStep.proof_heq_of_hypotheses
            (by simp [weakenHyps, List.map_map, Function.comp_def, HOL.mapConst_weaken]) _)))

set_option backward.isDefEq.respectTransparency false in
/-- Translating the elaborated proof of an execution is elaborating the
translated execution. -/
theorem executionProof_mapConst_heq (translation : source ⟶ target) {Γ : Ctx Base}
    (Δ : List (Formula source.Const Γ)) {τ : Ty Base} {before after : Term source.Const Γ τ}
    (execution : ContextualTrinity.Execution before after) :
    HEq (ProofSyntax.substConst (fun constant => .const (translation.map constant))
        (execution.proof Δ))
      ((Execution.mapConst translation execution).proof (Δ.map (HOL.mapConst translation.map))) := by
  induction execution with
  | done term =>
      dsimp only [ContextualTrinity.Execution.proof, ProofSyntax.substConst, Execution.mapConst]
      congr 1
      · exact terms_mapConst_eq translation Δ
      · exact HOL.substConst_constant_images translation.map term
  | step first rest ih =>
      dsimp only [ContextualTrinity.Execution.proof, ProofSyntax.substConst, Execution.mapConst]
      congr 1
      · exact terms_mapConst_eq translation Δ
      · exact HOL.substConst_constant_images translation.map _
      · exact HOL.substConst_constant_images translation.map _
      · exact HOL.substConst_constant_images translation.map _
      · exact stepProof_mapConst_heq translation Δ first

end Elaboration

/-! ## Positions survive translation -/

theorem BetaStep.position_mapConst {source target : Signature Base} (translation : source ⟶ target)
    {Γ : Ctx Base} {τ : Ty Base} {before after : Term source.Const Γ τ}
    (step : ContextualTrinity.BetaStep before after) :
    (BetaStep.mapConst translation step).position = step.position := by
  induction step with
  | beta body argument =>
      exact ContextualTrinity.BetaStep.position_of_heq rfl
        (HOL.mapConst_instantiate translation.map argument body) (ProofSyntax.mpr_heq _ _)
  | appFun argument step ih =>
      simp [BetaStep.mapConst, ContextualTrinity.BetaStep.position, ih]
  | appArg function step ih =>
      simp [BetaStep.mapConst, ContextualTrinity.BetaStep.position, ih]
  | _ => simp_all [BetaStep.mapConst, ContextualTrinity.BetaStep.position]

theorem Execution.positions_mapConst {source target : Signature Base} (translation : source ⟶ target)
    {Γ : Ctx Base} {τ : Ty Base} {before after : Term source.Const Γ τ}
    (execution : ContextualTrinity.Execution before after) :
    (Execution.mapConst translation execution).positions = execution.positions := by
  induction execution with
  | done => rfl
  | step first rest ih =>
      simp [Execution.mapConst, ContextualTrinity.Execution.positions, ih,
        BetaStep.position_mapConst]

/-- Translation along an injective constant map is injective on terms. -/
theorem mapConst_injective {Const Const' : Ty Base → Type u}
    {translate : ∀ {τ : Ty Base}, Const τ → Const' τ}
    (injective : ∀ (τ : Ty Base) (first second : Const τ), translate first = translate second →
      first = second) :
    ∀ {Γ : Ctx Base} {τ : Ty Base} {first second : Term Const Γ τ},
      HOL.mapConst translate first = HOL.mapConst translate second → first = second := by
  intro Γ τ first
  induction first with
  | var index =>
      intro second same
      cases second <;> simp_all [HOL.mapConst]
  | const constant =>
      intro second same
      cases second <;> simp_all [HOL.mapConst]
      exact injective _ _ _ same
  | app function argument functionIh argumentIh =>
      intro second same
      cases second with
      | app function' argument' =>
          simp only [HOL.mapConst, Term.app.injEq] at same
          obtain ⟨types, functions, arguments⟩ := same
          cases types
          rw [functionIh (eq_of_heq functions), argumentIh (eq_of_heq arguments)]
      | _ => simp [HOL.mapConst] at same
  | lam body ih =>
      intro second same
      cases second with
      | lam body' =>
          simp only [HOL.mapConst, Term.lam.injEq] at same
          rw [ih same]
      | _ => simp [HOL.mapConst] at same
  | top => intro second same; cases second <;> simp_all [HOL.mapConst]
  | bot => intro second same; cases second <;> simp_all [HOL.mapConst]
  | and left right leftIh rightIh =>
      intro second same
      cases second <;> simp only [HOL.mapConst, Term.and.injEq, reduceCtorEq] at same
      rw [leftIh same.1, rightIh same.2]
  | or left right leftIh rightIh =>
      intro second same
      cases second <;> simp only [HOL.mapConst, Term.or.injEq, reduceCtorEq] at same
      rw [leftIh same.1, rightIh same.2]
  | imp left right leftIh rightIh =>
      intro second same
      cases second <;> simp only [HOL.mapConst, Term.imp.injEq, reduceCtorEq] at same
      rw [leftIh same.1, rightIh same.2]
  | not body ih =>
      intro second same
      cases second <;> simp only [HOL.mapConst, Term.not.injEq, reduceCtorEq] at same
      rw [ih same]
  | eq left right leftIh rightIh =>
      intro second same
      cases second with
      | eq left' right' =>
          simp only [HOL.mapConst, Term.eq.injEq] at same
          obtain ⟨types, lefts, rights⟩ := same
          cases types
          rw [leftIh (eq_of_heq lefts), rightIh (eq_of_heq rights)]
      | _ => simp [HOL.mapConst] at same
  | all body ih =>
      intro second same
      cases second with
      | all body' =>
          simp only [HOL.mapConst, Term.all.injEq] at same
          obtain ⟨types, bodies⟩ := same
          cases types
          rw [ih (eq_of_heq bodies)]
      | _ => simp [HOL.mapConst] at same
  | ex body ih =>
      intro second same
      cases second with
      | ex body' =>
          simp only [HOL.mapConst, Term.ex.injEq] at same
          obtain ⟨types, bodies⟩ := same
          cases types
          rw [ih (eq_of_heq bodies)]
      | _ => simp [HOL.mapConst] at same

/-! ## The map of trinities -/

section Map

variable {source target : Signature Base}

/-- The reduct of a model whose functions respect extensional equality
respects it too: carriers, admissible values and extensional equality are
unchanged. -/
theorem reduct_respects (translation : source ⟶ target)
    {model : HOL.HenkinModel.{u, u, u} Base target.Const} (respects : model.FunctionsRespectEqv) :
    (HenkinInstitution.HenkinModel.reduct translation model).FunctionsRespectEqv := by
  intro σ τ function first second functionAdmissible firstAdmissible secondAdmissible same
  exact (PreModel.eqv_reduct translation model.toPreModel _ _).mpr
    (respects functionAdmissible firstAdmissible secondAdmissible
      ((PreModel.eqv_reduct translation model.toPreModel _ _).mp same))

/-- Translate an execution at a context. -/
def mapExecutionAt (translation : source ⟶ target) {Γ : Ctx Base}
    (execution : ExecutionAt (Const := source.Const) Γ) : ExecutionAt (Const := target.Const) Γ :=
  ⟨execution.1, HOL.mapConst translation.map execution.2.1,
    HOL.mapConst translation.map execution.2.2.1,
    Execution.mapConst translation execution.2.2.2⟩

/-- Translate a proved sequent. -/
def mapProvedSequent (translation : source ⟶ target) {Γ : Ctx Base}
    (proved : ProvedSequent (Const := source.Const) Γ) : ProvedSequent (Const := target.Const) Γ :=
  ⟨(proved.1.1.map (HOL.mapConst translation.map), HOL.mapConst translation.map proved.1.2),
    ProofSyntax.mapConst translation.map proved.2⟩

variable (translation : source ⟶ target) (model : HOL.HenkinModel.{u, u, u} Base target.Const)
  (respects : model.FunctionsRespectEqv)

/-- The comparison over the smaller signature, with the reduct as its
extensional face. -/
abbrev sourceComparison :=
  ContextualTrinity.comparison (HenkinInstitution.HenkinModel.reduct translation model)
    (reduct_respects translation respects)

/-- The comparison over the larger signature, restricted to the smaller
signature's contexts. -/
abbrev targetComparison :=
  (ContextualTrinity.comparison model respects).reindex (extendContexts translation)

theorem pull_reduct {Γ Γ' : Ctx Base} (θ : Subst source.Const Γ Γ')
    (valuation : AdmissibleValuation model Γ') :
    (AdmissibleValuation.pull (HenkinInstitution.HenkinModel.reduct translation model) θ
        valuation : AdmissibleValuation model Γ) =
      AdmissibleValuation.pull model (fun index => HOL.mapConst translation.map (θ index))
        valuation := by
  apply Subtype.ext
  funext τ index
  exact PreModel.denote_reduct translation model.toPreModel (θ index) valuation.1

theorem satisfiesHyps_reduct {Γ : Ctx Base} (valuation : HOL.HenkinModel.Valuation model Γ)
    (hypotheses : List (Formula source.Const Γ)) :
    Soundness.SatisfiesHyps (HenkinInstitution.HenkinModel.reduct translation model) valuation
        hypotheses ↔
      Soundness.SatisfiesHyps model valuation (hypotheses.map (HOL.mapConst translation.map)) := by
  simp only [Soundness.SatisfiesHyps, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  apply forall_congr'
  intro formula
  apply imp_congr_right
  intro _
  exact Iff.of_eq (congrArg ULift.down
    (PreModel.denote_reduct translation model.toPreModel formula valuation))

theorem map_mapConst_subst {Γ Γ' : Ctx Base} (θ : Subst source.Const Γ Γ')
    (hypotheses : List (Formula source.Const Γ)) :
    (hypotheses.map (HOL.subst θ)).map (HOL.mapConst translation.map) =
      (hypotheses.map (HOL.mapConst translation.map)).map
        (HOL.subst fun index => HOL.mapConst translation.map (θ index)) := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left (fun formula _ => HOL.mapConst_subst translation.map θ formula)

/-- **Signature extension maps the trinity.** Executions and proofs are
translated, semantic sequents of the reduct are semantic sequents of the
model, and both squares commute. -/
def extensionMap :
    ComparisonMap (sourceComparison translation model respects)
      (targetComparison translation model respects) where
  program :=
    { app := fun _ => TypeCat.ofHom fun execution => ⟨mapExecutionAt translation execution.down⟩
      naturality := by
        intro first second θ
        apply ConcreteCategory.hom_ext
        rintro ⟨⟨τ, before, after, run⟩⟩
        apply congrArg ULift.up
        exact ExecutionAt.ext (HOL.mapConst_subst translation.map _ before)
          (HOL.mapConst_subst translation.map _ after)
          (Execution.mapConst_subst_heq translation θ.unop _ (fun _ => rfl) run).symm }
  logic :=
    { app := fun _ => TypeCat.ofHom fun proved => ⟨mapProvedSequent translation proved.down⟩
      naturality := by
        intro first second θ
        apply ConcreteCategory.hom_ext
        rintro ⟨⟨⟨hypotheses, conclusion⟩, proof⟩⟩
        apply congrArg ULift.up
        refine ProvedSequent.ext ?_ (HOL.mapConst_subst translation.map _ conclusion)
          (ProofSyntax.subst_mapConst_heq translation.map proof θ.unop).symm
        exact map_mapConst_subst translation θ.unop hypotheses }
  space :=
    { app := fun _ => TypeCat.ofHom fun sequent =>
        ⟨{ hypotheses := sequent.down.hypotheses
           conclusion := sequent.down.conclusion
           entails := sequent.down.entails }⟩
      naturality := by
        intro first second θ
        apply ConcreteCategory.hom_ext
        rintro ⟨sequent⟩
        apply congrArg ULift.up
        ext valuation
        · exact Iff.of_eq (congrArg sequent.hypotheses (pull_reduct translation model θ.unop valuation))
        · exact Iff.of_eq (congrArg sequent.conclusion (pull_reduct translation model θ.unop valuation)) }
  programLogic := by
    ext context ⟨⟨τ, before, after, run⟩⟩
    apply congrArg ULift.up
    exact ProvedSequent.ext rfl rfl
      ((ProofSyntax.castIndices_heq _ _ _).trans (executionProof_mapConst_heq translation [] run))
  logicSpace := by
    ext context ⟨⟨⟨hypotheses, conclusion⟩, proof⟩⟩
    apply congrArg ULift.up
    ext valuation
    · exact satisfiesHyps_reduct translation model valuation.1 hypotheses
    · exact Iff.of_eq (congrArg ULift.down
        (PreModel.denote_reduct translation model.toPreModel conclusion valuation.1))

/-- The extensional component loses nothing. -/
theorem extensionMap_space_injective (context : (SubstContext Base source.Const)ᵒᵖ) :
    Function.Injective ((extensionMap translation model respects).space.app context) := by
  rintro ⟨first⟩ ⟨second⟩ same
  apply congrArg ULift.up
  exact SemanticSequent.ext (congrArg (fun sequent => sequent.down.hypotheses) same)
    (congrArg (fun sequent => sequent.down.conclusion) same)

/-- Along an injective signature morphism the operational component loses
nothing: translated executions are distinct when the executions are. -/
theorem extensionMap_program_injective
    (injective : ∀ (τ : Ty Base) (first second : source.Const τ),
      translation.map first = translation.map second → first = second)
    (context : (SubstContext Base source.Const)ᵒᵖ) :
    Function.Injective ((extensionMap translation model respects).program.app context) := by
  rintro ⟨⟨τ₁, before₁, after₁, first⟩⟩ ⟨⟨τ₂, before₂, after₂, second⟩⟩ same
  have translated : mapExecutionAt translation ⟨τ₁, before₁, after₁, first⟩ =
      mapExecutionAt translation ⟨τ₂, before₂, after₂, second⟩ := congrArg ULift.down same
  have observed := congrArg (fun execution : ExecutionAt (Const := target.Const) context.unop.ctx =>
      ((⟨execution.1, execution.2.1⟩ : Σ τ : Ty Base, Term target.Const context.unop.ctx τ),
        execution.2.2.2.positions)) translated
  simp only [mapExecutionAt, Prod.mk.injEq] at observed
  obtain ⟨sources, positions⟩ := observed
  obtain ⟨types, befores⟩ := Sigma.mk.inj_iff.mp sources
  subst types
  have sameBefore := mapConst_injective injective (eq_of_heq befores)
  subst sameBefore
  rw [Execution.positions_mapConst, Execution.positions_mapConst] at positions
  obtain ⟨afters, runs⟩ := ContextualTrinity.Execution.eq_of_positions first second positions
  subst afters
  cases eq_of_heq runs
  rfl

end Map

/-! ## Controls -/

namespace Controls

abbrev ι : Ty Unit := .base ()

/-- Two constants of the base type. -/
inductive TwoConst : Ty Unit → Type where
  | left : TwoConst ι
  | right : TwoConst ι

/-- One constant of the base type. -/
inductive OneConst : Ty Unit → Type where
  | only : OneConst ι

def twoSignature : Signature Unit := ⟨TwoConst⟩
def oneSignature : Signature Unit := ⟨OneConst⟩

/-- Merge both constants into one: not injective. -/
def merge : twoSignature ⟶ oneSignature where
  map := fun {τ} constant => match τ, constant with
    | _, .left => .only
    | _, .right => .only

/-- The one-point model of the merged signature. -/
def onePoint : HOL.HenkinModel.{0, 0, 0} Unit oneSignature.Const :=
  HOL.HenkinModel.standard (fun _ => PUnit.{2})
    (fun {τ} constant => match τ, constant with
      | _, .only => PUnit.unit)

theorem onePoint_respects : onePoint.FunctionsRespectEqv :=
  HOL.HenkinModel.functionsRespectEqv_of_fullDomains _ (HOL.HenkinModel.fullDomains_standard _ _)

abbrev point : (SubstContext Unit twoSignature.Const)ᵒᵖ := Opposite.op ⟨[]⟩

/-- Merging constants identifies two distinct executions: injectivity of the
signature morphism is needed for the operational component. -/
theorem merge_not_program_injective :
    ¬ Function.Injective ((extensionMap merge onePoint onePoint_respects).program.app point) := by
  intro injective
  have same := injective (a₁ := ⟨⟨ι, .const .left, .const .left, .done _⟩⟩)
    (a₂ := ⟨⟨ι, .const .right, .const .right, .done _⟩⟩) rfl
  have constants := congrArg (fun execution =>
    (⟨execution.down.1, execution.down.2.1⟩ : Σ τ : Ty Unit, Term twoSignature.Const [] τ)) same
  obtain ⟨_, terms⟩ := Sigma.mk.inj_iff.mp constants
  cases eq_of_heq terms

/-- An injective signature morphism: the empty signature into the merged one. -/
def fromEmpty : (⟨fun _ => PEmpty⟩ : Signature Unit) ⟶ oneSignature where
  map := fun constant => PEmpty.elim constant

theorem fromEmpty_program_injective :
    ∀ context, Function.Injective
      ((extensionMap fromEmpty onePoint onePoint_respects).program.app context) :=
  extensionMap_program_injective fromEmpty onePoint onePoint_respects
    (fun _ first => PEmpty.elim first)

end Controls

#print axioms extensionMap
#print axioms extensionMap_program_injective
#print axioms extensionMap_space_injective
#print axioms ProofSyntax.subst_mapConst_heq
#print axioms Controls.merge_not_program_injective

end Mettapedia.Logic.HOL.InstitutionTrinity
