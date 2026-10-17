import Mettapedia.Logic.HOL.ProofSyntaxStructural
import Mettapedia.Logic.HOL.Syntax.ConstantSubstitutionComposition

/-!
# Closed definitions in retained HOL proofs

Constant interpretation traverses all 29 rules of the retained calculus. It
keeps ordered premises and the exact position of every hypothesis occurrence,
including duplicate formulas which become identical after expansion. It does
not obtain a new receipt from proposition-valued derivability.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ProofSyntax

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v} {Const' : Ty Base → Type w}
  {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}

/-- Interpret constants by closed typed terms while retaining the proof. -/
def substConst {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (images : ∀ {type}, Const type → ClosedTerm Const' type)
    (proof : ProofSyntax Const Δ φ) :
    ProofSyntax Const' (Δ.map (HOL.substConst images)) (HOL.substConst images φ) :=
  match proof with
  | .hyp occurrence => castIndices rfl (by simp)
      (ProofSyntax.hyp (Const := Const') (Δ := Δ.map (HOL.substConst images))
        (occurrence.cast (by simp)))
  | .topI => .topI
  | .botE proof => .botE (substConst images proof)
  | .andI left right => .andI (substConst images left) (substConst images right)
  | .andEL proof => .andEL (substConst images proof)
  | .andER proof => .andER (substConst images proof)
  | .orIL proof => .orIL (substConst images proof)
  | .orIR proof => .orIR (substConst images proof)
  | .orE cases left right =>
      .orE (substConst images cases) (substConst images left) (substConst images right)
  | .impI proof => .impI (substConst images proof)
  | .impE function argument => .impE (substConst images function) (substConst images argument)
  | .notI proof => .notI (substConst images proof)
  | .notE negative positive => .notE (substConst images negative) (substConst images positive)
  | .allI proof => .allI (castIndices
      (ExtDerivation.substConst_weakenHyps images _).symm rfl (substConst images proof))
  | .allE term proof => castIndices rfl (HOL.substConst_instantiate images term _).symm
      (ProofSyntax.allE (HOL.substConst images term) (substConst images proof))
  | .exI term proof => .exI (HOL.substConst images term)
      (castIndices rfl (HOL.substConst_instantiate images term _) (substConst images proof))
  | .exE existsProof body => .exE (substConst images existsProof)
      (castIndices (by simp [List.map, ExtDerivation.substConst_weakenHyps])
        (HOL.substConst_weaken images _) (substConst images body))
  | .eqRefl term => .eqRefl (HOL.substConst images term)
  | .eqSymm proof => .eqSymm (substConst images proof)
  | .eqTrans left right => .eqTrans (substConst images left) (substConst images right)
  | .eqPropI forward backward =>
      .eqPropI (substConst images forward) (substConst images backward)
  | .eqPropEL proof => .eqPropEL (substConst images proof)
  | .eqPropER proof => .eqPropER (substConst images proof)
  | .eqApp term proof => .eqApp (HOL.substConst images term) (substConst images proof)
  | .eqAppArg function proof =>
      .eqAppArg (HOL.substConst images function) (substConst images proof)
  | .eqLam proof => .eqLam (castIndices
      (ExtDerivation.substConst_weakenHyps images _).symm rfl (substConst images proof))
  | .funExt proof => .funExt (castIndices rfl
      (by simp [HOL.substConst, HOL.substConst_weaken]) (substConst images proof))
  | .beta term body => castIndices rfl
      (by simp [HOL.substConst, HOL.substConst_instantiate])
      (ProofSyntax.beta (Δ := Δ.map (HOL.substConst images))
        (HOL.substConst images term) (HOL.substConst images body))
  | .eta function => castIndices rfl
      (by simp [HOL.substConst, HOL.substConst_weaken])
      (ProofSyntax.eta (Δ := Δ.map (HOL.substConst images)) (HOL.substConst images function))

theorem substConst_erasure
    (images : ∀ {type}, Const type → ClosedTerm Const' type)
    (proof : ProofSyntax Const Δ φ) :
    ExtDerivation Const' (Δ.map (HOL.substConst images)) (HOL.substConst images φ) :=
  (substConst images proof).erase

/-- Embed a supplied proof into a larger constant signature. -/
def mapConst
    (constants : ∀ {type}, Const type → Const' type)
    (proof : ProofSyntax Const Δ φ) :
    ProofSyntax Const' (Δ.map (HOL.mapConst constants)) (HOL.mapConst constants φ) :=
  castIndices (by
    clear proof
    induction Δ with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons, HOL.substConst_constant_images, ih])
    (HOL.substConst_constant_images constants φ)
    (substConst (fun constant => .const (constants constant)) proof)

set_option backward.isDefEq.respectTransparency false in
/-- Rule and hypothesis position survive expansion, even if images coincide. -/
theorem substConst_rootObservation
    (images : ∀ {type}, Const type → ClosedTerm Const' type)
    (proof : ProofSyntax Const Δ φ) :
    (substConst images proof).rootObservation = proof.rootObservation := by
  cases proof <;> dsimp only [substConst] <;>
    first | (simp only [rootObservation_castIndices] <;> rfl) | rfl

set_option backward.isDefEq.respectTransparency false in
theorem substConst_nodeCount
    (images : ∀ {type}, Const type → ClosedTerm Const' type)
    (proof : ProofSyntax Const Δ φ) :
    (substConst images proof).nodeCount = proof.nodeCount := by
  have count_cast {Γ : Ctx Base} {Δ Δ' : List (Formula Const' Γ)}
      {φ ψ : Formula Const' Γ} (assumptions : Δ = Δ') (conclusion : φ = ψ)
      (proof : ProofSyntax Const' Δ φ) :
      (castIndices assumptions conclusion proof).observe.nodeCount = proof.observe.nodeCount :=
    nodeCount_castIndices assumptions conclusion proof
  induction proof with
  | hyp occurrence =>
      dsimp only [substConst]
      simp only [nodeCount_castIndices]
      rfl
  | topI | eqRefl _ => rfl
  | beta _ _ | eta _ =>
      dsimp only [substConst]
      simp only [nodeCount_castIndices]
      rfl
  | _ =>
      dsimp only [substConst]
      try simp only [nodeCount_castIndices]
      change 1 + _ = 1 + _
      simp_all [nodeCount, weakenHyps]

/-- Forget sequents while retaining the complete ordered rule tree and every
local hypothesis occurrence. This observation does not retain rule terms. -/
inductive RuleTree where
  | node (rule : RuleObservation) (children : List RuleTree)

def ruleTree {Judgment : Type v}
    (tree : Mettapedia.Logic.Derivation Judgment RuleObservation) :
    RuleTree :=
  match tree with
  | .node _ rule _ children => .node rule (List.ofFn (fun index => ruleTree (children index)))

@[simp] theorem ruleTree_castIndices
    {Δ' : List (Formula Const Γ)} {ψ : Formula Const Γ}
    (assumptions : Δ = Δ') (conclusion : φ = ψ) (proof : ProofSyntax Const Δ φ) :
    ruleTree (castIndices assumptions conclusion proof).observe = ruleTree proof.observe := by
  cases assumptions
  cases conclusion
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem substConst_ruleTree
    (images : ∀ {type}, Const type → ClosedTerm Const' type)
    (proof : ProofSyntax Const Δ φ) :
    ruleTree (substConst images proof).observe = ruleTree proof.observe := by
  induction proof <;> dsimp only [substConst]
  all_goals try simp only [ruleTree_castIndices]
  all_goals
    first
    | rfl
    | (change RuleTree.node _ _ = RuleTree.node _ _
       congr 1
       simp_all only [List.ofFn_succ, List.ofFn_zero,
         List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ,
         Fin.val_zero, Fin.val_succ, ruleTree_castIndices])


/-! ## Constant substitution and variable substitution commute -/

section Commutation

theorem castIndices_heq {Γ : Ctx Base} {Δ Δ' : List (Formula Const Γ)} {φ ψ : Formula Const Γ}
    (assumptions : Δ = Δ') (conclusion : φ = ψ) (proof : ProofSyntax Const Δ φ) :
    HEq (castIndices assumptions conclusion proof) proof := by
  subst assumptions conclusion
  rfl

theorem substConst_heq_of_heq (images : ∀ {type}, Const type → ClosedTerm Const' type)
    {Γ : Ctx Base} {Δ₁ Δ₂ : List (Formula Const Γ)} {φ₁ φ₂ : Formula Const Γ}
    (hypotheses : Δ₁ = Δ₂) (conclusion : φ₁ = φ₂)
    {first : ProofSyntax Const Δ₁ φ₁} {second : ProofSyntax Const Δ₂ φ₂}
    (same : HEq first second) : HEq (substConst images first) (substConst images second) := by
  subst hypotheses conclusion
  cases same
  rfl

theorem lift_of_constant (images : ∀ {type}, Const type → ClosedTerm Const' type)
    {Γ Γ' : Ctx Base} {σ : Ty Base} {θ : Subst Const Γ Γ'} {θ' : Subst Const' Γ Γ'}
    (pointwise : ∀ {τ : Ty Base} (index : Var Γ τ), θ' index = HOL.substConst images (θ index)) :
    ∀ {τ : Ty Base} (index : Var (σ :: Γ) τ),
      Subst.lift (σ := σ) θ' index = HOL.substConst images (Subst.lift θ index) := by
  intro τ index
  cases index with
  | vz => rfl
  | vs index =>
      change weaken (θ' index) = HOL.substConst images (weaken (θ index))
      rw [pointwise index, HOL.substConst_weaken]

theorem term_of_constant (images : ∀ {type}, Const type → ClosedTerm Const' type)
    {Γ Γ' : Ctx Base} {θ : Subst Const Γ Γ'} {θ' : Subst Const' Γ Γ'}
    (pointwise : ∀ {τ : Ty Base} (index : Var Γ τ), θ' index = HOL.substConst images (θ index))
    {τ : Ty Base} (term : Term Const Γ τ) :
    HOL.subst θ' (HOL.substConst images term) = HOL.substConst images (HOL.subst θ term) := by
  rw [← HOL.substConst_subst images θ term]
  exact subst_ext (fun index => pointwise index) _

theorem terms_of_constant (images : ∀ {type}, Const type → ClosedTerm Const' type)
    {Γ Γ' : Ctx Base} {θ : Subst Const Γ Γ'} {θ' : Subst Const' Γ Γ'}
    (pointwise : ∀ {τ : Ty Base} (index : Var Γ τ), θ' index = HOL.substConst images (θ index))
    {τ : Ty Base} (terms : List (Term Const Γ τ)) :
    (terms.map (HOL.substConst images)).map (HOL.subst θ') =
      (terms.map (HOL.subst θ)).map (HOL.substConst images) := by
  simp only [List.map_map]
  exact List.map_congr_left (fun term _ => term_of_constant images pointwise term)

local macro "strip_casts" : tactic => `(tactic| repeat (first
  | refine (ProofSyntax.mpr_heq _ _).trans ?_
  | refine (ProofSyntax.mp_heq _ _).trans ?_
  | refine (ProofSyntax.id_mp_heq _ _).trans ?_
  | refine (castIndices_heq _ _ _).trans ?_
  | refine HEq.trans ?_ (ProofSyntax.mpr_heq _ _).symm
  | refine HEq.trans ?_ (ProofSyntax.mp_heq _ _).symm
  | refine HEq.trans ?_ (ProofSyntax.id_mp_heq _ _).symm
  | refine HEq.trans ?_ (castIndices_heq _ _ _).symm))

local macro "strip_inner" : tactic => `(tactic| repeat (first
  | (refine (subst_heq_of_heq _ ?_ ?_ (castIndices_heq _ _ _)).trans ?_; rotate_left 2)
  | (refine (subst_heq_of_heq _ ?_ ?_ (ProofSyntax.id_mp_heq _ _)).trans ?_; rotate_left 2)
  | (refine HEq.trans ?_ (substConst_heq_of_heq _ ?_ ?_ (ProofSyntax.mpr_heq _ _)).symm;
      rotate_left 0)
  | (refine HEq.trans ?_ (substConst_heq_of_heq _ ?_ ?_ (ProofSyntax.mp_heq _ _)).symm;
      rotate_left 0)
  | (refine HEq.trans ?_ (substConst_heq_of_heq _ ?_ ?_ (ProofSyntax.id_mp_heq _ _)).symm;
      rotate_left 0)))

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option backward.isDefEq.respectTransparency false in
/-- **Constant substitution commutes with variable substitution on retained
proofs.** Substituting along `θ'` after interpreting constants is
interpreting constants after substituting along `θ`, when `θ'` is the
interpretation of `θ`. Every rule, hypothesis occurrence and term argument is
compared. -/
theorem subst_substConst_heq (images : ∀ {type}, Const type → ClosedTerm Const' type)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) {Γ' : Ctx Base} (θ : Subst Const Γ Γ') (θ' : Subst Const' Γ Γ')
    (pointwise : ∀ {τ : Ty Base} (index : Var Γ τ), θ' index = HOL.substConst images (θ index)) :
    HEq (subst θ' (substConst images proof)) (substConst images (subst θ proof)) := by
  induction proof generalizing Γ' with
  | _ =>
      dsimp only [substConst, subst]
      strip_inner
      all_goals try (simp [HOL.substConst_instantiate, HOL.substConst_weaken,
        ExtDerivation.substConst_weakenHyps, subst_instantiate, subst_weakenHyps, HOL.substConst,
        HOL.subst, Subst.lift]; done)
      all_goals try dsimp only [substConst, subst]
      all_goals strip_casts
      all_goals try congr 1
      all_goals try (first
        | exact term_of_constant images pointwise _
        | exact term_of_constant images (lift_of_constant images pointwise) _
        | exact terms_of_constant images pointwise _
        | exact terms_of_constant images (lift_of_constant images pointwise) _
        | solve_by_elim (maxDepth := 6) [lift_of_constant]
        | exact (Fin.heq_ext_iff (by simp)).2 (by simp)
        | (strip_casts
           strip_inner
           all_goals try (simp [HOL.substConst_instantiate, HOL.substConst_weaken,
             ExtDerivation.substConst_weakenHyps, subst_instantiate, subst_weakenHyps,
             HOL.substConst, HOL.subst, Subst.lift]; done)
           all_goals try strip_casts
           all_goals solve_by_elim (maxDepth := 6) [lift_of_constant]))
      all_goals done

/-- Embedding a proof into a larger signature commutes with substitution. -/
theorem subst_mapConst_heq (constants : ∀ {type}, Const type → Const' type)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) {Γ' : Ctx Base} (θ : Subst Const Γ Γ') :
    HEq (subst (fun index => HOL.mapConst constants (θ index)) (mapConst constants proof))
      (mapConst constants (subst θ proof)) := by
  have pointwise : ∀ {τ : Ty Base} (index : Var Γ τ),
      HOL.mapConst constants (θ index) =
        HOL.substConst (fun constant => .const (constants constant)) (θ index) :=
    fun index => (HOL.substConst_constant_images constants (θ index)).symm
  have expand : ∀ {Γ'' : Ctx Base} {Δ' : List (Formula Const Γ'')} {φ' : Formula Const Γ''}
      (inner : ProofSyntax Const Δ' φ'),
      HEq (mapConst constants inner) (substConst (fun constant => .const (constants constant)) inner) :=
    fun inner => castIndices_heq _ _ _
  refine HEq.trans ?_ (expand _).symm
  refine HEq.trans (subst_heq_of_heq _ ?_ ?_ (expand proof)) ?_
  · exact List.map_congr_left (fun formula _ =>
      (HOL.substConst_constant_images constants formula).symm)
  · exact (HOL.substConst_constant_images constants φ).symm
  · exact subst_substConst_heq _ proof θ _ pointwise

end Commutation

end Mettapedia.Logic.HOL.ProofSyntax
