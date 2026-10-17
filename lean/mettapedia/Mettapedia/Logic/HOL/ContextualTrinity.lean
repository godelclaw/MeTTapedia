import Mettapedia.Logic.HOL.ProofSyntaxStructural
import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Semantics.ModelProperties
import Mettapedia.Computability.FragmentwiseComputationalTrinity

/-!
# The computational trinity of the HOL kernel over substitution contexts

The three faces of the contextual computational trinity are instantiated on
the extensional HOL calculus, with contexts and simultaneous substitutions as
the base category.

* **Contexts.** Objects are HOL contexts; a morphism `Δ ⟶ Γ` is a simultaneous
  substitution of `Δ`-terms for the variables of `Γ` (`SubstContext`). The
  category laws are the term-level identity and composition laws of
  substitution.
* **Operational face.** Explicit beta executions: finite sequences of
  one-step beta contractions at any position, including under the logical
  connectives and quantifiers (`BetaStep`, `Execution`). A contraction under a
  connective or quantifier is elaborated through a one-hole context or through
  quantifier elimination and introduction (`holeCongr`, `allCongr`,
  `exCongr`). Substitution acts on every step, including the
  contracted redex, and is functorial on executions.
* **Intensional face.** Retained natural-deduction proofs (`ProofSyntax`),
  with their hypothesis occurrences and every rule argument. Substitution acts
  by the existing capture-safe proof substitution; its identity and
  composition laws are `ProofSyntax.subst_id_heq` and
  `ProofSyntax.subst_comp_heq`.
* **Extensional face.** For a Henkin model whose functions respect extensional
  equality: semantic sequents, pairs of predicates on admissible valuations
  with the first entailing the second. Substitution acts by precomposition
  with the valuation a substitution denotes.

The maps are elaboration of an execution into an explicit equational proof
(`Execution.proof`), soundness of retained proofs, and the direct denotational
reading of an execution (both endpoints denote extensionally equal values).
Their substitution-naturality squares are the substitution lemmas of the three
levels: execution steps commute with substitution up to the
`subst_instantiate` identity, proofs by the functoriality above, and
denotation by `Soundness.denote_subst`. The triangle commutes: soundness of
the elaborated proof is the direct reading of the execution.

This is a `Comparison`, not an `Exact` trinity, and the losses are located:

* elaboration is injective at every context (`elaborate_injective`): the
  explicit-conversion proof retains the entire execution, step order included;
* the extensional face forgets the execution: the outer-first and the
  inner-first executions of `(λy. y) ((λz. z) x)` are different programs with
  different proofs and one semantic sequent (`Controls.losesProgramInformation`);
* it forgets hypothesis occurrences: the proofs of `φ` from the first and from
  the second copy of `φ` in `[φ, φ]` are different and have one semantic
  sequent (`Controls.logicToSpace_identifies_occurrences`).

Hence no natural isomorphism from executions to semantic sequents agrees with
the direct reading (`Controls.no_exact_programSpace`), and no requirement on the
extensional face, pulled back to proofs, selects the proofs rooted at the first
hypothesis occurrence (`Controls.occurrence_not_extensional`): occurrence
identity stays on the presentation. The fragment of
hypothesis-free proofs is substitution-stable and is carried by both maps into
the unconditional semantic sequents (`closedFragment`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ContextualTrinity

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.FragmentwiseComputationalTrinity

universe u v w

/-! ## The category of contexts and substitutions -/

/-- A HOL context, as an object of the category of simultaneous
substitutions. -/
structure SubstContext (Base : Type u) (Const : Ty Base → Type v) where
  ctx : Ctx Base

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A morphism `Δ ⟶ Γ` substitutes a `Δ`-term for every variable of `Γ`.
Composition substitutes into the terms of the later substitution. -/
instance substContextCategory : Category.{max u v} (SubstContext Base Const) where
  Hom source target := Subst Const target.ctx source.ctx
  id _ := Subst.id
  comp first second := Subst.comp first second
  id_comp substitution := by
    funext τ index
    exact subst_id (substitution index)
  comp_id _ := rfl
  assoc first second third := by
    funext τ index
    exact (subst_comp first second (third index)).symm

/-! ## The operational face: explicit beta executions -/

/-- One beta contraction at any position of a term: the compatible closure of
the beta rule. The step records its redex position and the contracted redex.
Contraction under the logical connectives and quantifiers is included; without
it, `(λx. x ∧ ⊤) ((λy. y) ⊤)` would have the two distinct normal forms
`((λy. y) ⊤) ∧ ⊤` and `⊤ ∧ ⊤`. -/
inductive BetaStep : {Γ : Ctx Base} → {τ : Ty Base} →
    Term Const Γ τ → Term Const Γ τ → Type (max u v) where
  | beta {Γ : Ctx Base} {σ τ : Ty Base} (body : Term Const (σ :: Γ) τ)
      (argument : Term Const Γ σ) :
      BetaStep (.app (.lam body) argument) (instantiate argument body)
  | appFun {Γ : Ctx Base} {σ τ : Ty Base} {function function' : Term Const Γ (σ ⇒ τ)}
      (argument : Term Const Γ σ) :
      BetaStep function function' → BetaStep (.app function argument) (.app function' argument)
  | appArg {Γ : Ctx Base} {σ τ : Ty Base} (function : Term Const Γ (σ ⇒ τ))
      {argument argument' : Term Const Γ σ} :
      BetaStep argument argument' → BetaStep (.app function argument) (.app function argument')
  | lam {Γ : Ctx Base} {σ τ : Ty Base} {body body' : Term Const (σ :: Γ) τ} :
      BetaStep body body' → BetaStep (.lam body) (.lam body')
  | andLeft {Γ : Ctx Base} {left left' : Formula Const Γ} (right : Formula Const Γ) :
      BetaStep left left' → BetaStep (.and left right) (.and left' right)
  | andRight {Γ : Ctx Base} (left : Formula Const Γ) {right right' : Formula Const Γ} :
      BetaStep right right' → BetaStep (.and left right) (.and left right')
  | orLeft {Γ : Ctx Base} {left left' : Formula Const Γ} (right : Formula Const Γ) :
      BetaStep left left' → BetaStep (.or left right) (.or left' right)
  | orRight {Γ : Ctx Base} (left : Formula Const Γ) {right right' : Formula Const Γ} :
      BetaStep right right' → BetaStep (.or left right) (.or left right')
  | impLeft {Γ : Ctx Base} {left left' : Formula Const Γ} (right : Formula Const Γ) :
      BetaStep left left' → BetaStep (.imp left right) (.imp left' right)
  | impRight {Γ : Ctx Base} (left : Formula Const Γ) {right right' : Formula Const Γ} :
      BetaStep right right' → BetaStep (.imp left right) (.imp left right')
  | not {Γ : Ctx Base} {operand operand' : Formula Const Γ} :
      BetaStep operand operand' → BetaStep (.not operand) (.not operand')
  | eqLeft {Γ : Ctx Base} {τ : Ty Base} {left left' : Term Const Γ τ} (right : Term Const Γ τ) :
      BetaStep left left' → BetaStep (.eq left right) (.eq left' right)
  | eqRight {Γ : Ctx Base} {τ : Ty Base} (left : Term Const Γ τ) {right right' : Term Const Γ τ} :
      BetaStep right right' → BetaStep (.eq left right) (.eq left right')
  | all {Γ : Ctx Base} {σ : Ty Base} {body body' : Formula Const (σ :: Γ)} :
      BetaStep body body' → BetaStep (.all body) (.all body')
  | ex {Γ : Ctx Base} {σ : Ty Base} {body body' : Formula Const (σ :: Γ)} :
      BetaStep body body' → BetaStep (.ex body) (.ex body')

/-- An execution: a finite sequence of beta steps, retaining every
intermediate term and every step. -/
inductive Execution {Γ : Ctx Base} {τ : Ty Base} :
    Term Const Γ τ → Term Const Γ τ → Type (max u v) where
  | done (term : Term Const Γ τ) : Execution term term
  | step {source middle target : Term Const Γ τ} :
      BetaStep source middle → Execution middle target → Execution source target

/-! ## Congruence proofs under the connectives

The calculus has congruence rules for application and abstraction only. A step
under a connective is elaborated through a one-hole context: an equation
between the holes gives one between the filled contexts by two beta steps and
argument congruence (`holeCongr`). Under a quantifier the hole binds a
variable, so the step is elaborated by eliminating and reintroducing the
quantifier on both sides (`allCongr`, `exCongr`). -/

section Congruence

variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)}

/-- Transport a proof along an equality of conclusions. -/
def castConclusion {φ ψ : Formula Const Γ} (same : φ = ψ) (proof : ProofSyntax Const Δ φ) :
    ProofSyntax Const Δ ψ :=
  same ▸ proof

theorem castConclusion_heq {φ ψ : Formula Const Γ} (same : φ = ψ)
    (proof : ProofSyntax Const Δ φ) : HEq (castConclusion same proof) proof := by
  subst same
  rfl

/-- Transport an equational proof along equalities of its two sides. -/
def castEq {τ : Ty Base} {s s' t t' : Term Const Γ τ} (sources : s = s') (targets : t = t')
    (proof : ProofSyntax Const Δ (.eq s t)) : ProofSyntax Const Δ (.eq s' t') :=
  castConclusion (by rw [sources, targets]) proof

theorem castEq_heq {τ : Ty Base} {s s' t t' : Term Const Γ τ} (sources : s = s')
    (targets : t = t') (proof : ProofSyntax Const Δ (.eq s t)) :
    HEq (castEq sources targets proof) proof :=
  castConclusion_heq _ proof

/-- Rewriting inside a one-hole context: an equation between two holes gives
an equation between the filled contexts. -/
def holeCongr {σ τ : Ty Base} (body : Term Const (σ :: Γ) τ) {hole hole' : Term Const Γ σ}
    (proof : ProofSyntax Const Δ (.eq hole hole')) :
    ProofSyntax Const Δ (.eq (instantiate hole body) (instantiate hole' body)) :=
  .eqTrans (.eqSymm (.beta hole body)) (.eqTrans (.eqAppArg (.lam body) proof) (.beta hole' body))

theorem instantiate_vz_rename_lift_weaken {σ τ : Ty Base} (term : Term Const (σ :: Γ) τ) :
    instantiate (.var .vz) (rename (Rename.lift (Rename.weaken (Γ := Γ) (σ := σ))) term) =
      term := by
  unfold instantiate
  rw [subst_rename]
  conv_rhs => rw [← subst_id term]
  apply subst_ext
  intro _ index
  cases index <;> rfl

theorem subst_lift_rename_lift_weaken {Γ' : Ctx Base} {σ ρ τ : Ty Base}
    (θ : Subst Const Γ Γ') (term : Term Const (ρ :: Γ) τ) :
    HOL.subst (Subst.lift (Subst.lift θ))
        (rename (Rename.lift (Rename.weaken (Γ := Γ) (σ := σ))) term) =
      rename (Rename.lift (Rename.weaken (Γ := Γ') (σ := σ))) (HOL.subst (Subst.lift θ) term) := by
  rw [subst_rename, rename_subst]
  apply subst_ext
  intro _ index
  cases index with
  | vz => rfl
  | vs index =>
      simp only [Subst.lift, Rename.lift]
      rw [rename_lift_weaken]
      rfl

theorem fin_heq_of_val {m n : Nat} (lengths : m = n) (first : Fin m) (second : Fin n)
    (values : first.val = second.val) : HEq first second := by
  subst lengths
  exact heq_of_eq (Fin.ext values)

/-- Instantiate the bound variable of a weakened quantifier body at the new
variable. -/
def instantiateFresh {σ : Ty Base} {Ξ : List (Formula Const (σ :: Γ))}
    {φ : Formula Const (σ :: Γ)}
    (proof : ProofSyntax Const Ξ (.all (rename (Rename.lift (Rename.weaken (Γ := Γ) (σ := σ))) φ))) :
    ProofSyntax Const Ξ φ :=
  castConclusion (instantiate_vz_rename_lift_weaken φ) (.allE (.var .vz) proof)

/-- From `∀x. φ → φ'`, conclude `(∀x. φ) → (∀x. φ')`. -/
def allImp {σ : Ty Base} {φ φ' : Formula Const (σ :: Γ)}
    (pointwise : ProofSyntax Const Δ (.all (.imp φ φ'))) :
    ProofSyntax Const Δ (.imp (.all φ) (.all φ')) :=
  .impE (.impI (.impI (.allI (.impE
      (instantiateFresh
        (ProofSyntax.hyp (Δ := weakenHyps (σ := σ) (.all φ :: .all (.imp φ φ') :: Δ))
          ⟨1, by simp [weakenHyps]⟩))
      (instantiateFresh
        (ProofSyntax.hyp (Δ := weakenHyps (σ := σ) (.all φ :: .all (.imp φ φ') :: Δ))
          ⟨0, by simp [weakenHyps]⟩))))))
    pointwise

/-- From `∀x. φ → φ'`, conclude `(∃x. φ) → (∃x. φ')`. -/
def exImp {σ : Ty Base} {φ φ' : Formula Const (σ :: Γ)}
    (pointwise : ProofSyntax Const Δ (.all (.imp φ φ'))) :
    ProofSyntax Const Δ (.imp (.ex φ) (.ex φ')) :=
  .impE (.impI (.impI (.exE (ψ := .ex φ') (ProofSyntax.hyp ⟨0, by simp⟩)
      (.exI (φ := rename (Rename.lift (Rename.weaken (Γ := Γ) (σ := σ))) φ') (.var .vz)
        (castConclusion (instantiate_vz_rename_lift_weaken φ').symm
          (.impE
            (instantiateFresh
              (ProofSyntax.hyp
                (Δ := φ :: weakenHyps (σ := σ) (.ex φ :: .all (.imp φ φ') :: Δ))
                ⟨2, by simp [weakenHyps]⟩))
            (ProofSyntax.hyp ⟨0, by simp⟩)))))))
    pointwise

/-- Congruence of the universal quantifier. -/
def allCongr {σ : Ty Base} {φ φ' : Formula Const (σ :: Γ)}
    (proof : ProofSyntax Const (weakenHyps (σ := σ) Δ) (.eq φ φ')) :
    ProofSyntax Const Δ (.eq (.all φ) (.all φ')) :=
  .eqPropI (allImp (.allI (.eqPropEL proof))) (allImp (.allI (.eqPropER proof)))

/-- Congruence of the existential quantifier. -/
def exCongr {σ : Ty Base} {φ φ' : Formula Const (σ :: Γ)}
    (proof : ProofSyntax Const (weakenHyps (σ := σ) Δ) (.eq φ φ')) :
    ProofSyntax Const Δ (.eq (.ex φ) (.ex φ')) :=
  .eqPropI (exImp (.allI (.eqPropEL proof))) (exImp (.allI (.eqPropER proof)))

theorem allCongr_heq {Δ₁ Δ₂ : List (Formula Const Γ)} (hypotheses : Δ₁ = Δ₂) {σ : Ty Base}
    {φ₁ φ₁' φ₂ φ₂' : Formula Const (σ :: Γ)} (sources : φ₁ = φ₂) (targets : φ₁' = φ₂')
    {first : ProofSyntax Const (weakenHyps (σ := σ) Δ₁) (.eq φ₁ φ₁')}
    {second : ProofSyntax Const (weakenHyps (σ := σ) Δ₂) (.eq φ₂ φ₂')}
    (same : HEq first second) : HEq (allCongr first) (allCongr second) := by
  subst hypotheses sources targets
  cases same
  rfl

theorem exCongr_heq {Δ₁ Δ₂ : List (Formula Const Γ)} (hypotheses : Δ₁ = Δ₂) {σ : Ty Base}
    {φ₁ φ₁' φ₂ φ₂' : Formula Const (σ :: Γ)} (sources : φ₁ = φ₂) (targets : φ₁' = φ₂')
    {first : ProofSyntax Const (weakenHyps (σ := σ) Δ₁) (.eq φ₁ φ₁')}
    {second : ProofSyntax Const (weakenHyps (σ := σ) Δ₂) (.eq φ₂ φ₂')}
    (same : HEq first second) : HEq (exCongr first) (exCongr second) := by
  subst hypotheses sources targets
  cases same
  rfl

end Congruence

namespace BetaStep

/-- Substitution acts on a step. At a root redex the contracted term is
transported along the substitution lemma for instantiation. -/
def subst {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') :
    {τ : Ty Base} → {source target : Term Const Γ τ} →
      BetaStep source target → BetaStep (HOL.subst θ source) (HOL.subst θ target)
  | _, _, _, .beta body argument =>
      (congrArg (BetaStep (Const := Const) _)
        (ProofSyntax.subst_instantiate θ argument body)).mpr
        (.beta (HOL.subst (Subst.lift θ) body) (HOL.subst θ argument))
  | _, _, _, .appFun argument step => .appFun (HOL.subst θ argument) (subst θ step)
  | _, _, _, .appArg function step => .appArg (HOL.subst θ function) (subst θ step)
  | _, _, _, .lam step => .lam (subst (Subst.lift θ) step)
  | _, _, _, .andLeft right step => .andLeft (HOL.subst θ right) (subst θ step)
  | _, _, _, .andRight left step => .andRight (HOL.subst θ left) (subst θ step)
  | _, _, _, .orLeft right step => .orLeft (HOL.subst θ right) (subst θ step)
  | _, _, _, .orRight left step => .orRight (HOL.subst θ left) (subst θ step)
  | _, _, _, .impLeft right step => .impLeft (HOL.subst θ right) (subst θ step)
  | _, _, _, .impRight left step => .impRight (HOL.subst θ left) (subst θ step)
  | _, _, _, .not step => .not (subst θ step)
  | _, _, _, .eqLeft right step => .eqLeft (HOL.subst θ right) (subst θ step)
  | _, _, _, .eqRight left step => .eqRight (HOL.subst θ left) (subst θ step)
  | _, _, _, .all step => .all (subst (Subst.lift θ) step)
  | _, _, _, .ex step => .ex (subst (Subst.lift θ) step)

theorem subst_heq_of_heq {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') {τ : Ty Base}
    {source₁ source₂ target₁ target₂ : Term Const Γ τ}
    (sources : source₁ = source₂) (targets : target₁ = target₂)
    {first : BetaStep source₁ target₁} {second : BetaStep source₂ target₂}
    (same : HEq first second) : HEq (subst θ first) (subst θ second) := by
  subst sources targets
  cases same
  rfl

theorem subst_heq_self {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (step : BetaStep source target) (θ : Subst Const Γ Γ)
    (identity : ∀ {τ : Ty Base} (index : Var Γ τ), θ index = .var index) :
    HEq (subst θ step) step := by
  induction step with
  | _ =>
      simp only [subst]
      try refine (ProofSyntax.mpr_heq _ _).trans ?_
      congr 1
      all_goals first
        | exact ProofSyntax.term_subst_of_identity identity _
        | exact ProofSyntax.term_subst_of_identity (ProofSyntax.lift_of_identity identity) _
        | solve_by_elim (maxDepth := 4) [ProofSyntax.lift_of_identity]

theorem subst_subst_heq {Γ Γ' Γ'' : Ctx Base} {τ : Ty Base}
    {source target : Term Const Γ τ} (step : BetaStep source target)
    (θ : Subst Const Γ Γ'') (f : Subst Const Γ' Γ'') (g : Subst Const Γ Γ')
    (composite : ∀ {τ : Ty Base} (index : Var Γ τ), θ index = HOL.subst f (g index)) :
    HEq (subst θ step) (subst f (subst g step)) := by
  induction step generalizing Γ' Γ'' with
  | beta body argument =>
      simp only [subst]
      refine (ProofSyntax.mpr_heq _ _).trans ?_
      refine HEq.trans ?_ (subst_heq_of_heq f rfl
        (ProofSyntax.subst_instantiate g argument body) (ProofSyntax.mpr_heq _ _)).symm
      simp only [subst]
      refine HEq.trans ?_ (ProofSyntax.mpr_heq _ _).symm
      congr 1
      · exact ProofSyntax.term_subst_of_composite
          (ProofSyntax.lift_of_composite composite) body
      · exact ProofSyntax.term_subst_of_composite composite argument
  | _ =>
      simp only [subst]
      congr 1
      all_goals first
        | exact ProofSyntax.term_subst_of_composite composite _
        | exact ProofSyntax.term_subst_of_composite (ProofSyntax.lift_of_composite composite) _
        | solve_by_elim (maxDepth := 6) [ProofSyntax.lift_of_composite]

/-- The explicit equational proof of one step, under any assumptions. -/
def proof {Γ : Ctx Base} (Δ : List (Formula Const Γ)) :
    {τ : Ty Base} → {source target : Term Const Γ τ} →
      BetaStep source target → ProofSyntax Const Δ (.eq source target)
  | _, _, _, .beta body argument => .beta argument body
  | _, _, _, .appFun argument step => .eqApp argument (proof Δ step)
  | _, _, _, .appArg function step => .eqAppArg function (proof Δ step)
  | _, _, _, .lam step => .eqLam (proof (weakenHyps Δ) step)
  | _, _, _, @BetaStep.andLeft _ _ _ left left' right step =>
      castEq (congrArg (Term.and left) (instantiate_weaken left right))
        (congrArg (Term.and left') (instantiate_weaken left' right))
        (holeCongr (.and (.var .vz) (weaken right)) (proof Δ step))
  | _, _, _, @BetaStep.andRight _ _ _ left right right' step =>
      castEq (congrArg (fun hole => Term.and hole right) (instantiate_weaken right left))
        (congrArg (fun hole => Term.and hole right') (instantiate_weaken right' left))
        (holeCongr (.and (weaken left) (.var .vz)) (proof Δ step))
  | _, _, _, @BetaStep.orLeft _ _ _ left left' right step =>
      castEq (congrArg (Term.or left) (instantiate_weaken left right))
        (congrArg (Term.or left') (instantiate_weaken left' right))
        (holeCongr (.or (.var .vz) (weaken right)) (proof Δ step))
  | _, _, _, @BetaStep.orRight _ _ _ left right right' step =>
      castEq (congrArg (fun hole => Term.or hole right) (instantiate_weaken right left))
        (congrArg (fun hole => Term.or hole right') (instantiate_weaken right' left))
        (holeCongr (.or (weaken left) (.var .vz)) (proof Δ step))
  | _, _, _, @BetaStep.impLeft _ _ _ left left' right step =>
      castEq (congrArg (Term.imp left) (instantiate_weaken left right))
        (congrArg (Term.imp left') (instantiate_weaken left' right))
        (holeCongr (.imp (.var .vz) (weaken right)) (proof Δ step))
  | _, _, _, @BetaStep.impRight _ _ _ left right right' step =>
      castEq (congrArg (fun hole => Term.imp hole right) (instantiate_weaken right left))
        (congrArg (fun hole => Term.imp hole right') (instantiate_weaken right' left))
        (holeCongr (.imp (weaken left) (.var .vz)) (proof Δ step))
  | _, _, _, .not step => castEq rfl rfl (holeCongr (.not (.var .vz)) (proof Δ step))
  | _, _, _, @BetaStep.eqLeft _ _ _ _ left left' right step =>
      castEq (congrArg (Term.eq left) (instantiate_weaken left right))
        (congrArg (Term.eq left') (instantiate_weaken left' right))
        (holeCongr (.eq (.var .vz) (weaken right)) (proof Δ step))
  | _, _, _, @BetaStep.eqRight _ _ _ _ left right right' step =>
      castEq (congrArg (fun hole => Term.eq hole right) (instantiate_weaken right left))
        (congrArg (fun hole => Term.eq hole right') (instantiate_weaken right' left))
        (holeCongr (.eq (weaken left) (.var .vz)) (proof Δ step))
  | _, _, _, .all step => allCongr (proof (weakenHyps Δ) step)
  | _, _, _, .ex step => exCongr (proof (weakenHyps Δ) step)

theorem proof_heq_of_hypotheses {Γ : Ctx Base} {Δ₁ Δ₂ : List (Formula Const Γ)}
    (same : Δ₁ = Δ₂) {τ : Ty Base} {source target : Term Const Γ τ}
    (step : BetaStep source target) : HEq (proof Δ₁ step) (proof Δ₂ step) := by
  subst same
  rfl

theorem subst_holeCongr_heq {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') {Δ : List (Formula Const Γ)}
    {σ τ : Ty Base} (body : Term Const (σ :: Γ) τ) {hole hole' : Term Const Γ σ}
    (proof : ProofSyntax Const Δ (.eq hole hole')) :
    HEq (ProofSyntax.subst θ (holeCongr body proof))
      (holeCongr (HOL.subst (Subst.lift θ) body) (ProofSyntax.subst θ proof)) := by
  simp only [holeCongr, ProofSyntax.subst]
  congr 1
  all_goals first
    | exact ProofSyntax.subst_instantiate _ _ _
    | (congr 1
       all_goals first
        | exact ProofSyntax.subst_instantiate _ _ _
        | exact ProofSyntax.mpr_heq _ _)

theorem holeCongr_heq {Γ : Ctx Base} {Δ₁ Δ₂ : List (Formula Const Γ)} (hypotheses : Δ₁ = Δ₂)
    {σ τ : Ty Base} {body₁ body₂ : Term Const (σ :: Γ) τ} (bodies : body₁ = body₂)
    {hole₁ hole₁' hole₂ hole₂' : Term Const Γ σ} (holes : hole₁ = hole₂) (holes' : hole₁' = hole₂')
    {first : ProofSyntax Const Δ₁ (.eq hole₁ hole₁')} {second : ProofSyntax Const Δ₂ (.eq hole₂ hole₂')}
    (same : HEq first second) : HEq (holeCongr body₁ first) (holeCongr body₂ second) := by
  subst hypotheses bodies holes holes'
  cases same
  rfl

theorem subst_castConclusion_heq {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ')
    {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ} (same : φ = ψ)
    (proof : ProofSyntax Const Δ φ) :
    HEq (ProofSyntax.subst θ (castConclusion same proof)) (ProofSyntax.subst θ proof) := by
  subst same
  rfl

/-- One step of peeling a heterogeneous equality between a substituted
composite proof and its expected form. -/
local macro "heq_step" : tactic => `(tactic| first
    | (with_reducible rfl)
    | assumption
    | (exact ProofSyntax.subst_weakenHyps _ _)
    | (exact heq_of_eq (ProofSyntax.subst_weakenHyps _ _))
    | (exact congrArg (List.cons _) (ProofSyntax.subst_weakenHyps _ _))
    | (exact ProofSyntax.fin_cast_heq _ _)
    | (refine (ProofSyntax.mpr_heq _ _).trans ?_)
    | (refine (ProofSyntax.mp_heq _ _).trans ?_)
    | (refine (ProofSyntax.id_mp_heq _ _).trans ?_)
    | (refine (subst_castConclusion_heq _ _ _).trans ?_)
    | (refine HEq.trans ?_ (castConclusion_heq _ _).symm)
    | (apply eq_of_heq; refine (ProofSyntax.mpr_heq _ _).trans ?_)
    | (apply eq_of_heq; refine (ProofSyntax.mp_heq _ _).trans ?_)
    | (apply eq_of_heq; refine (ProofSyntax.id_mp_heq _ _).trans ?_)
    | (apply eq_of_heq; refine (subst_castConclusion_heq _ _ _).trans ?_)
    | (apply eq_of_heq; refine HEq.trans ?_ (castConclusion_heq _ _).symm)
    | (show @HEq (ProofSyntax _ _ _) _ (ProofSyntax _ _ _) _; simp only [ProofSyntax.subst])
    | (show @Eq (ProofSyntax _ _ _) _ _; simp only [ProofSyntax.subst])
    | (show @HEq (ProofSyntax _ _ _) _ (ProofSyntax _ _ _) _; congr 1)
    | (show @Eq (ProofSyntax _ _ _) _ _; congr 1)
    | (exact subst_lift_rename_lift_weaken _ _)
    | (exact fin_heq_of_val (by simp [weakenHyps]) _ _ rfl)
    | (simp [ProofSyntax.subst_instantiate, instantiate_vz_rename_lift_weaken,
        subst_lift_rename_lift_weaken, rename]; done))

theorem subst_allCongr_heq {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') {Δ : List (Formula Const Γ)}
    {σ : Ty Base} {φ φ' : Formula Const (σ :: Γ)}
    (proof : ProofSyntax Const (weakenHyps (σ := σ) Δ) (.eq φ φ'))
    {proof' : ProofSyntax Const (weakenHyps (σ := σ) (Δ.map (HOL.subst θ)))
      (.eq (HOL.subst (Subst.lift θ) φ) (HOL.subst (Subst.lift θ) φ'))}
    (same : HEq (ProofSyntax.subst (Subst.lift θ) proof) proof') :
    HEq (ProofSyntax.subst θ (allCongr proof)) (allCongr proof') := by
  simp only [allCongr, allImp, instantiateFresh, ProofSyntax.subst]
  congr 1
  repeat' heq_step

theorem subst_exCongr_heq {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') {Δ : List (Formula Const Γ)}
    {σ : Ty Base} {φ φ' : Formula Const (σ :: Γ)}
    (proof : ProofSyntax Const (weakenHyps (σ := σ) Δ) (.eq φ φ'))
    {proof' : ProofSyntax Const (weakenHyps (σ := σ) (Δ.map (HOL.subst θ)))
      (.eq (HOL.subst (Subst.lift θ) φ) (HOL.subst (Subst.lift θ) φ'))}
    (same : HEq (ProofSyntax.subst (Subst.lift θ) proof) proof') :
    HEq (ProofSyntax.subst θ (exCongr proof)) (exCongr proof') := by
  simp only [exCongr, exImp, instantiateFresh, ProofSyntax.subst]
  congr 1
  repeat' heq_step

/-- Elaboration commutes with substitution. -/
theorem proof_subst_heq {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') (Δ : List (Formula Const Γ))
    {τ : Ty Base} {source target : Term Const Γ τ} (step : BetaStep source target) :
    HEq (ProofSyntax.subst θ (proof Δ step)) (proof (Δ.map (HOL.subst θ)) (subst θ step)) := by
  induction step generalizing Γ' with
  | beta body argument =>
      simp only [proof, subst, ProofSyntax.subst]
      refine (ProofSyntax.mpr_heq _ _).trans ?_
      have transported :
          ∀ {target' : Term Const Γ' _}
            (same : instantiate (HOL.subst θ argument) (HOL.subst (Subst.lift θ) body) = target')
            (moved : BetaStep (HOL.subst θ (.app (.lam body) argument)) target'),
            HEq moved (BetaStep.beta (HOL.subst (Subst.lift θ) body) (HOL.subst θ argument)) →
            HEq (ProofSyntax.beta (Δ := Δ.map (HOL.subst θ)) (HOL.subst θ argument)
                (HOL.subst (Subst.lift θ) body))
              (proof (Δ.map (HOL.subst θ)) moved) := by
        intro target' same moved related
        subst same
        cases related
        rfl
      exact transported (ProofSyntax.subst_instantiate θ argument body).symm _
        (ProofSyntax.mpr_heq _ _)
  | appFun argument step ih =>
      simp only [proof, subst, ProofSyntax.subst]
      congr 1
      exact eq_of_heq (ih θ Δ)
  | appArg function step ih =>
      simp only [proof, subst, ProofSyntax.subst]
      congr 1
      exact eq_of_heq (ih θ Δ)
  | lam step ih =>
      simp only [proof, subst, ProofSyntax.subst]
      congr 1
      apply eq_of_heq
      refine (ProofSyntax.mp_heq _ _).trans ?_
      refine (ih (Subst.lift θ) (weakenHyps Δ)).trans ?_
      exact proof_heq_of_hypotheses (ProofSyntax.subst_weakenHyps θ Δ) _
  | andLeft right step ih =>
      simp only [proof, subst, castEq]
      refine (subst_castConclusion_heq _ _ _).trans ?_
      refine (subst_holeCongr_heq θ _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact holeCongr_heq rfl (by simp [HOL.subst, Subst.lift]) rfl rfl (ih θ Δ)
  | andRight left step ih =>
      simp only [proof, subst, castEq]
      refine (subst_castConclusion_heq _ _ _).trans ?_
      refine (subst_holeCongr_heq θ _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact holeCongr_heq rfl (by simp [HOL.subst, Subst.lift]) rfl rfl (ih θ Δ)
  | orLeft right step ih =>
      simp only [proof, subst, castEq]
      refine (subst_castConclusion_heq _ _ _).trans ?_
      refine (subst_holeCongr_heq θ _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact holeCongr_heq rfl (by simp [HOL.subst, Subst.lift]) rfl rfl (ih θ Δ)
  | orRight left step ih =>
      simp only [proof, subst, castEq]
      refine (subst_castConclusion_heq _ _ _).trans ?_
      refine (subst_holeCongr_heq θ _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact holeCongr_heq rfl (by simp [HOL.subst, Subst.lift]) rfl rfl (ih θ Δ)
  | impLeft right step ih =>
      simp only [proof, subst, castEq]
      refine (subst_castConclusion_heq _ _ _).trans ?_
      refine (subst_holeCongr_heq θ _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact holeCongr_heq rfl (by simp [HOL.subst, Subst.lift]) rfl rfl (ih θ Δ)
  | impRight left step ih =>
      simp only [proof, subst, castEq]
      refine (subst_castConclusion_heq _ _ _).trans ?_
      refine (subst_holeCongr_heq θ _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact holeCongr_heq rfl (by simp [HOL.subst, Subst.lift]) rfl rfl (ih θ Δ)
  | eqLeft right step ih =>
      simp only [proof, subst, castEq]
      refine (subst_castConclusion_heq _ _ _).trans ?_
      refine (subst_holeCongr_heq θ _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact holeCongr_heq rfl (by simp [HOL.subst, Subst.lift]) rfl rfl (ih θ Δ)
  | eqRight left step ih =>
      simp only [proof, subst, castEq]
      refine (subst_castConclusion_heq _ _ _).trans ?_
      refine (subst_holeCongr_heq θ _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact holeCongr_heq rfl (by simp [HOL.subst, Subst.lift]) rfl rfl (ih θ Δ)
  | not step ih =>
      simp only [proof, subst, castEq]
      refine (subst_castConclusion_heq _ _ _).trans ?_
      refine (subst_holeCongr_heq θ _ _).trans ?_
      refine HEq.trans ?_ (castConclusion_heq _ _).symm
      exact holeCongr_heq rfl rfl rfl rfl (ih θ Δ)
  | all step ih =>
      simp only [proof, subst]
      exact subst_allCongr_heq θ _ ((ih (Subst.lift θ) (weakenHyps Δ)).trans
        (proof_heq_of_hypotheses (ProofSyntax.subst_weakenHyps θ Δ) _))
  | ex step ih =>
      simp only [proof, subst]
      exact subst_exCongr_heq θ _ ((ih (Subst.lift θ) (weakenHyps Δ)).trans
        (proof_heq_of_hypotheses (ProofSyntax.subst_weakenHyps θ Δ) _))

end BetaStep

namespace Execution

/-- Substitution acts step by step on an execution. -/
def subst {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') {τ : Ty Base} :
    {source target : Term Const Γ τ} →
      Execution source target → Execution (HOL.subst θ source) (HOL.subst θ target)
  | _, _, .done term => .done (HOL.subst θ term)
  | _, _, .step first rest => .step (first.subst θ) (subst θ rest)

theorem subst_heq_self {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (execution : Execution source target) (θ : Subst Const Γ Γ)
    (identity : ∀ {τ : Ty Base} (index : Var Γ τ), θ index = .var index) :
    HEq (subst θ execution) execution := by
  induction execution with
  | done term =>
      simp only [subst]
      congr 1
      all_goals exact ProofSyntax.term_subst_of_identity identity term
  | step first rest ih =>
      simp only [subst]
      congr 1
      all_goals first
        | exact ProofSyntax.term_subst_of_identity identity _
        | exact first.subst_heq_self θ identity

theorem subst_subst_heq {Γ Γ' Γ'' : Ctx Base} {τ : Ty Base}
    {source target : Term Const Γ τ} (execution : Execution source target)
    (θ : Subst Const Γ Γ'') (f : Subst Const Γ' Γ'') (g : Subst Const Γ Γ')
    (composite : ∀ {τ : Ty Base} (index : Var Γ τ), θ index = HOL.subst f (g index)) :
    HEq (subst θ execution) (subst f (subst g execution)) := by
  induction execution with
  | done term =>
      simp only [subst]
      congr 1
      all_goals exact ProofSyntax.term_subst_of_composite composite term
  | step first rest ih =>
      simp only [subst]
      congr 1
      all_goals first
        | exact ProofSyntax.term_subst_of_composite composite _
        | exact first.subst_subst_heq θ f g composite

/-- Elaborate an execution into an explicit equational proof: reflexivity for
the empty execution, transitivity through every intermediate term. -/
def proof {Γ : Ctx Base} (Δ : List (Formula Const Γ)) {τ : Ty Base} :
    {source target : Term Const Γ τ} →
      Execution source target → ProofSyntax Const Δ (.eq source target)
  | _, _, .done term => .eqRefl term
  | _, _, .step first rest => .eqTrans (first.proof Δ) (proof Δ rest)

theorem proof_subst_heq {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') (Δ : List (Formula Const Γ))
    {τ : Ty Base} {source target : Term Const Γ τ} (execution : Execution source target) :
    HEq (ProofSyntax.subst θ (proof Δ execution))
      (proof (Δ.map (HOL.subst θ)) (subst θ execution)) := by
  induction execution with
  | done term => rfl
  | step first rest ih =>
      simp only [proof, subst, ProofSyntax.subst]
      congr 1
      · exact eq_of_heq (BetaStep.proof_subst_heq θ Δ first)
      · exact eq_of_heq ih

end Execution

/-! ## Elaboration retains the whole execution -/

/-- A retained proof together with its sequent: the carrier of the intensional
face at one context. -/
abbrev ProvedSequent (Γ : Ctx Base) : Type (max u v) :=
  Σ sequent : List (Formula Const Γ) × Formula Const Γ,
    ProofSyntax Const sequent.1 sequent.2

/-- The root rule of an equational proof, for the rules elaboration uses. -/
def equationalRule {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    ProofSyntax Const Δ φ → Option ProofSyntax.RuleTag
  | .beta _ _ => some .beta
  | .eqApp _ _ => some .eqApp
  | .eqAppArg _ _ => some .eqAppArg
  | .eqLam _ => some .eqLam
  | .eqRefl _ => some .eqRefl
  | .eqTrans _ _ => some .eqTrans
  | _ => none

/-- The root rule of a packed proof. -/
def rootRule {Γ : Ctx Base} (packed : ProvedSequent (Const := Const) Γ) :
    Option ProofSyntax.RuleTag :=
  equationalRule packed.2

theorem eq_targets_of_packed {Γ : Ctx Base} {Δ₁ Δ₂ : List (Formula Const Γ)} {τ : Ty Base}
    {source₁ source₂ target₁ target₂ : Term Const Γ τ}
    {first : ProofSyntax Const Δ₁ (.eq source₁ target₁)}
    {second : ProofSyntax Const Δ₂ (.eq source₂ target₂)}
    (same : (⟨(Δ₁, .eq source₁ target₁), first⟩ : ProvedSequent Γ) =
      ⟨(Δ₂, .eq source₂ target₂), second⟩) :
    Δ₁ = Δ₂ ∧ source₁ = source₂ ∧ target₁ = target₂ ∧ HEq first second := by
  obtain ⟨sequents, proofs⟩ := Sigma.mk.inj_iff.mp same
  obtain ⟨hypotheses, conclusions⟩ := Prod.mk.inj sequents
  obtain ⟨_, sources, targets⟩ := Term.eq.inj conclusions
  exact ⟨hypotheses, eq_of_heq sources, eq_of_heq targets, proofs⟩

/-- The middle term of a transitivity step, if the proof ends with one. -/
def eqTransMiddle {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    ProofSyntax Const Δ φ → Option (Σ τ : Ty Base, Term Const Γ τ)
  | @ProofSyntax.eqTrans _ _ _ _ τ _ middle _ _ _ => some ⟨τ, middle⟩
  | _ => none

theorem eqTransMiddle_heq {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ₁ φ₂ : Formula Const Γ}
    (conclusions : φ₁ = φ₂) {first : ProofSyntax Const Δ φ₁} {second : ProofSyntax Const Δ φ₂}
    (same : HEq first second) : eqTransMiddle first = eqTransMiddle second := by
  subst conclusions
  cases same
  rfl

theorem holeCongr_injective {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {σ τ : Ty Base}
    {body : Term Const (σ :: Γ) τ} {hole hole' : Term Const Γ σ}
    {first second : ProofSyntax Const Δ (.eq hole hole')}
    (same : holeCongr body first = holeCongr body second) : first = second := by
  simpa [holeCongr] using same

theorem allCongr_injective {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {σ : Ty Base}
    {φ φ' : Formula Const (σ :: Γ)} {first second : ProofSyntax Const (weakenHyps Δ) (.eq φ φ')}
    (same : allCongr first = allCongr second) : first = second := by
  simpa [allCongr, allImp] using same

theorem exCongr_injective {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {σ : Ty Base}
    {φ φ' : Formula Const (σ :: Γ)} {first second : ProofSyntax Const (weakenHyps Δ) (.eq φ φ')}
    (same : exCongr first = exCongr second) : first = second := by
  simpa [exCongr, exImp] using same

theorem instantiate_and {Γ : Ctx Base} {σ : Ty Base} (term : Term Const Γ σ)
    (left right : Formula Const (σ :: Γ)) :
    instantiate term (.and left right) = .and (instantiate term left) (instantiate term right) := rfl

theorem instantiate_or {Γ : Ctx Base} {σ : Ty Base} (term : Term Const Γ σ)
    (left right : Formula Const (σ :: Γ)) :
    instantiate term (.or left right) = .or (instantiate term left) (instantiate term right) := rfl

theorem instantiate_imp {Γ : Ctx Base} {σ : Ty Base} (term : Term Const Γ σ)
    (left right : Formula Const (σ :: Γ)) :
    instantiate term (.imp left right) = .imp (instantiate term left) (instantiate term right) := rfl

theorem instantiate_eq {Γ : Ctx Base} {σ τ : Ty Base} (term : Term Const Γ σ)
    (left right : Term Const (σ :: Γ) τ) :
    instantiate term (.eq left right) = .eq (instantiate term left) (instantiate term right) := rfl

/-- Two hole congruences with the same conclusion and the same proof have the
same context and the same hole. -/
theorem holeCongr_bodies {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {σ τ : Ty Base}
    {body₁ body₂ : Term Const (σ :: Γ) τ} {hole₁ hole₁' hole₂ hole₂' : Term Const Γ σ}
    {first : ProofSyntax Const Δ (.eq hole₁ hole₁')}
    {second : ProofSyntax Const Δ (.eq hole₂ hole₂')}
    (sources : instantiate hole₁ body₁ = instantiate hole₂ body₂)
    (targets : instantiate hole₁' body₁ = instantiate hole₂' body₂)
    (same : HEq (holeCongr body₁ first) (holeCongr body₂ second)) :
    body₁ = body₂ ∧ hole₁ = hole₂ := by
  have middles := eqTransMiddle_heq (by rw [sources, targets]) same
  simp only [holeCongr, eqTransMiddle, Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq,
    true_and, Term.app.injEq, Term.lam.injEq] at middles
  exact middles

theorem weaken_ne_var_vz {Γ : Ctx Base} {σ : Ty Base} (term : Term Const Γ σ) :
    weaken (σ := σ) term ≠ .var .vz := by
  cases term <;> simp [weaken, rename, Rename.weaken]

/-- Steps elaborate injectively: the rule, the redex position and the
contracted redex are all visible in the elaborated proof. -/
theorem BetaStep.proof_packed_injective {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {τ : Ty Base} {source target₁ target₂ : Term Const Γ τ}
    (first : BetaStep source target₁) (second : BetaStep source target₂)
    (same : (⟨(Δ, .eq source target₁), first.proof Δ⟩ : ProvedSequent Γ) =
      ⟨(Δ, .eq source target₂), second.proof Δ⟩) :
    target₁ = target₂ ∧ HEq first second := by
  induction first with
  | beta body argument =>
      cases second with
      | beta => exact ⟨rfl, HEq.rfl⟩
      | appFun _ inner =>
          have rules := congrArg rootRule same
          simp [rootRule, BetaStep.proof, equationalRule] at rules
      | appArg _ inner =>
          have rules := congrArg rootRule same
          simp [rootRule, BetaStep.proof, equationalRule] at rules
  | appFun argument step ih =>
      cases second with
      | beta =>
          have rules := congrArg rootRule same
          simp [rootRule, BetaStep.proof, equationalRule] at rules
      | appFun _ inner =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨_, functions, _⟩ := Term.app.inj targets
          cases eq_of_heq functions
          have premises := ProofSyntax.eqApp.inj (eq_of_heq proofs)
          obtain ⟨_, steps⟩ := ih inner (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _))
            premises)
          cases eq_of_heq steps
          exact ⟨rfl, HEq.rfl⟩
      | appArg _ inner =>
          have rules := congrArg rootRule same
          simp [rootRule, BetaStep.proof, equationalRule] at rules
  | appArg function step ih =>
      cases second with
      | beta =>
          have rules := congrArg rootRule same
          simp [rootRule, BetaStep.proof, equationalRule] at rules
      | appFun _ inner =>
          have rules := congrArg rootRule same
          simp [rootRule, BetaStep.proof, equationalRule] at rules
      | appArg _ inner =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨_, _, arguments⟩ := Term.app.inj targets
          cases eq_of_heq arguments
          have premises := ProofSyntax.eqAppArg.inj (eq_of_heq proofs)
          obtain ⟨_, steps⟩ := ih inner (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _))
            premises)
          cases eq_of_heq steps
          exact ⟨rfl, HEq.rfl⟩
  | lam step ih =>
      cases second with
      | lam inner =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          cases Term.lam.inj targets
          have premises := ProofSyntax.eqLam.inj (eq_of_heq proofs)
          obtain ⟨_, steps⟩ := ih inner (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _))
            premises)
          cases eq_of_heq steps
          exact ⟨rfl, HEq.rfl⟩
  | andLeft right step ih =>
      cases second with
      | andLeft _ inner =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨lefts, -⟩ := Term.and.inj targets
          cases lefts
          have premises := holeCongr_injective (eq_of_heq
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _))))
          obtain ⟨_, steps⟩ := ih inner
            (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _)) premises)
          cases eq_of_heq steps
          exact ⟨rfl, HEq.rfl⟩
      | andRight _ inner =>
          exfalso
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨bodies, -⟩ := holeCongr_bodies
            (by simp [instantiate_and])
            (by simpa [instantiate_and] using targets)
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _)))
          simp only [Term.and.injEq] at bodies
          exact weaken_ne_var_vz _ bodies.1.symm
  | andRight left step ih =>
      cases second with
      | andLeft _ inner =>
          exfalso
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨bodies, -⟩ := holeCongr_bodies
            (by simp [instantiate_and])
            (by simpa [instantiate_and] using targets)
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _)))
          simp only [Term.and.injEq] at bodies
          exact weaken_ne_var_vz _ bodies.2.symm
      | andRight _ inner =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨-, lefts⟩ := Term.and.inj targets
          cases lefts
          have premises := holeCongr_injective (eq_of_heq
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _))))
          obtain ⟨_, steps⟩ := ih inner
            (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _)) premises)
          cases eq_of_heq steps
          exact ⟨rfl, HEq.rfl⟩
  | orLeft right step ih =>
      cases second with
      | orLeft _ inner =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨lefts, -⟩ := Term.or.inj targets
          cases lefts
          have premises := holeCongr_injective (eq_of_heq
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _))))
          obtain ⟨_, steps⟩ := ih inner
            (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _)) premises)
          cases eq_of_heq steps
          exact ⟨rfl, HEq.rfl⟩
      | orRight _ inner =>
          exfalso
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨bodies, -⟩ := holeCongr_bodies
            (by simp [instantiate_or])
            (by simpa [instantiate_or] using targets)
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _)))
          simp only [Term.or.injEq] at bodies
          exact weaken_ne_var_vz _ bodies.1.symm
  | orRight left step ih =>
      cases second with
      | orLeft _ inner =>
          exfalso
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨bodies, -⟩ := holeCongr_bodies
            (by simp [instantiate_or])
            (by simpa [instantiate_or] using targets)
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _)))
          simp only [Term.or.injEq] at bodies
          exact weaken_ne_var_vz _ bodies.2.symm
      | orRight _ inner =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨-, lefts⟩ := Term.or.inj targets
          cases lefts
          have premises := holeCongr_injective (eq_of_heq
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _))))
          obtain ⟨_, steps⟩ := ih inner
            (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _)) premises)
          cases eq_of_heq steps
          exact ⟨rfl, HEq.rfl⟩
  | impLeft right step ih =>
      cases second with
      | impLeft _ inner =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨lefts, -⟩ := Term.imp.inj targets
          cases lefts
          have premises := holeCongr_injective (eq_of_heq
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _))))
          obtain ⟨_, steps⟩ := ih inner
            (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _)) premises)
          cases eq_of_heq steps
          exact ⟨rfl, HEq.rfl⟩
      | impRight _ inner =>
          exfalso
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨bodies, -⟩ := holeCongr_bodies
            (by simp [instantiate_imp])
            (by simpa [instantiate_imp] using targets)
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _)))
          simp only [Term.imp.injEq] at bodies
          exact weaken_ne_var_vz _ bodies.1.symm
  | impRight left step ih =>
      cases second with
      | impLeft _ inner =>
          exfalso
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨bodies, -⟩ := holeCongr_bodies
            (by simp [instantiate_imp])
            (by simpa [instantiate_imp] using targets)
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _)))
          simp only [Term.imp.injEq] at bodies
          exact weaken_ne_var_vz _ bodies.2.symm
      | impRight _ inner =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨-, lefts⟩ := Term.imp.inj targets
          cases lefts
          have premises := holeCongr_injective (eq_of_heq
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _))))
          obtain ⟨_, steps⟩ := ih inner
            (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _)) premises)
          cases eq_of_heq steps
          exact ⟨rfl, HEq.rfl⟩
  | eqLeft right step ih =>
      cases second with
      | eqLeft _ inner =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          simp only [Term.eq.injEq, heq_eq_eq, true_and, and_true] at targets
          cases targets
          have premises := holeCongr_injective (eq_of_heq
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _))))
          obtain ⟨_, steps⟩ := ih inner
            (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _)) premises)
          cases eq_of_heq steps
          exact ⟨rfl, HEq.rfl⟩
      | eqRight _ inner =>
          exfalso
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨bodies, -⟩ := holeCongr_bodies
            (by simp [instantiate_eq])
            (by simpa [instantiate_eq] using targets)
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _)))
          simp only [Term.eq.injEq, heq_eq_eq, true_and] at bodies
          exact weaken_ne_var_vz _ bodies.1.symm
  | eqRight left step ih =>
      cases second with
      | eqLeft _ inner =>
          exfalso
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          obtain ⟨bodies, -⟩ := holeCongr_bodies
            (by simp [instantiate_eq])
            (by simpa [instantiate_eq] using targets)
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _)))
          simp only [Term.eq.injEq, heq_eq_eq, true_and] at bodies
          exact weaken_ne_var_vz _ bodies.2.symm
      | eqRight _ inner =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          simp only [Term.eq.injEq, heq_eq_eq, true_and] at targets
          cases targets
          have premises := holeCongr_injective (eq_of_heq
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _))))
          obtain ⟨_, steps⟩ := ih inner
            (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _)) premises)
          cases eq_of_heq steps
          exact ⟨rfl, HEq.rfl⟩
  | not step ih =>
      cases second with
      | not inner =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          cases Term.not.inj targets
          have premises := holeCongr_injective (eq_of_heq
            ((castEq_heq _ _ _).symm.trans (proofs.trans (castEq_heq _ _ _))))
          obtain ⟨_, steps⟩ := ih inner
            (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _)) premises)
          cases eq_of_heq steps
          exact ⟨rfl, HEq.rfl⟩
  | all step ih =>
      cases second with
      | all inner =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          simp only [Term.all.injEq, heq_eq_eq, true_and] at targets
          cases targets
          simp only [BetaStep.proof] at proofs
          have premises := allCongr_injective (eq_of_heq proofs)
          obtain ⟨_, steps⟩ := ih inner
            (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _)) premises)
          cases eq_of_heq steps
          exact ⟨rfl, HEq.rfl⟩
  | ex step ih =>
      cases second with
      | ex inner =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          simp only [Term.ex.injEq, heq_eq_eq, true_and] at targets
          cases targets
          simp only [BetaStep.proof] at proofs
          have premises := exCongr_injective (eq_of_heq proofs)
          obtain ⟨_, steps⟩ := ih inner
            (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _)) premises)
          cases eq_of_heq steps
          exact ⟨rfl, HEq.rfl⟩

/-- Executions elaborate injectively: the elaborated proof determines every
step and every intermediate term. -/
theorem Execution.proof_packed_injective {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {τ : Ty Base} {source target₁ target₂ : Term Const Γ τ}
    (first : Execution source target₁) (second : Execution source target₂)
    (same : (⟨(Δ, .eq source target₁), first.proof Δ⟩ : ProvedSequent Γ) =
      ⟨(Δ, .eq source target₂), second.proof Δ⟩) :
    target₁ = target₂ ∧ HEq first second := by
  induction first with
  | done term =>
      cases second with
      | done => exact ⟨rfl, HEq.rfl⟩
      | step _ _ =>
          have rules := congrArg rootRule same
          simp [rootRule, Execution.proof, equationalRule] at rules
  | step firstStep rest ih =>
      cases second with
      | done =>
          have rules := congrArg rootRule same
          simp [rootRule, Execution.proof, equationalRule] at rules
      | step secondStep secondRest =>
          obtain ⟨_, _, targets, proofs⟩ := eq_targets_of_packed same
          cases targets
          obtain ⟨middles, steps, rests⟩ := ProofSyntax.eqTrans.inj (eq_of_heq proofs)
          cases middles
          obtain ⟨_, sameStep⟩ := BetaStep.proof_packed_injective firstStep secondStep
            (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _)) (eq_of_heq steps))
          cases eq_of_heq sameStep
          obtain ⟨_, sameRest⟩ := ih secondRest
            (congrArg (fun proof => (⟨_, proof⟩ : ProvedSequent _)) (eq_of_heq rests))
          cases eq_of_heq sameRest
          exact ⟨rfl, HEq.rfl⟩

/-! ## Carriers of the three faces -/

/-- Executions at one context, of any type. -/
abbrev ExecutionAt (Γ : Ctx Base) : Type (max u v) :=
  Σ τ : Ty Base, Σ source : Term Const Γ τ, Σ target : Term Const Γ τ,
    Execution source target

namespace ExecutionAt

def subst {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') (execution : ExecutionAt (Const := Const) Γ) :
    ExecutionAt (Const := Const) Γ' :=
  ⟨execution.1, HOL.subst θ execution.2.1, HOL.subst θ execution.2.2.1,
    execution.2.2.2.subst θ⟩

theorem ext {Γ : Ctx Base} {τ : Ty Base} {source₁ source₂ target₁ target₂ : Term Const Γ τ}
    {first : Execution source₁ target₁} {second : Execution source₂ target₂}
    (sources : source₁ = source₂) (targets : target₁ = target₂) (same : HEq first second) :
    (⟨τ, source₁, target₁, first⟩ : ExecutionAt Γ) = ⟨τ, source₂, target₂, second⟩ := by
  subst sources targets
  cases same
  rfl

theorem subst_id {Γ : Ctx Base} (execution : ExecutionAt (Const := Const) Γ) :
    execution.subst Subst.id = execution := by
  obtain ⟨τ, source, target, run⟩ := execution
  exact ext (HOL.subst_id source) (HOL.subst_id target) (run.subst_heq_self _ (fun _ => rfl))

theorem subst_comp {Γ Γ' Γ'' : Ctx Base} (f : Subst Const Γ' Γ'') (g : Subst Const Γ Γ')
    (execution : ExecutionAt (Const := Const) Γ) :
    execution.subst (Subst.comp f g) = (execution.subst g).subst f := by
  obtain ⟨τ, source, target, run⟩ := execution
  exact ext (HOL.subst_comp f g source).symm (HOL.subst_comp f g target).symm
    (run.subst_subst_heq _ f g (fun _ => rfl))

end ExecutionAt

namespace ProvedSequent

def subst {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') (proved : ProvedSequent (Const := Const) Γ) :
    ProvedSequent (Const := Const) Γ' :=
  ⟨(proved.1.1.map (HOL.subst θ), HOL.subst θ proved.1.2), ProofSyntax.subst θ proved.2⟩

theorem ext {Γ : Ctx Base} {Δ₁ Δ₂ : List (Formula Const Γ)} {φ₁ φ₂ : Formula Const Γ}
    {first : ProofSyntax Const Δ₁ φ₁} {second : ProofSyntax Const Δ₂ φ₂}
    (hypotheses : Δ₁ = Δ₂) (conclusions : φ₁ = φ₂) (same : HEq first second) :
    (⟨(Δ₁, φ₁), first⟩ : ProvedSequent Γ) = ⟨(Δ₂, φ₂), second⟩ := by
  subst hypotheses conclusions
  cases same
  rfl

theorem subst_id {Γ : Ctx Base} (proved : ProvedSequent (Const := Const) Γ) :
    proved.subst Subst.id = proved := by
  obtain ⟨⟨Δ, φ⟩, proof⟩ := proved
  exact ext (ProofSyntax.terms_subst_of_identity (fun _ => rfl) Δ) (HOL.subst_id φ)
    (ProofSyntax.subst_id_heq proof)

theorem subst_comp {Γ Γ' Γ'' : Ctx Base} (f : Subst Const Γ' Γ'') (g : Subst Const Γ Γ')
    (proved : ProvedSequent (Const := Const) Γ) :
    proved.subst (Subst.comp f g) = (proved.subst g).subst f := by
  obtain ⟨⟨Δ, φ⟩, proof⟩ := proved
  exact ext (ProofSyntax.terms_subst_of_composite (fun _ => rfl) Δ)
    (HOL.subst_comp f g φ).symm (ProofSyntax.subst_comp_heq proof f g)

end ProvedSequent

section Semantics

variable (M : HenkinModel.{u, v, w} Base Const)

/-- The admissible valuations of a context: the points of its space. -/
abbrev AdmissibleValuation (Γ : Ctx Base) :=
  {valuation : HenkinModel.Valuation M Γ // HenkinModel.ValuationAdmissible M valuation}

/-- The valuation denoted by a substitution, pulled back along it. -/
def AdmissibleValuation.pull {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ')
    (valuation : AdmissibleValuation M Γ') : AdmissibleValuation M Γ :=
  ⟨Soundness.substVal M θ valuation.1,
    fun index => HenkinModel.denote_admissible M valuation.2 (θ index)⟩

theorem AdmissibleValuation.pull_id {Γ : Ctx Base} (valuation : AdmissibleValuation M Γ) :
    AdmissibleValuation.pull M Subst.id valuation = valuation := rfl

theorem AdmissibleValuation.pull_comp {Γ Γ' Γ'' : Ctx Base} (f : Subst Const Γ' Γ'')
    (g : Subst Const Γ Γ') (valuation : AdmissibleValuation M Γ'') :
    AdmissibleValuation.pull M (Subst.comp f g) valuation =
      AdmissibleValuation.pull M g (AdmissibleValuation.pull M f valuation) := by
  apply Subtype.ext
  funext τ index
  exact Soundness.denote_subst M f (g index) valuation.1

/-- A semantic sequent: a predicate on the admissible valuations entailing
another. It retains which valuations satisfy each side, and nothing about a
proof. -/
structure SemanticSequent (Γ : Ctx Base) where
  hypotheses : AdmissibleValuation M Γ → Prop
  conclusion : AdmissibleValuation M Γ → Prop
  entails : ∀ valuation, hypotheses valuation → conclusion valuation

namespace SemanticSequent

variable {M}

@[ext] theorem ext {Γ : Ctx Base} {first second : SemanticSequent M Γ}
    (hypotheses : first.hypotheses = second.hypotheses)
    (conclusion : first.conclusion = second.conclusion) : first = second := by
  cases first
  cases second
  cases hypotheses
  cases conclusion
  rfl

/-- Substitution precomposes both predicates with the denoted valuation. -/
def pull {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') (sequent : SemanticSequent M Γ) :
    SemanticSequent M Γ' where
  hypotheses valuation := sequent.hypotheses (AdmissibleValuation.pull M θ valuation)
  conclusion valuation := sequent.conclusion (AdmissibleValuation.pull M θ valuation)
  entails _ := sequent.entails _

end SemanticSequent

end Semantics

/-! ## The three faces as presheaves on contexts -/

variable (Base Const) in
/-- The operational face: explicit executions. -/
def programFace : Face.{u, max u v, max (u + 1) v w} (SubstContext Base Const) where
  obj context := ULift.{max (u + 1) v w} (ExecutionAt (Const := Const) context.unop.ctx)
  map θ := TypeCat.ofHom (fun execution => ⟨execution.down.subst θ.unop⟩)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro execution
    exact congrArg ULift.up (ExecutionAt.subst_id execution.down)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro execution
    exact congrArg ULift.up (ExecutionAt.subst_comp g.unop f.unop execution.down)

variable (Base Const) in
/-- The intensional face: retained proofs with their sequents. -/
def logicFace : Face.{u, max u v, max (u + 1) v w} (SubstContext Base Const) where
  obj context := ULift.{max (u + 1) v w} (ProvedSequent (Const := Const) context.unop.ctx)
  map θ := TypeCat.ofHom (fun proved => ⟨proved.down.subst θ.unop⟩)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro proved
    exact congrArg ULift.up (ProvedSequent.subst_id proved.down)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro proved
    exact congrArg ULift.up (ProvedSequent.subst_comp g.unop f.unop proved.down)

/-- The extensional face of a Henkin model: semantic sequents. -/
def spaceFace (M : HenkinModel.{u, v, w} Base Const) :
    Face.{u, max u v, max (u + 1) v w} (SubstContext Base Const) where
  obj context := ULift.{max (u + 1) v w} (SemanticSequent M context.unop.ctx)
  map θ := TypeCat.ofHom (fun sequent => ⟨sequent.down.pull θ.unop⟩)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro sequent
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro sequent
    apply congrArg ULift.up
    ext valuation
    · exact Iff.of_eq (congrArg sequent.down.hypotheses
        (AdmissibleValuation.pull_comp M g.unop f.unop valuation))
    · exact Iff.of_eq (congrArg sequent.down.conclusion
        (AdmissibleValuation.pull_comp M g.unop f.unop valuation))

/-! ## Elaboration, soundness and the direct reading -/

theorem satisfiesHyps_subst (M : HenkinModel.{u, v, w} Base Const) {Γ Γ' : Ctx Base}
    (θ : Subst Const Γ Γ') (valuation : HenkinModel.Valuation M Γ')
    (hypotheses : List (Formula Const Γ)) :
    Soundness.SatisfiesHyps M valuation (hypotheses.map (HOL.subst θ)) ↔
      Soundness.SatisfiesHyps M (Soundness.substVal M θ valuation) hypotheses := by
  simp only [Soundness.SatisfiesHyps, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Soundness.denote_subst]

variable (Base Const) in
/-- Elaborate every execution into its explicit hypothesis-free equational
proof. -/
def elaborate : programFace Base Const ⟶ logicFace Base Const where
  app _ := TypeCat.ofHom fun execution =>
    ⟨⟨([], .eq execution.down.2.1 execution.down.2.2.1), execution.down.2.2.2.proof []⟩⟩
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨τ, source, target, run⟩⟩
    exact congrArg ULift.up
      (ProvedSequent.ext rfl rfl (Execution.proof_subst_heq θ.unop [] run).symm)

/-- Soundness of retained proofs in a Henkin model whose functions respect
extensional equality. -/
def soundness (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv) :
    logicFace Base Const ⟶ spaceFace M where
  app _ := TypeCat.ofHom fun proved =>
    ⟨{ hypotheses := fun valuation =>
          Soundness.SatisfiesHyps M valuation.1 proved.down.1.1
       conclusion := fun valuation =>
          (HenkinModel.denote M proved.down.1.2 valuation.1).down
       entails := fun valuation satisfied =>
          Soundness.extDerivation_sound proved.down.2.erase respects valuation.2 satisfied }⟩
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨⟨hypotheses, conclusion⟩, proof⟩⟩
    apply congrArg ULift.up
    ext valuation
    · exact satisfiesHyps_subst M θ.unop valuation.1 hypotheses
    · exact Iff.of_eq (congrArg ULift.down
        (Soundness.denote_subst M θ.unop conclusion valuation.1))

/-- The direct reading of an execution: its endpoints denote extensionally
equal values at every admissible valuation. -/
def meaning (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv) :
    programFace Base Const ⟶ spaceFace M where
  app _ := TypeCat.ofHom fun execution =>
    ⟨{ hypotheses := fun _ => True
       conclusion := fun valuation =>
          PreModel.Eqv M.toPreModel execution.down.1
            (HenkinModel.denote M execution.down.2.1 valuation.1)
            (HenkinModel.denote M execution.down.2.2.1 valuation.1)
       entails := fun valuation _ =>
          Soundness.extDerivation_sound (execution.down.2.2.2.proof []).erase respects
            valuation.2 (fun _ member => nomatch member) }⟩
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨τ, source, target, run⟩⟩
    apply congrArg ULift.up
    ext valuation
    · rfl
    · change PreModel.Eqv M.toPreModel τ
          (HenkinModel.denote M (HOL.subst θ.unop source) valuation.1)
          (HenkinModel.denote M (HOL.subst θ.unop target) valuation.1) ↔
        PreModel.Eqv M.toPreModel τ
          (HenkinModel.denote M source (Soundness.substVal M θ.unop valuation.1))
          (HenkinModel.denote M target (Soundness.substVal M θ.unop valuation.1))
      rw [Soundness.denote_subst, Soundness.denote_subst]

/-- **The contextual trinity of the HOL kernel.** Elaboration followed by
soundness is the direct denotational reading of an execution. -/
def comparison (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv) :
    Comparison.{u, max u v, max (u + 1) v w} (SubstContext Base Const) where
  program := programFace Base Const
  logic := logicFace Base Const
  space := spaceFace M
  programToLogic := elaborate Base Const
  logicToSpace := soundness M respects
  programToSpace := meaning M respects
  coherence := by
    ext context ⟨execution⟩
    apply congrArg ULift.up
    ext valuation
    · exact ⟨fun _ => trivial, fun _ _ member => nomatch member⟩
    · rfl

/-- The explicit-conversion intensional face loses nothing operational:
elaboration is injective at every context. -/
theorem elaborate_injective (context : (SubstContext Base Const)ᵒᵖ) :
    Function.Injective ((elaborate Base Const).app context) := by
  rintro ⟨τ₁, source₁, target₁, first⟩ ⟨τ₂, source₂, target₂, second⟩ same
  have packed := congrArg ULift.down same
  obtain ⟨sequents, _⟩ := Sigma.mk.inj_iff.mp packed
  obtain ⟨_, conclusions⟩ := Prod.mk.inj sequents
  obtain ⟨types, sources, _⟩ := Term.eq.inj conclusions
  subst types
  cases eq_of_heq sources
  obtain ⟨targets, runs⟩ := Execution.proof_packed_injective first second packed
  subst targets
  cases eq_of_heq runs
  rfl

/-! ## Fragments transported by both maps -/

/-- The number of steps of an execution. -/
def Execution.length {Γ : Ctx Base} {τ : Ty Base} :
    {source target : Term Const Γ τ} → Execution source target → Nat
  | _, _, .done _ => 0
  | _, _, .step _ rest => rest.length + 1

theorem Execution.length_subst {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') {τ : Ty Base}
    {source target : Term Const Γ τ} (execution : Execution source target) :
    (execution.subst θ).length = execution.length := by
  induction execution with
  | done => rfl
  | step _ _ ih => simp only [Execution.subst, Execution.length, ih]

/-- Executions that perform at least one step. -/
def running : Constraint (programFace Base Const) where
  holds _ execution := 0 < execution.down.2.2.2.length
  map_closed θ := by
    rintro ⟨⟨τ, source, target, run⟩⟩ positive
    change 0 < (run.subst θ.unop).length
    rw [Execution.length_subst]
    exact positive

/-- Hypothesis-free proofs. Substitution keeps the empty hypothesis list. -/
def closedProofs : Constraint (logicFace Base Const) where
  holds _ proved := proved.down.1.1 = []
  map_closed θ := by
    rintro ⟨⟨⟨hypotheses, conclusion⟩, proof⟩⟩ closed
    change hypotheses = [] at closed
    subst closed
    rfl

/-- Unconditional semantic sequents: the hypothesis predicate holds at every
admissible valuation. -/
def unconditional (M : HenkinModel.{u, v, w} Base Const) : Constraint (spaceFace M) where
  holds _ sequent := ∀ valuation, sequent.down.hypotheses valuation
  map_closed _ := fun holds _ => holds _

/-- Running executions elaborate to hypothesis-free proofs, whose meanings are
unconditional. -/
def closedFragment (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv) :
    ComputationalTrinity.FragmentwiseComparison (comparison M respects) where
  programFragment := running
  logicFragment := closedProofs
  spaceFragment := unconditional M
  programLogicCompatible := by
    rintro _ _ ⟨⟨⟨τ, source, target, run⟩⟩, _, rfl⟩
    rfl
  logicSpaceCompatible := by
    rintro _ _ ⟨⟨⟨⟨hypotheses, conclusion⟩, proof⟩⟩, closed, rfl⟩ valuation
    change hypotheses = [] at closed
    subst closed
    exact fun _ member => nomatch member

/-! ## Controls -/

namespace Controls

/-- One base type and no constants. -/
abbrev NoConstant : Ty Unit → Type := fun _ => Empty

abbrev ι : Ty Unit := .base ()

abbrev here : Ctx Unit := [ι]

abbrev x : Term NoConstant here ι := .var .vz

abbrev identity : Term NoConstant here (ι ⇒ ι) := .lam (.var .vz)

abbrev nested : Term NoConstant here ι := .app identity (.app identity x)

/-- Contract the outer redex first. -/
def outerFirst : Execution nested x :=
  .step (.beta (.var .vz) (.app identity x)) (.step (.beta (.var .vz) x) (.done x))

/-- Contract the inner redex first. -/
def innerFirst : Execution nested x :=
  .step (.appArg identity (.beta (.var .vz) x)) (.step (.beta (.var .vz) x) (.done x))

/-- Whether a step contracts a root redex. -/
def atRoot {Γ : Ctx Unit} {τ : Ty Unit} {source target : Term NoConstant Γ τ} :
    BetaStep source target → Bool
  | .beta _ _ => true
  | _ => false

/-- Whether an execution starts with a root redex. -/
def startsAtRoot {Γ : Ctx Unit} {τ : Ty Unit} {source target : Term NoConstant Γ τ} :
    Execution source target → Bool
  | .done _ => false
  | .step first _ => atRoot first

/-- The full standard model over one point. -/
def model : HenkinModel.{0, 0, 0} Unit NoConstant :=
  HenkinModel.standard (fun _ => PUnit) (fun constant => Empty.elim constant)

theorem model_respects : model.FunctionsRespectEqv :=
  HenkinModel.functionsRespectEqv_of_fullDomains _ (HenkinModel.fullDomains_standard _ _)

abbrev trinity := comparison model model_respects

abbrev point : (SubstContext Unit NoConstant)ᵒᵖ := Opposite.op ⟨here⟩

abbrev outerProgram : (trinity.program).obj point := ⟨⟨ι, nested, x, outerFirst⟩⟩
abbrev innerProgram : (trinity.program).obj point := ⟨⟨ι, nested, x, innerFirst⟩⟩

theorem programs_distinct : outerProgram ≠ innerProgram := by
  intro same
  have roots := congrArg (fun program => startsAtRoot program.down.2.2.2) same
  simp [startsAtRoot, atRoot, outerFirst, innerFirst] at roots

/-- The explicit-conversion proofs of the two executions differ. -/
theorem proofs_distinct :
    trinity.programToLogic.app point outerProgram ≠
      trinity.programToLogic.app point innerProgram :=
  fun same => programs_distinct (elaborate_injective.{0, 0, 0} point same)

/-- The two executions have one semantic sequent. -/
theorem same_meaning :
    trinity.programToSpace.app point outerProgram =
      trinity.programToSpace.app point innerProgram := rfl

theorem losesProgramInformation : trinity.LosesProgramInformation :=
  ⟨point, outerProgram, innerProgram, programs_distinct, same_meaning⟩

/-- No natural isomorphism from executions to semantic sequents agrees with
the direct reading. -/
theorem no_exact_programSpace :
    ¬ ∃ isomorphism : trinity.program ≅ trinity.space,
      isomorphism.hom = trinity.programToSpace :=
  trinity.no_programSpace_iso_of_losesProgramInformation losesProgramInformation

abbrev firstOccurrence : (trinity.logic).obj point :=
  ⟨⟨([.top, .top], .top), ProofSyntax.Controls.firstOccurrence .top⟩⟩

abbrev secondOccurrence : (trinity.logic).obj point :=
  ⟨⟨([.top, .top], .top), ProofSyntax.Controls.secondOccurrence .top⟩⟩

theorem occurrences_distinct : firstOccurrence ≠ secondOccurrence := by
  intro same
  exact ProofSyntax.Controls.duplicate_occurrences_distinct _
    (eq_of_heq (Sigma.mk.inj_iff.mp (congrArg ULift.down same)).2)

/-- The extensional face forgets which copy of a repeated hypothesis a proof
uses. -/
theorem logicToSpace_identifies_occurrences :
    trinity.logicToSpace.app point firstOccurrence =
      trinity.logicToSpace.app point secondOccurrence := rfl

/-- Proofs whose root is the first hypothesis occurrence. -/
def firstOccurrenceRoot : Constraint (logicFace.{0, 0, 0} Unit NoConstant) where
  holds _ proved := proved.down.2.rootObservation = ⟨.hyp, some 0⟩
  map_closed θ := by
    rintro ⟨⟨⟨hypotheses, conclusion⟩, proof⟩⟩ holds
    change (ProofSyntax.subst θ.unop proof).rootObservation = _
    rw [ProofSyntax.rootObservation_subst]
    exact holds

/-- **Occurrence identity stays on the presentation.** No requirement on the
extensional face, pulled back to proofs, selects the proofs rooted at the first
hypothesis occurrence. -/
theorem occurrence_not_extensional (requirement : Constraint trinity.space) :
    ¬ firstOccurrenceRoot.Equivalent (requirement.pullback trinity.logicToSpace) :=
  Constraint.not_equivalent_pullback_of_separates_fibre _ _ _
    logicToSpace_identifies_occurrences rfl (by
      change ¬ (ProofSyntax.Controls.secondOccurrence _).rootObservation = _
      rw [(ProofSyntax.Controls.occurrence_observations _).2]
      decide)

end Controls

#print axioms ProofSyntax.subst_id_heq
#print axioms ProofSyntax.subst_comp_heq
#print axioms comparison
#print axioms elaborate_injective
#print axioms closedFragment
#print axioms Controls.losesProgramInformation
#print axioms Controls.no_exact_programSpace
#print axioms Controls.proofs_distinct
#print axioms Controls.occurrences_distinct
#print axioms Controls.logicToSpace_identifies_occurrences
#print axioms Controls.occurrence_not_extensional

end Mettapedia.Logic.HOL.ContextualTrinity
