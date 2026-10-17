import Mettapedia.Logic.HOL.ContextualTrinity

/-!
# Strong normalization and confluence of simply typed beta

The operational face of the HOL kernel contracts beta redexes at every position
of an intrinsically typed term (`ContextualTrinity.BetaStep`). This module proves
the two facts on which normalize-and-compare checking rests.

* **Strong normalization** (`stronglyNormalizing`): every reduction sequence from
  every term is finite. The proof is Tait's method with Kripke-style
  reducibility over renamings (`Red`); renaming reflects steps
  (`reduces_rename_inv`), so reducibility at base type is closed under renaming.
* **Confluence** (`confluent`): two reducts of one term have a common reduct.
  The proof is Takahashi's: parallel reduction (`Par`) lies between one step
  and many steps, and every parallel reduct reduces in parallel to the complete
  development (`Par.triangle`).

Together they give unique normal forms (`normalForm_unique`), and joinability
coincides with equality of normal forms.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.BetaNormalization

open Mettapedia.Logic.HOL.ContextualTrinity

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Steps as a relation -/

/-- One beta step, as a proposition. -/
def Reduces {Γ : Ctx Base} {τ : Ty Base} (source target : Term Const Γ τ) : Prop :=
  Nonempty (BetaStep source target)

/-- Finitely many steps. -/
abbrev ReducesStar {Γ : Ctx Base} {τ : Ty Base} : Term Const Γ τ → Term Const Γ τ → Prop :=
  Relation.ReflTransGen Reduces

/-- Strongly normalizing: no infinite reduction sequence starts at the term. -/
def StronglyNormalizing {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) : Prop :=
  Acc (fun later earlier => Reduces earlier later) term

/-- A term that is not an abstraction. -/
def Neutral {Γ : Ctx Base} {τ : Ty Base} : Term Const Γ τ → Prop
  | .lam _ => False
  | _ => True

section Inversion

variable {Γ : Ctx Base}

theorem var_irreducible {τ : Ty Base} (index : Var Γ τ) (target : Term Const Γ τ) :
    ¬ Reduces (.var index) target := fun ⟨step⟩ => by cases step

theorem const_irreducible {τ : Ty Base} (constant : Const τ) (target : Term Const Γ τ) :
    ¬ Reduces (.const constant) target := fun ⟨step⟩ => by cases step

theorem top_irreducible (target : Formula Const Γ) : ¬ Reduces .top target :=
  fun ⟨step⟩ => by cases step

theorem bot_irreducible (target : Formula Const Γ) : ¬ Reduces .bot target :=
  fun ⟨step⟩ => by cases step

theorem app_cases {σ τ : Ty Base} {function : Term Const Γ (σ ⇒ τ)} {argument : Term Const Γ σ}
    {target : Term Const Γ τ} (reduces : Reduces (.app function argument) target) :
    (∃ body, function = .lam body ∧ target = instantiate argument body) ∨
      (∃ function', Reduces function function' ∧ target = .app function' argument) ∨
      (∃ argument', Reduces argument argument' ∧ target = .app function argument') := by
  obtain ⟨step⟩ := reduces
  cases step with
  | beta body _ => exact .inl ⟨body, rfl, rfl⟩
  | appFun _ inner => exact .inr (.inl ⟨_, ⟨inner⟩, rfl⟩)
  | appArg _ inner => exact .inr (.inr ⟨_, ⟨inner⟩, rfl⟩)

theorem lam_cases {σ τ : Ty Base} {body : Term Const (σ :: Γ) τ} {target : Term Const Γ (σ ⇒ τ)}
    (reduces : Reduces (.lam body) target) : ∃ body', Reduces body body' ∧ target = .lam body' := by
  obtain ⟨step⟩ := reduces
  cases step with
  | lam inner => exact ⟨_, ⟨inner⟩, rfl⟩

theorem and_cases {left right target : Formula Const Γ} (reduces : Reduces (.and left right) target) :
    (∃ left', Reduces left left' ∧ target = .and left' right) ∨
      (∃ right', Reduces right right' ∧ target = .and left right') := by
  obtain ⟨step⟩ := reduces
  cases step with
  | andLeft _ inner => exact .inl ⟨_, ⟨inner⟩, rfl⟩
  | andRight _ inner => exact .inr ⟨_, ⟨inner⟩, rfl⟩

theorem or_cases {left right target : Formula Const Γ} (reduces : Reduces (.or left right) target) :
    (∃ left', Reduces left left' ∧ target = .or left' right) ∨
      (∃ right', Reduces right right' ∧ target = .or left right') := by
  obtain ⟨step⟩ := reduces
  cases step with
  | orLeft _ inner => exact .inl ⟨_, ⟨inner⟩, rfl⟩
  | orRight _ inner => exact .inr ⟨_, ⟨inner⟩, rfl⟩

theorem imp_cases {left right target : Formula Const Γ} (reduces : Reduces (.imp left right) target) :
    (∃ left', Reduces left left' ∧ target = .imp left' right) ∨
      (∃ right', Reduces right right' ∧ target = .imp left right') := by
  obtain ⟨step⟩ := reduces
  cases step with
  | impLeft _ inner => exact .inl ⟨_, ⟨inner⟩, rfl⟩
  | impRight _ inner => exact .inr ⟨_, ⟨inner⟩, rfl⟩

theorem eq_cases {τ : Ty Base} {left right : Term Const Γ τ} {target : Formula Const Γ}
    (reduces : Reduces (.eq left right) target) :
    (∃ left', Reduces left left' ∧ target = .eq left' right) ∨
      (∃ right', Reduces right right' ∧ target = .eq left right') := by
  obtain ⟨step⟩ := reduces
  cases step with
  | eqLeft _ inner => exact .inl ⟨_, ⟨inner⟩, rfl⟩
  | eqRight _ inner => exact .inr ⟨_, ⟨inner⟩, rfl⟩

theorem not_cases {operand target : Formula Const Γ} (reduces : Reduces (.not operand) target) :
    ∃ operand', Reduces operand operand' ∧ target = .not operand' := by
  obtain ⟨step⟩ := reduces
  cases step with
  | not inner => exact ⟨_, ⟨inner⟩, rfl⟩

theorem all_cases {σ : Ty Base} {body : Formula Const (σ :: Γ)} {target : Formula Const Γ}
    (reduces : Reduces (.all body) target) : ∃ body', Reduces body body' ∧ target = .all body' := by
  obtain ⟨step⟩ := reduces
  cases step with
  | all inner => exact ⟨_, ⟨inner⟩, rfl⟩

theorem ex_cases {σ : Ty Base} {body : Formula Const (σ :: Γ)} {target : Formula Const Γ}
    (reduces : Reduces (.ex body) target) : ∃ body', Reduces body body' ∧ target = .ex body' := by
  obtain ⟨step⟩ := reduces
  cases step with
  | ex inner => exact ⟨_, ⟨inner⟩, rfl⟩

end Inversion

/-! ## Substitution and renaming move steps -/

theorem reduces_subst {Γ Δ : Ctx Base} (θ : Subst Const Γ Δ) {τ : Ty Base}
    {source target : Term Const Γ τ} (reduces : Reduces source target) :
    Reduces (HOL.subst θ source) (HOL.subst θ target) :=
  let ⟨step⟩ := reduces
  ⟨step.subst θ⟩

theorem reduces_rename {Γ Δ : Ctx Base} (ρ : Rename Base Γ Δ) {τ : Ty Base}
    {source target : Term Const Γ τ} (reduces : Reduces source target) :
    Reduces (rename ρ source) (rename ρ target) := by
  have moved := reduces_subst (Subst.ofRename (Const := Const) ρ) reduces
  simpa using moved

/-- **Renaming reflects steps.** Every step of a renamed term is the renaming
of a step of the term. -/
theorem reduces_rename_inv {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) :
    ∀ {Δ : Ctx Base} (ρ : Rename Base Γ Δ) {target : Term Const Δ τ},
      Reduces (rename ρ term) target →
        ∃ target', Reduces term target' ∧ target = rename ρ target' := by
  induction term with
  | var index => intro Δ ρ target reduces; exact absurd reduces (var_irreducible _ _)
  | const constant => intro Δ ρ target reduces; exact absurd reduces (const_irreducible _ _)
  | top => intro Δ ρ target reduces; exact absurd reduces (top_irreducible _)
  | bot => intro Δ ρ target reduces; exact absurd reduces (bot_irreducible _)
  | app function argument functionIh argumentIh =>
      intro Δ ρ target reduces
      rcases app_cases reduces with ⟨body, isLam, rfl⟩ | ⟨function', inner, rfl⟩ |
          ⟨argument', inner, rfl⟩
      · cases function with
        | lam body₀ =>
            simp only [rename, Term.lam.injEq] at isLam
            subst isLam
            exact ⟨instantiate argument body₀, ⟨.beta body₀ argument⟩,
              (ExtDerivation.rename_instantiate ρ argument body₀).symm⟩
        | _ => simp [rename] at isLam
      · obtain ⟨function₀, step, rfl⟩ := functionIh ρ inner
        exact ⟨.app function₀ argument, let ⟨s⟩ := step; ⟨.appFun argument s⟩, rfl⟩
      · obtain ⟨argument₀, step, rfl⟩ := argumentIh ρ inner
        exact ⟨.app function argument₀, let ⟨s⟩ := step; ⟨.appArg function s⟩, rfl⟩
  | lam body ih =>
      intro Δ ρ target reduces
      obtain ⟨body', inner, rfl⟩ := lam_cases reduces
      obtain ⟨body₀, step, rfl⟩ := ih (Rename.lift ρ) inner
      exact ⟨.lam body₀, let ⟨s⟩ := step; ⟨.lam s⟩, rfl⟩
  | and left right leftIh rightIh =>
      intro Δ ρ target reduces
      rcases and_cases reduces with ⟨left', inner, rfl⟩ | ⟨right', inner, rfl⟩
      · obtain ⟨left₀, step, rfl⟩ := leftIh ρ inner
        exact ⟨.and left₀ right, let ⟨s⟩ := step; ⟨.andLeft right s⟩, rfl⟩
      · obtain ⟨right₀, step, rfl⟩ := rightIh ρ inner
        exact ⟨.and left right₀, let ⟨s⟩ := step; ⟨.andRight left s⟩, rfl⟩
  | or left right leftIh rightIh =>
      intro Δ ρ target reduces
      rcases or_cases reduces with ⟨left', inner, rfl⟩ | ⟨right', inner, rfl⟩
      · obtain ⟨left₀, step, rfl⟩ := leftIh ρ inner
        exact ⟨.or left₀ right, let ⟨s⟩ := step; ⟨.orLeft right s⟩, rfl⟩
      · obtain ⟨right₀, step, rfl⟩ := rightIh ρ inner
        exact ⟨.or left right₀, let ⟨s⟩ := step; ⟨.orRight left s⟩, rfl⟩
  | imp left right leftIh rightIh =>
      intro Δ ρ target reduces
      rcases imp_cases reduces with ⟨left', inner, rfl⟩ | ⟨right', inner, rfl⟩
      · obtain ⟨left₀, step, rfl⟩ := leftIh ρ inner
        exact ⟨.imp left₀ right, let ⟨s⟩ := step; ⟨.impLeft right s⟩, rfl⟩
      · obtain ⟨right₀, step, rfl⟩ := rightIh ρ inner
        exact ⟨.imp left right₀, let ⟨s⟩ := step; ⟨.impRight left s⟩, rfl⟩
  | eq left right leftIh rightIh =>
      intro Δ ρ target reduces
      rcases eq_cases reduces with ⟨left', inner, rfl⟩ | ⟨right', inner, rfl⟩
      · obtain ⟨left₀, step, rfl⟩ := leftIh ρ inner
        exact ⟨.eq left₀ right, let ⟨s⟩ := step; ⟨.eqLeft right s⟩, rfl⟩
      · obtain ⟨right₀, step, rfl⟩ := rightIh ρ inner
        exact ⟨.eq left right₀, let ⟨s⟩ := step; ⟨.eqRight left s⟩, rfl⟩
  | not operand ih =>
      intro Δ ρ target reduces
      obtain ⟨operand', inner, rfl⟩ := not_cases reduces
      obtain ⟨operand₀, step, rfl⟩ := ih ρ inner
      exact ⟨.not operand₀, let ⟨s⟩ := step; ⟨.not s⟩, rfl⟩
  | all body ih =>
      intro Δ ρ target reduces
      obtain ⟨body', inner, rfl⟩ := all_cases reduces
      obtain ⟨body₀, step, rfl⟩ := ih (Rename.lift ρ) inner
      exact ⟨.all body₀, let ⟨s⟩ := step; ⟨.all s⟩, rfl⟩
  | ex body ih =>
      intro Δ ρ target reduces
      obtain ⟨body', inner, rfl⟩ := ex_cases reduces
      obtain ⟨body₀, step, rfl⟩ := ih (Rename.lift ρ) inner
      exact ⟨.ex body₀, let ⟨s⟩ := step; ⟨.ex s⟩, rfl⟩

/-! ## Many steps -/

section Star

variable {Γ : Ctx Base}

theorem star_map {Γ' : Ctx Base} {σ τ : Ty Base} (f : Term Const Γ σ → Term Const Γ' τ)
    (moves : ∀ {a b : Term Const Γ σ}, Reduces a b → Reduces (f a) (f b))
    {a b : Term Const Γ σ} (many : ReducesStar a b) : ReducesStar (f a) (f b) :=
  many.lift f (fun _ _ step => moves step)

theorem star_two {σ₁ σ₂ τ : Ty Base} (f : Term Const Γ σ₁ → Term Const Γ σ₂ → Term Const Γ τ)
    (movesLeft : ∀ {a a' : Term Const Γ σ₁} (b : Term Const Γ σ₂), Reduces a a' →
      Reduces (f a b) (f a' b))
    (movesRight : ∀ (a : Term Const Γ σ₁) {b b' : Term Const Γ σ₂}, Reduces b b' →
      Reduces (f a b) (f a b'))
    {a a' : Term Const Γ σ₁} {b b' : Term Const Γ σ₂} (left : ReducesStar a a')
    (right : ReducesStar b b') : ReducesStar (f a b) (f a' b') :=
  (star_map (fun a => f a b) (fun step => movesLeft b step) left).trans
    (star_map (f a') (fun step => movesRight a' step) right)

theorem star_rename {Δ : Ctx Base} (ρ : Rename Base Γ Δ) {τ : Ty Base} {a b : Term Const Γ τ}
    (many : ReducesStar a b) : ReducesStar (rename ρ a) (rename ρ b) :=
  star_map (rename ρ) (reduces_rename ρ) many

theorem star_subst {Δ : Ctx Base} (θ : Subst Const Γ Δ) {τ : Ty Base} {a b : Term Const Γ τ}
    (many : ReducesStar a b) : ReducesStar (HOL.subst θ a) (HOL.subst θ b) :=
  star_map (HOL.subst θ) (reduces_subst θ) many

/-- Substituting pointwise reducing terms reduces. -/
theorem star_subst_pointwise {τ : Ty Base} (term : Term Const Γ τ) :
    ∀ {Δ : Ctx Base} {θ θ' : Subst Const Γ Δ},
      (∀ {σ : Ty Base} (index : Var Γ σ), ReducesStar (θ index) (θ' index)) →
        ReducesStar (HOL.subst θ term) (HOL.subst θ' term) := by
  have lifted : ∀ {Γ Δ : Ctx Base} {ρ : Ty Base} {θ θ' : Subst Const Γ Δ},
      (∀ {σ : Ty Base} (index : Var Γ σ), ReducesStar (θ index) (θ' index)) →
        ∀ {σ : Ty Base} (index : Var (ρ :: Γ) σ),
          ReducesStar (Subst.lift θ index) (Subst.lift θ' index) := by
    intro Γ Δ ρ θ θ' pointwise σ index
    cases index with
    | vz => exact .refl
    | vs index => exact star_rename _ (pointwise index)
  induction term with
  | var index => intro Δ θ θ' pointwise; exact pointwise index
  | const => intro Δ θ θ' _; exact .refl
  | top => intro Δ θ θ' _; exact .refl
  | bot => intro Δ θ θ' _; exact .refl
  | app function argument functionIh argumentIh =>
      intro Δ θ θ' pointwise
      exact star_two Term.app (fun b ⟨s⟩ => ⟨.appFun b s⟩) (fun a _ _ ⟨s⟩ => ⟨.appArg a s⟩)
        (functionIh pointwise) (argumentIh pointwise)
  | lam body ih =>
      intro Δ θ θ' pointwise
      exact star_map Term.lam (fun ⟨s⟩ => ⟨.lam s⟩) (ih (lifted pointwise))
  | and left right leftIh rightIh =>
      intro Δ θ θ' pointwise
      exact star_two Term.and (fun b ⟨s⟩ => ⟨.andLeft b s⟩) (fun a _ _ ⟨s⟩ => ⟨.andRight a s⟩)
        (leftIh pointwise) (rightIh pointwise)
  | or left right leftIh rightIh =>
      intro Δ θ θ' pointwise
      exact star_two Term.or (fun b ⟨s⟩ => ⟨.orLeft b s⟩) (fun a _ _ ⟨s⟩ => ⟨.orRight a s⟩)
        (leftIh pointwise) (rightIh pointwise)
  | imp left right leftIh rightIh =>
      intro Δ θ θ' pointwise
      exact star_two Term.imp (fun b ⟨s⟩ => ⟨.impLeft b s⟩) (fun a _ _ ⟨s⟩ => ⟨.impRight a s⟩)
        (leftIh pointwise) (rightIh pointwise)
  | eq left right leftIh rightIh =>
      intro Δ θ θ' pointwise
      exact star_two Term.eq (fun b ⟨s⟩ => ⟨.eqLeft b s⟩) (fun a _ _ ⟨s⟩ => ⟨.eqRight a s⟩)
        (leftIh pointwise) (rightIh pointwise)
  | not operand ih =>
      intro Δ θ θ' pointwise
      exact star_map Term.not (fun ⟨s⟩ => ⟨.not s⟩) (ih pointwise)
  | all body ih =>
      intro Δ θ θ' pointwise
      exact star_map Term.all (fun ⟨s⟩ => ⟨.all s⟩) (ih (lifted pointwise))
  | ex body ih =>
      intro Δ θ θ' pointwise
      exact star_map Term.ex (fun ⟨s⟩ => ⟨.ex s⟩) (ih (lifted pointwise))

theorem star_instantiate {σ τ : Ty Base} {argument argument' : Term Const Γ σ}
    (many : ReducesStar argument argument') (body : Term Const (σ :: Γ) τ) :
    ReducesStar (instantiate argument body) (instantiate argument' body) :=
  star_subst_pointwise body (fun index => by
    cases index with
    | vz => exact many
    | vs index => exact .refl)

end Star

/-! ## Strong normalization -/

section StrongNormalization

variable {Γ : Ctx Base}

theorem sn_step {τ : Ty Base} {term term' : Term Const Γ τ} (sn : StronglyNormalizing term)
    (reduces : Reduces term term') : StronglyNormalizing term' :=
  sn.inv reduces

theorem sn_star {τ : Ty Base} {term term' : Term Const Γ τ} (sn : StronglyNormalizing term)
    (many : ReducesStar term term') : StronglyNormalizing term' := by
  induction many with
  | refl => exact sn
  | tail _ step ih => exact sn_step ih step

/-- Strong normalization pulls back along a map that moves every step. -/
theorem sn_of_map {Γ' : Ctx Base} {σ τ : Ty Base} (f : Term Const Γ σ → Term Const Γ' τ)
    (moves : ∀ {a b : Term Const Γ σ}, Reduces a b → Reduces (f a) (f b))
    {term : Term Const Γ σ} (sn : StronglyNormalizing (f term)) : StronglyNormalizing term := by
  generalize mapped : f term = image at sn
  induction sn generalizing term with
  | intro image _ ih =>
      subst mapped
      exact ⟨_, fun later step => ih _ (moves step) rfl⟩

/-- A term built by a binary constructor is strongly normalizing when its parts
are and every step happens in a part. -/
theorem sn_two {σ₁ σ₂ τ : Ty Base} (f : Term Const Γ σ₁ → Term Const Γ σ₂ → Term Const Γ τ)
    (cases : ∀ {a : Term Const Γ σ₁} {b : Term Const Γ σ₂} {target : Term Const Γ τ},
      Reduces (f a b) target →
        (∃ a', Reduces a a' ∧ target = f a' b) ∨ (∃ b', Reduces b b' ∧ target = f a b'))
    {a : Term Const Γ σ₁} {b : Term Const Γ σ₂} (snA : StronglyNormalizing a)
    (snB : StronglyNormalizing b) : StronglyNormalizing (f a b) := by
  induction snA generalizing b with
  | intro a _ ihA =>
      induction snB with
      | intro b accB ihB =>
          refine ⟨_, fun target reduces => ?_⟩
          rcases cases reduces with ⟨a', step, rfl⟩ | ⟨b', step, rfl⟩
          · exact ihA a' step ⟨b, accB⟩
          · exact ihB b' step

theorem sn_one {σ τ : Ty Base} {Γ' : Ctx Base} (f : Term Const Γ' σ → Term Const Γ τ)
    (cases : ∀ {a : Term Const Γ' σ} {target : Term Const Γ τ},
      Reduces (f a) target → ∃ a', Reduces a a' ∧ target = f a')
    {a : Term Const Γ' σ} (snA : StronglyNormalizing a) : StronglyNormalizing (f a) := by
  induction snA with
  | intro a _ ih =>
      refine ⟨_, fun target reduces => ?_⟩
      obtain ⟨a', step, rfl⟩ := cases reduces
      exact ih a' step

theorem sn_irreducible {τ : Ty Base} {term : Term Const Γ τ}
    (irreducible : ∀ target, ¬ Reduces term target) : StronglyNormalizing term :=
  ⟨_, fun target reduces => absurd reduces (irreducible target)⟩

theorem sn_rename {Δ : Ctx Base} (ρ : Rename Base Γ Δ) {τ : Ty Base} {term : Term Const Γ τ}
    (sn : StronglyNormalizing term) : StronglyNormalizing (rename ρ term) := by
  induction sn with
  | intro term _ ih =>
      refine ⟨_, fun target reduces => ?_⟩
      obtain ⟨term', step, rfl⟩ := reduces_rename_inv term ρ reduces
      exact ih term' step

end StrongNormalization

/-- Reducibility: strong normalization at the proposition and base types, and
at an arrow type, reducible results on reducible arguments in every renamed
context. -/
def Red : (τ : Ty Base) → {Γ : Ctx Base} → Term Const Γ τ → Prop
  | .prop, _, term => StronglyNormalizing term
  | .base _, _, term => StronglyNormalizing term
  | .arr σ τ, Γ, term => ∀ (Δ : Ctx Base) (ρ : Rename Base Γ Δ) (argument : Term Const Δ σ),
      Red σ argument → Red τ (.app (rename ρ term) argument)

theorem neutral_rename {Γ Δ : Ctx Base} (ρ : Rename Base Γ Δ) {τ : Ty Base}
    {term : Term Const Γ τ} (neutral : Neutral term) : Neutral (rename ρ term) := by
  cases term <;> simp_all [Neutral, rename]

/-- The three properties of reducibility candidates, by induction on the
type. -/
theorem candidates (τ : Ty Base) :
    (∀ {Γ : Ctx Base} {term : Term Const Γ τ}, Red τ term → StronglyNormalizing term) ∧
    (∀ {Γ : Ctx Base} {term term' : Term Const Γ τ}, Red τ term → Reduces term term' →
      Red τ term') ∧
    (∀ {Γ : Ctx Base} {term : Term Const Γ τ}, Neutral term →
      (∀ term', Reduces term term' → Red τ term') → Red τ term) := by
  induction τ with
  | prop =>
      exact ⟨fun red => red, fun red step => sn_step red step,
        fun _ reducts => ⟨_, fun target step => reducts target step⟩⟩
  | base b =>
      exact ⟨fun red => red, fun red step => sn_step red step,
        fun _ reducts => ⟨_, fun target step => reducts target step⟩⟩
  | arr σ τ σIh τIh =>
      obtain ⟨σ₁, σ₂, σ₃⟩ := σIh
      obtain ⟨τ₁, τ₂, τ₃⟩ := τIh
      have variable_red : ∀ {Γ : Ctx Base} (index : Var Γ σ), Red σ (.var (Const := Const) index) :=
        fun index => σ₃ trivial (fun target step => absurd step (var_irreducible index target))
      refine ⟨?_, ?_, ?_⟩
      · intro Γ term red
        have applied := τ₁ (red (σ :: Γ) Rename.weaken (.var .vz) (variable_red _))
        have functionSN := sn_of_map (fun function => Term.app function (.var .vz))
          (fun ⟨s⟩ => ⟨.appFun _ s⟩) applied
        exact sn_of_map (rename Rename.weaken) (reduces_rename _) functionSN
      · intro Γ term term' red step Δ ρ argument argumentRed
        exact τ₂ (red Δ ρ argument argumentRed)
          (let ⟨s⟩ := reduces_rename ρ step; ⟨.appFun argument s⟩)
      · intro Γ term neutral reducts Δ ρ argument argumentRed
        have argumentSN := σ₁ argumentRed
        induction argumentSN with
        | intro argument _ ih =>
            refine τ₃ trivial (fun target reduces => ?_)
            rcases app_cases reduces with ⟨body, isLam, rfl⟩ | ⟨function', inner, rfl⟩ |
                ⟨argument', inner, rfl⟩
            · have renamed := neutral_rename ρ neutral
              rw [isLam] at renamed
              exact renamed.elim
            · obtain ⟨term', step, rfl⟩ := reduces_rename_inv term ρ inner
              exact reducts term' step Δ ρ argument argumentRed
            · exact ih argument' inner (σ₂ argumentRed inner)

theorem red_sn {τ : Ty Base} {Γ : Ctx Base} {term : Term Const Γ τ} (red : Red τ term) :
    StronglyNormalizing term :=
  (candidates τ).1 red

theorem red_step {τ : Ty Base} {Γ : Ctx Base} {term term' : Term Const Γ τ} (red : Red τ term)
    (step : Reduces term term') : Red τ term' :=
  (candidates τ).2.1 red step

theorem red_star {τ : Ty Base} {Γ : Ctx Base} {term term' : Term Const Γ τ} (red : Red τ term)
    (many : ReducesStar term term') : Red τ term' := by
  induction many with
  | refl => exact red
  | tail _ step ih => exact red_step ih step

theorem red_neutral {τ : Ty Base} {Γ : Ctx Base} {term : Term Const Γ τ} (neutral : Neutral term)
    (reducts : ∀ term', Reduces term term' → Red τ term') : Red τ term :=
  (candidates τ).2.2 neutral reducts

theorem red_var {τ : Ty Base} {Γ : Ctx Base} (index : Var Γ τ) :
    Red τ (.var (Const := Const) index) :=
  red_neutral trivial (fun target step => absurd step (var_irreducible index target))

/-- Reducibility is closed under renaming. -/
theorem red_rename (τ : Ty Base) :
    ∀ {Γ Δ : Ctx Base} (ρ : Rename Base Γ Δ) {term : Term Const Γ τ}, Red τ term →
      Red τ (rename ρ term) := by
  cases τ with
  | prop => exact fun ρ _ red => sn_rename ρ red
  | base _ => exact fun ρ _ red => sn_rename ρ red
  | arr σ τ =>
      intro Γ Δ ρ term red Ξ ρ' argument argumentRed
      have applied := red Ξ (fun index => ρ' (ρ index)) argument argumentRed
      rwa [← rename_comp] at applied

/-- **Weak head expansion.** A beta redex is reducible when its argument is
strongly normalizing and its contractum is reducible. -/
theorem red_expand {σ τ : Ty Base} {Γ : Ctx Base} {argument : Term Const Γ σ}
    (argumentSN : StronglyNormalizing argument) :
    ∀ {body : Term Const (σ :: Γ) τ}, Red τ (instantiate argument body) →
      Red τ (.app (.lam body) argument) := by
  induction argumentSN with
  | intro argument _ argumentIh =>
      intro body red
      have bodySN : StronglyNormalizing body :=
        sn_of_map (instantiate argument) (fun step => reduces_subst _ step) (red_sn red)
      induction bodySN with
      | intro body _ bodyIh =>
          refine red_neutral trivial (fun target reduces => ?_)
          rcases app_cases reduces with ⟨body', isLam, rfl⟩ | ⟨function', inner, rfl⟩ |
              ⟨argument', inner, rfl⟩
          · cases isLam
            exact red
          · obtain ⟨body', step, rfl⟩ := lam_cases inner
            exact bodyIh body' step (red_step red (reduces_subst _ step))
          · exact argumentIh argument' inner
              (red_star red (star_instantiate (.single inner) body))

/-- Extend a substitution by a term for a new outermost variable. -/
def extend {Γ Δ : Ctx Base} {σ : Ty Base} (argument : Term Const Δ σ) (θ : Subst Const Γ Δ) :
    Subst Const (σ :: Γ) Δ
  | _, .vz => argument
  | _, .vs index => θ index

theorem instantiate_rename_subst_lift {Γ Δ Ξ : Ctx Base} {σ τ : Ty Base}
    (θ : Subst Const Γ Δ) (ρ : Rename Base Δ Ξ) (argument : Term Const Ξ σ)
    (body : Term Const (σ :: Γ) τ) :
    instantiate argument (rename (Rename.lift ρ) (HOL.subst (Subst.lift θ) body)) =
      HOL.subst (extend argument (fun index => rename ρ (θ index))) body := by
  unfold instantiate
  rw [rename_subst, subst_comp]
  apply subst_ext
  intro _ index
  cases index with
  | vz => rfl
  | vs index =>
      change HOL.subst (Subst.single argument)
          (rename (Rename.lift ρ) (rename Rename.weaken (θ index))) = rename ρ (θ index)
      rw [rename_lift_weaken]
      exact instantiate_weaken argument _

/-- **The fundamental lemma.** Substituting reducible terms into any term gives
a reducible term. -/
theorem red_subst {τ : Ty Base} {Γ : Ctx Base} (term : Term Const Γ τ) :
    ∀ {Δ : Ctx Base} (θ : Subst Const Γ Δ),
      (∀ {σ : Ty Base} (index : Var Γ σ), Red σ (θ index)) → Red τ (HOL.subst θ term) := by
  have liftRed : ∀ {Γ Δ : Ctx Base} {ρ : Ty Base} (θ : Subst Const Γ Δ),
      (∀ {σ : Ty Base} (index : Var Γ σ), Red σ (θ index)) →
        ∀ {σ : Ty Base} (index : Var (ρ :: Γ) σ), Red σ (Subst.lift θ index) := by
    intro Γ Δ ρ θ reds σ index
    cases index with
    | vz => exact red_var _
    | vs index => exact red_rename _ _ (reds index)
  induction term with
  | var index => intro Δ θ reds; exact reds index
  | const constant =>
      intro Δ θ _
      exact red_neutral trivial (fun target step => absurd step (const_irreducible _ _))
  | top => intro Δ θ _; exact sn_irreducible (top_irreducible)
  | bot => intro Δ θ _; exact sn_irreducible (bot_irreducible)
  | app function argument functionIh argumentIh =>
      intro Δ θ reds
      have applied := functionIh θ reds Δ Rename.id _ (argumentIh θ reds)
      rwa [rename_id] at applied
  | lam body ih =>
      intro Δ θ reds Ξ ρ argument argumentRed
      refine red_expand (red_sn argumentRed) ?_
      rw [instantiate_rename_subst_lift]
      refine ih _ (fun index => ?_)
      cases index with
      | vz => exact argumentRed
      | vs index => exact red_rename _ _ (reds index)
  | and left right leftIh rightIh =>
      intro Δ θ reds
      exact sn_two Term.and and_cases (leftIh θ reds) (rightIh θ reds)
  | or left right leftIh rightIh =>
      intro Δ θ reds
      exact sn_two Term.or or_cases (leftIh θ reds) (rightIh θ reds)
  | imp left right leftIh rightIh =>
      intro Δ θ reds
      exact sn_two Term.imp imp_cases (leftIh θ reds) (rightIh θ reds)
  | eq left right leftIh rightIh =>
      intro Δ θ reds
      exact sn_two Term.eq eq_cases (red_sn (leftIh θ reds)) (red_sn (rightIh θ reds))
  | not operand ih =>
      intro Δ θ reds
      exact sn_one Term.not not_cases (ih θ reds)
  | all body ih =>
      intro Δ θ reds
      exact sn_one Term.all all_cases (ih _ (liftRed θ reds))
  | ex body ih =>
      intro Δ θ reds
      exact sn_one Term.ex ex_cases (ih _ (liftRed θ reds))

/-- **Strong normalization of simply typed beta.** -/
theorem stronglyNormalizing {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) :
    StronglyNormalizing term := by
  have red := red_subst term Subst.id (fun index => red_var index)
  rw [subst_id] at red
  exact red_sn red

/-! ## Confluence -/

/-- Parallel reduction: contract any set of redexes present in the term at once. -/
inductive Par : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Term Const Γ τ → Prop where
  | var {Γ : Ctx Base} {τ : Ty Base} (index : Var Γ τ) : Par (.var index) (.var index)
  | const {Γ : Ctx Base} {τ : Ty Base} (constant : Const τ) :
      Par (Γ := Γ) (.const constant) (.const constant)
  | top {Γ : Ctx Base} : Par (Γ := Γ) .top .top
  | bot {Γ : Ctx Base} : Par (Γ := Γ) .bot .bot
  | app {Γ : Ctx Base} {σ τ : Ty Base} {function function' : Term Const Γ (σ ⇒ τ)}
      {argument argument' : Term Const Γ σ} :
      Par function function' → Par argument argument' →
        Par (.app function argument) (.app function' argument')
  | lam {Γ : Ctx Base} {σ τ : Ty Base} {body body' : Term Const (σ :: Γ) τ} :
      Par body body' → Par (.lam body) (.lam body')
  | beta {Γ : Ctx Base} {σ τ : Ty Base} {body body' : Term Const (σ :: Γ) τ}
      {argument argument' : Term Const Γ σ} :
      Par body body' → Par argument argument' →
        Par (.app (.lam body) argument) (instantiate argument' body')
  | and {Γ : Ctx Base} {left left' right right' : Formula Const Γ} :
      Par left left' → Par right right' → Par (.and left right) (.and left' right')
  | or {Γ : Ctx Base} {left left' right right' : Formula Const Γ} :
      Par left left' → Par right right' → Par (.or left right) (.or left' right')
  | imp {Γ : Ctx Base} {left left' right right' : Formula Const Γ} :
      Par left left' → Par right right' → Par (.imp left right) (.imp left' right')
  | eq {Γ : Ctx Base} {τ : Ty Base} {left left' right right' : Term Const Γ τ} :
      Par left left' → Par right right' → Par (.eq left right) (.eq left' right')
  | not {Γ : Ctx Base} {operand operand' : Formula Const Γ} :
      Par operand operand' → Par (.not operand) (.not operand')
  | all {Γ : Ctx Base} {σ : Ty Base} {body body' : Formula Const (σ :: Γ)} :
      Par body body' → Par (.all body) (.all body')
  | ex {Γ : Ctx Base} {σ : Ty Base} {body body' : Formula Const (σ :: Γ)} :
      Par body body' → Par (.ex body) (.ex body')

namespace Par

theorem refl {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) : Par term term := by
  induction term with
  | var index => exact .var index
  | const constant => exact .const constant
  | top => exact .top
  | bot => exact .bot
  | app _ _ functionIh argumentIh => exact .app functionIh argumentIh
  | lam _ ih => exact .lam ih
  | and _ _ leftIh rightIh => exact .and leftIh rightIh
  | or _ _ leftIh rightIh => exact .or leftIh rightIh
  | imp _ _ leftIh rightIh => exact .imp leftIh rightIh
  | eq _ _ leftIh rightIh => exact .eq leftIh rightIh
  | not _ ih => exact .not ih
  | all _ ih => exact .all ih
  | ex _ ih => exact .ex ih

theorem of_step {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (step : BetaStep source target) : Par source target := by
  induction step with
  | beta body argument => exact .beta (refl body) (refl argument)
  | appFun argument _ ih => exact .app ih (refl argument)
  | appArg function _ ih => exact .app (refl function) ih
  | lam _ ih => exact .lam ih
  | andLeft right _ ih => exact .and ih (refl right)
  | andRight left _ ih => exact .and (refl left) ih
  | orLeft right _ ih => exact .or ih (refl right)
  | orRight left _ ih => exact .or (refl left) ih
  | impLeft right _ ih => exact .imp ih (refl right)
  | impRight left _ ih => exact .imp (refl left) ih
  | not _ ih => exact .not ih
  | eqLeft right _ ih => exact .eq ih (refl right)
  | eqRight left _ ih => exact .eq (refl left) ih
  | all _ ih => exact .all ih
  | ex _ ih => exact .ex ih

theorem to_star {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (par : Par source target) : ReducesStar source target := by
  induction par with
  | var | const | top | bot => exact .refl
  | app _ _ functionIh argumentIh =>
      exact star_two Term.app (fun b ⟨s⟩ => ⟨.appFun b s⟩) (fun a _ _ ⟨s⟩ => ⟨.appArg a s⟩)
        functionIh argumentIh
  | lam _ ih => exact star_map Term.lam (fun ⟨s⟩ => ⟨.lam s⟩) ih
  | beta _ _ bodyIh argumentIh =>
      have toRedex := star_two Term.app (fun b ⟨s⟩ => ⟨.appFun b s⟩)
        (fun a _ _ ⟨s⟩ => ⟨.appArg a s⟩) (star_map Term.lam (fun ⟨s⟩ => ⟨.lam s⟩) bodyIh)
        argumentIh
      exact toRedex.tail ⟨.beta _ _⟩
  | and _ _ leftIh rightIh =>
      exact star_two Term.and (fun b ⟨s⟩ => ⟨.andLeft b s⟩) (fun a _ _ ⟨s⟩ => ⟨.andRight a s⟩)
        leftIh rightIh
  | or _ _ leftIh rightIh =>
      exact star_two Term.or (fun b ⟨s⟩ => ⟨.orLeft b s⟩) (fun a _ _ ⟨s⟩ => ⟨.orRight a s⟩)
        leftIh rightIh
  | imp _ _ leftIh rightIh =>
      exact star_two Term.imp (fun b ⟨s⟩ => ⟨.impLeft b s⟩) (fun a _ _ ⟨s⟩ => ⟨.impRight a s⟩)
        leftIh rightIh
  | eq _ _ leftIh rightIh =>
      exact star_two Term.eq (fun b ⟨s⟩ => ⟨.eqLeft b s⟩) (fun a _ _ ⟨s⟩ => ⟨.eqRight a s⟩)
        leftIh rightIh
  | not _ ih => exact star_map Term.not (fun ⟨s⟩ => ⟨.not s⟩) ih
  | all _ ih => exact star_map Term.all (fun ⟨s⟩ => ⟨.all s⟩) ih
  | ex _ ih => exact star_map Term.ex (fun ⟨s⟩ => ⟨.ex s⟩) ih

theorem rename {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (par : Par source target) : ∀ {Δ : Ctx Base} (ρ : Rename Base Γ Δ),
      Par (HOL.rename ρ source) (HOL.rename ρ target) := by
  induction par with
  | var index => intro Δ ρ; exact .var _
  | const constant => intro Δ ρ; exact .const _
  | top => intro Δ ρ; exact .top
  | bot => intro Δ ρ; exact .bot
  | app _ _ functionIh argumentIh => intro Δ ρ; exact .app (functionIh ρ) (argumentIh ρ)
  | lam _ ih => intro Δ ρ; exact .lam (ih _)
  | beta _ _ bodyIh argumentIh =>
      intro Δ ρ
      rw [ExtDerivation.rename_instantiate]
      exact .beta (bodyIh _) (argumentIh ρ)
  | and _ _ leftIh rightIh => intro Δ ρ; exact .and (leftIh ρ) (rightIh ρ)
  | or _ _ leftIh rightIh => intro Δ ρ; exact .or (leftIh ρ) (rightIh ρ)
  | imp _ _ leftIh rightIh => intro Δ ρ; exact .imp (leftIh ρ) (rightIh ρ)
  | eq _ _ leftIh rightIh => intro Δ ρ; exact .eq (leftIh ρ) (rightIh ρ)
  | not _ ih => intro Δ ρ; exact .not (ih ρ)
  | all _ ih => intro Δ ρ; exact .all (ih _)
  | ex _ ih => intro Δ ρ; exact .ex (ih _)

/-- Parallel reduction is closed under substituting parallel reducts. -/
theorem subst {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (par : Par source target) : ∀ {Δ : Ctx Base} {θ θ' : Subst Const Γ Δ},
      (∀ {σ : Ty Base} (index : Var Γ σ), Par (θ index) (θ' index)) →
        Par (HOL.subst θ source) (HOL.subst θ' target) := by
  have lifted : ∀ {Γ Δ : Ctx Base} {ρ : Ty Base} {θ θ' : Subst Const Γ Δ},
      (∀ {σ : Ty Base} (index : Var Γ σ), Par (θ index) (θ' index)) →
        ∀ {σ : Ty Base} (index : Var (ρ :: Γ) σ), Par (Subst.lift θ index) (Subst.lift θ' index) := by
    intro Γ Δ ρ θ θ' pointwise σ index
    cases index with
    | vz => exact .var _
    | vs index => exact (pointwise index).rename _
  induction par with
  | var index => intro Δ θ θ' pointwise; exact pointwise index
  | const constant => intro Δ θ θ' _; exact .const _
  | top => intro Δ θ θ' _; exact .top
  | bot => intro Δ θ θ' _; exact .bot
  | app _ _ functionIh argumentIh =>
      intro Δ θ θ' pointwise; exact .app (functionIh pointwise) (argumentIh pointwise)
  | lam _ ih => intro Δ θ θ' pointwise; exact .lam (ih (lifted pointwise))
  | beta _ _ bodyIh argumentIh =>
      intro Δ θ θ' pointwise
      rw [ProofSyntax.subst_instantiate]
      exact .beta (bodyIh (lifted pointwise)) (argumentIh pointwise)
  | and _ _ leftIh rightIh =>
      intro Δ θ θ' pointwise; exact .and (leftIh pointwise) (rightIh pointwise)
  | or _ _ leftIh rightIh =>
      intro Δ θ θ' pointwise; exact .or (leftIh pointwise) (rightIh pointwise)
  | imp _ _ leftIh rightIh =>
      intro Δ θ θ' pointwise; exact .imp (leftIh pointwise) (rightIh pointwise)
  | eq _ _ leftIh rightIh =>
      intro Δ θ θ' pointwise; exact .eq (leftIh pointwise) (rightIh pointwise)
  | not _ ih => intro Δ θ θ' pointwise; exact .not (ih pointwise)
  | all _ ih => intro Δ θ θ' pointwise; exact .all (ih (lifted pointwise))
  | ex _ ih => intro Δ θ θ' pointwise; exact .ex (ih (lifted pointwise))

theorem instantiate {Γ : Ctx Base} {σ τ : Ty Base} {body body' : Term Const (σ :: Γ) τ}
    {argument argument' : Term Const Γ σ} (bodies : Par body body')
    (arguments : Par argument argument') :
    Par (HOL.instantiate argument body) (HOL.instantiate argument' body') :=
  bodies.subst (fun index => by
    cases index with
    | vz => exact arguments
    | vs index => exact .var _)

theorem lam_inv {Γ : Ctx Base} {σ τ : Ty Base} {body : Term Const (σ :: Γ) τ}
    {target : Term Const Γ (σ ⇒ τ)} (par : Par (.lam body) target) :
    ∃ body', Par body body' ∧ target = .lam body' := by
  cases par with
  | lam inner => exact ⟨_, inner, rfl⟩

end Par

/-- Develop an application from its function, the development of the
function and the development of the argument: a redex is contracted, any other
application is kept. -/
def developApp {Γ : Ctx Base} {σ τ : Ty Base} :
    Term Const Γ (σ ⇒ τ) → Term Const Γ (σ ⇒ τ) → Term Const Γ σ → Term Const Γ τ
  | .lam _, .lam developedBody, developedArgument => instantiate developedArgument developedBody
  | _, developedFunction, developedArgument => .app developedFunction developedArgument

/-- The complete development: contract every redex present in the term. -/
def develop : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Term Const Γ τ
  | _, _, .var index => .var index
  | _, _, .const constant => .const constant
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, _, .app function argument => developApp function (develop function) (develop argument)
  | _, _, .lam body => .lam (develop body)
  | _, _, .and left right => .and (develop left) (develop right)
  | _, _, .or left right => .or (develop left) (develop right)
  | _, _, .imp left right => .imp (develop left) (develop right)
  | _, _, .eq left right => .eq (develop left) (develop right)
  | _, _, .not operand => .not (develop operand)
  | _, _, .all body => .all (develop body)
  | _, _, .ex body => .ex (develop body)

/-- **Triangle property.** Every parallel reduct of a term reduces in parallel
to its complete development. -/
theorem Par.triangle {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (par : Par source target) : Par target (develop source) := by
  induction par with
  | var index => exact .var index
  | const constant => exact .const constant
  | top => exact .top
  | bot => exact .bot
  | @app _ _ _ function function' argument argument' functionPar _ functionIh argumentIh =>
      cases function with
      | lam body =>
          obtain ⟨body', bodyPar, rfl⟩ := Par.lam_inv functionPar
          obtain ⟨developed, developedPar, same⟩ := Par.lam_inv functionIh
          simp only [develop, Term.lam.injEq] at same
          subst same
          exact .beta developedPar argumentIh
      | var => exact .app functionIh argumentIh
      | const => exact .app functionIh argumentIh
      | app => exact .app functionIh argumentIh
  | lam _ ih => exact .lam ih
  | beta _ _ bodyIh argumentIh => exact Par.instantiate bodyIh argumentIh
  | and _ _ leftIh rightIh => exact .and leftIh rightIh
  | or _ _ leftIh rightIh => exact .or leftIh rightIh
  | imp _ _ leftIh rightIh => exact .imp leftIh rightIh
  | eq _ _ leftIh rightIh => exact .eq leftIh rightIh
  | not _ ih => exact .not ih
  | all _ ih => exact .all ih
  | ex _ ih => exact .ex ih

theorem star_iff_par_star {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ} :
    ReducesStar source target ↔ Relation.ReflTransGen Par source target := by
  constructor
  · intro many
    induction many with
    | refl => exact .refl
    | tail _ step ih => exact ih.tail (let ⟨s⟩ := step; Par.of_step s)
  · intro many
    induction many with
    | refl => exact .refl
    | tail _ par ih => exact ih.trans par.to_star

/-- **Confluence of simply typed beta.** -/
theorem confluent {Γ : Ctx Base} {τ : Ty Base} {source first second : Term Const Γ τ}
    (toFirst : ReducesStar source first) (toSecond : ReducesStar source second) :
    ∃ meet, ReducesStar first meet ∧ ReducesStar second meet := by
  have joined := Relation.church_rosser
    (r := Par (Const := Const) (Γ := Γ) (τ := τ))
    (fun a b c ab ac => ⟨develop a, .single ab.triangle, .single ac.triangle⟩)
    (star_iff_par_star.mp toFirst) (star_iff_par_star.mp toSecond)
  obtain ⟨meet, firstMeet, secondMeet⟩ := joined
  exact ⟨meet, star_iff_par_star.mpr firstMeet, star_iff_par_star.mpr secondMeet⟩

/-! ## Normal forms -/

/-- A term with no step. -/
def Normal {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) : Prop :=
  ∀ target, ¬ Reduces term target

theorem eq_of_normal_star {Γ : Ctx Base} {τ : Ty Base} {term target : Term Const Γ τ}
    (normal : Normal term) (many : ReducesStar term target) : target = term := by
  cases many.cases_head with
  | inl same => exact same.symm
  | inr more =>
      obtain ⟨middle, step, _⟩ := more
      exact absurd step (normal middle)

/-- **Normal forms are unique.** -/
theorem normalForm_unique {Γ : Ctx Base} {τ : Ty Base} {source first second : Term Const Γ τ}
    (toFirst : ReducesStar source first) (firstNormal : Normal first)
    (toSecond : ReducesStar source second) (secondNormal : Normal second) : first = second := by
  obtain ⟨meet, firstMeet, secondMeet⟩ := confluent toFirst toSecond
  rw [← eq_of_normal_star firstNormal firstMeet, eq_of_normal_star secondNormal secondMeet]

/-- Two terms with a common reduct have the same normal form. -/
theorem normal_eq_of_joinable {Γ : Ctx Base} {τ : Ty Base} {left right meet : Term Const Γ τ}
    (leftMeet : ReducesStar left meet) (rightMeet : ReducesStar right meet)
    {leftNormal rightNormal : Term Const Γ τ} (toLeftNormal : ReducesStar left leftNormal)
    (leftIsNormal : Normal leftNormal) (toRightNormal : ReducesStar right rightNormal)
    (rightIsNormal : Normal rightNormal) : leftNormal = rightNormal := by
  obtain ⟨leftJoin, normalLeftJoin, meetLeftJoin⟩ := confluent toLeftNormal leftMeet
  obtain ⟨rightJoin, normalRightJoin, meetRightJoin⟩ := confluent toRightNormal rightMeet
  have leftSame := eq_of_normal_star leftIsNormal normalLeftJoin
  have rightSame := eq_of_normal_star rightIsNormal normalRightJoin
  subst leftSame rightSame
  exact normalForm_unique meetLeftJoin leftIsNormal meetRightJoin rightIsNormal

#print axioms stronglyNormalizing
#print axioms confluent
#print axioms normalForm_unique

end Mettapedia.Logic.HOL.BetaNormalization
