import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Finite
import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Native types in a higher-order signature that defines the language's relations

`HigherOrder` reads every generated formula as a predicate over the language's own relations, written in the
OSLF basis. This module reads them into any signature of higher-order logic that **defines** those relations, so a
theory able to define them, a set theory for instance, states the native types as its own predicates.

- **The definitions** (`Relations`): one term of the signature for each relation of a native structure, at a
  chosen type of elements: the steps of each label, each constructor at each arity, each collection kind's splits,
  emptiness and singletons, bodies, multi-bodies, bound variables, types, named terms, declared relations, identity, and the application
  of a body to an argument.
- **The translation** (`translate`) uses the logic's own connectives and quantifiers. A least fixed point is the
  intersection of the predicates closed under its body, and a greatest fixed point the union of those its body
  preserves, so fixed points quantify over predicates. Counting nests existentials: at least `k + 1` elements satisfy
  `P` when some `y` does and at least `k` others that are not the same as `y` do (`countTerm`).
- **Correctness** (`denote_translate`). Take a model with full domains whose definitions denote the relations of a
  native structure, through a bijection between the structure's carrier and the elements of the model
  (`Interprets`). There a formula's translation holds exactly where the formula does (`denote_translate_closed` for
  closed formulas).

Positive and negative examples are in the instances: the membership language read in set theory
(`SetMembershipKernel`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Relational

open Mettapedia.Logic.HOL hiding Formula
open Mettapedia.OSLF.MeTTaIL.Syntax (CollType TypeExpr Pattern)

universe u v w c

variable {B : Type u} {K : Ty B → Type v}

/-- `elem ⇒ ⋯ ⇒ elem ⇒ prop`, with `arity` elements. -/
def relationTy (elem : Ty B) : ℕ → Ty B
  | 0 => .prop
  | arity + 1 => elem ⇒ relationTy elem arity

/-- **Definitions of the relations of a native structure**: a term of the signature for each, in every
context, at the type of elements `elem`. -/
structure Relations (K : Ty B → Type v) (elem : Ty B) where
  /-- A step with the label, from the first element to the second. -/
  step : StepLabel → {Γ : Ctx B} → Term K Γ (elem ⇒ elem ⇒ .prop)
  /-- The first element is built by the constructor from the others. -/
  built : String → (arity : ℕ) → {Γ : Ctx B} → Term K Γ (elem ⇒ relationTy elem arity)
  /-- The first element is a collection of the kind splitting into the other two. -/
  split : CollType → {Γ : Ctx B} → Term K Γ (elem ⇒ elem ⇒ elem ⇒ .prop)
  /-- The element is the empty collection of the kind. -/
  empty : CollType → {Γ : Ctx B} → Term K Γ (elem ⇒ .prop)
  /-- The first element is the one-element collection of the kind with the second. -/
  single : CollType → {Γ : Ctx B} → Term K Γ (elem ⇒ elem ⇒ .prop)
  /-- The first element is an abstraction with the second as its body. -/
  body : {Γ : Ctx B} → Term K Γ (elem ⇒ elem ⇒ .prop)
  /-- The first element abstracts this many variables, with the second as its body. -/
  multiBody : ℕ → {Γ : Ctx B} → Term K Γ (elem ⇒ elem ⇒ .prop)
  /-- The element is the bound variable with this index. -/
  bound : ℕ → {Γ : Ctx B} → Term K Γ (elem ⇒ .prop)
  /-- The element has the type. -/
  typed : TypeExpr → {Γ : Ctx B} → Term K Γ (elem ⇒ .prop)
  /-- The element is the one the term names. -/
  named : Pattern → {Γ : Ctx B} → Term K Γ (elem ⇒ .prop)
  /-- The element is in the declared relation. -/
  inRelation : String → {Γ : Ctx B} → Term K Γ (elem ⇒ .prop)
  /-- A body applied to an argument. -/
  apply : {Γ : Ctx B} → Term K Γ (elem ⇒ elem ⇒ elem)
  /-- The two elements are the same element. -/
  same : {Γ : Ctx B} → Term K Γ (elem ⇒ elem ⇒ .prop)

/-- Predicates on elements. -/
abbrev predicate (elem : Ty B) : Ty B := elem ⇒ .prop

/-- The fixed-point variables of a formula with `n` of them, as predicate variables, newest first. -/
abbrev context (elem : Ty B) (n : ℕ) : Ctx B := List.replicate n (predicate elem)

/-! ## The translation -/

section Terms

variable {elem : Ty B} {Γ : Ctx B}

/-- A term applied to the newest variable. -/
def atNewest {result : Ty B} (function : Term K Γ (elem ⇒ result)) : Term K (elem :: Γ) result :=
  .app (weaken function) (.var .vz)

/-- A binary relation from the second newest variable to the newest. -/
def related (relation : Term K (elem :: elem :: Γ) (elem ⇒ elem ⇒ .prop)) : Term K (elem :: elem :: Γ) .prop :=
  .app (.app relation (.var (.vs .vz))) (.var .vz)

/-- A binary relation from the newest variable to the second newest. -/
def relatedBack (relation : Term K (elem :: elem :: Γ) (elem ⇒ elem ⇒ .prop)) :
    Term K (elem :: elem :: Γ) .prop :=
  .app (.app relation (.var .vz)) (.var (.vs .vz))

/-- A unary relation of the newest variable. -/
def holding (relation : Term K (elem :: Γ) (elem ⇒ .prop)) : Term K (elem :: Γ) .prop :=
  .app relation (.var .vz)

/-- A relation of the newest variable, still awaiting its other arguments. -/
def holdingAll {result : Ty B} (relation : Term K (elem :: Γ) (elem ⇒ result)) : Term K (elem :: Γ) result :=
  .app relation (.var .vz)

/-- A split of the third newest variable into the second newest and the newest. -/
def splitting (relation : Term K (elem :: elem :: elem :: Γ) (elem ⇒ elem ⇒ elem ⇒ .prop)) :
    Term K (elem :: elem :: elem :: Γ) .prop :=
  .app (.app (.app relation (.var (.vs (.vs .vz)))) (.var (.vs .vz))) (.var .vz)

/-- The second newest variable, a body, applied to the newest. -/
def applying (relation : Term K (elem :: elem :: Γ) (elem ⇒ elem ⇒ elem)) : Term K (elem :: elem :: Γ) elem :=
  .app (.app relation (.var (.vs .vz))) (.var .vz)

/-- `λx. ∃y. R x y ∧ φ y`. -/
def someWith (relation : Term K (elem :: elem :: Γ) .prop) (formula : Term K Γ (predicate elem)) :
    Term K Γ (predicate elem) :=
  .lam (.ex (.and relation (atNewest (weaken formula))))

/-- `λx. ∀y. R x y ⇒ φ y`. -/
def everyWith (relation : Term K (elem :: elem :: Γ) .prop) (formula : Term K Γ (predicate elem)) :
    Term K Γ (predicate elem) :=
  .lam (.all (.imp relation (atNewest (weaken formula))))

/-- Three weakenings. -/
abbrev weaken₃ {type first second third : Ty B} (term : Term K Γ type) : Term K (first :: second :: third :: Γ) type :=
  weaken (weaken (weaken term))

/-- **The least fixed point** of an operator on predicates: `λx. ∀X. (∀y. F X y ⇒ X y) ⇒ X x`. -/
def least (operator : Term K Γ (predicate elem ⇒ predicate elem)) : Term K Γ (predicate elem) :=
  .lam (.all (σ := predicate elem) (.imp (.all (σ := elem)
    (.imp (.app (.app (weaken₃ operator) (.var (.vs .vz))) (.var .vz)) (.app (.var (.vs .vz)) (.var .vz))))
    (.app (.var .vz) (.var (.vs .vz)))))

/-- **The greatest fixed point**: `λx. ∃X. (∀y. X y ⇒ F X y) ∧ X x`. -/
def greatest (operator : Term K Γ (predicate elem ⇒ predicate elem)) : Term K Γ (predicate elem) :=
  .lam (.ex (σ := predicate elem) (.and (.all (σ := elem)
    (.imp (.app (.var (.vs .vz)) (.var .vz)) (.app (.app (weaken₃ operator) (.var (.vs .vz))) (.var .vz))))
    (.app (.var .vz) (.var (.vs .vz)))))

variable (rels : Relations K elem)

/-- A step in the direction, between the second newest variable and the newest. -/
def stepping (direction : Direction) (label : StepLabel) : Term K (elem :: elem :: Γ) .prop :=
  match direction with
  | .forward => related (rels.step label)
  | .backward => relatedBack (rels.step label)

end Terms

variable {elem : Ty B} (rels : Relations K elem)

/-- **At least `count` distinct elements satisfy a predicate**: always for `0`; for one more, some element
satisfies it, and as many others do that are not the same as that element. -/
def countTerm : (count : ℕ) → {Γ : Ctx B} → Term K Γ (predicate elem) → Term K Γ .prop
  | 0, _, _ => .top
  | count + 1, _, holds =>
    .ex (.and (atNewest holds) (countTerm count (.lam (.and (atNewest (weaken holds)) (.not (related rels.same))))))

mutual
/-- **The translation of a formula**: a predicate on elements, in the context of its fixed-point
variables. -/
def translate : {n : ℕ} → Formula n → Term K (context elem n) (predicate elem)
  | _, .top => .lam .top
  | _, .bot => .lam .bot
  | _, .and left right => .lam (.and (atNewest (translate left)) (atNewest (translate right)))
  | _, .or left right => .lam (.or (atNewest (translate left)) (atNewest (translate right)))
  | n, .var index => .var (Var.ofFinRepeat (predicate elem) n index)
  | _, .mu inner => least (.lam (translate inner))
  | _, .nu inner => greatest (.lam (translate inner))
  | _, .possibly label formula => someWith (related (rels.step label)) (translate formula)
  | _, .necessarily label formula => everyWith (related (rels.step label)) (translate formula)
  | _, .sometimeBefore label formula => someWith (relatedBack (rels.step label)) (translate formula)
  | _, .alwaysBefore label formula => everyWith (relatedBack (rels.step label)) (translate formula)
  | _, .atLeast count direction label formula =>
    .lam (countTerm rels count (.lam (.and (stepping rels direction label) (atNewest (weaken (translate formula))))))
  | _, .allButFewer count direction label formula =>
    .lam (.not (countTerm rels count
      (.lam (.and (stepping rels direction label) (.not (atNewest (weaken (translate formula))))))))
  | _, .built constructor arguments =>
    .lam (someParts arguments Rename.weaken (holdingAll (rels.built constructor arguments.length)))
  | _, .everyBuilt constructor arguments =>
    .lam (everyParts arguments Rename.weaken (holdingAll (rels.built constructor arguments.length)))
  | _, .split kind left right =>
    .lam (.ex (σ := elem) (.ex (σ := elem) (.and (splitting (rels.split kind))
      (.and (.app (weaken₃ (translate left)) (.var (.vs .vz))) (.app (weaken₃ (translate right)) (.var .vz))))))
  | _, .everySplit kind left right =>
    .lam (.all (σ := elem) (.all (σ := elem) (.imp (splitting (rels.split kind))
      (.or (.app (weaken₃ (translate left)) (.var (.vs .vz))) (.app (weaken₃ (translate right)) (.var .vz))))))
  | _, .empty kind => .lam (holding (rels.empty kind))
  | _, .nonEmpty kind => .lam (.not (holding (rels.empty kind)))
  | _, .single kind formula => someWith (related (rels.single kind)) (translate formula)
  | _, .everySingle kind formula => everyWith (related (rels.single kind)) (translate formula)
  | _, .body formula => someWith (related rels.body) (translate formula)
  | _, .everyBody formula => everyWith (related rels.body) (translate formula)
  | _, .multiBody arity formula => someWith (related (rels.multiBody arity)) (translate formula)
  | _, .everyMultiBody arity formula => everyWith (related (rels.multiBody arity)) (translate formula)
  | _, .bound index => .lam (holding (rels.bound index))
  | _, .notBound index => .lam (.not (holding (rels.bound index)))
  | _, .typed type => .lam (holding (rels.typed type))
  | _, .untyped type => .lam (.not (holding (rels.typed type)))
  | _, .is term => .lam (holding (rels.named term))
  | _, .isNot term => .lam (.not (holding (rels.named term)))
  | _, .inRelation relation => .lam (holding (rels.inRelation relation))
  | _, .notInRelation relation => .lam (.not (holding (rels.inRelation relation)))
  | _, .mapsAll argument result =>
    .lam (.ex (σ := elem) (.and (related rels.body) (.all (σ := elem)
      (.or (.app (weaken₃ (translate argument)) (.var .vz)) (.app (weaken₃ (translate result)) (applying rels.apply))))))
  | _, .mapsSome argument result =>
    .lam (.all (σ := elem) (.imp (related rels.body) (.ex (σ := elem)
      (.and (.app (weaken₃ (translate argument)) (.var .vz)) (.app (weaken₃ (translate result)) (applying rels.apply))))))
  | _, .someOf type formula => someWith (holding (rels.typed type)) (translate formula)
  | _, .everyOf type formula => everyWith (holding (rels.typed type)) (translate formula)

/-- `∃y₁ ⋯ yₖ. φ₁ y₁ ∧ ⋯ ∧ φₖ yₖ ∧ R y₁ ⋯ yₖ`, the formulas read through a renaming. -/
def someParts : {n : ℕ} → {Δ : Ctx B} → (arguments : Formulas n) → Rename B (context elem n) Δ →
    Term K Δ (relationTy elem arguments.length) → Term K Δ .prop
  | _, _, .nil, _, relation => relation
  | _, _, .cons formula formulas, embed, relation =>
    .ex (.and (atNewest (rename embed (translate formula)))
      (someParts formulas (fun index => .vs (embed index)) (atNewest relation)))

/-- `∀y₁ ⋯ yₖ. φ₁ y₁ ∨ ⋯ ∨ φₖ yₖ ∨ ¬ R y₁ ⋯ yₖ`, the formulas read through a renaming. -/
def everyParts : {n : ℕ} → {Δ : Ctx B} → (arguments : Formulas n) → Rename B (context elem n) Δ →
    Term K Δ (relationTy elem arguments.length) → Term K Δ .prop
  | _, _, .nil, _, relation => .not relation
  | _, _, .cons formula formulas, embed, relation =>
    .all (.or (atNewest (rename embed (translate formula)))
      (everyParts formulas (fun index => .vs (embed index)) (atNewest relation)))
end

/-! ## What the translation denotes -/

section Denotation

variable {rels : Relations K elem} {M : HenkinModel.{u, v, w} B K} {Carrier : Type c}

/-- A curried relation of the model, applied through the bijection to a list of elements of its length. -/
def applyRel (M : HenkinModel.{u, v, w} B K) (e : Carrier ≃ Ty.denote M.Carrier elem) :
    (arity : ℕ) → Ty.denote M.Carrier (relationTy elem arity) → List Carrier → Prop
  | 0, value, [] => ULift.down value
  | 0, _, _ :: _ => False
  | _ + 1, _, [] => False
  | arity + 1, value, first :: rest => applyRel M e arity (value (e first)) rest

/-- **The definitions denote the relations of a native structure**, through a bijection of carriers, at every
valuation. -/
structure Interprets (M : HenkinModel.{u, v, w} B K) (e : Carrier ≃ Ty.denote M.Carrier elem)
    (rels : Relations K elem) (S : NativeStructure Carrier) : Prop where
  step : ∀ {Γ : Ctx B} (valuation : M.Valuation Γ) (label : StepLabel) (source target : Carrier),
    (M.denote (rels.step label) valuation (e source) (e target)).down ↔ S.step source label target
  built : ∀ {Γ : Ctx B} (valuation : M.Valuation Γ) (constructor : String) (arity : ℕ) (whole : Carrier)
    (parts : List Carrier), applyRel M e arity (M.denote (rels.built constructor arity) valuation (e whole)) parts ↔
      S.built whole constructor parts ∧ parts.length = arity
  split : ∀ {Γ : Ctx B} (valuation : M.Valuation Γ) (kind : CollType) (whole first second : Carrier),
    (M.denote (rels.split kind) valuation (e whole) (e first) (e second)).down ↔ S.split whole kind first second
  empty : ∀ {Γ : Ctx B} (valuation : M.Valuation Γ) (kind : CollType) (whole : Carrier),
    (M.denote (rels.empty kind) valuation (e whole)).down ↔ S.empty whole kind
  single : ∀ {Γ : Ctx B} (valuation : M.Valuation Γ) (kind : CollType) (whole member : Carrier),
    (M.denote (rels.single kind) valuation (e whole) (e member)).down ↔ S.single whole kind member
  body : ∀ {Γ : Ctx B} (valuation : M.Valuation Γ) (whole inner : Carrier),
    (M.denote rels.body valuation (e whole) (e inner)).down ↔ S.body whole inner
  multiBody : ∀ {Γ : Ctx B} (valuation : M.Valuation Γ) (arity : ℕ) (whole inner : Carrier),
    (M.denote (rels.multiBody arity) valuation (e whole) (e inner)).down ↔ S.multiBody whole arity inner
  bound : ∀ {Γ : Ctx B} (valuation : M.Valuation Γ) (index : ℕ) (whole : Carrier),
    (M.denote (rels.bound index) valuation (e whole)).down ↔ S.bound whole index
  typed : ∀ {Γ : Ctx B} (valuation : M.Valuation Γ) (type : TypeExpr) (whole : Carrier),
    (M.denote (rels.typed type) valuation (e whole)).down ↔ S.typed whole type
  named : ∀ {Γ : Ctx B} (valuation : M.Valuation Γ) (term : Pattern) (whole : Carrier),
    (M.denote (rels.named term) valuation (e whole)).down ↔ S.named whole term
  inRelation : ∀ {Γ : Ctx B} (valuation : M.Valuation Γ) (relation : String) (whole : Carrier),
    (M.denote (rels.inRelation relation) valuation (e whole)).down ↔ S.inRelation whole relation
  apply : ∀ {Γ : Ctx B} (valuation : M.Valuation Γ) (inner argument : Carrier),
    M.denote rels.apply valuation (e inner) (e argument) = e (S.apply inner argument)
  same : ∀ {Γ : Ctx B} (valuation : M.Valuation Γ) (first second : Carrier),
    (M.denote rels.same valuation (e first) (e second)).down ↔ S.same first second

variable {e : Carrier ≃ Ty.denote M.Carrier elem} {S : NativeStructure Carrier}

/-- A valuation of the fixed-point variables that holds exactly on the environment's sets. -/
def Agrees (e : Carrier ≃ Ty.denote M.Carrier elem) {n : ℕ} (valuation : M.Valuation (context elem n))
    (env : Env Carrier n) : Prop :=
  ∀ (index : Fin n) (point : Carrier),
    (valuation (Var.ofFinRepeat (predicate elem) n index) (e point)).down ↔ point ∈ env index

theorem agrees_closed (valuation : M.Valuation (context elem 0)) : Agrees e valuation (Env.closed : Env Carrier 0) :=
  fun index => index.elim0

theorem Agrees.extend {n : ℕ} {valuation : M.Valuation (context elem n)} {env : Env Carrier n}
    (agrees : Agrees e valuation env) (value : Ty.denote M.Carrier (predicate elem)) (set : Set Carrier)
    (same : ∀ point : Carrier, (value (e point)).down ↔ point ∈ set) :
    Agrees e (n := n + 1) (M.extend valuation value) (env.extend set) := by
  intro index point
  refine Fin.cases ?_ (fun index => ?_) index
  · exact same point
  · exact agrees index point

/-- Reading the next argument keeps the valuation's agreement. -/
theorem Agrees.shift {n : ℕ} {Δ : Ctx B} {embed : Rename B (context elem n) Δ} {outer : M.Valuation Δ}
    {env : Env Carrier n} (agrees : Agrees e (Soundness.renameVal M embed outer) env)
    (value : Ty.denote M.Carrier elem) :
    Agrees e (Soundness.renameVal M (fun index => .vs (embed index)) (M.extend outer value)) env :=
  agrees

variable (full : M.FullDomains)

include full in
/-- An existential over the elements of the model is one over the carrier. -/
theorem exists_element {holds : Ty.denote M.Carrier elem → Prop} :
    (∃ x, M.adm elem x ∧ holds x) ↔ ∃ point : Carrier, holds (e point) := by
  constructor
  · rintro ⟨x, -, inside⟩
    exact ⟨e.symm x, by rwa [Equiv.apply_symm_apply]⟩
  · rintro ⟨point, inside⟩
    exact ⟨e point, full _ _, inside⟩

include full in
/-- A universal over the elements of the model is one over the carrier. -/
theorem forall_element {holds : Ty.denote M.Carrier elem → Prop} :
    (∀ x, M.adm elem x → holds x) ↔ ∀ point : Carrier, holds (e point) := by
  constructor
  · intro every point
    exact every (e point) (full _ _)
  · intro every x _
    have := every (e.symm x)
    rwa [Equiv.apply_symm_apply] at this

variable {Γ : Ctx B}

theorem denote_atNewest {result : Ty B} (function : Term K Γ (elem ⇒ result)) (valuation : M.Valuation Γ)
    (point : Ty.denote M.Carrier elem) :
    M.denote (atNewest function) (M.extend valuation point) = M.denote function valuation point := by
  show M.denote (weaken function) _ point = _
  rw [Soundness.denote_weaken]

theorem denote_atNewest_weaken (formula : Term K Γ (predicate elem)) (valuation : M.Valuation Γ)
    (x y : Ty.denote M.Carrier elem) :
    M.denote (atNewest (weaken formula)) (M.extend (M.extend valuation x) y) = M.denote formula valuation y := by
  show M.denote (weaken (weaken formula)) _ y = _
  rw [Soundness.denote_weaken, Soundness.denote_weaken]

theorem denote_app_weaken₃ {result first second : Ty B} (function : Term K Γ (elem ⇒ result))
    (argument : Term K (first :: second :: elem :: Γ) elem) (valuation : M.Valuation Γ)
    (x : Ty.denote M.Carrier elem) (y : Ty.denote M.Carrier second) (z : Ty.denote M.Carrier first) :
    M.denote (.app (weaken₃ function) argument) (M.extend (M.extend (M.extend valuation x) y) z) =
      M.denote function valuation (M.denote argument (M.extend (M.extend (M.extend valuation x) y) z)) := by
  show M.denote (weaken (weaken (weaken function))) _ _ = _
  rw [Soundness.denote_weaken, Soundness.denote_weaken, Soundness.denote_weaken]

/-- The body of a fixed point, applied to the bound predicate and the newest element. -/
theorem denote_operator_step (operator : Term K Γ (predicate elem ⇒ predicate elem)) (valuation : M.Valuation Γ)
    (x : Ty.denote M.Carrier elem) (set : Ty.denote M.Carrier (predicate elem)) (y : Ty.denote M.Carrier elem) :
    M.denote (.app (.app (weaken₃ operator) (.var (.vs .vz))) (.var .vz))
        (M.extend (M.extend (M.extend valuation x) set) y) =
      M.denote operator valuation set y := by
  show M.denote (weaken (weaken (weaken operator))) _ set y = _
  rw [Soundness.denote_weaken, Soundness.denote_weaken, Soundness.denote_weaken]

include full in
theorem denote_someWith (relation : Term K (elem :: elem :: Γ) .prop) (formula : Term K Γ (predicate elem))
    (valuation : M.Valuation Γ) (point : Carrier) :
    (M.denote (someWith relation formula) valuation (e point)).down ↔
      ∃ other : Carrier, (M.denote relation (M.extend (M.extend valuation (e point)) (e other))).down ∧
        (M.denote formula valuation (e other)).down := by
  change (∃ x, M.adm elem x ∧ (M.denote relation (M.extend (M.extend valuation (e point)) x)).down ∧
    (M.denote (atNewest (weaken formula)) (M.extend (M.extend valuation (e point)) x)).down) ↔ _
  simp only [denote_atNewest_weaken]
  exact exists_element full

include full in
theorem denote_everyWith (relation : Term K (elem :: elem :: Γ) .prop) (formula : Term K Γ (predicate elem))
    (valuation : M.Valuation Γ) (point : Carrier) :
    (M.denote (everyWith relation formula) valuation (e point)).down ↔
      ∀ other : Carrier, (M.denote relation (M.extend (M.extend valuation (e point)) (e other))).down →
        (M.denote formula valuation (e other)).down := by
  change (∀ x, M.adm elem x → (M.denote relation (M.extend (M.extend valuation (e point)) x)).down →
    (M.denote (atNewest (weaken formula)) (M.extend (M.extend valuation (e point)) x)).down) ↔ _
  simp only [denote_atNewest_weaken]
  exact forall_element full

include full in
theorem denote_least (operator : Term K Γ (predicate elem ⇒ predicate elem)) (valuation : M.Valuation Γ)
    (point : Carrier) :
    (M.denote (least operator) valuation (e point)).down ↔
      ∀ set : Ty.denote M.Carrier (predicate elem),
        (∀ other : Carrier, (M.denote operator valuation set (e other)).down → (set (e other)).down) →
          (set (e point)).down := by
  change (∀ set, M.adm (predicate elem) set →
    (∀ y, M.adm elem y → (M.denote (.app (.app (weaken₃ operator) (.var (.vs .vz))) (.var .vz))
      (M.extend (M.extend (M.extend valuation (e point)) set) y)).down → (set y).down) → (set (e point)).down) ↔ _
  simp only [denote_operator_step]
  constructor
  · intro holds set closed
    exact holds set (full _ _) ((forall_element full).mpr closed)
  · intro holds set _ closed
    exact holds set ((forall_element full).mp closed)

include full in
theorem denote_greatest (operator : Term K Γ (predicate elem ⇒ predicate elem)) (valuation : M.Valuation Γ)
    (point : Carrier) :
    (M.denote (greatest operator) valuation (e point)).down ↔
      ∃ set : Ty.denote M.Carrier (predicate elem),
        (∀ other : Carrier, (set (e other)).down → (M.denote operator valuation set (e other)).down) ∧
          (set (e point)).down := by
  change (∃ set, M.adm (predicate elem) set ∧
    (∀ y, M.adm elem y → (set y).down → (M.denote (.app (.app (weaken₃ operator) (.var (.vs .vz))) (.var .vz))
      (M.extend (M.extend (M.extend valuation (e point)) set) y)).down) ∧ (set (e point)).down) ↔ _
  simp only [denote_operator_step]
  constructor
  · rintro ⟨set, -, preserved, inside⟩
    exact ⟨set, (forall_element full).mp preserved, inside⟩
  · rintro ⟨set, preserved, inside⟩
    exact ⟨set, full _ _, (forall_element full).mpr preserved, inside⟩

variable (interprets : Interprets M e rels S)

include interprets in
theorem denote_stepping (direction : Direction) (label : StepLabel) (valuation : M.Valuation Γ)
    (first second : Carrier) :
    (M.denote (stepping rels direction label) (M.extend (M.extend valuation (e first)) (e second))).down ↔
      S.stepIn direction first label second := by
  cases direction
  · exact interprets.step _ label first second
  · exact interprets.step _ label second first

include full interprets in
/-- **The counting term counts**, distinct up to the structure's identity. -/
theorem denote_countTerm : ∀ (count : ℕ) {Γ : Ctx B} (holds : Term K Γ (predicate elem)) (valuation : M.Valuation Γ),
    (M.denote (countTerm rels count holds) valuation).down ↔
      S.AtLeast count fun element => (M.denote holds valuation (e element)).down
  | 0, _, _, _ => iff_of_true trivial (NativeStructure.atLeast_zero _)
  | count + 1, _, holds, valuation => by
    have inner : ∀ (first : Carrier) (other : Carrier),
        (M.denote (.lam (.and (atNewest (weaken holds)) (.not (related rels.same))))
          (M.extend valuation (e first)) (e other)).down ↔
            (M.denote holds valuation (e other)).down ∧ ¬ S.same first other := by
      intro first other
      change (M.denote (atNewest (weaken holds)) (M.extend (M.extend valuation (e first)) (e other))).down ∧
        ¬ (M.denote (related rels.same) (M.extend (M.extend valuation (e first)) (e other))).down ↔ _
      rw [denote_atNewest_weaken]
      exact and_congr Iff.rfl (not_congr (interprets.same _ first other))
    change (∃ x, M.adm elem x ∧ (M.denote (atNewest holds) (M.extend valuation x)).down ∧
      (M.denote (countTerm rels count (.lam (.and (atNewest (weaken holds)) (.not (related rels.same)))))
        (M.extend valuation x)).down) ↔ _
    rw [exists_element full, NativeStructure.atLeast_succ]
    refine exists_congr fun first => ?_
    rw [denote_atNewest, denote_countTerm count _ _]
    exact and_congr Iff.rfl (NativeStructure.AtLeast.congr fun other => inner first other)

/-- A rewrite under a relation's argument list. -/
theorem applyRel_congr {arity : ℕ} {first second : Ty.denote M.Carrier (relationTy elem arity)}
    (same : first = second) (parts : List Carrier) :
    applyRel M e arity first parts = applyRel M e arity second parts :=
  congrArg (applyRel M e arity · parts) same

/-- A formula read through a renaming, at the newest variable. -/
theorem denote_renamed {n : ℕ} {Δ : Ctx B} (embed : Rename B (context elem n) Δ) (formula : Formula n)
    (outer : M.Valuation Δ) (first : Ty.denote M.Carrier elem) :
    (M.denote (atNewest (rename embed (translate rels formula))) (M.extend outer first)).down =
      (M.denote (translate rels formula) (Soundness.renameVal M embed outer) first).down :=
  congrArg ULift.down ((denote_atNewest _ outer first).trans
    (congrFun (Soundness.denote_rename M embed _ outer) first))

section Correctness

mutual
/-- **The translation is correct**: in a model with full domains whose definitions denote the structure's
relations, a formula's translation holds exactly where the formula does, for a valuation that agrees with the
fixed-point environment. -/
theorem denote_translate (full : M.FullDomains) (interprets : Interprets M e rels S) : ∀ {n : ℕ} (formula : Formula n) {env : Env Carrier n}
    {valuation : M.Valuation (context elem n)}, Agrees e valuation env → ∀ point : Carrier,
      (M.denote (translate rels formula) valuation (e point)).down ↔ S.sat env formula point
  | _, .top, _, _, _, _ => Iff.rfl
  | _, .bot, _, _, _, _ => Iff.rfl
  | _, .and left right, _, valuation, agrees, point => by
    change (M.denote (atNewest (translate rels left)) (M.extend valuation (e point))).down ∧
      (M.denote (atNewest (translate rels right)) (M.extend valuation (e point))).down ↔ _
    rw [denote_atNewest, denote_atNewest]
    exact and_congr (denote_translate full interprets left agrees point) (denote_translate full interprets right agrees point)
  | _, .or left right, _, valuation, agrees, point => by
    change (M.denote (atNewest (translate rels left)) (M.extend valuation (e point))).down ∨
      (M.denote (atNewest (translate rels right)) (M.extend valuation (e point))).down ↔ _
    rw [denote_atNewest, denote_atNewest]
    exact or_congr (denote_translate full interprets left agrees point) (denote_translate full interprets right agrees point)
  | _, .var index, _, _, agrees, point => agrees index point
  | _, .mu inner, env, valuation, agrees, point => by
    refine (denote_least full (.lam (translate rels inner)) valuation point).trans ?_
    constructor
    · intro holds closed isClosed
      have reads : ∀ other : Carrier,
          ((fun x => ULift.up (e.symm x ∈ closed) : Ty.denote M.Carrier (predicate elem)) (e other)).down ↔
            other ∈ closed := fun other => by
        show e.symm (e other) ∈ closed ↔ other ∈ closed
        rw [Equiv.symm_apply_apply]
      exact (reads point).mp (holds (fun x => ULift.up (e.symm x ∈ closed)) fun other inside =>
        (reads other).mpr (isClosed other ((denote_translate full interprets inner (agrees.extend _ closed reads) other).mp inside)))
    · intro holds set isClosed
      exact holds {other | (set (e other)).down} fun other inside =>
        isClosed other ((denote_translate full interprets inner (agrees.extend set _ fun _ => Iff.rfl) other).mpr inside)
  | _, .nu inner, env, valuation, agrees, point => by
    refine (denote_greatest full (.lam (translate rels inner)) valuation point).trans ?_
    constructor
    · rintro ⟨set, preserved, inside⟩
      exact ⟨{other | (set (e other)).down}, inside, fun other member =>
        (denote_translate full interprets inner (agrees.extend set _ fun _ => Iff.rfl) other).mp (preserved other member)⟩
    · rintro ⟨invariant, inside, preserved⟩
      have reads : ∀ other : Carrier,
          ((fun x => ULift.up (e.symm x ∈ invariant) : Ty.denote M.Carrier (predicate elem)) (e other)).down ↔
            other ∈ invariant := fun other => by
        show e.symm (e other) ∈ invariant ↔ other ∈ invariant
        rw [Equiv.symm_apply_apply]
      exact ⟨fun x => ULift.up (e.symm x ∈ invariant), fun other member =>
        (denote_translate full interprets inner (agrees.extend _ invariant reads) other).mpr
        (preserved other ((reads other).mp member)), (reads point).mpr inside⟩
  | _, .possibly label formula, _, valuation, agrees, point =>
    (denote_someWith full _ _ valuation point).trans (exists_congr fun other =>
      and_congr (interprets.step _ label point other) (denote_translate full interprets formula agrees other))
  | _, .necessarily label formula, _, valuation, agrees, point =>
    (denote_everyWith full _ _ valuation point).trans (forall_congr' fun other =>
      imp_congr (interprets.step _ label point other) (denote_translate full interprets formula agrees other))
  | _, .sometimeBefore label formula, _, valuation, agrees, point =>
    (denote_someWith full _ _ valuation point).trans (exists_congr fun other =>
      and_congr (interprets.step _ label other point) (denote_translate full interprets formula agrees other))
  | _, .alwaysBefore label formula, _, valuation, agrees, point =>
    (denote_everyWith full _ _ valuation point).trans (forall_congr' fun other =>
      imp_congr (interprets.step _ label other point) (denote_translate full interprets formula agrees other))
  | _, .atLeast count direction label formula, _, valuation, agrees, point => by
    change (M.denote (countTerm rels count (.lam (.and (stepping rels direction label)
      (atNewest (weaken (translate rels formula)))))) (M.extend valuation (e point))).down ↔ _
    rw [denote_countTerm full interprets]
    exact NativeStructure.AtLeast.congr fun other => by
      change (M.denote (stepping rels direction label) (M.extend (M.extend valuation (e point)) (e other))).down ∧
        (M.denote (atNewest (weaken (translate rels formula))) (M.extend (M.extend valuation (e point)) (e other))).down ↔ _
      rw [denote_atNewest_weaken]
      exact and_congr (denote_stepping interprets direction label valuation point other)
        (denote_translate full interprets formula agrees other)
  | _, .allButFewer count direction label formula, _, valuation, agrees, point => by
    change ¬ (M.denote (countTerm rels count (.lam (.and (stepping rels direction label)
      (.not (atNewest (weaken (translate rels formula))))))) (M.extend valuation (e point))).down ↔ _
    rw [denote_countTerm full interprets]
    exact not_congr (NativeStructure.AtLeast.congr fun other => by
      change (M.denote (stepping rels direction label) (M.extend (M.extend valuation (e point)) (e other))).down ∧
        ¬ (M.denote (atNewest (weaken (translate rels formula)))
          (M.extend (M.extend valuation (e point)) (e other))).down ↔ _
      rw [denote_atNewest_weaken]
      exact and_congr (denote_stepping interprets direction label valuation point other)
        (not_congr (denote_translate full interprets formula agrees other)))
  | _, .built constructor arguments, env, valuation, agrees, point => by
    refine (denote_someParts full interprets arguments Rename.weaken (outer := M.extend valuation (e point)) agrees _).trans ?_
    refine exists_congr fun parts => ?_
    rw [show applyRel M e arguments.length (M.denote (holdingAll (rels.built constructor arguments.length))
        (M.extend valuation (e point))) parts ↔ S.built point constructor parts ∧ parts.length = arguments.length
      from interprets.built _ constructor arguments.length point parts]
    constructor
    · rintro ⟨⟨isBuilt, -⟩, all⟩
      exact ⟨isBuilt, all⟩
    · rintro ⟨isBuilt, all⟩
      exact ⟨⟨isBuilt, S.satAll_length arguments all⟩, all⟩
  | _, .everyBuilt constructor arguments, env, valuation, agrees, point => by
    refine (denote_everyParts full interprets arguments Rename.weaken (outer := M.extend valuation (e point)) agrees _).trans ?_
    refine forall_congr' fun parts => ?_
    rw [show applyRel M e arguments.length (M.denote (holdingAll (rels.built constructor arguments.length))
        (M.extend valuation (e point))) parts ↔ S.built point constructor parts ∧ parts.length = arguments.length
      from interprets.built _ constructor arguments.length point parts]
    constructor
    · intro holds isBuilt
      by_cases same : parts.length = arguments.length
      · exact holds ⟨isBuilt, same⟩
      · exact S.satSome_of_length_ne arguments same
    · rintro holds ⟨isBuilt, -⟩
      exact holds isBuilt
  | _, .split kind left right, env, valuation, agrees, point => by
    change (∃ x, M.adm elem x ∧ ∃ y, M.adm elem y ∧
      (M.denote (splitting (rels.split kind)) (M.extend (M.extend (M.extend valuation (e point)) x) y)).down ∧
      (M.denote (.app (weaken₃ (translate rels left)) (.var (.vs .vz)))
        (M.extend (M.extend (M.extend valuation (e point)) x) y)).down ∧
      (M.denote (.app (weaken₃ (translate rels right)) (.var .vz))
        (M.extend (M.extend (M.extend valuation (e point)) x) y)).down) ↔ _
    simp only [denote_app_weaken₃]
    rw [exists_element full]
    refine exists_congr fun first => ?_
    rw [exists_element full]
    refine exists_congr fun second => ?_
    exact and_congr (interprets.split _ kind point first second)
      (and_congr (denote_translate full interprets left agrees first) (denote_translate full interprets right agrees second))
  | _, .everySplit kind left right, env, valuation, agrees, point => by
    change (∀ x, M.adm elem x → ∀ y, M.adm elem y →
      (M.denote (splitting (rels.split kind)) (M.extend (M.extend (M.extend valuation (e point)) x) y)).down →
      (M.denote (.app (weaken₃ (translate rels left)) (.var (.vs .vz)))
        (M.extend (M.extend (M.extend valuation (e point)) x) y)).down ∨
      (M.denote (.app (weaken₃ (translate rels right)) (.var .vz))
        (M.extend (M.extend (M.extend valuation (e point)) x) y)).down) ↔ _
    simp only [denote_app_weaken₃]
    rw [forall_element full]
    refine forall_congr' fun first => ?_
    rw [forall_element full]
    refine forall_congr' fun second => ?_
    exact imp_congr (interprets.split _ kind point first second)
      (or_congr (denote_translate full interprets left agrees first) (denote_translate full interprets right agrees second))
  | _, .empty kind, _, _, _, point => interprets.empty _ kind point
  | _, .nonEmpty kind, _, _, _, point => not_congr (interprets.empty _ kind point)
  | _, .single kind formula, _, valuation, agrees, point =>
    (denote_someWith full _ _ valuation point).trans (exists_congr fun other =>
      and_congr (interprets.single _ kind point other) (denote_translate full interprets formula agrees other))
  | _, .everySingle kind formula, _, valuation, agrees, point =>
    (denote_everyWith full _ _ valuation point).trans (forall_congr' fun other =>
      imp_congr (interprets.single _ kind point other) (denote_translate full interprets formula agrees other))
  | _, .body formula, _, valuation, agrees, point =>
    (denote_someWith full _ _ valuation point).trans (exists_congr fun other =>
      and_congr (interprets.body _ point other) (denote_translate full interprets formula agrees other))
  | _, .everyBody formula, _, valuation, agrees, point =>
    (denote_everyWith full _ _ valuation point).trans (forall_congr' fun other =>
      imp_congr (interprets.body _ point other) (denote_translate full interprets formula agrees other))
  | _, .multiBody arity formula, _, valuation, agrees, point =>
    (denote_someWith full _ _ valuation point).trans (exists_congr fun other =>
      and_congr (interprets.multiBody _ arity point other) (denote_translate full interprets formula agrees other))
  | _, .everyMultiBody arity formula, _, valuation, agrees, point =>
    (denote_everyWith full _ _ valuation point).trans (forall_congr' fun other =>
      imp_congr (interprets.multiBody _ arity point other) (denote_translate full interprets formula agrees other))
  | _, .bound index, _, _, _, point => interprets.bound _ index point
  | _, .notBound index, _, _, _, point => not_congr (interprets.bound _ index point)
  | _, .typed type, _, _, _, point => interprets.typed _ type point
  | _, .untyped type, _, _, _, point => not_congr (interprets.typed _ type point)
  | _, .is term, _, _, _, point => interprets.named _ term point
  | _, .isNot term, _, _, _, point => not_congr (interprets.named _ term point)
  | _, .inRelation relation, _, _, _, point => interprets.inRelation _ relation point
  | _, .notInRelation relation, _, _, _, point => not_congr (interprets.inRelation _ relation point)
  | _, .mapsAll argument result, env, valuation, agrees, point => by
    change (∃ x, M.adm elem x ∧
      (M.denote (related rels.body) (M.extend (M.extend valuation (e point)) x)).down ∧
      ∀ y, M.adm elem y →
        (M.denote (.app (weaken₃ (translate rels argument)) (.var .vz))
          (M.extend (M.extend (M.extend valuation (e point)) x) y)).down ∨
        (M.denote (.app (weaken₃ (translate rels result)) (applying rels.apply))
          (M.extend (M.extend (M.extend valuation (e point)) x) y)).down) ↔ _
    simp only [denote_app_weaken₃]
    rw [exists_element full]
    refine exists_congr fun inner => and_congr (interprets.body _ point inner) ?_
    rw [forall_element full]
    refine forall_congr' fun value => or_congr (denote_translate full interprets argument agrees value) ?_
    rw [show M.denote (applying rels.apply) (M.extend (M.extend (M.extend valuation (e point)) (e inner)) (e value)) =
      e (S.apply inner value) from interprets.apply _ inner value]
    exact denote_translate full interprets result agrees _
  | _, .mapsSome argument result, env, valuation, agrees, point => by
    change (∀ x, M.adm elem x →
      (M.denote (related rels.body) (M.extend (M.extend valuation (e point)) x)).down →
      ∃ y, M.adm elem y ∧
        (M.denote (.app (weaken₃ (translate rels argument)) (.var .vz))
          (M.extend (M.extend (M.extend valuation (e point)) x) y)).down ∧
        (M.denote (.app (weaken₃ (translate rels result)) (applying rels.apply))
          (M.extend (M.extend (M.extend valuation (e point)) x) y)).down) ↔ _
    simp only [denote_app_weaken₃]
    rw [forall_element full]
    refine forall_congr' fun inner => imp_congr (interprets.body _ point inner) ?_
    rw [exists_element full]
    refine exists_congr fun value => and_congr (denote_translate full interprets argument agrees value) ?_
    rw [show M.denote (applying rels.apply) (M.extend (M.extend (M.extend valuation (e point)) (e inner)) (e value)) =
      e (S.apply inner value) from interprets.apply _ inner value]
    exact denote_translate full interprets result agrees _
  | _, .someOf type formula, _, valuation, agrees, point =>
    (denote_someWith full _ _ valuation point).trans (exists_congr fun other =>
      and_congr (interprets.typed _ type other) (denote_translate full interprets formula agrees other))
  | _, .everyOf type formula, _, valuation, agrees, point =>
    (denote_everyWith full _ _ valuation point).trans (forall_congr' fun other =>
      imp_congr (interprets.typed _ type other) (denote_translate full interprets formula agrees other))

/-- The existential reading of a constructor's arguments. -/
theorem denote_someParts (full : M.FullDomains) (interprets : Interprets M e rels S) : ∀ {n : ℕ} {Δ : Ctx B} (arguments : Formulas n) {env : Env Carrier n}
    (embed : Rename B (context elem n) Δ) {outer : M.Valuation Δ},
    Agrees e (Soundness.renameVal M embed outer) env →
    ∀ relation : Term K Δ (relationTy elem arguments.length),
      (M.denote (someParts rels arguments embed relation) outer).down ↔
        ∃ parts, applyRel M e arguments.length (M.denote relation outer) parts ∧ S.satAll env arguments parts
  | _, _, .nil, _, _, outer, _, relation => by
    constructor
    · intro holds
      exact ⟨[], holds, trivial⟩
    · rintro ⟨parts, holds, all⟩
      cases parts with
      | nil => exact holds
      | cons _ _ => exact False.elim all
  | _, _, .cons formula formulas, env, embed, outer, agrees, relation => by
    change (∃ x, M.adm elem x ∧ (M.denote (atNewest (rename embed (translate rels formula))) (M.extend outer x)).down ∧
      (M.denote (someParts rels formulas (fun index => .vs (embed index)) (atNewest relation))
        (M.extend outer x)).down) ↔ _
    rw [exists_element full]
    constructor
    · rintro ⟨first, holds, rest⟩
      obtain ⟨parts, applies, all⟩ :=
        (denote_someParts full interprets formulas (fun index => .vs (embed index)) (agrees.shift (e first)) _).mp rest
      exact ⟨first :: parts, Eq.mp (applyRel_congr (denote_atNewest relation outer (e first)) parts) applies,
        (denote_translate full interprets formula agrees first).mp (Eq.mp (denote_renamed embed formula outer (e first)) holds), all⟩
    · rintro ⟨parts, applies, all⟩
      cases parts with
      | nil => exact False.elim all
      | cons first parts =>
        exact ⟨first, Eq.mpr (denote_renamed embed formula outer (e first)) ((denote_translate full interprets formula agrees first).mpr all.1),
          (denote_someParts full interprets formulas (fun index => .vs (embed index)) (agrees.shift (e first)) _).mpr
            ⟨parts, Eq.mpr (applyRel_congr (denote_atNewest relation outer (e first)) parts) applies, all.2⟩⟩

/-- The universal reading of a constructor's arguments. -/
theorem denote_everyParts (full : M.FullDomains) (interprets : Interprets M e rels S) : ∀ {n : ℕ} {Δ : Ctx B} (arguments : Formulas n) {env : Env Carrier n}
    (embed : Rename B (context elem n) Δ) {outer : M.Valuation Δ},
    Agrees e (Soundness.renameVal M embed outer) env →
    ∀ relation : Term K Δ (relationTy elem arguments.length),
      (M.denote (everyParts rels arguments embed relation) outer).down ↔
        ∀ parts, applyRel M e arguments.length (M.denote relation outer) parts → S.satSome env arguments parts
  | _, _, .nil, _, _, outer, _, relation => by
    change ¬ (M.denote relation outer).down ↔ _
    constructor
    · intro fails parts applies
      cases parts with
      | nil => exact fails applies
      | cons _ _ => exact False.elim applies
    · intro holds applies
      exact holds [] applies
  | _, _, .cons formula formulas, env, embed, outer, agrees, relation => by
    change (∀ x, M.adm elem x → (M.denote (atNewest (rename embed (translate rels formula))) (M.extend outer x)).down ∨
      (M.denote (everyParts rels formulas (fun index => .vs (embed index)) (atNewest relation))
        (M.extend outer x)).down) ↔ _
    rw [forall_element full]
    constructor
    · intro holds parts applies
      cases parts with
      | nil => exact False.elim applies
      | cons first parts =>
        rcases holds first with inFormula | rest
        · exact Or.inl ((denote_translate full interprets formula agrees first).mp
            (Eq.mp (denote_renamed embed formula outer (e first)) inFormula))
        · exact Or.inr ((denote_everyParts full interprets formulas (fun index => .vs (embed index)) (agrees.shift (e first)) _).mp
            rest parts (Eq.mpr (applyRel_congr (denote_atNewest relation outer (e first)) parts) applies))
    · intro holds first
      by_cases inFormula : S.sat env formula first
      · exact Or.inl (Eq.mpr (denote_renamed embed formula outer (e first))
          ((denote_translate full interprets formula agrees first).mpr inFormula))
      · refine Or.inr ((denote_everyParts full interprets formulas (fun index => .vs (embed index)) (agrees.shift (e first)) _).mpr
          fun parts applies => ?_)
        exact (holds (first :: parts)
          (Eq.mp (applyRel_congr (denote_atNewest relation outer (e first)) parts) applies)).resolve_left inFormula
end

/-- **A closed formula's translation holds exactly where the formula does.** -/
theorem denote_translate_closed (full : M.FullDomains) (interprets : Interprets M e rels S) (formula : Formula 0) (valuation : M.Valuation (context elem 0)) (point : Carrier) :
    (M.denote (translate rels formula) valuation (e point)).down ↔ S.sat Env.closed formula point :=
  denote_translate full interprets formula (agrees_closed valuation) point

end Correctness

end Denotation

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Relational
