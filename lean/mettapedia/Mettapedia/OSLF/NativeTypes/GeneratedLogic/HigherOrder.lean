import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Finite
import Mettapedia.OSLF.Framework.NativeBasis

/-!
# The generated formulas as higher-order logic

Every formula a language generates is a predicate of higher-order logic over the language's own
relations, built from equality, abstraction and application.

- **The signature** (`Symbol`): a constant for each relation of a native structure. These are the steps
  of each label, each constructor at each arity, each collection kind's splits, emptiness and singletons,
  bodies, multi-bodies, bound variables, types and named terms, and the application of a body to an
  argument. Constructors are relations, since modulo equations an element has many presentations.
- **The model** (`presentation`): a native structure is a presentation of the OSLF basis, with the span
  of all its steps. Its standard model interprets each constant as the relation it names.
- **The translation** (`translate`): each former becomes its defining formula. A least fixed point
  becomes the intersection of the predicates closed under its body, and a greatest fixed point the union
  of the predicates its body preserves, so fixed points quantify over predicates. Quantifiers over a type
  are relativized to it. Counting nests existentials: at least `k + 1` elements satisfy `P` when some `y`
  does and at least `k` others that are not the same as `y` do (`countTerm`).
- **Correctness** (`denote_translate`): in the standard model, a formula's translation holds exactly
  where the formula does.
- **The basis** (`basisOnly_translate`): translations use only variables, constants, application,
  abstraction and equality. Truth, falsity, the connectives and both quantifiers are the equality-based
  definitions of HOL Light, and disjunction and negation are defined the same way here.
- **Φ(L) stays in L's signature** (`usesOnly_translate`): the translation of a formula the language
  generates mentions only relations the language provides (`Provides`).
- **Agreement with the OSLF operators**: for all steps, the four modalities are the change-of-base
  operators of the step span (`diamond_eq_possibly`, `forwardBox_eq_necessarily`,
  `image_eq_sometimeBefore`, `pastBox_eq_alwaysBefore`). For closed formulas, the fixed points translate
  to the basis's `lfp` and `gfp` term for term (`translate_mu`, `translate_nu`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder

open Mettapedia.Logic.HOL hiding Formula
open Mettapedia.Logic.HOL.HOLLightBooleanDefinitions (truth falsity negation conj imp all ex applyClosed
  denote_truth denote_falsity denote_negation denote_conj denote_imp denote_all denote_ex denote_applyClosed)
open Mettapedia.OSLF.Framework.NativeBasis (Base Const Presentation model model_full carriers stateTy predTy nowhere)
open Mettapedia.OSLF.Framework.DerivedModalities (ReductionSpan)
open Mettapedia.OSLF.MeTTaIL.Syntax (CollType TypeExpr Pattern)

universe u v w

/-! ## Disjunction and negation from equality -/

section Connectives

variable {B : Type u} {K : Ty B → Type v} {Γ : Ctx B}

/-- Disjunction from equality: `λp. λq. ∀r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r`. -/
def disjunction : ClosedTerm K (.prop ⇒ .prop ⇒ .prop) :=
  .lam (.lam (all (imp (imp (.var (.vs (.vs .vz))) (.var .vz)) (imp (imp (.var (.vs .vz)) (.var .vz)) (.var .vz)))))

/-- The disjunction of two propositions. -/
def disj (left right : Term K Γ .prop) : Term K Γ .prop :=
  .app (applyClosed disjunction left) right

/-- The negation of a proposition. -/
def neg (proposition : Term K Γ .prop) : Term K Γ .prop :=
  applyClosed negation proposition

theorem denote_disjunction (M : HenkinModel.{u, v, w} B K) (full : M.FullDomains) (valuation : M.Valuation [])
    (left right : Ty.denote M.Carrier .prop) :
    M.denote disjunction valuation left right = .up (left.down ∨ right.down) := by
  apply ULift.ext
  apply propext
  simp only [disjunction, HenkinModel.denote, PreModel.denote, denote_all, denote_imp M full, PreModel.extend]
  constructor
  · intro holds
    exact holds (.up (left.down ∨ right.down)) (full _ _) Or.inl Or.inr
  · rintro (holds | holds) _ _ first second
    · exact first holds
    · exact second holds

theorem denote_disj (M : HenkinModel.{u, v, w} B K) (full : M.FullDomains) (left right : Term K Γ .prop)
    (valuation : M.Valuation Γ) :
    M.denote (disj left right) valuation = .up ((M.denote left valuation).down ∨ (M.denote right valuation).down) := by
  change M.denote (applyClosed disjunction left) valuation (M.denote right valuation) = _
  rw [denote_applyClosed]
  exact denote_disjunction M full _ _ _

theorem denote_neg (M : HenkinModel.{u, v, w} B K) (full : M.FullDomains) (proposition : Term K Γ .prop)
    (valuation : M.Valuation Γ) :
    M.denote (neg proposition) valuation = .up (¬ (M.denote proposition valuation).down) := by
  rw [neg, denote_applyClosed]
  exact denote_negation M full _ _

end Connectives

/-! ## The signature of a native structure -/

/-- The type of elements. -/
abbrev element : Ty (Base Unit) := stateTy ()

/-- Predicates on elements. -/
abbrev predicate : Ty (Base Unit) := predTy ()

/-- `element ⇒ ⋯ ⇒ element ⇒ prop`, with `arity` elements. -/
def relationTy : ℕ → Ty (Base Unit)
  | 0 => .prop
  | arity + 1 => element ⇒ relationTy arity

/-- **The relations of a native structure, as constants.** -/
inductive Symbol : Ty (Base Unit) → Type where
  /-- A step with the label, from the first element to the second. -/
  | step (label : StepLabel) : Symbol (element ⇒ element ⇒ .prop)
  /-- The first element is built by the constructor from the others. -/
  | built (constructor : String) (arity : ℕ) : Symbol (element ⇒ relationTy arity)
  /-- The first element is a collection of the kind splitting into the other two. -/
  | split (kind : CollType) : Symbol (element ⇒ element ⇒ element ⇒ .prop)
  /-- The element is the empty collection of the kind. -/
  | empty (kind : CollType) : Symbol (element ⇒ .prop)
  /-- The first element is the one-element collection of the kind with the second. -/
  | single (kind : CollType) : Symbol (element ⇒ element ⇒ .prop)
  /-- The first element is an abstraction with the second as its body. -/
  | body : Symbol (element ⇒ element ⇒ .prop)
  /-- The first element abstracts this many variables, with the second as its body. -/
  | multiBody (arity : ℕ) : Symbol (element ⇒ element ⇒ .prop)
  /-- The element is the bound variable with this index. -/
  | bound (index : ℕ) : Symbol (element ⇒ .prop)
  /-- The element has the type. -/
  | typed (type : TypeExpr) : Symbol (element ⇒ .prop)
  /-- The element is the one the term names. -/
  | named (term : Pattern) : Symbol (element ⇒ .prop)
  /-- A body applied to an argument. -/
  | apply : Symbol (element ⇒ element ⇒ element)
  /-- The two elements are the same element. -/
  | same : Symbol (element ⇒ element ⇒ .prop)

/-- The constants: the relations, and the two legs of the step span. -/
abbrev Constant := Const Unit () Symbol

/-! ## A native structure as a presentation -/

section Presentation

variable {Carrier : Type} {Edge : Type}

/-- The values of a standard model over these elements and steps. -/
abbrev Value (Carrier Edge : Type) (type : Ty (Base Unit)) : Type 1 :=
  Ty.denote.{0, 0} (carriers (fun _ : Unit => Carrier) Edge) type

/-- A predicate on lists of elements, curried. -/
def curryList : (arity : ℕ) → (List Carrier → Prop) → Value Carrier Edge (relationTy arity)
  | 0, holds => ULift.up (holds [])
  | arity + 1, holds => fun first => curryList arity fun rest => holds (ULift.down first :: rest)

/-- A curried relation, applied to a list of its length. -/
def applyList : (arity : ℕ) → Value Carrier Edge (relationTy arity) → List Carrier → Prop
  | 0, value, [] => ULift.down value
  | 0, _, _ :: _ => False
  | _ + 1, _, [] => False
  | arity + 1, value, first :: rest => applyList arity (value (ULift.up first)) rest

theorem applyList_curryList : ∀ (arity : ℕ) (holds : List Carrier → Prop) (parts : List Carrier),
    applyList (Edge := Edge) arity (curryList arity holds) parts ↔ holds parts ∧ parts.length = arity
  | 0, _, [] => by simp [applyList, curryList]
  | 0, _, _ :: _ => by simp [applyList]
  | _ + 1, _, [] => by simp [applyList]
  | arity + 1, holds, first :: rest => by
    simp only [applyList, curryList, applyList_curryList arity _ rest, List.length_cons, Nat.add_right_cancel_iff]

variable (S : NativeStructure Carrier)

/-- **The value of each relation** in a native structure. -/
def interpret : {type : Ty (Base Unit)} → Symbol type → Value Carrier Edge type
  | _, .step label => fun source target => ULift.up (S.step (ULift.down source) label (ULift.down target))
  | _, .built constructor arity => fun whole => curryList arity fun parts => S.built (ULift.down whole) constructor parts
  | _, .split kind => fun whole first second =>
    ULift.up (S.split (ULift.down whole) kind (ULift.down first) (ULift.down second))
  | _, .empty kind => fun whole => ULift.up (S.empty (ULift.down whole) kind)
  | _, .single kind => fun whole member => ULift.up (S.single (ULift.down whole) kind (ULift.down member))
  | _, .body => fun whole inner => ULift.up (S.body (ULift.down whole) (ULift.down inner))
  | _, .multiBody arity => fun whole inner => ULift.up (S.multiBody (ULift.down whole) arity (ULift.down inner))
  | _, .bound index => fun whole => ULift.up (S.bound (ULift.down whole) index)
  | _, .typed type => fun whole => ULift.up (S.typed (ULift.down whole) type)
  | _, .named term => fun whole => ULift.up (S.named (ULift.down whole) term)
  | _, .apply => fun inner argument => ULift.up (S.apply (ULift.down inner) (ULift.down argument))
  | _, .same => fun first second => ULift.up (S.same (ULift.down first) (ULift.down second))

/-- The span of all steps. -/
abbrev stepSpan : ReductionSpan.{0, 0} Carrier where
  Edge := { pair : Carrier × Carrier // S.step pair.1 .any pair.2 }
  source edge := edge.1.1
  target edge := edge.1.2

/-- **A native structure as a presentation** of the OSLF basis: its elements, the span of all its steps,
and its relations. -/
abbrev presentation : Presentation Unit () Symbol where
  Carrier _ := Carrier
  span := stepSpan S
  operation symbol := interpret S symbol

/-- **The standard model** of a native structure. -/
abbrev standardModel : HenkinModel.{0, 0, 0} (Base Unit) Constant := model (presentation S)

theorem full : (standardModel S).FullDomains := model_full (presentation S)

end Presentation

/-! ## The translation -/

/-- The fixed-point variables of a formula with `n` of them, as predicate variables, newest first. -/
abbrev context (n : ℕ) : Ctx (Base Unit) := List.replicate n predicate

section Terms

variable {Γ : Ctx (Base Unit)}

/-- A term applied to the newest variable. -/
def atNewest {result : Ty (Base Unit)} (function : Term Constant Γ (element ⇒ result)) :
    Term Constant (element :: Γ) result :=
  .app (weaken function) (.var .vz)

/-- A binary relation from the second newest variable to the newest. -/
def related (symbol : Symbol (element ⇒ element ⇒ .prop)) : Term Constant (element :: element :: Γ) .prop :=
  .app (.app (.const (.op symbol)) (.var (.vs .vz))) (.var .vz)

/-- A binary relation from the newest variable to the second newest. -/
def relatedBack (symbol : Symbol (element ⇒ element ⇒ .prop)) : Term Constant (element :: element :: Γ) .prop :=
  .app (.app (.const (.op symbol)) (.var .vz)) (.var (.vs .vz))

/-- A unary relation of the newest variable. -/
def holding (symbol : Symbol (element ⇒ .prop)) : Term Constant (element :: Γ) .prop :=
  .app (.const (.op symbol)) (.var .vz)

/-- A split of the third newest variable into the second newest and the newest. -/
def splitting (kind : CollType) : Term Constant (element :: element :: element :: Γ) .prop :=
  .app (.app (.app (.const (.op (.split kind))) (.var (.vs (.vs .vz)))) (.var (.vs .vz))) (.var .vz)

/-- The second newest variable, a body, applied to the newest. -/
def applying : Term Constant (element :: element :: Γ) element :=
  .app (.app (.const (.op .apply)) (.var (.vs .vz))) (.var .vz)

/-- `λx. ∃y. R x y ∧ φ y`. -/
def someWith (relation : Term Constant (element :: element :: Γ) .prop) (formula : Term Constant Γ predicate) :
    Term Constant Γ predicate :=
  .lam (ex (conj relation (atNewest (weaken formula))))

/-- `λx. ∀y. R x y ⇒ φ y`. -/
def everyWith (relation : Term Constant (element :: element :: Γ) .prop) (formula : Term Constant Γ predicate) :
    Term Constant Γ predicate :=
  .lam (all (imp relation (atNewest (weaken formula))))

/-- Three weakenings. -/
abbrev weaken₃ {type : Ty (Base Unit)} {first second third : Ty (Base Unit)} (term : Term Constant Γ type) :
    Term Constant (first :: second :: third :: Γ) type :=
  weaken (weaken (weaken term))

/-- **The least fixed point** of an operator on predicates: `λx. ∀X. (∀y. F X y ⇒ X y) ⇒ X x`. -/
def least (operator : Term Constant Γ (predicate ⇒ predicate)) : Term Constant Γ predicate :=
  .lam (all (imp (all (imp (.app (.app (weaken₃ operator) (.var (.vs .vz))) (.var .vz)) (.app (.var (.vs .vz)) (.var .vz))))
    (.app (.var .vz) (.var (.vs .vz)))))

/-- **The greatest fixed point**: `λx. ∃X. (∀y. X y ⇒ F X y) ∧ X x`. -/
def greatest (operator : Term Constant Γ (predicate ⇒ predicate)) : Term Constant Γ predicate :=
  .lam (ex (conj (all (imp (.app (.var (.vs .vz)) (.var .vz)) (.app (.app (weaken₃ operator) (.var (.vs .vz))) (.var .vz))))
    (.app (.var .vz) (.var (.vs .vz)))))

/-- A step in the direction, between the second newest variable and the newest. -/
def stepping (direction : Direction) (label : StepLabel) : Term Constant (element :: element :: Γ) .prop :=
  match direction with
  | .forward => related (.step label)
  | .backward => relatedBack (.step label)

end Terms

/-- **At least `count` distinct elements satisfy a predicate**: always for `0`; for one more, some element
satisfies it, and as many others do that are not the same as that element. -/
def countTerm : (count : ℕ) → {Γ : Ctx (Base Unit)} → Term Constant Γ predicate → Term Constant Γ .prop
  | 0, _, _ => weakenCtx _ truth
  | count + 1, _, holds =>
    ex (conj (atNewest holds) (countTerm count (.lam (conj (atNewest (weaken holds)) (neg (related .same))))))

mutual
/-- **The translation of a formula**: a predicate on elements, in the context of its fixed-point
variables. -/
def translate : {n : ℕ} → Formula n → Term Constant (context n) predicate
  | _, .top => .lam (weakenCtx _ truth)
  | _, .bot => .lam (weakenCtx _ falsity)
  | _, .and left right => .lam (conj (atNewest (translate left)) (atNewest (translate right)))
  | _, .or left right => .lam (disj (atNewest (translate left)) (atNewest (translate right)))
  | n, .var index => .var (Var.ofFinRepeat predicate n index)
  | _, .mu inner => least (.lam (translate inner))
  | _, .nu inner => greatest (.lam (translate inner))
  | _, .possibly label formula => someWith (related (.step label)) (translate formula)
  | _, .necessarily label formula => everyWith (related (.step label)) (translate formula)
  | _, .sometimeBefore label formula => someWith (relatedBack (.step label)) (translate formula)
  | _, .alwaysBefore label formula => everyWith (relatedBack (.step label)) (translate formula)
  | _, .atLeast count direction label formula =>
    .lam (countTerm count (.lam (conj (stepping direction label) (atNewest (weaken (translate formula))))))
  | _, .allButFewer count direction label formula =>
    .lam (neg (countTerm count (.lam (conj (stepping direction label) (neg (atNewest (weaken (translate formula))))))))
  | _, .built constructor arguments =>
    .lam (someParts arguments Rename.weaken (atNewest (.const (.op (.built constructor arguments.length)))))
  | _, .everyBuilt constructor arguments =>
    .lam (everyParts arguments Rename.weaken (atNewest (.const (.op (.built constructor arguments.length)))))
  | _, .split kind left right =>
    .lam (ex (ex (conj (splitting kind)
      (conj (.app (weaken₃ (translate left)) (.var (.vs .vz))) (.app (weaken₃ (translate right)) (.var .vz))))))
  | _, .everySplit kind left right =>
    .lam (all (all (imp (splitting kind)
      (disj (.app (weaken₃ (translate left)) (.var (.vs .vz))) (.app (weaken₃ (translate right)) (.var .vz))))))
  | _, .empty kind => .lam (holding (.empty kind))
  | _, .nonEmpty kind => .lam (neg (holding (.empty kind)))
  | _, .single kind formula => someWith (related (.single kind)) (translate formula)
  | _, .everySingle kind formula => everyWith (related (.single kind)) (translate formula)
  | _, .body formula => someWith (related .body) (translate formula)
  | _, .everyBody formula => everyWith (related .body) (translate formula)
  | _, .multiBody arity formula => someWith (related (.multiBody arity)) (translate formula)
  | _, .everyMultiBody arity formula => everyWith (related (.multiBody arity)) (translate formula)
  | _, .bound index => .lam (holding (.bound index))
  | _, .notBound index => .lam (neg (holding (.bound index)))
  | _, .typed type => .lam (holding (.typed type))
  | _, .untyped type => .lam (neg (holding (.typed type)))
  | _, .is term => .lam (holding (.named term))
  | _, .isNot term => .lam (neg (holding (.named term)))
  | _, .mapsAll argument result =>
    .lam (ex (conj (related .body)
      (all (disj (.app (weaken₃ (translate argument)) (.var .vz)) (.app (weaken₃ (translate result)) applying)))))
  | _, .mapsSome argument result =>
    .lam (all (imp (related .body)
      (ex (conj (.app (weaken₃ (translate argument)) (.var .vz)) (.app (weaken₃ (translate result)) applying)))))
  | _, .someOf type formula => someWith (holding (.typed type)) (translate formula)
  | _, .everyOf type formula => everyWith (holding (.typed type)) (translate formula)

/-- `∃y₁ ⋯ yₖ. φ₁ y₁ ∧ ⋯ ∧ φₖ yₖ ∧ R y₁ ⋯ yₖ`, the formulas read through a renaming. -/
def someParts : {n : ℕ} → {Δ : Ctx (Base Unit)} → (arguments : Formulas n) → Rename (Base Unit) (context n) Δ →
    Term Constant Δ (relationTy arguments.length) → Term Constant Δ .prop
  | _, _, .nil, _, relation => relation
  | _, _, .cons formula formulas, embed, relation =>
    ex (conj (atNewest (rename embed (translate formula)))
      (someParts formulas (fun index => .vs (embed index)) (atNewest relation)))

/-- `∀y₁ ⋯ yₖ. φ₁ y₁ ∨ ⋯ ∨ φₖ yₖ ∨ ¬ R y₁ ⋯ yₖ`, the formulas read through a renaming. -/
def everyParts : {n : ℕ} → {Δ : Ctx (Base Unit)} → (arguments : Formulas n) → Rename (Base Unit) (context n) Δ →
    Term Constant Δ (relationTy arguments.length) → Term Constant Δ .prop
  | _, _, .nil, _, relation => neg relation
  | _, _, .cons formula formulas, embed, relation =>
    all (disj (atNewest (rename embed (translate formula)))
      (everyParts formulas (fun index => .vs (embed index)) (atNewest relation)))
end


/-! ## What the translation denotes -/

section Denotation

variable {Carrier : Type} {S : NativeStructure Carrier}

/-- A valuation of the fixed-point variables that holds exactly on the environment's sets. -/
def Agrees (S : NativeStructure Carrier) {n : ℕ} (valuation : (standardModel S).Valuation (context n))
    (env : Env Carrier n) : Prop :=
  ∀ (index : Fin n) (point : Carrier),
    (valuation (Var.ofFinRepeat predicate n index) (ULift.up point)).down ↔ point ∈ env index

theorem agrees_closed (valuation : (standardModel S).Valuation (context 0)) : Agrees S valuation Env.closed :=
  fun index => index.elim0

theorem Agrees.extend {n : ℕ} {valuation : (standardModel S).Valuation (context n)} {env : Env Carrier n}
    (agrees : Agrees S valuation env) (value : Ty.denote (standardModel S).Carrier predicate) (set : Set Carrier)
    (same : ∀ point : Carrier, (value (ULift.up point)).down ↔ point ∈ set) :
    Agrees S (n := n + 1) ((standardModel S).extend valuation value) (env.extend set) := by
  intro index point
  refine Fin.cases ?_ (fun index => ?_) index
  · exact same point
  · exact agrees index point

/-- Reading the next argument keeps the valuation's agreement. -/
theorem Agrees.shift {n : ℕ} {Δ : Ctx (Base Unit)} {embed : Rename (Base Unit) (context n) Δ}
    {outer : (standardModel S).Valuation Δ} {env : Env Carrier n}
    (agrees : Agrees S (Soundness.renameVal (standardModel S) embed outer) env)
    (value : Ty.denote (standardModel S).Carrier element) :
    Agrees S (Soundness.renameVal (standardModel S) (fun index => .vs (embed index))
      ((standardModel S).extend outer value)) env :=
  agrees

variable {Γ : Ctx (Base Unit)}

theorem denote_rename_renameVal {Δ : Ctx (Base Unit)} {type : Ty (Base Unit)} (embed : Rename (Base Unit) Γ Δ)
    (term : Term Constant Γ type) (valuation : (standardModel S).Valuation Δ) :
    (standardModel S).denote (rename embed term) valuation =
      (standardModel S).denote term (Soundness.renameVal (standardModel S) embed valuation) :=
  Soundness.denote_rename _ embed term valuation

theorem denote_atNewest {result : Ty (Base Unit)} (function : Term Constant Γ (element ⇒ result))
    (valuation : (standardModel S).Valuation Γ) (point : Ty.denote (standardModel S).Carrier element) :
    (standardModel S).denote (atNewest function) ((standardModel S).extend valuation point) =
      (standardModel S).denote function valuation point := by
  show (standardModel S).denote (weaken function) _ point = _
  rw [Soundness.denote_weaken]

theorem denote_atNewest_weaken (formula : Term Constant Γ predicate) (valuation : (standardModel S).Valuation Γ)
    (x y : Ty.denote (standardModel S).Carrier element) :
    (standardModel S).denote (atNewest (weaken formula))
        ((standardModel S).extend ((standardModel S).extend valuation x) y) =
      (standardModel S).denote formula valuation y := by
  show (standardModel S).denote (weaken (weaken formula)) _ y = _
  rw [Soundness.denote_weaken, Soundness.denote_weaken]

theorem denote_app_weaken₃ {result first second : Ty (Base Unit)} (function : Term Constant Γ (element ⇒ result))
    (argument : Term Constant (first :: second :: element :: Γ) element) (valuation : (standardModel S).Valuation Γ)
    (x : Ty.denote (standardModel S).Carrier element) (y : Ty.denote (standardModel S).Carrier second)
    (z : Ty.denote (standardModel S).Carrier first) :
    (standardModel S).denote (.app (weaken₃ function) argument)
        ((standardModel S).extend ((standardModel S).extend ((standardModel S).extend valuation x) y) z) =
      (standardModel S).denote function valuation ((standardModel S).denote argument
        ((standardModel S).extend ((standardModel S).extend ((standardModel S).extend valuation x) y) z)) := by
  show (standardModel S).denote (weaken (weaken (weaken function))) _ _ = _
  rw [Soundness.denote_weaken, Soundness.denote_weaken, Soundness.denote_weaken]

/-- The body of a fixed point, applied to the bound predicate and the newest element. -/
theorem denote_operator_step (operator : Term Constant Γ (predicate ⇒ predicate))
    (valuation : (standardModel S).Valuation Γ) (x : Ty.denote (standardModel S).Carrier element)
    (set : Ty.denote (standardModel S).Carrier predicate) (y : Ty.denote (standardModel S).Carrier element) :
    (standardModel S).denote (.app (.app (weaken₃ operator) (.var (.vs .vz))) (.var .vz))
        ((standardModel S).extend ((standardModel S).extend ((standardModel S).extend valuation x) set) y) =
      (standardModel S).denote operator valuation set y := by
  show (standardModel S).denote (weaken (weaken (weaken operator))) _ set y = _
  rw [Soundness.denote_weaken, Soundness.denote_weaken, Soundness.denote_weaken]

theorem denote_someWith (relation : Term Constant (element :: element :: Γ) .prop)
    (formula : Term Constant Γ predicate) (valuation : (standardModel S).Valuation Γ) (point : Carrier) :
    ((standardModel S).denote (someWith relation formula) valuation (ULift.up point)).down ↔
      ∃ other : Carrier, ((standardModel S).denote relation
          ((standardModel S).extend (σ := element) ((standardModel S).extend (σ := element) valuation (ULift.up point))
            (ULift.up other))).down ∧
        ((standardModel S).denote formula valuation (ULift.up other)).down := by
  change ((standardModel S).denote (ex (conj relation (atNewest (weaken formula))))
    ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ _
  rw [denote_ex _ (full S)]
  simp only [denote_conj _ (full S)]
  constructor
  · rintro ⟨other, _, holds, satisfies⟩
    exact ⟨ULift.down other, holds,
      Eq.mp (congrArg ULift.down (denote_atNewest_weaken formula valuation _ other)) satisfies⟩
  · rintro ⟨other, holds, satisfies⟩
    exact ⟨ULift.up other, trivial, holds,
      Eq.mpr (congrArg ULift.down (denote_atNewest_weaken formula valuation _ _)) satisfies⟩

theorem denote_everyWith (relation : Term Constant (element :: element :: Γ) .prop)
    (formula : Term Constant Γ predicate) (valuation : (standardModel S).Valuation Γ) (point : Carrier) :
    ((standardModel S).denote (everyWith relation formula) valuation (ULift.up point)).down ↔
      ∀ other : Carrier, ((standardModel S).denote relation
          ((standardModel S).extend (σ := element) ((standardModel S).extend (σ := element) valuation (ULift.up point))
            (ULift.up other))).down →
        ((standardModel S).denote formula valuation (ULift.up other)).down := by
  change ((standardModel S).denote (all (imp relation (atNewest (weaken formula))))
    ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ _
  rw [denote_all]
  simp only [denote_imp _ (full S)]
  constructor
  · intro holds other related
    exact Eq.mp (congrArg ULift.down (denote_atNewest_weaken formula valuation _ _)) (holds (ULift.up other) trivial related)
  · intro holds other _ related
    exact Eq.mpr (congrArg ULift.down (denote_atNewest_weaken formula valuation _ other)) (holds (ULift.down other) related)

theorem denote_least (operator : Term Constant Γ (predicate ⇒ predicate)) (valuation : (standardModel S).Valuation Γ)
    (point : Carrier) :
    ((standardModel S).denote (least operator) valuation (ULift.up point)).down ↔
      ∀ set : Ty.denote (standardModel S).Carrier predicate,
        (∀ other : Carrier, ((standardModel S).denote operator valuation set (ULift.up other)).down →
          (set (ULift.up other)).down) → (set (ULift.up point)).down := by
  change ((standardModel S).denote (all (imp (all (imp (.app (.app (weaken₃ operator) (.var (.vs .vz))) (.var .vz))
    (.app (.var (.vs .vz)) (.var .vz)))) (.app (.var .vz) (.var (.vs .vz)))))
    ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ _
  simp only [denote_all, denote_imp _ (full S)]
  constructor
  · intro holds set closed
    exact holds set trivial fun other _ inside => closed (ULift.down other)
      (Eq.mp (congrArg ULift.down (denote_operator_step operator valuation _ set other)) inside)
  · intro holds set _ closed
    exact holds set fun other inside => closed (ULift.up other) trivial
      (Eq.mpr (congrArg ULift.down (denote_operator_step operator valuation _ set _)) inside)

theorem denote_greatest (operator : Term Constant Γ (predicate ⇒ predicate))
    (valuation : (standardModel S).Valuation Γ) (point : Carrier) :
    ((standardModel S).denote (greatest operator) valuation (ULift.up point)).down ↔
      ∃ set : Ty.denote (standardModel S).Carrier predicate,
        (∀ other : Carrier, (set (ULift.up other)).down →
          ((standardModel S).denote operator valuation set (ULift.up other)).down) ∧ (set (ULift.up point)).down := by
  change ((standardModel S).denote (ex (conj (all (imp (.app (.var (.vs .vz)) (.var .vz))
    (.app (.app (weaken₃ operator) (.var (.vs .vz))) (.var .vz)))) (.app (.var .vz) (.var (.vs .vz)))))
    ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ _
  rw [denote_ex _ (full S)]
  simp only [denote_conj _ (full S), denote_all, denote_imp _ (full S)]
  constructor
  · rintro ⟨set, _, preserved, inside⟩
    exact ⟨set, fun other member => Eq.mp (congrArg ULift.down (denote_operator_step operator valuation _ set _))
      (preserved (ULift.up other) trivial member), inside⟩
  · rintro ⟨set, preserved, inside⟩
    exact ⟨set, trivial, fun other _ member => Eq.mpr (congrArg ULift.down (denote_operator_step operator valuation _ set other))
      (preserved (ULift.down other) member), inside⟩

theorem denote_stepping (direction : Direction) (label : StepLabel) (valuation : (standardModel S).Valuation Γ)
    (first second : Carrier) :
    ((standardModel S).denote (stepping direction label)
        ((standardModel S).extend (σ := element) ((standardModel S).extend (σ := element) valuation (ULift.up first))
          (ULift.up second))).down ↔ S.stepIn direction first label second := by
  cases direction <;> exact Iff.rfl

/-- **The counting term counts**, distinct up to the structure's identity. -/
theorem denote_countTerm : ∀ (count : ℕ) {Γ : Ctx (Base Unit)} (holds : Term Constant Γ predicate)
    (valuation : (standardModel S).Valuation Γ),
    ((standardModel S).denote (countTerm count holds) valuation).down ↔
      S.AtLeast count fun element => ((standardModel S).denote holds valuation (ULift.up element)).down
  | 0, _, _, valuation => by
    change ((standardModel S).denote (weakenCtx _ truth) valuation).down ↔ _
    rw [HenkinModel.denote_weakenCtx, denote_truth]
    exact iff_of_true trivial (NativeStructure.atLeast_zero _)
  | count + 1, _, holds, valuation => by
    have inner : ∀ (first : Ty.denote (standardModel S).Carrier element) (other : Carrier),
        ((standardModel S).denote (.lam (conj (atNewest (weaken holds)) (neg (related .same))))
          ((standardModel S).extend valuation first) (ULift.up other)).down ↔
            ((standardModel S).denote holds valuation (ULift.up other)).down ∧ ¬ S.same (ULift.down first) other := by
      intro first other
      change ((standardModel S).denote (conj (atNewest (weaken holds)) (neg (related .same)))
        ((standardModel S).extend (σ := element) ((standardModel S).extend valuation first) (ULift.up other))).down ↔ _
      rw [denote_conj _ (full S), denote_neg _ (full S)]
      exact and_congr (Eq.to_iff (congrArg ULift.down (denote_atNewest_weaken holds valuation first (ULift.up other))))
        Iff.rfl
    change ((standardModel S).denote (ex (conj (atNewest holds)
      (countTerm count (.lam (conj (atNewest (weaken holds)) (neg (related .same))))))) valuation).down ↔ _
    rw [denote_ex _ (full S), NativeStructure.atLeast_succ]
    simp only [denote_conj _ (full S)]
    constructor
    · rintro ⟨first, _, holdsFirst, rest⟩
      exact ⟨ULift.down first, Eq.mp (congrArg ULift.down (denote_atNewest holds valuation first)) holdsFirst,
        ((denote_countTerm count _ _).mp rest).mono fun other inside => (inner first other).mp inside⟩
    · rintro ⟨first, holdsFirst, rest⟩
      exact ⟨ULift.up first, trivial, Eq.mpr (congrArg ULift.down (denote_atNewest holds valuation _)) holdsFirst,
        (denote_countTerm count _ _).mpr (rest.mono fun other inside => (inner (ULift.up first) other).mpr inside)⟩

/-- A rewrite under a formula's argument relation. -/
theorem applyList_congr {arity : ℕ} {first second : Value Carrier (stepSpan S).Edge (relationTy arity)}
    (same : first = second) (parts : List Carrier) :
    applyList arity first parts = applyList arity second parts :=
  congrArg (applyList arity · parts) same

/-- A formula read through a renaming, at the newest variable. -/
theorem denote_renamed {n : ℕ} {Δ : Ctx (Base Unit)} (embed : Rename (Base Unit) (context n) Δ)
    (formula : Formula n) (outer : (standardModel S).Valuation Δ) (first : Ty.denote (standardModel S).Carrier element) :
    ((standardModel S).denote (atNewest (rename embed (translate formula))) ((standardModel S).extend outer first)).down =
      ((standardModel S).denote (translate formula) (Soundness.renameVal (standardModel S) embed outer) first).down :=
  congrArg ULift.down ((denote_atNewest _ outer first).trans (congrFun (denote_rename_renameVal embed _ outer) first))

mutual
/-- **The translation is correct**: in the standard model, a formula's translation holds exactly where
the formula does, for a valuation that agrees with the fixed-point environment. -/
theorem denote_translate : ∀ {n : ℕ} (formula : Formula n) {env : Env Carrier n}
    {valuation : (standardModel S).Valuation (context n)}, Agrees S valuation env → ∀ point : Carrier,
      ((standardModel S).denote (translate formula) valuation (ULift.up point)).down ↔ S.sat env formula point
  | _, .top, _, valuation, _, point => by
    change ((standardModel S).denote (weakenCtx _ truth)
      ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ True
    rw [HenkinModel.denote_weakenCtx, denote_truth]
  | _, .bot, _, valuation, _, point => by
    change ((standardModel S).denote (weakenCtx _ falsity)
      ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ False
    rw [HenkinModel.denote_weakenCtx, denote_falsity]
  | _, .and left right, env, valuation, agrees, point => by
    change ((standardModel S).denote (conj (atNewest (translate left)) (atNewest (translate right)))
      ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔
        S.sat env left point ∧ S.sat env right point
    rw [denote_conj _ (full S)]
    exact and_congr
      ((Eq.to_iff (congrArg ULift.down (denote_atNewest (translate left) valuation (ULift.up point)))).trans
        (denote_translate left agrees point))
      ((Eq.to_iff (congrArg ULift.down (denote_atNewest (translate right) valuation (ULift.up point)))).trans
        (denote_translate right agrees point))
  | _, .or left right, env, valuation, agrees, point => by
    change ((standardModel S).denote (disj (atNewest (translate left)) (atNewest (translate right)))
      ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔
        S.sat env left point ∨ S.sat env right point
    rw [denote_disj _ (full S)]
    exact or_congr
      ((Eq.to_iff (congrArg ULift.down (denote_atNewest (translate left) valuation (ULift.up point)))).trans
        (denote_translate left agrees point))
      ((Eq.to_iff (congrArg ULift.down (denote_atNewest (translate right) valuation (ULift.up point)))).trans
        (denote_translate right agrees point))
  | _, .var index, _, _, agrees, point => agrees index point
  | _, .mu inner, env, valuation, agrees, point => by
    refine (denote_least (.lam (translate inner)) valuation point).trans ?_
    constructor
    · intro holds closed isClosed
      exact holds (fun other => ULift.up (ULift.down other ∈ closed)) fun other inside =>
        isClosed other ((denote_translate inner
          (agrees.extend (fun other => ULift.up (ULift.down other ∈ closed)) closed fun _ => Iff.rfl) other).mp inside)
    · intro holds set isClosed
      exact holds {other | (set (ULift.up other)).down} fun other inside =>
        isClosed other ((denote_translate inner (agrees.extend set _ fun _ => Iff.rfl) other).mpr inside)
  | _, .nu inner, env, valuation, agrees, point => by
    refine (denote_greatest (.lam (translate inner)) valuation point).trans ?_
    constructor
    · rintro ⟨set, preserved, inside⟩
      exact ⟨{other | (set (ULift.up other)).down}, inside, fun other member =>
        (denote_translate inner (agrees.extend set _ fun _ => Iff.rfl) other).mp (preserved other member)⟩
    · rintro ⟨invariant, inside, preserved⟩
      exact ⟨fun other => ULift.up (ULift.down other ∈ invariant), fun other member =>
        (denote_translate inner (agrees.extend (fun other => ULift.up (ULift.down other ∈ invariant)) invariant
          fun _ => Iff.rfl) other).mpr (preserved other member), inside⟩
  | _, .possibly label formula, _, valuation, agrees, point =>
    (denote_someWith _ _ valuation point).trans
      (exists_congr fun other => and_congr Iff.rfl (denote_translate formula agrees other))
  | _, .necessarily label formula, _, valuation, agrees, point =>
    (denote_everyWith _ _ valuation point).trans
      (forall_congr' fun other => imp_congr Iff.rfl (denote_translate formula agrees other))
  | _, .sometimeBefore label formula, _, valuation, agrees, point =>
    (denote_someWith _ _ valuation point).trans
      (exists_congr fun other => and_congr Iff.rfl (denote_translate formula agrees other))
  | _, .alwaysBefore label formula, _, valuation, agrees, point =>
    (denote_everyWith _ _ valuation point).trans
      (forall_congr' fun other => imp_congr Iff.rfl (denote_translate formula agrees other))
  | _, .atLeast count direction label formula, _, valuation, agrees, point => by
    change ((standardModel S).denote (countTerm count (.lam (conj (stepping direction label)
      (atNewest (weaken (translate formula)))))) ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ _
    rw [denote_countTerm]
    exact NativeStructure.AtLeast.congr fun other => by
      change ((standardModel S).denote (conj (stepping direction label) (atNewest (weaken (translate formula))))
        ((standardModel S).extend (σ := element) ((standardModel S).extend (σ := element) valuation (ULift.up point))
          (ULift.up other))).down ↔ _
      rw [denote_conj _ (full S)]
      exact and_congr (denote_stepping direction label valuation point other)
        ((Eq.to_iff (congrArg ULift.down (denote_atNewest_weaken (translate formula) valuation _ _))).trans
          (denote_translate formula agrees other))
  | _, .allButFewer count direction label formula, _, valuation, agrees, point => by
    change ((standardModel S).denote (neg (countTerm count (.lam (conj (stepping direction label)
      (neg (atNewest (weaken (translate formula)))))))) ((standardModel S).extend (σ := element) valuation
        (ULift.up point))).down ↔ _
    rw [denote_neg _ (full S), denote_countTerm]
    exact not_congr (NativeStructure.AtLeast.congr fun other => by
      change ((standardModel S).denote (conj (stepping direction label) (neg (atNewest (weaken (translate formula)))))
        ((standardModel S).extend (σ := element) ((standardModel S).extend (σ := element) valuation (ULift.up point))
          (ULift.up other))).down ↔ _
      rw [denote_conj _ (full S), denote_neg _ (full S)]
      exact and_congr (denote_stepping direction label valuation point other)
        (not_congr ((Eq.to_iff (congrArg ULift.down (denote_atNewest_weaken (translate formula) valuation _ _))).trans
          (denote_translate formula agrees other))))
  | _, .built constructor arguments, env, valuation, agrees, point => by
    refine (denote_someParts arguments Rename.weaken
      (outer := (standardModel S).extend (σ := element) valuation (ULift.up point)) agrees _).trans ?_
    refine exists_congr fun parts => ?_
    change applyList _ (curryList (Edge := (stepSpan S).Edge) _ fun parts => S.built point constructor parts) parts ∧ _ ↔ _
    rw [applyList_curryList]
    constructor
    · rintro ⟨⟨isBuilt, -⟩, all⟩
      exact ⟨isBuilt, all⟩
    · rintro ⟨isBuilt, all⟩
      exact ⟨⟨isBuilt, S.satAll_length arguments all⟩, all⟩
  | _, .everyBuilt constructor arguments, env, valuation, agrees, point => by
    refine (denote_everyParts arguments Rename.weaken
      (outer := (standardModel S).extend (σ := element) valuation (ULift.up point)) agrees _).trans ?_
    refine forall_congr' fun parts => ?_
    change applyList _ (curryList (Edge := (stepSpan S).Edge) _ fun parts => S.built point constructor parts) parts → _ ↔ _
    rw [applyList_curryList]
    constructor
    · intro holds isBuilt
      by_cases same : parts.length = arguments.length
      · exact holds ⟨isBuilt, same⟩
      · exact S.satSome_of_length_ne arguments same
    · rintro holds ⟨isBuilt, -⟩
      exact holds isBuilt
  | _, .split kind left right, env, valuation, agrees, point => by
    change ((standardModel S).denote (ex (ex (conj (splitting kind)
      (conj (.app (weaken₃ (translate left)) (.var (.vs .vz))) (.app (weaken₃ (translate right)) (.var .vz))))))
      ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ _
    rw [denote_ex _ (full S)]
    simp only [denote_ex _ (full S), denote_conj _ (full S)]
    constructor
    · rintro ⟨first, _, second, _, isSplit, inLeft, inRight⟩
      exact ⟨ULift.down first, ULift.down second, isSplit,
        (denote_translate left agrees _).mp (Eq.mp (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _)) inLeft),
        (denote_translate right agrees _).mp (Eq.mp (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _)) inRight)⟩
    · rintro ⟨first, second, isSplit, inLeft, inRight⟩
      exact ⟨ULift.up first, trivial, ULift.up second, trivial, isSplit,
        Eq.mpr (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _)) ((denote_translate left agrees first).mpr inLeft),
        Eq.mpr (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _)) ((denote_translate right agrees second).mpr inRight)⟩
  | _, .everySplit kind left right, env, valuation, agrees, point => by
    change ((standardModel S).denote (all (all (imp (splitting kind)
      (disj (.app (weaken₃ (translate left)) (.var (.vs .vz))) (.app (weaken₃ (translate right)) (.var .vz))))))
      ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ _
    rw [denote_all]
    simp only [denote_all, denote_imp _ (full S), denote_disj _ (full S)]
    constructor
    · intro holds first second isSplit
      rcases holds (ULift.up first) trivial (ULift.up second) trivial isSplit with inLeft | inRight
      · exact Or.inl ((denote_translate left agrees first).mp
          (Eq.mp (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _)) inLeft))
      · exact Or.inr ((denote_translate right agrees second).mp
          (Eq.mp (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _)) inRight))
    · intro holds first _ second _ isSplit
      rcases holds (ULift.down first) (ULift.down second) isSplit with inLeft | inRight
      · exact Or.inl (Eq.mpr (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _))
          ((denote_translate left agrees _).mpr inLeft))
      · exact Or.inr (Eq.mpr (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _))
          ((denote_translate right agrees _).mpr inRight))
  | _, .empty _, _, _, _, _ => Iff.rfl
  | _, .nonEmpty kind, _, valuation, _, point => by
    change ((standardModel S).denote (neg (holding (.empty kind)))
      ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ _
    rw [denote_neg _ (full S)]
    exact Iff.rfl
  | _, .single kind formula, _, valuation, agrees, point =>
    (denote_someWith _ _ valuation point).trans
      (exists_congr fun other => and_congr Iff.rfl (denote_translate formula agrees other))
  | _, .everySingle kind formula, _, valuation, agrees, point =>
    (denote_everyWith _ _ valuation point).trans
      (forall_congr' fun other => imp_congr Iff.rfl (denote_translate formula agrees other))
  | _, .body formula, _, valuation, agrees, point =>
    (denote_someWith _ _ valuation point).trans
      (exists_congr fun other => and_congr Iff.rfl (denote_translate formula agrees other))
  | _, .everyBody formula, _, valuation, agrees, point =>
    (denote_everyWith _ _ valuation point).trans
      (forall_congr' fun other => imp_congr Iff.rfl (denote_translate formula agrees other))
  | _, .multiBody arity formula, _, valuation, agrees, point =>
    (denote_someWith _ _ valuation point).trans
      (exists_congr fun other => and_congr Iff.rfl (denote_translate formula agrees other))
  | _, .everyMultiBody arity formula, _, valuation, agrees, point =>
    (denote_everyWith _ _ valuation point).trans
      (forall_congr' fun other => imp_congr Iff.rfl (denote_translate formula agrees other))
  | _, .bound _, _, _, _, _ => Iff.rfl
  | _, .notBound index, _, valuation, _, point => by
    change ((standardModel S).denote (neg (holding (.bound index)))
      ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ _
    rw [denote_neg _ (full S)]
    exact Iff.rfl
  | _, .typed _, _, _, _, _ => Iff.rfl
  | _, .untyped type, _, valuation, _, point => by
    change ((standardModel S).denote (neg (holding (.typed type)))
      ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ _
    rw [denote_neg _ (full S)]
    exact Iff.rfl
  | _, .is _, _, _, _, _ => Iff.rfl
  | _, .isNot term, _, valuation, _, point => by
    change ((standardModel S).denote (neg (holding (.named term)))
      ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ _
    rw [denote_neg _ (full S)]
    exact Iff.rfl
  | _, .mapsAll argument result, env, valuation, agrees, point => by
    change ((standardModel S).denote (ex (conj (related .body)
      (all (disj (.app (weaken₃ (translate argument)) (.var .vz)) (.app (weaken₃ (translate result)) applying)))))
      ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ _
    rw [denote_ex _ (full S)]
    simp only [denote_conj _ (full S), denote_all, denote_disj _ (full S)]
    constructor
    · rintro ⟨inner, _, isBody, maps⟩
      refine ⟨ULift.down inner, isBody, fun value => ?_⟩
      rcases maps (ULift.up value) trivial with holds | holds
      · exact Or.inl ((denote_translate argument agrees value).mp
          (Eq.mp (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _)) holds))
      · exact Or.inr ((denote_translate result agrees _).mp
          (Eq.mp (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _)) holds))
    · rintro ⟨inner, isBody, maps⟩
      refine ⟨ULift.up inner, trivial, isBody, fun value _ => ?_⟩
      rcases maps (ULift.down value) with holds | holds
      · exact Or.inl (Eq.mpr (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _))
          ((denote_translate argument agrees _).mpr holds))
      · exact Or.inr (Eq.mpr (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _))
          ((denote_translate result agrees _).mpr holds))
  | _, .mapsSome argument result, env, valuation, agrees, point => by
    change ((standardModel S).denote (all (imp (related .body)
      (ex (conj (.app (weaken₃ (translate argument)) (.var .vz)) (.app (weaken₃ (translate result)) applying)))))
      ((standardModel S).extend (σ := element) valuation (ULift.up point))).down ↔ _
    rw [denote_all]
    simp only [denote_imp _ (full S), denote_ex _ (full S), denote_conj _ (full S)]
    constructor
    · intro holds inner isBody
      obtain ⟨value, _, inArgument, inResult⟩ := holds (ULift.up inner) trivial isBody
      exact ⟨ULift.down value,
        (denote_translate argument agrees _).mp (Eq.mp (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _)) inArgument),
        (denote_translate result agrees _).mp (Eq.mp (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _)) inResult)⟩
    · intro holds inner _ isBody
      obtain ⟨value, inArgument, inResult⟩ := holds (ULift.down inner) isBody
      exact ⟨ULift.up value, trivial,
        Eq.mpr (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _)) ((denote_translate argument agrees _).mpr inArgument),
        Eq.mpr (congrArg ULift.down (denote_app_weaken₃ _ _ _ _ _ _)) ((denote_translate result agrees _).mpr inResult)⟩
  | _, .someOf type formula, _, valuation, agrees, point =>
    (denote_someWith _ _ valuation point).trans
      (exists_congr fun other => and_congr Iff.rfl (denote_translate formula agrees other))
  | _, .everyOf type formula, _, valuation, agrees, point =>
    (denote_everyWith _ _ valuation point).trans
      (forall_congr' fun other => imp_congr Iff.rfl (denote_translate formula agrees other))

/-- The existential reading of a constructor's arguments. -/
theorem denote_someParts : ∀ {n : ℕ} {Δ : Ctx (Base Unit)} (arguments : Formulas n) {env : Env Carrier n}
    (embed : Rename (Base Unit) (context n) Δ) {outer : (standardModel S).Valuation Δ},
    Agrees S (Soundness.renameVal (standardModel S) embed outer) env →
    ∀ relation : Term Constant Δ (relationTy arguments.length),
      ((standardModel S).denote (someParts arguments embed relation) outer).down ↔
        ∃ parts, applyList arguments.length ((standardModel S).denote relation outer) parts ∧
          S.satAll env arguments parts
  | _, _, .nil, _, _, outer, _, relation => by
    constructor
    · intro holds
      exact ⟨[], holds, trivial⟩
    · rintro ⟨parts, holds, all⟩
      cases parts with
      | nil => exact holds
      | cons _ _ => exact False.elim all
  | _, _, .cons formula formulas, env, embed, outer, agrees, relation => by
    change ((standardModel S).denote (ex (conj (atNewest (rename embed (translate formula)))
      (someParts formulas (fun index => .vs (embed index)) (atNewest relation)))) outer).down ↔ _
    rw [denote_ex _ (full S)]
    simp only [denote_conj _ (full S)]
    constructor
    · rintro ⟨first, _, holds, rest⟩
      obtain ⟨parts, applies, all⟩ := (denote_someParts formulas (fun index => .vs (embed index)) (agrees.shift first) _).mp rest
      exact ⟨ULift.down first :: parts, Eq.mp (applyList_congr (denote_atNewest relation outer first) parts) applies,
        (denote_translate formula agrees _).mp (Eq.mp (denote_renamed embed formula outer first) holds), all⟩
    · rintro ⟨parts, applies, all⟩
      cases parts with
      | nil => exact False.elim all
      | cons first parts =>
        exact ⟨ULift.up first, trivial,
          Eq.mpr (denote_renamed embed formula outer _) ((denote_translate formula agrees first).mpr all.1),
          (denote_someParts formulas (fun index => .vs (embed index)) (agrees.shift (ULift.up first)) _).mpr
            ⟨parts, Eq.mpr (applyList_congr (denote_atNewest relation outer _) parts) applies, all.2⟩⟩

/-- The universal reading of a constructor's arguments. -/
theorem denote_everyParts : ∀ {n : ℕ} {Δ : Ctx (Base Unit)} (arguments : Formulas n) {env : Env Carrier n}
    (embed : Rename (Base Unit) (context n) Δ) {outer : (standardModel S).Valuation Δ},
    Agrees S (Soundness.renameVal (standardModel S) embed outer) env →
    ∀ relation : Term Constant Δ (relationTy arguments.length),
      ((standardModel S).denote (everyParts arguments embed relation) outer).down ↔
        ∀ parts, applyList arguments.length ((standardModel S).denote relation outer) parts →
          S.satSome env arguments parts
  | _, _, .nil, _, _, outer, _, relation => by
    refine (Eq.to_iff (congrArg ULift.down (denote_neg (standardModel S) (full S) relation outer))).trans ?_
    constructor
    · intro fails parts applies
      cases parts with
      | nil => exact fails applies
      | cons _ _ => exact False.elim applies
    · intro holds applies
      exact holds [] applies
  | _, _, .cons formula formulas, env, embed, outer, agrees, relation => by
    change ((standardModel S).denote (all (disj (atNewest (rename embed (translate formula)))
      (everyParts formulas (fun index => .vs (embed index)) (atNewest relation)))) outer).down ↔ _
    rw [denote_all]
    simp only [denote_disj _ (full S)]
    constructor
    · intro holds parts applies
      cases parts with
      | nil => exact False.elim applies
      | cons first parts =>
        rcases holds (ULift.up first) trivial with inFormula | rest
        · exact Or.inl ((denote_translate formula agrees first).mp (Eq.mp (denote_renamed embed formula outer _) inFormula))
        · exact Or.inr ((denote_everyParts formulas (fun index => .vs (embed index)) (agrees.shift (ULift.up first)) _).mp rest parts
            (Eq.mpr (applyList_congr (denote_atNewest relation outer _) parts) applies))
    · intro holds first _
      by_cases inFormula : S.sat env formula (ULift.down first)
      · exact Or.inl (Eq.mpr (denote_renamed embed formula outer first) ((denote_translate formula agrees _).mpr inFormula))
      · refine Or.inr ((denote_everyParts formulas (fun index => .vs (embed index)) (agrees.shift first) _).mpr fun parts applies => ?_)
        exact (holds (ULift.down first :: parts)
          (Eq.mp (applyList_congr (denote_atNewest relation outer first) parts) applies)).resolve_left inFormula
end

/-- **A closed formula's translation holds exactly where the formula does.** -/
theorem denote_translate_closed (formula : Formula 0) (point : Carrier) :
    ((standardModel S).denote (translate formula) (nowhere (presentation S)) (ULift.up point)).down ↔
      S.sat Env.closed formula point :=
  denote_translate formula (agrees_closed _) point

end Denotation


/-! ## Built from the basis -/

section Basis

open Mettapedia.OSLF.Framework.NativeBasis (BasisOnly basisOnly_rename basisOnly_weaken basisOnly_weakenCtx
  basisOnly_truth basisOnly_applyClosed basisOnly_conj basisOnly_imp basisOnly_all basisOnly_ex)

variable {B : Type} {K : Ty B → Type} {Γ : Ctx B}

theorem basisOnly_disj (left right : Term K Γ .prop) :
    BasisOnly (disj left right) = (BasisOnly left && BasisOnly right) := by
  have : BasisOnly (disjunction : ClosedTerm K _) = true := by
    simp [disjunction, BasisOnly, basisOnly_all, basisOnly_imp]
  simp [disj, BasisOnly, basisOnly_applyClosed, this]

theorem basisOnly_falsity : BasisOnly (falsity : ClosedTerm K .prop) = true := by
  simp [falsity, BasisOnly, basisOnly_all]

theorem basisOnly_neg (proposition : Term K Γ .prop) : BasisOnly (neg proposition) = BasisOnly proposition := by
  have : BasisOnly (negation : ClosedTerm K _) = true := by
    simp [negation, BasisOnly, basisOnly_imp, basisOnly_falsity]
  simp [neg, basisOnly_applyClosed, this]

theorem basisOnly_countTerm : ∀ (count : ℕ) {Γ : Ctx (Base Unit)} (holds : Term Constant Γ predicate),
    BasisOnly holds = true → BasisOnly (countTerm count holds) = true
  | 0, _, _, _ => by simp [countTerm, basisOnly_weakenCtx, basisOnly_truth]
  | count + 1, _, holds, basis => by
    have rest := basisOnly_countTerm count (.lam (conj (atNewest (weaken holds)) (neg (related .same))))
      (by simp [BasisOnly, basisOnly_conj, basisOnly_neg, atNewest, related, basis])
    show BasisOnly (ex (conj (atNewest holds) (countTerm count _))) = true
    rw [basisOnly_ex, basisOnly_conj, rest]
    simp [atNewest, BasisOnly, basis]

theorem basisOnly_stepping {Γ : Ctx (Base Unit)} (direction : Direction) (label : StepLabel) :
    BasisOnly (stepping (Γ := Γ) direction label) = true := by
  cases direction <;> rfl

mutual
/-- **Every translation is built from the basis**: variables, constants, application, abstraction and
equality. -/
theorem basisOnly_translate : ∀ {n : ℕ} (formula : Formula n), BasisOnly (translate formula) = true
  | _, .top => by simp [translate, BasisOnly, basisOnly_weakenCtx, basisOnly_truth]
  | _, .bot => by simp [translate, BasisOnly, basisOnly_weakenCtx, basisOnly_falsity]
  | _, .and left right => by
    simp [translate, atNewest, BasisOnly, basisOnly_conj, basisOnly_translate left, basisOnly_translate right]
  | _, .or left right => by
    simp [translate, atNewest, BasisOnly, basisOnly_disj, basisOnly_translate left, basisOnly_translate right]
  | _, .var _ => rfl
  | _, .mu inner => by
    simp [translate, least, BasisOnly, basisOnly_all, basisOnly_imp, basisOnly_translate inner]
  | _, .nu inner => by
    simp [translate, greatest, BasisOnly, basisOnly_ex, basisOnly_conj, basisOnly_all, basisOnly_imp,
      basisOnly_translate inner]
  | _, .possibly _ formula | _, .sometimeBefore _ formula | _, .single _ formula | _, .body formula
  | _, .multiBody _ formula | _, .someOf _ formula => by
    simp [translate, someWith, related, relatedBack, holding, atNewest, BasisOnly, basisOnly_ex, basisOnly_conj,
      basisOnly_translate formula]
  | _, .necessarily _ formula | _, .alwaysBefore _ formula | _, .everySingle _ formula | _, .everyBody formula
  | _, .everyMultiBody _ formula | _, .everyOf _ formula => by
    simp [translate, everyWith, related, relatedBack, holding, atNewest, BasisOnly, basisOnly_all, basisOnly_imp,
      basisOnly_translate formula]
  | _, .atLeast _ direction _ formula => by
    simp only [translate, BasisOnly]
    exact basisOnly_countTerm _ _ (by simp [BasisOnly, basisOnly_conj, basisOnly_stepping, atNewest,
      basisOnly_translate formula])
  | _, .allButFewer _ direction _ formula => by
    simp only [translate, BasisOnly, basisOnly_neg]
    exact basisOnly_countTerm _ _ (by simp [BasisOnly, basisOnly_conj, basisOnly_neg, basisOnly_stepping, atNewest,
      basisOnly_translate formula])
  | _, .built _ arguments => by
    simp [translate, BasisOnly, basisOnly_someParts arguments, atNewest]
  | _, .everyBuilt _ arguments => by
    simp [translate, BasisOnly, basisOnly_everyParts arguments, atNewest]
  | _, .split _ left right => by
    simp [translate, splitting, BasisOnly, basisOnly_ex, basisOnly_conj, basisOnly_translate left,
      basisOnly_translate right]
  | _, .everySplit _ left right => by
    simp [translate, splitting, BasisOnly, basisOnly_all, basisOnly_imp, basisOnly_disj, basisOnly_translate left,
      basisOnly_translate right]
  | _, .empty _ | _, .bound _ | _, .typed _ | _, .is _ => rfl
  | _, .nonEmpty _ | _, .notBound _ | _, .untyped _ | _, .isNot _ => by
    simp [translate, holding, BasisOnly, basisOnly_neg]
  | _, .mapsAll argument result => by
    simp [translate, related, applying, BasisOnly, basisOnly_ex, basisOnly_conj, basisOnly_all, basisOnly_disj,
      basisOnly_translate argument, basisOnly_translate result]
  | _, .mapsSome argument result => by
    simp [translate, related, applying, BasisOnly, basisOnly_ex, basisOnly_conj, basisOnly_all, basisOnly_imp,
      basisOnly_translate argument, basisOnly_translate result]

theorem basisOnly_someParts : ∀ {n : ℕ} {Δ : Ctx (Base Unit)} (arguments : Formulas n)
    {embed : Rename (Base Unit) (context n) Δ} {relation : Term Constant Δ (relationTy arguments.length)},
    BasisOnly (someParts arguments embed relation) = BasisOnly relation
  | _, _, .nil, _, _ => rfl
  | _, _, .cons formula formulas, _, relation => by
    simp [someParts, atNewest, BasisOnly, basisOnly_ex, basisOnly_conj, basisOnly_rename, basisOnly_translate formula,
      basisOnly_someParts formulas]
    exact basisOnly_weaken relation

theorem basisOnly_everyParts : ∀ {n : ℕ} {Δ : Ctx (Base Unit)} (arguments : Formulas n)
    {embed : Rename (Base Unit) (context n) Δ} {relation : Term Constant Δ (relationTy arguments.length)},
    BasisOnly (everyParts arguments embed relation) = BasisOnly relation
  | _, _, .nil, _, relation => basisOnly_neg relation
  | _, _, .cons formula formulas, _, relation => by
    simp [everyParts, atNewest, BasisOnly, basisOnly_all, basisOnly_disj, basisOnly_rename,
      basisOnly_translate formula, basisOnly_everyParts formulas]
    exact basisOnly_weaken relation
end

end Basis


/-! ## Φ(L) stays in L's signature -/

section Signature

open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef)
open Mettapedia.GSLT.LanguageDef.WellSorted (OpenPatternWellSorted FreeTypeContext)

/-- **The relation constants a term mentions satisfy a predicate.** The legs of the step span are
always allowed. -/
def UsesOnly (allowed : ∀ {type : Ty (Base Unit)}, Symbol type → Prop) :
    {Γ : Ctx (Base Unit)} → {type : Ty (Base Unit)} → Term Constant Γ type → Prop
  | _, _, .var _ => True
  | _, _, .const (.op symbol) => allowed symbol
  | _, _, .const .source => True
  | _, _, .const .target => True
  | _, _, .app function argument => UsesOnly allowed function ∧ UsesOnly allowed argument
  | _, _, .lam body => UsesOnly allowed body
  | _, _, .top => True
  | _, _, .bot => True
  | _, _, .and left right => UsesOnly allowed left ∧ UsesOnly allowed right
  | _, _, .or left right => UsesOnly allowed left ∧ UsesOnly allowed right
  | _, _, .imp left right => UsesOnly allowed left ∧ UsesOnly allowed right
  | _, _, .not body => UsesOnly allowed body
  | _, _, .eq left right => UsesOnly allowed left ∧ UsesOnly allowed right
  | _, _, .all body => UsesOnly allowed body
  | _, _, .ex body => UsesOnly allowed body

variable {allowed : ∀ {type : Ty (Base Unit)}, Symbol type → Prop}

theorem usesOnly_rename : ∀ {Γ Δ : Ctx (Base Unit)} {type : Ty (Base Unit)} (relabel : Rename (Base Unit) Γ Δ)
    (term : Term Constant Γ type), UsesOnly allowed (rename relabel term) ↔ UsesOnly allowed term
  | _, _, _, _, .var _ => Iff.rfl
  | _, _, _, _, .const (.op _) => Iff.rfl
  | _, _, _, _, .const .source => Iff.rfl
  | _, _, _, _, .const .target => Iff.rfl
  | _, _, _, relabel, .app function argument => by
    simp only [rename, UsesOnly, usesOnly_rename relabel function, usesOnly_rename relabel argument]
  | _, _, _, relabel, .lam body => by simp only [rename, UsesOnly, usesOnly_rename (Rename.lift relabel) body]
  | _, _, _, _, .top => Iff.rfl
  | _, _, _, _, .bot => Iff.rfl
  | _, _, _, relabel, .and left right => by
    simp only [rename, UsesOnly, usesOnly_rename relabel left, usesOnly_rename relabel right]
  | _, _, _, relabel, .or left right => by
    simp only [rename, UsesOnly, usesOnly_rename relabel left, usesOnly_rename relabel right]
  | _, _, _, relabel, .imp left right => by
    simp only [rename, UsesOnly, usesOnly_rename relabel left, usesOnly_rename relabel right]
  | _, _, _, relabel, .not body => by simp only [rename, UsesOnly, usesOnly_rename relabel body]
  | _, _, _, relabel, .eq left right => by
    simp only [rename, UsesOnly, usesOnly_rename relabel left, usesOnly_rename relabel right]
  | _, _, _, relabel, .all body => by simp only [rename, UsesOnly, usesOnly_rename (Rename.lift relabel) body]
  | _, _, _, relabel, .ex body => by simp only [rename, UsesOnly, usesOnly_rename (Rename.lift relabel) body]

@[simp] theorem usesOnly_weaken {Γ : Ctx (Base Unit)} {σ type : Ty (Base Unit)} (term : Term Constant Γ type) :
    UsesOnly allowed (weaken (σ := σ) term) ↔ UsesOnly allowed term :=
  usesOnly_rename _ term

theorem usesOnly_weakenCtx {type : Ty (Base Unit)} :
    ∀ (Γ : Ctx (Base Unit)) (term : ClosedTerm Constant type), UsesOnly allowed (weakenCtx Γ term) ↔ UsesOnly allowed term
  | [], _ => Iff.rfl
  | _ :: Γ, term => by rw [weakenCtx_cons, usesOnly_weaken, usesOnly_weakenCtx Γ term]

section Connectives

variable {Γ : Ctx (Base Unit)}

theorem usesOnly_truth : UsesOnly allowed (truth : ClosedTerm Constant .prop) := by
  simp [truth, UsesOnly]

theorem usesOnly_falsity : UsesOnly allowed (falsity : ClosedTerm Constant .prop) := by
  simp [falsity, all, applyClosed, HOLLightBooleanDefinitions.universal, UsesOnly, usesOnly_truth]

@[simp] theorem usesOnly_conj (left right : Term Constant Γ .prop) :
    UsesOnly allowed (conj left right) ↔ UsesOnly allowed left ∧ UsesOnly allowed right := by
  have : UsesOnly allowed (HOLLightBooleanDefinitions.conjunction : ClosedTerm Constant _) := by
    simp [HOLLightBooleanDefinitions.conjunction, UsesOnly, usesOnly_truth]
  simp [conj, applyClosed, UsesOnly, usesOnly_weakenCtx, this]

@[simp] theorem usesOnly_imp (left right : Term Constant Γ .prop) :
    UsesOnly allowed (imp left right) ↔ UsesOnly allowed left ∧ UsesOnly allowed right := by
  have : UsesOnly allowed (HOLLightBooleanDefinitions.implication : ClosedTerm Constant _) := by
    simp [HOLLightBooleanDefinitions.implication, UsesOnly]
  simp [imp, applyClosed, UsesOnly, usesOnly_weakenCtx, this]

@[simp] theorem usesOnly_all {type : Ty (Base Unit)} (body : Term Constant (type :: Γ) .prop) :
    UsesOnly allowed (all body) ↔ UsesOnly allowed body := by
  have : UsesOnly allowed (HOLLightBooleanDefinitions.universal type : ClosedTerm Constant _) := by
    simp [HOLLightBooleanDefinitions.universal, UsesOnly, usesOnly_truth]
  simp [all, applyClosed, UsesOnly, usesOnly_weakenCtx, this]

@[simp] theorem usesOnly_ex {type : Ty (Base Unit)} (body : Term Constant (type :: Γ) .prop) :
    UsesOnly allowed (ex body) ↔ UsesOnly allowed body := by
  have : UsesOnly allowed (HOLLightBooleanDefinitions.existential type : ClosedTerm Constant _) := by
    simp [HOLLightBooleanDefinitions.existential, UsesOnly]
  simp [ex, applyClosed, UsesOnly, usesOnly_weakenCtx, this]

@[simp] theorem usesOnly_disj (left right : Term Constant Γ .prop) :
    UsesOnly allowed (disj left right) ↔ UsesOnly allowed left ∧ UsesOnly allowed right := by
  have : UsesOnly allowed (disjunction : ClosedTerm Constant _) := by
    simp [disjunction, UsesOnly]
  simp [disj, applyClosed, UsesOnly, usesOnly_weakenCtx, this]

@[simp] theorem usesOnly_neg (proposition : Term Constant Γ .prop) :
    UsesOnly allowed (neg proposition) ↔ UsesOnly allowed proposition := by
  have : UsesOnly allowed (negation : ClosedTerm Constant _) := by
    simp [negation, UsesOnly, usesOnly_falsity]
  simp [neg, applyClosed, UsesOnly, usesOnly_weakenCtx, this]

end Connectives

theorem usesOnly_stepping {Γ : Ctx (Base Unit)} (direction : Direction) (label : StepLabel) :
    UsesOnly allowed (stepping (Γ := Γ) direction label) ↔ allowed (.step label) := by
  cases direction <;> simp [stepping, related, relatedBack, UsesOnly]

theorem usesOnly_countTerm : ∀ (count : ℕ) {Γ : Ctx (Base Unit)} (holds : Term Constant Γ predicate),
    UsesOnly allowed holds → allowed .same → UsesOnly allowed (countTerm count holds)
  | 0, _, _, _, _ => by simp [countTerm, usesOnly_weakenCtx, usesOnly_truth]
  | count + 1, _, holds, uses, same => by
    have rest := usesOnly_countTerm count (.lam (conj (atNewest (weaken holds)) (neg (related .same))))
      (by simp [UsesOnly, atNewest, related, uses, same]) same
    show UsesOnly allowed (ex (conj (atNewest holds) (countTerm count _)))
    rw [usesOnly_ex, usesOnly_conj]
    exact ⟨by simp [atNewest, UsesOnly, uses], rest⟩

/-- **The relations a language provides**: steps of its rules and sites, its constructors at their
arities, the collection kinds it uses, bodies and application when it has binders, multi-bodies when it
has multi-binders, its types, and its closed well-sorted terms. -/
def Provides (language : LanguageDef) : {type : Ty (Base Unit)} → Symbol type → Prop
  | _, .step label => LabelOf language label
  | _, .built constructor arity => HasConstructor language constructor arity
  | _, .split kind => language.usesCollection kind = true
  | _, .empty kind => language.usesCollection kind = true
  | _, .single kind => language.usesCollection kind = true
  | _, .body => HasBinder language
  | _, .multiBody _ => HasMultiBinder language
  | _, .bound _ => HasBinder language ∨ HasMultiBinder language
  | _, .typed type => DeclaresType language type
  | _, .named term => ∃ type, OpenPatternWellSorted language FreeTypeContext.empty [] type term
  | _, .apply => HasBinder language
  | _, .same => True

mutual
/-- **Φ(L) translates into the logic of L's own signature**: the translation of a formula the language
generates mentions only relations the language provides. -/
theorem usesOnly_translate (language : LanguageDef) : ∀ {n : ℕ} (formula : Formula n),
    GeneratedBy language formula → UsesOnly (Provides language) (translate formula)
  | _, .top, _ => by simp [translate, UsesOnly, usesOnly_weakenCtx, usesOnly_truth]
  | _, .bot, _ => by simp [translate, UsesOnly, usesOnly_weakenCtx, usesOnly_falsity]
  | _, .and left right, generated | _, .or left right, generated => by
    simp [translate, atNewest, UsesOnly, usesOnly_translate language left generated.1,
      usesOnly_translate language right generated.2]
  | _, .var _, _ => trivial
  | _, .mu inner, generated | _, .nu inner, generated => by
    simp [translate, least, greatest, UsesOnly, usesOnly_translate language inner generated]
  | _, .possibly _ formula, generated | _, .necessarily _ formula, generated
  | _, .sometimeBefore _ formula, generated | _, .alwaysBefore _ formula, generated => by
    simp [translate, someWith, everyWith, related, relatedBack, atNewest, UsesOnly, Provides, generated.1,
      usesOnly_translate language formula generated.2]
  | _, .atLeast _ _ _ formula, generated => by
    simp only [translate, UsesOnly]
    exact usesOnly_countTerm _ _ (by simp [UsesOnly, usesOnly_stepping, Provides, generated.1, atNewest,
      usesOnly_translate language formula generated.2]) trivial
  | _, .allButFewer _ _ _ formula, generated => by
    simp only [translate, UsesOnly, usesOnly_neg]
    exact usesOnly_countTerm _ _ (by simp [UsesOnly, usesOnly_stepping, Provides, generated.1, atNewest,
      usesOnly_translate language formula generated.2]) trivial
  | _, .built _ arguments, generated => by
    simp only [translate, UsesOnly]
    exact usesOnly_someParts language arguments generated.2 ⟨generated.1, trivial⟩
  | _, .everyBuilt _ arguments, generated => by
    simp only [translate, UsesOnly]
    exact usesOnly_everyParts language arguments generated.2 ⟨generated.1, trivial⟩
  | _, .split _ left right, generated | _, .everySplit _ left right, generated => by
    simp [translate, splitting, UsesOnly, Provides, generated.1, usesOnly_translate language left generated.2.1,
      usesOnly_translate language right generated.2.2]
  | _, .empty _, generated | _, .nonEmpty _, generated => by
    simpa [translate, holding, UsesOnly, Provides, GeneratedBy] using generated
  | _, .single _ formula, generated | _, .everySingle _ formula, generated
  | _, .body formula, generated | _, .everyBody formula, generated
  | _, .multiBody _ formula, generated | _, .everyMultiBody _ formula, generated
  | _, .someOf _ formula, generated | _, .everyOf _ formula, generated => by
    simp [translate, someWith, everyWith, related, holding, atNewest, UsesOnly, Provides, generated.1,
      usesOnly_translate language formula generated.2]
  | _, .bound _, generated | _, .notBound _, generated | _, .typed _, generated | _, .untyped _, generated
  | _, .is _, generated | _, .isNot _, generated => by
    simpa [translate, holding, UsesOnly, Provides, GeneratedBy] using generated
  | _, .mapsAll argument result, generated | _, .mapsSome argument result, generated => by
    simp [translate, related, applying, UsesOnly, Provides, generated.1,
      usesOnly_translate language argument generated.2.1, usesOnly_translate language result generated.2.2]

theorem usesOnly_someParts (language : LanguageDef) : ∀ {n : ℕ} {Δ : Ctx (Base Unit)} (arguments : Formulas n)
    {embed : Rename (Base Unit) (context n) Δ} {relation : Term Constant Δ (relationTy arguments.length)},
    GeneratedByList language arguments → UsesOnly (Provides language) relation →
      UsesOnly (Provides language) (someParts arguments embed relation)
  | _, _, .nil, _, _, _, uses => uses
  | _, _, .cons formula formulas, _, relation, generated, uses => by
    simp only [someParts, usesOnly_ex, usesOnly_conj, atNewest, UsesOnly]
    exact ⟨⟨(usesOnly_weaken _).mpr ((usesOnly_rename _ _).mpr (usesOnly_translate language formula generated.1)),
      trivial⟩, usesOnly_someParts language formulas generated.2 ⟨(usesOnly_weaken relation).mpr uses, trivial⟩⟩

theorem usesOnly_everyParts (language : LanguageDef) : ∀ {n : ℕ} {Δ : Ctx (Base Unit)} (arguments : Formulas n)
    {embed : Rename (Base Unit) (context n) Δ} {relation : Term Constant Δ (relationTy arguments.length)},
    GeneratedByList language arguments → UsesOnly (Provides language) relation →
      UsesOnly (Provides language) (everyParts arguments embed relation)
  | _, _, .nil, _, relation, _, uses => (usesOnly_neg relation).mpr uses
  | _, _, .cons formula formulas, _, relation, generated, uses => by
    simp only [everyParts, usesOnly_all, usesOnly_disj, atNewest, UsesOnly]
    exact ⟨⟨(usesOnly_weaken _).mpr ((usesOnly_rename _ _).mpr (usesOnly_translate language formula generated.1)),
      trivial⟩, usesOnly_everyParts language formulas generated.2 ⟨(usesOnly_weaken relation).mpr uses, trivial⟩⟩
end

end Signature


/-! ## Agreement with the operators of the basis -/

section Operators

open Mettapedia.OSLF.Framework.NativeBasis (diamond forwardBox image pastBox lfp gfp denote_diamond
  denote_forwardBox denote_image denote_pastBox)
open Mettapedia.OSLF.Framework.DerivedModalities (derivedDiamond derivedForwardBox derivedImage derivedBox di ui pb)

variable {Carrier : Type} (S : NativeStructure Carrier)

/-- **The diamond of the step span is the generated modality** for all steps. -/
theorem diamond_eq_possibly (formula : Formula 0) :
    Mettapedia.OSLF.Framework.NativeBasis.apply (presentation S) diamond (S.sat Env.closed formula) =
      S.sat Env.closed (.possibly .any formula) := by
  rw [denote_diamond]
  funext point
  apply propext
  simp only [derivedDiamond, di, pb, Function.comp]
  constructor
  · rintro ⟨edge, starts, holds⟩
    exact ⟨edge.1.2, starts ▸ edge.2, holds⟩
  · rintro ⟨next, isStep, holds⟩
    exact ⟨⟨(point, next), isStep⟩, rfl, holds⟩

/-- **The forward box of the step span is the generated modality** for all steps. -/
theorem forwardBox_eq_necessarily (formula : Formula 0) :
    Mettapedia.OSLF.Framework.NativeBasis.apply (presentation S) forwardBox (S.sat Env.closed formula) =
      S.sat Env.closed (.necessarily .any formula) := by
  rw [denote_forwardBox]
  funext point
  apply propext
  simp only [derivedForwardBox, ui, pb, Function.comp]
  constructor
  · intro holds next isStep
    exact holds ⟨(point, next), isStep⟩ rfl
  · intro holds edge starts
    exact holds edge.1.2 (starts ▸ edge.2)

/-- **The image of the step span is the generated past modality** for all steps. -/
theorem image_eq_sometimeBefore (formula : Formula 0) :
    Mettapedia.OSLF.Framework.NativeBasis.apply (presentation S) image (S.sat Env.closed formula) =
      S.sat Env.closed (.sometimeBefore .any formula) := by
  rw [denote_image]
  funext point
  apply propext
  simp only [derivedImage, di, pb, Function.comp]
  constructor
  · rintro ⟨edge, ends, holds⟩
    exact ⟨edge.1.1, ends ▸ edge.2, holds⟩
  · rintro ⟨previous, isStep, holds⟩
    exact ⟨⟨(previous, point), isStep⟩, rfl, holds⟩

/-- **The past box of the step span is the generated past modality** for all steps. -/
theorem pastBox_eq_alwaysBefore (formula : Formula 0) :
    Mettapedia.OSLF.Framework.NativeBasis.apply (presentation S) pastBox (S.sat Env.closed formula) =
      S.sat Env.closed (.alwaysBefore .any formula) := by
  rw [denote_pastBox]
  funext point
  apply propext
  simp only [derivedBox, ui, pb, Function.comp]
  constructor
  · intro holds previous isStep
    exact holds ⟨(previous, point), isStep⟩ rfl
  · intro holds edge ends
    exact holds edge.1.1 (ends ▸ edge.2)

/-- **For closed formulas, the least fixed point translates to the basis's `lfp`.** -/
theorem translate_mu (inner : Formula 1) : translate (.mu inner) = lfp (.lam (translate inner)) := rfl

/-- **For closed formulas, the greatest fixed point translates to the basis's `gfp`.** -/
theorem translate_nu (inner : Formula 1) : translate (.nu inner) = gfp (.lam (translate inner)) := rfl

end Operators

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.HigherOrder
