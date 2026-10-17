import Mettapedia.TypeTheory.BubbleJoinCongruence

/-!
# When decisions of bubbles compose

`join_normalizedBy` reduces the decision of a join to one obligation: the
first normal form must respect the second bubble.  This module discharges the
obligation for the arithmetic recursion bubble against every bubble that is
rigid and compatible for it, and shows that each hypothesis is load-bearing.

**The general theorem.**  The arithmetic normal form inspects only shapes
headed by an arithmetic constant: a numeral `0`, a successor application, a
partial sum.  A bubble is *rigid for arithmetic* when none of its redexes and
none of its contracta is headed by an arithmetic constant (`ArithmeticRigid`),
and *compatible* when the arithmetic normal form sends each of its root
instances to a step of the bubble (`ArithmeticCompatible`).  The arithmetic
normal form respects every rigid, compatible bubble
(`norm_respects_of_rigid`), so the join is decided by the arithmetic normal
form followed by the bubble's own (`join_rule_normalizedBy_of_rigid`).
Disjointness gives rigidity for non-collapsing bubbles: redexes and contracta
rooted in symbols outside the arithmetic constants (`rigid_of_rootedIn`).
Normal forms that contract at the root of every node normalize their bubble
once the contraction is a conversion and every root step keeps them
(`bottomUp_normalizedBy`).

**The instances.**
* `¬⊤ ↦ ⊥`: the existing positive control is an instance.
* `t = t ↦ ⊤`, a non-left-linear rule disjoint from arithmetic
  (`rule_eqRefl_disjoint`): normalizing the arithmetic aliens first decides the
  join (`arith_eqRefl_normalizedBy`), because equal aliens have equal normal
  forms; testing equality first fails (`eqRefl_first_not_normalizedBy`).
* `p ∧ ⊤ ↦ p`, a collapsing rule disjoint from arithmetic
  (`rule_andTop_disjoint`): the collapse can produce a numeral, so the bubble is
  not rigid (`andTop_not_rigid`), and no normal form of it composes after
  arithmetic (`andTop_after_arith_not_normalizedBy`).  Disjointness of symbols
  alone does not make decisions compose.
* **Typed joins.**  The same collapse at sorts other than the numerals,
  `p ∧ ⊤ ↦ p` for `p` not headed by an arithmetic constant, is rigid and
  compatible, and the join is decided (`arith_sortedAndTop_normalizedBy`).
  Sorts buy what disjointness cannot: the collapse stays inside sorts that the
  other normal form never inspects.
* `a = b ↦ ⊥` for syntactically distinct `a` and `b`: rigid and disjoint
  (`rule_distinct_disjoint`), but the arithmetic normal form turns the redex
  `x + 0 = x` into `x = x`, which is no redex (`distinct_not_compatible`), and
  no normal form of the rule composes after arithmetic
  (`distinct_after_arith_not_normalizedBy`).
* `t + 0 ↦ 0 + t` shares the constant of addition and is not rigid
  (`zeroSwap_not_rigid`); its failure of respect is
  `norm_false_not_respects_zeroSwap`.
* The failures quantify over normal forms of the second bubble.  Without that
  hypothesis some function always composes after arithmetic: a normal form of
  the join itself (`exists_composite_after_arith`).

**What follows from what.**  The ordered-results transport of a structural
coproduct is an exact embedding of step relations.  An exact embedding
conserves normal forms and every may- and must-observation; it conserves
conversion when the larger step relation is confluent, and not otherwise
(`ExtensionConservativity`).  Conversely a bubble forgets the order and the
multiplicity of results: declaring every rewrite row twice keeps the bubble
and changes every nonempty ordered result (`doubled_rows_same_bubble`,
`oneRow_fires`), so no statement about bubbles implies one about ordered
results.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleJoinDisjoint

open Relation
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.BubbleJoinCongruence
open Mettapedia.TypeTheory.BubbleJoinCongruence.Arith
open Expr

/-! ## Heads and rigidity -/

/-- The symbol heading the application spine of an expression; a variable
heads nothing. -/
def spineHead : AExpr → Option (ExprSymbol Unit ArithConst)
  | .bvar _ => none
  | .univ => some .univ
  | .prop => some .prop
  | .base b => some (.base b)
  | .pi _ _ => some .pi
  | .lam _ _ => some .lam
  | .app f _ => spineHead f
  | .const τ c => some (.const τ c)
  | .tyFam b => some (.tyFam b)
  | .top => some .top
  | .bot => some .bot
  | .and _ _ => some .and
  | .or _ _ => some .or
  | .imp _ _ => some .imp
  | .not _ => some .not
  | .eq _ _ => some .eq
  | .all _ _ => some .all
  | .ex _ _ => some .ex

/-- Headed by an arithmetic constant. -/
def ArithmeticHeaded (expression : AExpr) : Prop :=
  ∃ (τ : Ty Unit) (c : ArithConst τ), spineHead expression = some (.const τ c)

/-- **Rigid for arithmetic**: no redex and no contractum of the bubble is
headed by an arithmetic constant. -/
def ArithmeticRigid (rules : AExpr → AExpr → Prop) : Prop :=
  ∀ redex contractum, rules redex contractum →
    ¬ ArithmeticHeaded redex ∧ ¬ ArithmeticHeaded contractum

/-- The arithmetic normal form sends each root instance of the bubble to a
step of the bubble. -/
def ArithmeticCompatible (rules : AExpr → AExpr → Prop) : Prop :=
  ∀ redex contractum, rules redex contractum →
    Rewrite rules (norm false redex) (norm false contractum)

/-- **Disjoint and non-collapsing implies rigid.**  A bubble whose redexes and
whose contracta are rooted in a set of symbols containing no arithmetic
constant is rigid. -/
theorem rigid_of_rootedIn {rules : AExpr → AExpr → Prop}
    {symbols : Set (ExprSymbol Unit ArithConst)}
    (disjoint : ∀ (τ : Ty Unit) (c : ArithConst τ), ExprSymbol.const τ c ∉ symbols)
    (redexes : RootedIn spineHead rules symbols)
    (contracta : RootedIn spineHead (flip rules) symbols) :
    ArithmeticRigid rules := by
  intro redex contractum rule
  obtain ⟨redexSymbol, redexMember, redexHead⟩ := redexes _ _ rule
  obtain ⟨contractumSymbol, contractumMember, contractumHead⟩ := contracta _ _ rule
  constructor
  · rintro ⟨τ, c, arithmetic⟩
    rw [redexHead, Option.some.injEq] at arithmetic
    exact disjoint τ c (arithmetic ▸ redexMember)
  · rintro ⟨τ, c, arithmetic⟩
    rw [contractumHead, Option.some.injEq] at arithmetic
    exact disjoint τ c (arithmetic ▸ contractumMember)

section Rigid

variable {rules : AExpr → AExpr → Prop} (rigid : ArithmeticRigid rules)
include rigid

/-- Nothing steps out of a constant. -/
theorem not_rewrite_from_const {τ : Ty Unit} {c : ArithConst τ} {target : AExpr} :
    ¬ Rewrite rules (.const τ c) target := by
  intro stepped
  cases stepped with
  | root rule => exact (rigid _ _ rule).1 ⟨τ, c, rfl⟩

/-- Nothing steps into a constant. -/
theorem not_rewrite_to_const {τ : Ty Unit} {c : ArithConst τ} {source : AExpr} :
    ¬ Rewrite rules source (.const τ c) := by
  intro stepped
  cases stepped with
  | root rule => exact (rigid _ _ rule).2 ⟨τ, c, rfl⟩

/-- A step out of an applied constant moves only the argument. -/
theorem rewrite_from_app_const {τ : Ty Unit} {c : ArithConst τ} {argument target : AExpr}
    (stepped : Rewrite rules (.app (.const τ c) argument) target) :
    ∃ argument', target = .app (.const τ c) argument' ∧ Rewrite rules argument argument' := by
  cases stepped with
  | root rule => exact absurd ⟨τ, c, rfl⟩ (rigid _ _ rule).1
  | appFunction inner => exact absurd inner (not_rewrite_from_const rigid)
  | appArgument inner => exact ⟨_, rfl, inner⟩

/-- A step into an applied constant moved only the argument. -/
theorem rewrite_to_app_const {τ : Ty Unit} {c : ArithConst τ} {source argument' : AExpr}
    (stepped : Rewrite rules source (.app (.const τ c) argument')) :
    ∃ argument, source = .app (.const τ c) argument ∧ Rewrite rules argument argument' := by
  cases stepped with
  | root rule => exact absurd ⟨τ, c, rfl⟩ (rigid _ _ rule).2
  | appFunction inner => exact absurd inner (not_rewrite_to_const rigid)
  | appArgument inner => exact ⟨_, rfl, inner⟩

end Rigid

/-! ## The arithmetic normal form respects rigid bubbles -/

/-- Recursion addition falls through to a sum on every second summand that is
neither the numeral zero nor a successor application. -/
theorem addNorm_eq_addE {x y : AExpr} (notZero : y ≠ zeroE)
    (notSucc : ∀ argument, y ≠ succE argument) :
    addNorm x y = addE x y := by
  cases y with
  | const τ c =>
      cases c with
      | zero => exact absurd rfl notZero
      | succ => rfl
      | add => rfl
  | app f a =>
      cases f with
      | const τ c =>
          cases c with
          | succ => exact absurd rfl (notSucc a)
          | zero => rfl
          | add => rfl
      | _ => rfl
  | _ => rfl

/-- Application of normal forms falls through on every function that is not a
partial sum. -/
theorem appNorm_eq_app {f a : AExpr}
    (notAdd : ∀ x, f ≠ .app (.const _ .add) x) :
    appNorm false f a = .app f a := by
  cases f with
  | app g x =>
      cases g with
      | const τ c =>
          cases c with
          | add => exact absurd rfl (notAdd x)
          | zero => rfl
          | succ => rfl
      | _ => rfl
  | _ => rfl

section Respect

variable {rules : AExpr → AExpr → Prop}

/-- Recursion addition carries a step in its first summand, for any bubble. -/
theorem addNorm_left {x x' : AExpr} (stepped : Rewrite rules x x') :
    ∀ y, Rewrite rules (addNorm x y) (addNorm x' y) := by
  intro y
  induction y with
  | const τ c =>
      cases c with
      | zero => exact stepped
      | succ => exact .appFunction (.appArgument stepped)
      | add => exact .appFunction (.appArgument stepped)
  | app f a _ argumentHypothesis =>
      cases f with
      | const τ c =>
          cases c with
          | succ => exact .appArgument argumentHypothesis
          | zero => exact .appFunction (.appArgument stepped)
          | add => exact .appFunction (.appArgument stepped)
      | _ => exact .appFunction (.appArgument stepped)
  | _ => exact .appFunction (.appArgument stepped)

variable (rigid : ArithmeticRigid rules)
include rigid

/-- A step between second summands keeps the shape that recursion addition
inspects. -/
private theorem shape_of_step {y y' : AExpr} (stepped : Rewrite rules y y')
    (notSuccSource : ∀ argument, y ≠ succE argument) :
    y ≠ zeroE ∧ y' ≠ zeroE ∧ ∀ argument, y' ≠ succE argument := by
  refine ⟨fun same => ?_, fun same => ?_, fun argument same => ?_⟩
  · subst same
    exact not_rewrite_from_const rigid stepped
  · subst same
    exact not_rewrite_to_const rigid stepped
  · subst same
    obtain ⟨source, sourceEq, _⟩ := rewrite_to_app_const rigid stepped
    exact notSuccSource source sourceEq

/-- **Recursion addition carries a rigid step in its second summand.**  The case
split on the head of the summand is structural, so no decision of equality of
expressions is needed. -/
theorem addNorm_right (x : AExpr) :
    ∀ {y y' : AExpr}, Rewrite rules y y' → Rewrite rules (addNorm x y) (addNorm x y') := by
  intro y
  induction y with
  | app f a _ argumentHypothesis =>
      intro y' stepped
      have fallthrough : (∀ argument, Expr.app f a ≠ succE argument) →
          Rewrite rules (addNorm x (.app f a)) (addNorm x y') := by
        intro notSucc
        obtain ⟨notZero, notZero', notSucc'⟩ := shape_of_step rigid stepped notSucc
        rw [addNorm_eq_addE notZero notSucc, addNorm_eq_addE notZero' notSucc']
        exact .appArgument stepped
      cases f with
      | const τ c =>
          cases c with
          | succ =>
              obtain ⟨a', rfl, inner⟩ := rewrite_from_app_const rigid stepped
              exact .appArgument (argumentHypothesis inner)
          | zero => exact fallthrough fun _ same => by cases same
          | add => exact fallthrough fun _ same => by cases same
      | _ => exact fallthrough fun _ same => by cases same
  | _ =>
      intro y' stepped
      obtain ⟨notZero, notZero', notSucc'⟩ :=
        shape_of_step rigid stepped (fun argument same => by cases same)
      rw [addNorm_eq_addE notZero (fun argument same => by cases same),
        addNorm_eq_addE notZero' notSucc']
      exact .appArgument stepped

/-- **Application of normal forms carries a rigid step in its function.** -/
theorem appNorm_function {f f' : AExpr} (stepped : Rewrite rules f f') (a : AExpr) :
    Rewrite rules (appNorm false f a) (appNorm false f' a) := by
  have fallthrough : (∀ x, f ≠ .app (.const _ .add) x) →
      Rewrite rules (appNorm false f a) (appNorm false f' a) := by
    intro notAdd
    have notAdd' : ∀ x, f' ≠ .app (.const _ .add) x := by
      intro x same
      subst same
      obtain ⟨source, sourceEq, _⟩ := rewrite_to_app_const rigid stepped
      exact notAdd source sourceEq
    rw [appNorm_eq_app notAdd, appNorm_eq_app notAdd']
    exact .appFunction stepped
  cases f with
  | app g x =>
      cases g with
      | const τ c =>
          cases c with
          | add =>
              obtain ⟨x', rfl, inner⟩ := rewrite_from_app_const rigid stepped
              exact addNorm_left inner a
          | zero => exact fallthrough fun _ same => by cases same
          | succ => exact fallthrough fun _ same => by cases same
      | _ => exact fallthrough fun _ same => by cases same
  | _ => exact fallthrough fun _ same => by cases same

/-- **Application of normal forms carries a rigid step in its argument.** -/
theorem appNorm_argument (f : AExpr) {a a' : AExpr} (stepped : Rewrite rules a a') :
    Rewrite rules (appNorm false f a) (appNorm false f a') := by
  cases f with
  | app g x =>
      cases g with
      | const τ c =>
          cases c with
          | add => exact addNorm_right rigid x stepped
          | zero => exact .appArgument stepped
          | succ => exact .appArgument stepped
      | _ => exact .appArgument stepped
  | _ => exact .appArgument stepped

/-- **The arithmetic normal form sends every step of a rigid, compatible bubble
to a step of the bubble.** -/
theorem rewrite_norm (compatible : ArithmeticCompatible rules) {e e' : AExpr}
    (stepped : Rewrite rules e e') : Rewrite rules (norm false e) (norm false e') := by
  induction stepped with
  | root rule => exact compatible _ _ rule
  | piDomain _ ih => exact .piDomain ih
  | piBody _ ih => exact .piBody ih
  | lamDomain _ ih => exact .lamDomain ih
  | lamBody _ ih => exact .lamBody ih
  | @appFunction f f' a _ ih => exact appNorm_function rigid ih (norm false a)
  | @appArgument f a a' _ ih => exact appNorm_argument rigid (norm false f) ih
  | andLeft _ ih => exact .andLeft ih
  | andRight _ ih => exact .andRight ih
  | orLeft _ ih => exact .orLeft ih
  | orRight _ ih => exact .orRight ih
  | impLeft _ ih => exact .impLeft ih
  | impRight _ ih => exact .impRight ih
  | notBody _ ih => exact .notBody ih
  | eqLeft _ ih => exact .eqLeft ih
  | eqRight _ ih => exact .eqRight ih
  | allDomain _ ih => exact .allDomain ih
  | allBody _ ih => exact .allBody ih
  | exDomain _ ih => exact .exDomain ih
  | exBody _ ih => exact .exBody ih

/-- The arithmetic normal form respects a rigid, compatible bubble. -/
theorem norm_respects_of_rigid (compatible : ArithmeticCompatible rules) :
    ∀ e e', Convertible rules e e' → Convertible rules (norm false e) (norm false e') := by
  intro e e' converted
  induction converted with
  | rel _ _ stepped => exact EqvGen.rel _ _ (rewrite_norm rigid compatible stepped)
  | refl => exact EqvGen.refl _
  | symm _ _ _ ih => exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ first second => exact EqvGen.trans _ _ _ first second

/-- **The general composition theorem.**  The join of the arithmetic recursion
bubble with any rigid, compatible bubble normalized by its own function is
normalized by the arithmetic normal form followed by that function; this
decides the join's conversion when that function is computable.  The proof
splits on the heads of terms structurally and uses no choice. -/
theorem join_rule_normalizedBy_of_rigid (compatible : ArithmeticCompatible rules)
    {normal : AExpr → AExpr} (bySecond : NormalizedBy rules normal) :
    NormalizedBy (join Rule rules) (fun e => normal (norm false e)) :=
  join_normalizedBy rule_normalizedBy bySecond (norm_respects_of_rigid rigid compatible)

end Respect

/-- Without the second normal form, the composite need not decide even a rigid,
compatible join: the arithmetic normal form alone misses `¬⊤ ~ ⊥`. -/
example : ¬ NormalizedBy (join Rule NotTop) (norm false) := by
  intro normalized
  have equal := normalized.2 _ _
    (convertible_join_right (Relation.EqvGen.rel _ _ (.root NotTop.notTop)) :
      Convertible (join Rule NotTop) (.not .top) .bot)
  cases equal

/-- Without asking the second function to normalize the second bubble, some
function always composes after arithmetic: a normal form of the join itself. -/
theorem exists_composite_after_arith (second : AExpr → AExpr → Prop) :
    ∃ normal : AExpr → AExpr,
      NormalizedBy (join Rule second) (fun e => normal (norm false e)) := by
  obtain ⟨normal, normalized⟩ :=
    CongruenceClosure.exists_normalizedBy (closure := exprClosure) (join Rule second)
  have reaches : ∀ e, Convertible (join Rule second) e (norm false e) :=
    fun e => convertible_join_left (norm_reachable false e)
  refine ⟨normal, fun e => EqvGen.trans _ _ _ (reaches e) (normalized.1 _),
    fun e e' converted => normalized.2 _ _ ?_⟩
  exact EqvGen.trans _ _ _ (EqvGen.symm _ _ (reaches e)) (EqvGen.trans _ _ _ converted (reaches e'))

/-! ## Normal forms that contract at the root of every node -/

/-- Rebuild every node from the normal forms of its children, then contract at
its root. -/
def bottomUp (contract : AExpr → AExpr) : AExpr → AExpr
  | .bvar i => contract (.bvar i)
  | .univ => contract .univ
  | .prop => contract .prop
  | .base b => contract (.base b)
  | .pi A B => contract (.pi (bottomUp contract A) (bottomUp contract B))
  | .lam A b => contract (.lam (bottomUp contract A) (bottomUp contract b))
  | .app f a => contract (.app (bottomUp contract f) (bottomUp contract a))
  | .const τ c => contract (.const τ c)
  | .tyFam b => contract (.tyFam b)
  | .top => contract .top
  | .bot => contract .bot
  | .and p q => contract (.and (bottomUp contract p) (bottomUp contract q))
  | .or p q => contract (.or (bottomUp contract p) (bottomUp contract q))
  | .imp p q => contract (.imp (bottomUp contract p) (bottomUp contract q))
  | .not p => contract (.not (bottomUp contract p))
  | .eq a b => contract (.eq (bottomUp contract a) (bottomUp contract b))
  | .all A b => contract (.all (bottomUp contract A) (bottomUp contract b))
  | .ex A b => contract (.ex (bottomUp contract A) (bottomUp contract b))

section BottomUp

variable {rules : AExpr → AExpr → Prop} {contract : AExpr → AExpr}

/-- A step keeps the bottom-up normal form once every root step keeps it. -/
theorem rewrite_bottomUp
    (keeps : ∀ redex contractum, rules redex contractum →
      bottomUp contract redex = bottomUp contract contractum)
    {e e' : AExpr} (stepped : Rewrite rules e e') : bottomUp contract e = bottomUp contract e' := by
  induction stepped with
  | root rule => exact keeps _ _ rule
  | piDomain _ ih => simp only [bottomUp, ih]
  | piBody _ ih => simp only [bottomUp, ih]
  | lamDomain _ ih => simp only [bottomUp, ih]
  | lamBody _ ih => simp only [bottomUp, ih]
  | appFunction _ ih => simp only [bottomUp, ih]
  | appArgument _ ih => simp only [bottomUp, ih]
  | andLeft _ ih => simp only [bottomUp, ih]
  | andRight _ ih => simp only [bottomUp, ih]
  | orLeft _ ih => simp only [bottomUp, ih]
  | orRight _ ih => simp only [bottomUp, ih]
  | impLeft _ ih => simp only [bottomUp, ih]
  | impRight _ ih => simp only [bottomUp, ih]
  | notBody _ ih => simp only [bottomUp, ih]
  | eqLeft _ ih => simp only [bottomUp, ih]
  | eqRight _ ih => simp only [bottomUp, ih]
  | allDomain _ ih => simp only [bottomUp, ih]
  | allBody _ ih => simp only [bottomUp, ih]
  | exDomain _ ih => simp only [bottomUp, ih]
  | exBody _ ih => simp only [bottomUp, ih]

/-- **A root contraction that is a conversion, and whose bottom-up normal form
every root step keeps, normalizes the bubble.** -/
theorem bottomUp_normalizedBy (reaches : ∀ e, Convertible rules e (contract e))
    (keeps : ∀ redex contractum, rules redex contractum →
      bottomUp contract redex = bottomUp contract contractum) :
    NormalizedBy rules (bottomUp contract) := by
  refine ⟨fun e => ?_, fun e e' converted => ?_⟩
  · induction e with
    | pi A B ihA ihB =>
        exact EqvGen.trans _ _ _
          (convertible_two pi (fun step => .piDomain step) (fun step => .piBody step) ihA ihB)
          (reaches _)
    | lam A b ihA ihb =>
        exact EqvGen.trans _ _ _
          (convertible_two lam (fun step => .lamDomain step) (fun step => .lamBody step) ihA ihb)
          (reaches _)
    | app f a ihf iha =>
        exact EqvGen.trans _ _ _
          (convertible_two app (fun step => .appFunction step) (fun step => .appArgument step)
            ihf iha)
          (reaches _)
    | and p q ihp ihq =>
        exact EqvGen.trans _ _ _
          (convertible_two Expr.and (fun step => .andLeft step) (fun step => .andRight step)
            ihp ihq)
          (reaches _)
    | or p q ihp ihq =>
        exact EqvGen.trans _ _ _
          (convertible_two Expr.or (fun step => .orLeft step) (fun step => .orRight step) ihp ihq)
          (reaches _)
    | imp p q ihp ihq =>
        exact EqvGen.trans _ _ _
          (convertible_two imp (fun step => .impLeft step) (fun step => .impRight step) ihp ihq)
          (reaches _)
    | not p ihp =>
        exact EqvGen.trans _ _ _ (convertible_lift Expr.not (fun step => .notBody step) ihp)
          (reaches _)
    | eq a b iha ihb =>
        exact EqvGen.trans _ _ _
          (convertible_two Expr.eq (fun step => .eqLeft step) (fun step => .eqRight step) iha ihb)
          (reaches _)
    | all A b ihA ihb =>
        exact EqvGen.trans _ _ _
          (convertible_two all (fun step => .allDomain step) (fun step => .allBody step) ihA ihb)
          (reaches _)
    | ex A b ihA ihb =>
        exact EqvGen.trans _ _ _
          (convertible_two ex (fun step => .exDomain step) (fun step => .exBody step) ihA ihb)
          (reaches _)
    | _ => exact reaches _
  · induction converted with
    | rel _ _ stepped => exact rewrite_bottomUp keeps stepped
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second

end BottomUp

/-- A term with no step in or out is convertible only to itself. -/
private theorem eqvGen_isolated {α : Type} {r : α → α → Prop} {a : α}
    (noOut : ∀ b, ¬ r a b) (noIn : ∀ b, ¬ r b a) {b : α} (converted : EqvGen r a b) :
    b = a := by
  have sameSide : ∀ c d, EqvGen r c d → (c = a ↔ d = a) := by
    intro c d related
    induction related with
    | rel c d stepped =>
        constructor
        · rintro rfl
          exact absurd stepped (noOut d)
        · rintro rfl
          exact absurd stepped (noIn c)
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second
  exact (sameSide a b converted).mp rfl

/-! ## Instances and controls -/

/-! ### A logical bubble: `¬⊤ ↦ ⊥` -/

theorem notTop_rigid : ArithmeticRigid NotTop :=
  rigid_of_rootedIn const_not_logical
    (fun _ _ rule => by cases rule; exact ⟨.not, rfl, rfl⟩)
    (fun _ _ rule => by cases rule; exact ⟨.bot, rfl, rfl⟩)

theorem notTop_compatible : ArithmeticCompatible NotTop := by
  intro redex contractum rule
  cases rule
  exact .root NotTop.notTop

/-! ### A non-left-linear rule: `t = t ↦ ⊤` -/

/-- Reflexivity of equality: the redex repeats its variable. -/
inductive EqRefl : AExpr → AExpr → Prop where
  | refl (t : AExpr) : EqRefl (.eq t t) .top

/-- The reflexivity rule as one schema. -/
def eqReflSchemas : Unit → AExpr → AExpr → Prop :=
  fun _ redex contractum => ∃ t, redex = .eq t t ∧ contractum = .top

theorem eqRefl_presented : Presented eqReflSchemas = EqRefl := by
  funext redex contractum
  apply propext
  constructor
  · rintro ⟨_, t, rfl, rfl⟩
    exact EqRefl.refl t
  · intro rule
    cases rule with
    | refl t => exact ⟨(), t, rfl, rfl⟩

/-- **The reflexivity bubble is disjoint from arithmetic.** -/
theorem rule_eqRefl_disjoint :
    Disjoint (Signature ExprOccurs ruleSchemas) (Signature ExprOccurs eqReflSchemas) :=
  rule_disjoint_of_logical
    (signature_subset fun _ _ => ⟨_, _, ⟨.bvar 0, rfl, rfl⟩, logical_of_symbols rfl⟩)

open Classical in
/-- Equality with its reflexive instances contracted. -/
noncomputable def contractEq : AExpr → AExpr
  | .eq a b => if a = b then .top else .eq a b
  | e => e

theorem eqRefl_normalizedBy : NormalizedBy EqRefl (bottomUp contractEq) := by
  apply bottomUp_normalizedBy
  · intro e
    cases e with
    | eq a b =>
        by_cases same : a = b
        · subst same
          simp only [contractEq]
          exact EqvGen.rel _ _ (.root (EqRefl.refl a))
        · simp only [contractEq, if_neg same]
          exact EqvGen.refl _
    | _ => exact EqvGen.refl _
  · intro redex contractum rule
    cases rule with
    | refl t => simp [bottomUp, contractEq]

theorem eqRefl_rigid : ArithmeticRigid EqRefl :=
  rigid_of_rootedIn const_not_logical
    (fun _ _ rule => by cases rule; exact ⟨.eq, rfl, rfl⟩)
    (fun _ _ rule => by cases rule; exact ⟨.top, rfl, rfl⟩)

/-- The arithmetic normal form sends reflexive equations to reflexive
equations: equal aliens have equal normal forms. -/
theorem eqRefl_compatible : ArithmeticCompatible EqRefl := by
  intro redex contractum rule
  cases rule with
  | refl t => exact .root (EqRefl.refl (norm false t))

/-- **A non-left-linear rule beside arithmetic.**  Normalizing the arithmetic
aliens first, then testing equality, decides the join. -/
theorem arith_eqRefl_normalizedBy :
    NormalizedBy (join Rule EqRefl) (fun e => bottomUp contractEq (norm false e)) :=
  join_rule_normalizedBy_of_rigid eqRefl_rigid eqRefl_compatible eqRefl_normalizedBy

/-- The other order fails: testing equality before normalizing the aliens
misses `x + 0 = x`. -/
theorem eqRefl_first_not_normalizedBy :
    ¬ NormalizedBy (join Rule EqRefl) (fun e => norm false (bottomUp contractEq e)) := by
  intro normalized
  have converted : Convertible (join Rule EqRefl) (.eq (addE (.bvar 0) zeroE) (.bvar 0)) .top :=
    EqvGen.trans _ _ _
      (EqvGen.rel _ _ (.eqLeft (.root (Or.inl (Rule.addZero (.bvar 0))))))
      (EqvGen.rel _ _ (.root (Or.inr (EqRefl.refl (.bvar 0)))))
  have equal := normalized.2 _ _ converted
  simp [bottomUp, contractEq, addE, zeroE, norm, appNorm, addNorm] at equal

/-! ### A collapsing rule: `p ∧ ⊤ ↦ p` -/

/-- Conjunction with truth collapses to its first conjunct. -/
inductive AndTop : AExpr → AExpr → Prop where
  | andTop (p : AExpr) : AndTop (.and p .top) p

/-- The collapsing rule as one schema. -/
def andTopSchemas : Unit → AExpr → AExpr → Prop :=
  fun _ redex contractum => ∃ p, redex = .and p .top ∧ contractum = p

theorem andTop_presented : Presented andTopSchemas = AndTop := by
  funext redex contractum
  apply propext
  constructor
  · rintro ⟨_, p, rfl, rfl⟩
    exact AndTop.andTop _
  · intro rule
    cases rule with
    | andTop => exact ⟨(), _, rfl, rfl⟩

/-- **The collapsing bubble is disjoint from arithmetic**, symbol by symbol. -/
theorem rule_andTop_disjoint :
    Disjoint (Signature ExprOccurs ruleSchemas) (Signature ExprOccurs andTopSchemas) :=
  rule_disjoint_of_logical
    (signature_subset fun _ _ => ⟨_, _, ⟨.bvar 0, rfl, rfl⟩, logical_of_symbols rfl⟩)

/-- Conjunction with truth contracted. -/
def contractAnd : AExpr → AExpr
  | .and p .top => p
  | e => e

theorem andTop_normalizedBy : NormalizedBy AndTop (bottomUp contractAnd) := by
  apply bottomUp_normalizedBy
  · intro e
    cases e with
    | and p q =>
        cases q with
        | top => exact EqvGen.rel _ _ (.root (AndTop.andTop p))
        | _ => exact EqvGen.refl _
    | _ => exact EqvGen.refl _
  · intro redex contractum rule
    cases rule with
    | andTop p => rfl

/-- The collapse can produce a numeral: the bubble is not rigid. -/
theorem andTop_not_rigid : ¬ ArithmeticRigid AndTop :=
  fun rigid => (rigid _ _ (AndTop.andTop zeroE)).2 ⟨_, .zero, rfl⟩

/-- **Symbol disjointness does not make decisions compose with a collapsing
rule.**  For every normal form of the collapsing bubble, the composite after
arithmetic fails on `x + (0 ∧ ⊤)`: the collapse exposes a recursion redex
after the arithmetic normal form has passed it. -/
theorem andTop_after_arith_not_normalizedBy {normal : AExpr → AExpr}
    (bySecond : NormalizedBy AndTop normal) :
    ¬ NormalizedBy (join Rule AndTop) (fun e => normal (norm false e)) := by
  intro normalized
  have converted : Convertible (join Rule AndTop) (addE (.bvar 0) (.and zeroE .top)) (.bvar 0) :=
    EqvGen.trans _ _ _
      (EqvGen.rel _ _ (.appArgument (.root (Or.inr (AndTop.andTop zeroE)))))
      (EqvGen.rel _ _ (.root (Or.inl (Rule.addZero (.bvar 0)))))
  have equal : normal (addE (.bvar 0) (.and zeroE .top)) = normal (.bvar 0) :=
    normalized.2 _ _ converted
  have collapsed := andTop_normalizedBy.conv_iff.mp (bySecond.conv_iff.mpr equal)
  simp [bottomUp, contractAnd, addE, zeroE] at collapsed

/-! ### Typed joins: the collapse confined to a sort -/

/-- **The collapse at sorts other than the numerals**: `p ∧ ⊤ ↦ p` for every `p`
not headed by an arithmetic constant.  Reading the sort of a term from its
head, this is the collapsing rule with its variable sorted away from the
numerals. -/
inductive SortedAndTop : AExpr → AExpr → Prop where
  | andTop (p : AExpr) (sorted : ¬ ArithmeticHeaded p) : SortedAndTop (.and p .top) p

/-- The arithmetic normal form keeps the head of a term that no arithmetic
constant heads. -/
theorem spineHead_norm {p : AExpr} (sorted : ¬ ArithmeticHeaded p) :
    spineHead (norm false p) = spineHead p := by
  induction p with
  | app f a ihf _ =>
      have sortedFunction : ¬ ArithmeticHeaded f := sorted
      have head := ihf sortedFunction
      have notAdd : ∀ y, norm false f ≠ .app (.const _ .add) y := by
        intro y same
        apply sortedFunction
        exact ⟨_, .add, by rw [← head, same]; rfl⟩
      show spineHead (appNorm false (norm false f) (norm false a)) = spineHead f
      rw [appNorm_eq_app notAdd]
      exact head
  | const τ c => exact absurd ⟨τ, c, rfl⟩ sorted
  | _ => rfl

theorem sortedAndTop_rigid : ArithmeticRigid SortedAndTop := fun _ _ rule =>
  match rule with
  | .andTop _ sorted => ⟨fun ⟨_, _, head⟩ => (by cases head), sorted⟩

theorem sortedAndTop_compatible : ArithmeticCompatible SortedAndTop := fun _ _ rule =>
  match rule with
  | .andTop p sorted => .root (SortedAndTop.andTop (norm false p) fun ⟨τ, c, head⟩ =>
      sorted ⟨τ, c, (spineHead_norm sorted).symm.trans head⟩)

open Classical in
/-- Conjunction with truth contracted at sorts other than the numerals. -/
noncomputable def contractSortedAnd : AExpr → AExpr
  | .and p .top => if ArithmeticHeaded p then .and p .top else p
  | e => e

/-- Not being headed by an arithmetic constant survives the sorted normal
form. -/
theorem sorted_bottomUp {p : AExpr} (sorted : ¬ ArithmeticHeaded p) :
    ¬ ArithmeticHeaded (bottomUp contractSortedAnd p) := by
  induction p with
  | and q r _ _ =>
      show ¬ ArithmeticHeaded
        (contractSortedAnd (.and (bottomUp contractSortedAnd q) (bottomUp contractSortedAnd r)))
      generalize bottomUp contractSortedAnd q = q'
      generalize bottomUp contractSortedAnd r = r'
      cases r' with
      | top =>
          by_cases headed : ArithmeticHeaded q'
          · simp only [contractSortedAnd, if_pos headed]
            rintro ⟨_, _, head⟩
            cases head
          · simp only [contractSortedAnd, if_neg headed]
            exact headed
      | _ =>
          rintro ⟨_, _, head⟩
          cases head
  | app f a ihf _ =>
      exact ihf sorted
  | const τ c => exact absurd ⟨τ, c, rfl⟩ sorted
  | _ =>
      rintro ⟨_, _, head⟩
      cases head

theorem sortedAndTop_normalizedBy : NormalizedBy SortedAndTop (bottomUp contractSortedAnd) := by
  apply bottomUp_normalizedBy
  · intro e
    cases e with
    | and p q =>
        cases q with
        | top =>
            by_cases headed : ArithmeticHeaded p
            · simp only [contractSortedAnd, if_pos headed]
              exact EqvGen.refl _
            · simp only [contractSortedAnd, if_neg headed]
              exact EqvGen.rel _ _ (.root (SortedAndTop.andTop p headed))
        | _ => exact EqvGen.refl _
    | _ => exact EqvGen.refl _
  · intro redex contractum rule
    match rule with
    | .andTop p sorted =>
        show contractSortedAnd (.and (bottomUp contractSortedAnd p) .top) =
          bottomUp contractSortedAnd p
        simp only [contractSortedAnd, if_neg (sorted_bottomUp sorted)]

/-- **Typed join.**  Confined to sorts other than the numerals, the collapsing
rule composes with arithmetic: the join is decided by the arithmetic normal
form followed by the sorted collapse. -/
theorem arith_sortedAndTop_normalizedBy :
    NormalizedBy (join Rule SortedAndTop) (fun e => bottomUp contractSortedAnd (norm false e)) :=
  join_rule_normalizedBy_of_rigid sortedAndTop_rigid sortedAndTop_compatible
    sortedAndTop_normalizedBy

/-! ### A rule that normalizing aliens disables: distinct sides are unequal -/

/-- An equation between syntactically distinct sides is false. -/
inductive Distinct : AExpr → AExpr → Prop where
  | distinct (a b : AExpr) (different : a ≠ b) : Distinct (.eq a b) .bot

/-- The rule as one schema. -/
def distinctSchemas : Unit → AExpr → AExpr → Prop :=
  fun _ redex contractum => ∃ a b, a ≠ b ∧ redex = .eq a b ∧ contractum = .bot

theorem distinct_presented : Presented distinctSchemas = Distinct := by
  funext redex contractum
  apply propext
  constructor
  · rintro ⟨_, a, b, different, rfl, rfl⟩
    exact Distinct.distinct a b different
  · intro rule
    cases rule with
    | distinct a b different => exact ⟨(), a, b, different, rfl, rfl⟩

/-- The rule is disjoint from arithmetic. -/
theorem rule_distinct_disjoint :
    Disjoint (Signature ExprOccurs ruleSchemas) (Signature ExprOccurs distinctSchemas) :=
  rule_disjoint_of_logical
    (signature_subset fun _ _ =>
      ⟨_, _, ⟨.bvar 0, .bvar 1, by simp, rfl, rfl⟩, logical_of_symbols rfl⟩)

theorem distinct_rigid : ArithmeticRigid Distinct :=
  rigid_of_rootedIn const_not_logical
    (fun _ _ rule => by cases rule; exact ⟨.eq, rfl, rfl⟩)
    (fun _ _ rule => by cases rule; exact ⟨.bot, rfl, rfl⟩)

/-- `x = x` neither steps nor is stepped to. -/
private theorem distinct_isolated :
    (∀ e, ¬ Rewrite Distinct (.eq (.bvar 0) (.bvar 0)) e) ∧
      ∀ e, ¬ Rewrite Distinct e (.eq (.bvar 0) (.bvar 0)) := by
  constructor
  · intro e stepped
    cases stepped with
    | root rule =>
        cases rule with
        | distinct _ _ different => exact different rfl
    | eqLeft inner => cases inner with | root rule => cases rule
    | eqRight inner => cases inner with | root rule => cases rule
  · intro e stepped
    cases stepped with
    | root rule => cases rule
    | eqLeft inner => cases inner with | root rule => cases rule
    | eqRight inner => cases inner with | root rule => cases rule

/-- The arithmetic normal form turns the redex `x + 0 = x` into `x = x`, which
is no redex: the rule is rigid and disjoint, yet not compatible. -/
theorem distinct_not_compatible : ¬ ArithmeticCompatible Distinct := fun compatible =>
  distinct_isolated.1 _
    (compatible _ _ (Distinct.distinct (addE (.bvar 0) zeroE) (.bvar 0) (by simp [addE])))

/-- **Compatibility is needed.**  For every normal form of the rule, the
composite after arithmetic fails: the join converts `x = x` with `⊥` through
`x + 0 = x`, and the rule alone does not. -/
theorem distinct_after_arith_not_normalizedBy {normal : AExpr → AExpr}
    (bySecond : NormalizedBy Distinct normal) :
    ¬ NormalizedBy (join Rule Distinct) (fun e => normal (norm false e)) := by
  intro normalized
  have converted : Convertible (join Rule Distinct) (.eq (.bvar 0) (.bvar 0)) .bot :=
    EqvGen.trans _ (.eq (addE (.bvar 0) zeroE) (.bvar 0)) _
      (EqvGen.symm _ _ (EqvGen.rel _ _ (.eqLeft (.root (Or.inl (Rule.addZero (.bvar 0)))))))
      (EqvGen.rel _ _ (.root (Or.inr (Distinct.distinct _ _ (by simp [addE])))))
  have equal : normal (.eq (.bvar 0) (.bvar 0)) = normal .bot := normalized.2 _ _ converted
  have isolated := eqvGen_isolated distinct_isolated.1 distinct_isolated.2
    (bySecond.conv_iff.mpr equal)
  cases isolated

/-! ### A shared symbol -/

/-- The zero-swap bubble shares the constant of addition: it is not rigid.  Its
failure of respect is `norm_false_not_respects_zeroSwap`. -/
theorem zeroSwap_not_rigid : ¬ ArithmeticRigid ZeroSwap :=
  fun rigid => (rigid _ _ (ZeroSwap.swap (.bvar 0))).1 ⟨_, .add, rfl⟩

/-! ## Bubbles forget ordered results -/

section OrderedResults

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-- **A bubble forgets the order and multiplicity of results.**  Declaring
every rewrite row twice keeps the bubble and doubles every ordered result. -/
theorem doubled_rows_same_bubble (language : LanguageDef) :
    languageBubble { language with rewrites := language.rewrites ++ language.rewrites } =
        languageBubble language ∧
      ∀ term, rewriteStep language term ≠ [] →
        rewriteStep { language with rewrites := language.rewrites ++ language.rewrites } term ≠
          rewriteStep language term := by
  have doubled : ∀ term,
      rewriteStep { language with rewrites := language.rewrites ++ language.rewrites } term =
        rewriteStep language term ++ rewriteStep language term := by
    intro term
    simp [rewriteStep, List.flatMap_append]
  refine ⟨?_, fun term nonempty same => ?_⟩
  · funext redex contractum
    simp [languageBubble, doubled]
  · have lengths := congrArg List.length same
    rw [doubled, List.length_append] at lengths
    exact nonempty (List.length_eq_zero_iff.mp (by omega))

/-- One premise-free rewrite row, `a ↦ b`. -/
def oneRow : LanguageDef where
  name := "oneRow"
  types := [TypeDecl.plain "S"]
  terms := [{ label := "a", category := "S", params := [], syntaxPattern := [] },
    { label := "b", category := "S", params := [], syntaxPattern := [] }]
  equations := []
  rewrites := [
    { name := "ab"
      typeContext := []
      premises := []
      left := .apply "a" []
      right := .apply "b" [] }]

/-- The row fires on `a`, so its doubled declaration returns a different
ordered result. -/
theorem oneRow_fires : rewriteStep oneRow (.apply "a" []) = [.apply "b" []] := by
  decide +kernel

end OrderedResults

#print axioms join_rule_normalizedBy_of_rigid
#print axioms norm_respects_of_rigid
#print axioms exists_composite_after_arith
#print axioms bottomUp_normalizedBy
#print axioms arith_eqRefl_normalizedBy
#print axioms eqRefl_first_not_normalizedBy
#print axioms rule_andTop_disjoint
#print axioms andTop_after_arith_not_normalizedBy
#print axioms arith_sortedAndTop_normalizedBy
#print axioms rule_distinct_disjoint
#print axioms distinct_after_arith_not_normalizedBy
#print axioms zeroSwap_not_rigid
#print axioms doubled_rows_same_bubble
#print axioms oneRow_fires

end Mettapedia.TypeTheory.BubbleJoinDisjoint

namespace Mettapedia.TypeTheory.BubbleConversion.Arith

/-- **Arithmetic beside `¬⊤ ↦ ⊥`.**  The join of addition's recursion equations
with the logical bubble is normalized by the composite normal form: the logical
bubble is rigid and compatible for arithmetic, so this is an instance of
`BubbleJoinDisjoint.join_rule_normalizedBy_of_rigid`.  Both normal forms are
computable, so the join's conversion is decided by comparing them. -/
theorem arith_notTop_normalizedBy :
    NormalizedBy (join Rule NotTop) (fun e => normNot (norm false e)) :=
  BubbleJoinDisjoint.join_rule_normalizedBy_of_rigid BubbleJoinDisjoint.notTop_rigid
    BubbleJoinDisjoint.notTop_compatible notTop_normalizedBy

theorem arith_notTop_conv_iff {e e' : AExpr} :
    Convertible (join Rule NotTop) e e' ↔ normNot (norm false e) = normNot (norm false e') :=
  arith_notTop_normalizedBy.conv_iff

end Mettapedia.TypeTheory.BubbleConversion.Arith
