import Mettapedia.TypeTheory.FreeConversion
import Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent

/-!
# Definitional equality carved per bubble

A weak dependent type theory has no global definitional equality.  Its global
typing is syntax-directed, and computation is available globally only as
evidence.  Definitional equality lives in bubbles: each bubble declares the
steps it treats as definitional, its conversion is the free conversion those
steps generate (`FreeConversion.Path`), and its typing judgment adds a
conversion rule for that conversion and no other.

Three coherence laws are folds of free conversion evidence, so each has only
step-level obligations:

* `Bubbles.widen`: a bubble whose steps embed in another's has its
  conversions embedded, functorially (`widen_refl`, `widen_comp`).
* `Bubbles.sound`: if every declared step of a bubble is justified by a global
  equality, every conversion of the bubble is a global equality.
* `Bubbles.substitute`: if the declared steps are stable under a substitution,
  so are the conversions.

`unjustified_step_not_sound` is the control: a bubble that declares a step its
global equality does not justify has a conversion that no fold can send there.

The second half instantiates this on the dependent comparison core of the HOL
embedding (`SimpleSliceOfDependent`).  A bubble's typing is syntax-directed
typing followed by one conversion of the bubble (`hasTypeIn_iff`), and the
empty bubble is the global judgment (`hasTypeIn_none_iff`).  The arithmetic
bubbles over a base type of numbers are

* `arith`: addition with its two recursion equations, the computation rules of
  ordinary definitional unfolding;
* `arithPlus`: the same with the left-unit equation `0 + t ↦ t`, a rewrite
  rule justified by induction and true in the standard model.

Each is decided by a normal form (`arith_conv_iff`, `arithPlus_conv_iff`), is
stable under substitution, and is sound for the standard model of its
arithmetic subterms.  A vector of length `n + 0` has the type of a vector of
length `n` in both bubbles and not in the global judgment; a vector of length
`0 + n` has it only in `arithPlus`; a vector of length `n + 1` has it in
neither.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleConversion

open FreeConversion JudgmentalEquality

universe uIndex uState uBubble uStep uTarget

/-! ## Bubbles over shared judgment fibres -/

set_option linter.checkUnivs false in
/-- Judgment-indexed states shared by every bubble, and the definitional steps
each bubble declares. -/
structure Bubbles (Index : Type uIndex) where
  State : Index → Type uState
  Bubble : Type uBubble
  Step : Bubble → {index : Index} → State index → State index → Type uStep

namespace Bubbles

variable {Index : Type uIndex} (B : Bubbles.{uIndex, uState, uBubble, uStep} Index)

/-- The definitional equality of a bubble: the free conversion trees of its
declared steps. -/
abbrev Conv (bubble : B.Bubble) {index : Index} (source target : B.State index) :=
  Path B.State (B.Step bubble) source target

/-- **Fibres compose.**  A map of declared steps maps conversion trees. -/
def widen {small large : B.Bubble}
    (embed : ∀ {index : Index} {source target : B.State index},
      B.Step small source target → B.Step large source target) :
    ∀ {index : Index} {source target : B.State index},
      B.Conv small source target → B.Conv large source target :=
  fun path => Algebra.fold
    (Target := fun {index} (source target : B.State index) => B.Conv large source target)
    { onStep := fun step => .step (embed step)
      onRefl := fun state => ConversionEvidence.refl
        (computation := computation B.State (B.Step large)) state
      onSymm := fun converted => .symm converted
      onTrans := fun first second => .trans first second } path

section WidenEquations

variable {small large : B.Bubble}
    (embed : ∀ {index : Index} {source target : B.State index},
      B.Step small source target → B.Step large source target)
    {index : Index}

@[simp] theorem widen_step {source target : B.State index} (step : B.Step small source target) :
    B.widen embed (.step step) = .step (embed step) := by
  simp [widen]

@[simp] theorem widen_reflexive (state : B.State index) :
    B.widen embed (ConversionEvidence.refl (computation := computation B.State (B.Step small)) state) =
      ConversionEvidence.refl (computation := computation B.State (B.Step large)) state := by
  simp [widen]

@[simp] theorem widen_symm {source target : B.State index} (path : B.Conv small source target) :
    B.widen embed (.symm path) = .symm (B.widen embed path) := by
  simp [widen]

@[simp] theorem widen_trans {source middle target : B.State index}
    (first : B.Conv small source middle) (second : B.Conv small middle target) :
    B.widen embed (.trans first second) = .trans (B.widen embed first) (B.widen embed second) := by
  simp [widen]

end WidenEquations

/-- Widening along the identity map of steps is the identity. -/
theorem widen_refl {bubble : B.Bubble} : ∀ {index : Index} {source target : B.State index}
    (path : B.Conv bubble source target), B.widen (fun step => step) path = path
  | _, _, _, .step _ => by rw [widen_step]
  | _, _, _, .refl _ => by rw [widen_reflexive]
  | _, _, _, .symm path => by rw [widen_symm, widen_refl path]
  | _, _, _, .trans first second => by rw [widen_trans, widen_refl first, widen_refl second]

/-- Widening in two stages is widening along the composite map. -/
theorem widen_comp {small middle large : B.Bubble}
    (first : ∀ {index : Index} {source target : B.State index},
      B.Step small source target → B.Step middle source target)
    (second : ∀ {index : Index} {source target : B.State index},
      B.Step middle source target → B.Step large source target) :
    ∀ {index : Index} {source target : B.State index} (path : B.Conv small source target),
      B.widen second (B.widen first path) = B.widen (fun step => second (first step)) path
  | _, _, _, .step _ => by simp only [widen_step]
  | _, _, _, .refl _ => by simp only [widen_reflexive]
  | _, _, _, .symm path => by simp only [widen_symm, widen_comp first second path]
  | _, _, _, .trans one two => by
      simp only [widen_trans, widen_comp first second one, widen_comp first second two]

/-- A global proof-relevant equality on the shared states. -/
structure GlobalEquality where
  Eq : {index : Index} → B.State index → B.State index → Type uTarget
  refl : ∀ {index : Index} (state : B.State index), Eq state state
  symm : ∀ {index : Index} {source target : B.State index}, Eq source target → Eq target source
  trans : ∀ {index : Index} {source middle target : B.State index},
    Eq source middle → Eq middle target → Eq source target

/-- **Each bubble's conversion is sound for the global equality** once every
declared step of the bubble is justified by it. -/
def sound (global : GlobalEquality.{uIndex, uState, uBubble, uStep, uTarget} B) {bubble : B.Bubble}
    (justify : ∀ {index : Index} {source target : B.State index},
      B.Step bubble source target → global.Eq source target) :
    ∀ {index : Index} {source target : B.State index},
      B.Conv bubble source target → global.Eq source target :=
  fun path => Algebra.fold
    (Target := fun {index} (source target : B.State index) => global.Eq source target)
    { onStep := justify
      onRefl := global.refl
      onSymm := global.symm
      onTrans := global.trans } path

/-- **Stability under substitution.**  A substitution that moves states between
fibres and keeps the declared steps keeps every conversion. -/
def substitute {bubble : B.Bubble} (reindex : Index → Index)
    (substitution : ∀ {index : Index}, B.State index → B.State (reindex index))
    (stable : ∀ {index : Index} {source target : B.State index},
      B.Step bubble source target →
        B.Step bubble (substitution source) (substitution target)) :
    ∀ {index : Index} {source target : B.State index},
      B.Conv bubble source target →
        B.Conv bubble (substitution source) (substitution target) :=
  fun path => Algebra.fold
    (Target := fun {index} (source target : B.State index) =>
      B.Conv bubble (substitution source) (substitution target))
    { onStep := fun step => .step (stable step)
      onRefl := fun state => ConversionEvidence.refl
        (computation := computation B.State (B.Step bubble)) (substitution state)
      onSymm := fun converted => .symm converted
      onTrans := fun first second => .trans first second } path

end Bubbles

/-! ### The control: an unjustified step -/

namespace UnjustifiedControl

/-- Two states, and one bubble that declares a step from the first to the second. -/
def twoStates : Bubbles.{0, 0, 0, 0} Unit where
  State := fun _ => Bool
  Bubble := Unit
  Step := fun _ {_} source target => PLift (source = false ∧ target = true)

/-- Strict equality of states as the global equality. -/
def strictEquality : Bubbles.GlobalEquality.{0, 0, 0, 0, 0} twoStates where
  Eq := fun source target => PLift (source = target)
  refl := fun _ => ⟨rfl⟩
  symm := fun equal => ⟨equal.down.symm⟩
  trans := fun first second => ⟨first.down.trans second.down⟩

/-- The declared step is a conversion of the bubble. -/
def falseToTrue : twoStates.Conv () (index := ()) false true :=
  .step ⟨⟨rfl, rfl⟩⟩

/-- No sending of the bubble's conversions into the global equality exists:
the declared step is not justified, and its conversion would identify two
distinct states. -/
theorem unjustified_step_not_sound
    (send : ∀ {source target : Bool},
      twoStates.Conv () (index := ()) source target →
        strictEquality.Eq (index := ()) source target) : False :=
  Bool.false_ne_true (send falseToTrue).down

end UnjustifiedControl

/-! ## Bubbles on the dependent comparison core -/

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- One step of a set of root rules, at any position of an expression. -/
inductive Rewrite (rules : Expr Base Const → Expr Base Const → Prop) :
    Expr Base Const → Expr Base Const → Prop where
  | root {left right : Expr Base Const} : rules left right → Rewrite rules left right
  | piDomain {A A' B : Expr Base Const} : Rewrite rules A A' → Rewrite rules (pi A B) (pi A' B)
  | piBody {A B B' : Expr Base Const} : Rewrite rules B B' → Rewrite rules (pi A B) (pi A B')
  | lamDomain {A A' b : Expr Base Const} :
      Rewrite rules A A' → Rewrite rules (lam A b) (lam A' b)
  | lamBody {A b b' : Expr Base Const} : Rewrite rules b b' → Rewrite rules (lam A b) (lam A b')
  | appFunction {f f' a : Expr Base Const} :
      Rewrite rules f f' → Rewrite rules (app f a) (app f' a)
  | appArgument {f a a' : Expr Base Const} :
      Rewrite rules a a' → Rewrite rules (app f a) (app f a')
  | andLeft {p p' q : Expr Base Const} : Rewrite rules p p' → Rewrite rules (and p q) (and p' q)
  | andRight {p q q' : Expr Base Const} : Rewrite rules q q' → Rewrite rules (and p q) (and p q')
  | orLeft {p p' q : Expr Base Const} : Rewrite rules p p' → Rewrite rules (or p q) (or p' q)
  | orRight {p q q' : Expr Base Const} : Rewrite rules q q' → Rewrite rules (or p q) (or p q')
  | impLeft {p p' q : Expr Base Const} : Rewrite rules p p' → Rewrite rules (imp p q) (imp p' q)
  | impRight {p q q' : Expr Base Const} : Rewrite rules q q' → Rewrite rules (imp p q) (imp p q')
  | notBody {p p' : Expr Base Const} : Rewrite rules p p' → Rewrite rules (not p) (not p')
  | eqLeft {a a' b : Expr Base Const} : Rewrite rules a a' → Rewrite rules (eq a b) (eq a' b)
  | eqRight {a b b' : Expr Base Const} : Rewrite rules b b' → Rewrite rules (eq a b) (eq a b')
  | allDomain {A A' b : Expr Base Const} :
      Rewrite rules A A' → Rewrite rules (all A b) (all A' b)
  | allBody {A b b' : Expr Base Const} : Rewrite rules b b' → Rewrite rules (all A b) (all A b')
  | exDomain {A A' b : Expr Base Const} :
      Rewrite rules A A' → Rewrite rules (ex A b) (ex A' b)
  | exBody {A b b' : Expr Base Const} : Rewrite rules b b' → Rewrite rules (ex A b) (ex A b')

/-- A bubble's definitional equality on the core: the equivalence closure of
its rewrite steps. -/
abbrev Convertible (rules : Expr Base Const → Expr Base Const → Prop) :=
  Relation.EqvGen (Rewrite rules)

/-- Typing in a bubble: the syntax-directed core with the bubble's conversion rule. -/
inductive HasTypeIn (rules : Expr Base Const → Expr Base Const → Prop)
    (Γ : List (Expr Base Const)) : Expr Base Const → Expr Base Const → Prop where
  | of {e A : Expr Base Const} : HasType Γ e A → HasTypeIn rules Γ e A
  | conv {e A B : Expr Base Const} :
      HasTypeIn rules Γ e A → Convertible rules A B → HasTypeIn rules Γ e B

/-- **Typing in a bubble is global typing followed by one conversion of the
bubble.**  An implementation either finds that conversion or is handed it. -/
theorem hasTypeIn_iff {rules : Expr Base Const → Expr Base Const → Prop}
    {Γ : List (Expr Base Const)} {e B : Expr Base Const} :
    HasTypeIn rules Γ e B ↔ ∃ A, HasType Γ e A ∧ Convertible rules A B := by
  constructor
  · intro typed
    induction typed with
    | of typing => exact ⟨_, typing, Relation.EqvGen.refl _⟩
    | conv _ converted ih =>
        obtain ⟨A, typing, before⟩ := ih
        exact ⟨A, typing, Relation.EqvGen.trans _ _ _ before converted⟩
  · rintro ⟨A, typing, converted⟩
    exact .conv (.of typing) converted

/-- A rule set with no rules has no rewrite step. -/
theorem rewrite_none {e e' : Expr Base Const} (step : Rewrite (fun _ _ => False) e e') : False := by
  induction step with
  | root impossible => exact impossible
  | piDomain _ next => exact next
  | piBody _ next => exact next
  | lamDomain _ next => exact next
  | lamBody _ next => exact next
  | appFunction _ next => exact next
  | appArgument _ next => exact next
  | andLeft _ next => exact next
  | andRight _ next => exact next
  | orLeft _ next => exact next
  | orRight _ next => exact next
  | impLeft _ next => exact next
  | impRight _ next => exact next
  | notBody _ next => exact next
  | eqLeft _ next => exact next
  | eqRight _ next => exact next
  | allDomain _ next => exact next
  | allBody _ next => exact next
  | exDomain _ next => exact next
  | exBody _ next => exact next

/-- With no rules, a bubble's conversion is syntactic identity. -/
theorem convertible_none_iff {e e' : Expr Base Const} :
    Convertible (fun _ _ => False) e e' ↔ e = e' := by
  constructor
  · intro converted
    induction converted with
    | rel _ _ step => exact (rewrite_none step).elim
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond
  · rintro rfl
    exact Relation.EqvGen.refl _

/-- **The empty bubble is the global judgment.** -/
theorem hasTypeIn_none_iff {Γ : List (Expr Base Const)} {e A : Expr Base Const} :
    HasTypeIn (fun _ _ => False) Γ e A ↔ HasType Γ e A := by
  rw [hasTypeIn_iff]
  constructor
  · rintro ⟨A', typing, converted⟩
    rwa [convertible_none_iff.mp converted] at typing
  · intro typing
    exact ⟨A, typing, Relation.EqvGen.refl _⟩

/-- More rules, more rewrite steps. -/
theorem rewrite_mono {small large : Expr Base Const → Expr Base Const → Prop}
    (included : ∀ left right, small left right → large left right)
    {e e' : Expr Base Const} (step : Rewrite small e e') : Rewrite large e e' := by
  induction step with
  | root rule => exact .root (included _ _ rule)
  | piDomain _ next => exact .piDomain next
  | piBody _ next => exact .piBody next
  | lamDomain _ next => exact .lamDomain next
  | lamBody _ next => exact .lamBody next
  | appFunction _ next => exact .appFunction next
  | appArgument _ next => exact .appArgument next
  | andLeft _ next => exact .andLeft next
  | andRight _ next => exact .andRight next
  | orLeft _ next => exact .orLeft next
  | orRight _ next => exact .orRight next
  | impLeft _ next => exact .impLeft next
  | impRight _ next => exact .impRight next
  | notBody _ next => exact .notBody next
  | eqLeft _ next => exact .eqLeft next
  | eqRight _ next => exact .eqRight next
  | allDomain _ next => exact .allDomain next
  | allBody _ next => exact .allBody next
  | exDomain _ next => exact .exDomain next
  | exBody _ next => exact .exBody next

theorem convertible_mono {small large : Expr Base Const → Expr Base Const → Prop}
    (included : ∀ left right, small left right → large left right)
    {e e' : Expr Base Const} (converted : Convertible small e e') : Convertible large e e' := by
  induction converted with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ (rewrite_mono included step)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

/-- **Fibres compose on the core.**  More rules, more typings. -/
theorem hasTypeIn_mono {small large : Expr Base Const → Expr Base Const → Prop}
    (included : ∀ left right, small left right → large left right)
    {Γ : List (Expr Base Const)} {e A : Expr Base Const} (typed : HasTypeIn small Γ e A) :
    HasTypeIn large Γ e A := by
  obtain ⟨A₀, typing, converted⟩ := hasTypeIn_iff.mp typed
  exact hasTypeIn_iff.mpr ⟨A₀, typing, convertible_mono included converted⟩

/-- A set of root rules is stable under substitution when every instance of a
rule stays an instance after substituting at any depth. -/
def SubstitutionStable (rules : Expr Base Const → Expr Base Const → Prop) : Prop :=
  ∀ left right, rules left right → ∀ (depth : Nat) (replacement : Expr Base Const),
    rules (substAt depth replacement left) (substAt depth replacement right)

/-- **Stability under substitution on the core.** -/
theorem rewrite_substAt {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : SubstitutionStable rules) {e e' : Expr Base Const} (step : Rewrite rules e e') :
    ∀ (depth : Nat) (replacement : Expr Base Const),
      Rewrite rules (substAt depth replacement e) (substAt depth replacement e') := by
  induction step with
  | root rule => exact fun depth replacement => .root (stable _ _ rule depth replacement)
  | piDomain _ ih => exact fun depth replacement => .piDomain (ih depth replacement)
  | piBody _ ih => exact fun depth replacement => .piBody (ih (depth + 1) replacement)
  | lamDomain _ ih => exact fun depth replacement => .lamDomain (ih depth replacement)
  | lamBody _ ih => exact fun depth replacement => .lamBody (ih (depth + 1) replacement)
  | appFunction _ ih => exact fun depth replacement => .appFunction (ih depth replacement)
  | appArgument _ ih => exact fun depth replacement => .appArgument (ih depth replacement)
  | andLeft _ ih => exact fun depth replacement => .andLeft (ih depth replacement)
  | andRight _ ih => exact fun depth replacement => .andRight (ih depth replacement)
  | orLeft _ ih => exact fun depth replacement => .orLeft (ih depth replacement)
  | orRight _ ih => exact fun depth replacement => .orRight (ih depth replacement)
  | impLeft _ ih => exact fun depth replacement => .impLeft (ih depth replacement)
  | impRight _ ih => exact fun depth replacement => .impRight (ih depth replacement)
  | notBody _ ih => exact fun depth replacement => .notBody (ih depth replacement)
  | eqLeft _ ih => exact fun depth replacement => .eqLeft (ih depth replacement)
  | eqRight _ ih => exact fun depth replacement => .eqRight (ih depth replacement)
  | allDomain _ ih => exact fun depth replacement => .allDomain (ih depth replacement)
  | allBody _ ih => exact fun depth replacement => .allBody (ih (depth + 1) replacement)
  | exDomain _ ih => exact fun depth replacement => .exDomain (ih depth replacement)
  | exBody _ ih => exact fun depth replacement => .exBody (ih (depth + 1) replacement)

theorem convertible_substAt {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : SubstitutionStable rules) {e e' : Expr Base Const}
    (converted : Convertible rules e e') (depth : Nat) (replacement : Expr Base Const) :
    Convertible rules (substAt depth replacement e) (substAt depth replacement e') := by
  induction converted with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ (rewrite_substAt stable step depth replacement)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

/-- The bubbles of the core as instances of the general structure: the steps of
a rule set are its proof-relevant rewrite steps. -/
def coreBubbles : Bubbles.{0, max u v, max u v, 0} Unit where
  State := fun _ => Expr Base Const
  Bubble := Expr Base Const → Expr Base Const → Prop
  Step := fun rules {_} source target => PLift (Rewrite rules source target)

end Core

/-! ## The arithmetic bubbles -/

/-- Constants of a signature with one base type of numbers. -/
inductive ArithConst : Ty Unit → Type where
  | zero : ArithConst (.base ())
  | succ : ArithConst (.arr (.base ()) (.base ()))
  | add : ArithConst (.arr (.base ()) (.arr (.base ()) (.base ())))

/-- Expressions of the core over the arithmetic signature. -/
abbrev AExpr := Expr Unit ArithConst

namespace Arith

def natType : AExpr := base ()
def zeroE : AExpr := const _ .zero
def succE (t : AExpr) : AExpr := app (const _ .succ) t
def addE (t u : AExpr) : AExpr := app (app (const _ .add) t) u
/-- Vectors indexed by a number: the declared family of the base type. -/
def vec (t : AExpr) : AExpr := app (tyFam ()) t

/-- The two recursion equations of addition. -/
inductive Rule : AExpr → AExpr → Prop where
  | addZero (t : AExpr) : Rule (addE t zeroE) t
  | addSucc (t u : AExpr) : Rule (addE t (succE u)) (succE (addE t u))

/-- The recursion equations and the left-unit equation. -/
inductive RulePlus : AExpr → AExpr → Prop where
  | recursion {left right : AExpr} : Rule left right → RulePlus left right
  | zeroAdd (t : AExpr) : RulePlus (addE zeroE t) t

/-! ### Normal forms -/

/-- Addition of two normal forms, by the recursion equations. -/
def addNorm (x : AExpr) : AExpr → AExpr
  | const _ .zero => x
  | app (const _ .succ) y => succE (addNorm x y)
  | y => addE x y

/-- The left-unit equation at the root of a sum whose second summand is not a
numeral constructor. -/
def addOther (x y : AExpr) : AExpr :=
  match x with
  | const _ .zero => y
  | _ => addE x y

/-- Addition of two normal forms, by the recursion and left-unit equations. -/
def addNormPlus (x : AExpr) : AExpr → AExpr
  | const _ .zero => x
  | app (const _ .succ) y => succE (addNormPlus x y)
  | y => addOther x y

/-- Application of two normal forms. -/
def appNorm (plus : Bool) (f a : AExpr) : AExpr :=
  match f with
  | app (const _ .add) x => if plus then addNormPlus x a else addNorm x a
  | _ => app f a

/-- The normal form of an expression: every arithmetic redex contracted, at
every position, compositionally. -/
def norm (plus : Bool) : AExpr → AExpr
  | .bvar i => .bvar i
  | .univ => .univ
  | .prop => .prop
  | .base b => .base b
  | .pi A B => .pi (norm plus A) (norm plus B)
  | .lam A b => .lam (norm plus A) (norm plus b)
  | .app f a => appNorm plus (norm plus f) (norm plus a)
  | .const τ c => .const τ c
  | .tyFam b => .tyFam b
  | .top => .top
  | .bot => .bot
  | .and p q => .and (norm plus p) (norm plus q)
  | .or p q => .or (norm plus p) (norm plus q)
  | .imp p q => .imp (norm plus p) (norm plus q)
  | .not p => .not (norm plus p)
  | .eq a b => .eq (norm plus a) (norm plus b)
  | .all A b => .all (norm plus A) (norm plus b)
  | .ex A b => .ex (norm plus A) (norm plus b)

/-! ### Normal-form equations -/

@[simp] theorem norm_zeroE (plus : Bool) : norm plus zeroE = zeroE := rfl

@[simp] theorem norm_succE (plus : Bool) (t : AExpr) : norm plus (succE t) = succE (norm plus t) := rfl

@[simp] theorem norm_vec (plus : Bool) (t : AExpr) : norm plus (vec t) = vec (norm plus t) := rfl

@[simp] theorem norm_addE_false (t u : AExpr) :
    norm false (addE t u) = addNorm (norm false t) (norm false u) := rfl

@[simp] theorem norm_addE_true (t u : AExpr) :
    norm true (addE t u) = addNormPlus (norm true t) (norm true u) := rfl

@[simp] theorem addNorm_zeroE (x : AExpr) : addNorm x zeroE = x := rfl

@[simp] theorem addNorm_succE (x y : AExpr) : addNorm x (succE y) = succE (addNorm x y) := rfl

@[simp] theorem addNormPlus_zeroE (x : AExpr) : addNormPlus x zeroE = x := rfl

@[simp] theorem addNormPlus_succE (x y : AExpr) :
    addNormPlus x (succE y) = succE (addNormPlus x y) := rfl

/-- The left unit holds for the normal-form addition of the second bubble. -/
theorem addNormPlus_zero_left (y : AExpr) : addNormPlus zeroE y = y := by
  induction y with
  | app f a _ iha =>
      cases f with
      | const τ c =>
          cases c with
          | succ => exact (congrArg succE iha : succE (addNormPlus zeroE a) = succE a)
          | zero => rfl
          | add => rfl
      | bvar _ => rfl
      | univ => rfl
      | prop => rfl
      | base _ => rfl
      | pi _ _ => rfl
      | lam _ _ => rfl
      | app _ _ => rfl
      | tyFam _ => rfl
      | top => rfl
      | bot => rfl
      | and _ _ => rfl
      | or _ _ => rfl
      | imp _ _ => rfl
      | not _ => rfl
      | eq _ _ => rfl
      | all _ _ => rfl
      | ex _ _ => rfl
  | const τ c => cases c <;> rfl
  | bvar _ => rfl
  | univ => rfl
  | prop => rfl
  | base _ => rfl
  | pi _ _ _ _ => rfl
  | lam _ _ _ _ => rfl
  | tyFam _ => rfl
  | top => rfl
  | bot => rfl
  | and _ _ _ _ => rfl
  | or _ _ _ _ => rfl
  | imp _ _ _ _ => rfl
  | not _ _ => rfl
  | eq _ _ _ _ => rfl
  | all _ _ _ _ => rfl
  | ex _ _ _ _ => rfl

/-! ### Conversion is equality of normal forms -/

/-- A rewrite step whose root instances keep the normal form keeps it anywhere. -/
theorem rewrite_norm (plus : Bool) {rules : AExpr → AExpr → Prop}
    (invariant : ∀ left right, rules left right → norm plus left = norm plus right)
    {e e' : AExpr} (step : Rewrite rules e e') : norm plus e = norm plus e' := by
  induction step with
  | root rule => exact invariant _ _ rule
  | piDomain _ ih => simp only [norm, ih]
  | piBody _ ih => simp only [norm, ih]
  | lamDomain _ ih => simp only [norm, ih]
  | lamBody _ ih => simp only [norm, ih]
  | appFunction _ ih => simp only [norm, ih]
  | appArgument _ ih => simp only [norm, ih]
  | andLeft _ ih => simp only [norm, ih]
  | andRight _ ih => simp only [norm, ih]
  | orLeft _ ih => simp only [norm, ih]
  | orRight _ ih => simp only [norm, ih]
  | impLeft _ ih => simp only [norm, ih]
  | impRight _ ih => simp only [norm, ih]
  | notBody _ ih => simp only [norm, ih]
  | eqLeft _ ih => simp only [norm, ih]
  | eqRight _ ih => simp only [norm, ih]
  | allDomain _ ih => simp only [norm, ih]
  | allBody _ ih => simp only [norm, ih]
  | exDomain _ ih => simp only [norm, ih]
  | exBody _ ih => simp only [norm, ih]

theorem convertible_norm (plus : Bool) {rules : AExpr → AExpr → Prop}
    (invariant : ∀ left right, rules left right → norm plus left = norm plus right)
    {e e' : AExpr} (converted : Convertible rules e e') : norm plus e = norm plus e' := by
  induction converted with
  | rel _ _ step => exact rewrite_norm plus invariant step
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem rule_norm (plus : Bool) {left right : AExpr} (rule : Rule left right) :
    norm plus left = norm plus right := by
  cases plus <;> cases rule <;> rfl

theorem rulePlus_norm {left right : AExpr} (rule : RulePlus left right) :
    norm true left = norm true right := by
  cases rule with
  | recursion rule => exact rule_norm true rule
  | zeroAdd _ => exact addNormPlus_zero_left _

/-- Congruence of conversion at an argument position. -/
theorem convertible_appArgument {rules : AExpr → AExpr → Prop} (f : AExpr) {a a' : AExpr}
    (converted : Convertible rules a a') : Convertible rules (app f a) (app f a') := by
  induction converted with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ (.appArgument step)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

/-- Congruence of conversion at the function position. -/
theorem convertible_appFunction {rules : AExpr → AExpr → Prop} {f f' : AExpr} (a : AExpr)
    (converted : Convertible rules f f') : Convertible rules (app f a) (app f' a) := by
  induction converted with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ (.appFunction step)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

/-- A one-hole context that every rewrite step crosses carries conversions. -/
theorem convertible_lift {rules : AExpr → AExpr → Prop} (context : AExpr → AExpr)
    (crosses : ∀ {a a' : AExpr}, Rewrite rules a a' → Rewrite rules (context a) (context a'))
    {a a' : AExpr} (converted : Convertible rules a a') :
    Convertible rules (context a) (context a') := by
  induction converted with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ (crosses step)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

/-- Two conversions under a binary constructor. -/
theorem convertible_two {rules : AExpr → AExpr → Prop} (former : AExpr → AExpr → AExpr)
    (left : ∀ {a a' b : AExpr}, Rewrite rules a a' → Rewrite rules (former a b) (former a' b))
    (right : ∀ {a b b' : AExpr}, Rewrite rules b b' → Rewrite rules (former a b) (former a b'))
    {a a' b b' : AExpr} (first : Convertible rules a a') (second : Convertible rules b b') :
    Convertible rules (former a b) (former a' b') :=
  Relation.EqvGen.trans _ _ _
    (convertible_lift (fun x => former x b) left first)
    (convertible_lift (fun y => former a' y) right second)

/-- Every sum converts to its normal-form addition, by the recursion equations. -/
theorem addNorm_reachable (x y : AExpr) : Convertible Rule (addE x y) (addNorm x y) := by
  induction y with
  | app f a _ iha =>
      cases f with
      | const τ c =>
          cases c with
          | succ =>
              exact Relation.EqvGen.trans _ _ _
                (Relation.EqvGen.rel _ _ (.root (Rule.addSucc x a)))
                (convertible_appArgument _ iha)
          | zero => exact Relation.EqvGen.refl _
          | add => exact Relation.EqvGen.refl _
      | _ => exact Relation.EqvGen.refl _
  | const τ c =>
      cases c with
      | zero => exact Relation.EqvGen.rel _ _ (.root (Rule.addZero x))
      | succ => exact Relation.EqvGen.refl _
      | add => exact Relation.EqvGen.refl _
  | _ => exact Relation.EqvGen.refl _

theorem addOther_reachable (x y : AExpr) : Convertible RulePlus (addE x y) (addOther x y) := by
  cases x with
  | const τ c =>
      cases c with
      | zero => exact Relation.EqvGen.rel _ _ (.root (RulePlus.zeroAdd y))
      | succ => exact Relation.EqvGen.refl _
      | add => exact Relation.EqvGen.refl _
  | _ => exact Relation.EqvGen.refl _

/-- Every sum converts to its normal-form addition, with the left unit. -/
theorem addNormPlus_reachable (x y : AExpr) :
    Convertible RulePlus (addE x y) (addNormPlus x y) := by
  induction y with
  | app f a _ iha =>
      cases f with
      | const τ c =>
          cases c with
          | succ =>
              exact Relation.EqvGen.trans _ _ _
                (Relation.EqvGen.rel _ _ (.root (RulePlus.recursion (Rule.addSucc x a))))
                (convertible_appArgument _ iha)
          | zero => exact addOther_reachable x _
          | add => exact addOther_reachable x _
      | _ => exact addOther_reachable x _
  | const τ c =>
      cases c with
      | zero => exact Relation.EqvGen.rel _ _ (.root (RulePlus.recursion (Rule.addZero x)))
      | succ => exact addOther_reachable x _
      | add => exact addOther_reachable x _
  | _ => exact addOther_reachable x _

/-- The rules of each bubble. -/
def bubbleRules : Bool → AExpr → AExpr → Prop
  | false => Rule
  | true => RulePlus

theorem appNorm_reachable (plus : Bool) (f a : AExpr) :
    Convertible (bubbleRules plus) (app f a) (appNorm plus f a) := by
  cases f with
  | app g x =>
      cases g with
      | const τ c =>
          cases c with
          | add =>
              cases plus
              · exact addNorm_reachable x a
              · exact addNormPlus_reachable x a
          | zero => exact Relation.EqvGen.refl _
          | succ => exact Relation.EqvGen.refl _
      | _ => exact Relation.EqvGen.refl _
  | _ => exact Relation.EqvGen.refl _

/-- **Every expression converts to its normal form.** -/
theorem norm_reachable (plus : Bool) (e : AExpr) : Convertible (bubbleRules plus) e (norm plus e) := by
  induction e with
  | app f a ihf iha =>
      exact Relation.EqvGen.trans _ _ _
        (convertible_two app (fun step => .appFunction step) (fun step => .appArgument step) ihf iha)
        (appNorm_reachable plus _ _)
  | pi A B ihA ihB =>
      exact convertible_two pi (fun step => .piDomain step) (fun step => .piBody step) ihA ihB
  | lam A b ihA ihb =>
      exact convertible_two lam (fun step => .lamDomain step) (fun step => .lamBody step) ihA ihb
  | and p q ihp ihq =>
      exact convertible_two Expr.and (fun step => .andLeft step) (fun step => .andRight step) ihp ihq
  | or p q ihp ihq =>
      exact convertible_two Expr.or (fun step => .orLeft step) (fun step => .orRight step) ihp ihq
  | imp p q ihp ihq =>
      exact convertible_two imp (fun step => .impLeft step) (fun step => .impRight step) ihp ihq
  | not p ihp => exact convertible_lift Expr.not (fun step => .notBody step) ihp
  | eq a b iha ihb =>
      exact convertible_two Expr.eq (fun step => .eqLeft step) (fun step => .eqRight step) iha ihb
  | all A b ihA ihb =>
      exact convertible_two all (fun step => .allDomain step) (fun step => .allBody step) ihA ihb
  | ex A b ihA ihb =>
      exact convertible_two ex (fun step => .exDomain step) (fun step => .exBody step) ihA ihb
  | _ => exact Relation.EqvGen.refl _

theorem bubbleRules_norm (plus : Bool) {left right : AExpr} (rule : bubbleRules plus left right) :
    norm plus left = norm plus right := by
  cases plus
  · exact rule_norm false rule
  · exact rulePlus_norm rule

/-- **Each arithmetic bubble is decided by its normal form.**  This is the
carve-out theorem of the bubble: its definitional equality is equality of
normal forms. -/
theorem conv_iff_norm (plus : Bool) {e e' : AExpr} :
    Convertible (bubbleRules plus) e e' ↔ norm plus e = norm plus e' := by
  constructor
  · exact convertible_norm plus (fun _ _ rule => bubbleRules_norm plus rule)
  · intro equal
    exact Relation.EqvGen.trans _ _ _ (norm_reachable plus e)
      (Relation.EqvGen.symm _ _ (equal ▸ norm_reachable plus e'))

/-- The proof-relevant conversions of the core bubbles fold into equality of
normal forms: the general soundness law at the normal-form equality. -/
def normEquality (plus : Bool) : (coreBubbles (Base := Unit) (Const := ArithConst)).GlobalEquality where
  Eq := fun e e' => PLift (norm plus e = norm plus e')
  refl := fun _ => ⟨rfl⟩
  symm := fun equal => ⟨equal.down.symm⟩
  trans := fun first second => ⟨first.down.trans second.down⟩

theorem bubble_conv_norm (plus : Bool) {e e' : AExpr}
    (path : (coreBubbles (Base := Unit) (Const := ArithConst)).Conv (bubbleRules plus)
      (index := ()) e e') :
    norm plus e = norm plus e' :=
  ((coreBubbles (Base := Unit) (Const := ArithConst)).sound (normEquality plus)
    (fun step => ⟨rewrite_norm plus (fun _ _ rule => bubbleRules_norm plus rule) step.down⟩)
    path).down

/-! ### Stability under substitution -/

theorem rule_stable : SubstitutionStable Rule := by
  intro left right rule depth replacement
  cases rule with
  | addZero => exact Rule.addZero _
  | addSucc => exact Rule.addSucc _ _

theorem rulePlus_stable : SubstitutionStable RulePlus := by
  intro left right rule depth replacement
  cases rule with
  | recursion rule => exact RulePlus.recursion (rule_stable _ _ rule depth replacement)
  | zeroAdd => exact RulePlus.zeroAdd _

theorem bubbleRules_stable (plus : Bool) : SubstitutionStable (bubbleRules plus) := by
  cases plus
  · exact rule_stable
  · exact rulePlus_stable

/-! ### Soundness in the standard model -/

/-- Numeral terms: variables, zero, successors and sums. -/
inductive IsNumeral : AExpr → Prop where
  | var (i : Nat) : IsNumeral (bvar i)
  | zero : IsNumeral zeroE
  | succ {t : AExpr} : IsNumeral t → IsNumeral (succE t)
  | add {t u : AExpr} : IsNumeral t → IsNumeral u → IsNumeral (addE t u)

/-- The standard model of numeral terms under a valuation of the variables;
nothing for any other expression. -/
def value (ρ : Nat → Nat) : AExpr → Option Nat
  | .bvar i => some (ρ i)
  | .const _ .zero => some 0
  | .app (.const _ .succ) t => (value ρ t).map (· + 1)
  | .app (.app (.const _ .add) t) u => (value ρ t).bind fun a => (value ρ u).map (a + ·)
  | _ => none

theorem value_addE (ρ : Nat → Nat) (t u : AExpr) :
    value ρ (addE t u) = (value ρ t).bind fun a => (value ρ u).map (a + ·) := rfl

theorem value_succE (ρ : Nat → Nat) (t : AExpr) :
    value ρ (succE t) = (value ρ t).map (· + 1) := rfl

theorem value_zeroE (ρ : Nat → Nat) : value ρ zeroE = some 0 := rfl

/-- Adding a successor is the successor of the sum, in the standard model. -/
theorem bind_succ (x y : Option Nat) :
    ((x.bind fun a => y.map (a + ·)).map (· + 1)) =
      x.bind fun a => (y.map (· + 1)).map (a + ·) := by
  cases x <;> cases y <;> simp [Nat.add_assoc]

/-- Adding zero, in the standard model. -/
theorem bind_zero (x : Option Nat) : x = x.bind fun a => (some 0).map (a + ·) := by
  cases x <;> rfl

/-- Zero plus, in the standard model. -/
theorem zero_bind (y : Option Nat) : y = (some 0).bind fun a => y.map (a + ·) := by
  cases y <;> simp

theorem value_addNorm (ρ : Nat → Nat) (x y : AExpr) :
    value ρ (addNorm x y) = (value ρ x).bind fun a => (value ρ y).map (a + ·) := by
  induction y with
  | app f a _ iha =>
      cases f with
      | const τ c =>
          cases c with
          | succ =>
              show value ρ (succE (addNorm x a)) = (value ρ x).bind fun c => (value ρ (succE a)).map (c + ·)
              rw [value_succE, iha, value_succE, bind_succ]
          | zero => rfl
          | add => rfl
      | _ => rfl
  | const τ c =>
      cases c with
      | zero => exact bind_zero (value ρ x)
      | succ => rfl
      | add => rfl
  | _ => rfl

theorem value_addOther (ρ : Nat → Nat) (x y : AExpr) :
    value ρ (addOther x y) = (value ρ x).bind fun a => (value ρ y).map (a + ·) := by
  cases x with
  | const τ c =>
      cases c with
      | zero => exact zero_bind (value ρ y)
      | succ => rfl
      | add => rfl
  | _ => rfl

theorem value_addNormPlus (ρ : Nat → Nat) (x y : AExpr) :
    value ρ (addNormPlus x y) = (value ρ x).bind fun a => (value ρ y).map (a + ·) := by
  induction y with
  | app f a _ iha =>
      cases f with
      | const τ c =>
          cases c with
          | succ =>
              show value ρ (succE (addNormPlus x a)) =
                (value ρ x).bind fun c => (value ρ (succE a)).map (c + ·)
              rw [value_succE, iha, value_succE, bind_succ]
          | zero => exact value_addOther ρ x _
          | add => exact value_addOther ρ x _
      | _ => exact value_addOther ρ x _
  | const τ c =>
      cases c with
      | zero => exact bind_zero (value ρ x)
      | succ => exact value_addOther ρ x _
      | add => exact value_addOther ρ x _
  | _ => exact value_addOther ρ x _

/-- Normalizing a numeral term keeps its value in the standard model. -/
theorem value_norm (plus : Bool) (ρ : Nat → Nat) {t : AExpr} (numeral : IsNumeral t) :
    value ρ (norm plus t) = value ρ t := by
  induction numeral with
  | var _ => rfl
  | zero => rfl
  | succ _ ih =>
      show (value ρ (norm plus _)).map (· + 1) = _
      rw [ih]
      rfl
  | add _ _ ihT ihU =>
      cases plus
      · show value ρ (addNorm _ _) = _
        rw [value_addNorm, ihT, ihU]
        rfl
      · show value ρ (addNormPlus _ _) = _
        rw [value_addNormPlus, ihT, ihU]
        rfl

/-- **Soundness of the arithmetic bubbles.**  They identify two vector types
only when the lengths have the same value under every valuation. -/
theorem vec_conv_sound (plus : Bool) {t t' : AExpr} (numeral : IsNumeral t)
    (numeral' : IsNumeral t')
    (converted : Convertible (bubbleRules plus) (vec t) (vec t')) (ρ : Nat → Nat) :
    value ρ t = value ρ t' := by
  have equal := (conv_iff_norm plus).mp converted
  rw [norm_vec, norm_vec] at equal
  have lengths : norm plus t = norm plus t' := (Expr.app.inj equal).2
  rw [← value_norm plus ρ numeral, lengths, value_norm plus ρ numeral']

/-! ### A vector inside and outside the bubbles -/

/-- The context `n : nat, v : Vec n`, newest first. -/
def vecContext : List AExpr := [vec (bvar 0), natType]

theorem vecVariable_typed : HasType vecContext (bvar 0) (vec (bvar 1)) :=
  HasType.var (Γ := vecContext) (i := 0) rfl

theorem vecVariable_type_unique {A : AExpr} (typed : HasType vecContext (bvar 0) A) :
    A = vec (bvar 1) :=
  (vecVariable_typed.unique typed).symm

/-- **Inside either arithmetic bubble, `v : Vec n` has type `Vec (n + 0)`.** -/
theorem vec_addZero_inside (plus : Bool) :
    HasTypeIn (bubbleRules plus) vecContext (bvar 0) (vec (addE (bvar 1) zeroE)) := by
  refine hasTypeIn_iff.mpr ⟨_, vecVariable_typed, (conv_iff_norm plus).mpr ?_⟩
  cases plus <;> rfl

/-- **In the global judgment it does not.** -/
theorem vec_addZero_not_global :
    ¬ HasType vecContext (bvar 0) (vec (addE (bvar 1) zeroE)) := by
  intro typed
  have equal := vecVariable_type_unique typed
  simp [vec, addE] at equal

/-- The left-unit bubble also gives `v : Vec (0 + n)`. -/
theorem vec_zeroAdd_plus :
    HasTypeIn (bubbleRules true) vecContext (bvar 0) (vec (addE zeroE (bvar 1))) := by
  refine hasTypeIn_iff.mpr ⟨_, vecVariable_typed, (conv_iff_norm true).mpr ?_⟩
  rfl

/-- The recursion equations alone do not: `0 + n` does not compute at a variable. -/
theorem vec_zeroAdd_not_arith :
    ¬ HasTypeIn (bubbleRules false) vecContext (bvar 0) (vec (addE zeroE (bvar 1))) := by
  intro typed
  obtain ⟨A, typing, converted⟩ := hasTypeIn_iff.mp typed
  rw [vecVariable_type_unique typing] at converted
  have equal := (conv_iff_norm false).mp converted
  simp [norm, appNorm, addNorm, vec, addE, zeroE] at equal

/-- Neither bubble gives `v : Vec (n + 1)`: the bubbles are not degenerate. -/
theorem vec_succ_not_inside (plus : Bool) :
    ¬ HasTypeIn (bubbleRules plus) vecContext (bvar 0) (vec (succE (bvar 1))) := by
  intro typed
  obtain ⟨A, typing, converted⟩ := hasTypeIn_iff.mp typed
  rw [vecVariable_type_unique typing] at converted
  have equal := (conv_iff_norm plus).mp converted
  cases plus <;> simp [norm, appNorm, vec, succE] at equal

end Arith

end Mettapedia.TypeTheory.BubbleConversion



