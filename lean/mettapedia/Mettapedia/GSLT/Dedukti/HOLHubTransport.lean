import Mettapedia.GSLT.Dedukti.TranslationTransport
import Mettapedia.Logic.HOL.BetaNormalization

/-!
# End to end: higher-order logic through the HOL encodings of Dedukti

The checker of the λΠ-calculus modulo decides conversion by normalizing both
sides.  This module proves, for the encodings of higher-order logic used by
Holide and by the STTfa hub of Logipedia, that the checker decides conversion
of translated HOL terms, and that its answer is exactly β-conversion of the
source.

**Source.**  The intrinsically typed terms of higher-order logic
(`Logic.HOL.Term`): many sorts, the type of propositions, the constants of a
signature, the connectives `⊤ ⊥ ∧ ∨ ⇒ ¬`, equality at every type and the two
quantifiers, with β-reduction at every position
(`ContextualTrinity.BetaStep`), which strongly normalizes and is confluent in
the tree (`BetaNormalization.stronglyNormalizing`,
`BetaNormalization.confluent`).

**Encoding** (`Encoding`).  The sorts, the constants, `prop`, the arrow and the
connectives are named injectively.  A simple type becomes a closed code, and a
term becomes the shallow embedding: an application is an application, an
abstraction is an abstraction whose domain is the decoding `El` of its type's
code, a connective is its constant applied to its operands, equality at `τ` is
its constant applied to the code of `τ` and the two sides, and a quantifier over
`σ` is its constant applied to the code of `σ` and an abstraction.  A theory of
the encoding (`HubTheory`) has rules headed by constants, is confluent and
defines none of the named symbols; the decoding of a named code reduces to a
normal form (`elAt`: closed, injective, not a product), and the decoding of a
function code reduces to the product of the decodings.

**Results.**

* Every β-step of the source is a step of the target (`translate_betaStep`),
  through the substitution law `translate_instantiate`.
* Decodings of codes compute (`reduces_El_code`) to normal terms
  (`elNF_normal`), products of the normal decodings of named codes.  The translation of a source normal form, with its domains
  computed, is normal (`translateNF_normal`), and the translation with
  computed domains is injective, recovering types and terms
  (`translateNF_injective`).
* So every translated term has a normal form, the image of a source normal
  form (`translate_normalForm`), and the target decides conversion by normal
  forms on all translated terms (`decidedOn_translations`).
* **The end-to-end theorem** (`translate_conv_iff`): two source terms are
  β-convertible exactly when their translations are convertible in the
  target, and (`betaConv_iff_normalForm_eq`) exactly when the normal forms the
  checker computes for the translations are equal.  The second is also the
  instance of the general transport `DecidedOn.transport`
  (`betaConv_iff_normalForm_eq_by_transport`).

**Instances.**  Holide's encoding (`TwoRoutes.holTheory`, decoding `term`,
arrow `arr`) and the STTfa hub (`TranslationTransport.STTfa.theory`, decoding
`eta`, arrow `arrow`) are theories of every encoding that uses these two names
and names nothing else after a rule head of the theory (`holideHub`,
`sttfaHub`).  In Holide's theory the decoding `term c` of a named code is
normal and one rule takes `term (arr a b)` to `term a → term b`.  The STTfa hub
is transcribed from Logipedia's theory file (`TranslationTransport.STTfa.rules`):
there `eta` is defined as `λ t. etap (p t)`, so `eta c` unfolds to the normal
`etap (p c)` (`sttfa_eta_unfold`, `sttfa_etap_normal`), and `eta (arrow a b)`
reaches `eta a → eta b` through `etap` (`sttfa_eta_arrow`).

**Scope.**  Normalization is used only where it is proved: the source's.  The
target is shown to normalize on translated terms, not on every term it types.
The connectives and the constants of the signature are constants of the target
without rules: the STTfa rules for `impl` and `forall` act on proofs (`eps`),
which translated terms do not contain.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.HOLHub

open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 lookupBody)
open Mettapedia.Logic.Relation (Confluent IsNormal IsNormalFormOf DecidedOn)
open Mettapedia.Logic.HOL (Ty Ctx Var Term)
open Mettapedia.Logic.HOL.ContextualTrinity (BetaStep)

universe u v

/-! ## The encoding -/

/-- The symbols an encoding names: the sorts and the constants of the
signature, the type of propositions, the function-type former and the
connectives. -/
inductive Symbol (Base : Type u) (Const : Ty Base → Type v) : Type (max u v) where
  | sort (b : Base)
  | const {τ : Ty Base} (c : Const τ)
  | bool
  | arrow
  | top
  | bot
  | and
  | or
  | imp
  | not
  | eq
  | all
  | ex

/-- An encoding of a HOL signature in the λΠ-calculus modulo: the constant that
decodes type codes, and an injective naming of the symbols. -/
structure Encoding (Base : Type u) (Const : Ty Base → Type v) where
  el : String
  name : Symbol Base Const → String
  injective : Function.Injective name

/-- The de Bruijn position of a typed variable. -/
def varIndex {Base : Type u} : {Γ : Ctx Base} → {τ : Ty Base} → Var Γ τ → Nat
  | _, _, .vz => 0
  | _, _, .vs v => varIndex v + 1

/-- Steps of the source, as a relation. -/
abbrev SourceStep {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {τ : Ty Base} :
    Term Const Γ τ → Term Const Γ τ → Prop :=
  HOL.BetaNormalization.Reduces

/-- β-conversion of the source. -/
abbrev BetaConv {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {τ : Ty Base} :
    Term Const Γ τ → Term Const Γ τ → Prop :=
  Relation.EqvGen SourceStep

namespace Encoding

variable {Base : Type u} {Const : Ty Base → Type v} (e : Encoding Base Const)

/-- The constant of a symbol. -/
def sym (s : Symbol Base Const) : LF.Term := .con (e.name s)

/-- The decoding of a code. -/
def El (code : LF.Term) : LF.Term := .app (.con e.el) code

/-- The code of a function type. -/
def arr (domain codomain : LF.Term) : LF.Term := .app (.app (e.sym .arrow) domain) codomain

/-- The code of a simple type. -/
def code : Ty Base → LF.Term
  | .prop => e.sym .bool
  | .base b => e.sym (.sort b)
  | .arr σ τ => e.arr (code σ) (code τ)

/-- The decoding of a code, computed: products of the normal decodings `base`
of the named codes. -/
def elNF (base : Symbol Base Const → LF.Term) : Ty Base → LF.Term
  | .prop => base .bool
  | .base b => base (.sort b)
  | .arr σ τ => .pi (elNF base σ) (elNF base τ)

/-- `El (arrow a b) ↪ El a → El b`. -/
def arrowRule : RewriteRule :=
  ⟨e.El (e.arr (.var 1) (.var 0)), .pi (e.El (.var 1)) (e.El (.var 1))⟩

/-- A binary connective applied to its operands. -/
def binary (s : Symbol Base Const) (left right : LF.Term) : LF.Term :=
  .app (.app (e.sym s) left) right

/-- Equality at a type applied to its two sides. -/
def equation (τ : Ty Base) (left right : LF.Term) : LF.Term :=
  .app (.app (.app (e.sym .eq) (e.code τ)) left) right

/-- A quantifier over a type applied to an abstraction. -/
def binder (s : Symbol Base Const) (σ : Ty Base) (domain body : LF.Term) : LF.Term :=
  .app (.app (e.sym s) (e.code σ)) (.lam domain body)

/-- **The translation**: the shallow embedding, with the decoding of its type's
code as the domain of every abstraction. -/
def translate : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → LF.Term
  | _, _, .var v => .var (varIndex v)
  | _, _, .const c => e.sym (.const c)
  | _, _, .app f a => .app (translate f) (translate a)
  | _, _, .lam (σ := σ) b => .lam (e.El (e.code σ)) (translate b)
  | _, _, .top => e.sym .top
  | _, _, .bot => e.sym .bot
  | _, _, .and p q => e.binary .and (translate p) (translate q)
  | _, _, .or p q => e.binary .or (translate p) (translate q)
  | _, _, .imp p q => e.binary .imp (translate p) (translate q)
  | _, _, .not p => .app (e.sym .not) (translate p)
  | _, _, .eq (τ := τ) l r => e.equation τ (translate l) (translate r)
  | _, _, .all (σ := σ) b => e.binder .all σ (e.El (e.code σ)) (translate b)
  | _, _, .ex (σ := σ) b => e.binder .ex σ (e.El (e.code σ)) (translate b)

/-- The translation with every domain computed, over the normal decodings
`base` of the named codes. -/
def translateNF (base : Symbol Base Const → LF.Term) :
    {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → LF.Term
  | _, _, .var v => .var (varIndex v)
  | _, _, .const c => e.sym (.const c)
  | _, _, .app f a => .app (translateNF base f) (translateNF base a)
  | _, _, .lam (σ := σ) b => .lam (elNF base σ) (translateNF base b)
  | _, _, .top => e.sym .top
  | _, _, .bot => e.sym .bot
  | _, _, .and p q => e.binary .and (translateNF base p) (translateNF base q)
  | _, _, .or p q => e.binary .or (translateNF base p) (translateNF base q)
  | _, _, .imp p q => e.binary .imp (translateNF base p) (translateNF base q)
  | _, _, .not p => .app (e.sym .not) (translateNF base p)
  | _, _, .eq (τ := τ) l r => e.equation τ (translateNF base l) (translateNF base r)
  | _, _, .all (σ := σ) b => e.binder .all σ (elNF base σ) (translateNF base b)
  | _, _, .ex (σ := σ) b => e.binder .ex σ (elNF base σ) (translateNF base b)

/-! ### Closed pieces -/

theorem code_closed : ∀ τ : Ty Base, Closed (e.code τ)
  | .prop => .con
  | .base _ => .con
  | .arr σ τ => .app (.app .con (code_closed σ)) (code_closed τ)

theorem El_code_closed (τ : Ty Base) : Closed (e.El (e.code τ)) := .app .con (e.code_closed τ)

theorem elNF_closed {base : Symbol Base Const → LF.Term} (closed : ∀ s, Closed (base s)) :
    ∀ τ : Ty Base, Closed (Encoding.elNF base τ)
  | .prop => closed _
  | .base _ => closed _
  | .arr σ τ => .pi (elNF_closed closed σ) ((elNF_closed closed τ).mono (Nat.zero_le 1))

/-! ### Renaming and substitution -/

/-- A renaming that shifts the variables from `k` on keeps doing so under a
binder, from `k + 1` on. -/
theorem shift_lift {Γ Δ : Ctx Base} {k : Nat} {r : HOL.Rename Base Γ Δ} {σ : Ty Base}
    (shift : ∀ {τ : Ty Base} (v : Var Γ τ),
      varIndex (r v) = if varIndex v < k then varIndex v else varIndex v + 1) :
    ∀ {τ : Ty Base} (v : Var (σ :: Γ) τ), varIndex (HOL.Rename.lift r v) =
      if varIndex v < k + 1 then varIndex v else varIndex v + 1
  | _, .vz => by simp [HOL.Rename.lift, varIndex]
  | _, .vs prior => by
      simp only [HOL.Rename.lift, varIndex]
      rw [shift prior]
      by_cases below : varIndex prior < k
      · have below' : varIndex prior + 1 < k + 1 := by omega
        simp [below, below']
      · have notBelow : ¬ varIndex prior + 1 < k + 1 := by omega
        simp [below, notBelow]

theorem translate_rename : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) {Δ : Ctx Base}
    (k : Nat) (r : HOL.Rename Base Γ Δ),
    (∀ {σ : Ty Base} (v : Var Γ σ),
      varIndex (r v) = if varIndex v < k then varIndex v else varIndex v + 1) →
    e.translate (HOL.rename r t) = lift 1 k (e.translate t) := by
  intro Γ τ t
  induction t with
  | var v =>
      intro Δ k r shift
      simp only [HOL.rename, translate, LFTyping.lift, shift]
  | const c => intro Δ k r _; rfl
  | app f a ihf iha =>
      intro Δ k r shift
      simp only [HOL.rename, translate, LFTyping.lift]
      rw [ihf k r shift, iha k r shift]
  | @lam σ Γ τ body ih =>
      intro Δ k r shift
      simp only [HOL.rename, translate, LFTyping.lift]
      rw [(e.El_code_closed σ).lift, ih (k + 1) (HOL.Rename.lift r) (shift_lift shift)]
  | top => intro Δ k r _; rfl
  | bot => intro Δ k r _; rfl
  | and p q ihp ihq =>
      intro Δ k r shift
      simp only [HOL.rename, translate, binary, sym, LFTyping.lift]
      rw [ihp k r shift, ihq k r shift]
  | or p q ihp ihq =>
      intro Δ k r shift
      simp only [HOL.rename, translate, binary, sym, LFTyping.lift]
      rw [ihp k r shift, ihq k r shift]
  | imp p q ihp ihq =>
      intro Δ k r shift
      simp only [HOL.rename, translate, binary, sym, LFTyping.lift]
      rw [ihp k r shift, ihq k r shift]
  | not p ih =>
      intro Δ k r shift
      simp only [HOL.rename, translate, sym, LFTyping.lift]
      rw [ih k r shift]
  | @eq Γ τ l r' ihl ihr =>
      intro Δ k r shift
      simp only [HOL.rename, translate, equation, sym, LFTyping.lift]
      rw [(e.code_closed τ).lift, ihl k r shift, ihr k r shift]
  | @all σ Γ body ih =>
      intro Δ k r shift
      simp only [HOL.rename, translate, binder, sym, LFTyping.lift]
      rw [(e.code_closed σ).lift, (e.El_code_closed σ).lift,
        ih (k + 1) (HOL.Rename.lift r) (shift_lift shift)]
  | @ex σ Γ body ih =>
      intro Δ k r shift
      simp only [HOL.rename, translate, binder, sym, LFTyping.lift]
      rw [(e.code_closed σ).lift, (e.El_code_closed σ).lift,
        ih (k + 1) (HOL.Rename.lift r) (shift_lift shift)]

theorem translate_weaken {Γ : Ctx Base} {τ σ : Ty Base} (t : Term Const Γ τ) :
    e.translate (HOL.rename (HOL.Rename.weaken (σ := σ)) t) = lift 1 0 (e.translate t) :=
  e.translate_rename t 0 HOL.Rename.weaken fun v => by simp [HOL.Rename.weaken, varIndex]

/-- A substitution that replaces the variable `k` keeps doing so under a
binder, at `k + 1`. -/
theorem image_lift {Γ Δ : Ctx Base} {k : Nat} {σs : HOL.Subst Const Γ Δ} {replacement : LF.Term}
    {σ : Ty Base}
    (image : ∀ {τ : Ty Base} (v : Var Γ τ), e.translate (σs v) =
      if varIndex v < k then .var (varIndex v)
      else if varIndex v = k then lift k 0 replacement else .var (varIndex v - 1)) :
    ∀ {τ : Ty Base} (v : Var (σ :: Γ) τ), e.translate (HOL.Subst.lift σs v) =
      if varIndex v < k + 1 then .var (varIndex v)
      else if varIndex v = k + 1 then lift (k + 1) 0 replacement else .var (varIndex v - 1)
  | _, .vz => by simp [HOL.Subst.lift, varIndex, translate]
  | _, .vs prior => by
      simp only [HOL.Subst.lift, varIndex]
      rw [e.translate_weaken, image prior]
      by_cases below : varIndex prior < k
      · have below' : varIndex prior + 1 < k + 1 := by omega
        simp only [below, below', if_true, LFTyping.lift, Nat.not_lt_zero, if_false]
      · by_cases same : varIndex prior = k
        · subst same
          simp only [lt_irrefl, if_false, if_true]
          rw [lift_lift_same, Nat.add_comm 1]
        · have notBelow : ¬ varIndex prior + 1 < k + 1 := by omega
          have notSame : ¬ varIndex prior + 1 = k + 1 := by omega
          simp only [below, same, notBelow, notSame, if_false, LFTyping.lift, Nat.not_lt_zero]
          congr 1
          omega

theorem translate_substitute : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ)
    {Δ : Ctx Base} (k : Nat) (σs : HOL.Subst Const Γ Δ) (replacement : LF.Term),
    (∀ {σ : Ty Base} (v : Var Γ σ), e.translate (σs v) =
      if varIndex v < k then .var (varIndex v)
      else if varIndex v = k then lift k 0 replacement else .var (varIndex v - 1)) →
    e.translate (HOL.subst σs t) = subst k (lift k 0 replacement) (e.translate t) := by
  intro Γ τ t
  induction t with
  | var v =>
      intro Δ k σs replacement image
      simp only [HOL.subst, translate, LFTyping.subst, image]
      by_cases below : varIndex v < k
      · have notSame : varIndex v ≠ k := by omega
        have notAbove : ¬ k < varIndex v := by omega
        simp [below, notSame, notAbove]
      · by_cases same : varIndex v = k
        · simp [same]
        · have above : k < varIndex v := by omega
          simp [below, same, above]
  | const c => intro Δ k σs replacement _; rfl
  | app f a ihf iha =>
      intro Δ k σs replacement image
      simp only [HOL.subst, translate, LFTyping.subst]
      rw [ihf k σs replacement image, iha k σs replacement image]
  | @lam σ Γ τ body ih =>
      intro Δ k σs replacement image
      simp only [HOL.subst, translate, LFTyping.subst]
      rw [(e.El_code_closed σ).subst, lift_lift_same, Nat.add_comm 1 k,
        ih (k + 1) (HOL.Subst.lift σs) replacement (e.image_lift image)]
  | top => intro Δ k σs replacement _; rfl
  | bot => intro Δ k σs replacement _; rfl
  | and p q ihp ihq =>
      intro Δ k σs replacement image
      simp only [HOL.subst, translate, binary, sym, LFTyping.subst]
      rw [ihp k σs replacement image, ihq k σs replacement image]
  | or p q ihp ihq =>
      intro Δ k σs replacement image
      simp only [HOL.subst, translate, binary, sym, LFTyping.subst]
      rw [ihp k σs replacement image, ihq k σs replacement image]
  | imp p q ihp ihq =>
      intro Δ k σs replacement image
      simp only [HOL.subst, translate, binary, sym, LFTyping.subst]
      rw [ihp k σs replacement image, ihq k σs replacement image]
  | not p ih =>
      intro Δ k σs replacement image
      simp only [HOL.subst, translate, sym, LFTyping.subst]
      rw [ih k σs replacement image]
  | @eq Γ τ l r ihl ihr =>
      intro Δ k σs replacement image
      simp only [HOL.subst, translate, equation, sym, LFTyping.subst]
      rw [(e.code_closed τ).subst, ihl k σs replacement image, ihr k σs replacement image]
  | @all σ Γ body ih =>
      intro Δ k σs replacement image
      simp only [HOL.subst, translate, binder, sym, LFTyping.subst]
      rw [(e.code_closed σ).subst, (e.El_code_closed σ).subst, lift_lift_same, Nat.add_comm 1 k,
        ih (k + 1) (HOL.Subst.lift σs) replacement (e.image_lift image)]
  | @ex σ Γ body ih =>
      intro Δ k σs replacement image
      simp only [HOL.subst, translate, binder, sym, LFTyping.subst]
      rw [(e.code_closed σ).subst, (e.El_code_closed σ).subst, lift_lift_same, Nat.add_comm 1 k,
        ih (k + 1) (HOL.Subst.lift σs) replacement (e.image_lift image)]

/-- **Translation commutes with opening the newest variable.** -/
theorem translate_instantiate {Γ : Ctx Base} {σ τ : Ty Base} (body : Term Const (σ :: Γ) τ)
    (argument : Term Const Γ σ) :
    e.translate (HOL.instantiate argument body) =
      subst0 (e.translate argument) (e.translate body) := by
  have general := e.translate_substitute body 0 (HOL.Subst.single argument) (e.translate argument)
    (by
      intro τ v
      cases v with
      | vz => simp [HOL.Subst.single, varIndex, Mettapedia.GSLT.Dedukti.lift_zero]
      | vs prior => simp [HOL.Subst.single, varIndex, translate])
  rw [Mettapedia.GSLT.Dedukti.lift_zero] at general
  exact general

/-! ### Steps -/

variable {e}

/-- **Every β-step of the source is a step of the target**, in every theory. -/
theorem translate_betaStep {theory : Theory} {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (step : BetaStep s t) : Step theory (e.translate s) (e.translate t) := by
  induction step with
  | beta body argument =>
      rw [e.translate_instantiate]
      exact Step.root (.beta _ _ _)
  | appFun _ _ ih => exact ih.plug (.appFunction .hole _)
  | appArg _ _ ih => exact ih.plug (.appArgument _ .hole)
  | lam _ ih => exact ih.plug (.lamBody _ .hole)
  | andLeft _ _ ih => exact ih.plug (.appFunction (.appArgument _ .hole) _)
  | andRight _ _ ih => exact ih.plug (.appArgument _ .hole)
  | orLeft _ _ ih => exact ih.plug (.appFunction (.appArgument _ .hole) _)
  | orRight _ _ ih => exact ih.plug (.appArgument _ .hole)
  | impLeft _ _ ih => exact ih.plug (.appFunction (.appArgument _ .hole) _)
  | impRight _ _ ih => exact ih.plug (.appArgument _ .hole)
  | not _ ih => exact ih.plug (.appArgument _ .hole)
  | eqLeft _ _ ih => exact ih.plug (.appFunction (.appArgument _ .hole) _)
  | eqRight _ _ ih => exact ih.plug (.appArgument _ .hole)
  | all _ ih => exact ih.plug (.appArgument _ (.lamBody _ .hole))
  | ex _ ih => exact ih.plug (.appArgument _ (.lamBody _ .hole))

theorem translate_reduces {theory : Theory} {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (steps : HOL.BetaNormalization.ReducesStar s t) :
    Reduces theory (e.translate s) (e.translate t) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact step.elim fun one => ih.tail (translate_betaStep one)

theorem translate_conv {theory : Theory} {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (converted : BetaConv s t) : Conv theory (e.translate s) (e.translate t) := by
  induction converted with
  | rel _ _ step => exact step.elim fun one => .rel _ _ (translate_betaStep one)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

variable (e)

/-- The rule of the arrow at two codes: `El (code (σ ⇒ τ))` steps to the
product of the decodings. -/
theorem step_El_code_arr {theory : Theory} (arrowRule : theory.rule e.arrowRule) (σ τ : Ty Base) :
    Step theory (e.El (e.code (.arr σ τ))) (.pi (e.El (e.code σ)) (e.El (e.code τ))) := by
  have root := RootStep.rule (theory := theory) (rule := e.arrowRule)
    (fun index => if index = 0 then e.code τ else e.code σ) arrowRule
  have closedτ := (e.code_closed τ).lift 1 0
  simpa [Encoding.arrowRule, Encoding.El, Encoding.arr, Encoding.code, Encoding.sym, inst,
    Dedukti.instantiate, Mettapedia.GSLT.Dedukti.lift_zero, closedτ] using Step.root root

end Encoding

/-! ## Normal forms of the source -/

section Source

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Every term has a normal form, by strong normalization. -/
theorem exists_normalForm {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    ∃ n, HOL.BetaNormalization.ReducesStar t n ∧ HOL.BetaNormalization.Normal n := by
  induction HOL.BetaNormalization.stronglyNormalizing t with
  | intro t _ ih =>
      by_cases reducible : ∃ t', HOL.BetaNormalization.Reduces t t'
      · obtain ⟨t', step⟩ := reducible
        obtain ⟨n, reduces, normal⟩ := ih t' step
        exact ⟨n, Relation.ReflTransGen.head step reduces, normal⟩
      · exact ⟨t, .refl, fun t' step => reducible ⟨t', step⟩⟩

/-- β-reduction of the source is confluent. -/
theorem sourceConfluent {Γ : Ctx Base} {τ : Ty Base} :
    Confluent (SourceStep (Const := Const) (Γ := Γ) (τ := τ)) :=
  fun _ _ _ toLeft toRight => HOL.BetaNormalization.confluent toLeft toRight

/-- A subterm of a normal term at a congruence position is normal. -/
theorem normal_of_congr {Γ Γ' : Ctx Base} {σ τ : Ty Base} (f : Term Const Γ σ → Term Const Γ' τ)
    (congr : ∀ {a b : Term Const Γ σ}, BetaStep a b → BetaStep (f a) (f b)) {a : Term Const Γ σ}
    (normal : HOL.BetaNormalization.Normal (f a)) : HOL.BetaNormalization.Normal a :=
  fun b step => step.elim fun one => normal (f b) ⟨congr one⟩

/-- `λ x. f x`, in the context `f : σ ⇒ τ`. -/
def etaExpanded (σ τ : Ty Base) : Term Const [.arr σ τ] (.arr σ τ) :=
  .lam (.app (.var (.vs .vz)) (.var .vz))

/-- `f`, in the context `f : σ ⇒ τ`. -/
def etaContracted (σ τ : Ty Base) : Term Const [.arr σ τ] (.arr σ τ) := .var .vz

theorem etaExpanded_normal (σ τ : Ty Base) :
    HOL.BetaNormalization.Normal (etaExpanded (Const := Const) σ τ) := by
  intro target step
  obtain ⟨_, inner, _⟩ := HOL.BetaNormalization.lam_cases step
  rcases HOL.BetaNormalization.app_cases inner with ⟨_, same, _⟩ | ⟨_, more, _⟩ | ⟨_, more, _⟩
  · cases same
  · exact HOL.BetaNormalization.var_irreducible _ _ more
  · exact HOL.BetaNormalization.var_irreducible _ _ more

end Source

/-! ## Theories of the encoding -/

/-- A theory of the λΠ-calculus modulo that hosts an encoding: its rules are
headed by constants, it is confluent, and it defines none of the named
symbols; the decoding of each named code reduces to a normal form `elAt`
(closed, injective, not a product), and the decoding of a function code
reduces to the product of the decodings. -/
structure HubTheory {Base : Type u} {Const : Ty Base → Type v} (e : Encoding Base Const) where
  theory : Theory
  headed : theory.Headed
  confluent : Confluent (Step theory)
  rigid : ∀ s, ¬ theory.Defines (e.name s)
  /-- The normal form of the decoding of a named code. -/
  elAt : Symbol Base Const → LF.Term
  elAt_reduces : ∀ s, Reduces theory (e.El (e.sym s)) (elAt s)
  elAt_normal : ∀ s, IsNormal (Step theory) (elAt s)
  elAt_closed : ∀ s, Closed (elAt s)
  elAt_injective : Function.Injective elAt
  elAt_not_pi : ∀ s domain body, elAt s ≠ .pi domain body
  arrow_reduces : ∀ σ τ : Ty Base,
    Reduces theory (e.El (e.code (.arr σ τ))) (.pi (e.El (e.code σ)) (e.El (e.code τ)))

namespace HubTheory

variable {Base : Type u} {Const : Ty Base → Type v} {e : Encoding Base Const} (h : HubTheory e)

/-- **Decodings of codes compute.** -/
theorem reduces_El_code : ∀ τ : Ty Base, Reduces h.theory (e.El (e.code τ)) (Encoding.elNF h.elAt τ)
  | .prop => h.elAt_reduces _
  | .base _ => h.elAt_reduces _
  | .arr σ τ => (h.arrow_reduces σ τ).trans (Reduces.pi (reduces_El_code σ) (reduces_El_code τ))

/-- The translation reduces to the translation with computed domains. -/
theorem reduces_translateNF : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ),
    Reduces h.theory (e.translate t) (e.translateNF h.elAt t) := by
  intro Γ τ t
  induction t with
  | var v => exact .refl
  | const c => exact .refl
  | app f a ihf iha => exact Reduces.app ihf iha
  | @lam σ Γ τ body ih => exact Reduces.lam (h.reduces_El_code σ) ih
  | top => exact .refl
  | bot => exact .refl
  | and p q ihp ihq => exact Reduces.app (Reduces.app .refl ihp) ihq
  | or p q ihp ihq => exact Reduces.app (Reduces.app .refl ihp) ihq
  | imp p q ihp ihq => exact Reduces.app (Reduces.app .refl ihp) ihq
  | not p ih => exact Reduces.app .refl ih
  | eq l r ihl ihr => exact Reduces.app (Reduces.app .refl ihl) ihr
  | @all σ Γ body ih => exact Reduces.app .refl (Reduces.lam (h.reduces_El_code σ) ih)
  | @ex σ Γ body ih => exact Reduces.app .refl (Reduces.lam (h.reduces_El_code σ) ih)

/-! ### Normality -/

theorem sym_normal (s : Symbol Base Const) : IsNormal (Step h.theory) (e.sym s) :=
  fun _ step => RootStep.not_of_rigid h.headed (h.rigid s) rfl step.con_inv

/-- An application whose head is a named symbol is normal when its function
and its argument are. -/
theorem app_normal {function argument : LF.Term} {s : Symbol Base Const}
    (head : headConst function = some (e.name s)) (functionNormal : IsNormal (Step h.theory) function)
    (argumentNormal : IsNormal (Step h.theory) argument) :
    IsNormal (Step h.theory) (.app function argument) := by
  intro target step
  rcases step.app_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · exact RootStep.not_of_rigid h.headed (h.rigid s) (by simpa [headConst] using head) root
  · exact functionNormal _ inner
  · exact argumentNormal _ inner

theorem lam_normal {domain body : LF.Term} (domainNormal : IsNormal (Step h.theory) domain)
    (bodyNormal : IsNormal (Step h.theory) body) : IsNormal (Step h.theory) (.lam domain body) := by
  intro target step
  rcases step.lam_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · exact RootStep.not_lam h.headed root
  · exact domainNormal _ inner
  · exact bodyNormal _ inner

theorem code_normal : ∀ τ : Ty Base, IsNormal (Step h.theory) (e.code τ)
  | .prop => h.sym_normal _
  | .base _ => h.sym_normal _
  | .arr σ τ => h.app_normal (s := .arrow) rfl (h.app_normal (s := .arrow) rfl (h.sym_normal _)
      (code_normal σ)) (code_normal τ)

/-- **Computed decodings are normal.** -/
theorem elNF_normal : ∀ τ : Ty Base, IsNormal (Step h.theory) (Encoding.elNF h.elAt τ)
  | .prop => h.elAt_normal _
  | .base _ => h.elAt_normal _
  | .arr σ τ => by
      intro target step
      rcases step.pi_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
      · exact RootStep.not_pi h.headed root
      · exact elNF_normal σ _ inner
      · exact elNF_normal τ _ inner

/-- The head of a translation with computed domains is a variable, an
abstraction or a named symbol. -/
theorem headConst_translateNF : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ),
    headConst (e.translateNF h.elAt t) = none ∨
      ∃ s, headConst (e.translateNF h.elAt t) = some (e.name s) := by
  intro Γ τ t
  induction t with
  | var v => exact Or.inl rfl
  | const c => exact Or.inr ⟨.const c, rfl⟩
  | app f a ihf _ => simpa [Encoding.translateNF, headConst] using ihf
  | lam body _ => exact Or.inl rfl
  | top => exact Or.inr ⟨.top, rfl⟩
  | bot => exact Or.inr ⟨.bot, rfl⟩
  | and p q _ _ => exact Or.inr ⟨.and, rfl⟩
  | or p q _ _ => exact Or.inr ⟨.or, rfl⟩
  | imp p q _ _ => exact Or.inr ⟨.imp, rfl⟩
  | not p _ => exact Or.inr ⟨.not, rfl⟩
  | eq l r _ _ => exact Or.inr ⟨.eq, rfl⟩
  | all body _ => exact Or.inr ⟨.all, rfl⟩
  | ex body _ => exact Or.inr ⟨.ex, rfl⟩

/-- **The translation of a source normal form, with computed domains, is
normal.** -/
theorem translateNF_normal : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ),
    HOL.BetaNormalization.Normal t → IsNormal (Step h.theory) (e.translateNF h.elAt t) := by
  intro Γ τ t
  induction t with
  | var v => intro _; exact var_normal h.headed _
  | const c => intro _; exact h.sym_normal _
  | @app Γ σ τ f a ihf iha =>
      intro sourceNormal target step
      rcases step.app_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
      · rcases root.defines h.headed with ⟨domain, body, argument, same⟩ | ⟨name, head, defines⟩
        · cases f with
          | var v => simp [Encoding.translateNF] at same
          | const c => simp [Encoding.translateNF, Encoding.sym] at same
          | app g b => simp [Encoding.translateNF] at same
          | lam body' => exact sourceNormal _ ⟨.beta body' a⟩
        · change headConst (e.translateNF h.elAt (.app f a)) = some name at head
          rcases h.headConst_translateNF (.app f a) with none | ⟨s, some⟩
          · rw [none] at head; cases head
          · rw [some] at head
            cases head
            exact h.rigid s defines
      · exact ihf (normal_of_congr (fun x => Term.app x a) (fun one => .appFun a one) sourceNormal)
          _ inner
      · exact iha (normal_of_congr (fun x => Term.app f x) (fun one => .appArg f one) sourceNormal)
          _ inner
  | lam body ih =>
      intro sourceNormal
      exact h.lam_normal (h.elNF_normal _)
        (ih (normal_of_congr Term.lam (fun one => .lam one) sourceNormal))
  | top => intro _; exact h.sym_normal _
  | bot => intro _; exact h.sym_normal _
  | and p q ihp ihq =>
      intro sourceNormal
      exact h.app_normal (s := .and) rfl (h.app_normal (s := .and) rfl (h.sym_normal _)
        (ihp (normal_of_congr (fun x => Term.and x q) (fun one => .andLeft q one) sourceNormal)))
        (ihq (normal_of_congr (fun x => Term.and p x) (fun one => .andRight p one) sourceNormal))
  | or p q ihp ihq =>
      intro sourceNormal
      exact h.app_normal (s := .or) rfl (h.app_normal (s := .or) rfl (h.sym_normal _)
        (ihp (normal_of_congr (fun x => Term.or x q) (fun one => .orLeft q one) sourceNormal)))
        (ihq (normal_of_congr (fun x => Term.or p x) (fun one => .orRight p one) sourceNormal))
  | imp p q ihp ihq =>
      intro sourceNormal
      exact h.app_normal (s := .imp) rfl (h.app_normal (s := .imp) rfl (h.sym_normal _)
        (ihp (normal_of_congr (fun x => Term.imp x q) (fun one => .impLeft q one) sourceNormal)))
        (ihq (normal_of_congr (fun x => Term.imp p x) (fun one => .impRight p one) sourceNormal))
  | not p ih =>
      intro sourceNormal
      exact h.app_normal (s := .not) rfl (h.sym_normal _)
        (ih (normal_of_congr Term.not (fun one => .not one) sourceNormal))
  | @eq Γ τ l r ihl ihr =>
      intro sourceNormal
      exact h.app_normal (s := .eq) rfl (h.app_normal (s := .eq) rfl
        (h.app_normal (s := .eq) rfl (h.sym_normal _) (h.code_normal τ))
        (ihl (normal_of_congr (fun x => Term.eq x r) (fun one => .eqLeft r one) sourceNormal)))
        (ihr (normal_of_congr (fun x => Term.eq l x) (fun one => .eqRight l one) sourceNormal))
  | @all σ Γ body ih =>
      intro sourceNormal
      exact h.app_normal (s := .all) rfl (h.app_normal (s := .all) rfl (h.sym_normal _)
        (h.code_normal σ)) (h.lam_normal (h.elNF_normal σ)
          (ih (normal_of_congr Term.all (fun one => .all one) sourceNormal)))
  | @ex σ Γ body ih =>
      intro sourceNormal
      exact h.app_normal (s := .ex) rfl (h.app_normal (s := .ex) rfl (h.sym_normal _)
        (h.code_normal σ)) (h.lam_normal (h.elNF_normal σ)
          (ih (normal_of_congr Term.ex (fun one => .ex one) sourceNormal)))

end HubTheory

/-! ## Injectivity -/

namespace Encoding

variable {Base : Type u} {Const : Ty Base → Type v} (e : Encoding Base Const)

theorem name_eq_iff {s s' : Symbol Base Const} : e.name s = e.name s' ↔ s = s' :=
  e.injective.eq_iff

theorem code_injective : ∀ {σ τ : Ty Base}, e.code σ = e.code τ → σ = τ
  | .prop, .prop, _ => rfl
  | .prop, .base _, same => by simp [code, sym, e.name_eq_iff] at same
  | .prop, .arr _ _, same => by simp [code, sym, arr] at same
  | .base _, .prop, same => by simp [code, sym, e.name_eq_iff] at same
  | .base _, .base _, same => by simpa [code, sym, e.name_eq_iff] using same
  | .base _, .arr _ _, same => by simp [code, sym, arr] at same
  | .arr _ _, .prop, same => by simp [code, sym, arr] at same
  | .arr _ _, .base _, same => by simp [code, sym, arr] at same
  | .arr σ₁ σ₂, .arr τ₁ τ₂, same => by
      simp only [code, arr, LF.Term.app.injEq] at same
      rw [code_injective same.1.2, code_injective same.2]

section Base

variable (base : Symbol Base Const → LF.Term) (inj : Function.Injective base)
  (notPi : ∀ s domain body, base s ≠ .pi domain body)

include inj notPi in
theorem elNF_injective {σ τ : Ty Base} (same : Encoding.elNF base σ = Encoding.elNF base τ) : σ = τ := by
  induction σ generalizing τ with
  | prop =>
      cases τ with
      | prop => rfl
      | base b => exact nomatch inj same
      | arr _ _ => exact absurd same (notPi _ _ _)
  | base b =>
      cases τ with
      | prop => exact nomatch inj same
      | base b' =>
          have named := inj same
          cases named
          rfl
      | arr _ _ => exact absurd same (notPi _ _ _)
  | arr σ₁ σ₂ ih₁ ih₂ =>
      cases τ with
      | prop => exact absurd same.symm (notPi _ _ _)
      | base _ => exact absurd same.symm (notPi _ _ _)
      | arr τ₁ τ₂ =>
          simp only [elNF, LF.Term.pi.injEq] at same
          rw [ih₁ same.1, ih₂ same.2]

theorem varIndex_injective {Γ : Ctx Base} {σ τ : Ty Base} (v : Var Γ σ) (w : Var Γ τ)
    (same : varIndex v = varIndex w) : σ = τ ∧ HEq v w := by
  induction v generalizing τ with
  | vz =>
      cases w with
      | vz => exact ⟨rfl, HEq.rfl⟩
      | vs w => simp [varIndex] at same
  | vs v ih =>
      cases w with
      | vz => simp [varIndex] at same
      | vs w =>
          obtain ⟨rfl, equal⟩ := ih w (by simpa [varIndex] using same)
          cases equal
          exact ⟨rfl, HEq.rfl⟩

/-- A term of a function type translates to a named symbol only when it is a
constant of the signature. -/
theorem translateNF_arrow_con {Γ : Ctx Base} {σ τ : Ty Base} (f : Term Const Γ (.arr σ τ))
    (s : Symbol Base Const) (same : e.translateNF base f = .con (e.name s)) :
    ∃ (τ' : Ty Base) (c : Const τ'), s = .const c := by
  cases f with
  | var v => simp [translateNF] at same
  | const c => exact ⟨_, c, (e.injective (by simpa [translateNF, sym] using same)).symm⟩
  | app g a => simp [translateNF] at same
  | lam b => simp [translateNF] at same

/-- A term of a function type translates to a named symbol applied to one
argument only when the symbol is a constant of the signature. -/
theorem translateNF_arrow_app_con {Γ : Ctx Base} {σ τ : Ty Base} (f : Term Const Γ (.arr σ τ))
    (s : Symbol Base Const) (x : LF.Term)
    (same : e.translateNF base f = .app (.con (e.name s)) x) :
    ∃ (τ' : Ty Base) (c : Const τ'), s = .const c := by
  cases f with
  | var v => simp [translateNF] at same
  | const c => simp [translateNF, sym] at same
  | app g a =>
      simp only [translateNF, LF.Term.app.injEq] at same
      exact e.translateNF_arrow_con base g s same.1
  | lam b => simp [translateNF] at same

/-- A term of a function type translates to a named symbol applied to two
arguments only when the symbol is a constant of the signature. -/
theorem translateNF_arrow_app_app_con {Γ : Ctx Base} {σ τ : Ty Base} (f : Term Const Γ (.arr σ τ))
    (s : Symbol Base Const) (x y : LF.Term)
    (same : e.translateNF base f = .app (.app (.con (e.name s)) x) y) :
    ∃ (τ' : Ty Base) (c : Const τ'), s = .const c := by
  cases f with
  | var v => simp [translateNF] at same
  | const c => simp [translateNF, sym] at same
  | app g a =>
      simp only [translateNF, LF.Term.app.injEq] at same
      exact e.translateNF_arrow_app_con base g s x same.1
  | lam b => simp [translateNF] at same

include inj notPi in
/-- **The translation with computed domains is injective**, recovering the
types as well. -/
theorem translateNF_injective : ∀ {Γ : Ctx Base} {τ : Ty Base} (s : Term Const Γ τ) {τ' : Ty Base}
    (t : Term Const Γ τ'), e.translateNF base s = e.translateNF base t → τ = τ' ∧ HEq s t := by
  intro Γ τ s
  induction s with
  | var v =>
      intro τ' t same
      cases t
      case var w =>
        obtain ⟨rfl, equal⟩ := varIndex_injective v w (by simpa [translateNF] using same)
        cases equal
        exact ⟨rfl, HEq.rfl⟩
      all_goals simp [translateNF, sym, binary, equation, binder] at same
  | const c =>
      intro τ' t same
      cases t
      case const c' =>
        have equal := e.injective (by simpa [translateNF, sym] using same)
        simp only [Symbol.const.injEq] at equal
        obtain ⟨rfl, equal⟩ := equal
        cases equal
        exact ⟨rfl, HEq.rfl⟩
      all_goals simp [translateNF, sym, binary, equation, binder, e.name_eq_iff] at same
  | @app Γ σ τ f a ihf iha =>
      intro τ' t same
      cases t
      case app =>
        simp only [translateNF, LF.Term.app.injEq] at same
        obtain ⟨types, equalF⟩ := ihf _ same.1
        simp only [Ty.arr.injEq] at types
        obtain ⟨rfl, rfl⟩ := types
        cases equalF
        obtain ⟨_, equalA⟩ := iha _ same.2
        cases equalA
        exact ⟨rfl, HEq.rfl⟩
      case and p q =>
        simp only [translateNF, binary, sym, LF.Term.app.injEq] at same
        obtain ⟨_, _, bad⟩ := e.translateNF_arrow_app_con base f _ _ same.1
        cases bad
      case or p q =>
        simp only [translateNF, binary, sym, LF.Term.app.injEq] at same
        obtain ⟨_, _, bad⟩ := e.translateNF_arrow_app_con base f _ _ same.1
        cases bad
      case imp p q =>
        simp only [translateNF, binary, sym, LF.Term.app.injEq] at same
        obtain ⟨_, _, bad⟩ := e.translateNF_arrow_app_con base f _ _ same.1
        cases bad
      case not p =>
        simp only [translateNF, sym, LF.Term.app.injEq] at same
        obtain ⟨_, _, bad⟩ := e.translateNF_arrow_con base f _ same.1
        cases bad
      case eq τ'' l r =>
        simp only [translateNF, equation, sym, LF.Term.app.injEq] at same
        obtain ⟨_, _, bad⟩ := e.translateNF_arrow_app_app_con base f _ _ _ same.1
        cases bad
      case all σ' body =>
        simp only [translateNF, binder, sym, LF.Term.app.injEq] at same
        obtain ⟨_, _, bad⟩ := e.translateNF_arrow_app_con base f _ _ same.1
        cases bad
      case ex σ' body =>
        simp only [translateNF, binder, sym, LF.Term.app.injEq] at same
        obtain ⟨_, _, bad⟩ := e.translateNF_arrow_app_con base f _ _ same.1
        cases bad
      all_goals simp [translateNF, sym] at same
  | @lam σ Γ τ body ih =>
      intro τ' t same
      cases t
      case lam σ' τ'' body' =>
        simp only [translateNF, LF.Term.lam.injEq] at same
        obtain rfl := Encoding.elNF_injective base inj notPi same.1
        obtain ⟨rfl, equal⟩ := ih body' same.2
        cases equal
        exact ⟨rfl, HEq.rfl⟩
      all_goals simp [translateNF, sym, binary, equation, binder] at same
  | top =>
      intro τ' t same
      cases t
      case top => exact ⟨rfl, HEq.rfl⟩
      all_goals simp [translateNF, sym, binary, equation, binder, e.name_eq_iff] at same
  | bot =>
      intro τ' t same
      cases t
      case bot => exact ⟨rfl, HEq.rfl⟩
      all_goals simp [translateNF, sym, binary, equation, binder, e.name_eq_iff] at same
  | and p q ihp ihq =>
      intro τ' t same
      cases t
      case and p' q' =>
        simp only [translateNF, binary, LF.Term.app.injEq] at same
        obtain ⟨_, equalP⟩ := ihp p' same.1.2
        obtain ⟨_, equalQ⟩ := ihq q' same.2
        cases equalP
        cases equalQ
        exact ⟨rfl, HEq.rfl⟩
      case app =>
        simp only [translateNF, binary, sym, LF.Term.app.injEq] at same
        obtain ⟨_, _, bad⟩ := e.translateNF_arrow_app_con base _ _ _ same.1.symm
        cases bad
      all_goals simp [translateNF, sym, binary, equation, binder, e.name_eq_iff] at same
  | or p q ihp ihq =>
      intro τ' t same
      cases t
      case or p' q' =>
        simp only [translateNF, binary, LF.Term.app.injEq] at same
        obtain ⟨_, equalP⟩ := ihp p' same.1.2
        obtain ⟨_, equalQ⟩ := ihq q' same.2
        cases equalP
        cases equalQ
        exact ⟨rfl, HEq.rfl⟩
      case app =>
        simp only [translateNF, binary, sym, LF.Term.app.injEq] at same
        obtain ⟨_, _, bad⟩ := e.translateNF_arrow_app_con base _ _ _ same.1.symm
        cases bad
      all_goals simp [translateNF, sym, binary, equation, binder, e.name_eq_iff] at same
  | imp p q ihp ihq =>
      intro τ' t same
      cases t
      case imp p' q' =>
        simp only [translateNF, binary, LF.Term.app.injEq] at same
        obtain ⟨_, equalP⟩ := ihp p' same.1.2
        obtain ⟨_, equalQ⟩ := ihq q' same.2
        cases equalP
        cases equalQ
        exact ⟨rfl, HEq.rfl⟩
      case app =>
        simp only [translateNF, binary, sym, LF.Term.app.injEq] at same
        obtain ⟨_, _, bad⟩ := e.translateNF_arrow_app_con base _ _ _ same.1.symm
        cases bad
      all_goals simp [translateNF, sym, binary, equation, binder, e.name_eq_iff] at same
  | not p ih =>
      intro τ' t same
      cases t
      case not p' =>
        simp only [translateNF, LF.Term.app.injEq] at same
        obtain ⟨_, equal⟩ := ih p' same.2
        cases equal
        exact ⟨rfl, HEq.rfl⟩
      case app =>
        simp only [translateNF, sym, LF.Term.app.injEq] at same
        obtain ⟨_, _, bad⟩ := e.translateNF_arrow_con base _ _ same.1.symm
        cases bad
      all_goals simp [translateNF, sym, binary, equation, binder] at same
  | @eq Γ τ l r ihl ihr =>
      intro τ' t same
      cases t
      case eq τ'' l' r' =>
        simp only [translateNF, equation, LF.Term.app.injEq] at same
        obtain rfl := e.code_injective same.1.1.2
        obtain ⟨_, equalL⟩ := ihl l' same.1.2
        obtain ⟨_, equalR⟩ := ihr r' same.2
        cases equalL
        cases equalR
        exact ⟨rfl, HEq.rfl⟩
      case app =>
        simp only [translateNF, equation, sym, LF.Term.app.injEq] at same
        obtain ⟨_, _, bad⟩ := e.translateNF_arrow_app_app_con base _ _ _ _ same.1.symm
        cases bad
      all_goals simp [translateNF, sym, binary, equation, binder] at same
  | @all σ Γ body ih =>
      intro τ' t same
      cases t
      case all σ' body' =>
        simp only [translateNF, binder, LF.Term.app.injEq, LF.Term.lam.injEq] at same
        obtain rfl := Encoding.elNF_injective base inj notPi same.2.1
        obtain ⟨_, equal⟩ := ih body' same.2.2
        cases equal
        exact ⟨rfl, HEq.rfl⟩
      case app =>
        simp only [translateNF, binder, sym, LF.Term.app.injEq] at same
        obtain ⟨_, _, bad⟩ := e.translateNF_arrow_app_con base _ _ _ same.1.symm
        cases bad
      all_goals simp [translateNF, sym, binary, equation, binder, e.name_eq_iff] at same
  | @ex σ Γ body ih =>
      intro τ' t same
      cases t
      case ex σ' body' =>
        simp only [translateNF, binder, LF.Term.app.injEq, LF.Term.lam.injEq] at same
        obtain rfl := Encoding.elNF_injective base inj notPi same.2.1
        obtain ⟨_, equal⟩ := ih body' same.2.2
        cases equal
        exact ⟨rfl, HEq.rfl⟩
      case app =>
        simp only [translateNF, binder, sym, LF.Term.app.injEq] at same
        obtain ⟨_, _, bad⟩ := e.translateNF_arrow_app_con base _ _ _ same.1.symm
        cases bad
      all_goals simp [translateNF, sym, binary, equation, binder, e.name_eq_iff] at same

end Base

end Encoding

/-! ## The end-to-end theorems -/

namespace HubTheory

variable {Base : Type u} {Const : Ty Base → Type v} {e : Encoding Base Const} (h : HubTheory e)

/-- **The translation of a term has a normal form**: the translation, with
computed domains, of a source normal form. -/
theorem translate_normalForm {Γ : Ctx Base} {τ : Ty Base} {t n : Term Const Γ τ}
    (reduces : HOL.BetaNormalization.ReducesStar t n) (normal : HOL.BetaNormalization.Normal n) :
    IsNormalFormOf (Step h.theory) (e.translate t) (e.translateNF h.elAt n) :=
  ⟨(Encoding.translate_reduces reduces).trans (h.reduces_translateNF n), h.translateNF_normal n normal⟩

/-- **The checker decides conversion by normal forms on all translated terms.** -/
theorem decidedOn_translations (Γ : Ctx Base) (τ : Ty Base) :
    DecidedOn (Step h.theory) (Set.range (e.translate (Γ := Γ) (τ := τ))) :=
  Mettapedia.Logic.Relation.decidedOn_of_confluent h.confluent (by
    rintro _ ⟨t, rfl⟩
    obtain ⟨n, reduces, normal⟩ := exists_normalForm t
    exact ⟨_, h.translate_normalForm reduces normal⟩)

/-- **Convertible translations come from one source normal form.** -/
theorem normalForm_eq_of_conv {Γ : Ctx Base} {τ : Ty Base} {s t ns nt : Term Const Γ τ}
    (converted : Conv h.theory (e.translate s) (e.translate t))
    (toNs : HOL.BetaNormalization.ReducesStar s ns) (normalNs : HOL.BetaNormalization.Normal ns)
    (toNt : HOL.BetaNormalization.ReducesStar t nt) (normalNt : HOL.BetaNormalization.Normal nt) :
    ns = nt := by
  have same := (Mettapedia.Logic.Relation.conv_iff_normalForm_eq_of_confluent h.confluent
    (h.translate_normalForm toNs normalNs) (h.translate_normalForm toNt normalNt)).mp converted
  obtain ⟨_, equal⟩ := e.translateNF_injective h.elAt h.elAt_injective h.elAt_not_pi ns nt same
  exact eq_of_heq equal

/-- **End to end**: two source terms are β-convertible exactly when their
translations are convertible in the theory of the encoding. -/
theorem translate_conv_iff {Γ : Ctx Base} {τ : Ty Base} (s t : Term Const Γ τ) :
    Conv h.theory (e.translate s) (e.translate t) ↔ BetaConv s t := by
  refine ⟨fun converted => ?_, Encoding.translate_conv⟩
  obtain ⟨ns, toNs, normalNs⟩ := exists_normalForm s
  obtain ⟨nt, toNt, normalNt⟩ := exists_normalForm t
  obtain rfl := h.normalForm_eq_of_conv converted toNs normalNs toNt normalNt
  exact .trans _ _ _ (Mettapedia.Logic.Relation.IsNormalFormOf.eqvGen ⟨toNs, normalNs⟩)
    (.symm _ _ (Mettapedia.Logic.Relation.IsNormalFormOf.eqvGen ⟨toNt, normalNt⟩))

/-- **End to end, read off the checker's normal forms**: two source terms are
β-convertible exactly when the normal forms computed for their translations
are equal, whichever normal forms are computed. -/
theorem betaConv_iff_normalForm_eq {Γ : Ctx Base} {τ : Ty Base} (s t : Term Const Γ τ)
    {n m : LF.Term} (normalS : IsNormalFormOf (Step h.theory) (e.translate s) n)
    (normalT : IsNormalFormOf (Step h.theory) (e.translate t) m) : BetaConv s t ↔ n = m :=
  (h.translate_conv_iff s t).symm.trans
    ((h.decidedOn_translations Γ τ).2 _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ n m normalS normalT)

/-- The same, as an instance of the general transport of decisions along a
translation: preservation, reflection and the image in the fiber. -/
theorem betaConv_iff_normalForm_eq_by_transport {Γ : Ctx Base} {τ : Ty Base} (s t : Term Const Γ τ)
    {n m : LF.Term} (normalS : IsNormalFormOf (Step h.theory) (e.translate s) n)
    (normalT : IsNormalFormOf (Step h.theory) (e.translate t) m) : BetaConv s t ↔ n = m := by
  have transported := Mettapedia.Logic.Relation.DecidedOn.transport (S := Set.univ)
    (e.translate (Γ := Γ) (τ := τ)) (finer := BetaConv) (coarser := BetaConv)
    (fun _ _ converted => Encoding.translate_conv converted)
    (fun a b converted => (h.translate_conv_iff a b).mp converted)
    (by simpa [Set.image_univ] using h.decidedOn_translations Γ τ)
    (Set.mem_univ s) (Set.mem_univ t) normalS normalT
  exact ⟨transported.1, transported.2⟩

/-! ### η is not a conversion of a hub -/

/-- **η is not a conversion of a hub**: the translations of `λ x. f x` and `f`
are not convertible. -/
theorem eta_not_conv (σ τ : Ty Base) :
    ¬ Conv h.theory (e.translate (etaExpanded (Const := Const) σ τ))
      (e.translate (etaContracted (Const := Const) σ τ)) := by
  intro converted
  have same := h.normalForm_eq_of_conv converted .refl (etaExpanded_normal σ τ) .refl
    (fun target => HOL.BetaNormalization.var_irreducible _ target)
  cases same

end HubTheory

/-! ## The two hubs -/

/-- A root step of an application of a constant is an instance of a rule. -/
theorem rootStep_app_con {theory : Theory} {name : String} {argument target : LF.Term}
    (root : RootStep theory (.app (.con name) argument) target) :
    ∃ rule assignment, theory.rule rule ∧ inst assignment rule.lhs = .app (.con name) argument := by
  generalize sourceEq : LF.Term.app (.con name) argument = source at root
  cases root with
  | beta domain body argument' => cases sourceEq
  | delta defined => cases sourceEq
  | rule assignment member =>
      first
        | exact ⟨_, assignment, member, sourceEq.symm⟩
        | exact ⟨_, assignment, member, rfl⟩

/-- A constant without a definition, which is no instance of a rule's left
side, has no step. -/
theorem con_normal_of {theory : Theory} {name : String} (undefined : theory.body name = none)
    (unmatched : ∀ rule assignment, theory.rule rule → inst assignment rule.lhs ≠ .con name) :
    IsNormal (Step theory) (.con name) := by
  intro target step
  rcases RootStep.con_inv step.con_inv with defined | ⟨rule, assignment, member, shape, _⟩
  · rw [undefined] at defined; cases defined
  · exact unmatched rule assignment member shape

section Hubs

variable {Base : Type u} {Const : Ty Base → Type v}

theorem holide_rules {rule : RewriteRule} (member : TwoRoutes.holTheory.rule rule) :
    rule = TwoRoutes.termArrow :=
  List.mem_singleton.mp member

theorem holide_undefined (name : String) : TwoRoutes.holTheory.body name = none := by
  simp [TwoRoutes.holTheory, Theory.ofSig, TwoRoutes.holSig, lookupBody]

/-- In Holide's theory only `term` is defined. -/
theorem holide_defines {name : String} (defines : TwoRoutes.holTheory.Defines name) :
    name = "term" := by
  rcases defines with defined | ⟨rule, member, head⟩
  · exact absurd (holide_undefined name) defined
  · rw [holide_rules member] at head
    simp [TwoRoutes.termArrow, TwoRoutes.termOf, headConst] at head
    exact head.symm

/-- In Holide's theory the decoding of every constant is normal. -/
theorem holide_El_con_normal (name : String) :
    IsNormal (Step TwoRoutes.holTheory) (.app (.con "term") (.con name)) := by
  have unmatched : ∀ other rule assignment, TwoRoutes.holTheory.rule rule →
      inst assignment rule.lhs ≠ .con other := by
    intro other rule assignment member
    rw [holide_rules member]
    simp [TwoRoutes.termArrow, TwoRoutes.termOf]
  intro target step
  rcases step.app_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · obtain ⟨rule, assignment, member, shape⟩ := rootStep_app_con root
    rw [holide_rules member] at shape
    simp [TwoRoutes.termArrow, TwoRoutes.termOf, TwoRoutes.arr] at shape
  · exact con_normal_of (holide_undefined _) (unmatched _) _ inner
  · exact con_normal_of (holide_undefined _) (unmatched _) _ inner

/-- Holide's theory has the arrow rule of every encoding that decodes with
`term` and codes functions with `arr`. -/
theorem holide_arrowRule (e : Encoding Base Const) (el : e.el = "term")
    (arrow : e.name .arrow = "arr") : TwoRoutes.holTheory.rule e.arrowRule := by
  have same : e.arrowRule = TwoRoutes.termArrow := by
    simp [Encoding.arrowRule, Encoding.El, Encoding.arr, Encoding.sym, el, arrow,
      TwoRoutes.termArrow, TwoRoutes.termOf, TwoRoutes.arr]
  rw [same]
  exact List.mem_singleton.mpr rfl

/-- **Holide's theory hosts every encoding** that decodes with `term`, codes
functions with `arr`, and names no symbol `term`.  The decoding of a named code
is normal. -/
def holideHub (e : Encoding Base Const) (el : e.el = "term") (arrow : e.name .arrow = "arr")
    (fresh : ∀ s, e.name s ≠ "term") : HubTheory e where
  theory := TwoRoutes.holTheory
  headed := TranslationTransport.holTheory_orthogonal.leftAlgebraic.headed
  confluent := TranslationTransport.holTheory_confluent
  rigid := fun s defines => fresh s (holide_defines defines)
  elAt s := e.El (e.sym s)
  elAt_reduces _ := .refl
  elAt_normal s := by
    simpa [Encoding.El, Encoding.sym, el] using holide_El_con_normal (e.name s)
  elAt_closed _ := .app .con .con
  elAt_injective s s' same := e.injective (by simpa [Encoding.El, Encoding.sym] using same)
  elAt_not_pi _ _ _ := by simp [Encoding.El]
  arrow_reduces σ τ := .single (e.step_El_code_arr (holide_arrowRule e el arrow) σ τ)

theorem sttfa_rules {rule : RewriteRule} (member : TranslationTransport.STTfa.theory.rule rule) :
    rule = TranslationTransport.STTfa.etaDef ∨ rule = TranslationTransport.STTfa.etapArrow ∨
      rule = TranslationTransport.STTfa.etapForall ∨ rule = TranslationTransport.STTfa.epsForall ∨
      rule = TranslationTransport.STTfa.epsImpl ∨ rule = TranslationTransport.STTfa.epsForallP := by
  simpa [TranslationTransport.STTfa.theory, Theory.ofSig, TranslationTransport.STTfa.rules]
    using member

theorem sttfa_undefined (name : String) : TranslationTransport.STTfa.theory.body name = none := by
  simp [TranslationTransport.STTfa.theory, Theory.ofSig, lookupBody]

/-- In the STTfa hub only `eta`, `etap` and `eps` are defined. -/
theorem sttfa_defines {name : String} (defines : TranslationTransport.STTfa.theory.Defines name) :
    name = "eta" ∨ name = "etap" ∨ name = "eps" := by
  rcases defines with defined | ⟨rule, member, head⟩
  · exact absurd (sttfa_undefined name) defined
  · rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [TranslationTransport.STTfa.etaDef, TranslationTransport.STTfa.etapArrow,
        TranslationTransport.STTfa.etapForall, TranslationTransport.STTfa.epsImpl,
        TranslationTransport.STTfa.epsForall, TranslationTransport.STTfa.epsForallP,
        TranslationTransport.STTfa.eta, TranslationTransport.STTfa.etap,
        TranslationTransport.STTfa.eps, headConst] at head <;>
      simp [head]

/-- In the STTfa hub every constant other than `eta` is normal. -/
theorem sttfa_con_normal {name : String} (notEta : name ≠ "eta") :
    IsNormal (Step TranslationTransport.STTfa.theory) (.con name) :=
  con_normal_of (sttfa_undefined _) fun rule assignment member => by
    rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [TranslationTransport.STTfa.etaDef, TranslationTransport.STTfa.etapArrow,
        TranslationTransport.STTfa.etapForall, TranslationTransport.STTfa.epsImpl,
        TranslationTransport.STTfa.epsForall, TranslationTransport.STTfa.epsForallP,
        TranslationTransport.STTfa.eta, TranslationTransport.STTfa.etap,
        TranslationTransport.STTfa.eps, Ne.symm notEta]

/-- **In the STTfa hub `etap (p c)` is normal** for every constant `c` other
than `eta`. -/
theorem sttfa_etap_normal {name : String} (notEta : name ≠ "eta") :
    IsNormal (Step TranslationTransport.STTfa.theory)
      (.app (.con "etap") (.app (.con "p") (.con name))) := by
  intro target step
  rcases step.app_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · obtain ⟨rule, assignment, member, shape⟩ := rootStep_app_con root
    rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [TranslationTransport.STTfa.etaDef, TranslationTransport.STTfa.etapArrow,
        TranslationTransport.STTfa.etapForall, TranslationTransport.STTfa.epsImpl,
        TranslationTransport.STTfa.epsForall, TranslationTransport.STTfa.epsForallP,
        TranslationTransport.STTfa.eta, TranslationTransport.STTfa.etap,
        TranslationTransport.STTfa.eps, TranslationTransport.STTfa.binary] at shape
  · exact sttfa_con_normal (by decide) _ inner
  · rcases inner.app_inv with root | ⟨_, inner', _⟩ | ⟨_, inner', _⟩
    · obtain ⟨rule, assignment, member, shape⟩ := rootStep_app_con root
      rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [TranslationTransport.STTfa.etaDef, TranslationTransport.STTfa.etapArrow,
          TranslationTransport.STTfa.etapForall, TranslationTransport.STTfa.epsImpl,
          TranslationTransport.STTfa.epsForall, TranslationTransport.STTfa.epsForallP,
          TranslationTransport.STTfa.eta, TranslationTransport.STTfa.etap,
          TranslationTransport.STTfa.eps, TranslationTransport.STTfa.binary] at shape
    · exact sttfa_con_normal (by decide) _ inner'
    · exact sttfa_con_normal notEta _ inner'

/-- **`eta a` unfolds to `etap (p a)`**: the definition of `eta`, then β. -/
theorem sttfa_eta_unfold (argument : LF.Term) :
    Reduces TranslationTransport.STTfa.theory (.app (.con "eta") argument)
      (.app (.con "etap") (.app (.con "p") argument)) := by
  have member : TranslationTransport.STTfa.theory.rule TranslationTransport.STTfa.etaDef := by
    simp [TranslationTransport.STTfa.theory, Theory.ofSig, TranslationTransport.STTfa.rules]
  have unfold : Step TranslationTransport.STTfa.theory (.app (.con "eta") argument)
      (.app (.lam (.con "type") (.app (.con "etap") (.app (.con "p") (.var 0)))) argument) := by
    have root := Step.root (RootStep.rule (theory := TranslationTransport.STTfa.theory)
      (fun _ => .con "type") member)
    simpa [TranslationTransport.STTfa.etaDef, TranslationTransport.STTfa.etap, inst,
      Dedukti.instantiate, LFContextualBetaEta.Context.plug] using
      root.plug (.appFunction .hole argument)
  have beta : Step TranslationTransport.STTfa.theory
      (.app (.lam (.con "type") (.app (.con "etap") (.app (.con "p") (.var 0)))) argument)
      (.app (.con "etap") (.app (.con "p") argument)) := by
    simpa [subst0, LFTyping.subst] using
      Step.root (theory := TranslationTransport.STTfa.theory)
        (.beta (.con "type") (.app (.con "etap") (.app (.con "p") (.var 0))) argument)
  exact (Relation.ReflTransGen.single unfold).tail beta

/-- **`eta (arrow a b)` reduces to `eta a → eta b`**: the definition of `eta`,
β, and the rule of `etap` at a function code. -/
theorem sttfa_eta_arrow (a b : LF.Term) :
    Reduces TranslationTransport.STTfa.theory
      (.app (.con "eta") (.app (.app (.con "arrow") a) b))
      (.pi (.app (.con "eta") a) (.app (.con "eta") (lift 1 0 b))) := by
  have member : TranslationTransport.STTfa.theory.rule TranslationTransport.STTfa.etapArrow := by
    simp [TranslationTransport.STTfa.theory, Theory.ofSig, TranslationTransport.STTfa.rules]
  have root := Step.root (RootStep.rule (theory := TranslationTransport.STTfa.theory)
    (fun index => if index = 0 then b else a) member)
  have arrowStep : Step TranslationTransport.STTfa.theory
      (.app (.con "etap") (.app (.con "p") (.app (.app (.con "arrow") a) b)))
      (.pi (.app (.con "eta") a) (.app (.con "eta") (lift 1 0 b))) := by
    simpa [TranslationTransport.STTfa.etapArrow, TranslationTransport.STTfa.etap,
      TranslationTransport.STTfa.eta, TranslationTransport.STTfa.binary, inst,
      Dedukti.instantiate, Mettapedia.GSLT.Dedukti.lift_zero] using root
  exact (sttfa_eta_unfold _).tail arrowStep

/-- **The STTfa hub hosts every encoding** that decodes with `eta`, codes
functions with `arrow`, and names no symbol `eta`, `etap` or `eps`.  The
decoding `eta c` of a named code is not normal: it unfolds to the normal
`etap (p c)`. -/
def sttfaHub (e : Encoding Base Const) (el : e.el = "eta") (arrow : e.name .arrow = "arrow")
    (fresh : ∀ s, e.name s ≠ "eta" ∧ e.name s ≠ "etap" ∧ e.name s ≠ "eps") : HubTheory e where
  theory := TranslationTransport.STTfa.theory
  headed := TranslationTransport.STTfa.orthogonal.leftAlgebraic.headed
  confluent := TranslationTransport.STTfa.confluent
  rigid := fun s defines => by
    obtain ⟨notEta, notEtap, notEps⟩ := fresh s
    rcases sttfa_defines defines with same | same | same
    · exact notEta same
    · exact notEtap same
    · exact notEps same
  elAt s := .app (.con "etap") (.app (.con "p") (e.sym s))
  elAt_reduces s := by
    simpa [Encoding.El, Encoding.sym, el] using sttfa_eta_unfold (e.sym s)
  elAt_normal s := sttfa_etap_normal (fresh s).1
  elAt_closed _ := .app .con (.app .con .con)
  elAt_injective s s' same := e.injective (by simpa [Encoding.sym] using same)
  elAt_not_pi _ _ _ := by simp
  arrow_reduces σ τ := by
    have reduces := sttfa_eta_arrow (e.code σ) (e.code τ)
    rw [(e.code_closed τ).lift] at reduces
    simpa [Encoding.El, Encoding.code, Encoding.arr, Encoding.sym, el, arrow] using reduces

end Hubs

/-! ## Controls -/

/-- The signature of the controls: one sort `ι`, a point and a predicate on
it. -/
inductive ControlConst : Ty Unit → Type
  | point : ControlConst (.base ())
  | pred : ControlConst (.arr (.base ()) .prop)

/-- The sort of the controls. -/
abbrev ι : Ty Unit := .base ()

/-- The names of the controls, with the arrow named as a hub requires. -/
def controlName (arrow : String) : Symbol Unit ControlConst → String
  | .sort _ => "iota"
  | .const .point => "point"
  | .const .pred => "pred"
  | .bool => "bool"
  | .arrow => arrow
  | .top => "top"
  | .bot => "bot"
  | .and => "and"
  | .or => "or"
  | .imp => "impl"
  | .not => "not"
  | .eq => "eq"
  | .all => "forall"
  | .ex => "exists"

/-- The names the controls reserve for the symbols other than the arrow. -/
def controlReserved : List String :=
  ["iota", "point", "pred", "bool", "top", "bot", "and", "or", "impl", "not", "eq", "forall",
    "exists"]

theorem controlName_injective {arrow : String} (fresh : arrow ∉ controlReserved) :
    Function.Injective (controlName arrow) := by
  simp only [controlReserved, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
  intro a b same
  cases a <;> (try (rename_i c; cases c)) <;> cases b <;> (try (rename_i c; cases c)) <;>
    simp_all [controlName]

/-- The encoding of the controls, decoding with `el` and coding functions with
`arrow`. -/
def controlEncoding (el arrow : String) (fresh : arrow ∉ controlReserved) :
    Encoding Unit ControlConst :=
  ⟨el, controlName arrow, controlName_injective fresh⟩

/-- The controls in Holide's names. -/
def holideControl : Encoding Unit ControlConst := controlEncoding "term" "arr" (by decide)

/-- The controls in the STTfa hub's names. -/
def sttfaControl : Encoding Unit ControlConst := controlEncoding "eta" "arrow" (by decide)

/-- Holide's theory hosts the controls. -/
def holideControlHub : HubTheory holideControl :=
  holideHub holideControl rfl rfl fun s => by
    cases s <;> (try (rename_i c; cases c)) <;>
      simp [holideControl, controlEncoding, controlName]

/-- The STTfa hub hosts the controls. -/
def sttfaControlHub : HubTheory sttfaControl :=
  sttfaHub sttfaControl rfl rfl fun s => by
    cases s <;> (try (rename_i c; cases c)) <;>
      simp [sttfaControl, controlEncoding, controlName]

/-- `(λ x. x) y`, in the context `y : ι`. -/
def identityRedex : Term ControlConst [ι] ι := .app (.lam (.var .vz)) (.var .vz)

theorem identityRedex_reduces : HOL.BetaNormalization.ReducesStar identityRedex (.var .vz) :=
  .single ⟨.beta (.var .vz) (.var .vz)⟩

theorem identityRedex_betaConv : BetaConv identityRedex (.var .vz) :=
  .rel _ _ ⟨.beta (.var .vz) (.var .vz)⟩

theorem var_normal_source {Γ : Ctx Unit} {τ : Ty Unit} (v : Var Γ τ) :
    HOL.BetaNormalization.Normal (.var v : Term ControlConst Γ τ) :=
  fun target => HOL.BetaNormalization.var_irreducible v target

/-- The β-step of `(λ x. x) y` is a step of Holide's theory. -/
theorem holide_identityRedex_step :
    Step TwoRoutes.holTheory (holideControl.translate identityRedex)
      (holideControl.translate (.var .vz : Term ControlConst [ι] ι)) :=
  Encoding.translate_betaStep (BetaStep.beta (.var .vz) (.var .vz))

/-- Holide's checker decides conversion by normal forms on the translated terms
of the sort `ι` in the context `y : ι`. -/
theorem holide_decidedOn_controls :
    DecidedOn (Step TwoRoutes.holTheory)
      (Set.range (holideControl.translate (Γ := [ι]) (τ := ι))) :=
  holideControlHub.decidedOn_translations [ι] ι

/-- **The checker's answer certifies conversion**: the STTfa hub computes one
normal form for the translations of `(λ x. x) y` and of `y`, and this alone
gives their β-conversion, through the general transport. -/
theorem sttfa_identityRedex_betaConv_by_checker :
    BetaConv identityRedex (.var .vz : Term ControlConst [ι] ι) :=
  (sttfaControlHub.betaConv_iff_normalForm_eq_by_transport identityRedex (.var .vz)
    (sttfaControlHub.translate_normalForm identityRedex_reduces (var_normal_source _))
    (sttfaControlHub.translate_normalForm .refl (var_normal_source _))).mpr rfl

/-- **The checker's answer reflects**: Holide's checker computes different
normal forms for the translations of two distinct variables, so the variables
are not β-convertible. -/
theorem holide_distinct_variables_not_betaConv :
    ¬ BetaConv (.var .vz : Term ControlConst [ι, ι] ι) (.var (.vs .vz)) := fun converted => by
  have same := (holideControlHub.betaConv_iff_normalForm_eq _ _
    (holideControlHub.translate_normalForm .refl (var_normal_source _))
    (holideControlHub.translate_normalForm .refl (var_normal_source _))).mp converted
  simp [Encoding.translateNF, varIndex] at same

/-- `(λ x. pred x) point ∧ ⊤`. -/
def predicateRedex : Term ControlConst [] .prop :=
  .and (.app (.lam (.app (.const .pred) (.var .vz))) (.const .point)) .top

/-- `pred point ∧ ⊤`. -/
def predicateContractum : Term ControlConst [] .prop :=
  .and (.app (.const .pred) (.const .point)) .top

/-- **Through a constant and a connective**: the STTfa hub converts the
translations of `(λ x. pred x) point ∧ ⊤` and `pred point ∧ ⊤`. -/
theorem sttfa_predicateRedex_conv :
    Conv TranslationTransport.STTfa.theory (sttfaControl.translate predicateRedex)
      (sttfaControl.translate predicateContractum) :=
  (sttfaControlHub.translate_conv_iff predicateRedex predicateContractum).mpr
    (.rel _ _ ⟨.andLeft .top
      (.beta (.app (.const ControlConst.pred) (.var .vz)) (.const ControlConst.point))⟩)

/-- **η is not a conversion of either hub**, at `ι ⇒ ι`. -/
theorem hubs_eta_not_conv :
    ¬ Conv TwoRoutes.holTheory (holideControl.translate (etaExpanded ι ι))
        (holideControl.translate (etaContracted ι ι)) ∧
      ¬ Conv TranslationTransport.STTfa.theory (sttfaControl.translate (etaExpanded ι ι))
        (sttfaControl.translate (etaContracted ι ι)) :=
  ⟨holideControlHub.eta_not_conv ι ι, sttfaControlHub.eta_not_conv ι ι⟩

#print axioms Encoding.translate_instantiate
#print axioms Encoding.translate_betaStep
#print axioms HubTheory.reduces_El_code
#print axioms HubTheory.translateNF_normal
#print axioms Encoding.translateNF_injective
#print axioms HubTheory.decidedOn_translations
#print axioms HubTheory.translate_conv_iff
#print axioms HubTheory.betaConv_iff_normalForm_eq
#print axioms HubTheory.betaConv_iff_normalForm_eq_by_transport
#print axioms holideHub
#print axioms sttfaHub
#print axioms sttfa_identityRedex_betaConv_by_checker
#print axioms holide_distinct_variables_not_betaConv
#print axioms sttfa_predicateRedex_conv
#print axioms hubs_eta_not_conv

end Mettapedia.GSLT.Dedukti.HOLHub
