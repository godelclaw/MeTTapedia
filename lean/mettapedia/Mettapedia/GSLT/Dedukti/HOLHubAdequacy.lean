import Mettapedia.GSLT.Dedukti.HOLHubProofs

/-!
# Adequacy of the STTfa hub for closed implicational formulas

`HOLHubProofs` compiles every proof of `Logic.HOL.ProofSyntaxModulo` into a
term of `eps (tr φ)` in the STTfa hub.  This module proves the converse on the
closed implicational fragment: **every normal inhabitant of `eps (tr φ)` comes
from a HOL proof**, and shows where exactness fails once universal
quantification enters.

**The fragment** (`ImpForm`).  An atom is a β-normal formula that is neither an
implication nor a universal (`Atom`); the fragment closes the closed atoms
under `⇒`.  An atom may contain quantifiers, connectives and abstractions; it is
not decomposed.

**Normal types of proofs** (`Encoding.epsNF`).  For a formula of the fragment
the type `eps (tr φ)` of its proofs reduces (`reduces_eps`) to a normal form
(`epsNF_normal`): a product for an implication, `eps` of the translation with
computed domains for an atom.  Distinct formulas have distinct normal forms
(`epsNF_injective`).

**Object types** (`ObjTree`).  The declared types of the hub with proofs
(`objTree_constType`), the sorts, and their reducts and substitution instances
form a class closed under the steps of the hub (`ObjTree.step`,
`ObjTree.subst`) that contains no normal type of a proof
(`objTree_not_conv_epsNF`).

**Adequacy** (`adequacy_induction`, `sttfa_adequate`).  By induction on a
normal term, with typing inversion: a variable is a hypothesis; an abstraction
is an ⇒-introduction, since only an implication has a product as the normal
type of its proofs, and its normal domain is that of the premise; an
application of a proof to a proof is an ⇒-elimination; every other term has an
object type.  A normal inhabitant of `eps (tr φ)` in the context of the types
of the proofs of hypotheses gives a proof of `φ` from them (`sttfa_adequate`),
and a closed one a theorem (`sttfa_adequate_closed`).

**Controls.**  The normal compiled identity gives back `pred point ⇒ pred point`
(`predIdentity_adequate`), and `h₀ h₁` gives back `pred point` from
`pred point ⇒ pred point` and `pred point` (`modusPonens_adequate`).  The hub
has no normal closed proof of `pred point`, which fails in a model
(`predPoint_no_normal_inhabitant`).

**The boundary at universal quantification.**  Every translation applies
`and` to two operands, and the steps of the hub keep every occurrence of a
constant of no rule so (`Applied.step`); the bare `and` is normal, so it
converts with no translation (`bareAnd_not_conv_translate`), as in Cousineau
and Dowek's witness for pure type systems.  As a ∀-witness it gives a normal
inhabitant of the type of the proofs of `pred point`, in the context of the
proofs of `∀ f. pred point`, that no proof compiles to, although the formula is
provable with another witness (`sttfa_not_exactly_adequate`).  Adequacy with
universal quantification, modulo the coding of witnesses, is
`HOLHubAdequacyForall`.

**Scope.**  The theorems are about normal terms of the typed STTfa hub of
`HOLHubProofs`; normalization of its typed terms is not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.HOLHub

open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 lookupBody)
open Mettapedia.Logic.Relation (Confluent IsNormal)
open Mettapedia.Logic.HOL (Ty Ctx Var Term Formula)
open TranslationTransport

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## The fragment -/

/-- A closed atom: a β-normal closed formula that is neither an implication nor
a universal. -/
structure Atom (a : Formula Const []) : Prop where
  normal : HOL.BetaNormalization.Normal a
  notImp : ∀ p q : Formula Const [], a ≠ .imp p q
  notAll : ∀ {σ : Ty Base} (b : Formula Const [σ]), a ≠ .all b

/-- The closed implicational fragment: atoms closed under implication. -/
inductive ImpForm : Formula Const [] → Prop where
  | atom {a : Formula Const []} : Atom a → ImpForm a
  | imp {p q : Formula Const []} : ImpForm p → ImpForm q → ImpForm (.imp p q)

/-- The names the STTfa hub with proofs needs of an encoding. -/
structure SttfaNames (e : Encoding Base Const) : Prop where
  el : e.el = "eta"
  arrow : e.name .arrow = "arrow"
  imp : e.name .imp = "impl"
  all : e.name .all = "forall"
  fresh : ∀ s, e.name s ≠ "eta" ∧ e.name s ≠ "etap" ∧ e.name s ≠ "eps"
  typeFresh : ∀ s, e.name s ≠ "type"
  forallPFresh : ∀ s, e.name s ≠ "forallP"
  pFresh : ∀ s, e.name s ≠ "p" ∧ e.name s ≠ "ptype"
  forallKFresh : ∀ s, e.name s ≠ "forallK"

namespace SttfaNames

variable {e : Encoding Base Const} (names : SttfaNames e)

/-- The STTfa hub of the encoding. -/
def hub : HubTheory e := sttfaHub e names.el names.arrow names.fresh

/-- The normal decoding of a named code, `etap (p c)`. -/
def base : Symbol Base Const → LF.Term := names.hub.elAt

theorem base_closed (s : Symbol Base Const) : Closed (names.base s) := names.hub.elAt_closed s

theorem hub_theory : names.hub.theory = STTfa.theory := rfl

end SttfaNames

/-! ## Closed translations and the normal types of proofs -/

namespace Encoding

variable (e : Encoding Base Const)

theorem varIndex_lt : ∀ {Γ : Ctx Base} {τ : Ty Base} (v : Var Γ τ), varIndex v < Γ.length
  | _, _, .vz => Nat.succ_pos _
  | _, _, .vs v => Nat.succ_lt_succ (varIndex_lt v)

theorem translate_wellScoped : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ),
    LF.WellScoped Γ.length (e.translate t) := by
  intro Γ τ t
  induction t with
  | var v => exact .var (varIndex_lt v)
  | const c => exact .con
  | app f a ihf iha => exact .app ihf iha
  | @lam σ Γ τ body ih => exact .lam ((e.El_code_closed σ).mono (Nat.zero_le _)) ih
  | top => exact .con
  | bot => exact .con
  | and p q ihp ihq => exact .app (.app .con ihp) ihq
  | or p q ihp ihq => exact .app (.app .con ihp) ihq
  | imp p q ihp ihq => exact .app (.app .con ihp) ihq
  | not p ih => exact .app .con ih
  | @eq Γ τ l r ihl ihr =>
      exact .app (.app (.app .con ((e.code_closed τ).mono (Nat.zero_le _))) ihl) ihr
  | @all σ Γ body ih =>
      exact .app (.app .con ((e.code_closed σ).mono (Nat.zero_le _)))
        (.lam ((e.El_code_closed σ).mono (Nat.zero_le _)) ih)
  | @ex σ Γ body ih =>
      exact .app (.app .con ((e.code_closed σ).mono (Nat.zero_le _)))
        (.lam ((e.El_code_closed σ).mono (Nat.zero_le _)) ih)

theorem translateNF_wellScoped {base : Symbol Base Const → LF.Term}
    (closed : ∀ s, Closed (base s)) : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ),
    LF.WellScoped Γ.length (e.translateNF base t) := by
  intro Γ τ t
  induction t with
  | var v => exact .var (varIndex_lt v)
  | const c => exact .con
  | app f a ihf iha => exact .app ihf iha
  | @lam σ Γ τ body ih => exact .lam ((elNF_closed closed σ).mono (Nat.zero_le _)) ih
  | top => exact .con
  | bot => exact .con
  | and p q ihp ihq => exact .app (.app .con ihp) ihq
  | or p q ihp ihq => exact .app (.app .con ihp) ihq
  | imp p q ihp ihq => exact .app (.app .con ihp) ihq
  | not p ih => exact .app .con ih
  | @eq Γ τ l r ihl ihr =>
      exact .app (.app (.app .con ((e.code_closed τ).mono (Nat.zero_le _))) ihl) ihr
  | @all σ Γ body ih =>
      exact .app (.app .con ((e.code_closed σ).mono (Nat.zero_le _)))
        (.lam ((elNF_closed closed σ).mono (Nat.zero_le _)) ih)
  | @ex σ Γ body ih =>
      exact .app (.app .con ((e.code_closed σ).mono (Nat.zero_le _)))
        (.lam ((elNF_closed closed σ).mono (Nat.zero_le _)) ih)

theorem wellScoped_lift {t : LF.Term} {n : Nat} (wellScoped : LF.WellScoped n t) :
    ∀ cutoff : Nat, LF.WellScoped (n + 1) (lift 1 cutoff t) := by
  induction wellScoped with
  | srt => intro _; exact .srt
  | con => intro _; exact .con
  | var bound => intro cutoff; exact .var (by split <;> omega)
  | pi _ _ ihDomain ihBody => intro cutoff; exact .pi (ihDomain cutoff) (ihBody (cutoff + 1))
  | lam _ _ ihDomain ihBody => intro cutoff; exact .lam (ihDomain cutoff) (ihBody (cutoff + 1))
  | app _ _ ihFunction ihArgument => intro cutoff; exact .app (ihFunction cutoff) (ihArgument cutoff)

/-- **The normal type of the proofs of a formula**: a product over the
premise for an implication, a product over the computed decoding for a
universal, and `eps` of the translation with computed domains otherwise. -/
def epsNF (base : Symbol Base Const → LF.Term) :
    {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → LF.Term
  | _, _, .imp p q => .pi (epsNF base p) (lift 1 0 (epsNF base q))
  | _, _, .all (σ := σ) b => .pi (elNF base σ) (epsNF base b)
  | _, _, t => .app (.con "eps") (e.translateNF base t)

theorem epsNF_wellScoped {base : Symbol Base Const → LF.Term} (closed : ∀ s, Closed (base s)) :
    ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ),
      LF.WellScoped Γ.length (e.epsNF base t) := by
  intro Γ τ t
  induction t with
  | imp p q ihp ihq => exact .pi ihp (wellScoped_lift ihq 0)
  | @all σ Γ b ih => exact .pi ((elNF_closed closed σ).mono (Nat.zero_le _)) ih
  | _ => exact .app .con (e.translateNF_wellScoped closed _)

theorem epsNF_closed {base : Symbol Base Const → LF.Term} (closed : ∀ s, Closed (base s))
    (φ : Formula Const []) : Closed (e.epsNF base φ) :=
  e.epsNF_wellScoped closed φ

/-- For closed formulas the product of an implication needs no lifting. -/
theorem epsNF_imp {base : Symbol Base Const → LF.Term} (closed : ∀ s, Closed (base s))
    (p q : Formula Const []) :
    e.epsNF base (.imp p q) = .pi (e.epsNF base p) (e.epsNF base q) := by
  show LF.Term.pi _ (lift 1 0 _) = _
  rw [(e.epsNF_closed closed q).lift]

theorem epsNF_atom (base : Symbol Base Const → LF.Term) {a : Formula Const []} (atom : Atom a) :
    e.epsNF base a = .app (.con "eps") (e.translateNF base a) := by
  cases a with
  | imp p q => exact absurd rfl (atom.notImp p q)
  | all b => exact absurd rfl (atom.notAll b)
  | _ => rfl

end Encoding

theorem SttfaNames.epsNF_imp {e : Encoding Base Const} (names : SttfaNames e) (p q : Formula Const []) :
    e.epsNF names.base (.imp p q) = .pi (e.epsNF names.base p) (e.epsNF names.base q) :=
  e.epsNF_imp names.base_closed p q

/-! ## The normal types of proofs are normal and distinct -/

section Normal

variable {e : Encoding Base Const} (names : SttfaNames e)
include names

/-- An atom's translation is no application of `forall` or `impl` to two
arguments. -/
theorem atom_translate_not_binary {a : Formula Const []} (atom : Atom a) {s : Symbol Base Const}
    (binary : s = .imp ∨ s = .all) {y z : LF.Term} :
    e.translateNF names.base a ≠ .app (.app (.con (e.name s)) y) z := by
  intro same
  rcases binary with rfl | rfl <;> cases a with
  | var v => exact nomatch v
  | app f x =>
      simp only [Encoding.translateNF, LF.Term.app.injEq] at same
      obtain ⟨_, c, bad⟩ := e.translateNF_arrow_app_con names.base f _ y same.1
      cases bad
  | imp p q => exact atom.notImp p q rfl
  | all b => exact atom.notAll b rfl
  | _ => simp [Encoding.translateNF, Encoding.sym, Encoding.binary, Encoding.equation,
      Encoding.binder, e.name_eq_iff] at same

/-- An atom's translation is no application of `forallP`. -/
theorem atom_translate_not_forallP {a : Formula Const []} (atom : Atom a) {y : LF.Term} :
    e.translateNF names.base a ≠ .app (.con "forallP") y := by
  intro same
  cases a with
  | var v => exact nomatch v
  | app f x =>
      simp only [Encoding.translateNF, LF.Term.app.injEq] at same
      cases f with
      | const c =>
          simp only [Encoding.translateNF, Encoding.sym, LF.Term.con.injEq] at same
          exact names.forallPFresh _ same.1
      | _ => simp [Encoding.translateNF] at same
  | not p =>
      simp only [Encoding.translateNF, Encoding.sym, LF.Term.app.injEq, LF.Term.con.injEq] at same
      exact names.forallPFresh _ same.1
  | imp p q => exact atom.notImp p q rfl
  | all b => exact atom.notAll b rfl
  | _ => simp [Encoding.translateNF, Encoding.sym, Encoding.binary, Encoding.equation,
      Encoding.binder] at same

/-- **The normal type of the proofs of a formula of the fragment is normal.** -/
theorem epsNF_normal {φ : Formula Const []} (form : ImpForm φ) :
    IsNormal (Step STTfa.theory) (e.epsNF names.base φ) := by
  induction form with
  | @atom a atom =>
      rw [e.epsNF_atom names.base atom]
      have argumentNormal : IsNormal (Step STTfa.theory) (e.translateNF names.base a) :=
        names.hub.translateNF_normal a atom.normal
      intro target step
      rcases step.app_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
      · obtain ⟨rule, assignment, member, shape⟩ := rootStep_app_con root
        rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl
        · simp [STTfa.etaDef] at shape
        · simp [STTfa.etapArrow, STTfa.etap] at shape
        · simp [STTfa.etapForall, STTfa.etap] at shape
        · simp only [STTfa.epsForall, STTfa.eps, STTfa.binary, inst_app, inst_con, inst_var,
            LF.Term.app.injEq, true_and] at shape
          exact atom_translate_not_binary names atom (s := .all) (Or.inr rfl)
            (by rw [names.all]; exact shape.symm)
        · simp only [STTfa.epsImpl, STTfa.eps, STTfa.binary, inst_app, inst_con, inst_var,
            LF.Term.app.injEq, true_and] at shape
          exact atom_translate_not_binary names atom (s := .imp) (Or.inl rfl)
            (by rw [names.imp]; exact shape.symm)
        · simp only [STTfa.epsForallP, STTfa.eps, inst_app, inst_con, inst_var,
            LF.Term.app.injEq, true_and] at shape
          exact atom_translate_not_forallP names atom shape.symm
      · exact sttfa_con_normal (by decide) _ inner
      · exact argumentNormal _ inner
  | @imp p q _ _ ihp ihq =>
      rw [names.epsNF_imp]
      intro target step
      rcases step.pi_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
      · exact RootStep.not_pi STTfa.orthogonal.leftAlgebraic.headed root
      · exact ihp _ inner
      · exact ihq _ inner

/-- **Normal types of proofs of distinct formulas differ.** -/
theorem epsNF_injective {φ ψ : Formula Const []} (formφ : ImpForm φ) (formψ : ImpForm ψ)
    (same : e.epsNF names.base φ = e.epsNF names.base ψ) : φ = ψ := by
  induction formφ generalizing ψ with
  | @atom a atomA =>
      cases formψ with
      | @atom b atomB =>
          rw [e.epsNF_atom names.base atomA, e.epsNF_atom names.base atomB] at same
          simp only [LF.Term.app.injEq, true_and] at same
          exact eq_of_heq (e.translateNF_injective names.base names.hub.elAt_injective
            names.hub.elAt_not_pi _ _ same).2
      | @imp p q _ _ =>
          rw [e.epsNF_atom names.base atomA, names.epsNF_imp] at same
          cases same
  | @imp p q _ _ ihp ihq =>
      cases formψ with
      | @atom b atomB =>
          rw [e.epsNF_atom names.base atomB, names.epsNF_imp] at same
          cases same
      | @imp p' q' formp' formq' =>
          rw [names.epsNF_imp, names.epsNF_imp] at same
          simp only [LF.Term.pi.injEq] at same
          rw [ihp formp' same.1, ihq formq' same.2]

/-- **The type of the proofs of a formula of the fragment reduces to its normal
form.** -/
theorem reduces_eps {φ : Formula Const []} (form : ImpForm φ) :
    Reduces STTfa.theory (.app (.con "eps") (e.translate φ)) (e.epsNF names.base φ) := by
  induction form with
  | @atom a atom =>
      rw [e.epsNF_atom names.base atom]
      exact Reduces.app .refl (names.hub.reduces_translateNF a)
  | @imp p q _ _ ihp ihq =>
      have member : STTfa.theory.rule STTfa.epsImpl := by
        simp [STTfa.theory, Theory.ofSig, STTfa.rules]
      have root := Step.root (RootStep.rule (theory := STTfa.theory)
        (fun index => if index = 0 then e.translate q else e.translate p) member)
      have closedQ : Closed (e.translate q) := e.translate_wellScoped q
      have step : Step STTfa.theory (.app (.con "eps") (e.translate (.imp p q)))
          (.pi (.app (.con "eps") (e.translate p)) (.app (.con "eps") (e.translate q))) := by
        simpa [STTfa.epsImpl, STTfa.eps, STTfa.binary, Encoding.translate, Encoding.binary,
          Encoding.sym, names.imp, inst, Dedukti.instantiate, Mettapedia.GSLT.Dedukti.lift_zero,
          closedQ.lift] using root
      rw [names.epsNF_imp]
      exact (Relation.ReflTransGen.single step).trans (Reduces.pi ihp ihq)

end Normal

/-! ## Root steps and normal subterms -/

/-- A root step is a β-step, the unfolding of a definition, or an instance of
a rule. -/
theorem rootStep_cases {theory : Theory} {source target : LF.Term}
    (root : RootStep theory source target) :
    (∃ domain body argument, source = .app (.lam domain body) argument ∧
        target = subst0 argument body) ∨
      (∃ name, source = .con name ∧ theory.body name = some target) ∨
      ∃ rule assignment, theory.rule rule ∧ source = inst assignment rule.lhs ∧
        target = inst assignment rule.rhs := by
  cases root with
  | beta domain body argument => exact Or.inl ⟨domain, body, argument, rfl, rfl⟩
  | delta defined => exact Or.inr (Or.inl ⟨_, rfl, defined⟩)
  | rule assignment member => exact Or.inr (Or.inr ⟨_, assignment, member, rfl, rfl⟩)

/-- A root step of a constant applied to an argument is an instance of a
rule. -/
theorem rootStep_app_con_rule {theory : Theory} {name : String} {argument target : LF.Term}
    (root : RootStep theory (.app (.con name) argument) target) :
    ∃ rule assignment, theory.rule rule ∧ inst assignment rule.lhs = .app (.con name) argument ∧
      target = inst assignment rule.rhs := by
  rcases rootStep_cases root with ⟨_, _, _, same, _⟩ | ⟨_, same, _⟩ |
    ⟨rule, assignment, member, same, rfl⟩
  · cases same
  · cases same
  · exact ⟨rule, assignment, member, same.symm, rfl⟩

theorem sttfa_closedBodies : STTfa.theory.ClosedBodies := by
  intro name term defined
  rw [sttfa_undefined] at defined
  cases defined

theorem normal_app_function {theory : Theory} {function argument : LF.Term}
    (normal : IsNormal (Step theory) (.app function argument)) : IsNormal (Step theory) function :=
  fun _ step => normal _ (step.plug (.appFunction .hole argument))

theorem normal_app_argument {theory : Theory} {function argument : LF.Term}
    (normal : IsNormal (Step theory) (.app function argument)) : IsNormal (Step theory) argument :=
  fun _ step => normal _ (step.plug (.appArgument function .hole))

theorem normal_lam_domain {theory : Theory} {domain body : LF.Term}
    (normal : IsNormal (Step theory) (.lam domain body)) : IsNormal (Step theory) domain :=
  fun _ step => normal _ (step.plug (.lamDomain .hole body))

theorem normal_lam_body {theory : Theory} {domain body : LF.Term}
    (normal : IsNormal (Step theory) (.lam domain body)) : IsNormal (Step theory) body :=
  fun _ step => normal _ (step.plug (.lamBody domain .hole))

/-- Under confluence, convertible normal terms are equal. -/
theorem sttfa_normal_conv_eq {a b : LF.Term} (normalA : IsNormal (Step STTfa.theory) a)
    (normalB : IsNormal (Step STTfa.theory) b) (converted : Conv STTfa.theory a b) : a = b := by
  obtain ⟨common, toA, toB⟩ := (conv_iff_joinable STTfa.confluent).mp converted
  exact (normalA.reflTransGen_eq toA).symm.trans (normalB.reflTransGen_eq toB)

/-- Under confluence, a term convertible to a normal term reduces to it. -/
theorem sttfa_reduces_of_conv {a b : LF.Term} (converted : Conv STTfa.theory a b)
    (normalB : IsNormal (Step STTfa.theory) b) : Reduces STTfa.theory a b := by
  obtain ⟨common, toCommon, fromB⟩ := (conv_iff_joinable STTfa.confluent).mp converted
  rwa [normalB.reflTransGen_eq fromB] at toCommon

/-! ## Object types -/

/-- The types of the hub's objects, at every stage of their unfolding: the
decoding `eta c` of a code, its unfolding `(λ t. etap (p t)) c` and
`etap (p c)`, the types of codes and of polymorphic codes, the sorts, and
products of these. -/
inductive ObjTree : LF.Term → Prop where
  | eta (code : LF.Term) : ObjTree (.app (.con "eta") code)
  | unfolded (code : LF.Term) :
      ObjTree (.app (.lam (.con "type") (.app (.con "etap") (.app (.con "p") (.var 0)))) code)
  | etap (code : LF.Term) : ObjTree (.app (.con "etap") (.app (.con "p") code))
  | codes : ObjTree (.con "type")
  | ptypes : ObjTree (.con "ptype")
  | sort (sort : LF.Srt) : ObjTree (.srt sort)
  | pi {domain body : LF.Term} : ObjTree domain → ObjTree body → ObjTree (.pi domain body)

theorem ObjTree.pi_body {domain body : LF.Term} (tree : ObjTree (.pi domain body)) : ObjTree body := by
  cases tree with
  | pi _ bodyTree => exact bodyTree

/-- The unfolding `λ t. etap (p t)` of `eta` is normal. -/
theorem unfolded_normal :
    IsNormal (Step STTfa.theory)
      (.lam (.con "type") (.app (.con "etap") (.app (.con "p") (.var 0)))) := by
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  intro target step
  rcases step.lam_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · exact RootStep.not_lam headed root
  · exact sttfa_con_normal (by decide) _ inner
  · rcases inner.app_inv with root | ⟨_, inner', _⟩ | ⟨_, inner', _⟩
    · obtain ⟨rule, assignment, member, shape, -⟩ := rootStep_app_con_rule root
      rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [STTfa.etaDef, STTfa.etapArrow, STTfa.etapForall, STTfa.epsImpl, STTfa.epsForall,
          STTfa.epsForallP, STTfa.eta, STTfa.etap, STTfa.eps, STTfa.binary] at shape
    · exact sttfa_con_normal (by decide) _ inner'
    · rcases inner'.app_inv with root | ⟨_, inner'', _⟩ | ⟨_, inner'', _⟩
      · obtain ⟨rule, assignment, member, shape, -⟩ := rootStep_app_con_rule root
        rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [STTfa.etaDef, STTfa.etapArrow, STTfa.etapForall, STTfa.epsImpl, STTfa.epsForall,
            STTfa.epsForallP, STTfa.eta, STTfa.etap, STTfa.eps, STTfa.binary] at shape
      · exact sttfa_con_normal (by decide) _ inner''
      · exact var_normal headed _ _ inner''

/-- **Object types are closed under the steps of the hub.** -/
theorem ObjTree.step {t u : LF.Term} (tree : ObjTree t) (step : Step STTfa.theory t u) :
    ObjTree u := by
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  induction tree generalizing u with
  | eta code =>
      rcases step.app_inv with root | ⟨function, inner, rfl⟩ | ⟨code', inner, rfl⟩
      · obtain ⟨rule, assignment, member, shape, -⟩ := rootStep_app_con_rule root
        exfalso
        rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [STTfa.etaDef, STTfa.etapArrow, STTfa.etapForall, STTfa.epsImpl, STTfa.epsForall,
            STTfa.epsForallP, STTfa.eta, STTfa.etap, STTfa.eps, STTfa.binary] at shape
      · rcases rootStep_cases inner.con_inv with ⟨_, _, _, same, _⟩ | ⟨_, same, defined⟩ |
          ⟨rule, assignment, member, shape, rfl⟩
        · cases same
        · cases same
          rw [sttfa_undefined] at defined
          cases defined
        · rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl
          · simpa [STTfa.etaDef, STTfa.etap, inst, Dedukti.instantiate] using ObjTree.unfolded code
          all_goals simp [STTfa.etapArrow, STTfa.etapForall, STTfa.epsImpl, STTfa.epsForall,
            STTfa.epsForallP, STTfa.eta, STTfa.etap, STTfa.eps, STTfa.binary] at shape
      · exact .eta code'
  | unfolded code =>
      rcases step.app_inv with root | ⟨function, inner, rfl⟩ | ⟨code', inner, rfl⟩
      · rcases rootStep_cases root with ⟨domain, body, argument, same, rfl⟩ | ⟨_, same, _⟩ |
          ⟨rule, assignment, member, same, -⟩
        · simp only [LF.Term.app.injEq, LF.Term.lam.injEq] at same
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
          simpa [subst0, LFTyping.subst] using ObjTree.etap code
        · cases same
        · exfalso
          rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [STTfa.etaDef, STTfa.etapArrow, STTfa.etapForall, STTfa.epsImpl,
              STTfa.epsForall, STTfa.epsForallP, STTfa.eta, STTfa.etap, STTfa.eps,
              STTfa.binary] at same
      · exact absurd inner (unfolded_normal _)
      · exact .unfolded code'
  | etap code =>
      rcases step.app_inv with root | ⟨function, inner, rfl⟩ | ⟨argument', inner, rfl⟩
      · obtain ⟨rule, assignment, member, shape, rfl⟩ := rootStep_app_con_rule root
        rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl
        · simp [STTfa.etaDef] at shape
        · simp only [STTfa.etapArrow, STTfa.eta, STTfa.etap, STTfa.binary, inst,
            Dedukti.instantiate]
          exact .pi (.eta _) (.eta _)
        · simp [STTfa.etapForall, STTfa.etap] at shape
        all_goals simp [STTfa.epsImpl, STTfa.epsForall, STTfa.epsForallP, STTfa.eps,
          STTfa.binary] at shape
      · exact absurd inner (sttfa_con_normal (by decide) _)
      · rcases inner.app_inv with root | ⟨_, inner', rfl⟩ | ⟨code', inner', rfl⟩
        · obtain ⟨rule, assignment, member, shape, -⟩ := rootStep_app_con_rule root
          exfalso
          rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [STTfa.etaDef, STTfa.etapArrow, STTfa.etapForall, STTfa.epsImpl,
              STTfa.epsForall, STTfa.epsForallP, STTfa.eta, STTfa.etap, STTfa.eps,
              STTfa.binary] at shape
        · exact absurd inner' (sttfa_con_normal (by decide) _)
        · exact .etap code'
  | codes => exact absurd step (sttfa_con_normal (by decide) _)
  | ptypes => exact absurd step (sttfa_con_normal (by decide) _)
  | sort sort => exact absurd step (srt_normal headed sort _)
  | pi domainTree bodyTree ihDomain ihBody =>
      rcases step.pi_inv with root | ⟨domain', inner, rfl⟩ | ⟨body', inner, rfl⟩
      · exact absurd root (RootStep.not_pi headed)
      · exact .pi (ihDomain inner) bodyTree
      · exact .pi domainTree (ihBody inner)

theorem ObjTree.reduces {t u : LF.Term} (tree : ObjTree t) (reduces : Reduces STTfa.theory t u) :
    ObjTree u := by
  induction reduces with
  | refl => exact tree
  | tail _ step ih => exact ih.step step

/-- **Object types are closed under substitution.** -/
theorem ObjTree.subst {t : LF.Term} (tree : ObjTree t) :
    ∀ (index : Nat) (replacement : LF.Term), ObjTree (LFTyping.subst index replacement t) := by
  induction tree with
  | eta code => intro index replacement; exact .eta _
  | unfolded code =>
      intro index replacement
      have notZero : (0 : Nat) ≠ index + 1 := by omega
      simpa [LFTyping.subst, notZero] using
        ObjTree.unfolded (LFTyping.subst index replacement code)
  | etap code => intro index replacement; exact .etap _
  | codes => intro index replacement; exact .codes
  | ptypes => intro index replacement; exact .ptypes
  | sort sort => intro index replacement; exact .sort sort
  | pi _ _ ihDomain ihBody =>
      intro index replacement
      exact .pi (ihDomain index replacement) (ihBody (index + 1) (lift 1 0 replacement))

/-! ## Typing in the STTfa hub with proofs -/

theorem conv_proofTheory {e : Encoding Base Const} {a b : LF.Term}
    (converted : Conv (sttfaProofTheory e) a b) : Conv STTfa.theory a b := by
  induction converted with
  | rel _ _ step =>
      exact .rel _ _ (Step.of_sameRules (theory := sttfaProofTheory e) (theory' := STTfa.theory)
        rfl rfl step)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem step_proofTheory (e : Encoding Base Const) :
    Step (sttfaProofTheory e) = Step STTfa.theory :=
  e.step_typedTheory _ _ _

section Adequacy

variable {e : Encoding Base Const} (names : SttfaNames e)
include names

/-- Every declared type of the encoding is an object type. -/
theorem objTree_declaredType (s : Symbol Base Const) :
    ObjTree (e.declaredType (.con "type") s) := by
  cases s <;> simp only [Encoding.declaredType, Encoding.El, names.el] <;>
    first
      | exact .eta _
      | exact .codes
      | exact .pi .codes (.pi .codes .codes)
      | exact .pi .codes (.eta _)

/-- **Every declared type of the STTfa hub with proofs is an object type**:
`eps` and `etap` are families of types, not proofs. -/
theorem objTree_constType {name : String} {type : LF.Term}
    (declared : (sttfaProofTheory e).constType name = some type) : ObjTree type := by
  simp only [sttfaProofTheory, Encoding.typedTheory] at declared
  split_ifs at declared with named
  · cases declared
    exact objTree_declaredType names _
  · cases declared
    exact .sort _
  · cases declared
    exact .pi .codes (.sort _)
  · simp only [sttfaProofTypes] at declared
    split_ifs at declared <;> cases declared
    · simp only [Encoding.El, Encoding.sym, names.el]
      exact .pi (.eta _) (.sort _)
    · exact .sort _
    · exact .pi .codes .ptypes
    · exact .pi .ptypes (.sort _)
    · exact .pi (.pi .codes .ptypes) .ptypes
    · simp only [Encoding.El, Encoding.sym, names.el]
      exact .pi (.pi .codes (.eta _)) (.eta _)

/-- The normal type of the proofs of a formula of the fragment is no object
type. -/
theorem not_objTree_epsNF {φ : Formula Const []} (form : ImpForm φ) :
    ¬ ObjTree (e.epsNF names.base φ) := by
  induction form with
  | @atom a atom =>
      rw [e.epsNF_atom names.base atom]
      intro tree
      generalize same : LF.Term.app (.con "eps") (e.translateNF names.base a) = t at tree
      cases tree <;> simp at same
  | @imp p q _ _ ihp _ =>
      rw [names.epsNF_imp]
      intro tree
      cases tree with
      | pi domainTree _ => exact ihp domainTree

/-- **No object type converts with the type of the proofs of a formula of the
fragment.** -/
theorem objTree_not_conv_epsNF {C : LF.Term} (tree : ObjTree C) {φ : Formula Const []}
    (form : ImpForm φ) : ¬ Conv STTfa.theory C (e.epsNF names.base φ) := by
  intro converted
  exact not_objTree_epsNF names form
    (tree.reduces (sttfa_reduces_of_conv converted (epsNF_normal names form)))

/-- A hypothesis entry of a context: a closed type that converts with the
normal type of the proofs of a formula of the fragment. -/
def HypEntry (entry : LF.Term) (δ : Formula Const []) : Prop :=
  Closed entry ∧ ImpForm δ ∧ Conv STTfa.theory entry (e.epsNF names.base δ)

theorem lookup_hypEntry {Γ : LFTyping.Ctx} {Δ : List (Formula Const [])}
    (related : List.Forall₂ (HypEntry names) Γ Δ) : ∀ {index : Nat} {found : LF.Term},
      LFTyping.ctxLookup Γ index = some found → ∃ j : Fin Δ.length, HypEntry names found (Δ.get j) := by
  induction related with
  | nil => intro index found lookup; simp [ctxLookup_eq_getElem?] at lookup
  | @cons entry δ Γ Δ head tail ih =>
      intro index found lookup
      cases index with
      | zero =>
          rw [lookup_cons_zero, head.1.lift] at lookup
          cases lookup
          exact ⟨⟨0, by simp⟩, head⟩
      | succ index =>
          rw [lookup_cons_succ] at lookup
          obtain ⟨prior, priorLookup, same⟩ := Option.map_eq_some_iff.mp lookup
          obtain ⟨j, entryJ⟩ := ih priorLookup
          rw [← same, entryJ.1.lift]
          exact ⟨j.succ, by simpa using entryJ⟩

/-- What a term may be typed at when it is not an abstraction: the type of the
proofs of a formula of the fragment that it proves, or an object type. -/
def NeutralType (Δ : List (Formula Const [])) (A : LF.Term) : Prop :=
  (∃ ψ, ImpForm ψ ∧ Conv STTfa.theory A (e.epsNF names.base ψ) ∧
      Nonempty (HOL.ProofSyntaxModulo [] Δ ψ)) ∨
    ∃ C, ObjTree C ∧ Conv STTfa.theory A C

/-- A type all of whose readings as the type of the proofs of a formula of the
fragment are proved. -/
def Proves (Δ : List (Formula Const [])) (A : LF.Term) : Prop :=
  ∀ φ, ImpForm φ → Conv STTfa.theory A (e.epsNF names.base φ) →
    Nonempty (HOL.ProofSyntaxModulo [] Δ φ)

theorem proves_of_neutral {Δ : List (Formula Const [])} {A : LF.Term}
    (neutral : NeutralType names Δ A) : Proves names Δ A := by
  intro φ form converted
  rcases neutral with ⟨ψ, formψ, convψ, proof⟩ | ⟨C, tree, convC⟩
  · have same : e.epsNF names.base ψ = e.epsNF names.base φ :=
      sttfa_normal_conv_eq (epsNF_normal names formψ) (epsNF_normal names form)
        (.trans _ _ _ (.symm _ _ convψ) converted)
    rw [← epsNF_injective names formψ form same]
    exact proof
  · exact absurd (.trans _ _ _ (.symm _ _ convC) converted) (objTree_not_conv_epsNF names tree form)

/-- **The induction of adequacy.**  For a normal term typed in a context of
hypotheses: every reading of its type as the type of the proofs of a formula
of the fragment is proved, and when the term is not an abstraction its type is
the type of the proofs of a formula it proves, or an object type. -/
theorem adequacy_induction : ∀ (M : LF.Term) {Γ : LFTyping.Ctx} {Δ : List (Formula Const [])}
    {A : LF.Term}, List.Forall₂ (HypEntry names) Γ Δ → IsNormal (Step STTfa.theory) M →
    LambdaPiModulo (sttfaProofTheory e) Γ M A →
    Proves names Δ A ∧ ((∀ domain body, M ≠ .lam domain body) → NeutralType names Δ A) := by
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  intro M
  induction M with
  | srt sort =>
      intro Γ Δ A related normal typed
      have neutral : NeutralType names Δ A := by
        obtain ⟨target, _, converted⟩ := typed.sort_inv
        exact Or.inr ⟨.srt target, .sort target, .symm _ _ (conv_proofTheory converted)⟩
      exact ⟨proves_of_neutral names neutral, fun _ => neutral⟩
  | con name =>
      intro Γ Δ A related normal typed
      have neutral : NeutralType names Δ A := by
        obtain ⟨declared, found, converted⟩ := typed.con_inv
        exact Or.inr ⟨declared, objTree_constType names found,
          .symm _ _ (conv_proofTheory converted)⟩
      exact ⟨proves_of_neutral names neutral, fun _ => neutral⟩
  | var index =>
      intro Γ Δ A related normal typed
      have neutral : NeutralType names Δ A := by
        obtain ⟨declared, found, converted⟩ := typed.var_inv
        obtain ⟨j, _, form, entryConv⟩ := lookup_hypEntry names related found
        exact Or.inl ⟨Δ.get j, form,
          .trans _ _ _ (.symm _ _ (conv_proofTheory converted)) entryConv, ⟨.hyp j⟩⟩
      exact ⟨proves_of_neutral names neutral, fun _ => neutral⟩
  | pi domain body _ _ =>
      intro Γ Δ A related normal typed
      have neutral : NeutralType names Δ A := by
        obtain ⟨_, _, resultSort, _, _, _, converted⟩ := typed.pi_inv
        exact Or.inr ⟨.srt resultSort, .sort resultSort, .symm _ _ (conv_proofTheory converted)⟩
      exact ⟨proves_of_neutral names neutral, fun _ => neutral⟩
  | lam domain body _ ihBody =>
      intro Γ Δ A related normal typed
      refine ⟨?_, fun notLam => absurd rfl (notLam domain body)⟩
      intro φ form converted
      obtain ⟨bodyType, _, _, _, _, _, _, bodyTyped, typeConv⟩ := typed.lam_inv
      have toNF : Reduces STTfa.theory (.pi domain bodyType) (e.epsNF names.base φ) :=
        sttfa_reduces_of_conv (.trans _ _ _ (conv_proofTheory typeConv) converted)
          (epsNF_normal names form)
      obtain ⟨domain', bodyType', shape, domainReduces, bodyReduces⟩ := toNF.pi_inv headed
      cases form with
      | @atom a atom =>
          rw [e.epsNF_atom names.base atom] at shape
          cases shape
      | @imp p q formP formQ =>
          rw [names.epsNF_imp] at shape
          simp only [LF.Term.pi.injEq] at shape
          obtain ⟨rfl, rfl⟩ := shape
          have domainEq := (normal_lam_domain normal).reflTransGen_eq domainReduces
          subst domainEq
          have related' : List.Forall₂ (HypEntry names) (e.epsNF names.base p :: Γ) (p :: Δ) :=
            .cons ⟨e.epsNF_closed names.base_closed p, formP, .refl _⟩ related
          obtain ⟨proof⟩ :=
            (ihBody related' (normal_lam_body normal) bodyTyped).1 q formQ bodyReduces.conv
          exact ⟨.impI proof⟩
  | app function argument ihFunction ihArgument =>
      intro Γ Δ A related normal typed
      have notLam : ∀ domain body, function ≠ .lam domain body := by
        rintro domain body rfl
        exact normal _ (Step.root (.beta domain body argument))
      obtain ⟨domain, bodyType, functionTyped, argumentTyped, typeConv⟩ := typed.app_inv
      have neutral : NeutralType names Δ A := by
        rcases (ihFunction related (normal_app_function normal) functionTyped).2 notLam with
          ⟨ψ, formψ, convψ, ⟨proofψ⟩⟩ | ⟨C, tree, convC⟩
        · have toNF := sttfa_reduces_of_conv convψ (epsNF_normal names formψ)
          obtain ⟨domain', bodyType', shape, domainReduces, bodyReduces⟩ := toNF.pi_inv headed
          cases formψ with
          | @atom a atom =>
              rw [e.epsNF_atom names.base atom] at shape
              cases shape
          | @imp p q formP formQ =>
              rw [names.epsNF_imp] at shape
              simp only [LF.Term.pi.injEq] at shape
              obtain ⟨rfl, rfl⟩ := shape
              obtain ⟨proofP⟩ := (ihArgument related (normal_app_argument normal)
                argumentTyped).1 p formP domainReduces.conv
              have substituted := Conv.subst sttfa_closedBodies bodyReduces.conv 0 argument
              rw [(e.epsNF_closed names.base_closed q).subst] at substituted
              exact Or.inl ⟨q, formQ,
                .trans _ _ _ (.symm _ _ (conv_proofTheory typeConv)) substituted,
                ⟨.impE proofψ proofP⟩⟩
        · obtain ⟨common, toCommon, fromC⟩ := (conv_iff_joinable STTfa.confluent).mp convC
          obtain ⟨domain', bodyType', rfl, _, bodyReduces⟩ := toCommon.pi_inv headed
          have bodyTree := (tree.reduces fromC).pi_body
          exact Or.inr ⟨subst0 argument bodyType', bodyTree.subst 0 argument,
            .trans _ _ _ (.symm _ _ (conv_proofTheory typeConv))
              (Conv.subst sttfa_closedBodies bodyReduces.conv 0 argument)⟩
      exact ⟨proves_of_neutral names neutral, fun _ => neutral⟩

/-- The types of the proofs of the hypotheses form a context of hypotheses. -/
theorem forall₂_hypotheses : ∀ {Δ : List (Formula Const [])}, (∀ δ ∈ Δ, ImpForm δ) →
    List.Forall₂ (HypEntry names) (Δ.map fun δ => .app (.con "eps") (e.translate δ)) Δ
  | [], _ => .nil
  | δ :: _, forms =>
      .cons ⟨.app .con (e.translate_wellScoped δ), forms δ List.mem_cons_self,
          (reduces_eps names (forms δ List.mem_cons_self)).conv⟩
        (forall₂_hypotheses fun δ' member => forms δ' (List.mem_cons_of_mem _ member))

/-- **Adequacy of the STTfa hub on the closed implicational fragment**: a
normal term of the type of the proofs of a formula, in the context of the types
of the proofs of hypotheses, all of the fragment, gives a proof of the formula
from the hypotheses. -/
theorem sttfa_adequate {Δ : List (Formula Const [])} (hypotheses : ∀ δ ∈ Δ, ImpForm δ)
    {φ : Formula Const []} (form : ImpForm φ) {M : LF.Term}
    (normal : IsNormal (Step (sttfaProofTheory e)) M)
    (typed : LambdaPiModulo (sttfaProofTheory e)
      (Δ.map fun δ => .app (.con "eps") (e.translate δ)) M (.app (.con "eps") (e.translate φ))) :
    Nonempty (HOL.ProofSyntaxModulo [] Δ φ) := by
  rw [step_proofTheory] at normal
  exact (adequacy_induction names M (forall₂_hypotheses names hypotheses) normal typed).1 φ form
    (reduces_eps names form).conv

/-- **A normal closed inhabitant of the type of the proofs of a formula of the
fragment gives a theorem.** -/
theorem sttfa_adequate_closed {φ : Formula Const []} (form : ImpForm φ) {M : LF.Term}
    (normal : IsNormal (Step (sttfaProofTheory e)) M)
    (typed : LambdaPiModulo (sttfaProofTheory e) [] M (.app (.con "eps") (e.translate φ))) :
    Nonempty (HOL.ProofSyntaxModulo [] [] φ) :=
  sttfa_adequate names (Δ := []) (fun _ member => absurd member List.not_mem_nil) form normal typed

end Adequacy

/-! ## Controls -/

/-- `pred point`. -/
def predPoint : Formula ControlConst [] := .app (.const ControlConst.pred) (.const ControlConst.point)

theorem predPoint_normal : HOL.BetaNormalization.Normal predPoint := by
  rintro target ⟨step⟩
  cases step with
  | appFun _ inner => cases inner
  | appArg _ inner => cases inner

theorem predPoint_atom : Atom predPoint where
  normal := predPoint_normal
  notImp _ _ same := by simp [predPoint] at same
  notAll _ same := by simp [predPoint] at same

/-- The controls satisfy the names of the STTfa hub with proofs. -/
theorem sttfaControl_names : SttfaNames sttfaControl where
  el := rfl
  arrow := rfl
  imp := rfl
  all := rfl
  fresh := sttfaControl_fresh
  typeFresh := sttfaControl_typeFresh
  forallPFresh s := by
    cases s <;> (try (rename_i c; cases c)) <;> simp [sttfaControl, controlEncoding, controlName]
  pFresh s := by
    cases s <;> (try (rename_i c; cases c)) <;> simp [sttfaControl, controlEncoding, controlName]
  forallKFresh s := by
    cases s <;> (try (rename_i c; cases c)) <;> simp [sttfaControl, controlEncoding, controlName]

/-- The type of the proofs of `pred point`. -/
abbrev predPointProofs : LF.Term := .app (.con "eps") (sttfaControl.translate predPoint)

theorem predPointProofs_normal : IsNormal (Step STTfa.theory) predPointProofs := by
  have normal := epsNF_normal sttfaControl_names (.atom predPoint_atom)
  rwa [sttfaControl.epsNF_atom _ predPoint_atom] at normal

theorem predPointProofs_closed : Closed predPointProofs :=
  .app .con (sttfaControl.translate_wellScoped predPoint)

/-- `⊢ pred point ⇒ pred point`. -/
def predIdentityProof :
    HOL.ProofSyntaxModulo [] ([] : List (Formula ControlConst [])) (.imp predPoint predPoint) :=
  .impI (.hyp ⟨0, by decide⟩)

/-- Its compilation is `λ h : eps (pred point). h`. -/
theorem compile_predIdentity :
    compile sttfaControl "eps" predIdentityProof (.base []) Fin.elim0 =
      .lam predPointProofs (.var 0) := rfl

theorem predIdentity_normal :
    IsNormal (Step (sttfaProofTheory sttfaControl)) (.lam predPointProofs (.var 0)) := by
  rw [step_proofTheory]
  intro target step
  rcases step.lam_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · exact RootStep.not_lam STTfa.orthogonal.leftAlgebraic.headed root
  · exact predPointProofs_normal _ inner
  · exact var_normal STTfa.orthogonal.leftAlgebraic.headed _ _ inner

/-- **Adequacy at an introduction**: the normal compiled identity gives back a
proof of `pred point ⇒ pred point`. -/
theorem predIdentity_adequate :
    Nonempty (HOL.ProofSyntaxModulo [] ([] : List (Formula ControlConst []))
      (.imp predPoint predPoint)) :=
  sttfa_adequate_closed sttfaControl_names (.imp (.atom predPoint_atom) (.atom predPoint_atom))
    predIdentity_normal (by
      rw [← compile_predIdentity]
      exact sttfa_theorem_typed sttfaControl rfl rfl rfl rfl sttfaControl_fresh
        sttfaControl_typeFresh predIdentityProof)

/-- The hypotheses `pred point ⇒ pred point` and `pred point`. -/
def modusPonensHypotheses : List (Formula ControlConst []) := [.imp predPoint predPoint, predPoint]

/-- The types of their proofs. -/
abbrev modusPonensContext : LFTyping.Ctx :=
  modusPonensHypotheses.map fun δ => .app (.con "eps") (sttfaControl.translate δ)

/-- `h₀ h₁` is typed at the type of the proofs of `pred point`. -/
theorem modusPonens_typed :
    LambdaPiModulo (sttfaProofTheory sttfaControl) modusPonensContext (.app (.var 0) (.var 1))
      predPointProofs := by
  have declares := sttfaControlProofs.toDeclares
  have formulaTyped : ∀ {Γ : LFTyping.Ctx}, LambdaPiModulo (sttfaProofTheory sttfaControl) Γ
      (sttfaControl.translate predPoint) (sttfaControl.El (sttfaControl.code .prop)) :=
    declares.apply_typed (declares.sym_typed (.const .pred)) (declares.sym_typed (.const .point))
  have proofsTyped : ∀ {Γ : LFTyping.Ctx},
      LambdaPiModulo (sttfaProofTheory sttfaControl) Γ predPointProofs (.srt .type) :=
    sttfaControlProofs.proof_typed formulaTyped
  have closedP : Closed (sttfaControl.translate predPoint) :=
    sttfaControl.translate_wellScoped predPoint
  have closedImp : Closed (LF.Term.app (.con "eps") (sttfaControl.translate (.imp predPoint predPoint))) :=
    .app .con (sttfaControl.translate_wellScoped (.imp predPoint predPoint))
  have first : LambdaPiModulo (sttfaProofTheory sttfaControl) modusPonensContext (.var 0)
      (.pi predPointProofs predPointProofs) := by
    have looked : LambdaPiModulo (sttfaProofTheory sttfaControl) modusPonensContext (.var 0)
        (.app (.con "eps") (sttfaControl.translate (.imp predPoint predPoint))) := by
      refine .var ?_
      show LFTyping.ctxLookup (_ :: _) 0 = _
      rw [lookup_cons_zero, closedImp.lift]
    have converted := sttfaControlProofs.conv_imp (sttfaControl.translate predPoint)
      (sttfaControl.translate predPoint)
    rw [closedP.lift] at converted
    exact .conv looked converted (.pi proofsTyped proofsTyped arrow_rule)
  have second : LambdaPiModulo (sttfaProofTheory sttfaControl) modusPonensContext (.var 1)
      predPointProofs := by
    refine .var ?_
    show LFTyping.ctxLookup (_ :: _ :: _) 1 = _
    rw [lookup_cons_succ, lookup_cons_zero]
    simp only [Option.map_some, predPointProofs_closed.lift]
  have applied := HasType.app first second
  rwa [show subst0 (.var 1) predPointProofs = predPointProofs from
    predPointProofs_closed.subst 0 _] at applied

theorem modusPonens_normal :
    IsNormal (Step (sttfaProofTheory sttfaControl)) (.app (.var 0) (.var 1)) := by
  rw [step_proofTheory]
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  intro target step
  rcases step.app_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · rcases root.headConst_or_beta headed with ⟨_, _, _, same⟩ | ⟨_, head⟩
    · cases same
    · simp [headConst] at head
  · exact var_normal headed _ _ inner
  · exact var_normal headed _ _ inner

/-- **Adequacy at an elimination**: the normal term `h₀ h₁` gives back a proof of
`pred point` from `pred point ⇒ pred point` and `pred point`. -/
theorem modusPonens_adequate : Nonempty (HOL.ProofSyntaxModulo [] modusPonensHypotheses predPoint) :=
  sttfa_adequate sttfaControl_names (by
      intro δ member
      simp only [modusPonensHypotheses, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .imp (.atom predPoint_atom) (.atom predPoint_atom)
      · exact .atom predPoint_atom)
    (.atom predPoint_atom) modusPonens_normal modusPonens_typed

/-- A model of the controls in which `pred` holds of nothing. -/
def emptyPredModel : HOL.HenkinModel.{0, 0, 0} Unit ControlConst where
  Carrier := fun _ => ULift Unit
  adm := fun _ _ => True
  base_mem := fun _ _ => trivial
  prop_mem := fun _ => trivial
  app_mem := fun _ _ => trivial
  constDen := fun c => match c with
    | .point => ULift.up ()
    | .pred => fun _ => ULift.up False
  const_mem := fun _ => trivial
  term_closed := fun _ _ _ => trivial

/-- `pred point` is no theorem: it fails in the model. -/
theorem predPoint_unprovable :
    IsEmpty (HOL.ProofSyntaxModulo [] ([] : List (Formula ControlConst [])) predPoint) :=
  ⟨fun d => HOL.Soundness.proofSyntaxModulo_sound d (M := emptyPredModel)
    (fun _ member => absurd member List.not_mem_nil) (ρ := fun v => nomatch v) (fun v => nomatch v)
    (fun _ member => absurd member List.not_mem_nil)⟩

/-- **The hub has no normal closed proof of `pred point`**, by adequacy. -/
theorem predPoint_no_normal_inhabitant :
    ¬ ∃ M : LF.Term, IsNormal (Step (sttfaProofTheory sttfaControl)) M ∧
      LambdaPiModulo (sttfaProofTheory sttfaControl) [] M predPointProofs := by
  rintro ⟨M, normal, typed⟩
  obtain ⟨d⟩ := sttfa_adequate_closed sttfaControl_names (.atom predPoint_atom) normal typed
  exact predPoint_unprovable.false d

/-! ## The boundary at universal quantification -/

/-- The constants of the rules of the STTfa hub. -/
def sttfaRuleConstants : List String :=
  ["eta", "type", "etap", "p", "arrow", "forallK", "eps", "forall", "impl", "forallP"]

/-- Every occurrence of the constant `name` is applied to two arguments at
least: Cousineau and Dowek's weak η-long condition, for one binary constant. -/
inductive Applied (name : String) : LF.Term → Prop where
  | srt (sort : LF.Srt) : Applied name (.srt sort)
  | var (index : Nat) : Applied name (.var index)
  | con {other : String} : other ≠ name → Applied name (.con other)
  | pi {domain body : LF.Term} : Applied name domain → Applied name body →
      Applied name (.pi domain body)
  | lam {domain body : LF.Term} : Applied name domain → Applied name body →
      Applied name (.lam domain body)
  | app {function argument : LF.Term} : Applied name function → Applied name argument →
      Applied name (.app function argument)
  | binary {left right : LF.Term} : Applied name left → Applied name right →
      Applied name (.app (.app (.con name) left) right)

namespace Applied

variable {name : String}

theorem not_bare : ¬ Applied name (.con name) := by
  intro applied
  generalize same : LF.Term.con name = t at applied
  cases applied with
  | con distinct => cases same; exact distinct rfl
  | _ => cases same

theorem app_argument {function argument : LF.Term} (applied : Applied name (.app function argument)) :
    Applied name argument := by
  cases applied with
  | app _ argumentApplied => exact argumentApplied
  | binary _ rightApplied => exact rightApplied

theorem app_function {function argument : LF.Term} (applied : Applied name (.app function argument))
    (notName : ∀ left, function ≠ .app (.con name) left) : Applied name function := by
  cases applied with
  | app functionApplied _ => exact functionApplied
  | binary _ _ => exact absurd rfl (notName _)

theorem app_con_argument {other : String} {argument : LF.Term}
    (applied : Applied name (.app (.con other) argument)) : Applied name argument :=
  applied.app_argument

theorem lam_body {domain body : LF.Term} (applied : Applied name (.lam domain body)) :
    Applied name body := by
  cases applied with
  | lam _ bodyApplied => exact bodyApplied

theorem lift {t : LF.Term} (applied : Applied name t) :
    ∀ amount cutoff : Nat, Applied name (lift amount cutoff t) := by
  induction applied with
  | srt sort => intro _ _; exact .srt sort
  | var index => intro _ _; exact .var _
  | con distinct => intro _ _; exact .con distinct
  | pi _ _ ihDomain ihBody => intro amount cutoff; exact .pi (ihDomain _ _) (ihBody _ _)
  | lam _ _ ihDomain ihBody => intro amount cutoff; exact .lam (ihDomain _ _) (ihBody _ _)
  | app _ _ ihFunction ihArgument =>
      intro amount cutoff; exact .app (ihFunction _ _) (ihArgument _ _)
  | binary _ _ ihLeft ihRight => intro amount cutoff; exact .binary (ihLeft _ _) (ihRight _ _)

theorem subst {t : LF.Term} (applied : Applied name t) :
    ∀ (target : Nat) {replacement : LF.Term}, Applied name replacement →
      Applied name (LFTyping.subst target replacement t) := by
  induction applied with
  | srt sort => intro _ _ _; exact .srt sort
  | var index =>
      intro target replacement replaced
      simp only [LFTyping.subst]
      split_ifs
      · exact replaced
      · exact .var _
      · exact .var _
  | con distinct => intro _ _ _; exact .con distinct
  | pi _ _ ihDomain ihBody =>
      intro target replacement replaced
      exact .pi (ihDomain _ replaced) (ihBody _ (replaced.lift 1 0))
  | lam _ _ ihDomain ihBody =>
      intro target replacement replaced
      exact .lam (ihDomain _ replaced) (ihBody _ (replaced.lift 1 0))
  | app _ _ ihFunction ihArgument =>
      intro target replacement replaced
      exact .app (ihFunction _ replaced) (ihArgument _ replaced)
  | binary _ _ ihLeft ihRight =>
      intro target replacement replaced
      exact .binary (ihLeft _ replaced) (ihRight _ replaced)

section Hub

variable (notRule : name ∉ sttfaRuleConstants)
include notRule

theorem ne_of_rule {other : String} (member : other ∈ sttfaRuleConstants) : other ≠ name := by
  rintro rfl
  exact notRule member

/-- **A root step of the hub keeps every occurrence of `name` applied**, for a
constant that occurs in no rule. -/
theorem rootStep {source target : LF.Term} (applied : Applied name source)
    (root : RootStep STTfa.theory source target) : Applied name target := by
  have ne : ∀ other ∈ sttfaRuleConstants, other ≠ name := fun _ member => ne_of_rule notRule member
  have neEta := ne "eta" (by simp [sttfaRuleConstants])
  have neType := ne "type" (by simp [sttfaRuleConstants])
  have neEtap := ne "etap" (by simp [sttfaRuleConstants])
  have neP := ne "p" (by simp [sttfaRuleConstants])
  have neArrow := ne "arrow" (by simp [sttfaRuleConstants])
  have neForallK := ne "forallK" (by simp [sttfaRuleConstants])
  have neEps := ne "eps" (by simp [sttfaRuleConstants])
  have neForall := ne "forall" (by simp [sttfaRuleConstants])
  have neImpl := ne "impl" (by simp [sttfaRuleConstants])
  have neForallP := ne "forallP" (by simp [sttfaRuleConstants])
  rcases rootStep_cases root with ⟨domain, body, argument, rfl, rfl⟩ | ⟨_, rfl, defined⟩ |
    ⟨rule, assignment, member, rfl, rfl⟩
  · have bodyApplied := (applied.app_function (by intro _ same; cases same)).lam_body
    exact bodyApplied.subst 0 applied.app_argument
  · rw [sttfa_undefined] at defined
    cases defined
  · rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [STTfa.etaDef, STTfa.etap, inst, Dedukti.instantiate]
      exact .lam (.con neType) (.app (.con neEtap) (.app (.con neP) (.var 0)))
    · simp only [STTfa.etapArrow, STTfa.etap, STTfa.eta, STTfa.binary, inst,
        Dedukti.instantiate] at applied ⊢
      simp only [Nat.lt_irrefl, if_false, Nat.sub_zero, Mettapedia.GSLT.Dedukti.lift_zero,
        show (1 : Nat) - 1 = 0 from rfl, show ¬ (1 : Nat) < 0 from by decide] at applied ⊢
      have codeApplied := applied.app_con_argument.app_con_argument
      have left := (codeApplied.app_function (by intro _ same; cases same; exact neArrow rfl))
      exact .pi (.app (.con neEta) left.app_con_argument)
        (.app (.con neEta) (codeApplied.app_argument.lift 1 0))
    · simp only [STTfa.etapForall, STTfa.etap, inst, Dedukti.instantiate] at applied ⊢
      simp only [Nat.lt_irrefl, if_false, Nat.sub_self, Mettapedia.GSLT.Dedukti.lift_zero,
        show (0 : Nat) < 1 from by decide, if_true] at applied ⊢
      have family := applied.app_con_argument.app_con_argument
      exact .pi (.con neType) (.app (.con neEtap) (.app (family.lift 1 0) (.var 0)))
    · simp only [STTfa.epsForall, STTfa.eps, STTfa.eta, STTfa.binary, inst,
        Dedukti.instantiate] at applied ⊢
      simp only [Nat.lt_irrefl, if_false, Nat.sub_zero, Mettapedia.GSLT.Dedukti.lift_zero,
        show ¬ (1 : Nat) < 0 from by decide, show (0 : Nat) < 1 from by decide, if_true,
        show (1 : Nat) - 1 = 0 from rfl] at applied ⊢
      have code := applied.app_con_argument
      have left := code.app_function (by intro _ same; cases same; exact neForall rfl)
      exact .pi (.app (.con neEta) left.app_con_argument)
        (.app (.con neEps) (.app (code.app_argument.lift 1 0) (.var 0)))
    · simp only [STTfa.epsImpl, STTfa.eps, STTfa.binary, inst, Dedukti.instantiate] at applied ⊢
      simp only [Nat.lt_irrefl, if_false, Nat.sub_zero, Mettapedia.GSLT.Dedukti.lift_zero,
        show ¬ (1 : Nat) < 0 from by decide, show (1 : Nat) - 1 = 0 from rfl] at applied ⊢
      have code := applied.app_con_argument
      have left := code.app_function (by intro _ same; cases same; exact neImpl rfl)
      exact .pi (.app (.con neEps) left.app_con_argument)
        (.app (.con neEps) (code.app_argument.lift 1 0))
    · simp only [STTfa.epsForallP, STTfa.eps, inst, Dedukti.instantiate] at applied ⊢
      simp only [Nat.lt_irrefl, if_false, Nat.sub_self, Mettapedia.GSLT.Dedukti.lift_zero,
        show (0 : Nat) < 1 from by decide, if_true] at applied ⊢
      have family := applied.app_con_argument.app_con_argument
      exact .pi (.con neType) (.app (.con neEps) (.app (family.lift 1 0) (.var 0)))

/-- **Steps of the hub keep every occurrence of `name` applied.** -/
theorem step {source target : LF.Term} (applied : Applied name source)
    (step : Step STTfa.theory source target) : Applied name target := by
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  induction applied generalizing target with
  | srt sort => exact absurd step (srt_normal headed sort _)
  | var index => exact absurd step (var_normal headed index _)
  | con distinct => exact rootStep notRule (.con distinct) step.con_inv
  | pi domainApplied bodyApplied ihDomain ihBody =>
      rcases step.pi_inv with root | ⟨_, inner, rfl⟩ | ⟨_, inner, rfl⟩
      · exact absurd root (RootStep.not_pi headed)
      · exact .pi (ihDomain inner) bodyApplied
      · exact .pi domainApplied (ihBody inner)
  | lam domainApplied bodyApplied ihDomain ihBody =>
      rcases step.lam_inv with root | ⟨_, inner, rfl⟩ | ⟨_, inner, rfl⟩
      · exact absurd root (RootStep.not_lam headed)
      · exact .lam (ihDomain inner) bodyApplied
      · exact .lam domainApplied (ihBody inner)
  | app functionApplied argumentApplied ihFunction ihArgument =>
      rcases step.app_inv with root | ⟨_, inner, rfl⟩ | ⟨_, inner, rfl⟩
      · exact rootStep notRule (.app functionApplied argumentApplied) root
      · exact .app (ihFunction inner) argumentApplied
      · exact .app functionApplied (ihArgument inner)
  | binary leftApplied rightApplied ihLeft ihRight =>
      rcases step.app_inv with root | ⟨_, inner, rfl⟩ | ⟨_, inner, rfl⟩
      · exact rootStep notRule (.binary leftApplied rightApplied) root
      · rcases inner.app_inv with root' | ⟨_, inner', rfl⟩ | ⟨_, inner', rfl⟩
        · obtain ⟨rule, assignment, member, shape, -⟩ := rootStep_app_con_rule root'
          exfalso
          rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp only [STTfa.etaDef, STTfa.etapArrow, STTfa.etapForall, STTfa.epsImpl,
              STTfa.epsForall, STTfa.epsForallP, STTfa.eta, STTfa.etap, STTfa.eps,
              STTfa.binary, inst_app, inst_con, LF.Term.app.injEq, LF.Term.con.injEq,
              reduceCtorEq] at shape
          all_goals exact ne_of_rule notRule (by simp [sttfaRuleConstants]) shape.1
        · exfalso
          rcases rootStep_cases inner'.con_inv with ⟨_, _, _, same, _⟩ | ⟨_, same, defined⟩ |
            ⟨rule, assignment, member, same, -⟩
          · cases same
          · cases same
            rw [sttfa_undefined] at defined
            cases defined
          · rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp only [STTfa.etaDef, STTfa.etapArrow, STTfa.etapForall, STTfa.epsImpl,
                STTfa.epsForall, STTfa.epsForallP, STTfa.eta, STTfa.etap, STTfa.eps,
                STTfa.binary, inst_app, inst_con, LF.Term.con.injEq, reduceCtorEq] at same
            exact ne_of_rule notRule (by simp [sttfaRuleConstants]) same.symm
        · exact .binary (ihLeft inner') rightApplied
      · exact .binary leftApplied (ihRight inner)

theorem reduces {source target : LF.Term} (applied : Applied name source)
    (reduces : Reduces STTfa.theory source target) : Applied name target := by
  induction reduces with
  | refl => exact applied
  | tail _ step ih => exact Applied.step notRule ih step

end Hub

end Applied

section Boundary

variable {e : Encoding Base Const} (names : SttfaNames e)
include names

/-- **Translations apply `and` to both operands.** -/
theorem translate_applied : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ),
    Applied (e.name .and) (e.translate t) := by
  have named : ∀ {s : Symbol Base Const}, s ≠ .and → Applied (e.name .and) (.con (e.name s)) :=
    fun distinct => .con fun same => distinct (e.injective same)
  have elApplied : Applied (e.name .and) (.con e.el) :=
    .con fun same => (names.fresh .and).1 (by rw [← same, names.el])
  have codeApplied : ∀ τ : Ty Base, Applied (e.name .and) (e.code τ) := by
    intro τ
    induction τ with
    | prop => exact named (by simp)
    | base b => exact named (by simp)
    | arr σ τ ihσ ihτ => exact .app (.app (named (by simp)) ihσ) ihτ
  have decodingApplied : ∀ τ : Ty Base, Applied (e.name .and) (e.El (e.code τ)) :=
    fun τ => .app elApplied (codeApplied τ)
  intro Γ τ t
  induction t with
  | var v => exact .var _
  | const c => exact named (by simp)
  | app f a ihf iha => exact .app ihf iha
  | @lam σ Γ τ body ih => exact .lam (decodingApplied σ) ih
  | top => exact named (by simp)
  | bot => exact named (by simp)
  | and p q ihp ihq => exact .binary ihp ihq
  | or p q ihp ihq => exact .app (.app (named (by simp)) ihp) ihq
  | imp p q ihp ihq => exact .app (.app (named (by simp)) ihp) ihq
  | not p ih => exact .app (named (by simp)) ih
  | @eq Γ τ l r ihl ihr => exact .app (.app (.app (named (by simp)) (codeApplied τ)) ihl) ihr
  | @all σ Γ body ih =>
      exact .app (.app (named (by simp)) (codeApplied σ)) (.lam (decodingApplied σ) ih)
  | @ex σ Γ body ih =>
      exact .app (.app (named (by simp)) (codeApplied σ)) (.lam (decodingApplied σ) ih)

/-- **The bare connective converts with no translation**: `and`, not applied,
is normal and has the type of the code of `prop ⇒ prop ⇒ prop`, but every
translation applies `and` to two operands, and the steps of the hub keep it
so (Cousineau and Dowek's witness, at a connective of higher-order logic). -/
theorem bareAnd_not_conv_translate (notRule : e.name .and ∉ sttfaRuleConstants)
    {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    ¬ Conv STTfa.theory (.con (e.name .and)) (e.translate t) := by
  intro converted
  have toBare := sttfa_reduces_of_conv (.symm _ _ converted)
    (sttfa_con_normal (names.fresh .and).1)
  exact Applied.not_bare ((translate_applied names t).reduces notRule toBare)

end Boundary

/-! ### The witness -/

/-- A translation is a constant only for a constant of the signature, `⊤` or
`⊥`. -/
theorem translate_eq_con (e : Encoding Base Const) {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ) {name : String} (same : e.translate t = .con name) :
    (∃ (τ' : Ty Base) (c : Const τ'), name = e.name (.const c)) ∨ name = e.name .top ∨
      name = e.name .bot := by
  cases t with
  | const c => exact Or.inl ⟨_, c, (LF.Term.con.inj same).symm⟩
  | top => exact Or.inr (Or.inl (LF.Term.con.inj same).symm)
  | bot => exact Or.inr (Or.inr (LF.Term.con.inj same).symm)
  | _ => simp [Encoding.translate, Encoding.sym, Encoding.binary, Encoding.equation,
      Encoding.binder] at same

theorem lift_eq_con {amount cutoff : Nat} {t : LF.Term} {name : String}
    (same : lift amount cutoff t = .con name) : t = .con name := by
  cases t <;> simp [LFTyping.lift] at same ⊢
  exact same

theorem place_eq_con {Γ : Ctx Base} (L : Layout Const Γ) :
    ∀ {k : Nat} {t : LF.Term} {name : String}, L.place k t = .con name → t = .con name := by
  induction L with
  | base _ => intro k t name same; exact same
  | obj rest _ ih => intro k t name same; exact ih same
  | hyp rest _ ih => intro k t name same; exact ih (lift_eq_con same)

/-- A compiled proof is never a constant. -/
theorem compile_ne_con (e : Encoding Base Const) (proof : String) {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} (d : HOL.ProofSyntaxModulo [] Δ φ)
    (L : Layout Const Γ) (hypVar : Fin Δ.length → Nat) (name : String) :
    compile e proof d L hypVar ≠ .con name := by
  induction d with
  | hyp _ => simp [compile]
  | impI _ _ => simp [compile]
  | impE _ _ _ _ => simp [compile]
  | allI _ _ => simp [compile]
  | allE _ _ _ => simp [compile]
  | convert _ _ ih => exact ih L hypVar

/-- **No proof compiles to a variable applied to the bare `and`.** -/
theorem compile_ne_bareAnd (e : Encoding Base Const) (proof : String) {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} (d : HOL.ProofSyntaxModulo [] Δ φ)
    (L : Layout Const Γ) (hypVar : Fin Δ.length → Nat) (index : Nat) :
    compile e proof d L hypVar ≠ .app (.var index) (.con (e.name .and)) := by
  induction d with
  | hyp _ => simp [compile]
  | impI _ _ => simp [compile]
  | impE function argument _ _ =>
      simp only [compile, ne_eq, LF.Term.app.injEq, not_and]
      intro _
      exact compile_ne_con e proof argument L hypVar _
  | allE t function _ =>
      simp only [compile, ne_eq, LF.Term.app.injEq, not_and]
      intro _ same
      rcases translate_eq_con e t (place_eq_con L same) with ⟨_, c, named⟩ | named | named
      · exact nomatch e.injective named
      · exact nomatch e.injective named
      · exact nomatch e.injective named
  | allI _ _ => simp [compile]
  | convert _ _ ih => exact ih L hypVar

/-- `∀ f : prop ⇒ prop ⇒ prop. pred point`. -/
def andWitnessFormula : Formula ControlConst [] :=
  .all (σ := .arr .prop (.arr .prop .prop)) (.app (.const ControlConst.pred) (.const ControlConst.point))

/-- **The witness**: the hypothesis of `∀ f. pred point` applied to the bare
`and`. -/
def andWitnessTerm : LF.Term := .app (.var 0) (.con "and")

theorem andWitnessTerm_normal :
    IsNormal (Step (sttfaProofTheory sttfaControl)) andWitnessTerm := by
  rw [step_proofTheory]
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  intro target step
  rcases step.app_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · rcases root.headConst_or_beta headed with ⟨_, _, _, same⟩ | ⟨_, head⟩
    · cases same
    · simp [headConst] at head
  · exact var_normal headed _ _ inner
  · exact sttfa_con_normal (by decide) _ inner

/-- The witness is typed at the type of the proofs of `pred point`, in the
context of the proofs of `∀ f. pred point`. -/
theorem andWitnessTerm_typed :
    LambdaPiModulo (sttfaProofTheory sttfaControl)
      [.app (.con "eps") (sttfaControl.translate andWitnessFormula)] andWitnessTerm
      predPointProofs := by
  have declares := sttfaControlProofs.toDeclares
  have formulaTyped : ∀ {Γ : LFTyping.Ctx}, LambdaPiModulo (sttfaProofTheory sttfaControl) Γ
      (sttfaControl.translate predPoint) (sttfaControl.El (sttfaControl.code .prop)) :=
    declares.apply_typed (declares.sym_typed (.const .pred)) (declares.sym_typed (.const .point))
  have closedAll : Closed (LF.Term.app (.con "eps") (sttfaControl.translate andWitnessFormula)) :=
    .app .con (sttfaControl.translate_wellScoped andWitnessFormula)
  have looked : LambdaPiModulo (sttfaProofTheory sttfaControl)
      [.app (.con "eps") (sttfaControl.translate andWitnessFormula)] (.var 0)
      (.app (.con "eps") (sttfaControl.translate andWitnessFormula)) := by
    refine .var ?_
    rw [lookup_cons_zero, closedAll.lift]
  have asFunction : LambdaPiModulo (sttfaProofTheory sttfaControl)
      [.app (.con "eps") (sttfaControl.translate andWitnessFormula)] (.var 0)
      (.pi (sttfaControl.El (sttfaControl.code (.arr .prop (.arr .prop .prop)))) predPointProofs) :=
    .conv looked (sttfaControlProofs.conv_all _ _)
      (.pi (declares.El_code_typed _) (sttfaControlProofs.proof_typed formulaTyped) arrow_rule)
  have applied := HasType.app asFunction (declares.sym_typed (Γ := [_]) .and)
  rwa [show subst0 (sttfaControl.sym .and) predPointProofs = predPointProofs from
    predPointProofs_closed.subst 0 _] at applied

/-- `pred point` follows from `∀ f. pred point`, with the witness `λ p q. p`. -/
theorem andWitnessFormula_provable :
    Nonempty (HOL.ProofSyntaxModulo [] [andWitnessFormula] predPoint) :=
  ⟨HOL.ProofSyntaxModulo.allE (Δ := [andWitnessFormula]) (σ := .arr .prop (.arr .prop .prop))
    (φ := .app (.const ControlConst.pred) (.const ControlConst.point))
    (.lam (.lam (.var (.vs .vz)))) (.hyp ⟨0, by decide⟩)⟩

/-- **Exact adequacy fails at universal quantification**: the witness is a
normal term of the type of the proofs of `pred point`, in the context of the
proofs of `∀ f. pred point`, whose ∀-witness `and` converts with no
translation, and no proof compiles to it.  The formula is provable from the
hypothesis, with another witness. -/
theorem sttfa_not_exactly_adequate :
    IsNormal (Step (sttfaProofTheory sttfaControl)) andWitnessTerm ∧
      LambdaPiModulo (sttfaProofTheory sttfaControl)
        [.app (.con "eps") (sttfaControl.translate andWitnessFormula)] andWitnessTerm
        predPointProofs ∧
      (∀ {Γ : Ctx Unit} {τ : Ty Unit} (t : Term ControlConst Γ τ),
        ¬ Conv STTfa.theory (.con "and") (sttfaControl.translate t)) ∧
      (∀ (d : HOL.ProofSyntaxModulo [] [andWitnessFormula] predPoint)
        (L : Layout ControlConst []) (hypVar : Fin 1 → Nat),
        compile sttfaControl "eps" d L hypVar ≠ andWitnessTerm) ∧
      Nonempty (HOL.ProofSyntaxModulo [] [andWitnessFormula] predPoint) :=
  ⟨andWitnessTerm_normal, andWitnessTerm_typed,
    fun t => bareAnd_not_conv_translate sttfaControl_names (by decide) t,
    fun d L hypVar => compile_ne_bareAnd sttfaControl "eps" d L hypVar 0,
    andWitnessFormula_provable⟩

#print axioms epsNF_normal
#print axioms objTree_not_conv_epsNF
#print axioms adequacy_induction
#print axioms sttfa_adequate
#print axioms sttfa_adequate_closed
#print axioms predIdentity_adequate
#print axioms modusPonens_adequate
#print axioms predPoint_no_normal_inhabitant
#print axioms Applied.step
#print axioms bareAnd_not_conv_translate
#print axioms compile_ne_bareAnd
#print axioms sttfa_not_exactly_adequate

end Mettapedia.GSLT.Dedukti.HOLHub
