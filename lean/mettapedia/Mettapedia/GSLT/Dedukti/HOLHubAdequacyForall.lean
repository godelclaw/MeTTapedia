import Mettapedia.GSLT.Dedukti.HOLHubAdequacy
import Mettapedia.Logic.HOL.CoreReduction

/-!
# Adequacy of the STTfa hub with universal quantification, modulo the coding of witnesses

`HOLHubAdequacy` proves that every normal inhabitant of `eps (tr φ)` comes from
a HOL proof when `φ` and the hypotheses are closed implicational formulas.
This module adds universal quantification.

**Exactness fails there** (`HOLHubAdequacy.sttfa_not_exactly_adequate`): a
∀-witness of a normal inhabitant can be an object of the hub that is the
translation of no HOL term, such as the bare connective `and`.  So adequacy
holds modulo the coding of witnesses.

**The coding** (`Coded`).  A hypothesis is a variable at a position that holds
no object; an abstraction binds a hypothesis, at a type of the shape of the
types of proofs, or an object, at the computed decoding of its type; an
application applies a proof to a proof, or to a ∀-witness that is the
translation, with computed domains, of a core HOL term placed among the
variables.  The placement is a renaming `ρ` of the HOL context of objects into
the variables of the framework.

**Contexts** (`Scoped`).  Each object sits at its place, at a type converting
with the decoding of its type; every other variable is a hypothesis, at a type
converting with the type of the proofs of a placed hypothesis.  Hypotheses
(`Scoped.extendHyp`) and objects (`Scoped.extendObj`, which weakens the
hypotheses) extend such contexts.

**The types of proofs of all formulas.**  The normal type of the proofs of a
β-normal formula is normal in every context (`epsNF_normal_all`, through the
fact that lifting keeps a term normal, `normal_lift`), distinct formulas have
distinct ones (`epsNF_injective_all`), and the type of the proofs of every
formula converts with it (`conv_eps_epsNF`).  Types of proofs have the shape of
products over `eps` (`ProofShape`), and no such normal type converts with an
object type (`ProofShape.not_conv_objTree`).

**Adequacy** (`adequacy_coded`).  By induction on the coding, with typing
inversion, uniqueness of types (`proofTheory_unique`), and the typing of placed
translations with computed domains (`translateNF_typed_scoped`): a coded
normal term typed in such a context proves every core formula whose placed
type of proofs its type converts with.  A proof is moved between two such
formulas along their common normal form, by the retyping step of the checker,
which converts core formulas (`transfer`, through
`Logic.HOL.CoreConversion.of_normalForm`).

* `sttfa_adequate_coded`: closed core hypotheses and conclusion.
* `sttfa_adequate_coded_open`: a core formula with free objects, in the
  context of their decodings.

**Controls.**  `λ x. λ h. h` gives back `∀ x. pred x ⇒ pred x`
(`predSelf_adequate`), and `λ h. h point` gives back
`(∀ x. pred x) ⇒ pred point` (`predInstance_adequate`).  The bare-`and`
witness of exact adequacy's failure is coded for no placement
(`sttfa_coding_needed`).

**Scope.**  The theorems are about normal terms of the typed STTfa hub of
`HOLHubProofs`; normalization of its typed terms is not proved here.  The
formulas, the hypotheses and the witnesses are core, because the retyping step
of `ProofSyntaxModulo` converts core terms only.
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

/-! ## Lifting reflects steps -/

/-- **A root step of a lifted term comes from a root step of the term.** -/
theorem rootStep_of_lift {theory : Theory} {cutoff : Nat} {t u : LF.Term}
    (root : RootStep theory (lift 1 cutoff t) u) : ∃ u', RootStep theory t u' := by
  have back : t = LFTyping.subst cutoff (.con "type") (lift 1 cutoff t) :=
    (subst_lift_cancel t cutoff _).symm
  rcases rootStep_cases root with ⟨domain, body, argument, same, -⟩ | ⟨name, same, defined⟩ |
    ⟨rule, assignment, member, same, -⟩
  · rw [same] at back
    simp only [LFTyping.subst] at back
    rw [back]
    exact ⟨_, .beta _ _ _⟩
  · rw [lift_eq_con same]
    exact ⟨_, .delta defined⟩
  · rw [same, subst_inst] at back
    rw [back]
    exact ⟨_, .rule _ member⟩

theorem normal_pi_domain {theory : Theory} {domain body : LF.Term}
    (normal : IsNormal (Step theory) (.pi domain body)) : IsNormal (Step theory) domain :=
  fun _ step => normal _ (step.plug (.piDomain .hole body))

theorem normal_pi_body {theory : Theory} {domain body : LF.Term}
    (normal : IsNormal (Step theory) (.pi domain body)) : IsNormal (Step theory) body :=
  fun _ step => normal _ (step.plug (.piBody domain .hole))

/-- **Lifting keeps a term normal.** -/
theorem normal_lift {theory : Theory} :
    ∀ (t : LF.Term) (cutoff : Nat), IsNormal (Step theory) t →
      IsNormal (Step theory) (lift 1 cutoff t) := by
  intro t
  induction t with
  | srt sort =>
      intro cutoff normal target step
      obtain ⟨_, root⟩ := rootStep_of_lift
        (show RootStep theory (lift 1 cutoff (.srt sort)) target from step.srt_inv)
      exact normal _ (Step.root root)
  | con name =>
      intro cutoff normal target step
      obtain ⟨_, root⟩ := rootStep_of_lift
        (show RootStep theory (lift 1 cutoff (.con name)) target from step.con_inv)
      exact normal _ (Step.root root)
  | var index =>
      intro cutoff normal target step
      obtain ⟨_, root⟩ := rootStep_of_lift
        (show RootStep theory (lift 1 cutoff (.var index)) target from step.var_inv)
      exact normal _ (Step.root root)
  | pi domain body ihDomain ihBody =>
      intro cutoff normal target step
      rcases (show Step theory (.pi (lift 1 cutoff domain) (lift 1 (cutoff + 1) body)) target
          from step).pi_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
      · obtain ⟨_, root'⟩ := rootStep_of_lift
          (show RootStep theory (lift 1 cutoff (.pi domain body)) target from root)
        exact normal _ (Step.root root')
      · exact ihDomain cutoff (normal_pi_domain normal) _ inner
      · exact ihBody (cutoff + 1) (normal_pi_body normal) _ inner
  | lam domain body ihDomain ihBody =>
      intro cutoff normal target step
      rcases (show Step theory (.lam (lift 1 cutoff domain) (lift 1 (cutoff + 1) body)) target
          from step).lam_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
      · obtain ⟨_, root'⟩ := rootStep_of_lift
          (show RootStep theory (lift 1 cutoff (.lam domain body)) target from root)
        exact normal _ (Step.root root')
      · exact ihDomain cutoff (normal_lam_domain normal) _ inner
      · exact ihBody (cutoff + 1) (normal_lam_body normal) _ inner
  | app function argument ihFunction ihArgument =>
      intro cutoff normal target step
      rcases (show Step theory (.app (lift 1 cutoff function) (lift 1 cutoff argument)) target
          from step).app_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
      · obtain ⟨_, root'⟩ := rootStep_of_lift
          (show RootStep theory (lift 1 cutoff (.app function argument)) target from root)
        exact normal _ (Step.root root')
      · exact ihFunction cutoff (normal_app_function normal) _ inner
      · exact ihArgument cutoff (normal_app_argument normal) _ inner

theorem lift_injective {cutoff : Nat} {s t : LF.Term} (same : lift 1 cutoff s = lift 1 cutoff t) :
    s = t := by
  rw [← subst_lift_cancel s cutoff (.con "type"), same, subst_lift_cancel]

/-! ## The types of proofs of all formulas -/

/-- `eps X` is normal when `X` is, and is no application of `forall`, `impl` or
`forallP`. -/
theorem eps_app_normal {X : LF.Term} (normalX : IsNormal (Step STTfa.theory) X)
    (notForall : ∀ y z, X ≠ .app (.app (.con "forall") y) z)
    (notImpl : ∀ y z, X ≠ .app (.app (.con "impl") y) z)
    (notForallP : ∀ y, X ≠ .app (.con "forallP") y) :
    IsNormal (Step STTfa.theory) (.app (.con "eps") X) := by
  intro target step
  rcases step.app_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · obtain ⟨rule, assignment, member, shape, -⟩ := rootStep_app_con_rule root
    rcases sttfa_rules member with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [STTfa.etaDef] at shape
    · simp [STTfa.etapArrow, STTfa.etap] at shape
    · simp [STTfa.etapForall, STTfa.etap] at shape
    · simp only [STTfa.epsForall, STTfa.eps, STTfa.binary, inst_app, inst_con, inst_var,
        LF.Term.app.injEq, true_and] at shape
      exact notForall _ _ shape.symm
    · simp only [STTfa.epsImpl, STTfa.eps, STTfa.binary, inst_app, inst_con, inst_var,
        LF.Term.app.injEq, true_and] at shape
      exact notImpl _ _ shape.symm
    · simp only [STTfa.epsForallP, STTfa.eps, inst_app, inst_con, inst_var,
        LF.Term.app.injEq, true_and] at shape
      exact notForallP _ shape.symm
  · exact sttfa_con_normal (by decide) _ inner
  · exact normalX _ inner


section Shapes

variable {Base : Type u} {Const : Ty Base → Type v}
variable {e : Encoding Base Const} (names : SttfaNames e)
include names

/-- A translation applies no named symbol but a constant of the signature to
an argument. -/
theorem translateNF_app_not_named {Γ : Ctx Base} {σ τ : Ty Base} (f : Term Const Γ (.arr σ τ))
    (a : Term Const Γ σ) {s : Symbol Base Const} (notConst : ∀ (τ' : Ty Base) (c : Const τ'), s ≠ .const c)
    {y z : LF.Term} :
    e.translateNF names.base (.app f a) ≠ .app (.app (.con (e.name s)) y) z := by
  intro same
  simp only [Encoding.translateNF, LF.Term.app.injEq] at same
  obtain ⟨_, c, bad⟩ := e.translateNF_arrow_app_con names.base f s y same.1
  exact notConst _ c bad

/-- **The normal type of the proofs of a β-normal formula is normal**, in
every context. -/
theorem epsNF_normal_all : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ),
    HOL.BetaNormalization.Normal t → IsNormal (Step STTfa.theory) (e.epsNF names.base t) := by
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  intro Γ τ t
  induction t with
  | imp p q ihp ihq =>
      intro normal target step
      rcases step.pi_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
      · exact RootStep.not_pi headed root
      · exact ihp (normal_of_congr (fun x => Term.imp x q) (fun one => .impLeft q one) normal)
          _ inner
      · exact normal_lift _ 0 (ihq (normal_of_congr (fun x => Term.imp p x)
          (fun one => .impRight p one) normal)) _ inner
  | @all σ Γ b ih =>
      intro normal target step
      rcases step.pi_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
      · exact RootStep.not_pi headed root
      · exact names.hub.elNF_normal σ _ inner
      · exact ih (normal_of_congr Term.all (fun one => .all one) normal) _ inner
  | app f a _ _ =>
      intro normal
      refine eps_app_normal (names.hub.translateNF_normal _ normal) ?_ ?_ ?_
      · rw [← names.all]
        intro y z
        exact translateNF_app_not_named names f a (fun _ _ same => by cases same)
      · rw [← names.imp]
        intro y z
        exact translateNF_app_not_named names f a (fun _ _ same => by cases same)
      · intro y same
        simp only [Encoding.translateNF, LF.Term.app.injEq] at same
        cases f with
        | const c =>
            simp only [Encoding.translateNF, Encoding.sym, LF.Term.con.injEq] at same
            exact names.forallPFresh _ same.1
        | _ => simp [Encoding.translateNF] at same
  | not p _ =>
      intro normal
      refine eps_app_normal (names.hub.translateNF_normal _ normal) ?_ ?_ ?_
      · intro y z same
        simp [Encoding.translateNF, Encoding.sym] at same
      · intro y z same
        simp [Encoding.translateNF, Encoding.sym] at same
      · intro y same
        simp only [Encoding.translateNF, Encoding.sym, LF.Term.app.injEq, LF.Term.con.injEq] at same
        exact names.forallPFresh _ same.1
  | _ =>
      intro normal
      refine eps_app_normal (names.hub.translateNF_normal _ normal) ?_ ?_ ?_
      · intro y z same
        simp [Encoding.translateNF, Encoding.sym, Encoding.binary, Encoding.equation,
          Encoding.binder, ← names.all, e.name_eq_iff] at same
      · intro y z same
        simp [Encoding.translateNF, Encoding.sym, Encoding.binary, Encoding.equation,
          Encoding.binder, ← names.imp, e.name_eq_iff] at same
      · intro y same
        simp [Encoding.translateNF, Encoding.sym, Encoding.binary, Encoding.equation,
          Encoding.binder] at same

/-- The normal type of the proofs of a formula is never a computed decoding. -/
theorem epsNF_ne_elNF : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) (σ : Ty Base),
    e.epsNF names.base t ≠ Encoding.elNF names.base σ := by
  intro Γ τ t
  induction t with
  | imp p q ihp _ =>
      intro σ same
      cases σ with
      | arr σ₁ σ₂ =>
          simp only [Encoding.epsNF, Encoding.elNF, LF.Term.pi.injEq] at same
          exact ihp σ₁ same.1
      | _ => simp [Encoding.epsNF, Encoding.elNF, SttfaNames.base, SttfaNames.hub, sttfaHub] at same
  | all b ih =>
      intro σ same
      cases σ with
      | arr σ₁ σ₂ =>
          simp only [Encoding.epsNF, Encoding.elNF, LF.Term.pi.injEq] at same
          exact ih σ₂ same.2
      | _ => simp [Encoding.epsNF, Encoding.elNF, SttfaNames.base, SttfaNames.hub, sttfaHub] at same
  | _ =>
      intro σ same
      cases σ <;> simp [Encoding.epsNF, Encoding.elNF, SttfaNames.base, SttfaNames.hub,
        sttfaHub] at same

/-- **Normal types of proofs of distinct formulas differ**, in every context. -/
theorem epsNF_injective_all : ∀ {Γ : Ctx Base} {τ : Ty Base} (s t : Term Const Γ τ),
    e.epsNF names.base s = e.epsNF names.base t → s = t := by
  intro Γ τ s
  induction s with
  | imp p q ihp ihq =>
      intro t same
      cases t with
      | imp p' q' =>
          simp only [Encoding.epsNF, LF.Term.pi.injEq] at same
          rw [ihp _ same.1, ihq _ (lift_injective same.2)]
      | all b =>
          simp only [Encoding.epsNF, LF.Term.pi.injEq] at same
          exact absurd same.1 (epsNF_ne_elNF names p _)
      | _ => simp [Encoding.epsNF] at same
  | @all σ Γ b ih =>
      intro t same
      cases t with
      | @all σ' b' =>
          simp only [Encoding.epsNF, LF.Term.pi.injEq] at same
          obtain rfl := Encoding.elNF_injective names.base names.hub.elAt_injective
            names.hub.elAt_not_pi same.1
          rw [ih _ same.2]
      | imp p q =>
          simp only [Encoding.epsNF, LF.Term.pi.injEq] at same
          exact absurd same.1.symm (epsNF_ne_elNF names p _)
      | _ => simp [Encoding.epsNF] at same
  | _ =>
      intro t same
      cases t <;> first
        | (simp [Encoding.epsNF] at same; done)
        | exact eq_of_heq (e.translateNF_injective names.base names.hub.elAt_injective
            names.hub.elAt_not_pi _ _ (LF.Term.app.inj same).2).2

/-- **The type of the proofs of a formula converts with its normal type**, in
every context. -/
theorem conv_eps_epsNF : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ),
    Conv STTfa.theory (.app (.con "eps") (e.translate t)) (e.epsNF names.base t) := by
  have proofs := sttfaProofHub e names.el names.arrow names.imp names.all names.fresh
    names.typeFresh
  intro Γ τ t
  induction t with
  | imp p q ihp ihq =>
      have imp := conv_proofTheory (proofs.conv_imp (e.translate p) (e.translate q))
      exact .trans _ _ _ imp (Conv.pi ihp (ihq.lift sttfa_closedBodies 1 0))
  | @all σ Γ b ih =>
      have all := conv_proofTheory (proofs.conv_all σ (e.translate b))
      have decoding : Conv STTfa.theory (e.El (e.code σ)) (Encoding.elNF names.base σ) :=
        (names.hub.reduces_El_code σ).conv
      exact .trans _ _ _ all (Conv.pi decoding ih)
  | _ => exact Conv.app (.refl _) (names.hub.reduces_translateNF _).conv

end Shapes

/-! ## Types of proofs and types of objects -/

/-- The shape of the type of the proofs of a formula: `eps` of a proposition,
under products. -/
inductive ProofShape : LF.Term → Prop where
  | eps (proposition : LF.Term) : ProofShape (.app (.con "eps") proposition)
  | pi {domain body : LF.Term} : ProofShape body → ProofShape (.pi domain body)

theorem ProofShape.lift {t : LF.Term} (shape : ProofShape t) :
    ∀ amount cutoff : Nat, ProofShape (lift amount cutoff t) := by
  induction shape with
  | eps proposition => intro _ _; exact .eps _
  | pi _ ih => intro amount cutoff; exact .pi (ih _ _)

theorem ProofShape.not_objTree {t : LF.Term} (shape : ProofShape t) : ¬ ObjTree t := by
  induction shape with
  | eps proposition =>
      intro tree
      generalize same : LF.Term.app (.con "eps") proposition = t at tree
      cases tree <;> simp at same
  | pi _ ih =>
      intro tree
      cases tree with
      | pi _ bodyTree => exact ih bodyTree

/-- A normal type of the shape of proofs converts with no object type. -/
theorem ProofShape.not_conv_objTree {t C : LF.Term} (shape : ProofShape t)
    (normal : IsNormal (Step STTfa.theory) t) (tree : ObjTree C) : ¬ Conv STTfa.theory C t :=
  fun converted => shape.not_objTree (tree.reduces (sttfa_reduces_of_conv converted normal))

section Objects

variable {Base : Type u} {Const : Ty Base → Type v}
variable {e : Encoding Base Const} (names : SttfaNames e)
include names

theorem epsNF_proofShape : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ),
    ProofShape (e.epsNF names.base t) := by
  intro Γ τ t
  induction t with
  | imp p q _ ihq => exact .pi (ihq.lift 1 0)
  | all b ih => exact .pi ih
  | _ => exact .eps _

theorem elNF_objTree : ∀ σ : Ty Base, ObjTree (Encoding.elNF names.base σ)
  | .prop => .etap _
  | .base _ => .etap _
  | .arr σ τ => .pi (elNF_objTree σ) (elNF_objTree τ)

theorem El_objTree (code : LF.Term) : ObjTree (e.El code) := by
  simp only [Encoding.El, names.el]
  exact .eta _

end Objects

/-! ## Conversion and typing in the hub with proofs -/

theorem conv_toProofTheory {Base : Type u} {Const : Ty Base → Type v} {e : Encoding Base Const}
    {a b : LF.Term} (converted : Conv STTfa.theory a b) : Conv (sttfaProofTheory e) a b := by
  induction converted with
  | rel _ _ step =>
      exact .rel _ _ (Step.of_sameRules (theory := STTfa.theory) (theory' := sttfaProofTheory e)
        rfl rfl step)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- Conversion is a congruence in the replacement of a substitution. -/
theorem conv_subst_replacement {theory : Theory} (closed : theory.ClosedBodies) :
    ∀ (body : LF.Term) (target : Nat) {replacement replacement' : LF.Term},
      Conv theory replacement replacement' →
      Conv theory (LFTyping.subst target replacement body) (LFTyping.subst target replacement' body) := by
  intro body
  induction body with
  | srt sort => intro _ _ _ _; exact .refl _
  | con name => intro _ _ _ _; exact .refl _
  | var index =>
      intro target replacement replacement' converted
      simp only [LFTyping.subst]
      split_ifs
      · exact converted
      · exact .refl _
      · exact .refl _
  | pi domain body ihDomain ihBody =>
      intro target replacement replacement' converted
      exact Conv.pi (ihDomain target converted) (ihBody (target + 1) (converted.lift closed 1 0))
  | lam domain body ihDomain ihBody =>
      intro target replacement replacement' converted
      exact Conv.lam (ihDomain target converted) (ihBody (target + 1) (converted.lift closed 1 0))
  | app function argument ihFunction ihArgument =>
      intro target replacement replacement' converted
      exact Conv.app (ihFunction target converted) (ihArgument target converted)

theorem proofTheory_confluent {Base : Type u} {Const : Ty Base → Type v} (e : Encoding Base Const) :
    Confluent (Step (sttfaProofTheory e)) := by
  rw [step_proofTheory]
  exact STTfa.confluent

theorem proofTheory_headed {Base : Type u} {Const : Ty Base → Type v} (e : Encoding Base Const) :
    (sttfaProofTheory e).Headed :=
  fun rule member => STTfa.orthogonal.leftAlgebraic.headed rule member

/-- **Types are unique up to conversion** in the hub with proofs. -/
theorem proofTheory_unique {Base : Type u} {Const : Ty Base → Type v} {e : Encoding Base Const}
    {context : LFTyping.Ctx} {M A B : LF.Term}
    (first : LambdaPiModulo (sttfaProofTheory e) context M A)
    (second : LambdaPiModulo (sttfaProofTheory e) context M B) : Conv STTfa.theory A B :=
  conv_proofTheory (HasType.unique Example.standardLF_functional (proofTheory_confluent e)
    (proofTheory_headed e) (sttfaProofTheory_closedBodies e) M first second)

section Typing

variable {Base : Type u} {Const : Ty Base → Type v}
variable {e : Encoding Base Const} (names : SttfaNames e)
include names

/-- The hub with proofs declares the encoding. -/
theorem proofTheory_declares : Declares e (sttfaProofTheory e) "type" :=
  (sttfaProofHub e names.el names.arrow names.imp names.all names.fresh names.typeFresh).toDeclares

theorem constType_etap : (sttfaProofTheory e).constType "etap" = some (.pi (.con "ptype") (.srt .type)) := by
  rw [sttfaProofTheory_constType_extra e (fun s => (names.fresh s).2.1) (by decide)
    (by rw [names.el]; decide)]
  simp [sttfaProofTypes]

theorem constType_p : (sttfaProofTheory e).constType "p" = some (.pi (.con "type") (.con "ptype")) := by
  rw [sttfaProofTheory_constType_extra e (fun s => (names.pFresh s).1) (by decide)
    (by rw [names.el]; decide)]
  simp [sttfaProofTypes]

/-- **The computed decoding of a type is a type** of the hub with proofs. -/
theorem elNF_typed : ∀ (σ : Ty Base) {context : LFTyping.Ctx},
    LambdaPiModulo (sttfaProofTheory e) context (Encoding.elNF names.base σ) (.srt .type) := by
  have declares := proofTheory_declares names
  have named : ∀ (s : Symbol Base Const), e.declaredType (.con "type") s = .con "type" →
      ∀ {context : LFTyping.Ctx},
        LambdaPiModulo (sttfaProofTheory e) context (names.base s) (.srt .type) := by
    intro s declared context
    have symTyped := declares.sym_typed (Γ := context) s
    rw [declared] at symTyped
    have pApplied := HasType.app (.con (constType_p names)) symTyped
    have etapApplied := HasType.app (.con (constType_etap names)) pApplied
    simpa [SttfaNames.base, SttfaNames.hub, sttfaHub, subst0, LFTyping.subst, Encoding.sym]
      using etapApplied
  intro σ
  induction σ with
  | prop => intro context; exact named .bool rfl
  | base b => intro context; exact named (.sort b) rfl
  | arr σ τ ihσ ihτ => intro context; exact .pi ihσ ihτ arrow_rule

theorem El_conv_elNF (σ : Ty Base) :
    Conv STTfa.theory (e.El (e.code σ)) (Encoding.elNF names.base σ) :=
  (names.hub.reduces_El_code σ).conv

/-- An abstraction over the computed decoding of a type has the decoding of the
code of the function type. -/
theorem lamNF_typed {σ τ : Ty Base} {context : LFTyping.Ctx} {body : LF.Term}
    (bodyTyped : LambdaPiModulo (sttfaProofTheory e) (Encoding.elNF names.base σ :: context) body
      (e.El (e.code τ))) :
    LambdaPiModulo (sttfaProofTheory e) context (.lam (Encoding.elNF names.base σ) body)
      (e.El (e.code (.arr σ τ))) := by
  have declares := proofTheory_declares names
  have converted : Conv STTfa.theory (.pi (Encoding.elNF names.base σ) (e.El (e.code τ)))
      (e.El (e.code (.arr σ τ))) :=
    .symm _ _ (.trans _ _ _ (conv_proofTheory (declares.conv_El_arr σ τ))
      (Conv.pi (El_conv_elNF names σ) (.refl _)))
  exact .conv (.lam (elNF_typed names σ) (declares.El_code_typed τ) arrow_rule bodyTyped)
    (conv_toProofTheory converted) (declares.El_code_typed _)

end Typing

/-! ## The coding of proofs and the contexts of hypotheses -/

section Coding

variable {Base : Type u} {Const : Ty Base → Type v}
variable {e : Encoding Base Const} (names : SttfaNames e)

/-- **The coding of proofs.**  A hypothesis is a variable at a position that
holds no object.  An abstraction binds a hypothesis, at a type of the shape of
the types of proofs, or an object, at the computed decoding of its type.  An
application applies a proof to a proof, or to the translation, with computed
domains, of a core HOL term placed among the variables: its ∀-witness.  The
renaming `ρ` places the objects of the HOL context `Γ` among the variables of
the framework, which `Θ` lists, with `prop` for a hypothesis. -/
inductive Coded : {Γ Θ : Ctx Base} → HOL.Rename Base Γ Θ → LF.Term → Prop
  | hyp {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {index : Nat} :
      (∀ {σ : Ty Base} (v : Var Γ σ), varIndex (ρ v) ≠ index) → Coded ρ (.var index)
  | lamHyp {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {domain body : LF.Term} :
      ProofShape domain →
      Coded (Θ := .prop :: Θ) (fun v => .vs (ρ v)) body → Coded ρ (.lam domain body)
  | lamObj {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} (σ : Ty Base) {body : LF.Term} :
      Coded (HOL.Rename.lift (σ := σ) ρ) body →
      Coded ρ (.lam (Encoding.elNF names.base σ) body)
  | appProof {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {function argument : LF.Term} :
      Coded ρ function → Coded ρ argument → Coded ρ (.app function argument)
  | appObj {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {function : LF.Term} {σ : Ty Base}
      (witness : Term Const Γ σ) : witness.isCore = true → Coded ρ function →
      Coded ρ (.app function (e.translateNF names.base (HOL.rename ρ witness)))

/-- **A context of hypotheses with objects.**  The renaming `ρ` is injective;
each object sits at its place, at a type converting with the decoding of its
type; every other variable is a hypothesis, at a type converting with the type
of the proofs of the placed translation of one of the hypotheses `Δ`, which
are core. -/
structure Scoped (e : Encoding Base Const) {Γ Θ : Ctx Base} (ρ : HOL.Rename Base Γ Θ)
    (Δ : List (Formula Const Γ)) (context : LFTyping.Ctx) : Prop where
  injective : ∀ {σ : Ty Base} (v w : Var Γ σ), ρ v = ρ w → v = w
  objects : ∀ {σ : Ty Base} (v : Var Γ σ), ∃ X, LFTyping.ctxLookup context (varIndex (ρ v)) = some X ∧
    Conv STTfa.theory X (e.El (e.code σ))
  hyps : ∀ (index : Nat) (X : LF.Term), (∀ {σ : Ty Base} (v : Var Γ σ), varIndex (ρ v) ≠ index) →
    LFTyping.ctxLookup context index = some X →
      ∃ j : Fin Δ.length, Conv STTfa.theory X (.app (.con "eps") (e.translate (HOL.rename ρ (Δ.get j))))
  core : ∀ δ ∈ Δ, δ.isCore = true

end Coding

/-! ## Extending contexts of hypotheses -/

theorem translate_rename_vs {Base : Type u} {Const : Ty Base → Type v} (e : Encoding Base Const)
    {Γ Θ : Ctx Base} {σ τ : Ty Base} (ρ : HOL.Rename Base Γ Θ) (t : Term Const Γ τ) :
    e.translate (HOL.rename (Δ := σ :: Θ) (fun v => .vs (ρ v)) t) =
      lift 1 0 (e.translate (HOL.rename ρ t)) := by
  rw [← e.translate_weaken (σ := σ), HOL.rename_comp]
  rfl

/-- A hypothesis extends a context of hypotheses. -/
theorem Scoped.extendHyp {Base : Type u} {Const : Ty Base → Type v} {e : Encoding Base Const}
    {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {Δ : List (Formula Const Γ)}
    {context : LFTyping.Ctx} (placed : Scoped e ρ Δ context) {domain : LF.Term}
    {p : Formula Const Γ} (coreP : p.isCore = true)
    (converted : Conv STTfa.theory domain (.app (.con "eps") (e.translate (HOL.rename ρ p)))) :
    Scoped e (Θ := .prop :: Θ) (fun v => .vs (ρ v)) (p :: Δ) (domain :: context) where
  injective v w same := placed.injective v w (HOL.Var.vs.inj same)
  objects {σ} v := by
    obtain ⟨X, found, convX⟩ := placed.objects v
    refine ⟨lift 1 0 X, ?_, ?_⟩
    · show LFTyping.ctxLookup (domain :: context) (varIndex (ρ v) + 1) = _
      rw [lookup_cons_succ, found]
      rfl
    · have lifted := convX.lift sttfa_closedBodies 1 0
      rwa [(e.El_code_closed σ).lift] at lifted
  hyps index X notObject found := by
    cases index with
    | zero =>
        rw [lookup_cons_zero] at found
        cases found
        refine ⟨⟨0, by simp⟩, ?_⟩
        have lifted := converted.lift sttfa_closedBodies 1 0
        simp only [LFTyping.lift] at lifted
        rw [← translate_rename_vs e (σ := .prop) ρ p] at lifted
        exact lifted
    | succ index =>
        rw [lookup_cons_succ] at found
        obtain ⟨prior, priorFound, rfl⟩ := Option.map_eq_some_iff.mp found
        have notPrior : ∀ {σ : Ty Base} (v : Var Γ σ), varIndex (ρ v) ≠ index :=
          fun v same => notObject v (by simp [varIndex, same])
        obtain ⟨j, convPrior⟩ := placed.hyps index prior notPrior priorFound
        refine ⟨j.succ, ?_⟩
        have lifted := convPrior.lift sttfa_closedBodies 1 0
        simp only [LFTyping.lift] at lifted
        rw [← translate_rename_vs e (σ := .prop) ρ (Δ.get j)] at lifted
        simpa using lifted
  core δ member := by
    rcases List.mem_cons.mp member with rfl | member
    · exact coreP
    · exact placed.core δ member

section Extend

variable {Base : Type u} {Const : Ty Base → Type v}
variable {e : Encoding Base Const} (names : SttfaNames e)
include names

/-- An object extends a context of hypotheses, which weakens the hypotheses. -/
theorem Scoped.extendObj {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {Δ : List (Formula Const Γ)}
    {context : LFTyping.Ctx} (placed : Scoped e ρ Δ context) (σ : Ty Base) :
    Scoped e (HOL.Rename.lift (σ := σ) ρ) (HOL.weakenHyps (σ := σ) Δ)
      (Encoding.elNF names.base σ :: context) where
  injective v w same := HOL.Rename.lift_injective placed.injective v w same
  objects {τ} v := by
    cases v with
    | vz =>
        refine ⟨Encoding.elNF names.base σ, ?_, .symm _ _ (El_conv_elNF names σ)⟩
        show LFTyping.ctxLookup (Encoding.elNF names.base σ :: context) 0 = _
        rw [lookup_cons_zero, (Encoding.elNF_closed names.base_closed σ).lift]
    | vs w =>
        obtain ⟨X, found, convX⟩ := placed.objects w
        refine ⟨lift 1 0 X, ?_, ?_⟩
        · show LFTyping.ctxLookup (Encoding.elNF names.base σ :: context) (varIndex (ρ w) + 1) = _
          rw [lookup_cons_succ, found]
          rfl
        · have lifted := convX.lift sttfa_closedBodies 1 0
          rwa [(e.El_code_closed τ).lift] at lifted
  hyps index X notObject found := by
    cases index with
    | zero => exact absurd rfl (notObject .vz)
    | succ index =>
        rw [lookup_cons_succ] at found
        obtain ⟨prior, priorFound, rfl⟩ := Option.map_eq_some_iff.mp found
        have notPrior : ∀ {τ : Ty Base} (v : Var Γ τ), varIndex (ρ v) ≠ index :=
          fun v same => notObject (.vs v) (by simp [HOL.Rename.lift, varIndex, same])
        obtain ⟨j, convPrior⟩ := placed.hyps index prior notPrior priorFound
        refine ⟨j.cast (by simp [HOL.weakenHyps]), ?_⟩
        have member : (HOL.weakenHyps (σ := σ) Δ).get (j.cast (by simp [HOL.weakenHyps])) =
            HOL.weaken (Δ.get j) := by
          obtain ⟨n, bound⟩ := j
          simp only [HOL.weakenHyps, List.get_eq_getElem, List.getElem_map]
          rfl
        rw [member, HOL.ExtDerivation.rename_weaken, HOL.weaken, e.translate_weaken]
        have lifted := convPrior.lift sttfa_closedBodies 1 0
        simp only [LFTyping.lift] at lifted
        exact lifted
  core δ member := by
    simp only [HOL.weakenHyps, List.mem_map] at member
    obtain ⟨δ', member', rfl⟩ := member
    rw [HOL.weaken, HOL.Term.isCore_rename]
    exact placed.core δ' member'

/-- **A placed translation with computed domains has the decoding of the code of
its type.** -/
theorem translateNF_typed_scoped : ∀ {Γ : Ctx Base} {σ : Ty Base} (t : Term Const Γ σ)
    {Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {Δ : List (Formula Const Γ)} {context : LFTyping.Ctx},
    Scoped e ρ Δ context →
      LambdaPiModulo (sttfaProofTheory e) context (e.translateNF names.base (HOL.rename ρ t))
        (e.El (e.code σ)) := by
  have declares := proofTheory_declares names
  intro Γ σ t
  induction t with
  | var v =>
      intro Θ ρ Δ context placed
      obtain ⟨X, found, convX⟩ := placed.objects v
      exact .conv (.var found) (conv_toProofTheory convX) (declares.El_code_typed _)
  | const c => intro Θ ρ Δ context _; exact declares.sym_typed (.const c)
  | app f a ihf iha =>
      intro Θ ρ Δ context placed
      exact declares.apply_typed (ihf placed) (iha placed)
  | @lam σ Γ τ body ih =>
      intro Θ ρ Δ context placed
      exact lamNF_typed names (ih (placed.extendObj names σ))
  | top => intro Θ ρ Δ context _; exact declares.sym_typed .top
  | bot => intro Θ ρ Δ context _; exact declares.sym_typed .bot
  | and p q ihp ihq =>
      intro Θ ρ Δ context placed
      exact declares.apply_typed (σ := .prop)
        (declares.apply_typed (σ := .prop) (declares.sym_typed .and) (ihp placed)) (ihq placed)
  | or p q ihp ihq =>
      intro Θ ρ Δ context placed
      exact declares.apply_typed (σ := .prop)
        (declares.apply_typed (σ := .prop) (declares.sym_typed .or) (ihp placed)) (ihq placed)
  | imp p q ihp ihq =>
      intro Θ ρ Δ context placed
      exact declares.apply_typed (σ := .prop)
        (declares.apply_typed (σ := .prop) (declares.sym_typed .imp) (ihp placed)) (ihq placed)
  | not p ih =>
      intro Θ ρ Δ context placed
      exact declares.apply_typed (σ := .prop) (declares.sym_typed .not) (ih placed)
  | @eq Γ τ l r ihl ihr =>
      intro Θ ρ Δ context placed
      exact declares.apply_typed (declares.apply_typed (declares.eq_typed τ) (ihl placed)) (ihr placed)
  | @all σ Γ body ih =>
      intro Θ ρ Δ context placed
      exact declares.apply_typed (declares.quantifier_typed (s := .all) rfl σ)
        (lamNF_typed names (ih (placed.extendObj names σ)))
  | @ex σ Γ body ih =>
      intro Θ ρ Δ context placed
      exact declares.apply_typed (declares.quantifier_typed (s := .ex) rfl σ)
        (lamNF_typed names (ih (placed.extendObj names σ)))

end Extend

/-! ## Adequacy -/

theorem betaConv_of_reducesStar {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {τ : Ty Base} {s t : Term Const Γ τ} (reduces : HOL.BetaNormalization.ReducesStar s t) :
    BetaConv s t := by
  induction reduces with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ step)

/-- A type that converts with no object type. -/
def NoObject (A : LF.Term) : Prop := ∀ C, ObjTree C → ¬ Conv STTfa.theory A C

section Adequacy

variable {Base : Type u} {Const : Ty Base → Type v}
variable {e : Encoding Base Const} (names : SttfaNames e)
include names

/-- The type of the proofs of a placed formula converts with the normal type of
the proofs of its placed normal form. -/
theorem eps_conv_normalForm {Γ Θ : Ctx Base} (ρ : HOL.Rename Base Γ Θ) (φ : Formula Const Γ)
    {n : Formula Const Γ} (toN : HOL.BetaNormalization.ReducesStar φ n) :
    Conv STTfa.theory (.app (.con "eps") (e.translate (HOL.rename ρ φ)))
      (e.epsNF names.base (HOL.rename ρ n)) :=
  .trans _ _ _
    (Conv.app (.refl _) (Encoding.translate_conv
      (betaConv_of_reducesStar (HOL.BetaNormalization.star_rename ρ toN))))
    (conv_eps_epsNF names (HOL.rename ρ n))

/-- **Proofs move between formulas whose placed proof types convert**: they
have one normal form, and the checker converts core formulas along it. -/
theorem transfer {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ}
    (injective : ∀ {σ : Ty Base} (v w : Var Γ σ), ρ v = ρ w → v = w)
    {Δ : List (Formula Const Γ)} {ψ φ : Formula Const Γ} (coreψ : ψ.isCore = true)
    (coreφ : φ.isCore = true) {A : LF.Term}
    (convψ : Conv STTfa.theory A (.app (.con "eps") (e.translate (HOL.rename ρ ψ))))
    (convφ : Conv STTfa.theory A (.app (.con "eps") (e.translate (HOL.rename ρ φ))))
    (proof : Nonempty (HOL.ProofSyntaxModulo [] Δ ψ)) :
    Nonempty (HOL.ProofSyntaxModulo [] Δ φ) := by
  obtain ⟨nψ, toψ, normalψ⟩ := exists_normalForm ψ
  obtain ⟨nφ, toφ, normalφ⟩ := exists_normalForm φ
  have same : e.epsNF names.base (HOL.rename ρ nψ) = e.epsNF names.base (HOL.rename ρ nφ) :=
    sttfa_normal_conv_eq
      (epsNF_normal_all names _ (HOL.BetaNormalization.normal_rename ρ normalψ))
      (epsNF_normal_all names _ (HOL.BetaNormalization.normal_rename ρ normalφ))
      (.trans _ _ _ (.symm _ _ (eps_conv_normalForm names ρ ψ toψ))
        (.trans _ _ _ (.symm _ _ convψ) (.trans _ _ _ convφ (eps_conv_normalForm names ρ φ toφ))))
  have sameN : nψ = nφ :=
    HOL.rename_injective ρ injective _ _ (epsNF_injective_all names _ _ same)
  subst sameN
  obtain ⟨d⟩ := proof
  exact ⟨.convert (HOL.CoreConversion.of_normalForm toψ toφ coreψ coreφ) d⟩

/-- The type of the proofs of a placed formula converts with no object type. -/
theorem eps_not_conv_objTree {Γ Θ : Ctx Base} (ρ : HOL.Rename Base Γ Θ) (φ : Formula Const Γ)
    {A C : LF.Term} (convφ : Conv STTfa.theory A (.app (.con "eps") (e.translate (HOL.rename ρ φ))))
    (tree : ObjTree C) : ¬ Conv STTfa.theory A C := by
  intro convC
  obtain ⟨n, toN, normalN⟩ := exists_normalForm φ
  exact (epsNF_proofShape names (HOL.rename ρ n)).not_conv_objTree
    (epsNF_normal_all names _ (HOL.BetaNormalization.normal_rename ρ normalN)) tree
    (.trans _ _ _ (.symm _ _ convC) (.trans _ _ _ convφ (eps_conv_normalForm names ρ φ toN)))

/-- Every reading of a type as the type of the proofs of a placed core formula
is proved. -/
def ProvesAll (e : Encoding Base Const) {Γ Θ : Ctx Base} (ρ : HOL.Rename Base Γ Θ)
    (Δ : List (Formula Const Γ)) (A : LF.Term) : Prop :=
  ∀ φ : Formula Const Γ, φ.isCore = true →
    Conv STTfa.theory A (.app (.con "eps") (e.translate (HOL.rename ρ φ))) →
      Nonempty (HOL.ProofSyntaxModulo [] Δ φ)

/-- A type is the type of the proofs of a placed core formula that is proved. -/
def NeutralAll (e : Encoding Base Const) {Γ Θ : Ctx Base} (ρ : HOL.Rename Base Γ Θ)
    (Δ : List (Formula Const Γ)) (A : LF.Term) : Prop :=
  ∃ ψ : Formula Const Γ, ψ.isCore = true ∧
    Conv STTfa.theory A (.app (.con "eps") (e.translate (HOL.rename ρ ψ))) ∧
      Nonempty (HOL.ProofSyntaxModulo [] Δ ψ)

theorem of_neutral {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {Δ : List (Formula Const Γ)}
    {context : LFTyping.Ctx} (placed : Scoped e ρ Δ context) {A : LF.Term}
    (neutral : NeutralAll e ρ Δ A) : ProvesAll e ρ Δ A ∧ NoObject A := by
  obtain ⟨ψ, coreψ, convψ, proof⟩ := neutral
  exact ⟨fun φ coreφ convφ => transfer names placed.injective coreψ coreφ convψ convφ proof,
    fun C tree => eps_not_conv_objTree names ρ ψ convψ tree⟩

/-- **The induction of adequacy.**  For a coded normal term typed in a context
of hypotheses with objects: every reading of its type as the type of the proofs
of a placed core formula is proved; when it is not an abstraction, its type is
the type of the proofs of a placed core formula that it proves; and its type
converts with no object type. -/
theorem adequacy_coded : ∀ {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} {M : LF.Term},
    Coded names (@ρ) M → ∀ {Δ : List (Formula Const Γ)} {context : LFTyping.Ctx} {A : LF.Term},
    Scoped e ρ Δ context → IsNormal (Step STTfa.theory) M →
    LambdaPiModulo (sttfaProofTheory e) context M A →
    ProvesAll e ρ Δ A ∧ ((∀ domain body, M ≠ .lam domain body) → NeutralAll e ρ Δ A) ∧
      NoObject A := by
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  intro Γ Θ ρ M coded
  induction coded with
  | @hyp Γ Θ ρ index notObject =>
      intro Δ context A placed normal typed
      have neutral : NeutralAll e ρ Δ A := by
        obtain ⟨X, found, converted⟩ := typed.var_inv
        obtain ⟨j, convX⟩ := placed.hyps index X notObject found
        exact ⟨Δ.get j, placed.core _ (List.get_mem _ _),
          .trans _ _ _ (.symm _ _ (conv_proofTheory converted)) convX, ⟨.hyp j⟩⟩
      obtain ⟨proves, noObject⟩ := of_neutral names placed neutral
      exact ⟨proves, fun _ => neutral, noObject⟩
  | @lamHyp Γ Θ ρ domain body shape _ ih =>
      intro Δ context A placed normal typed
      obtain ⟨bodyType, _, _, _, _, _, _, bodyTyped, typeConv⟩ := typed.lam_inv
      have typeConv' := conv_proofTheory typeConv
      have domainNormal := normal_lam_domain normal
      refine ⟨?_, fun notLam => absurd rfl (notLam domain body), ?_⟩
      · intro φ coreφ convφ
        obtain ⟨n, toN, normalN⟩ := exists_normalForm φ
        have coreN := HOL.Term.isCore_of_reducesStar toN coreφ
        have back := HOL.CoreConversion.of_reducesStar toN coreφ
        have toNF := sttfa_reduces_of_conv
          (.trans _ _ _ typeConv' (.trans _ _ _ convφ (eps_conv_normalForm names ρ φ toN)))
          (epsNF_normal_all names _ (HOL.BetaNormalization.normal_rename ρ normalN))
        obtain ⟨domain', bodyType', shapeNF, domainReduces, bodyReduces⟩ := toNF.pi_inv headed
        have domainEq := domainNormal.reflTransGen_eq domainReduces
        cases n with
        | imp p q =>
            simp only [HOL.rename, Encoding.epsNF, LF.Term.pi.injEq] at shapeNF
            obtain ⟨domainIs, bodyIs⟩ := shapeNF
            have domainIs' := domainIs.trans domainEq
            simp only [HOL.Term.isCore, Bool.and_eq_true] at coreN
            have placed' := placed.extendHyp (domain := domain) coreN.1 (by
              rw [← domainIs']
              exact .symm _ _ (conv_eps_epsNF names (HOL.rename ρ p)))
            have bodyConv : Conv STTfa.theory bodyType
                (.app (.con "eps") (e.translate (HOL.rename (Δ := .prop :: Θ)
                  (fun v => .vs (ρ v)) q))) := by
              rw [translate_rename_vs e ρ q]
              have lifted := Conv.lift sttfa_closedBodies
                (Relation.EqvGen.symm _ _ (conv_eps_epsNF names (HOL.rename ρ q))) 1 0
              simp only [LFTyping.lift] at lifted
              rw [bodyIs] at lifted
              exact .trans _ _ _ bodyReduces.conv lifted
            obtain ⟨proof⟩ := (ih placed' (normal_lam_body normal) bodyTyped).1 q coreN.2 bodyConv
            exact ⟨.convert (.symm _ _ back) (.impI proof)⟩
        | @all σ _ b =>
            simp only [HOL.rename, Encoding.epsNF, LF.Term.pi.injEq] at shapeNF
            obtain ⟨domainIs, _⟩ := shapeNF
            have tree := elNF_objTree names σ
            rw [domainIs.trans domainEq] at tree
            exact absurd tree shape.not_objTree
        | _ => simp [HOL.rename, Encoding.epsNF] at shapeNF
      · intro C tree convC
        obtain ⟨common, toCommon, fromC⟩ :=
          (conv_iff_joinable STTfa.confluent).mp (.trans _ _ _ typeConv' convC)
        obtain ⟨domain', bodyType', rfl, domainReduces, _⟩ := toCommon.pi_inv headed
        have domainEq := domainNormal.reflTransGen_eq domainReduces
        subst domainEq
        cases tree.reduces fromC with
        | pi domainTree _ => exact shape.not_objTree domainTree
  | @lamObj Γ Θ ρ σ body _ ih =>
      intro Δ context A placed normal typed
      obtain ⟨bodyType, _, _, _, _, _, _, bodyTyped, typeConv⟩ := typed.lam_inv
      have typeConv' := conv_proofTheory typeConv
      have bodyFacts := ih (placed.extendObj names σ) (normal_lam_body normal) bodyTyped
      refine ⟨?_, fun notLam => absurd rfl (notLam _ body), ?_⟩
      · intro φ coreφ convφ
        obtain ⟨n, toN, normalN⟩ := exists_normalForm φ
        have coreN := HOL.Term.isCore_of_reducesStar toN coreφ
        have back := HOL.CoreConversion.of_reducesStar toN coreφ
        have toNF := sttfa_reduces_of_conv
          (.trans _ _ _ typeConv' (.trans _ _ _ convφ (eps_conv_normalForm names ρ φ toN)))
          (epsNF_normal_all names _ (HOL.BetaNormalization.normal_rename ρ normalN))
        obtain ⟨domain', bodyType', shapeNF, domainReduces, bodyReduces⟩ := toNF.pi_inv headed
        have domainEq := (normal_lam_domain normal).reflTransGen_eq domainReduces
        subst domainEq
        cases n with
        | @all σ' _ b =>
            simp only [HOL.rename, Encoding.epsNF, LF.Term.pi.injEq] at shapeNF
            obtain ⟨domainIs, bodyIs⟩ := shapeNF
            obtain rfl := Encoding.elNF_injective names.base names.hub.elAt_injective
              names.hub.elAt_not_pi domainIs
            simp only [HOL.Term.isCore] at coreN
            have bodyConv := Relation.EqvGen.symm _ _
              (conv_eps_epsNF names (HOL.rename (HOL.Rename.lift ρ) b))
            rw [bodyIs] at bodyConv
            obtain ⟨proof⟩ := bodyFacts.1 b coreN (.trans _ _ _ bodyReduces.conv bodyConv)
            exact ⟨.convert (.symm _ _ back) (.allI proof)⟩
        | imp p q =>
            simp only [HOL.rename, Encoding.epsNF, LF.Term.pi.injEq] at shapeNF
            exact absurd shapeNF.1 (epsNF_ne_elNF names _ σ)
        | _ => simp [HOL.rename, Encoding.epsNF] at shapeNF
      · intro C tree convC
        obtain ⟨common, toCommon, fromC⟩ :=
          (conv_iff_joinable STTfa.confluent).mp (.trans _ _ _ typeConv' convC)
        obtain ⟨domain', bodyType', rfl, _, bodyReduces⟩ := toCommon.pi_inv headed
        exact bodyFacts.2.2 _ (tree.reduces fromC).pi_body bodyReduces.conv
  | @appProof Γ Θ ρ function argument _ _ ihFunction ihArgument =>
      intro Δ context A placed normal typed
      have notLam : ∀ domain body, function ≠ .lam domain body := by
        rintro domain body rfl
        exact normal _ (Step.root (.beta domain body argument))
      obtain ⟨domain, bodyType, functionTyped, argumentTyped, typeConv⟩ := typed.app_inv
      have argumentFacts := ihArgument placed (normal_app_argument normal) argumentTyped
      have neutral : NeutralAll e ρ Δ A := by
        obtain ⟨ψ, coreψ, convψ, ⟨proofψ⟩⟩ :=
          (ihFunction placed (normal_app_function normal) functionTyped).2.1 notLam
        obtain ⟨n, toN, normalN⟩ := exists_normalForm ψ
        have coreN := HOL.Term.isCore_of_reducesStar toN coreψ
        have forth := HOL.CoreConversion.of_reducesStar toN coreψ
        have toNF := sttfa_reduces_of_conv (.trans _ _ _ convψ (eps_conv_normalForm names ρ ψ toN))
          (epsNF_normal_all names _ (HOL.BetaNormalization.normal_rename ρ normalN))
        obtain ⟨domain', bodyType', shapeNF, domainReduces, bodyReduces⟩ := toNF.pi_inv headed
        cases n with
        | imp p q =>
            simp only [HOL.rename, Encoding.epsNF, LF.Term.pi.injEq] at shapeNF
            obtain ⟨domainIs, bodyIs⟩ := shapeNF
            subst domainIs bodyIs
            simp only [HOL.Term.isCore, Bool.and_eq_true] at coreN
            obtain ⟨proofP⟩ := argumentFacts.1 p coreN.1
              (.trans _ _ _ domainReduces.conv (.symm _ _ (conv_eps_epsNF names _)))
            refine ⟨q, coreN.2, ?_, ⟨.impE (.convert forth proofψ) proofP⟩⟩
            have substituted := Conv.subst sttfa_closedBodies bodyReduces.conv 0 argument
            rw [subst_lift_cancel] at substituted
            exact .trans _ _ _ (.symm _ _ (conv_proofTheory typeConv))
              (.trans _ _ _ substituted (.symm _ _ (conv_eps_epsNF names _)))
        | @all σ _ b =>
            simp only [HOL.rename, Encoding.epsNF, LF.Term.pi.injEq] at shapeNF
            obtain ⟨domainIs, _⟩ := shapeNF
            subst domainIs
            exact absurd domainReduces.conv (argumentFacts.2.2 _ (elNF_objTree names σ))
        | _ => simp [HOL.rename, Encoding.epsNF] at shapeNF
      obtain ⟨proves, noObject⟩ := of_neutral names placed neutral
      exact ⟨proves, fun _ => neutral, noObject⟩
  | @appObj Γ Θ ρ function σw witness coreW _ ihFunction =>
      intro Δ context A placed normal typed
      have notLam : ∀ domain body, function ≠ .lam domain body := by
        rintro domain body rfl
        exact normal _ (Step.root (.beta domain body _))
      obtain ⟨domain, bodyType, functionTyped, argumentTyped, typeConv⟩ := typed.app_inv
      have domainConv : Conv STTfa.theory domain (e.El (e.code σw)) :=
        proofTheory_unique argumentTyped (translateNF_typed_scoped names witness placed)
      have neutral : NeutralAll e ρ Δ A := by
        obtain ⟨ψ, coreψ, convψ, ⟨proofψ⟩⟩ :=
          (ihFunction placed (normal_app_function normal) functionTyped).2.1 notLam
        obtain ⟨n, toN, normalN⟩ := exists_normalForm ψ
        have coreN := HOL.Term.isCore_of_reducesStar toN coreψ
        have forth := HOL.CoreConversion.of_reducesStar toN coreψ
        have toNF := sttfa_reduces_of_conv (.trans _ _ _ convψ (eps_conv_normalForm names ρ ψ toN))
          (epsNF_normal_all names _ (HOL.BetaNormalization.normal_rename ρ normalN))
        obtain ⟨domain', bodyType', shapeNF, domainReduces, bodyReduces⟩ := toNF.pi_inv headed
        cases n with
        | imp p q =>
            simp only [HOL.rename, Encoding.epsNF, LF.Term.pi.injEq] at shapeNF
            obtain ⟨domainIs, _⟩ := shapeNF
            subst domainIs
            have pNormal : HOL.BetaNormalization.Normal (HOL.rename ρ p) :=
              normal_of_congr (fun x => HOL.Term.imp x (HOL.rename ρ q)) (fun one => .impLeft _ one)
                (HOL.BetaNormalization.normal_rename ρ normalN)
            exact absurd (.trans _ _ _ (.symm _ _ domainConv) domainReduces.conv)
              ((epsNF_proofShape names _).not_conv_objTree (epsNF_normal_all names _ pNormal)
                (El_objTree names _))
        | @all σ _ b =>
            simp only [HOL.rename, Encoding.epsNF, LF.Term.pi.injEq] at shapeNF
            obtain ⟨domainIs, bodyIs⟩ := shapeNF
            subst domainIs bodyIs
            have sameDecoding : Encoding.elNF names.base σw = Encoding.elNF names.base σ :=
              sttfa_normal_conv_eq (names.hub.elNF_normal σw) (names.hub.elNF_normal σ)
                (.trans _ _ _ (.symm _ _ (El_conv_elNF names σw))
                  (.trans _ _ _ (.symm _ _ domainConv) domainReduces.conv))
            obtain rfl := Encoding.elNF_injective names.base names.hub.elAt_injective
              names.hub.elAt_not_pi sameDecoding
            simp only [HOL.Term.isCore] at coreN
            refine ⟨HOL.instantiate witness b, HOL.Term.isCore_instantiate coreW coreN, ?_,
              ⟨.allE witness (.convert forth proofψ)⟩⟩
            have substituted := Conv.subst sttfa_closedBodies
              (.trans _ _ _ bodyReduces.conv
                (.symm _ _ (conv_eps_epsNF names (HOL.rename (HOL.Rename.lift ρ) b)))) 0
              (e.translateNF names.base (HOL.rename ρ witness))
            have replaced := conv_subst_replacement sttfa_closedBodies
              (e.translate (HOL.rename (HOL.Rename.lift ρ) b)) 0
              (Relation.EqvGen.symm _ _ (names.hub.reduces_translateNF (HOL.rename ρ witness)).conv)
            have shape : LFTyping.subst 0 (e.translate (HOL.rename ρ witness))
                (e.translate (HOL.rename (HOL.Rename.lift ρ) b)) =
                e.translate (HOL.rename ρ (HOL.instantiate witness b)) := by
              rw [HOL.ExtDerivation.rename_instantiate, e.translate_instantiate]
              rfl
            rw [shape] at replaced
            exact .trans _ _ _ (.symm _ _ (conv_proofTheory typeConv))
              (.trans _ _ _ substituted (Conv.app (.refl _) replaced))
        | _ => simp [HOL.rename, Encoding.epsNF] at shapeNF
      obtain ⟨proves, noObject⟩ := of_neutral names placed neutral
      exact ⟨proves, fun _ => neutral, noObject⟩

end Adequacy

/-! ## The theorems -/

theorem exists_var_of_lt {Base : Type u} : ∀ {Γ : Ctx Base} {index : Nat}, index < Γ.length →
    ∃ (σ : Ty Base) (v : Var Γ σ), varIndex v = index
  | [], _, bound => absurd bound (Nat.not_lt_zero _)
  | σ :: _, 0, _ => ⟨σ, .vz, rfl⟩
  | _ :: Γ, index + 1, bound => by
      obtain ⟨σ, v, same⟩ := exists_var_of_lt (Γ := Γ) (Nat.lt_of_succ_lt_succ bound)
      exact ⟨σ, .vs v, by simp [varIndex, same]⟩

/-- The decodings of the types of a HOL context form a context of objects. -/
theorem scoped_objects {Base : Type u} {Const : Ty Base → Type v} (e : Encoding Base Const)
    (Γ : Ctx Base) : Scoped e (HOL.Rename.id (Γ := Γ)) ([] : List (Formula Const Γ)) (e.ctx Γ) where
  injective v w same := same
  objects v := ⟨_, e.ctxLookup_var v, .refl _⟩
  hyps index X notObject found := by
    rw [ctxLookup_eq_getElem?] at found
    have bound : index < Γ.length := by
      cases lookup : (e.ctx Γ)[index]? with
      | none => rw [lookup] at found; cases found
      | some _ =>
          have := (List.getElem?_eq_some_iff.mp lookup).1
          simpa [Encoding.ctx] using this
    obtain ⟨σ, v, same⟩ := exists_var_of_lt bound
    exact absurd same (notObject v)
  core _ member := absurd member List.not_mem_nil

/-- The types of the proofs of closed core hypotheses form a context of
hypotheses. -/
theorem scoped_hypotheses {Base : Type u} {Const : Ty Base → Type v} (e : Encoding Base Const)
    {Δ : List (Formula Const [])} (core : ∀ δ ∈ Δ, δ.isCore = true) :
    Scoped e (HOL.Rename.id (Γ := [])) Δ (Δ.map fun δ => .app (.con "eps") (e.translate δ)) where
  injective v := nomatch v
  objects v := nomatch v
  hyps index X _ found := by
    rw [ctxLookup_eq_getElem?, List.getElem?_map] at found
    cases lookup : Δ[index]? with
    | none => rw [lookup] at found; cases found
    | some δ =>
        rw [lookup] at found
        simp only [Option.map_some, Option.some.injEq] at found
        obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp lookup
        refine ⟨⟨index, bound⟩, ?_⟩
        have closedEntry : Closed (LF.Term.app (.con "eps") (e.translate δ)) :=
          .app .con (e.translate_wellScoped δ)
        rw [← found, closedEntry.lift, HOL.rename_id]
        simp [same]
        exact .refl _
  core := core

section Theorems

variable {Base : Type u} {Const : Ty Base → Type v}
variable {e : Encoding Base Const} (names : SttfaNames e)
include names

/-- **Adequacy of the STTfa hub with universal quantification, modulo the
coding of witnesses**: a coded normal term of the type of the proofs of a
closed core formula, in the context of the types of the proofs of closed core
hypotheses, gives a proof of the formula from the hypotheses. -/
theorem sttfa_adequate_coded {Δ : List (Formula Const [])} (core : ∀ δ ∈ Δ, δ.isCore = true)
    {φ : Formula Const []} (coreφ : φ.isCore = true) {M : LF.Term}
    (coded : Coded names (HOL.Rename.id (Γ := [])) M)
    (normal : IsNormal (Step (sttfaProofTheory e)) M)
    (typed : LambdaPiModulo (sttfaProofTheory e)
      (Δ.map fun δ => .app (.con "eps") (e.translate δ)) M (.app (.con "eps") (e.translate φ))) :
    Nonempty (HOL.ProofSyntaxModulo [] Δ φ) := by
  rw [step_proofTheory] at normal
  refine (adequacy_coded names coded (scoped_hypotheses e core) normal typed).1 φ coreφ ?_
  rw [HOL.rename_id]
  exact .refl _

/-- **Adequacy for formulas with free objects**: a coded normal term of the
type of the proofs of a core formula, in the context of the decodings of its
objects, gives a proof of the formula. -/
theorem sttfa_adequate_coded_open {Γ : Ctx Base} {φ : Formula Const Γ} (coreφ : φ.isCore = true)
    {M : LF.Term} (coded : Coded names (HOL.Rename.id (Γ := Γ)) M)
    (normal : IsNormal (Step (sttfaProofTheory e)) M)
    (typed : LambdaPiModulo (sttfaProofTheory e) (e.ctx Γ) M (.app (.con "eps") (e.translate φ))) :
    Nonempty (HOL.ProofSyntaxModulo [] [] φ) := by
  rw [step_proofTheory] at normal
  refine (adequacy_coded names coded (scoped_objects e Γ) normal typed).1 φ coreφ ?_
  rw [HOL.rename_id]
  exact .refl _

end Theorems

/-! ## Controls -/

theorem predVar_normal : HOL.BetaNormalization.Normal predVar := by
  rintro target ⟨step⟩
  cases step with
  | appFun _ inner => cases inner
  | appArg _ inner => cases inner

/-- The normal type of the proofs of `pred x`, for the newest object `x`. -/
abbrev predVarProofs : LF.Term := sttfaControl.epsNF sttfaControl_names.base predVar

/-- **The normal proof of `∀ x. pred x ⇒ pred x`**: `λ x. λ h. h`. -/
def predSelfTerm : LF.Term :=
  .lam (Encoding.elNF sttfaControl_names.base ι) (.lam predVarProofs (.var 0))

theorem predSelfTerm_coded : Coded sttfaControl_names (HOL.Rename.id (Γ := [])) predSelfTerm :=
  .lamObj ι (.lamHyp (.eps _) (.hyp fun v same => by
    cases v with
    | vz => simp [HOL.Rename.lift, varIndex] at same
    | vs w => exact nomatch w))

theorem predSelfTerm_normal : IsNormal (Step (sttfaProofTheory sttfaControl)) predSelfTerm := by
  rw [step_proofTheory]
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  intro target step
  rcases step.lam_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · exact RootStep.not_lam headed root
  · exact sttfaControl_names.hub.elNF_normal ι _ inner
  · rcases inner.lam_inv with root | ⟨_, inner', _⟩ | ⟨_, inner', _⟩
    · exact RootStep.not_lam headed root
    · exact epsNF_normal_all sttfaControl_names predVar predVar_normal _ inner'
    · exact var_normal headed _ _ inner'

theorem predSelfTerm_typed :
    LambdaPiModulo (sttfaProofTheory sttfaControl) [] predSelfTerm
      (.app (.con "eps") (sttfaControl.translate (.all (.imp predVar predVar)))) := by
  have names := sttfaControl_names
  have declares := proofTheory_declares names
  have objects := (scoped_objects sttfaControl []).extendObj names ι
  have hypothesis := objects.extendHyp (domain := predVarProofs) (p := predVar) rfl
    (.symm _ _ (conv_eps_epsNF names (HOL.rename (HOL.Rename.lift HOL.Rename.id) predVar)))
  have firstTyped := translateNF_typed_scoped names predVar objects
  have secondTyped := translateNF_typed_scoped names predVar hypothesis
  have innerTyped : LambdaPiModulo (sttfaProofTheory sttfaControl)
      [Encoding.elNF names.base ι] (.lam predVarProofs (.var 0))
      (.pi predVarProofs (lift 1 0 predVarProofs)) :=
    .lam (sttfaControlProofs.proof_typed firstTyped) (sttfaControlProofs.proof_typed secondTyped)
      arrow_rule (.var (lookup_cons_zero _ _))
  have outerTyped := HasType.lam (elNF_typed names ι)
    (.pi (sttfaControlProofs.proof_typed firstTyped) (sttfaControlProofs.proof_typed secondTyped)
      arrow_rule) arrow_rule innerTyped
  have converted := conv_eps_epsNF names (.all (.imp predVar predVar) : Formula ControlConst [])
  exact .conv outerTyped (conv_toProofTheory (.symm _ _ converted))
    (sttfaControlProofs.proof_typed (declares.translate_typed (Γ := []) _))

/-- **Adequacy at a universal introduction**: the normal `λ x. λ h. h` gives
back a proof of `∀ x. pred x ⇒ pred x`. -/
theorem predSelf_adequate :
    Nonempty (HOL.ProofSyntaxModulo [] ([] : List (Formula ControlConst []))
      (.all (.imp predVar predVar))) :=
  sttfa_adequate_coded sttfaControl_names (Δ := []) (fun _ member => absurd member List.not_mem_nil)
    rfl predSelfTerm_coded predSelfTerm_normal predSelfTerm_typed

/-- The normal type of the proofs of `∀ x. pred x`. -/
abbrev predAllProofs : LF.Term :=
  sttfaControl.epsNF sttfaControl_names.base (.all predVar : Formula ControlConst [])

/-- **The normal proof of `(∀ x. pred x) ⇒ pred point`**: `λ h. h point`, whose
∀-witness `point` is the translation of a HOL term. -/
def predInstanceTerm : LF.Term := .lam predAllProofs (.app (.var 0) (.con "point"))

theorem predInstanceTerm_coded :
    Coded sttfaControl_names (HOL.Rename.id (Γ := [])) predInstanceTerm :=
  .lamHyp (.pi (.eps _)) (.appObj (.const ControlConst.point) rfl (.hyp fun v => nomatch v))

theorem predInstanceTerm_normal :
    IsNormal (Step (sttfaProofTheory sttfaControl)) predInstanceTerm := by
  rw [step_proofTheory]
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  have allNormal : HOL.BetaNormalization.Normal (.all predVar : Formula ControlConst []) :=
    fun target ⟨step⟩ => by
      cases step with
      | all inner => exact predVar_normal _ ⟨inner⟩
  intro target step
  rcases step.lam_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · exact RootStep.not_lam headed root
  · exact epsNF_normal_all sttfaControl_names _ allNormal _ inner
  · rcases inner.app_inv with root | ⟨_, inner', _⟩ | ⟨_, inner', _⟩
    · rcases root.headConst_or_beta headed with ⟨_, _, _, same⟩ | ⟨_, head⟩
      · cases same
      · simp [headConst] at head
    · exact var_normal headed _ _ inner'
    · exact sttfa_con_normal (by decide) _ inner'

theorem predInstanceTerm_typed :
    LambdaPiModulo (sttfaProofTheory sttfaControl) [] predInstanceTerm
      (.app (.con "eps") (sttfaControl.translate (.imp (.all predVar) predPoint))) := by
  have names := sttfaControl_names
  have declares := proofTheory_declares names
  have objects := (scoped_objects sttfaControl []).extendObj names ι
  have firstTyped := translateNF_typed_scoped names predVar objects
  have allTyped : LambdaPiModulo (sttfaProofTheory sttfaControl) [] predAllProofs (.srt .type) :=
    .pi (elNF_typed names ι) (sttfaControlProofs.proof_typed firstTyped) arrow_rule
  have closedAll : Closed predAllProofs := sttfaControl.epsNF_closed names.base_closed _
  have headTyped : LambdaPiModulo (sttfaProofTheory sttfaControl) [predAllProofs] (.var 0)
      predAllProofs := .var (by rw [lookup_cons_zero, closedAll.lift])
  have pointTyped : LambdaPiModulo (sttfaProofTheory sttfaControl) [predAllProofs] (.con "point")
      (Encoding.elNF names.base ι) :=
    .conv (declares.sym_typed (.const .point)) (conv_toProofTheory (El_conv_elNF names ι))
      (elNF_typed names ι)
  have applied := HasType.app headTyped pointTyped
  have shape : subst0 (.con "point") predVarProofs = predPointProofs := rfl
  rw [shape] at applied
  have formulaTyped : ∀ {context : LFTyping.Ctx}, LambdaPiModulo (sttfaProofTheory sttfaControl)
      context (sttfaControl.translate predPoint) (sttfaControl.El (sttfaControl.code .prop)) :=
    declares.apply_typed (declares.sym_typed (.const .pred)) (declares.sym_typed (.const .point))
  have lamTyped := HasType.lam allTyped (sttfaControlProofs.proof_typed formulaTyped) arrow_rule
    applied
  have converted := conv_eps_epsNF names (.imp (.all predVar) predPoint : Formula ControlConst [])
  rw [sttfaControl.epsNF_imp names.base_closed] at converted
  exact .conv lamTyped (conv_toProofTheory (.symm _ _ converted))
    (sttfaControlProofs.proof_typed (declares.translate_typed (Γ := []) _))

/-- **Adequacy at a universal elimination**: the normal `λ h. h point` gives
back a proof of `(∀ x. pred x) ⇒ pred point`. -/
theorem predInstance_adequate :
    Nonempty (HOL.ProofSyntaxModulo [] ([] : List (Formula ControlConst []))
      (.imp (.all predVar) predPoint)) :=
  sttfa_adequate_coded sttfaControl_names (Δ := []) (fun _ member => absurd member List.not_mem_nil)
    rfl predInstanceTerm_coded predInstanceTerm_normal predInstanceTerm_typed

/-- **The normal proof of `pred x ⇒ pred x`**, with `x` free: `λ h. h`. -/
def predOpenTerm : LF.Term := .lam predVarProofs (.var 0)

theorem predOpenTerm_coded : Coded sttfaControl_names (HOL.Rename.id (Γ := [ι])) predOpenTerm :=
  .lamHyp (.eps _) (.hyp fun v same => by
    cases v with
    | vz => simp [HOL.Rename.id, varIndex] at same
    | vs w => exact nomatch w)

theorem predOpenTerm_normal : IsNormal (Step (sttfaProofTheory sttfaControl)) predOpenTerm := by
  rw [step_proofTheory]
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  intro target step
  rcases step.lam_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · exact RootStep.not_lam headed root
  · exact epsNF_normal_all sttfaControl_names predVar predVar_normal _ inner
  · exact var_normal headed _ _ inner

theorem predOpenTerm_typed :
    LambdaPiModulo (sttfaProofTheory sttfaControl) (sttfaControl.ctx [ι]) predOpenTerm
      (.app (.con "eps") (sttfaControl.translate (.imp predVar predVar))) := by
  have names := sttfaControl_names
  have declares := proofTheory_declares names
  have objects := scoped_objects sttfaControl [ι]
  have hypothesis := objects.extendHyp (domain := predVarProofs) (p := predVar) rfl
    (.symm _ _ (conv_eps_epsNF names (HOL.rename HOL.Rename.id predVar)))
  have firstTyped := translateNF_typed_scoped names predVar objects
  have secondTyped := translateNF_typed_scoped names predVar hypothesis
  have lamTyped : LambdaPiModulo (sttfaProofTheory sttfaControl) (sttfaControl.ctx [ι])
      predOpenTerm (.pi predVarProofs (lift 1 0 predVarProofs)) :=
    .lam (sttfaControlProofs.proof_typed firstTyped) (sttfaControlProofs.proof_typed secondTyped)
      arrow_rule (.var (lookup_cons_zero _ _))
  exact .conv lamTyped (conv_toProofTheory (.symm _ _ (conv_eps_epsNF names (.imp predVar predVar))))
    (sttfaControlProofs.proof_typed (declares.translate_typed _))

/-- **Adequacy with a free object**: the normal `λ h. h` gives back a proof of
`pred x ⇒ pred x` in the context `x : ι`. -/
theorem predOpen_adequate :
    Nonempty (HOL.ProofSyntaxModulo [] ([] : List (Formula ControlConst [ι]))
      (.imp predVar predVar)) :=
  sttfa_adequate_coded_open sttfaControl_names rfl predOpenTerm_coded predOpenTerm_normal
    predOpenTerm_typed

/-- A translation with computed domains is a constant only for a constant of
the signature, `⊤` or `⊥`. -/
theorem translateNF_eq_con {Base : Type u} {Const : Ty Base → Type v} (e : Encoding Base Const)
    (base : Symbol Base Const → LF.Term) {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ)
    {name : String} (same : e.translateNF base t = .con name) :
    (∃ (τ' : Ty Base) (c : Const τ'), name = e.name (.const c)) ∨ name = e.name .top ∨
      name = e.name .bot := by
  cases t with
  | const c => exact Or.inl ⟨_, c, (LF.Term.con.inj same).symm⟩
  | top => exact Or.inr (Or.inl (LF.Term.con.inj same).symm)
  | bot => exact Or.inr (Or.inr (LF.Term.con.inj same).symm)
  | _ => simp [Encoding.translateNF, Encoding.sym, Encoding.binary, Encoding.equation,
      Encoding.binder] at same

/-- A coded term is no constant. -/
theorem not_coded_con {Base : Type u} {Const : Ty Base → Type v} {e : Encoding Base Const}
    (names : SttfaNames e) {Γ Θ : Ctx Base} {ρ : HOL.Rename Base Γ Θ} (name : String) :
    ¬ Coded names (@ρ) (.con name) := by
  intro coded
  generalize sameTerm : LF.Term.con name = t at coded
  cases coded <;> simp at sameTerm

/-- **The coding excludes the bare `and`**: the normal inhabitant `h and` of
the type of the proofs of `pred point`, in the context of the proofs of
`∀ f. pred point`, is coded for no placement of objects. -/
theorem andWitnessTerm_not_coded {Γ Θ : Ctx Unit} {ρ : HOL.Rename Unit Γ Θ} :
    ¬ Coded sttfaControl_names (@ρ) andWitnessTerm := by
  intro coded
  generalize sameTerm : andWitnessTerm = t at coded
  cases coded with
  | appProof _ codedArgument =>
      simp only [andWitnessTerm, LF.Term.app.injEq] at sameTerm
      obtain ⟨-, rfl⟩ := sameTerm
      exact not_coded_con sttfaControl_names _ codedArgument
  | appObj witness _ _ =>
      simp only [andWitnessTerm, LF.Term.app.injEq] at sameTerm
      rcases translateNF_eq_con sttfaControl _ _ sameTerm.2.symm with ⟨_, c, named⟩ |
        named | named
      · cases c <;> simp [sttfaControl, controlEncoding, controlName] at named
      · simp [sttfaControl, controlEncoding, controlName] at named
      · simp [sttfaControl, controlEncoding, controlName] at named
  | _ => simp [andWitnessTerm] at sameTerm

/-- **The coding is needed**: the witness of `sttfa_not_exactly_adequate` is a
normal term of the type of the proofs of `pred point`, in the context of the
proofs of `∀ f. pred point`, and it is not coded. -/
theorem sttfa_coding_needed :
    IsNormal (Step (sttfaProofTheory sttfaControl)) andWitnessTerm ∧
      LambdaPiModulo (sttfaProofTheory sttfaControl)
        [.app (.con "eps") (sttfaControl.translate andWitnessFormula)] andWitnessTerm
        predPointProofs ∧
      ¬ Coded sttfaControl_names (HOL.Rename.id (Γ := [])) andWitnessTerm :=
  ⟨andWitnessTerm_normal, andWitnessTerm_typed, andWitnessTerm_not_coded⟩

#print axioms normal_lift
#print axioms epsNF_normal_all
#print axioms epsNF_injective_all
#print axioms translateNF_typed_scoped
#print axioms adequacy_coded
#print axioms sttfa_adequate_coded
#print axioms sttfa_adequate_coded_open
#print axioms predSelf_adequate
#print axioms predInstance_adequate
#print axioms predOpen_adequate
#print axioms sttfa_coding_needed

end Mettapedia.GSLT.Dedukti.HOLHub
