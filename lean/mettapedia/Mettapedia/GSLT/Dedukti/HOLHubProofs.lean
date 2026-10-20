import Mettapedia.GSLT.Dedukti.HOLHubTyping
import Mettapedia.Logic.HOL.ProofSyntaxModulo

/-!
# HOL proofs as terms of the STTfa hub

The STTfa hub decodes a proposition `p` as the type `eps p` of its proofs, with
the rules `eps (impl p q) ↪ eps p → eps q` and
`eps (forall a f) ↪ Π x : eta a. eps (f x)`.  So a natural-deduction proof of
implication and universal quantification is a λ-term.  This module compiles
the proofs of `Logic.HOL.ProofSyntaxModulo` with no defining equation (rules
for `⇒` and `∀`, and retyping along β-conversion) into λ-terms and proves them
typed at `eps` of the translation of their conclusions.

**Layouts** (`Layout`).  A proof brings objects (∀-introduction) and
hypotheses (⇒-introduction) into scope in any order, the newest innermost.  A
layout records that order.  Its context (`Layout.lfCtx`) declares each object
at the decoding of its type and each hypothesis at `eps` of its translation,
and `Layout.place` moves a translation over the objects into that context, past
the hypotheses.  Typing and conversion move along (`Layout.typed_place`,
`Layout.conv_place`), and placement commutes with substitution and with
weakening (`Layout.place_subst0`, `Layout.place_lift`).

**The compiler** (`compile`).  A hypothesis is its variable, ⇒-introduction is
an abstraction over a proof of the premise, ∀-introduction an abstraction over
the decoding of the quantified type, both eliminations are applications, and a
retyping step emits no term.

**Results.**

* `ProofHub.compile_typed`: every compiled proof is typed, in the context of
  its layout, at `eps` of the placed translation of its conclusion.
* `ProofHub.theorem_typed`: a proof with no hypothesis compiles to a term of
  `eps` of the translation of its conclusion, in the context of the
  decodings of the objects: **every theorem of this proof system is inhabited
  in the hub**.
* `sttfaProofHub`: the STTfa hub, with the declarations of Logipedia's theory
  file and the signature declared, is a theory of proofs for every encoding
  that names `⇒` `impl` and `∀` `forall`.

**Scope.**  The proof system is `ProofSyntaxModulo []`: hypotheses,
introduction and elimination of `⇒` and `∀`, and retyping along β-conversion
between core formulas.  The converse is `HOLHubAdequacy`.

An earlier version declared, beyond the encoding, only
`eps : eta bool → Type`.  It left `ptype`, `p`, `etap`, `forallK` and `forallP`
undeclared, so the right side `λ t. etap (p t)` of the definition of `eta` was
not typed, and the decoding `eta c` of a code, a type, reduced to a term that
is not typed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.HOLHub

open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 lookupBody)
open Mettapedia.Logic.HOL (Ty Ctx Var Term Formula)
open Mettapedia.Logic.HOL.ContextualTrinity (BetaStep)

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Contexts -/

theorem lookup_cons_zero (entry : LF.Term) (context : LFTyping.Ctx) :
    LFTyping.ctxLookup (entry :: context) 0 = some (lift 1 0 entry) := rfl

theorem lookup_cons_succ (entry : LF.Term) (context : LFTyping.Ctx) (index : Nat) :
    LFTyping.ctxLookup (entry :: context) (index + 1) =
      (LFTyping.ctxLookup context index).map (lift 1 0) := by
  rw [ctxLookup_eq_getElem?, ctxLookup_eq_getElem?]
  cases found : context[index]? with
  | none => simp [found]
  | some value =>
      simp only [List.getElem?_cons_succ, found, Option.map_some]
      rw [lift_lift_same]
      congr 2
      omega

theorem liftCtx_of_closed : ∀ {front : LFTyping.Ctx}, (∀ entry ∈ front, Closed entry) →
    liftCtx front = front
  | [], _ => rfl
  | head :: tail, closed => by
      simp only [liftCtx]
      rw [(closed head List.mem_cons_self).lift, liftCtx_of_closed fun entry member =>
        closed entry (List.mem_cons_of_mem _ member)]

/-! ## Layouts -/

/-- The order in which a proof brings objects and hypotheses into scope, above
a context of objects, the newest innermost. -/
inductive Layout (Const : Ty Base → Type v) : Ctx Base → Type (max u v) where
  | base (Γ : Ctx Base) : Layout Const Γ
  | obj {Γ : Ctx Base} (rest : Layout Const Γ) (σ : Ty Base) : Layout Const (σ :: Γ)
  | hyp {Γ : Ctx Base} (rest : Layout Const Γ) (δ : Formula Const Γ) : Layout Const Γ

namespace Layout

/-- Move a term over the objects of a layout, below `k` local binders, into the
context of the layout: past every hypothesis. -/
def place : {Γ : Ctx Base} → Layout Const Γ → Nat → LF.Term → LF.Term
  | _, .base _, _, t => t
  | _, .obj rest _, k, t => rest.place (k + 1) t
  | _, .hyp rest _, k, t => lift 1 k (rest.place k t)

/-- The context of a layout: an object at the decoding of its type, a
hypothesis at the type of its proofs. -/
def lfCtx (e : Encoding Base Const) (proof : String) :
    {Γ : Ctx Base} → Layout Const Γ → LFTyping.Ctx
  | _, .base Γ => e.ctx Γ
  | _, .obj rest σ => e.El (e.code σ) :: rest.lfCtx e proof
  | _, .hyp rest δ => .app (.con proof) (rest.place 0 (e.translate δ)) :: rest.lfCtx e proof

variable {Γ : Ctx Base}

theorem place_app (L : Layout Const Γ) : ∀ (k : Nat) (f a : LF.Term),
    L.place k (.app f a) = .app (L.place k f) (L.place k a) := by
  induction L with
  | base _ => intro k f a; rfl
  | obj rest _ ih => intro k f a; exact ih (k + 1) f a
  | hyp rest _ ih => intro k f a; simp only [place, ih, LFTyping.lift]

theorem place_lam (L : Layout Const Γ) : ∀ (k : Nat) (domain body : LF.Term),
    L.place k (.lam domain body) = .lam (L.place k domain) (L.place (k + 1) body) := by
  induction L with
  | base _ => intro k domain body; rfl
  | obj rest _ ih => intro k domain body; exact ih (k + 1) domain body
  | hyp rest _ ih => intro k domain body; simp only [place, ih, LFTyping.lift]

theorem place_closed (L : Layout Const Γ) {t : LF.Term} (closed : Closed t) :
    ∀ k : Nat, L.place k t = t := by
  induction L with
  | base _ => intro k; rfl
  | obj rest _ ih => intro k; exact ih (k + 1)
  | hyp rest _ ih => intro k; simp only [place, ih, closed.lift]

/-- Placement commutes with opening the newest local binder. -/
theorem place_subst0 (L : Layout Const Γ) : ∀ (k : Nat) (argument body : LF.Term),
    L.place k (subst0 argument body) = subst0 (L.place k argument) (L.place (k + 1) body) := by
  induction L with
  | base _ => intro k argument body; rfl
  | obj rest _ ih => intro k argument body; exact ih (k + 1) argument body
  | hyp rest _ ih =>
      intro k argument body
      simp only [place]
      rw [ih, lift_subst0]

/-- Placement commutes with weakening below the cutoff. -/
theorem place_lift (L : Layout Const Γ) : ∀ (k j : Nat), j ≤ k → ∀ u : LF.Term,
    L.place (k + 1) (lift 1 j u) = lift 1 j (L.place k u) := by
  induction L with
  | base _ => intro k j _ u; rfl
  | obj rest _ ih => intro k j below u; exact ih (k + 1) j (Nat.le_succ_of_le below) u
  | hyp rest _ ih =>
      intro k j below u
      simp only [place]
      rw [ih k j below u, lift_lift _ 1 1 j k below]

/-- Conversion moves along placement. -/
theorem conv_place {theory : Theory} (closedBodies : theory.ClosedBodies) (L : Layout Const Γ) :
    ∀ {k : Nat} {a b : LF.Term}, Conv theory a b → Conv theory (L.place k a) (L.place k b) := by
  induction L with
  | base _ => intro k a b converted; exact converted
  | obj rest _ ih => intro k a b converted; exact ih converted
  | hyp rest _ ih => intro k a b converted; exact (ih converted).lift closedBodies 1 k

/-- **Typing moves along placement**, below any front of closed entries. -/
theorem typed_place {theory : Theory} (closedBodies : theory.ClosedBodies)
    (closedTypes : theory.ClosedTypes) (e : Encoding Base Const) (proof : String)
    (L : Layout Const Γ) :
    ∀ (front : LFTyping.Ctx), (∀ entry ∈ front, Closed entry) → ∀ {u U : LF.Term}, Closed U →
      LambdaPiModulo theory (front ++ e.ctx Γ) u U →
      LambdaPiModulo theory (front ++ L.lfCtx e proof) (L.place front.length u) U := by
  induction L with
  | base _ => intro front _ u U _ typed; exact typed
  | @obj Γ rest σ ih =>
      intro front closedFront u U closedU typed
      have typed' : LambdaPiModulo theory ((front ++ [e.El (e.code σ)]) ++ e.ctx Γ) u U := by
        simpa [Encoding.ctx, List.append_assoc] using typed
      have closedFront' : ∀ entry ∈ front ++ [e.El (e.code σ)], Closed entry := by
        intro entry member
        rcases List.mem_append.mp member with inFront | inLast
        · exact closedFront entry inFront
        · rw [List.mem_singleton.mp inLast]; exact e.El_code_closed σ
      have result := ih (front ++ [e.El (e.code σ)]) closedFront' closedU typed'
      simpa [lfCtx, place, List.append_assoc] using result
  | @hyp Γ rest δ ih =>
      intro front closedFront u U closedU typed
      have inner := ih front closedFront closedU typed
      have weakened := inner.weaken_at closedBodies closedTypes (rest.lfCtx e proof)
        (.app (.con proof) (rest.place 0 (e.translate δ))) front rfl
      rw [liftCtx_of_closed closedFront, closedU.lift] at weakened
      exact weakened

theorem place_binary (e : Encoding Base Const) (L : Layout Const Γ) (s : Symbol Base Const) (a b : LF.Term) :
    L.place 0 (e.binary s a b) = e.binary s (L.place 0 a) (L.place 0 b) := by
  simp only [Encoding.binary, Layout.place_app, L.place_closed (t := e.sym s) .con]

theorem place_binder (e : Encoding Base Const) (L : Layout Const Γ) (s : Symbol Base Const) (σ : Ty Base)
    (body : LF.Term) :
    L.place 0 (e.binder s σ (e.El (e.code σ)) body) =
      e.binder s σ (e.El (e.code σ)) (L.place 1 body) := by
  simp only [Encoding.binder, Layout.place_app, Layout.place_lam,
    L.place_closed (t := e.sym s) .con, L.place_closed (e.code_closed σ),
    L.place_closed (e.El_code_closed σ)]

end Layout

/-! ## The rules of proofs -/

namespace Encoding

variable (e : Encoding Base Const)

/-- `eps (imp p q) ↪ eps p → eps q`, with `proof` for `eps`. -/
def impRule (proof : String) : RewriteRule :=
  ⟨.app (.con proof) (e.binary .imp (.var 1) (.var 0)),
    .pi (.app (.con proof) (.var 1)) (.app (.con proof) (.var 1))⟩

/-- `eps (all a f) ↪ Π x : El a. eps (f x)`, with `proof` for `eps`. -/
def allRule (proof : String) : RewriteRule :=
  ⟨.app (.con proof) (e.binary .all (.var 1) (.var 0)),
    .pi (e.El (.var 1)) (.app (.con proof) (.app (.var 1) (.var 0)))⟩

end Encoding

/-- A theory of proofs for an encoding: it declares the encoding over `codes`,
declares `proof : El bool → Type`, has the rules of `⇒` and `∀` for `proof`, and
has closed definitions and declared types. -/
structure ProofHub (e : Encoding Base Const) (theory : Theory) (codes proof : String) : Prop
    extends Declares e theory codes where
  closedBodies : theory.ClosedBodies
  closedTypes : theory.ClosedTypes
  proof_type : theory.constType proof = some (.pi (e.El (e.sym .bool)) (.srt .type))
  impRule : theory.rule (e.impRule proof)
  allRule : theory.rule (e.allRule proof)

/-- **The compiler**: a hypothesis is its variable, an introduction an
abstraction, an elimination an application, and a retyping step nothing. -/
def compile (e : Encoding Base Const) (proof : String) :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} → {φ : Formula Const Γ} →
    HOL.ProofSyntaxModulo [] Δ φ → Layout Const Γ → (Fin Δ.length → Nat) → LF.Term
  | _, _, _, .hyp occurrence, _, hypVar => .var (hypVar occurrence)
  | _, _, _, .impI (φ := premise) body, L, hypVar =>
      .lam (.app (.con proof) (L.place 0 (e.translate premise)))
        (compile e proof body (L.hyp premise) (Fin.cases 0 fun i => hypVar i + 1))
  | _, _, _, .impE function argument, L, hypVar =>
      .app (compile e proof function L hypVar) (compile e proof argument L hypVar)
  | _, _, _, .allI (σ := σ) body, L, hypVar =>
      .lam (e.El (e.code σ))
        (compile e proof body (L.obj σ) fun i =>
          hypVar (i.cast (by simp [HOL.weakenHyps])) + 1)
  | _, _, _, .allE t function, L, hypVar =>
      .app (compile e proof function L hypVar) (L.place 0 (e.translate t))
  | _, _, _, .convert _ inner, L, hypVar => compile e proof inner L hypVar

/-- A definitional step of the source with no defining equation is a β-step. -/
theorem betaStep_of_sourceStep {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (step : HOL.SourceStep [] s t) : SourceStep s t := by
  induction step with
  | beta body argument => exact ⟨.beta body argument⟩
  | delta _ listed _ _ => exact absurd listed List.not_mem_nil
  | appFun argument _ ih => exact ih.elim fun one => ⟨.appFun argument one⟩
  | appArg function _ ih => exact ih.elim fun one => ⟨.appArg function one⟩
  | lam _ ih => exact ih.elim fun one => ⟨.lam one⟩
  | impLeft right _ ih => exact ih.elim fun one => ⟨.impLeft right one⟩
  | impRight left _ ih => exact ih.elim fun one => ⟨.impRight left one⟩
  | eqLeft right _ ih => exact ih.elim fun one => ⟨.eqLeft right one⟩
  | eqRight left _ ih => exact ih.elim fun one => ⟨.eqRight left one⟩
  | all _ ih => exact ih.elim fun one => ⟨.all one⟩

/-- A conversion article with no defining equation is a β-conversion. -/
theorem betaConv_of_coreConversion {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ}
    (conversion : HOL.CoreConversion [] s t) : BetaConv s t := by
  induction conversion with
  | rel _ _ step => exact .rel _ _ (betaStep_of_sourceStep step.2.2)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

namespace ProofHub

variable {e : Encoding Base Const} {theory : Theory} {codes proof : String}
variable (p : ProofHub e theory codes proof)
include p

theorem conv_imp (P Q : LF.Term) :
    Conv theory (.app (.con proof) (e.binary .imp P Q))
      (.pi (.app (.con proof) P) (.app (.con proof) (lift 1 0 Q))) := by
  have instance_ := Conv.rule (theory := theory) (rule := e.impRule proof) p.impRule
    fun index => if index = 0 then Q else P
  simpa [Encoding.impRule, Encoding.binary, Encoding.sym, inst, Dedukti.instantiate,
    Mettapedia.GSLT.Dedukti.lift_zero] using instance_

theorem conv_all (σ : Ty Base) (body : LF.Term) :
    Conv theory (.app (.con proof) (e.binder .all σ (e.El (e.code σ)) body))
      (.pi (e.El (e.code σ)) (.app (.con proof) body)) := by
  have instance_ := Conv.rule (theory := theory) (rule := e.allRule proof) p.allRule
    fun index => if index = 0 then .lam (e.El (e.code σ)) body else e.code σ
  have closedCode := (e.code_closed σ).lift 1 0
  have shaped : Conv theory (.app (.con proof) (e.binder .all σ (e.El (e.code σ)) body))
      (.pi (e.El (e.code σ))
        (.app (.con proof) (.app (.lam (e.El (e.code σ)) (lift 1 1 body)) (.var 0)))) := by
    simpa [Encoding.allRule, Encoding.binary, Encoding.binder, Encoding.sym, Encoding.El, inst,
      Dedukti.instantiate, Mettapedia.GSLT.Dedukti.lift_zero, LFTyping.lift, closedCode] using instance_
  have beta := Conv.beta (theory := theory) (e.El (e.code σ)) (lift 1 1 body) (.var 0)
  rw [subst0_var_lift] at beta
  exact .trans _ _ _ shaped (Conv.pi (.refl _) (Conv.app (.refl _) beta))

theorem proof_typed {Γ : LFTyping.Ctx} {c : LF.Term}
    (typed : LambdaPiModulo theory Γ c (e.El (e.code .prop))) :
    LambdaPiModulo theory Γ (.app (.con proof) c) (.srt .type) :=
  .app (.con p.proof_type) typed

/-- A translation placed in the context of a layout keeps its type. -/
theorem placed_typed {Γ : Ctx Base} (L : Layout Const Γ) {τ : Ty Base} (t : Term Const Γ τ) :
    LambdaPiModulo theory (L.lfCtx e proof) (L.place 0 (e.translate t)) (e.El (e.code τ)) :=
  L.typed_place p.closedBodies p.closedTypes e proof [] (by simp) (e.El_code_closed τ)
    (p.toDeclares.translate_typed t)

theorem placed_proof_typed {Γ : Ctx Base} (L : Layout Const Γ) (φ : Formula Const Γ) :
    LambdaPiModulo theory (L.lfCtx e proof) (.app (.con proof) (L.place 0 (e.translate φ)))
      (.srt .type) :=
  p.proof_typed (p.placed_typed L φ)

/-- **Every compiled proof is typed**, in the context of its layout, at the
type of the proofs of its conclusion. -/
theorem compile_typed : ∀ {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (d : HOL.ProofSyntaxModulo [] Δ φ) (L : Layout Const Γ) (hypVar : Fin Δ.length → Nat),
    (∀ i, LFTyping.ctxLookup (L.lfCtx e proof) (hypVar i) =
      some (.app (.con proof) (L.place 0 (e.translate (Δ.get i))))) →
    LambdaPiModulo theory (L.lfCtx e proof) (compile e proof d L hypVar)
      (.app (.con proof) (L.place 0 (e.translate φ))) := by
  intro Γ Δ φ d
  induction d with
  | hyp occurrence =>
      intro L hypVar hyps
      exact .var (hyps occurrence)
  | @impI Γ Δ premise conclusion body ih =>
      intro L hypVar hyps
      have bodyTyped := ih (L.hyp premise) (Fin.cases 0 fun i => hypVar i + 1) (by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [Layout.lfCtx, Layout.place, lookup_cons_zero, LFTyping.lift]
        · simp only [Fin.cases_succ, Layout.lfCtx]
          rw [lookup_cons_succ, hyps j]
          simp [Layout.place, LFTyping.lift])
      have lamTyped := HasType.lam (p.placed_proof_typed L premise)
        (p.placed_proof_typed (L.hyp premise) conclusion) arrow_rule bodyTyped
      have goal : Conv theory (.pi (.app (.con proof) (L.place 0 (e.translate premise)))
          (.app (.con proof) ((L.hyp premise).place 0 (e.translate conclusion))))
          (.app (.con proof) (L.place 0 (e.translate (.imp premise conclusion)))) := by
        rw [show e.translate (.imp premise conclusion) =
          e.binary .imp (e.translate premise) (e.translate conclusion) from rfl, L.place_binary e]
        exact .symm _ _ (p.conv_imp _ _)
      exact .conv lamTyped goal (p.placed_proof_typed L _)
  | @impE Γ Δ premise conclusion function argument ihFunction ihArgument =>
      intro L hypVar hyps
      have functionTyped := ihFunction L hypVar hyps
      rw [show e.translate (.imp premise conclusion) =
        e.binary .imp (e.translate premise) (e.translate conclusion) from rfl,
        L.place_binary e] at functionTyped
      have asFunction := HasType.conv functionTyped (p.conv_imp _ _)
        (.pi (p.placed_proof_typed L premise)
          (p.placed_proof_typed (L.hyp premise) conclusion) arrow_rule)
      have applied := HasType.app asFunction (ihArgument L hypVar hyps)
      rwa [show subst0 (compile e proof argument L hypVar)
          (.app (.con proof) (lift 1 0 (L.place 0 (e.translate conclusion)))) =
          .app (.con proof) (L.place 0 (e.translate conclusion)) by
        simp [subst0, LFTyping.subst, subst_lift_cancel]] at applied
  | @allI Γ Δ σ body inner ih =>
      intro L hypVar hyps
      have bodyTyped := ih (L.obj σ) (fun i => hypVar (i.cast (by simp [HOL.weakenHyps])) + 1) (by
        intro i
        have member : (HOL.weakenHyps (σ := σ) Δ).get i =
            HOL.weaken (Δ.get (i.cast (by simp [HOL.weakenHyps]))) := by
          obtain ⟨n, bound⟩ := i
          simp only [HOL.weakenHyps, List.get_eq_getElem, List.getElem_map]
          rfl
        rw [member, HOL.weaken, e.translate_weaken]
        simp only [Layout.lfCtx]
        rw [lookup_cons_succ, hyps]
        simp only [Option.map_some, LFTyping.lift, Layout.place]
        rw [L.place_lift 0 0 le_rfl])
      have lamTyped := HasType.lam (p.toDeclares.El_code_typed σ)
        (p.placed_proof_typed (L.obj σ) body) arrow_rule bodyTyped
      have goal : Conv theory (.pi (e.El (e.code σ))
          (.app (.con proof) ((L.obj σ).place 0 (e.translate body))))
          (.app (.con proof) (L.place 0 (e.translate (.all body)))) := by
        rw [show e.translate (.all body) = e.binder .all σ (e.El (e.code σ)) (e.translate body)
          from rfl, L.place_binder e]
        exact .symm _ _ (p.conv_all σ _)
      exact .conv lamTyped goal (p.placed_proof_typed L _)
  | @allE Γ Δ σ body t function ih =>
      intro L hypVar hyps
      have functionTyped := ih L hypVar hyps
      rw [show e.translate (.all body) = e.binder .all σ (e.El (e.code σ)) (e.translate body)
        from rfl, L.place_binder e] at functionTyped
      have asFunction := HasType.conv functionTyped (p.conv_all σ _)
        (.pi (p.toDeclares.El_code_typed σ) (p.placed_proof_typed (L.obj σ) body) arrow_rule)
      have applied := HasType.app asFunction (p.placed_typed L t)
      have shape : subst0 (L.place 0 (e.translate t))
          (.app (.con proof) (L.place 1 (e.translate body))) =
          .app (.con proof) (L.place 0 (e.translate (HOL.instantiate t body))) := by
        rw [e.translate_instantiate, L.place_subst0]
        rfl
      rwa [shape] at applied
  | @convert Γ Δ source target conversion inner ih =>
      intro L hypVar hyps
      have converted : Conv theory (e.translate source) (e.translate target) :=
        Encoding.translate_conv (betaConv_of_coreConversion conversion)
      exact .conv (ih L hypVar hyps) (Conv.app (.refl _) (L.conv_place p.closedBodies converted))
        (p.placed_proof_typed L target)

/-- **Every theorem is inhabited in the hub**: a proof with no hypothesis
compiles to a term of the type of the proofs of the translation of its
conclusion, in the context of the decodings of the objects. -/
theorem theorem_typed {Γ : Ctx Base} {φ : Formula Const Γ} (d : HOL.ProofSyntaxModulo [] [] φ) :
    LambdaPiModulo theory (e.ctx Γ) (compile e proof d (.base Γ) Fin.elim0)
      (.app (.con proof) (e.translate φ)) :=
  p.compile_typed d (.base Γ) Fin.elim0 fun i => i.elim0

end ProofHub

/-! ## The STTfa hub -/

section STTfa

variable (e : Encoding Base Const)

/-- The declarations of the STTfa hub beyond the encoding, as in Logipedia's
theory file (`theories/sttfa/sttfa.dk` at commit `0bcb193`): `eps : eta bool → Type`,
`ptype : Type`, `p : type → ptype`, `etap : ptype → Type`,
`forallK : (type → ptype) → ptype` and `forallP : (type → eta bool) → eta bool`.
The file declares `type`, `arrow`, `bool`, `eta`, `impl` and `forall` as well; the
typed theory declares these through the encoding. -/
def sttfaProofTypes (name : String) : Option LF.Term :=
  if name = "eps" then some (.pi (e.El (e.sym .bool)) (.srt .type))
  else if name = "ptype" then some (.srt .type)
  else if name = "p" then some (.pi (.con "type") (.con "ptype"))
  else if name = "etap" then some (.pi (.con "ptype") (.srt .type))
  else if name = "forallK" then some (.pi (.pi (.con "type") (.con "ptype")) (.con "ptype"))
  else if name = "forallP" then
    some (.pi (.pi (.con "type") (e.El (e.sym .bool))) (e.El (e.sym .bool)))
  else none

/-- **The STTfa hub with proofs**: its six rules, the encoding of the signature
declared over `type`, and the remaining declarations of Logipedia's theory file
(`sttfaProofTypes`). -/
noncomputable def sttfaProofTheory : Theory :=
  e.typedTheory TranslationTransport.STTfa.theory "type" (sttfaProofTypes e)

theorem sttfaProofTheory_closedBodies : (sttfaProofTheory e).ClosedBodies := by
  intro name term defined
  simp [sttfaProofTheory, Encoding.typedTheory, TranslationTransport.STTfa.theory, Theory.ofSig,
    lookupBody] at defined

theorem sttfaProofTheory_closedTypes : (sttfaProofTheory e).ClosedTypes := by
  intro name type declared
  simp only [sttfaProofTheory, Encoding.typedTheory] at declared
  split_ifs at declared
  · cases declared; exact e.declaredType_closed _ _
  · cases declared; exact .srt
  · cases declared; exact .pi .con .srt
  · simp only [sttfaProofTypes] at declared
    split_ifs at declared <;> cases declared
    · exact .pi (.app .con .con) .srt
    · exact .srt
    · exact .pi .con .con
    · exact .pi .con .srt
    · exact .pi (.pi .con .con) .con
    · exact .pi (.pi .con (.app .con .con)) (.app .con .con)

/-- A constant that the encoding does not name, other than `type` and the
decoder, has its declaration of Logipedia's theory file. -/
theorem sttfaProofTheory_constType_extra {name : String} (unnamed : ∀ s, e.name s ≠ name)
    (notCodes : name ≠ "type") (notEl : name ≠ e.el) :
    (sttfaProofTheory e).constType name = sttfaProofTypes e name := by
  have none_ : ¬ ∃ s, e.name s = name := fun ⟨s, same⟩ => unnamed s same
  simp [sttfaProofTheory, Encoding.typedTheory, none_, notCodes, notEl]

/-- **The STTfa hub is a theory of proofs** for every encoding that decodes
with `eta`, codes functions with `arrow`, names `⇒` `impl` and `∀` `forall`,
and names no symbol `eta`, `etap`, `eps` or `type`. -/
theorem sttfaProofHub (el : e.el = "eta") (arrow : e.name .arrow = "arrow")
    (imp : e.name .imp = "impl") (all : e.name .all = "forall")
    (fresh : ∀ s, e.name s ≠ "eta" ∧ e.name s ≠ "etap" ∧ e.name s ≠ "eps")
    (typeFresh : ∀ s, e.name s ≠ "type") :
    ProofHub e (sttfaProofTheory e) "type" "eps" where
  toDeclares :=
    (sttfaHub e el arrow fresh).typed_declares (sttfaProofTypes e) typeFresh (by rw [el]; decide)
  closedBodies := sttfaProofTheory_closedBodies e
  closedTypes := sttfaProofTheory_closedTypes e
  proof_type := by
    have unnamed : ¬ ∃ s, e.name s = "eps" := fun ⟨s, same⟩ => (fresh s).2.2 same
    simp [sttfaProofTheory, Encoding.typedTheory, unnamed, el, sttfaProofTypes]
  impRule := by
    have same : e.impRule "eps" = TranslationTransport.STTfa.epsImpl := by
      simp [Encoding.impRule, Encoding.binary, Encoding.sym, imp,
        TranslationTransport.STTfa.epsImpl, TranslationTransport.STTfa.eps,
        TranslationTransport.STTfa.binary]
    show TranslationTransport.STTfa.theory.rule (e.impRule "eps")
    rw [same]
    simp [TranslationTransport.STTfa.theory, Theory.ofSig, TranslationTransport.STTfa.rules]
  allRule := by
    have same : e.allRule "eps" = TranslationTransport.STTfa.epsForall := by
      simp [Encoding.allRule, Encoding.binary, Encoding.sym, Encoding.El, all, el,
        TranslationTransport.STTfa.epsForall, TranslationTransport.STTfa.eps,
        TranslationTransport.STTfa.eta, TranslationTransport.STTfa.binary]
    show TranslationTransport.STTfa.theory.rule (e.allRule "eps")
    rw [same]
    simp [TranslationTransport.STTfa.theory, Theory.ofSig, TranslationTransport.STTfa.rules]

/-- **Every theorem is inhabited in the STTfa hub.** -/
theorem sttfa_theorem_typed (el : e.el = "eta") (arrow : e.name .arrow = "arrow")
    (imp : e.name .imp = "impl") (all : e.name .all = "forall")
    (fresh : ∀ s, e.name s ≠ "eta" ∧ e.name s ≠ "etap" ∧ e.name s ≠ "eps")
    (typeFresh : ∀ s, e.name s ≠ "type") {Γ : Ctx Base} {φ : Formula Const Γ}
    (d : HOL.ProofSyntaxModulo [] [] φ) :
    LambdaPiModulo (sttfaProofTheory e) (e.ctx Γ) (compile e "eps" d (.base Γ) Fin.elim0)
      (.app (.con "eps") (e.translate φ)) :=
  (sttfaProofHub e el arrow imp all fresh typeFresh).theorem_typed d

end STTfa

/-! ## Controls -/

/-- The STTfa hub is a theory of proofs for the controls. -/
theorem sttfaControlProofs : ProofHub sttfaControl (sttfaProofTheory sttfaControl) "type" "eps" :=
  sttfaProofHub sttfaControl rfl rfl rfl rfl sttfaControl_fresh sttfaControl_typeFresh

/-- `pred x`, in the context `x : ι`. -/
def predVar : Formula ControlConst [ι] := .app (.const ControlConst.pred) (.var .vz)

/-- `⊢ ∀ x. pred x ⇒ pred x`. -/
def predSelfProof : HOL.ProofSyntaxModulo [] ([] : List (Formula ControlConst []))
    (.all (.imp predVar predVar)) :=
  .allI (.impI (.hyp ⟨0, by decide⟩))

/-- `⊢ (∀ x. pred x) ⇒ ∀ y. pred y`: a universal introduction under a
hypothesis. -/
def predSwapProof : HOL.ProofSyntaxModulo [] ([] : List (Formula ControlConst []))
    (.imp (.all predVar) (.all predVar)) :=
  .impI (.allI (.allE (Δ := HOL.weakenHyps [Term.all predVar])
    (φ := (.app (.const ControlConst.pred) (.var .vz) : Formula ControlConst [ι, ι])) (.var .vz)
    (.hyp ⟨0, by decide⟩)))

/-- `⊢ (∀ x. pred x) ⇒ pred point`. -/
def predInstanceProof : HOL.ProofSyntaxModulo [] ([] : List (Formula ControlConst []))
    (.imp (.all predVar) (.app (.const ControlConst.pred) (.const ControlConst.point))) :=
  .impI (.allE (Δ := [Term.all predVar]) (φ := predVar) (.const ControlConst.point)
    (.hyp ⟨0, by decide⟩))

/-- **`∀ x. pred x ⇒ pred x` is inhabited in the STTfa hub.** -/
theorem sttfa_predSelf_typed :
    LambdaPiModulo (sttfaProofTheory sttfaControl) (sttfaControl.ctx [])
      (compile sttfaControl "eps" predSelfProof (.base []) Fin.elim0)
      (.app (.con "eps") (sttfaControl.translate (.all (.imp predVar predVar)))) :=
  sttfa_theorem_typed sttfaControl rfl rfl rfl rfl sttfaControl_fresh sttfaControl_typeFresh
    predSelfProof

/-- **`(∀ x. pred x) ⇒ ∀ y. pred y` is inhabited in the STTfa hub**, through a
layout that brings an object into scope after a hypothesis. -/
theorem sttfa_predSwap_typed :
    LambdaPiModulo (sttfaProofTheory sttfaControl) (sttfaControl.ctx [])
      (compile sttfaControl "eps" predSwapProof (.base []) Fin.elim0)
      (.app (.con "eps") (sttfaControl.translate (.imp (.all predVar) (.all predVar)))) :=
  sttfaControlProofs.theorem_typed predSwapProof

/-- **`(∀ x. pred x) ⇒ pred point` is inhabited in the STTfa hub.** -/
theorem sttfa_predInstance_typed :
    LambdaPiModulo (sttfaProofTheory sttfaControl) (sttfaControl.ctx [])
      (compile sttfaControl "eps" predInstanceProof (.base []) Fin.elim0)
      (.app (.con "eps") (sttfaControl.translate
        (.imp (.all predVar) (.app (.const ControlConst.pred) (.const ControlConst.point))))) :=
  sttfaControlProofs.compile_typed predInstanceProof (.base []) Fin.elim0 fun i => i.elim0

#print axioms Layout.typed_place
#print axioms ProofHub.compile_typed
#print axioms ProofHub.theorem_typed
#print axioms sttfaProofHub
#print axioms sttfa_theorem_typed
#print axioms sttfa_predSelf_typed
#print axioms sttfa_predSwap_typed
#print axioms sttfa_predInstance_typed

end Mettapedia.GSLT.Dedukti.HOLHub
