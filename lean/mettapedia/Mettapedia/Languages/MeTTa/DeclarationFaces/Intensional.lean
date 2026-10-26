import Mettapedia.Languages.MeTTa.DeclarationFaces.Controls
import Mettapedia.GSLT.Dedukti.OrthogonalCheck
import Mettapedia.Logic.Relation.NormalFormDecision
import Mathlib.Data.List.GetD

/-!
# The intensional face: the declaration as a theory of the λΠ-calculus modulo rewriting

A declaration is read as a theory of the λΠ-calculus modulo rewriting (`declTheory`): each symbol
is a constant, an application is a spine of applications, and each equation is a declared rewrite
rule whose pattern variables are numbered by their place in the left side. Its definitional
equality is the conversion `Mettapedia.GSLT.Dedukti.Conv`, the relation the conversion rule of the
typing judgment uses.

* **(a) Running is sound** (`Step.toDedukti`, `Step.toConv`): every MeTTa step is a step of the
  theory, hence a definitional equality. This holds for every program whose right sides use only
  their left side's variables, admitted or not, and for open terms too.
* **The normal-form fiber** (`Admitted.normalFormFiber`): for an admitted declaration whose
  translated rules pass the tree's orthogonality test, conversion on the translations of closed
  sorted terms is decided by normalizing both sides (`Mettapedia.Logic.Relation.DecidedOn`). This
  generalizes `Mettapedia.GSLT.Dedukti.PeanoFiber.peano_decidedOn` from addition to every such
  declaration.
* **(b) Adequacy in both directions** (`Admitted.dedukti_normalForm_iff`): a term of the theory is a
  normal form of the translation of a closed sorted term exactly when it is the translation of
  MeTTa's normal form, which is constructor data.

Constructor data translates to a term no rule, beta or unfolding applies to (`Inert.normal`).

Positive examples: the translated rules of addition and of polymorphic `length` and `append` pass
the orthogonality test (`Examples.add_orthogonal`, `Examples.list_orthogonal`). Negative example:
the translated overlapping rules do not (`Examples.overlap_not_orthogonal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Tm Relation
open Mettapedia.GSLT.LanguageDef.LF (Term)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
open Mettapedia.GSLT.Dedukti (Theory RewriteRule inst headConst orthogonalCheck
  orthogonal_of_check confluent_of_orthogonal)
open Mettapedia.Logic.Relation (IsNormal Confluent IsNormalFormOf DecidedOn
  decidedOn_image_of_simulation)

universe u

variable {S : Type u} (name : S → String)

/-! ## Translation -/

/-- A head applied to arguments, one application at a time. -/
def spine (head : Term) (args : List Term) : Term := args.foldl Term.app head

mutual
/-- **The translation of a term**: variables by an index, applications as spines. -/
def trWith (ix : String → Nat) : Tm S → Term
  | .var x => .var (ix x)
  | .app f args => spine (.con (name f)) (trList ix args)
/-- The translation of a list of terms. -/
def trList (ix : String → Nat) : List (Tm S) → List Term
  | [] => []
  | a :: as => trWith ix a :: trList ix as
end

theorem trList_eq (ix : String → Nat) (args : List (Tm S)) :
    trList name ix args = args.map (trWith name ix) := by
  induction args with
  | nil => rfl
  | cons a as ih => simp [trList, ih]

theorem trWith_app (ix : String → Nat) (f : S) (args : List (Tm S)) :
    trWith name ix (.app f args) = spine (.con (name f)) (args.map (trWith name ix)) := by
  simp [trWith, trList_eq]

/-- The index of a variable of an equation: its place among the left side's variables. -/
def Equation.index (e : Equation S) (x : String) : Nat := e.lhs.vars.idxOf x

/-- **The rewrite rule of an equation.** -/
def trRule (e : Equation S) : RewriteRule :=
  ⟨trWith name e.index e.lhs, trWith name e.index e.rhs⟩

/-- **The theory of a program**: its equations as rewrite rules; no definitions. -/
def declTheory (P : Program S) : Theory where
  constType := fun _ => none
  body := fun _ => none
  rule := fun r => r ∈ P.map (trRule name)

theorem inst_spine (a : Nat → Term) : ∀ (args : List Term) (head : Term),
    inst a (spine head args) = spine (inst a head) (args.map (inst a))
  | [], head => rfl
  | arg :: args, head => by
      simp only [spine, List.foldl_cons, List.map_cons] at *
      exact inst_spine a args (.app head arg)

/-- **Translation commutes with instantiation**: the translation of an instance of a term is the
instance of its rule translation by the translations of the instantiating terms. -/
theorem trWith_subst (ix : String → Nat) (σ : String → Tm S) (L : List String) :
    ∀ t : Tm S, (∀ x ∈ t.vars, x ∈ L) →
      trWith name ix (t.subst σ) =
        inst (fun j => trWith name ix (σ (L.getD j ""))) (trWith name (fun x => L.idxOf x) t) := by
  intro t
  induction t using Tm.induction' with
  | var x =>
      intro within
      have hx : x ∈ L := within x (by simp)
      simp only [subst_var, trWith, Mettapedia.GSLT.Dedukti.inst_var]
      rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.mpr hx), List.getElem_idxOf]
  | app f args ih =>
      intro within
      rw [subst_app, trWith_app, trWith_app, inst_spine, Mettapedia.GSLT.Dedukti.inst_con,
        List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih a ha fun x hx => within x (by simpa using ⟨a, ha, hx⟩)

/-! ## (a) Running is sound -/

theorem spine_step_head {theory : Theory} {x y : Term} (step : Mettapedia.GSLT.Dedukti.Step theory x y) :
    ∀ args : List Term, Mettapedia.GSLT.Dedukti.Step theory (spine x args) (spine y args)
  | [] => step
  | arg :: args => by
      simp only [spine, List.foldl_cons]
      exact spine_step_head (step.plug (.appFunction .hole arg)) args

theorem spine_step_arg {theory : Theory} {x y : Term} (step : Mettapedia.GSLT.Dedukti.Step theory x y) :
    ∀ (args : List Term) (head : Term) (i : Nat) (lt : i < args.length), args[i] = x →
      Mettapedia.GSLT.Dedukti.Step theory (spine head args) (spine head (args.set i y))
  | [], _, i, lt, _ => absurd lt (Nat.not_lt_zero _)
  | arg :: args, head, 0, _, same => by
      simp only [List.getElem_cons_zero] at same
      subst same
      simp only [spine, List.foldl_cons, List.set_cons_zero]
      exact spine_step_head (step.plug (.appArgument head .hole)) args
  | arg :: args, head, k + 1, lt, same => by
      simp only [spine, List.foldl_cons, List.set_cons_succ]
      exact spine_step_arg step args (.app head arg) k (by simpa using lt) (by simpa using same)

/-- **Every MeTTa step is a step of the theory**, for right sides that use only their left side's
variables, at every translation of variables. -/
theorem Step.toDedukti {P : Program S} (bound : P.RightBound) (ix : String → Nat) {s t : Tm S}
    (step : Step P s t) :
    Mettapedia.GSLT.Dedukti.Step (declTheory name P) (trWith name ix s) (trWith name ix t) := by
  induction step with
  | root root =>
      obtain ⟨e, he, σ, rfl, rfl⟩ := root.exists_rule
      rw [trWith_subst name ix σ e.lhs.vars e.lhs (fun x hx => hx),
        trWith_subst name ix σ e.lhs.vars e.rhs (bound e he)]
      exact Mettapedia.GSLT.Dedukti.Step.root
        (.rule (rule := trRule name e) _ (List.mem_map_of_mem he))
  | @arg f args i lt b _ ih =>
      rw [trWith_app, trWith_app, List.map_set]
      exact spine_step_arg ih _ _ i (by simpa using lt) (by simp)

/-- **(a) Running is sound**: MeTTa's convertibility is contained in the definitional equality of
the theory that receives the equations as rewrite rules. -/
theorem Step.toConv {P : Program S} (bound : P.RightBound) (ix : String → Nat) {s t : Tm S}
    (conv : EqvGen (Step P) s t) :
    Mettapedia.GSLT.Dedukti.Conv (declTheory name P) (trWith name ix s) (trWith name ix t) := by
  induction conv with
  | rel _ _ step => exact .rel _ _ (step.toDedukti name bound ix)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-! ## Data is normal in the theory -/

/-- A term of the theory built from constants outside a set of names, by application. -/
inductive Inert (D : String → Prop) : Term → Prop where
  | con {c : String} : ¬ D c → Inert D (.con c)
  | app {a b : Term} : Inert D a → Inert D b → Inert D (.app a b)

theorem Inert.head_spec {D : String → Prop} {t : Term} (inert : Inert D t) :
    ∃ c, headConst t = some c ∧ ¬ D c := by
  induction inert with
  | con h => exact ⟨_, rfl, h⟩
  | app _ _ ih _ => simpa [Mettapedia.GSLT.Dedukti.headConst] using ih

theorem Inert.spine {D : String → Prop} {head : Term} (h : Inert D head) :
    ∀ {args : List Term}, (∀ a ∈ args, Inert D a) → Inert D (spine head args) := by
  intro args
  induction args generalizing head with
  | nil => intro _; exact h
  | cons a as ih =>
      intro each
      exact ih (.app h (each a List.mem_cons_self)) fun b hb => each b (List.mem_cons_of_mem a hb)

theorem headConst_spine (n : String) : ∀ args : List Term,
    headConst (spine (.con n) args) = some n := by
  intro args
  suffices ∀ (head : Term), headConst head = some n → headConst (spine head args) = some n from
    this _ rfl
  induction args with
  | nil => intro head h; exact h
  | cons a as ih => intro head h; exact ih (.app head a) (by simpa [Mettapedia.GSLT.Dedukti.headConst] using h)

/-- The names of the defined symbols. -/
def definedNames (P : Program S) (c : String) : Prop := ∃ f, P.Defines f ∧ name f = c

/-- No root step starts inside an inert term, at any position. -/
theorem Inert.not_rootStep_plug {P : Program S} (headed : P.Headed) :
    ∀ (context : Context) {src tgt : Term}, Inert (definedNames name P) (context.plug src) →
      ¬ Mettapedia.GSLT.Dedukti.RootStep (declTheory name P) src tgt := by
  intro context
  induction context with
  | hole =>
      intro src tgt inert root
      simp only [Context.plug] at inert
      cases root with
      | beta => cases inert with | app h _ => cases h
      | delta h => simp [declTheory] at h
      | @rule r a member =>
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp member
          obtain ⟨f, ps, hl⟩ := headed e he
          have head : Mettapedia.GSLT.Dedukti.headConst (trRule name e).lhs = some (name f) := by
            simp only [trRule, hl, trWith_app]
            exact headConst_spine _ _
          obtain ⟨c, hc, notDefined⟩ := inert.head_spec
          rw [Mettapedia.GSLT.Dedukti.headConst_instantiate a 0 head] at hc
          cases hc
          exact notDefined ⟨f, ⟨e, he, by simp [hl, head?]⟩, rfl⟩
  | piDomain _ _ _ => intro src tgt inert; simp [Context.plug] at inert; cases inert
  | piBody _ _ _ => intro src tgt inert; simp [Context.plug] at inert; cases inert
  | lamDomain _ _ _ => intro src tgt inert; simp [Context.plug] at inert; cases inert
  | lamBody _ _ _ => intro src tgt inert; simp [Context.plug] at inert; cases inert
  | appFunction rest arg ih =>
      intro src tgt inert
      simp only [Context.plug] at inert
      cases inert with
      | app h _ => exact ih h
  | appArgument fn rest ih =>
      intro src tgt inert
      simp only [Context.plug] at inert
      cases inert with
      | app _ h => exact ih h

/-- **Inert terms take no step** in the theory of a headed program. -/
theorem Inert.normal {P : Program S} (headed : P.Headed) {t : Term}
    (inert : Inert (definedNames name P) t) :
    IsNormal (Mettapedia.GSLT.Dedukti.Step (declTheory name P)) t := by
  intro target step
  cases step with
  | inContext context root => exact Inert.not_rootStep_plug name headed context inert root

/-- **Constructor data translates to an inert term**, for an injective naming of symbols. -/
theorem IsValue.inert {P : Program S} (inj : Function.Injective name) (ix : String → Nat) :
    ∀ {v : Tm S}, IsValue P v → Inert (definedNames name P) (trWith name ix v) := by
  intro v value
  induction value with
  | @app c args undefined _ ih =>
      rw [trWith_app]
      refine Inert.spine (.con ?_) fun a ha => ?_
      · rintro ⟨f, defined, same⟩
        exact undefined (inj same ▸ defined)
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact ih b hb

/-! ## The normal-form fiber and adequacy -/

namespace Admitted

variable [DecidableEq S] {sig : Signature S} {P : Program S}

omit [DecidableEq S] in
/-- The theory of an orthogonal rule list is confluent. -/
theorem dedukti_confluent (check : orthogonalCheck (P.map (trRule name)) = true) :
    Confluent (Mettapedia.GSLT.Dedukti.Step (declTheory name P)) :=
  confluent_of_orthogonal (orthogonal_of_check _ (fun _ h => h) (fun _ => rfl) check)

/-- The closed sorted terms of a signature. -/
def ClosedSorted (sig : Signature S) : Set (Tm S) := {t | ∃ τ, HasSort sig Ctx.empty t τ}

/-- **The normal-form fiber**: for an admitted declaration whose translated rules pass the
orthogonality test, conversion in the theory on the translations of closed sorted terms is
decided by normalizing both sides. -/
theorem normalFormFiber (adm : Admitted sig P) (inj : Function.Injective name)
    (check : orthogonalCheck (P.map (trRule name)) = true) (ix : String → Nat) :
    DecidedOn (Mettapedia.GSLT.Dedukti.Step (declTheory name P))
      (trWith name ix '' ClosedSorted sig) := by
  refine decidedOn_image_of_simulation (r := Step P) (trWith name ix)
    (fun _ _ step => .single (step.toDedukti name adm.rightBound ix)) ?_
    (dedukti_confluent name check) ?_
  · rintro a ⟨τ, typed⟩ n ⟨steps, normal⟩
    refine ⟨trWith name ix n, .refl, Inert.normal name adm.typed.headed (IsValue.inert name inj ix ?_)⟩
    rw [adm.normalForm_unique ⟨steps, normal⟩]
    exact (adm.normalForm_value typed).1.isValue adm.wellFormed adm.typed
  · rintro a ⟨τ, typed⟩
    exact ⟨adm.normalForm a, adm.normalForm_spec a⟩

/-- **(b) Adequacy in both directions**: the normal forms in the theory of the translation of a
closed sorted term are exactly the translation of MeTTa's normal form. -/
theorem dedukti_normalForm_iff (adm : Admitted sig P) (inj : Function.Injective name)
    (check : orthogonalCheck (P.map (trRule name)) = true) (ix : String → Nat) {t : Tm S}
    {τ : Sort'} (typed : HasSort sig Ctx.empty t τ) (m : Term) :
    Mettapedia.Logic.Relation.IsNormalFormOf (Mettapedia.GSLT.Dedukti.Step (declTheory name P))
        (trWith name ix t) m ↔
      m = trWith name ix (adm.normalForm t) := by
  have spec := adm.normalForm_spec t
  have toNF : ReflTransGen (Mettapedia.GSLT.Dedukti.Step (declTheory name P)) (trWith name ix t)
      (trWith name ix (adm.normalForm t)) :=
    spec.1.lift' (trWith name ix) fun _ _ step => .single (step.toDedukti name adm.rightBound ix)
  have nfNormal : IsNormal (Mettapedia.GSLT.Dedukti.Step (declTheory name P))
      (trWith name ix (adm.normalForm t)) :=
    Inert.normal name adm.typed.headed (IsValue.inert name inj ix
      ((adm.normalForm_value typed).1.isValue adm.wellFormed adm.typed))
  constructor
  · rintro ⟨steps, normal⟩
    obtain ⟨c, h₁, h₂⟩ := dedukti_confluent name check _ _ _ steps toNF
    exact (normal.reflTransGen_eq h₁).symm.trans (nfNormal.reflTransGen_eq h₂)
  · rintro rfl
    exact ⟨toNF, nfNormal⟩

end Admitted

/-! ## Examples -/

namespace Examples

open Controls

/-- **Positive example**: the translated rules of addition pass the orthogonality test. -/
theorem add_orthogonal : orthogonalCheck (addProgram.map (trRule id)) = true := by decide

/-- **Positive example**: the translated rules of `length` and `append` pass the test. -/
theorem list_orthogonal : orthogonalCheck (listProgram.map (trRule id)) = true := by decide

/-- **Negative example**: the translated overlapping rules do not pass the test. -/
theorem overlap_not_orthogonal : orthogonalCheck (Controls.overlapping.map (trRule id)) = false := by
  decide

/-- **The normal-form fiber of addition**, as an instance of the general theorem. -/
theorem add_fiber (ix : String → Nat) :
    DecidedOn (Mettapedia.GSLT.Dedukti.Step (declTheory id addProgram))
      (trWith id ix '' Admitted.ClosedSorted addSig) :=
  Controls.add_adm.normalFormFiber id Function.injective_id add_orthogonal ix

end Examples

end Mettapedia.Languages.MeTTa.DeclarationFaces
