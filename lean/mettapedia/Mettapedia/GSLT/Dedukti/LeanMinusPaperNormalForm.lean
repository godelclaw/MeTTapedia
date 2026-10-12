import Mettapedia.GSLT.Dedukti.LeanMinusLevelValues

/-!
# The normal forms of the paper's own level rules, and what they lose

`LeanMinusLevels` shows by two witnesses that the paper's level theory fails
both directions of its Theorem 2.  This module computes its normal forms for
all levels, and measures the first failure.

## The normal form

The paper's rules differ from the corrected ones in one rule, the middle
branch of the rule on `Add`, and in the code of a level variable.  Their
mirror is `addSubPaper`: where the head of the set is dominated, the new
sublevel is inserted into the rest by plain sorted insertion, so dominated
elements of the rest are kept.

* `paperCode_reduces_paperSet`: in the paper's level theory the code of every
  level reduces to `normalCode (normalSetWith addSubPaper unguardedLeaf l)`.
* `conv_paperCode_iff`: so the conversion of the paper's level theory, on the
  paper's codes, is equality of these sets, for all levels.

## Reductions that do not reach the rule on `Add`

The comparisons, the sorted insertion, the union of guards and the increment
are computed by rules that the two theories share.  Their reductions are
proved once, in the corrected theory.  They are carried to the paper's theory
by a general fact (`Step.transfer`, `Reduces.transfer`): a reduction from a
term that mentions none of the constants on which two theories differ is a
reduction of both, provided the constants avoided are closed under the
definitions and the rules (`Reduces.addFree_transfer` for the two level
theories and the constants `addTainted`).

## What is lost, and where

* `addSubPaper_sound`: the paper's rule on `Add` is sound at every valuation:
  keeping a dominated element changes no value.
* `eval_eq_of_conv_paperCode`: **two levels whose codes the paper's level
  theory converts have equal values at every valuation that is positive
  everywhere.**  The empty guard of Definition 2 makes the dominance test
  unsound exactly where a variable is `0`; the rule on `Add` loses nothing.

## The guard corrected alone

With each level variable in its own guard and the paper's rule on `Add`, the
code of every level reduces to the set computed with `addSubPaper` and the
guarded code of a variable (`code_reduces_guardedPaperSet`,
`conv_code_paperLevelTheory_iff`).  That set has the value of the level at
every valuation (`setEval_guardedPaperSet`), so the paper's level theory
converts the corrected codes of equivalent levels only
(`equiv_of_conv_code_paperLevelTheory`): the converse of the failure
`guard_alone_incomplete`, which shows that it does not convert them all.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig Decl lookupBody lift subst subst0)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)

/-! ## The constants of a reduct -/

theorem constantsOf_lift (term : Term) :
    ∀ amount cutoff : Nat, constantsOf (lift amount cutoff term) = constantsOf term := by
  induction term with
  | var index => intro amount cutoff; rfl
  | srt sort => intro amount cutoff; rfl
  | con name => intro amount cutoff; rfl
  | pi domain body ihDomain ihBody =>
      intro amount cutoff; simp [lift, constantsOf, ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      intro amount cutoff; simp [lift, constantsOf, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro amount cutoff; simp [lift, constantsOf, ihFunction, ihArgument]

/-- A substitution creates no constant. -/
theorem mem_constantsOf_subst (name : String) (term : Term) :
    ∀ (target : Nat) (replacement : Term), name ∈ constantsOf (subst target replacement term) →
      name ∈ constantsOf replacement ∨ name ∈ constantsOf term := by
  induction term with
  | var index =>
      intro target replacement member
      simp only [subst] at member
      split at member
      · exact Or.inl member
      · split at member <;> simp [constantsOf] at member
  | srt sort => intro target replacement member; simp [subst, constantsOf] at member
  | con other => intro target replacement member; exact Or.inr member
  | pi domain body ihDomain ihBody =>
      intro target replacement member
      simp only [subst, constantsOf, List.mem_append] at member ⊢
      rcases member with inDomain | inBody
      · rcases ihDomain _ _ inDomain with here | there
        · exact Or.inl here
        · exact Or.inr (Or.inl there)
      · rcases ihBody _ _ inBody with here | there
        · rw [constantsOf_lift] at here
          exact Or.inl here
        · exact Or.inr (Or.inr there)
  | lam domain body ihDomain ihBody =>
      intro target replacement member
      simp only [subst, constantsOf, List.mem_append] at member ⊢
      rcases member with inDomain | inBody
      · rcases ihDomain _ _ inDomain with here | there
        · exact Or.inl here
        · exact Or.inr (Or.inl there)
      · rcases ihBody _ _ inBody with here | there
        · rw [constantsOf_lift] at here
          exact Or.inl here
        · exact Or.inr (Or.inr there)
  | app function argument ihFunction ihArgument =>
      intro target replacement member
      simp only [subst, constantsOf, List.mem_append] at member ⊢
      rcases member with inFunction | inArgument
      · rcases ihFunction _ _ inFunction with here | there
        · exact Or.inl here
        · exact Or.inr (Or.inl there)
      · rcases ihArgument _ _ inArgument with here | there
        · exact Or.inl here
        · exact Or.inr (Or.inr there)

/-- An instance has the constants of the term and of the assigned terms only. -/
theorem mem_constantsOf_instantiate (assignment : Nat → Term) (name : String) (term : Term) :
    ∀ depth : Nat, name ∈ constantsOf (instantiate assignment depth term) →
      name ∈ constantsOf term ∨ ∃ index, name ∈ constantsOf (assignment index) := by
  induction term with
  | var index =>
      intro depth member
      simp only [instantiate] at member
      split at member
      · simp [constantsOf] at member
      · rw [constantsOf_lift] at member
        exact Or.inr ⟨_, member⟩
  | srt sort => intro depth member; exact Or.inl member
  | con other => intro depth member; exact Or.inl member
  | pi domain body ihDomain ihBody =>
      intro depth member
      simp only [instantiate, constantsOf, List.mem_append] at member ⊢
      rcases member with inDomain | inBody
      · rcases ihDomain _ inDomain with here | there
        · exact Or.inl (Or.inl here)
        · exact Or.inr there
      · rcases ihBody _ inBody with here | there
        · exact Or.inl (Or.inr here)
        · exact Or.inr there
  | lam domain body ihDomain ihBody =>
      intro depth member
      simp only [instantiate, constantsOf, List.mem_append] at member ⊢
      rcases member with inDomain | inBody
      · rcases ihDomain _ inDomain with here | there
        · exact Or.inl (Or.inl here)
        · exact Or.inr there
      · rcases ihBody _ inBody with here | there
        · exact Or.inl (Or.inr here)
        · exact Or.inr there
  | app function argument ihFunction ihArgument =>
      intro depth member
      simp only [instantiate, constantsOf, List.mem_append] at member ⊢
      rcases member with inFunction | inArgument
      · rcases ihFunction _ inFunction with here | there
        · exact Or.inl (Or.inl here)
        · exact Or.inr there
      · rcases ihArgument _ inArgument with here | there
        · exact Or.inl (Or.inr here)
        · exact Or.inr there

/-- An instance has the constants of the term. -/
theorem mem_constantsOf_instantiate_of_mem (assignment : Nat → Term) (name : String) (term : Term) :
    ∀ depth : Nat, name ∈ constantsOf term → name ∈ constantsOf (instantiate assignment depth term) := by
  induction term with
  | var index => intro depth member; simp [constantsOf] at member
  | srt sort => intro depth member; exact member
  | con other => intro depth member; exact member
  | pi domain body ihDomain ihBody =>
      intro depth member
      simp only [instantiate, constantsOf, List.mem_append] at member ⊢
      exact member.imp (ihDomain _) (ihBody _)
  | lam domain body ihDomain ihBody =>
      intro depth member
      simp only [instantiate, constantsOf, List.mem_append] at member ⊢
      exact member.imp (ihDomain _) (ihBody _)
  | app function argument ihFunction ihArgument =>
      intro depth member
      simp only [instantiate, constantsOf, List.mem_append] at member ⊢
      exact member.imp (ihFunction _) (ihArgument _)

/-- An instance of a pattern has the constants of the terms assigned to its
variables. -/
theorem mem_constantsOf_inst_of_patternVar (assignment : Nat → Term) (name : String) (index : Nat) :
    ∀ pattern : Term, index ∈ patternVars pattern → name ∈ constantsOf (assignment index) →
      name ∈ constantsOf (inst assignment pattern) := by
  intro pattern
  induction pattern with
  | var other =>
      intro inVars member
      simp only [patternVars, List.mem_singleton] at inVars
      rw [inst_var, ← inVars]
      exact member
  | srt sort => intro inVars; simp [patternVars] at inVars
  | con other => intro inVars; simp [patternVars] at inVars
  | pi domain body _ _ => intro inVars; simp [patternVars] at inVars
  | lam domain body _ _ => intro inVars; simp [patternVars] at inVars
  | app function argument ihFunction ihArgument =>
      intro inVars member
      simp only [patternVars, List.mem_append] at inVars
      rw [inst_app]
      simp only [constantsOf, List.mem_append]
      exact inVars.imp (fun inFunction => ihFunction inFunction member)
        (fun inArgument => ihArgument inArgument member)

/-- The constants of a term in a context are those of the context and those
of the term. -/
theorem mem_constantsOf_plug (name : String) (inner : Term) :
    ∀ context : Context, name ∈ constantsOf (context.plug inner) ↔
      name ∈ constantsOf (context.plug (.srt .type)) ∨ name ∈ constantsOf inner := by
  intro context
  induction context with
  | hole => simp [Context.plug, constantsOf]
  | piDomain rest body ih => simp only [Context.plug, constantsOf, List.mem_append, ih]; tauto
  | piBody domain rest ih => simp only [Context.plug, constantsOf, List.mem_append, ih]; tauto
  | lamDomain rest body ih => simp only [Context.plug, constantsOf, List.mem_append, ih]; tauto
  | lamBody domain rest ih => simp only [Context.plug, constantsOf, List.mem_append, ih]; tauto
  | appFunction rest argument ih => simp only [Context.plug, constantsOf, List.mem_append, ih]; tauto
  | appArgument function rest ih => simp only [Context.plug, constantsOf, List.mem_append, ih]; tauto

/-! ## Reductions that avoid the constants on which two theories differ -/

section Transfer

variable {first second : Theory} (tainted : String → Prop)

/-- **A step from a term that mentions none of the constants on which two
theories differ is a step of both**, and its target mentions none of them:
when the definitions of the constants kept are definitions of the second
theory that mention only constants kept, and the rules whose left sides
mention only constants kept are rules of the second theory whose right sides
mention only constants kept. -/
theorem Step.transfer
    (bodies : ∀ name body, first.body name = some body → ¬ tainted name →
      second.body name = some body ∧ ∀ other ∈ constantsOf body, ¬ tainted other)
    (rules : ∀ rule, first.rule rule → (∀ other ∈ constantsOf rule.lhs, ¬ tainted other) →
      second.rule rule ∧ ∀ other ∈ constantsOf rule.rhs, ¬ tainted other)
    (rightDetermined : ∀ rule, first.rule rule → ∀ left right : Nat → Term,
      (∀ index ∈ patternVars rule.lhs, left index = right index) →
        inst left rule.rhs = inst right rule.rhs)
    {source target : Term} (clean : ∀ other ∈ constantsOf source, ¬ tainted other)
    (step : Step first source target) :
    Step second source target ∧ ∀ other ∈ constantsOf target, ¬ tainted other := by
  cases step with
  | @inContext context redex contractum root =>
      have redexClean : ∀ other ∈ constantsOf redex, ¬ tainted other := fun other member =>
        clean other ((mem_constantsOf_plug other redex context).mpr (Or.inr member))
      have rootTransfer : RootStep second redex contractum ∧
          ∀ other ∈ constantsOf contractum, ¬ tainted other := by
        cases root with
        | beta domain body argument =>
            refine ⟨.beta domain body argument, fun other member => ?_⟩
            rcases mem_constantsOf_subst other body 0 argument member with inArgument | inBody
            · exact redexClean other (by simp [constantsOf, inArgument])
            · exact redexClean other (by simp [constantsOf, inBody])
        | @delta name _ defined =>
            obtain ⟨defined', bodyClean⟩ :=
              bodies name _ defined (redexClean name (by simp [constantsOf]))
            exact ⟨.delta defined', bodyClean⟩
        | @rule rule assignment member =>
            have lhsClean : ∀ other ∈ constantsOf rule.lhs, ¬ tainted other := fun other inLhs =>
              redexClean other (mem_constantsOf_instantiate_of_mem assignment other rule.lhs 0 inLhs)
            obtain ⟨member', rhsClean⟩ := rules rule member lhsClean
            refine ⟨.rule assignment member', fun other inTarget => ?_⟩
            have same : inst assignment rule.rhs =
                inst (fun index => if index ∈ patternVars rule.lhs then assignment index
                  else .srt .type) rule.rhs :=
              rightDetermined rule member _ _ fun index inVars => by simp [inVars]
            rw [same] at inTarget
            rcases mem_constantsOf_instantiate _ other rule.rhs 0 inTarget with inRhs | ⟨index, inValue⟩
            · exact rhsClean other inRhs
            · by_cases inVars : index ∈ patternVars rule.lhs
              · simp only [inVars, if_true] at inValue
                exact redexClean other
                  (mem_constantsOf_inst_of_patternVar assignment other index rule.lhs inVars inValue)
              · simp [inVars, constantsOf] at inValue
      refine ⟨Step.inContext context rootTransfer.1, fun other member => ?_⟩
      rcases (mem_constantsOf_plug other contractum context).mp member with inContext | inContractum
      · exact clean other ((mem_constantsOf_plug other redex context).mpr (Or.inl inContext))
      · exact rootTransfer.2 other inContractum

/-- **A reduction from a term that mentions none of the constants on which two
theories differ is a reduction of both.** -/
theorem Reduces.transfer
    (bodies : ∀ name body, first.body name = some body → ¬ tainted name →
      second.body name = some body ∧ ∀ other ∈ constantsOf body, ¬ tainted other)
    (rules : ∀ rule, first.rule rule → (∀ other ∈ constantsOf rule.lhs, ¬ tainted other) →
      second.rule rule ∧ ∀ other ∈ constantsOf rule.rhs, ¬ tainted other)
    (rightDetermined : ∀ rule, first.rule rule → ∀ left right : Nat → Term,
      (∀ index ∈ patternVars rule.lhs, left index = right index) →
        inst left rule.rhs = inst right rule.rhs)
    {source target : Term} (clean : ∀ other ∈ constantsOf source, ¬ tainted other)
    (reduces : Reduces first source target) :
    Reduces second source target ∧ ∀ other ∈ constantsOf target, ¬ tainted other := by
  induction reduces with
  | refl => exact ⟨.refl, clean⟩
  | tail _ step ih =>
      obtain ⟨moved, cleanTarget⟩ := Step.transfer tainted bodies rules rightDetermined ih.2 step
      exact ⟨ih.1.tail moved, cleanTarget⟩

end Transfer

/-- A definition found in a signature is one of its declarations. -/
theorem defn_mem_of_lookupBody :
    ∀ {signature : Sig} {name : String} {body : Term}, lookupBody signature name = some body →
      ∃ type, Decl.defn name type body ∈ signature := by
  intro signature
  induction signature with
  | nil => intro name body found; simp [lookupBody] at found
  | cons head rest ih =>
      intro name body found
      cases head with
      | const declared type =>
          simp only [lookupBody] at found
          obtain ⟨type', member⟩ := ih found
          exact ⟨type', List.mem_cons_of_mem _ member⟩
      | defn declared type term =>
          simp only [lookupBody] at found
          split at found
          · rename_i same
            obtain rfl := Option.some.inj found
            subst same
            exact ⟨type, List.mem_cons_self⟩
          · obtain ⟨type', member⟩ := ih found
            exact ⟨type', List.mem_cons_of_mem _ member⟩

end Mettapedia.GSLT.Dedukti

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig Decl lookupBody lift subst subst0)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## The two level theories agree away from `Add` -/

/-- The constants from which a reduction can reach the rule on `Add`: `Add`
itself, the two definitions and the three level operations whose rules
mention it. -/
def addTainted : List String := ["Add", "Addguard", "FoldAddguard", "succ", "max", "imax"]

/-- A term that mentions none of the constants from which the rule on `Add`
can be reached. -/
def AddFree (term : Term) : Prop := ∀ name ∈ constantsOf term, name ∉ addTainted

instance (term : Term) : Decidable (AddFree term) :=
  inferInstanceAs (Decidable (∀ name ∈ constantsOf term, name ∉ addTainted))

/-- A definition keeps away from `Add`, or is one of the constants avoided. -/
def bodyAddFreeTest : Decl → Bool
  | .defn name _ body => decide (name ∈ addTainted) || decide (AddFree body)
  | .const _ _ => true

theorem pureSig_bodies_addFree : pureSig.all bodyAddFreeTest = true := by
  decide +kernel

theorem pureRulesExplicit_addFree :
    ∀ rule ∈ pureRulesExplicit, AddFree rule.lhs → rule ∈ paperLevelRules ∧ AddFree rule.rhs := by
  decide +kernel

/-- **A reduction of the corrected level theory from a term that keeps away
from `Add` is a reduction of the paper's level theory.** -/
theorem Reduces.addFree_transfer {source target : Term} (clean : AddFree source)
    (reduces : Reduces pureTheoryExplicit source target) : Reduces paperLevelTheory source target := by
  refine (Dedukti.Reduces.transfer (first := pureTheoryExplicit) (second := paperLevelTheory)
    (fun name => name ∈ addTainted) ?_ ?_ pureTheoryExplicit_orthogonal.rightDetermined clean
    reduces).1
  · intro name body defined kept
    refine ⟨defined, ?_⟩
    obtain ⟨type, member⟩ := defn_mem_of_lookupBody (signature := pureSig) defined
    have passed := List.all_eq_true.mp pureSig_bodies_addFree _ member
    simp only [bodyAddFreeTest, Bool.or_eq_true, decide_eq_true_eq] at passed
    rcases passed with tainted | free
    · exact absurd tainted kept
    · exact free
  · intro rule member lhsFree
    exact pureRulesExplicit_addFree rule member lhsFree

theorem setConstructors_addFree : ∀ name ∈ setConstructors, name ∉ addTainted := by
  decide

theorem addFree_con {name : String} (kept : name ∉ addTainted) : AddFree (.con name) := by
  intro other member
  simp only [constantsOf, List.mem_singleton] at member
  rw [member]
  exact kept

theorem addFree_sublevelCode (sublevel : Sublevel) : AddFree (sublevelCode sublevel) :=
  fun name member => setConstructors_addFree name (sublevelCode_constants sublevel name member)

theorem addFree_setCode (set : List Sublevel) : AddFree (setCode set) :=
  fun name member => setConstructors_addFree name (setCode_constants set name member)

theorem addFree_apT : ∀ {arguments : List Term} {function : Term}, AddFree function →
    (∀ argument ∈ arguments, AddFree argument) → AddFree (apT function arguments)
  | [], _, functionFree, _ => functionFree
  | argument :: rest, function, functionFree, argumentsFree => by
      refine addFree_apT (arguments := rest) (function := .app function argument) ?_
        (fun other member => argumentsFree other (List.mem_cons_of_mem _ member))
      intro name member
      simp only [constantsOf, List.mem_append] at member
      rcases member with inFunction | inArgument
      · exact functionFree name inFunction
      · exact argumentsFree argument List.mem_cons_self name inArgument

theorem addFree_ap {head : String} (kept : head ∉ addTainted) {arguments : List Term}
    (argumentsFree : ∀ argument ∈ arguments, AddFree argument) : AddFree (ap head arguments) :=
  addFree_apT (addFree_con kept) argumentsFree

/-! ## The shared rules, in the paper's level theory -/

theorem paper_leS_reduces (first second : Sublevel) :
    Reduces paperLevelTheory (ap "leS" [sublevelCode first, sublevelCode second])
      (boolCode (leSub first second)) :=
  Reduces.addFree_transfer
    (addFree_ap (by decide) (by simp [addFree_sublevelCode])) (leS_reduces first second)

theorem paper_insertSub_reduces (sublevel : Sublevel) (set : List Sublevel) :
    Reduces paperLevelTheory (ap "add" [.con "S_code", .con "cmpS", sublevelCode sublevel, setCode set])
      (setCode (insertSorted cmpSub sublevel set)) :=
  Reduces.addFree_transfer
    (addFree_ap (by decide) (by
      simp [addFree_sublevelCode, addFree_setCode, addFree_con (show "S_code" ∉ addTainted by decide),
        addFree_con (show "cmpS" ∉ addTainted by decide)]))
    (insertSub_reduces sublevel set)

theorem paper_Incr_reduces (set : List Sublevel) :
    Reduces paperLevelTheory (ap "Incr" [setCode set]) (setCode (set.map incrSub)) :=
  Reduces.addFree_transfer (addFree_ap (by decide) (by simp [addFree_setCode])) (Incr_reduces set)

theorem paper_addguard_reduces (first second : Sublevel) :
    Reduces paperLevelTheory (ap "addguard" [sublevelCode first, sublevelCode second])
      (sublevelCode (addguardSub first second)) :=
  Reduces.addFree_transfer
    (addFree_ap (by decide) (by simp [addFree_sublevelCode])) (addguard_reduces first second)

/-! ## Computed reductions of the paper's level theory -/

/-- A computed reduction of the paper's level theory on a term with free
variables, instantiated by closed terms. -/
theorem reducesPaper_inst {skeleton result : Term} {fuel : Nat}
    (computed : evaluate pureSig paperLevelRules fuel skeleton = result) (values : List Term)
    (closed : ∀ value ∈ values, Closed value) (skeletonFlat : flatBelow values.length skeleton = true)
    (resultFlat : flatBelow values.length result = true) :
    Reduces paperLevelTheory (inst (assign values) skeleton) (inst (assign values) result) := by
  have filled := Reduces.fill paperLevelTheory_orthogonal.closedBodies values
    (Reduces.of_evaluate paperLevelRules_linear computed)
  rwa [fill_eq_inst values closed skeleton skeletonFlat, fill_eq_inst values closed result resultFlat]
    at filled

theorem paper_assign_pointwise {values values' : List Term}
    (pointwise : List.Forall₂ (Reduces paperLevelTheory) values values') :
    ∀ index, Reduces paperLevelTheory (assign values index) (assign values' index) := by
  induction pointwise with
  | nil => intro index; exact .refl
  | cons head _ ih =>
      intro index
      cases index with
      | zero => simpa [assign] using head
      | succ index => simpa [assign] using ih index

/-- Reduce the values of an instance, all at once, in the paper's level theory. -/
theorem paper_reduces_values {values values' : List Term}
    (pointwise : List.Forall₂ (Reduces paperLevelTheory) values values') (skeleton : Term) :
    Reduces paperLevelTheory (inst (assign values) skeleton) (inst (assign values') skeleton) :=
  Reduces.instantiate paperLevelTheory_orthogonal.closedBodies (paper_assign_pointwise pointwise)
    skeleton 0

theorem paperLevelRule_mem {rule : RewriteRule} (member : rule ∈ paperLevelRules) :
    paperLevelTheory.rule rule :=
  member

/-- `if c b x y ⟶ x` or `y`, in the paper's level theory. -/
theorem paper_if_reduces (code : Term) (choice : Bool) (first second : Term) :
    Reduces paperLevelTheory (ap "if" [code, boolCode choice, first, second])
      (if choice then first else second) := by
  cases choice with
  | true =>
      exact .single (Step.root (rootStep_of_instance (rule := rulesBOrthogonal[4])
        (paperLevelRule_mem (by decide)) (assign [code, first, second])
        (by simp [rulesBOrthogonal, mkRule, closePattern, placeholderIndex, nv, assign, ap, apT, boolCode])
        (by simp [rulesBOrthogonal, mkRule, closePattern, placeholderIndex, nv, assign])))
  | false =>
      exact .single (Step.root (rootStep_of_instance (rule := rulesBOrthogonal[5])
        (paperLevelRule_mem (by decide)) (assign [code, first, second])
        (by simp [rulesBOrthogonal, mkRule, closePattern, placeholderIndex, nv, assign, ap, apT, boolCode])
        (by simp [rulesBOrthogonal, mkRule, closePattern, placeholderIndex, nv, assign])))

/-! ## The paper's rule on `Add` -/

/-- **The paper's `Add`**: insert a sublevel, dropping it if the head dominates
it; where it dominates the head, the head is dropped and the sublevel is
inserted into the rest by plain sorted insertion, which tests nothing. -/
def addSubPaper (sublevel : Sublevel) : List Sublevel → List Sublevel
  | [] => [sublevel]
  | head :: rest =>
      if leSub sublevel head then head :: rest
      else if leSub head sublevel then insertSorted cmpSub sublevel rest
      else insertSorted cmpSub head (addSubPaper sublevel rest)

/-- **The paper's rule on `Add` computes `addSubPaper`.** -/
theorem paper_Add_reduces (sublevel : Sublevel) :
    ∀ set : List Sublevel,
      Reduces paperLevelTheory (ap "Add" [sublevelCode sublevel, setCode set])
        (setCode (addSubPaper sublevel set))
  | [] => by
      have computed := reducesPaper_inst (skeleton := ap "Add" [.var 0, ap "nil" [.con "S_code"]])
        (result := ap "cons" [.con "S_code", .var 0, ap "nil" [.con "S_code"]]) (fuel := 1)
        (by decide +kernel) [sublevelCode sublevel]
        (closed_of_mem (by simp [sublevelCode_closed])) rfl rfl
      inst_simp at computed
      exact computed
  | head :: rest => by
      have computed := reducesPaper_inst
        (skeleton := ap "Add" [.var 0, ap "cons" [.con "S_code", .var 1, .var 2]])
        (result := ap "if" [ap "set" [.con "S_code"], ap "leS" [.var 0, .var 1],
          ap "cons" [.con "S_code", .var 1, .var 2],
          ap "if" [ap "set" [.con "S_code"], ap "leS" [.var 1, .var 0],
            ap "add" [.con "S_code", .con "cmpS", .var 0, .var 2],
            ap "add" [.con "S_code", .con "cmpS", .var 1, ap "Add" [.var 0, .var 2]]]]) (fuel := 1)
        (by decide +kernel) [sublevelCode sublevel, sublevelCode head, setCode rest]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      have inner := paper_reduces_values
        (values := [ap "leS" [sublevelCode sublevel, sublevelCode head],
          ap "leS" [sublevelCode head, sublevelCode sublevel], ap "Add" [sublevelCode sublevel, setCode rest],
          sublevelCode sublevel, sublevelCode head, setCode rest])
        (values' := [boolCode (leSub sublevel head), boolCode (leSub head sublevel),
          setCode (addSubPaper sublevel rest), sublevelCode sublevel, sublevelCode head, setCode rest])
        (.cons (paper_leS_reduces sublevel head) (.cons (paper_leS_reduces head sublevel)
          (.cons (paper_Add_reduces sublevel rest) (.cons .refl (.cons .refl (.cons .refl .nil))))))
        (ap "if" [ap "set" [.con "S_code"], .var 0, ap "cons" [.con "S_code", .var 4, .var 5],
          ap "if" [ap "set" [.con "S_code"], .var 1,
            ap "add" [.con "S_code", .con "cmpS", .var 3, .var 5],
            ap "add" [.con "S_code", .con "cmpS", .var 4, .var 2]]])
      inst_simp at computed inner
      refine (computed : Reduces paperLevelTheory (ap "Add" [sublevelCode sublevel, setCode (head :: rest)])
        _).trans (inner.trans ?_)
      refine (paper_if_reduces _ _ _ _).trans ?_
      by_cases dominated : leSub sublevel head
      · simp only [dominated, if_true, addSubPaper]
        exact .refl
      · simp only [dominated, Bool.false_eq_true, if_false]
        refine (paper_if_reduces _ _ _ _).trans ?_
        by_cases dominates : leSub head sublevel
        · simp only [dominates, if_true, addSubPaper, dominated, Bool.false_eq_true, if_false]
          exact paper_insertSub_reduces sublevel rest
        · simp only [dominates, Bool.false_eq_true, if_false, addSubPaper, dominated]
          exact paper_insertSub_reduces head (addSubPaper sublevel rest)

/-- `fold … Add` inserts the elements of the first set into the second, by the
paper's rule. -/
theorem paper_foldAdd_reduces :
    ∀ first second : List Sublevel,
      Reduces paperLevelTheory
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], .con "Add", setCode first, setCode second])
        (setCode (first.foldl (fun accumulated element => addSubPaper element accumulated) second))
  | [], second => by
      have computed := reducesPaper_inst (skeleton := ap "fold" [.con "S_code", ap "set" [.con "S_code"],
          .con "Add", ap "nil" [.con "S_code"], .var 0]) (result := .var 0) (fuel := 1) (by decide +kernel)
        [setCode second] (closed_of_mem (by simp [setCode_closed])) rfl rfl
      inst_simp at computed
      exact computed
  | head :: rest, second => by
      have computed := reducesPaper_inst (skeleton := ap "fold" [.con "S_code", ap "set" [.con "S_code"],
          .con "Add", ap "cons" [.con "S_code", .var 0, .var 1], .var 2])
        (result := ap "fold" [.con "S_code", ap "set" [.con "S_code"], .con "Add", .var 1,
          ap "Add" [.var 0, .var 2]]) (fuel := 1) (by decide +kernel)
        [sublevelCode head, setCode rest, setCode second]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      have inner := paper_reduces_values
        (values := [ap "Add" [sublevelCode head, setCode second], setCode rest])
        (values' := [setCode (addSubPaper head second), setCode rest])
        (.cons (paper_Add_reduces head second) (.cons .refl .nil))
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], .con "Add", .var 1, .var 0])
      inst_simp at computed inner
      exact (computed : Reduces paperLevelTheory
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], .con "Add", setCode (head :: rest),
          setCode second]) _).trans (inner.trans (paper_foldAdd_reduces rest (addSubPaper head second)))

/-- `fold … (Addguard u)` inserts `addguard u v` for every `v`, by the paper's
rule. -/
theorem paper_foldAddguard_reduces (sublevel : Sublevel) :
    ∀ set accumulated : List Sublevel,
      Reduces paperLevelTheory
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "Addguard" [sublevelCode sublevel],
          setCode set, setCode accumulated])
        (setCode (set.foldl
          (fun accumulated' other => addSubPaper (addguardSub sublevel other) accumulated') accumulated))
  | [], accumulated => by
      have computed := reducesPaper_inst (skeleton := ap "fold" [.con "S_code", ap "set" [.con "S_code"],
          ap "Addguard" [.var 0], ap "nil" [.con "S_code"], .var 1]) (result := .var 1) (fuel := 1)
        (by decide +kernel) [sublevelCode sublevel, setCode accumulated]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      inst_simp at computed
      exact computed
  | head :: rest, accumulated => by
      have computed := reducesPaper_inst (skeleton := ap "fold" [.con "S_code", ap "set" [.con "S_code"],
          ap "Addguard" [.var 0], ap "cons" [.con "S_code", .var 1, .var 2], .var 3])
        (result := ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "Addguard" [.var 0], .var 2,
          ap "Addguard" [.var 0, .var 1, .var 3]]) (fuel := 1) (by decide +kernel)
        [sublevelCode sublevel, sublevelCode head, setCode rest, setCode accumulated]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      have unfolded := reducesPaper_inst (skeleton := ap "Addguard" [.var 0, .var 1, .var 2])
        (result := ap "Add" [ap "addguard" [.var 0, .var 1], .var 2]) (fuel := 3) (by decide +kernel)
        [sublevelCode sublevel, sublevelCode head, setCode accumulated]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      have guarded := paper_reduces_values
        (values := [ap "addguard" [sublevelCode sublevel, sublevelCode head], setCode accumulated])
        (values' := [sublevelCode (addguardSub sublevel head), setCode accumulated])
        (.cons (paper_addguard_reduces sublevel head) (.cons .refl .nil)) (ap "Add" [.var 0, .var 1])
      inst_simp at computed unfolded guarded
      have step : Reduces paperLevelTheory
          (ap "Addguard" [sublevelCode sublevel, sublevelCode head, setCode accumulated])
          (setCode (addSubPaper (addguardSub sublevel head) accumulated)) :=
        (unfolded.trans guarded).trans (paper_Add_reduces _ _)
      have inner := paper_reduces_values
        (values := [ap "Addguard" [sublevelCode sublevel, sublevelCode head, setCode accumulated],
          sublevelCode sublevel, setCode rest])
        (values' := [setCode (addSubPaper (addguardSub sublevel head) accumulated), sublevelCode sublevel,
          setCode rest])
        (.cons step (.cons .refl (.cons .refl .nil)))
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "Addguard" [.var 1], .var 2, .var 0])
      inst_simp at inner
      exact (computed : Reduces paperLevelTheory
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "Addguard" [sublevelCode sublevel],
          setCode (head :: rest), setCode accumulated]) _).trans
        (inner.trans (paper_foldAddguard_reduces sublevel rest _))

/-- The nested insertion that the rule on `imax` performs, for an insertion
`add`: every copy of a sublevel of the first set guarded by a sublevel of the
second, inserted into the accumulated set. -/
def guardedSetWith (add : Sublevel → List Sublevel → List Sublevel)
    (first second accumulated : List Sublevel) : List Sublevel :=
  first.foldl (fun accumulated' element =>
    second.foldl (fun accumulated'' other => add (addguardSub element other) accumulated'')
      accumulated') accumulated

theorem guardedSetWith_eq_fold (add : Sublevel → List Sublevel → List Sublevel)
    (first second accumulated : List Sublevel) :
    guardedSetWith add first second accumulated =
      (first.flatMap fun element => second.map (addguardSub element)).foldl
        (fun accumulated' element => add element accumulated') accumulated := by
  induction first generalizing accumulated with
  | nil => rfl
  | cons head rest ih =>
      simp only [guardedSetWith, List.foldl_cons, List.flatMap_cons, List.foldl_append, List.foldl_map]
      exact ih _

/-- `fold … (FoldAddguard F)` computes the nested insertion, by the paper's
rule. -/
theorem paper_foldFoldAddguard_reduces (guards : List Sublevel) :
    ∀ set accumulated : List Sublevel,
      Reduces paperLevelTheory
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "FoldAddguard" [setCode guards],
          setCode set, setCode accumulated])
        (setCode (guardedSetWith addSubPaper set guards accumulated))
  | [], accumulated => by
      have computed := reducesPaper_inst (skeleton := ap "fold" [.con "S_code", ap "set" [.con "S_code"],
          ap "FoldAddguard" [.var 0], ap "nil" [.con "S_code"], .var 1]) (result := .var 1) (fuel := 1)
        (by decide +kernel) [setCode guards, setCode accumulated]
        (closed_of_mem (by simp [setCode_closed])) rfl rfl
      inst_simp at computed
      exact computed
  | head :: rest, accumulated => by
      have computed := reducesPaper_inst (skeleton := ap "fold" [.con "S_code", ap "set" [.con "S_code"],
          ap "FoldAddguard" [.var 0], ap "cons" [.con "S_code", .var 1, .var 2], .var 3])
        (result := ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "FoldAddguard" [.var 0], .var 2,
          ap "FoldAddguard" [.var 0, .var 1, .var 3]]) (fuel := 1) (by decide +kernel)
        [setCode guards, sublevelCode head, setCode rest, setCode accumulated]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      have unfolded := reducesPaper_inst (skeleton := ap "FoldAddguard" [.var 0, .var 1, .var 2])
        (result := ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "Addguard" [.var 1], .var 0, .var 2])
        (fuel := 4) (by decide +kernel) [setCode guards, sublevelCode head, setCode accumulated]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      inst_simp at computed unfolded
      have step : Reduces paperLevelTheory
          (ap "FoldAddguard" [setCode guards, sublevelCode head, setCode accumulated])
          (setCode (guards.foldl
            (fun accumulated' other => addSubPaper (addguardSub head other) accumulated') accumulated)) :=
        unfolded.trans (paper_foldAddguard_reduces head guards accumulated)
      have inner := paper_reduces_values
        (values := [ap "FoldAddguard" [setCode guards, sublevelCode head, setCode accumulated],
          setCode guards, setCode rest])
        (values' := [setCode (guards.foldl (fun accumulated' other =>
            addSubPaper (addguardSub head other) accumulated') accumulated), setCode guards, setCode rest])
        (.cons step (.cons .refl (.cons .refl .nil)))
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "FoldAddguard" [.var 1], .var 2, .var 0])
      inst_simp at inner
      exact (computed : Reduces paperLevelTheory
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "FoldAddguard" [setCode guards],
          setCode (head :: rest), setCode accumulated]) _).trans
        (inner.trans (paper_foldFoldAddguard_reduces guards rest _))

/-! ## The paper's codes of levels -/

theorem paper_succ_reduces (set : List Sublevel) :
    Reduces paperLevelTheory (succ (normalCode set))
      (normalCode (addSubPaper (.cst [] 1) (set.map incrSub))) := by
  have computed := reducesPaper_inst (skeleton := succ (ap "Max" [.var 0]))
    (result := ap "Max" [ap "Add" [ap "cst" [ap "nil" [.con "N_code"], ap "s" [zeroN]], ap "Incr" [.var 0]]])
    (fuel := 1) (by decide +kernel) [setCode set] (closed_of_mem (by simp [setCode_closed])) rfl rfl
  have inner := paper_reduces_values (values := [ap "Incr" [setCode set]])
    (values' := [setCode (set.map incrSub)]) (.cons (paper_Incr_reduces set) .nil)
    (ap "Max" [ap "Add" [ap "cst" [ap "nil" [.con "N_code"], ap "s" [zeroN]], .var 0]])
  simp only [succ, zeroN] at computed inner
  inst_simp at computed inner
  exact (computed : Reduces paperLevelTheory (succ (normalCode set)) _).trans
    (inner.trans (Reduces.app .refl (paper_Add_reduces (.cst [] 1) (set.map incrSub))))

theorem paper_max_reduces (first second : List Sublevel) :
    Reduces paperLevelTheory (ap "max" [normalCode first, normalCode second])
      (normalCode (first.foldl (fun accumulated element => addSubPaper element accumulated) second)) := by
  have computed := reducesPaper_inst (skeleton := ap "max" [ap "Max" [.var 0], ap "Max" [.var 1]])
    (result := ap "Max" [ap "fold" [.con "S_code", ap "set" [.con "S_code"], .con "Add", .var 0, .var 1]])
    (fuel := 2) (by decide +kernel) [setCode first, setCode second]
    (closed_of_mem (by simp [setCode_closed])) rfl rfl
  inst_simp at computed
  exact (computed : Reduces paperLevelTheory (ap "max" [normalCode first, normalCode second]) _).trans
    (Reduces.app .refl (paper_foldAdd_reduces first second))

theorem paper_imax_reduces (first second : List Sublevel) :
    Reduces paperLevelTheory (imax (normalCode first) (normalCode second))
      (normalCode (imaxSetWith addSubPaper first second)) := by
  cases second with
  | nil =>
      have computed := reducesPaper_inst
        (skeleton := imax (ap "Max" [.var 0]) (ap "Max" [ap "nil" [.con "S_code"]]))
        (result := ap "Max" [ap "nil" [.con "S_code"]]) (fuel := 1) (by decide +kernel) [setCode first]
        (closed_of_mem (by simp [setCode_closed])) rfl rfl
      simp only [imax] at computed
      inst_simp at computed
      exact computed
  | cons head rest =>
      have computed := reducesPaper_inst
        (skeleton := imax (ap "Max" [.var 0]) (ap "Max" [ap "cons" [.con "S_code", .var 1, .var 2]]))
        (result := ap "Max" [ap "fold" [.con "S_code", ap "set" [.con "S_code"],
          ap "FoldAddguard" [ap "cons" [.con "S_code", .var 1, .var 2]], .var 0,
          ap "cons" [.con "S_code", .var 1, .var 2]]]) (fuel := 2) (by decide +kernel)
        [setCode first, sublevelCode head, setCode rest]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      simp only [imax] at computed
      inst_simp at computed
      have folded := paper_foldFoldAddguard_reduces (head :: rest) first (head :: rest)
      rw [guardedSetWith_eq_fold] at folded
      exact (computed : Reduces paperLevelTheory
        (imax (normalCode first) (normalCode (head :: rest))) _).trans (Reduces.app .refl folded)

/-- **The normalization theorem for the paper's level theory**: for every
level, with any level variables, the paper's code reduces to the code of the
set computed with the paper's `Add` and the empty guard. -/
theorem paperCode_reduces_paperSet :
    ∀ level : LeanLevel,
      Reduces paperLevelTheory (paperCode level)
        (normalCode (normalSetWith addSubPaper unguardedLeaf level))
  | .zero => Reduces.of_evaluate paperLevelRules_linear (fuel := 1) (by decide +kernel)
  | .param _ => .refl
  | .succ level =>
      (Reduces.app .refl (paperCode_reduces_paperSet level)).trans (paper_succ_reduces _)
  | .max first second =>
      (Reduces.app (Reduces.app .refl (paperCode_reduces_paperSet first))
        (paperCode_reduces_paperSet second)).trans (paper_max_reduces _ _)
  | .imax first second =>
      (Reduces.app (Reduces.app .refl (paperCode_reduces_paperSet first))
        (paperCode_reduces_paperSet second)).trans (paper_imax_reduces _ _)

/-- **The same theorem for the corrected code**: with each level variable in
its own guard, the code of every level reduces, in the paper's level theory, to
the code of the set computed with the paper's `Add`. -/
theorem code_reduces_guardedPaperSet :
    ∀ level : LeanLevel,
      Reduces paperLevelTheory (code level) (normalCode (normalSetWith addSubPaper guardedLeaf level))
  | .zero => Reduces.of_evaluate paperLevelRules_linear (fuel := 1) (by decide +kernel)
  | .param _ => .refl
  | .succ level =>
      (Reduces.app .refl (code_reduces_guardedPaperSet level)).trans (paper_succ_reduces _)
  | .max first second =>
      (Reduces.app (Reduces.app .refl (code_reduces_guardedPaperSet first))
        (code_reduces_guardedPaperSet second)).trans (paper_max_reduces _ _)
  | .imax first second =>
      (Reduces.app (Reduces.app .refl (code_reduces_guardedPaperSet first))
        (code_reduces_guardedPaperSet second)).trans (paper_imax_reduces _ _)

/-- In the paper's level theory, two terms that reduce to the codes of two sets
of sublevels are convertible exactly when the two sets are one set. -/
theorem paper_conv_iff_of_reduces {left right : Term} {leftSet rightSet : List Sublevel}
    (leftReduces : Reduces paperLevelTheory left (normalCode leftSet))
    (rightReduces : Reduces paperLevelTheory right (normalCode rightSet)) :
    Conv paperLevelTheory left right ↔ leftSet = rightSet := by
  have rigid : ∀ name ∈ setConstructors, ¬ paperLevelTheory.Defines name :=
    setConstructors_rigid (by decide +kernel)
  have headed : paperLevelTheory.Headed := paperLevelTheory_orthogonal.leftAlgebraic.headed
  constructor
  · intro convertible
    by_contra distinct
    exact not_conv_of_normal paperLevelTheory_confluent (normalCode_normal headed rigid _)
      (normalCode_normal headed rigid _) (fun same => distinct (normalCode_injective same))
      (.trans _ _ _ (.symm _ _ leftReduces.conv) (.trans _ _ _ convertible rightReduces.conv))
  · intro same
    exact Joinable.conv ⟨_, leftReduces, same ▸ rightReduces⟩

/-- **The conversion of the paper's level theory, on the paper's codes, is
equality of the sets computed with the paper's `Add` and the empty guard**,
for all levels. -/
theorem conv_paperCode_iff {first second : LeanLevel} :
    Conv paperLevelTheory (paperCode first) (paperCode second) ↔
      normalSetWith addSubPaper unguardedLeaf first = normalSetWith addSubPaper unguardedLeaf second :=
  paper_conv_iff_of_reduces (paperCode_reduces_paperSet first) (paperCode_reduces_paperSet second)

/-- **The conversion of the paper's level theory, on the corrected codes, is
equality of the sets computed with the paper's `Add` and each variable in its
own guard**, for all levels. -/
theorem conv_code_paperLevelTheory_iff {first second : LeanLevel} :
    Conv paperLevelTheory (code first) (code second) ↔
      normalSetWith addSubPaper guardedLeaf first = normalSetWith addSubPaper guardedLeaf second :=
  paper_conv_iff_of_reduces (code_reduces_guardedPaperSet first) (code_reduces_guardedPaperSet second)

/-! ## The paper's rule on `Add` loses no value -/

theorem mem_addSubPaper (sublevel : Sublevel) :
    ∀ (set : List Sublevel) (other : Sublevel), other ∈ addSubPaper sublevel set →
      other = sublevel ∨ other ∈ set
  | [], other, member => by
      simp only [addSubPaper, List.mem_singleton] at member
      exact Or.inl member
  | head :: rest, other, member => by
      simp only [addSubPaper] at member
      split at member
      · exact Or.inr member
      · split at member
        · rcases mem_insertSorted cmpSub sublevel rest other member with same | inRest
          · exact Or.inl same
          · exact Or.inr (List.mem_cons_of_mem _ inRest)
        · rcases mem_insertSorted cmpSub head _ other member with same | inInner
          · exact Or.inr (List.mem_cons.mpr (Or.inl same))
          · rcases mem_addSubPaper sublevel rest other inInner with same | inRest
            · exact Or.inl same
            · exact Or.inr (List.mem_cons_of_mem _ inRest)

theorem setEval_addSubPaper {valuation : Nat → Nat} {sublevel : Sublevel}
    (admissible : Admissible valuation sublevel) :
    ∀ {set : List Sublevel}, (∀ other ∈ set, Admissible valuation other) →
      setEval valuation (addSubPaper sublevel set) =
        max (sublevelEval valuation sublevel) (setEval valuation set)
  | [], _ => rfl
  | head :: rest, admissibles => by
      have headAdmissible := admissibles head List.mem_cons_self
      have ih := setEval_addSubPaper admissible (set := rest) fun other member =>
        admissibles other (List.mem_cons_of_mem _ member)
      simp only [addSubPaper]
      by_cases dominated : leSub sublevel head = true
      · have below := leSub_sound headAdmissible dominated
        rw [if_pos dominated]
        simp only [setEval_cons]
        omega
      · rw [if_neg dominated]
        by_cases dominates : leSub head sublevel = true
        · have below := leSub_sound admissible dominates
          rw [if_pos dominates, setEval_insertSorted]
          simp only [setEval_cons]
          omega
        · rw [if_neg dominates, setEval_insertSorted, ih]
          simp only [setEval_cons]
          omega

/-- **The paper's rule on `Add` is sound at every valuation**: keeping a
dominated element changes no value. -/
theorem addSubPaper_sound (valuation : Nat → Nat) : InsertionSound valuation addSubPaper where
  admissible := fun {sublevel set} admissible admissibles other member => by
    rcases mem_addSubPaper sublevel set other member with same | inSet
    · rw [same]
      exact admissible
    · exact admissibles other inSet
  value := fun admissible admissibles => setEval_addSubPaper admissible admissibles

/-- **Every distinction that the paper's level theory loses is at a valuation
with a zero**: two levels whose codes it converts have equal values at every
valuation that is positive everywhere. -/
theorem eval_eq_of_conv_paperCode {first second : LeanLevel}
    (convertible : Conv paperLevelTheory (paperCode first) (paperCode second))
    {valuation : Nat → Nat} (positive : ∀ index, valuation index ≠ 0) :
    first.eval valuation = second.eval valuation := by
  rw [← setEval_unguarded (addSubPaper_sound valuation) positive first,
    ← setEval_unguarded (addSubPaper_sound valuation) positive second,
    conv_paperCode_iff.mp convertible]

/-! ## The guard corrected alone: the paper's rule on `Add` loses nothing -/

/-- **With the paper's `Add` and each variable in its own guard, the computed
set has the value of the level**, at every valuation. -/
theorem setEval_guardedPaperSet (valuation : Nat → Nat) (level : LeanLevel) :
    setEval valuation (normalSetWith addSubPaper guardedLeaf level) = level.eval valuation :=
  (normalSetWith_spec (addSubPaper_sound valuation) (guardedLeaf_admissible valuation)
    (sublevelEval_guardedLeaf valuation) level).2

/-- **With the code of a variable corrected, the paper's level theory converts
the codes of equivalent levels only**: the paper's rule on `Add` loses no
distinction. -/
theorem equiv_of_conv_code_paperLevelTheory {first second : LeanLevel}
    (convertible : Conv paperLevelTheory (code first) (code second)) :
    LeanLevel.Equiv first second := fun valuation => by
  rw [← setEval_guardedPaperSet valuation first, ← setEval_guardedPaperSet valuation second,
    conv_code_paperLevelTheory_iff.mp convertible]

#print axioms Step.transfer
#print axioms Reduces.transfer
#print axioms Reduces.addFree_transfer
#print axioms paper_Add_reduces
#print axioms paperCode_reduces_paperSet
#print axioms conv_paperCode_iff
#print axioms code_reduces_guardedPaperSet
#print axioms conv_code_paperLevelTheory_iff
#print axioms equiv_of_conv_code_paperLevelTheory
#print axioms addSubPaper_sound
#print axioms eval_eq_of_conv_paperCode

end Mettapedia.GSLT.Dedukti.LeanMinus
