import Mettapedia.OSLF.Framework.BackwardSearchPlans
import Mettapedia.Logic.LP.NarrowingLift
import Mettapedia.Logic.LP.TotalUnification
import Mettapedia.Logic.LP.LinearUnification

/-!
# Symbolic predecessors of first-order rewriting, by backward narrowing

For a finite list of first-order rules, the states that step into the instances of a pattern `P`
are computed from `P` itself (`backward`). At every non-variable position of `P`, a copy of each
rule renamed apart from `P` has its right side unified with the subterm there; the most general
unifier rebuilds the position with the rule's left side. Each result is a pattern again.

- `backward_sound`: every instance of a result steps into an instance of `P`.
- `backward_complete`: when `P` is linear (`Term.Linear`: no variable occurs twice), every state that
  steps into an instance of `P` is an instance of a result, or an instance of `P` itself. The
  second case is a step inside the value of one of `P`'s variables.
- `backward_linear`: under rules with linear sides, the results at a linear pattern are linear, so
  every node a search generates from linear goals is linear and fair plans are complete
  (`answer_complete`).
- `presentation`: the backward-search presentation of these predecessors, for goals given by
  patterns. Its plans, saturation certificates and verdicts are those of
  `BackwardSearchPlans`; only the nodes are new.

The position split (`split_of_fill`) is the combinatorial core: a redex in an instance of `P` sits
at a non-variable position of `P`, or inside the value of one of its variables. The first case uses
the most general unifier of the total Martelli–Montanari algorithm (`unifyTotal_mgu`); renaming
apart uses fresh variables above every variable of `P` (`offset`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.BackwardNarrowing

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.FirstOrderRewriting (Context Equation Rewrite)
open Mettapedia.Logic.LP.Narrowing (mapContext mapContext_fill outsideVars)
open Mettapedia.Logic.LP.NarrowingLift (splice apply_onDomain apply_offDomain splice_fill)
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.BackwardSearch

/-- A first-order signature whose variables are numbers. -/
abbrev Signature (C F : Type) (arity : F → ℕ) : LPSignature :=
  ⟨C, ℕ, Empty, Empty.elim, F, arity⟩

variable {C F : Type} {arity : F → ℕ}

local notation "Sig" => Signature C F arity

instance : DecidableEq (Sig).vars := inferInstanceAs (DecidableEq ℕ)

/-! ## Positions -/

/-- Every position of a term: the context around it and the subterm there. -/
def splits : Term Sig → List (Context Sig × Term Sig)
  | .var v => [(.hole, .var v)]
  | .const c => [(.hole, .const c)]
  | .app f args => (.hole, .app f args) ::
      (List.finRange ((Sig).functionArity f)).flatMap fun i =>
        (splits (args i)).map fun split => (Context.app f args i split.1, split.2)

theorem splits_fill : ∀ (term : Term Sig) (split : Context Sig × Term Sig), split ∈ splits term →
    split.1.fill split.2 = term
  | .var v, split, member => by simp [splits] at member; subst member; rfl
  | .const c, split, member => by simp [splits] at member; subst member; rfl
  | .app f args, split, member => by
    simp only [splits, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at member
    rcases member with rfl | ⟨i, inner, innerMember, rfl⟩
    · rfl
    · simp only [Context.fill]
      rw [splits_fill (args i) inner innerMember, Function.update_eq_self]

theorem hole_mem_splits (term : Term Sig) : (Context.hole, term) ∈ splits term := by
  cases term <;> simp [splits]

theorem app_mem_splits {f : F} {args : Fin (arity f) → Term Sig} {i : Fin (arity f)}
    {split : Context Sig × Term Sig} (member : split ∈ splits (args i)) :
    (Context.app f args i split.1, split.2) ∈ splits (.app f args) := by
  simp only [splits, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  exact Or.inr ⟨i, split, member, rfl⟩

/-- **The position split.** A redex in an instance of a pattern sits at a non-variable position
of the pattern, or inside the value of one of its variables. -/
theorem split_of_fill (substitution : Subst Sig) :
    ∀ (outer : Context Sig) (pattern : Term Sig) (redex : Term Sig),
      substitution.applyTerm pattern = outer.fill redex →
      (∃ split ∈ splits pattern, (∀ v, split.2 ≠ .var v) ∧ substitution.applyTerm split.2 = redex ∧
          ∀ term, outer.fill term = (mapContext substitution split.1).fill term) ∨
        (∃ split ∈ splits pattern, ∃ v, split.2 = .var v ∧ ∃ inner : Context Sig,
          substitution v = inner.fill redex ∧
            ∀ term, outer.fill term = (mapContext substitution split.1).fill (inner.fill term))
  | .hole, pattern, redex, same => by
    cases pattern with
    | var v =>
      exact Or.inr ⟨(.hole, .var v), hole_mem_splits _, v, rfl, .hole, same, fun _ => rfl⟩
    | const c =>
      exact Or.inl ⟨(.hole, .const c), hole_mem_splits _, fun _ h => by injection h, same, fun _ => rfl⟩
    | app f args =>
      exact Or.inl ⟨(.hole, .app f args), hole_mem_splits _, fun _ h => by injection h, same, fun _ => rfl⟩
  | .app g others position inner, pattern, redex, same => by
    cases pattern with
    | var v =>
      exact Or.inr ⟨(.hole, .var v), hole_mem_splits _, v, rfl, .app g others position inner, same,
        fun _ => rfl⟩
    | const c =>
      simp [Subst.applyTerm, Context.fill] at same
    | app f args =>
      simp only [Subst.applyTerm_app, Context.fill] at same
      obtain ⟨headSame, argumentsSame⟩ := Term.app.inj same
      subst headSame
      have pointwise := congrFun (eq_of_heq argumentsSame)
      have atPosition : substitution.applyTerm (args position) = inner.fill redex := by
        simpa using pointwise position
      have elsewhere : ∀ j, j ≠ position → others j = substitution.applyTerm (args j) := by
        intro j different
        simpa [Function.update_of_ne different] using (pointwise j).symm
      have outsideAgrees : ∀ term : Term Sig,
          (Context.app f others position inner).fill term =
            Term.app f (Function.update (fun j => substitution.applyTerm (args j)) position (inner.fill term)) := by
        intro term
        simp only [Context.fill]
        congr 1
        funext j
        by_cases here : j = position
        · subst here; simp
        · simp [Function.update_of_ne here, elsewhere j here]
      rcases split_of_fill substitution inner (args position) redex atPosition with
        ⟨split, member, notVariable, atRedex, fills⟩ | ⟨split, member, v, isVariable, deeper, value, fills⟩
      · refine Or.inl ⟨(Context.app f args position split.1, split.2), app_mem_splits member, notVariable,
          atRedex, fun term => ?_⟩
        rw [outsideAgrees, fills term]
        rfl
      · refine Or.inr ⟨(Context.app f args position split.1, split.2), app_mem_splits member, v, isVariable,
          deeper, value, fun term => ?_⟩
        rw [outsideAgrees, fills term]
        rfl

/-! ## Renaming apart -/

/-- One above every variable of a term. -/
def offset (term : Term Sig) : ℕ := term.freeVars.sup id + 1

theorem lt_offset {term : Term Sig} {v : ℕ} (member : v ∈ term.freeVars) : v < offset term :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) member)

/-- Shift every variable up by an amount. -/
def shift (amount : ℕ) : Subst Sig := fun v => .var (v + amount)

theorem shift_freeVars (amount : ℕ) : ∀ (term : Term Sig) (v : ℕ),
    v ∈ ((shift amount).applyTerm term).freeVars → amount ≤ v
  | .var w, v, member => by
    simp [shift, Subst.applyTerm, Term.freeVars] at member
    omega
  | .const _, v, member => by simp [Subst.applyTerm, Term.freeVars] at member
  | .app f args, v, member => by
    simp only [Subst.applyTerm_app, Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and] at member
    obtain ⟨i, inside⟩ := member
    exact shift_freeVars amount (args i) v inside

/-- Undo a shift before a substitution. -/
def unshift (amount : ℕ) (substitution : Subst Sig) : Subst Sig := fun v => substitution (v - amount)

theorem unshift_shift (amount : ℕ) (substitution : Subst Sig) (term : Term Sig) :
    (unshift amount substitution).applyTerm ((shift amount).applyTerm term) = substitution.applyTerm term := by
  rw [← Subst.applyTerm_comp]
  apply Narrowing.Subst.applyTerm_congr
  intro v _
  simp [Subst.comp, shift, unshift]

/-- A copy of a rule with every variable shifted. -/
def rename (amount : ℕ) (rule : Equation Sig) : Equation Sig :=
  ⟨(shift amount).applyTerm rule.left, (shift amount).applyTerm rule.right⟩

/-! ## The backward step -/

def isVariable : Term Sig → Bool
  | .var _ => true
  | _ => false

theorem isVariable_false {term : Term Sig} (no : isVariable term = false) : ∀ v, term ≠ .var v := by
  intro v same
  subst same
  simp [isVariable] at no

variable (rules : List (Equation (Signature C F arity)))

/-- The states the rules rewrite. -/
def span : ReductionSpan (Term Sig) where
  Edge := {pair : Term Sig × Term Sig // Rewrite {rule | rule ∈ rules} pair.1 pair.2}
  source edge := edge.1.1
  target edge := edge.1.2

/-- The instances of a pattern. -/
def Instance (pattern state : Term Sig) : Prop := ∃ substitution : Subst Sig, substitution.applyTerm pattern = state

theorem instance_of_instance {general specific : Term Sig} (instance_ : Instance general specific)
    {state : Term Sig} (more : Instance specific state) : Instance general state := by
  obtain ⟨first, rfl⟩ := instance_
  obtain ⟨second, rfl⟩ := more
  exact ⟨second ∘ₛ first, Subst.applyTerm_comp _ _ _⟩

variable {rules}

/-! ## Completeness at linear patterns -/

/-- Substitutions that agree outside a context act alike on it. -/
theorem mapContext_congr {first second : Subst Sig} :
    ∀ (context : Context Sig), (∀ v ∈ outsideVars context, first v = second v) →
      ∀ term, (mapContext first context).fill term = (mapContext second context).fill term
  | .hole, _, _ => rfl
  | .app f args position inner, agree, term => by
    simp only [mapContext, Context.fill]
    congr 1
    funext j
    by_cases here : j = position
    · subst here
      simp only [Function.update_self]
      exact mapContext_congr inner (fun v member => agree v (by
        simp only [outsideVars, Finset.mem_union]; exact Or.inr member)) term
    · simp only [Function.update_of_ne here]
      apply Narrowing.Subst.applyTerm_congr
      intro v member
      apply agree
      simp only [outsideVars, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact Or.inl ⟨j, here, member⟩

theorem outsideVars_lt {pattern : Term Sig} {split : Context Sig × Term Sig}
    (member : split ∈ splits pattern) {v : ℕ} (inside : v ∈ outsideVars split.1) : v < offset pattern := by
  apply lt_offset
  rw [← splits_fill pattern split member]
  exact Mettapedia.Logic.LP.Narrowing.outsideVars_subset_fill split.1 split.2 inside

theorem hole_lt {pattern : Term Sig} {split : Context Sig × Term Sig}
    (member : split ∈ splits pattern) {v : ℕ} (inside : v ∈ split.2.freeVars) : v < offset pattern := by
  apply lt_offset
  rw [← splits_fill pattern split member]
  exact Mettapedia.Logic.LP.Narrowing.freeVars_hole_subset split.1 split.2 inside

variable [DecidableEq C] [DecidableEq F]

instance : DecidableEq (Sig).constants := inferInstanceAs (DecidableEq C)
instance : DecidableEq (Sig).functionSymbols := inferInstanceAs (DecidableEq F)

/-! ## Equality of terms -/

/-- Equality of terms is decidable. -/
def termDecEq : (first second : Term Sig) → Decidable (first = second)
  | .var x, .var y => decidable_of_iff (x = y) ⟨fun same => same ▸ rfl, fun same => by injection same⟩
  | .const x, .const y => decidable_of_iff (x = y) ⟨fun same => same ▸ rfl, fun same => by injection same⟩
  | .app f xs, .app g ys =>
    if headSame : f = g then by
      subst headSame
      have : ∀ i, Decidable (xs i = ys i) := fun i => termDecEq (xs i) (ys i)
      exact decidable_of_iff (∀ i, xs i = ys i)
        ⟨fun same => by rw [funext same], fun same i => by rw [eq_of_heq (Term.app.inj same).2]⟩
    else isFalse fun same => headSame (Term.app.inj same).1
  | .var _, .const _ => isFalse (by intro same; cases same)
  | .var _, .app _ _ => isFalse (by intro same; cases same)
  | .const _, .var _ => isFalse (by intro same; cases same)
  | .const _, .app _ _ => isFalse (by intro same; cases same)
  | .app _ _, .var _ => isFalse (by intro same; cases same)
  | .app _ _, .const _ => isFalse (by intro same; cases same)

instance : DecidableEq (Term Sig) := termDecEq

variable (rules) in
/-- **The symbolic predecessors of a pattern**: at every non-variable position, every rule
renamed apart has its right side unified with the subterm, and the position is rebuilt with its
left side. -/
def backward (pattern : Term Sig) : List (Term Sig) :=
  (splits pattern).flatMap fun split =>
    if isVariable split.2 then [] else
      rules.filterMap fun rule =>
        (unifyTotal [((rename (offset pattern) rule).right, split.2)]).map fun unifier =>
          unifier.applyTerm (split.1.fill (rename (offset pattern) rule).left)


theorem mem_backward {pattern previous : Term Sig} (member : previous ∈ backward rules pattern) :
    ∃ split ∈ splits pattern, (∀ v, split.2 ≠ .var v) ∧ ∃ rule ∈ rules, ∃ unifier : Subst Sig,
      unifyTotal [((rename (offset pattern) rule).right, split.2)] = some unifier ∧
        previous = unifier.applyTerm (split.1.fill (rename (offset pattern) rule).left) := by
  simp only [backward, List.mem_flatMap] at member
  obtain ⟨split, splitMember, inside⟩ := member
  by_cases variable_ : isVariable split.2 = true
  · simp [variable_] at inside
  · simp only [variable_, Bool.false_eq_true, if_false, List.mem_filterMap, Option.map_eq_some_iff] at inside
    obtain ⟨rule, ruleMember, unifier, unified, rfl⟩ := inside
    exact ⟨split, splitMember, isVariable_false (Bool.eq_false_iff.mpr variable_), rule, ruleMember, unifier,
      unified, rfl⟩

/-- **Soundness**: every instance of a symbolic predecessor steps into an instance of the pattern. -/
theorem backward_sound {pattern previous : Term Sig} (member : previous ∈ backward rules pattern)
    (state : Term Sig) (instance_ : Instance previous state) :
    derivedDiamond (span rules) (Instance pattern) state := by
  obtain ⟨split, splitMember, _, rule, ruleMember, unifier, unified, rfl⟩ := mem_backward member
  obtain ⟨substitution, rfl⟩ := instance_
  have unifies : unifier.applyTerm (rename (offset pattern) rule).right = unifier.applyTerm split.2 :=
    unifyTotal_sound _ unifier unified _ (List.mem_singleton_self _)
  let total : Subst Sig := substitution ∘ₛ unifier
  have step : Rewrite {rule | rule ∈ rules}
      ((mapContext total split.1).fill ((total ∘ₛ shift (offset pattern)).applyTerm rule.left))
      ((mapContext total split.1).fill ((total ∘ₛ shift (offset pattern)).applyTerm rule.right)) :=
    Rewrite.rule rule ruleMember _ _
  have source : (mapContext total split.1).fill ((total ∘ₛ shift (offset pattern)).applyTerm rule.left) =
      substitution.applyTerm (unifier.applyTerm (split.1.fill (rename (offset pattern) rule).left)) := by
    rw [Subst.applyTerm_comp, ← mapContext_fill, ← Subst.applyTerm_comp]
    rfl
  have target : (mapContext total split.1).fill ((total ∘ₛ shift (offset pattern)).applyTerm rule.right) =
      total.applyTerm pattern := by
    rw [Subst.applyTerm_comp, ← mapContext_fill]
    conv_rhs => rw [← splits_fill pattern split splitMember]
    show total.applyTerm (split.1.fill (rename (offset pattern) rule).right) = total.applyTerm (split.1.fill split.2)
    simp only [total, Subst.applyTerm_comp, mapContext_fill, unifies]
  rw [source, target] at step
  exact ⟨⟨(_, _), step⟩, rfl, ⟨total, rfl⟩⟩

/-- **Completeness**: at a linear pattern, a state that steps into an instance is an instance of a
symbolic predecessor, or, when the pattern has variables, an instance of the pattern itself. -/
theorem backward_complete {pattern : Term Sig} (linear : pattern.Linear) (state : Term Sig)
    (steps : derivedDiamond (span rules) (Instance pattern) state) :
    (pattern.freeVars.Nonempty ∧ Instance pattern state) ∨
      ∃ previous ∈ backward rules pattern, Instance previous state := by
  obtain ⟨⟨⟨source, target⟩, rewrite⟩, rfl, ⟨substitution, intoPattern⟩⟩ := steps
  change Rewrite _ source target at rewrite
  change substitution.applyTerm pattern = target at intoPattern
  cases rewrite with
  | rule rule ruleMember ruleSubstitution outer =>
    rcases split_of_fill substitution outer pattern _ intoPattern with
      ⟨split, member, notVariable, atRedex, fills⟩ | ⟨split, member, v, isVar, inner, value, fills⟩
    · -- at a non-variable position: the most general unifier covers the step
      right
      let amount := offset pattern
      let renamed := rename amount rule
      let domain := renamed.left.freeVars ∪ renamed.right.freeVars
      let combined : Subst Sig := splice domain (unshift amount ruleSubstitution) substitution
      have renamedHigh : ∀ v ∈ domain, amount ≤ v := by
        intro v inside
        rcases Finset.mem_union.mp inside with leftSide | rightSide
        · exact shift_freeVars amount rule.left v leftSide
        · exact shift_freeVars amount rule.right v rightSide
      have holeAvoids : ∀ v ∈ split.2.freeVars, v ∉ domain := fun v inside within =>
        absurd (renamedHigh v within) (Nat.not_le.mpr (hole_lt member inside))
      have renamedRight : renamed.right = (shift amount).applyTerm rule.right := rfl
      have renamedLeft : renamed.left = (shift amount).applyTerm rule.left := rfl
      have unifies : combined.applyTerm renamed.right = combined.applyTerm split.2 := by
        rw [apply_onDomain (fun v inside => Finset.mem_union_right _ inside), apply_offDomain holeAvoids,
          renamedRight, unshift_shift, atRedex]
      obtain ⟨unifier, unified⟩ := unifyTotal_complete
        (equations := [(renamed.right, split.2)]) ⟨combined, by
          intro pair inside
          rw [List.mem_singleton.mp inside]
          exact unifies⟩
      obtain ⟨later, laterSame⟩ := unifyTotal_mgu _ unifier unified combined (by
        intro pair inside
        rw [List.mem_singleton.mp inside]
        exact unifies)
      refine ⟨unifier.applyTerm (split.1.fill renamed.left), ?_, later, ?_⟩
      · simp only [backward, List.mem_flatMap]
        refine ⟨split, member, ?_⟩
        have notVar : isVariable split.2 = false := by
          cases hsplit : split.2 with
          | var w => exact absurd hsplit (notVariable w)
          | const _ => rfl
          | app _ _ => rfl
        simp only [notVar, Bool.false_eq_true, if_false, List.mem_filterMap, Option.map_eq_some_iff]
        exact ⟨rule, ruleMember, unifier, unified, rfl⟩
      · change _ = outer.fill (ruleSubstitution.applyTerm rule.left)
        rw [← Subst.applyTerm_comp]
        have sameSubst : later ∘ₛ unifier = combined := by
          funext v
          exact (laterSame v).symm
        rw [sameSubst, splice_fill split.1 renamed.left domain _ _
          (fun v inside => Finset.mem_union_left _ inside)
          (fun v inside within => absurd (renamedHigh v within) (Nat.not_le.mpr (outsideVars_lt member inside))),
          renamedLeft, unshift_shift, ← fills]
    · -- inside the value of a variable: the step stays among the pattern's instances
      left
      have alone : v ∉ outsideVars split.1 := Term.Linear.not_mem_outside (by
        rw [← isVar, splits_fill pattern split member]
        exact linear)
      refine ⟨⟨v, ?_⟩, ?_⟩
      · rw [← splits_fill pattern split member, isVar]
        exact Narrowing.freeVars_hole_subset split.1 (.var v) (by simp [Term.freeVars])
      let value := inner.fill (ruleSubstitution.applyTerm rule.left)
      let updated : Subst Sig := Function.update substitution v value
      refine ⟨updated, ?_⟩
      change _ = outer.fill (ruleSubstitution.applyTerm rule.left)
      have agree := mapContext_congr (first := updated) (second := substitution) split.1 (by
          intro w inside
          have different : w ≠ v := fun same => alone (same ▸ inside)
          exact Function.update_of_ne different _ _)
      calc updated.applyTerm pattern
          = updated.applyTerm (split.1.fill (.var v)) := by
            rw [← isVar, splits_fill pattern split member]
        _ = (mapContext updated split.1).fill (updated.applyTerm (.var v)) :=
            Narrowing.mapContext_fill _ _ _
        _ = (mapContext substitution split.1).fill (inner.fill (ruleSubstitution.applyTerm rule.left)) := by
            rw [agree, Subst.applyTerm_var]
            exact congrArg _ (Function.update_self _ _ _)
        _ = outer.fill (ruleSubstitution.applyTerm rule.left) := (fills _).symm

theorem backward_complete' {pattern : Term Sig} (linear : pattern.Linear) (state : Term Sig)
    (steps : derivedDiamond (span rules) (Instance pattern) state) :
    Instance pattern state ∨ ∃ previous ∈ backward rules pattern, Instance previous state :=
  (backward_complete linear state steps).imp_left And.right

/-! ## Linearity is preserved -/

variable (rules) in
/-- Rules whose two sides are linear. -/
def LinearRules : Prop := ∀ rule ∈ rules, rule.left.Linear ∧ rule.right.Linear

omit [DecidableEq C] [DecidableEq F] in
theorem LinearRules.of_check
    (checked : (rules.all fun rule => rule.left.linearCheck && rule.right.linearCheck) = true) :
    LinearRules rules := fun rule member => by
  obtain ⟨left, right⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked rule member)
  exact ⟨(Term.linearCheck_iff _).mp left, (Term.linearCheck_iff _).mp right⟩

/-- **Linearity is preserved**: under linear rules, every symbolic predecessor of a linear pattern
is linear. The unifier overlays the renamed right side on the subterm, sending each variable of the
right side to a linear term and no two to terms with a shared variable. -/
theorem backward_linear (rulesLinear : LinearRules rules) {pattern previous : Term Sig} (linear : pattern.Linear)
    (member : previous ∈ backward rules pattern) : previous.Linear := by
  obtain ⟨split, splitMember, _, rule, ruleMember, unifier, unified, rfl⟩ := mem_backward member
  have filled : (split.1.fill split.2).Linear := by
    rw [splits_fill pattern split splitMember]
    exact linear
  obtain ⟨holeLinear, holeApart⟩ := Term.Linear.of_fill split.1 filled
  have shifted : ∀ term : Term Sig, term.Linear → ((shift (offset pattern)).applyTerm term).Linear :=
    fun term termLinear => Term.Linear.applyTerm _ term termLinear (fun _ _ => trivial) fun v _ w _ different => by
      show Disjoint ({v + offset pattern} : Finset ℕ) {w + offset pattern}
      exact Finset.disjoint_singleton.mpr fun same => different (Nat.add_right_cancel same)
  have high : ∀ (term : Term Sig), ∀ v ∈ ((shift (offset pattern)).applyTerm term).freeVars, offset pattern ≤ v :=
    shift_freeVars (offset pattern)
  have holeLow : ∀ v ∈ split.2.freeVars, v < offset pattern := fun v inside => hole_lt splitMember inside
  have outsideLow : ∀ v ∈ outsideVars split.1, v < offset pattern :=
    fun v inside => outsideVars_lt splitMember inside
  have equationsLinear : LinearEquations [((rename (offset pattern) rule).right, split.2)] := by
    refine ⟨fun equation inside => ?_, List.pairwise_singleton _ _⟩
    rw [List.mem_singleton.mp inside]
    exact ⟨shifted rule.right (rulesLinear rule ruleMember).2, holeLinear,
      Finset.disjoint_left.mpr fun v inRight inHole =>
        absurd (high rule.right v inRight) (Nat.not_le.mpr (holeLow v inHole))⟩
  have overlay := unifyTotal_overlay _ unifier unified equationsLinear
  have relevant := unifyTotal_relevantIdempotent _ unifier unified
  have contextLinear : (split.1.fill (rename (offset pattern) rule).left).Linear :=
    Term.Linear.fill split.1 filled (shifted rule.left (rulesLinear rule ruleMember).1)
      (Finset.disjoint_left.mpr fun v inLeft outside =>
        absurd (high rule.left v inLeft) (Nat.not_le.mpr (outsideLow v outside)))
  have leftOf : ∀ x ∈ (split.1.fill (rename (offset pattern) rule).left).freeVars,
      x ∈ eqVars [((rename (offset pattern) rule).right, split.2)] →
        LeftVar [((rename (offset pattern) rule).right, split.2)] x := by
    intro x inside mentioned
    simp only [eqVars, Finset.union_empty, Finset.mem_union] at mentioned
    rcases mentioned with inRight | inHole
    · exact ⟨_, List.mem_singleton_self _, inRight⟩
    · exfalso
      rcases Finset.mem_union.mp (freeVars_fill_subset split.1 _ inside) with inLeft | outside
      · exact absurd (high rule.left x inLeft) (Nat.not_le.mpr (holeLow x inHole))
      · exact Finset.disjoint_left.mp holeApart inHole outside
  apply Term.Linear.applyTerm unifier _ contextLinear
  · intro x inside
    by_cases mentioned : x ∈ eqVars [((rename (offset pattern) rule).right, split.2)]
    · exact (overlay x (leftOf x inside mentioned)).1
    · rw [relevant.fixes x mentioned]
      trivial
  · intro x xInside y yInside different
    by_cases xMentioned : x ∈ eqVars [((rename (offset pattern) rule).right, split.2)] <;>
      by_cases yMentioned : y ∈ eqVars [((rename (offset pattern) rule).right, split.2)]
    · exact (overlay x (leftOf x xInside xMentioned)).2 y (leftOf y yInside yMentioned) different
    · rw [relevant.fixes y yMentioned]
      refine Finset.disjoint_left.mpr fun u inImage isY => ?_
      simp only [Term.freeVars, Finset.mem_singleton] at isY
      subst isY
      exact yMentioned (relevant.range x xMentioned inImage)
    · rw [relevant.fixes x xMentioned]
      refine Finset.disjoint_left.mpr fun u isX inImage => ?_
      simp only [Term.freeVars, Finset.mem_singleton] at isX
      subst isX
      exact xMentioned (relevant.range y yMentioned inImage)
    · rw [relevant.fixes x xMentioned, relevant.fixes y yMentioned]
      simpa [Term.freeVars] using different

/-! ## The presentation -/

variable (rules) in
/-- **Backward search by narrowing**, for goals given by patterns: nodes are patterns, the good
nodes are the linear ones. -/
def presentation (goals : List (Term Sig)) :
    Presentation (span rules) (fun state => ∃ goal ∈ goals, Instance goal state) (Term Sig) where
  denote := Instance
  seeds := goals
  predecessors := backward rules
  seeds_exact _ := Iff.rfl
  good pattern := pattern.Linear
  predecessors_sound _ _ member state holds := backward_sound member state holds
  predecessors_complete _ linear state holds := backward_complete' linear state holds

/-! ## Decidable checks -/

/-- Whether a term is an instance of a pattern: rename the pattern apart, unify, and check that the
term is untouched. -/
def instanceOf (general specific : Term Sig) : Bool :=
  match unifyTotal [((shift (offset specific)).applyTerm general, specific)] with
  | some unifier => decide (unifier.applyTerm specific = specific)
  | none => false

theorem instance_of_check {general specific : Term Sig} (checked : instanceOf general specific = true) :
    Instance general specific := by
  unfold instanceOf at checked
  split at checked
  · rename_i unifier unified
    have fixed : unifier.applyTerm specific = specific := of_decide_eq_true checked
    have unifies := unifyTotal_sound _ unifier unified _ (List.mem_singleton_self _)
    refine ⟨unifier ∘ₛ shift (offset specific), ?_⟩
    rw [Subst.applyTerm_comp]
    exact unifies.trans fixed
  · cases checked

/-- A term without variables. -/
def Ground (term : Term Sig) : Prop := term.freeVars = ∅

omit [DecidableEq C] [DecidableEq F] in
theorem ground_fixed {term : Term Sig} (ground : Ground term) (substitution : Subst Sig) :
    substitution.applyTerm term = term :=
  Narrowing.Subst.applyTerm_id_of_fixed fun v member => by
    rw [ground] at member
    exact absurd member (Finset.notMem_empty v)

omit [DecidableEq C] [DecidableEq F] in
theorem instance_ground {term : Term Sig} (ground : Ground term) (state : Term Sig) :
    Instance term state ↔ state = term := by
  constructor
  · rintro ⟨substitution, rfl⟩
    exact ground_fixed ground substitution
  · rintro rfl
    exact ⟨Subst.id _, Subst.applyTerm_id _⟩

/-- **The instance check is complete at ground terms.** -/
theorem instanceOf_ground {general specific : Term Sig} (ground : Ground specific)
    (instance_ : Instance general specific) : instanceOf general specific = true := by
  obtain ⟨substitution, rfl⟩ := instance_
  let amount := offset (substitution.applyTerm general)
  let combined : Subst Sig := unshift amount substitution
  have unifies : combined.applyTerm ((shift amount).applyTerm general) =
      combined.applyTerm (substitution.applyTerm general) := by
    rw [unshift_shift, ground_fixed ground]
  obtain ⟨unifier, unified⟩ := unifyTotal_complete
    (equations := [((shift amount).applyTerm general, substitution.applyTerm general)]) ⟨combined, by
      intro pair inside
      rw [List.mem_singleton.mp inside]
      exact unifies⟩
  unfold instanceOf
  rw [unified]
  exact decide_eq_true (ground_fixed ground unifier)

variable (rules) in
/-- The covering test and the goodness test of the presentation. -/
def covering (goals : List (Term Sig)) : (presentation rules goals).Covering where
  covers node others := others.any fun other => instanceOf other node
  sound node others covered state holds := by
    obtain ⟨other, member, checked⟩ := List.any_eq_true.mp covered
    exact ⟨other, member, instance_of_instance (instance_of_check checked) holds⟩
  isGood := Term.linearCheck
  isGood_sound _ checked := (Term.linearCheck_iff _).mp checked

variable (rules) in
/-- **Read a backward search** at a state: `reaches`, `cannotReach` or `unknown`. -/
def answer (goals : List (Term Sig)) (scheduler : Mettapedia.GSLT.Core.BranchingTemporal.Scheduler (Term Sig))
    (fuel : Nat) (state : Term Sig) : Presentation.Answer :=
  (presentation rules goals).answer scheduler (covering rules goals) instanceOf fuel state

theorem answer_reaches {goals : List (Term Sig)} {scheduler : Mettapedia.GSLT.Core.BranchingTemporal.Scheduler (Term Sig)}
    {fuel : Nat} {state : Term Sig} (read : answer rules goals scheduler fuel state = .reaches) :
    Reaches (span rules) (fun state => ∃ goal ∈ goals, Instance goal state) state :=
  Presentation.answer_reaches (presentation := presentation rules goals) (member := instanceOf)
    (fun _ _ checked => instance_of_check checked) read

/-- **`cannotReach` at a ground state is a theorem.** -/
theorem answer_cannotReach {goals : List (Term Sig)}
    {scheduler : Mettapedia.GSLT.Core.BranchingTemporal.Scheduler (Term Sig)} {fuel : Nat} {state : Term Sig}
    (ground : Ground state) (read : answer rules goals scheduler fuel state = .cannotReach) :
    ¬ Reaches (span rules) (fun state => ∃ goal ∈ goals, Instance goal state) state :=
  Presentation.answer_cannotReach (presentation := presentation rules goals) (member := instanceOf)
    (fun _ holds => instanceOf_ground ground holds) read

/-! ## The backward box -/

/-- **The backward box at a ground term has finitely many open premises**: every predecessor
satisfies a property exactly when every instance of every symbolic predecessor does. -/
theorem pastBox_iff {term : Term Sig} (ground : Ground term) (property : Term Sig → Prop) :
    derivedBox (span rules) property term ↔
      ∀ previous ∈ backward rules term, ∀ substitution : Subst Sig, property (substitution.applyTerm previous) := by
  constructor
  · intro holds previous member substitution
    obtain ⟨event, starts, intoTerm⟩ := backward_sound member _ ⟨substitution, rfl⟩
    rw [← starts]
    exact holds event ((instance_ground ground _).mp intoTerm)
  · intro premises event ends
    rcases backward_complete (Term.linear_of_freeVars_empty ground) (span rules |>.source event)
        ⟨event, rfl, (instance_ground ground _).mpr ends⟩ with ⟨nonempty, _⟩ | ⟨previous, member, substitution, same⟩
    · rw [ground] at nonempty
      exact absurd nonempty Finset.not_nonempty_empty
    · show property ((span rules).source event)
      rw [← same]
      exact premises previous member substitution

/-- What the backward-box check says. -/
inductive PastBox where
  | proved
  | refuted
  | unknown
  deriving DecidableEq, Repr

/-- Whether a term has no variables, decided. -/
def groundCheck (term : Term Sig) : Bool := decide (term.freeVars = ∅)

variable (rules) in
/-- **Check the backward box** of a property given by patterns: proved when every symbolic
predecessor is an instance of one of them; refuted when a ground predecessor is an instance of
none; unknown otherwise. -/
def pastBox (term : Term Sig) (types : List (Term Sig)) : PastBox :=
  if (backward rules term).all (fun previous => types.any fun type => instanceOf type previous) then .proved
  else if (backward rules term).any
      (fun previous => groundCheck previous && !(types.any fun type => instanceOf type previous)) then .refuted
  else .unknown

theorem pastBox_proved {term : Term Sig} (ground : Ground term) {types : List (Term Sig)}
    (read : pastBox rules term types = .proved) :
    derivedBox (span rules) (fun state => ∃ type ∈ types, Instance type state) term := by
  unfold pastBox at read
  split_ifs at read with covered
  apply (pastBox_iff ground _).mpr
  intro previous member substitution
  obtain ⟨type, typeMember, checked⟩ := List.any_eq_true.mp (List.all_eq_true.mp covered previous member)
  exact ⟨type, typeMember, instance_of_instance (instance_of_check checked) ⟨substitution, rfl⟩⟩

theorem pastBox_refuted {term : Term Sig} (ground : Ground term) {types : List (Term Sig)}
    (read : pastBox rules term types = .refuted) :
    ¬ derivedBox (span rules) (fun state => ∃ type ∈ types, Instance type state) term := by
  unfold pastBox at read
  split_ifs at read with covered witness
  intro holds
  obtain ⟨previous, member, bad⟩ := List.any_eq_true.mp witness
  obtain ⟨groundPrevious, uncovered⟩ := Bool.and_eq_true_iff.mp bad
  have previousGround : Ground previous := of_decide_eq_true (p := previous.freeVars = ∅) groundPrevious
  obtain ⟨type, typeMember, instance_⟩ := (pastBox_iff ground _).mp holds previous member (Subst.id _)
  rw [Subst.applyTerm_id] at instance_
  have checked := instanceOf_ground previousGround instance_
  simp only [Bool.not_eq_true', List.any_eq_false] at uncovered
  exact absurd checked (by simpa using uncovered type typeMember)


/-! ## Root steps -/

variable (rules) in
/-- The steps of the rules at the root. -/
def rootSpan : ReductionSpan (Term Sig) where
  Edge := {pair : Term Sig × Term Sig // ∃ rule ∈ rules, ∃ substitution : Subst Sig,
    substitution.applyTerm rule.left = pair.1 ∧ substitution.applyTerm rule.right = pair.2}
  source edge := edge.1.1
  target edge := edge.1.2

variable (rules) in
/-- **The symbolic predecessors of a pattern at the root**: every rule renamed apart has its right
side unified with the pattern; the result is its left side. -/
def backwardRoot (pattern : Term Sig) : List (Term Sig) :=
  if isVariable pattern then [] else
    rules.filterMap fun rule =>
      (unifyTotal [((rename (offset pattern) rule).right, pattern)]).map fun unifier =>
        unifier.applyTerm (rename (offset pattern) rule).left

theorem backwardRoot_sound {pattern previous : Term Sig} (member : previous ∈ backwardRoot rules pattern)
    (state : Term Sig) (instance_ : Instance previous state) :
    derivedDiamond (rootSpan rules) (Instance pattern) state := by
  unfold backwardRoot at member
  split_ifs at member with variable_
  · simp at member
  simp only [List.mem_filterMap, Option.map_eq_some_iff] at member
  obtain ⟨rule, ruleMember, unifier, unified, rfl⟩ := member
  obtain ⟨substitution, rfl⟩ := instance_
  have unifies : unifier.applyTerm (rename (offset pattern) rule).right = unifier.applyTerm pattern :=
    unifyTotal_sound _ unifier unified _ (List.mem_singleton_self _)
  let total : Subst Sig := substitution ∘ₛ unifier ∘ₛ shift (offset pattern)
  refine ⟨⟨(_, total.applyTerm rule.right), rule, ruleMember, total, ?_, rfl⟩, rfl, ⟨substitution ∘ₛ unifier, ?_⟩⟩
  · simp only [total, Subst.applyTerm_comp]
    rfl
  · simp only [total, Subst.applyTerm_comp]
    exact congrArg substitution.applyTerm unifies.symm

/-- **Completeness at the root**, for every pattern: a state that steps at the root into an
instance is an instance of a symbolic predecessor, or the pattern is a variable. -/
theorem backwardRoot_complete {pattern : Term Sig} (state : Term Sig)
    (steps : derivedDiamond (rootSpan rules) (Instance pattern) state) :
    (isVariable pattern = true ∧ Instance pattern state) ∨
      ∃ previous ∈ backwardRoot rules pattern, Instance previous state := by
  obtain ⟨⟨⟨source, target⟩, rule, ruleMember, ruleSubstitution, isSource, isTarget⟩, rfl,
    ⟨substitution, intoPattern⟩⟩ := steps
  change substitution.applyTerm pattern = target at intoPattern
  change (isVariable pattern = true ∧ Instance pattern source) ∨
    ∃ previous ∈ backwardRoot rules pattern, Instance previous source
  by_cases variable_ : isVariable pattern = true
  · left
    refine ⟨variable_, ?_⟩
    cases pattern with
    | var v => exact ⟨fun _ => source, rfl⟩
    | const _ => simp [isVariable] at variable_
    | app _ _ => simp [isVariable] at variable_
  · right
    let amount := offset pattern
    let renamed := rename amount rule
    let domain := renamed.left.freeVars ∪ renamed.right.freeVars
    let combined : Subst Sig := splice domain (unshift amount ruleSubstitution) substitution
    have renamedHigh : ∀ v ∈ domain, amount ≤ v := by
      intro v inside
      rcases Finset.mem_union.mp inside with leftSide | rightSide
      · exact shift_freeVars amount rule.left v leftSide
      · exact shift_freeVars amount rule.right v rightSide
    have patternAvoids : ∀ v ∈ pattern.freeVars, v ∉ domain := fun v inside within =>
      absurd (renamedHigh v within) (Nat.not_le.mpr (lt_offset inside))
    have renamedRight : renamed.right = (shift amount).applyTerm rule.right := rfl
    have renamedLeft : renamed.left = (shift amount).applyTerm rule.left := rfl
    have unifies : combined.applyTerm renamed.right = combined.applyTerm pattern := by
      rw [apply_onDomain (fun v inside => Finset.mem_union_right _ inside), apply_offDomain patternAvoids,
        renamedRight, unshift_shift, isTarget, intoPattern]
    obtain ⟨unifier, unified⟩ := unifyTotal_complete
      (equations := [(renamed.right, pattern)]) ⟨combined, by
        intro pair inside
        rw [List.mem_singleton.mp inside]
        exact unifies⟩
    obtain ⟨later, laterSame⟩ := unifyTotal_mgu _ unifier unified combined (by
      intro pair inside
      rw [List.mem_singleton.mp inside]
      exact unifies)
    refine ⟨unifier.applyTerm renamed.left, ?_, later, ?_⟩
    · unfold backwardRoot
      rw [if_neg variable_]
      simp only [List.mem_filterMap, Option.map_eq_some_iff]
      exact ⟨rule, ruleMember, unifier, unified, rfl⟩
    · rw [← Subst.applyTerm_comp]
      have sameSubst : later ∘ₛ unifier = combined := by
        funext v
        exact (laterSame v).symm
      rw [sameSubst, apply_onDomain (fun v inside => Finset.mem_union_left _ inside), renamedLeft,
        unshift_shift, isSource]

theorem presentation_allGood (rulesLinear : LinearRules rules) {goals : List (Term Sig)}
    (goalsLinear : ∀ goal ∈ goals, goal.Linear) : (presentation rules goals).AllGood := by
  intro node generated
  induction generated with
  | root member => exact goalsLinear _ member
  | successor _ child linear => exact backward_linear rulesLinear linear child

/-- **Fair plans eventually answer `reaches`** under linear rules, from linear goals. -/
theorem answer_complete (rulesLinear : LinearRules rules) {goals : List (Term Sig)}
    (goalsLinear : ∀ goal ∈ goals, goal.Linear) {scheduler : Mettapedia.GSLT.Core.BranchingTemporal.Scheduler (Term Sig)}
    (fair : Mettapedia.GSLT.Core.BranchingTemporal.FairFrom (presentation rules goals).system scheduler goals)
    {state : Term Sig} (ground : Ground state)
    (reaches : Reaches (span rules) (fun state => ∃ goal ∈ goals, Instance goal state) state) :
    ∃ fuel, answer rules goals scheduler fuel state = .reaches := by
  obtain ⟨fuel, event, member, holds⟩ :=
    Presentation.fair_complete (presentation_allGood rulesLinear goalsLinear) fair reaches
  refine ⟨fuel, ?_⟩
  unfold answer Presentation.answer
  rw [if_pos (List.any_eq_true.mpr ⟨event, member, instanceOf_ground ground holds⟩)]

variable (rules) in
/-- **Backward search at the root**: every node is good, so fair plans are complete. -/
def rootPresentation (goals : List (Term Sig)) :
    Presentation (rootSpan rules) (fun state => ∃ goal ∈ goals, Instance goal state) (Term Sig) where
  denote := Instance
  seeds := goals
  predecessors := backwardRoot rules
  seeds_exact _ := Iff.rfl
  good _ := True
  predecessors_sound _ _ member state holds := backwardRoot_sound member state holds
  predecessors_complete _ _ state holds := (backwardRoot_complete state holds).imp_left And.right

theorem rootPresentation_allGood (goals : List (Term Sig)) : (rootPresentation rules goals).AllGood :=
  fun _ _ => trivial

variable (rules) in
def rootCovering (goals : List (Term Sig)) : (rootPresentation rules goals).Covering where
  covers node others := others.any fun other => instanceOf other node
  sound node others covered state holds := by
    obtain ⟨other, member, checked⟩ := List.any_eq_true.mp covered
    exact ⟨other, member, instance_of_instance (instance_of_check checked) holds⟩
  isGood _ := true
  isGood_sound _ _ := trivial

variable (rules) in
/-- **Read a backward search at the root.** -/
def rootAnswer (goals : List (Term Sig)) (scheduler : Mettapedia.GSLT.Core.BranchingTemporal.Scheduler (Term Sig))
    (fuel : Nat) (state : Term Sig) : Presentation.Answer :=
  (rootPresentation rules goals).answer scheduler (rootCovering rules goals) instanceOf fuel state

theorem rootAnswer_reaches {goals : List (Term Sig)}
    {scheduler : Mettapedia.GSLT.Core.BranchingTemporal.Scheduler (Term Sig)} {fuel : Nat} {state : Term Sig}
    (read : rootAnswer rules goals scheduler fuel state = .reaches) :
    Reaches (rootSpan rules) (fun state => ∃ goal ∈ goals, Instance goal state) state :=
  Presentation.answer_reaches (presentation := rootPresentation rules goals) (member := instanceOf)
    (fun _ _ checked => instance_of_check checked) read

theorem rootAnswer_cannotReach {goals : List (Term Sig)}
    {scheduler : Mettapedia.GSLT.Core.BranchingTemporal.Scheduler (Term Sig)} {fuel : Nat} {state : Term Sig}
    (ground : Ground state) (read : rootAnswer rules goals scheduler fuel state = .cannotReach) :
    ¬ Reaches (rootSpan rules) (fun state => ∃ goal ∈ goals, Instance goal state) state :=
  Presentation.answer_cannotReach (presentation := rootPresentation rules goals) (member := instanceOf)
    (fun _ holds => instanceOf_ground ground holds) read

/-- **Fair plans eventually answer `reaches` at the root**, with no condition on the patterns. -/
theorem rootAnswer_complete {goals : List (Term Sig)}
    {scheduler : Mettapedia.GSLT.Core.BranchingTemporal.Scheduler (Term Sig)}
    (fair : Mettapedia.GSLT.Core.BranchingTemporal.FairFrom (rootPresentation rules goals).system scheduler goals)
    {state : Term Sig} (ground : Ground state)
    (reaches : Reaches (rootSpan rules) (fun state => ∃ goal ∈ goals, Instance goal state) state) :
    ∃ fuel, rootAnswer rules goals scheduler fuel state = .reaches := by
  obtain ⟨fuel, event, member, holds⟩ :=
    Presentation.fair_complete (rootPresentation_allGood goals) fair reaches
  refine ⟨fuel, ?_⟩
  unfold rootAnswer Presentation.answer
  rw [if_pos (List.any_eq_true.mpr ⟨event, member, instanceOf_ground ground holds⟩)]

end Mettapedia.OSLF.Framework.BackwardNarrowing
