import Mettapedia.GSLT.Dedukti.LeanMinusLevels

/-!
# Theorems 2 and 3 for the closed levels, in the theory with explicit substitution

For every closed level `l` (no level variable), the code `|l|` reduces in
the level theory `pureTheoryExplicit`, hence in every theory that contains it,
to `closedNormal (eval l)`: `Max ∅` for the value `0`, `Max {C ∅ n}` for a
value `n ≥ 1` (`code_reduces_closedNormal`).  These codes
are normal and pairwise distinct.  So, with confluence:

* **Theorem 3, closed levels** (`theorem3_closed`): equivalent closed levels
  have convertible codes, and the codes read in any frame, `sub fr |l|`, are
  convertible as well.
* **Theorem 2, closed levels** (`theorem2_closed`): two closed levels have
  convertible codes exactly when they are equivalent.

The proof computes with numerals that are not fixed: a reduction is computed
once on a term whose free variables stand for the numerals
(`evaluate`), and instantiated by `Step.subst`; the comparisons of two
numerals, where such a computation stops, are reduced by induction
(`cmpN_reduces`) and put back by `Reduces.instantiate`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 lookupBody)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## Reductions of terms with free variables, instantiated by closed terms -/

theorem Reduces.substClosed {theory : Theory} (closed : theory.ClosedBodies) {source target : Term}
    (reduces : Reduces theory source target) (index : Nat) (replacement : Term) :
    Reduces theory (subst index replacement source) (subst index replacement target) := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.subst closed index replacement)

/-- Replace the variables `0, 1, …` of a term by the values, one at a time. -/
def fill (values : List Term) (term : Term) : Term :=
  values.foldl (fun accumulated value => subst0 value accumulated) term

theorem Reduces.fill {theory : Theory} (closed : theory.ClosedBodies) :
    ∀ (values : List Term) {source target : Term}, Reduces theory source target →
      Reduces theory (Dedukti.LeanMinus.fill values source) (Dedukti.LeanMinus.fill values target)
  | [], _, _, reduces => reduces
  | value :: rest, _, _, reduces =>
      Reduces.fill closed rest (Reduces.substClosed closed reduces 0 value)

/-- A term without binders whose variables are below `bound`. -/
def flatBelow (bound : Nat) : Term → Bool
  | .var index => decide (index < bound)
  | .srt _ => true
  | .con _ => true
  | .app function argument => flatBelow bound function && flatBelow bound argument
  | .pi _ _ => false
  | .lam _ _ => false

theorem fill_cons (value : Term) (rest : List Term) (term : Term) :
    fill (value :: rest) term = fill rest (subst0 value term) :=
  rfl

theorem fill_closed {term : Term} (closed : Closed term) :
    ∀ values : List Term, fill values term = term
  | [] => rfl
  | value :: rest => by
      rw [fill_cons, show subst0 value term = term from closed.subst 0 value]
      exact fill_closed closed rest

theorem fill_app (function argument : Term) :
    ∀ values : List Term,
      fill values (.app function argument) = .app (fill values function) (fill values argument)
  | [] => rfl
  | value :: rest => by
      simp only [fill, List.foldl, subst0, subst]
      exact fill_app _ _ rest

theorem fill_con (name : String) : ∀ values : List Term, fill values (.con name) = .con name
  | [] => rfl
  | value :: rest => by
      simp only [fill, List.foldl, subst0, subst]
      exact fill_con name rest

theorem fill_srt (sort : Srt) : ∀ values : List Term, fill values (.srt sort) = .srt sort
  | [] => rfl
  | value :: rest => by
      simp only [fill, List.foldl, subst0, subst]
      exact fill_srt sort rest

theorem fill_var (values : List Term) (closed : ∀ value ∈ values, Closed value) :
    ∀ index, index < values.length → fill values (.var index) = assign values index := by
  induction values with
  | nil => intro index bound; simp at bound
  | cons value rest ih =>
      intro index bound
      cases index with
      | zero =>
          have computed : subst0 value (Term.var 0) = value := by simp [subst0, subst]
          rw [fill_cons, computed, fill_closed (closed value (List.mem_cons_self ..)) rest]
          rfl
      | succ index =>
          have computed : subst0 value (Term.var (index + 1)) = Term.var index := by
            simp [subst0, subst]
          rw [fill_cons, computed, ih (fun other member => closed other (List.mem_cons_of_mem _ member))
            index (by simp at bound; omega)]
          rfl

/-- **On a term without binders, filling is instantiation.** -/
theorem fill_eq_inst (values : List Term) (closed : ∀ value ∈ values, Closed value) :
    ∀ term : Term, flatBelow values.length term = true →
      fill values term = inst (assign values) term := by
  intro term
  induction term with
  | var index =>
      intro flat
      rw [fill_var values closed index (by simpa [flatBelow] using flat), inst_var]
  | srt sort => intro _; rw [fill_srt]; rfl
  | con name => intro _; rw [fill_con]; rfl
  | pi domain body _ _ => intro flat; simp [flatBelow] at flat
  | lam domain body _ _ => intro flat; simp [flatBelow] at flat
  | app function argument ihFunction ihArgument =>
      intro flat
      simp only [flatBelow, Bool.and_eq_true] at flat
      rw [fill_app, ihFunction flat.1, ihArgument flat.2, inst_app]

theorem pureRulesExplicit_linear : ∀ rule ∈ pureRulesExplicit, (patternVars rule.lhs).Nodup :=
  fun rule member => pureTheoryExplicit_orthogonal.leftLinear rule member

/-- A computed reduction of the level theory, as a reduction. -/
theorem reducesPure_of_evaluate {fuel : Nat} {source target : Term}
    (computed : evaluate pureSig pureRulesExplicit fuel source = target) :
    Reduces pureTheoryExplicit source target :=
  Reduces.of_evaluate pureRulesExplicit_linear computed

/-- **A computed reduction of a term with free variables, instantiated by
closed terms.** -/
theorem reducesPure_inst {skeleton result : Term} {fuel : Nat}
    (computed : evaluate pureSig pureRulesExplicit fuel skeleton = result) (values : List Term)
    (closed : ∀ value ∈ values, Closed value) (skeletonFlat : flatBelow values.length skeleton = true)
    (resultFlat : flatBelow values.length result = true) :
    Reduces pureTheoryExplicit (inst (assign values) skeleton) (inst (assign values) result) := by
  have filled := Reduces.fill pureTheoryExplicit_orthogonal.closedBodies values
    (reducesPure_of_evaluate computed)
  rwa [fill_eq_inst values closed skeleton skeletonFlat, fill_eq_inst values closed result resultFlat]
    at filled

/-! ## Numerals and their comparison -/

theorem numeral_closed : ∀ count : Nat, Closed (numeral count)
  | 0 => .con
  | count + 1 => .app .con (numeral_closed count)

/-- The comparison of two naturals, as the rules on `cmpN` compute it. -/
def cmpNat : Nat → Nat → Ordering
  | 0, 0 => .eq
  | _ + 1, 0 => .gt
  | 0, _ + 1 => .lt
  | first + 1, second + 1 => cmpNat first second

theorem cmpNat_eq_lt {first second : Nat} : cmpNat first second = .lt ↔ first < second := by
  induction first generalizing second with
  | zero => cases second <;> simp [cmpNat]
  | succ first ih => cases second <;> simp [cmpNat, ih]

theorem cmpNat_eq_gt {first second : Nat} : cmpNat first second = .gt ↔ second < first := by
  induction first generalizing second with
  | zero => cases second <;> simp [cmpNat]
  | succ first ih => cases second <;> simp [cmpNat, ih]

theorem cmpNat_eq_eq {first second : Nat} : cmpNat first second = .eq ↔ first = second := by
  induction first generalizing second with
  | zero => cases second <;> simp [cmpNat]
  | succ first ih => cases second <;> simp [cmpNat, ih]

/-- The code of a comparison. -/
def cmpCode : Ordering → Term
  | .lt => .con "lt"
  | .eq => .con "eq"
  | .gt => .con "gt"

/-- The code of a Boolean. -/
def boolCode : Bool → Term
  | true => .con "true"
  | false => .con "false"

theorem assign_closed {values : List Term} (closed : ∀ value ∈ values, Closed value) (index : Nat) :
    Closed (assign values index) := by
  unfold assign
  rw [List.getD_eq_getElem?_getD]
  cases found : values[index]? with
  | none => exact .con
  | some value => exact closed value (List.mem_of_getElem? found)

/-- **`cmpN` compares two numerals.** -/
theorem cmpN_reduces : ∀ first second : Nat,
    Reduces pureTheoryExplicit (ap "cmpN" [numeral first, numeral second])
      (cmpCode (cmpNat first second))
  | 0, 0 => reducesPure_of_evaluate (fuel := 1) (by decide +kernel)
  | 0, second + 1 => by
      have step := reducesPure_inst (skeleton := ap "cmpN" [zeroN, ap "s" [.var 0]]) (result := .con "lt")
        (fuel := 1) (by decide +kernel) [numeral second]
        (fun value member => by rw [List.mem_singleton.mp member]; exact numeral_closed _) rfl rfl
      simpa [ap, apT, assign, numeral, cmpNat, cmpCode, zeroN] using step
  | first + 1, 0 => by
      have step := reducesPure_inst (skeleton := ap "cmpN" [ap "s" [.var 0], zeroN]) (result := .con "gt")
        (fuel := 1) (by decide +kernel) [numeral first]
        (fun value member => by rw [List.mem_singleton.mp member]; exact numeral_closed _) rfl rfl
      simpa [ap, apT, assign, numeral, cmpNat, cmpCode, zeroN] using step
  | first + 1, second + 1 => by
      have step := reducesPure_inst (skeleton := ap "cmpN" [ap "s" [.var 0], ap "s" [.var 1]])
        (result := ap "cmpN" [.var 0, .var 1]) (fuel := 1) (by decide +kernel)
        [numeral first, numeral second]
        (fun value member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> exact numeral_closed _) rfl rfl
      have inner := cmpN_reduces first second
      simp only [ap, apT, List.foldl, inst_app, inst_con, inst_var, assign, List.getD_cons_zero,
        List.getD_cons_succ] at step
      exact step.trans (by simpa [ap, apT, numeral, cmpNat] using inner)

theorem pureExplicitRule_mem {rule : RewriteRule} (member : rule ∈ pureRulesExplicit) :
    pureTheoryExplicit.rule rule :=
  member

/-- `case c (cmpCode o) x y z ⟶ x`, `y` or `z`. -/
theorem case_reduces (code : Term) (outcome : Ordering) (first second third : Term) :
    Reduces pureTheoryExplicit (ap "case" [code, cmpCode outcome, first, second, third])
      (match outcome with | .lt => first | .eq => second | .gt => third) := by
  cases outcome with
  | lt =>
      exact .single (Step.root (rootStep_of_instance (rule := rulesC[0])
        (pureExplicitRule_mem (by decide)) (assign [code, first, second, third])
        (by simp [rulesC, mkRule, closePattern, placeholderIndex, nv, assign, ap, apT, cmpCode])
        (by simp [rulesC, mkRule, closePattern, placeholderIndex, nv, assign])))
  | eq =>
      exact .single (Step.root (rootStep_of_instance (rule := rulesC[1])
        (pureExplicitRule_mem (by decide)) (assign [code, first, second, third])
        (by simp [rulesC, mkRule, closePattern, placeholderIndex, nv, assign, ap, apT, cmpCode])
        (by simp [rulesC, mkRule, closePattern, placeholderIndex, nv, assign])))
  | gt =>
      exact .single (Step.root (rootStep_of_instance (rule := rulesC[2])
        (pureExplicitRule_mem (by decide)) (assign [code, first, second, third])
        (by simp [rulesC, mkRule, closePattern, placeholderIndex, nv, assign, ap, apT, cmpCode])
        (by simp [rulesC, mkRule, closePattern, placeholderIndex, nv, assign])))

/-- `if c b x y ⟶ x` or `y`. -/
theorem if_reduces (code : Term) (choice : Bool) (first second : Term) :
    Reduces pureTheoryExplicit (ap "if" [code, boolCode choice, first, second])
      (if choice then first else second) := by
  cases choice with
  | true =>
      exact .single (Step.root (rootStep_of_instance (rule := rulesBOrthogonal[4])
        (pureExplicitRule_mem (by decide)) (assign [code, first, second])
        (by simp [rulesBOrthogonal, mkRule, closePattern, placeholderIndex, nv, assign, ap, apT, boolCode])
        (by simp [rulesBOrthogonal, mkRule, closePattern, placeholderIndex, nv, assign])))
  | false =>
      exact .single (Step.root (rootStep_of_instance (rule := rulesBOrthogonal[5])
        (pureExplicitRule_mem (by decide)) (assign [code, first, second])
        (by simp [rulesBOrthogonal, mkRule, closePattern, placeholderIndex, nv, assign, ap, apT, boolCode])
        (by simp [rulesBOrthogonal, mkRule, closePattern, placeholderIndex, nv, assign])))

theorem and_reduces (first second : Bool) :
    Reduces pureTheoryExplicit (ap "and" [boolCode first, boolCode second])
      (boolCode (first && second)) := by
  cases first <;> cases second <;> exact reducesPure_of_evaluate (fuel := 1) (by decide +kernel)

/-- `case B_code (cmpN m n) true true false ⟶* (m ≤ n)`. -/
theorem caseLe_reduces (first second : Nat) :
    Reduces pureTheoryExplicit
      (ap "case" [.con "B_code", ap "cmpN" [numeral first, numeral second], .con "true", .con "true",
        .con "false"])
      (boolCode (decide (first ≤ second))) := by
  have compared : Reduces pureTheoryExplicit
      (ap "case" [.con "B_code", ap "cmpN" [numeral first, numeral second], .con "true", .con "true",
        .con "false"])
      (ap "case" [.con "B_code", cmpCode (cmpNat first second), .con "true", .con "true",
        .con "false"]) :=
    Reduces.app (Reduces.app (Reduces.app (Reduces.app .refl (cmpN_reduces first second)) .refl) .refl)
      .refl
  refine compared.trans ((case_reduces _ _ _ _ _).trans ?_)
  rcases outcome : cmpNat first second with _ | _ | _
  · have below := cmpNat_eq_lt.mp outcome
    simp [boolCode, show first ≤ second by omega, Relation.ReflTransGen.refl]
  · have same := cmpNat_eq_eq.mp outcome
    simp [boolCode, same, Relation.ReflTransGen.refl]
  · have above := cmpNat_eq_gt.mp outcome
    simp [boolCode, show ¬ first ≤ second by omega, Relation.ReflTransGen.refl]

/-- `leN` compares two numerals. -/
theorem leN_reduces (first second : Nat) :
    Reduces pureTheoryExplicit (ap "leN" [numeral first, numeral second])
      (boolCode (decide (first ≤ second))) := by
  have unfolded := reducesPure_inst (skeleton := ap "leN" [.var 0, .var 1])
    (result := ap "case" [.con "B_code", ap "cmpN" [.var 0, .var 1], .con "true", .con "true",
      .con "false"]) (fuel := 10) (by decide +kernel) [numeral first, numeral second]
    (fun value member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact numeral_closed _) rfl rfl
  simp only [ap, apT, List.foldl, inst_app, inst_con, inst_var, assign, List.getD_cons_zero,
    List.getD_cons_succ] at unfolded
  exact unfolded.trans (caseLe_reduces first second)

/-- A closed sublevel `C ∅ c`. -/
def cstNil (constant : Term) : Term := ap "cst" [ap "nil" [.con "N_code"], constant]

/-- `leS (C ∅ m) (C ∅ n) ⟶* (m ≤ n)`. -/
theorem leS_cstNil_reduces (first second : Nat) :
    Reduces pureTheoryExplicit (ap "leS" [cstNil (numeral first), cstNil (numeral second)])
      (boolCode (decide (first ≤ second))) := by
  have unfolded := reducesPure_inst (skeleton := ap "leS" [cstNil (.var 0), cstNil (.var 1)])
    (result := ap "and" [.con "true", ap "case" [.con "B_code", ap "cmpN" [.var 0, .var 1],
      .con "true", .con "true", .con "false"]]) (fuel := 20) (by decide +kernel)
    [numeral first, numeral second]
    (fun value member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact numeral_closed _) rfl rfl
  simp only [cstNil, ap, apT, List.foldl, inst_app, inst_con, inst_var, assign, List.getD_cons_zero,
    List.getD_cons_succ] at unfolded
  refine unfolded.trans ((Reduces.app .refl (caseLe_reduces first second)).trans ?_)
  have conjunction := and_reduces true (decide (first ≤ second))
  simpa [boolCode, ap, apT] using conjunction

/-- `Add (C ∅ c) ∅ ⟶ {C ∅ c}`. -/
theorem add_nil_reduces (sublevel : Term) :
    Reduces pureTheoryExplicit (ap "Add" [sublevel, ap "nil" [.con "S_code"]]) (singletonSet sublevel) :=
  .single (Step.root (rootStep_of_instance (rule := rulesECorrected[2])
    (pureExplicitRule_mem (by decide)) (assign [sublevel, .con "S_code"])
    (by simp [rulesECorrected, mkRule, closePattern, placeholderIndex, nv, assign, ap, apT])
    (by simp [rulesECorrected, mkRule, closePattern, placeholderIndex, nv, assign, ap, apT,
      singletonSet])))

/-- **`Add (C ∅ m) {C ∅ n} ⟶* {C ∅ (max m n)}`.** -/
theorem add_singleton_reduces (first second : Nat) :
    Reduces pureTheoryExplicit
      (ap "Add" [cstNil (numeral first), singletonSet (cstNil (numeral second))])
      (singletonSet (cstNil (numeral (max first second)))) := by
  have unfolded : Reduces pureTheoryExplicit
      (ap "Add" [cstNil (numeral first), singletonSet (cstNil (numeral second))])
      (ap "if" [setOf (.con "S_code"), ap "leS" [cstNil (numeral first), cstNil (numeral second)],
        singletonSet (cstNil (numeral second)),
        ap "if" [setOf (.con "S_code"), ap "leS" [cstNil (numeral second), cstNil (numeral first)],
          ap "Add" [cstNil (numeral first), ap "nil" [.con "S_code"]],
          ap "add" [.con "S_code", .con "cmpS", cstNil (numeral second),
            ap "Add" [cstNil (numeral first), ap "nil" [.con "S_code"]]]]]) :=
    .single (Step.root (rootStep_of_instance (rule := addConsCorrected)
      (pureExplicitRule_mem (by decide))
      (assign [cstNil (numeral first), .con "S_code", cstNil (numeral second), ap "nil" [.con "S_code"]])
      (by simp [addConsCorrected, mkRule, closePattern, placeholderIndex, nv, assign, ap, apT,
        singletonSet])
      (by simp [addConsCorrected, mkRule, closePattern, placeholderIndex, nv, assign, ap, apT,
        singletonSet, setOf])))
  refine unfolded.trans ?_
  have firstTest := leS_cstNil_reduces first second
  refine (Reduces.app (Reduces.app (Reduces.app .refl firstTest) .refl) .refl).trans ?_
  refine (if_reduces _ _ _ _).trans ?_
  by_cases ordered : first ≤ second
  · simp only [ordered, decide_true, if_true]
    rw [Nat.max_eq_right ordered]
  · simp only [ordered, decide_false, Bool.false_eq_true, if_false]
    have secondTest := leS_cstNil_reduces second first
    refine (Reduces.app (Reduces.app (Reduces.app .refl secondTest) .refl) .refl).trans ?_
    refine (if_reduces _ _ _ _).trans ?_
    simp only [show second ≤ first by omega, decide_true, if_true]
    rw [Nat.max_eq_left (by omega)]
    exact add_nil_reduces _

/-! ## The normal forms of closed levels -/

/-- The set of sublevels of the normal form of a closed level of value
`count`: `∅`, or `{C ∅ count}`. -/
def closedSet : Nat → Term
  | 0 => ap "nil" [.con "S_code"]
  | count + 1 => singletonSet (cstNil (numeral (count + 1)))

/-- **The normal form of a closed level of value `count`.** -/
def closedNormal (count : Nat) : Term := ap "Max" [closedSet count]

theorem closedSet_closed : ∀ count : Nat, Closed (closedSet count)
  | 0 => .app .con .con
  | count + 1 => .app (.app (.app .con .con) (.app (.app .con (.app .con .con))
      (numeral_closed (count + 1)))) (.app .con .con)

theorem succ_closedNormal_reduces :
    ∀ count : Nat, Reduces pureTheoryExplicit (succ (closedNormal count)) (closedNormal (count + 1))
  | 0 => reducesPure_of_evaluate (fuel := 60) (by decide +kernel)
  | count + 1 => by
      have computed := reducesPure_inst
        (skeleton := succ (ap "Max" [singletonSet (cstNil (ap "s" [.var 0]))]))
        (result := ap "Max" [singletonSet (cstNil (ap "s" [ap "s" [.var 0]]))]) (fuel := 80)
        (by decide +kernel) [numeral count]
        (fun value member => by rw [List.mem_singleton.mp member]; exact numeral_closed _) rfl rfl
      simpa [closedNormal, closedSet, succ, singletonSet, cstNil, ap, apT, assign, numeral] using computed

theorem max_closedNormal_reduces (first second : Nat) :
    Reduces pureTheoryExplicit (ap "max" [closedNormal first, closedNormal second])
      (closedNormal (max first second)) := by
  rcases first with _ | first
  · have computed := reducesPure_inst (skeleton := ap "max" [ap "Max" [ap "nil" [.con "S_code"]],
        ap "Max" [.var 0]]) (result := ap "Max" [.var 0]) (fuel := 10) (by decide +kernel)
      [closedSet second]
      (fun value member => by rw [List.mem_singleton.mp member]; exact closedSet_closed _) rfl rfl
    simpa [closedNormal, closedSet, ap, apT, assign] using computed
  · rcases second with _ | second
    · have computed := reducesPure_inst
        (skeleton := ap "max" [ap "Max" [singletonSet (cstNil (.var 0))], ap "Max" [ap "nil" [.con "S_code"]]])
        (result := ap "Max" [singletonSet (cstNil (.var 0))]) (fuel := 20) (by decide +kernel)
        [numeral (first + 1)]
        (fun value member => by rw [List.mem_singleton.mp member]; exact numeral_closed _) rfl rfl
      simpa [closedNormal, closedSet, singletonSet, cstNil, ap, apT, assign] using computed
    · have computed := reducesPure_inst
        (skeleton := ap "max" [ap "Max" [singletonSet (cstNil (.var 0))],
          ap "Max" [singletonSet (cstNil (.var 1))]])
        (result := ap "Max" [ap "Add" [cstNil (.var 0), singletonSet (cstNil (.var 1))]]) (fuel := 4)
        (by decide +kernel) [numeral (first + 1), numeral (second + 1)]
        (fun value member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> exact numeral_closed _) rfl rfl
      simp only [singletonSet, cstNil, ap, apT, List.foldl, inst_app, inst_con, inst_var, assign,
        List.getD_cons_zero, List.getD_cons_succ] at computed
      have added := add_singleton_reduces (first + 1) (second + 1)
      rw [Nat.succ_max_succ] at added ⊢
      exact computed.trans (Reduces.app .refl added)

/-- `imax` of two values. -/
def imaxNat (first second : Nat) : Nat := if second = 0 then 0 else max first second

theorem imax_closedNormal_reduces (first second : Nat) :
    Reduces pureTheoryExplicit (imax (closedNormal first) (closedNormal second))
      (closedNormal (imaxNat first second)) := by
  rcases second with _ | second
  · have computed := reducesPure_inst (skeleton := imax (ap "Max" [.var 0]) (ap "Max" [ap "nil" [.con "S_code"]]))
      (result := ap "Max" [ap "nil" [.con "S_code"]]) (fuel := 10) (by decide +kernel)
      [closedSet first]
      (fun value member => by rw [List.mem_singleton.mp member]; exact closedSet_closed _) rfl rfl
    simpa [closedNormal, closedSet, imax, imaxNat, ap, apT, assign] using computed
  · rcases first with _ | first
    · have computed := reducesPure_inst
        (skeleton := imax (ap "Max" [ap "nil" [.con "S_code"]]) (ap "Max" [singletonSet (cstNil (.var 0))]))
        (result := ap "Max" [singletonSet (cstNil (.var 0))]) (fuel := 40) (by decide +kernel)
        [numeral (second + 1)]
        (fun value member => by rw [List.mem_singleton.mp member]; exact numeral_closed _) rfl rfl
      simpa [closedNormal, closedSet, singletonSet, cstNil, imax, imaxNat, ap, apT, assign] using computed
    · have computed := reducesPure_inst
        (skeleton := imax (ap "Max" [singletonSet (cstNil (.var 0))]) (ap "Max" [singletonSet (cstNil (.var 1))]))
        (result := ap "Max" [ap "Add" [ap "addguard" [cstNil (.var 0), cstNil (.var 1)],
          singletonSet (cstNil (.var 1))]]) (fuel := 13)
        (by decide +kernel) [numeral (first + 1), numeral (second + 1)]
        (fun value member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> exact numeral_closed _) rfl rfl
      have guarded := reducesPure_inst (skeleton := ap "addguard" [cstNil (.var 0), cstNil (.var 1)])
        (result := cstNil (.var 0)) (fuel := 20) (by decide +kernel)
        [numeral (first + 1), numeral (second + 1)]
        (fun value member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> exact numeral_closed _) rfl rfl
      simp only [singletonSet, cstNil, imax, ap, apT, List.foldl, inst_app, inst_con, inst_var, assign,
        List.getD_cons_zero, List.getD_cons_succ] at computed guarded
      have added := add_singleton_reduces (first + 1) (second + 1)
      have value : imaxNat (first + 1) (second + 1) = max first second + 1 := by
        simp [imaxNat, Nat.succ_max_succ]
      rw [Nat.succ_max_succ] at added
      rw [value]
      exact computed.trans ((Reduces.app .refl (Reduces.app (Reduces.app .refl guarded) .refl)).trans
        (Reduces.app .refl added))

/-- The value of a closed level, at any valuation. -/
def closedValue (level : LeanLevel) : Nat := level.eval fun _ => 0

theorem LeanLevel.eval_of_isClosed :
    ∀ (level : LeanLevel), level.IsClosed = true →
      ∀ valuation : Nat → Nat, level.eval valuation = closedValue level
  | .zero, _, _ => rfl
  | .succ level, closed, valuation => by
      simp only [LeanLevel.IsClosed] at closed
      simp [LeanLevel.eval, closedValue, LeanLevel.eval_of_isClosed level closed valuation]
  | .max first second, closed, valuation => by
      simp only [LeanLevel.IsClosed, Bool.and_eq_true] at closed
      simp only [LeanLevel.eval, LeanLevel.eval_of_isClosed first closed.1 valuation,
        LeanLevel.eval_of_isClosed second closed.2 valuation, closedValue]
  | .imax first second, closed, valuation => by
      simp only [LeanLevel.IsClosed, Bool.and_eq_true] at closed
      simp only [LeanLevel.eval, LeanLevel.eval_of_isClosed first closed.1 valuation,
        LeanLevel.eval_of_isClosed second closed.2 valuation, closedValue]
  | .param _, closed, _ => by simp [LeanLevel.IsClosed] at closed

theorem zero_reduces_pureExplicit : Reduces pureTheoryExplicit zero levelZero :=
  reducesPure_of_evaluate (fuel := 4) (by decide +kernel)

/-- **The code of a closed level reduces to the normal form of its value.** -/
theorem code_reduces_closedNormal :
    ∀ level : LeanLevel, level.IsClosed = true →
      Reduces pureTheoryExplicit (code level) (closedNormal (closedValue level))
  | .zero, _ => zero_reduces_pureExplicit
  | .succ level, closed => by
      have inner := code_reduces_closedNormal level closed
      exact (Reduces.app .refl inner).trans (succ_closedNormal_reduces _)
  | .max first second, closed => by
      simp only [LeanLevel.IsClosed, Bool.and_eq_true] at closed
      have left := code_reduces_closedNormal first closed.1
      have right := code_reduces_closedNormal second closed.2
      exact (Reduces.app (Reduces.app .refl left) right).trans (max_closedNormal_reduces _ _)
  | .imax first second, closed => by
      simp only [LeanLevel.IsClosed, Bool.and_eq_true] at closed
      have left := code_reduces_closedNormal first closed.1
      have right := code_reduces_closedNormal second closed.2
      have computed := (Reduces.app (Reduces.app .refl left) right).trans
        (imax_closedNormal_reduces (closedValue first) (closedValue second))
      have value : closedValue (.imax first second) = imaxNat (closedValue first) (closedValue second) :=
        rfl
      rw [value]
      exact computed
  | .param _, closed => by simp [LeanLevel.IsClosed] at closed

/-! ## The normal forms are normal and distinct -/

theorem headConst_mem_constantsOf : ∀ {term : Term} {name : String},
    headConst term = some name → name ∈ constantsOf term := by
  intro term
  induction term with
  | con other => intro name head; simp [headConst] at head; simp [constantsOf, head]
  | app function argument ihFunction _ =>
      intro name head
      simp only [headConst] at head
      simp [constantsOf, ihFunction head]
  | var _ => intro name head; simp [headConst] at head
  | srt _ => intro name head; simp [headConst] at head
  | pi _ _ _ _ => intro name head; simp [headConst] at head
  | lam _ _ _ _ => intro name head; simp [headConst] at head

/-- **A term without binders and variables whose constants are not defined by
the theory is normal.** -/
theorem normal_of_rigidConstants {theory : Theory} (headed : theory.Headed) :
    ∀ term : Term, flatBelow 0 term = true →
      (∀ name ∈ constantsOf term, ¬ theory.Defines name) → IsNormal (Step theory) term := by
  intro term
  induction term with
  | var index => intro flat; simp [flatBelow] at flat
  | srt sort => intro _ _; exact srt_normal headed sort
  | pi domain body _ _ => intro flat; simp [flatBelow] at flat
  | lam domain body _ _ => intro flat; simp [flatBelow] at flat
  | con name =>
      intro _ rigid next step
      exact RootStep.not_of_rigid headed (rigid name (by simp [constantsOf])) rfl step.con_inv
  | app function argument ihFunction ihArgument =>
      intro flat rigid next step
      simp only [flatBelow, Bool.and_eq_true] at flat
      rcases step.app_inv with root | ⟨inner, innerStep, _⟩ | ⟨inner, innerStep, _⟩
      · rcases root.defines headed with ⟨domain, body, operand, same⟩ | ⟨name, head, defines⟩
        · cases same
          simp [flatBelow] at flat
        · exact rigid name (headConst_mem_constantsOf head) defines
      · exact ihFunction flat.1 (fun name member => rigid name (by simp [constantsOf, member]))
          inner innerStep
      · exact ihArgument flat.2 (fun name member => rigid name (by simp [constantsOf, member]))
          inner innerStep

/-- The constants of normal forms of levels. -/
def levelConstructors : List String := ["Max", "nil", "S_code", "cons", "cst", "N_code", "s", "0"]

theorem levelConstructors_rigid :
    ∀ name ∈ levelConstructors, ¬ leanTheoryExplicit.Defines name := by
  have checked : ∀ name ∈ levelConstructors, lookupBody explicitSig name = none ∧
      explicitRules.all (fun rule => headConst rule.lhs != some name) = true := by
    decide +kernel
  intro name member defines
  obtain ⟨undefined, unheaded⟩ := checked name member
  rcases defines with defined | ⟨rule, ruleMember, head⟩
  · exact defined undefined
  · have absent := List.all_eq_true.mp unheaded rule ruleMember
    simp [head] at absent

theorem numeral_constants : ∀ count : Nat, ∀ name ∈ constantsOf (numeral count), name ∈ levelConstructors
  | 0, name, member => by simp [numeral, zeroN, constantsOf] at member; simp [member, levelConstructors]
  | count + 1, name, member => by
      simp only [numeral, ap, apT, List.foldl, constantsOf, List.mem_append, List.mem_singleton] at member
      rcases member with rfl | inner
      · simp [levelConstructors]
      · exact numeral_constants count name inner

theorem numeral_flat : ∀ count : Nat, flatBelow 0 (numeral count) = true
  | 0 => rfl
  | count + 1 => by simp [numeral, ap, apT, flatBelow, numeral_flat count]

theorem closedNormal_normal (count : Nat) : IsNormal (Step leanTheoryExplicit) (closedNormal count) := by
  refine normal_of_rigidConstants leanTheoryExplicit_headed _ ?_ ?_
  · rcases count with _ | count
    · rfl
    · simp [closedNormal, closedSet, singletonSet, cstNil, ap, apT, flatBelow, numeral_flat]
  · intro name member
    apply levelConstructors_rigid
    rcases count with _ | count
    · simp [closedNormal, closedSet, ap, apT, constantsOf] at member
      rcases member with rfl | rfl | rfl <;> simp [levelConstructors]
    · simp only [closedNormal, closedSet, singletonSet, cstNil, ap, apT, List.foldl, constantsOf,
        List.mem_append, List.mem_singleton] at member
      rcases member with ((rfl | (((rfl | rfl) | ((rfl | (rfl | rfl)) | inner)) | (rfl | rfl))))
      all_goals first
        | exact numeral_constants _ name inner
        | simp [levelConstructors]

theorem numeral_injective : ∀ {first second : Nat}, numeral first = numeral second → first = second
  | 0, 0, _ => rfl
  | 0, _ + 1, same => by simp [numeral, zeroN, ap, apT] at same
  | _ + 1, 0, same => by simp [numeral, zeroN, ap, apT] at same
  | first + 1, second + 1, same => by
      simp only [numeral, ap, apT, List.foldl, Term.app.injEq, true_and] at same
      rw [numeral_injective same]

theorem closedNormal_injective {first second : Nat} (same : closedNormal first = closedNormal second) :
    first = second := by
  rcases first with _ | first <;> rcases second with _ | second
  · rfl
  · simp [closedNormal, closedSet, singletonSet, ap, apT] at same
  · simp [closedNormal, closedSet, singletonSet, ap, apT] at same
  · simp only [closedNormal, closedSet, singletonSet, cstNil, ap, apT, List.foldl, Term.app.injEq,
      true_and, and_true] at same
    exact numeral_injective same

/-! ## Theorems 2 and 3 for the closed levels -/

/-- **Theorem 3, for the closed levels**: equivalent closed levels have
convertible codes. -/
theorem theorem3_closed {first second : LeanLevel} (firstClosed : first.IsClosed = true)
    (secondClosed : second.IsClosed = true) (equivalent : LeanLevel.Equiv first second) :
    Conv leanTheoryExplicit (code first) (code second) := by
  have same : closedValue first = closedValue second := equivalent fun _ => 0
  have left := (code_reduces_closedNormal first firstClosed).mono pureTheoryExplicit_extends
  have right := (code_reduces_closedNormal second secondClosed).mono pureTheoryExplicit_extends
  rw [same] at left
  exact Joinable.conv ⟨_, left, right⟩

/-- **Theorem 3, for the closed levels, in a frame**: read under any
instantiation `frame`, equivalent closed levels are convertible. -/
theorem theorem3_closed_in (frame : Term) {first second : LeanLevel}
    (firstClosed : first.IsClosed = true) (secondClosed : second.IsClosed = true)
    (equivalent : LeanLevel.Equiv first second) :
    Conv leanTheoryExplicit (levelIn frame first) (levelIn frame second) :=
  Conv.app (.refl _) (theorem3_closed firstClosed secondClosed equivalent)

/-- **Theorem 2, for the closed levels**: two closed levels have convertible
codes exactly when they are equivalent. -/
theorem theorem2_closed {first second : LeanLevel} (firstClosed : first.IsClosed = true)
    (secondClosed : second.IsClosed = true) :
    Conv leanTheoryExplicit (code first) (code second) ↔ LeanLevel.Equiv first second := by
  refine ⟨fun convertible => ?_, theorem3_closed firstClosed secondClosed⟩
  have left := (code_reduces_closedNormal first firstClosed).mono pureTheoryExplicit_extends
  have right := (code_reduces_closedNormal second secondClosed).mono pureTheoryExplicit_extends
  have normals : Conv leanTheoryExplicit (closedNormal (closedValue first)) (closedNormal (closedValue second)) :=
    .trans _ _ _ (.symm _ _ left.conv) (.trans _ _ _ convertible right.conv)
  have same : closedValue first = closedValue second := by
    by_contra distinct
    exact not_conv_of_normal leanTheoryExplicit_confluent (closedNormal_normal _) (closedNormal_normal _)
      (fun equal => distinct (closedNormal_injective equal)) normals
  intro valuation
  rw [LeanLevel.eval_of_isClosed first firstClosed, LeanLevel.eval_of_isClosed second secondClosed, same]

#print axioms cmpN_reduces
#print axioms add_singleton_reduces
#print axioms code_reduces_closedNormal
#print axioms closedNormal_normal
#print axioms theorem3_closed
#print axioms theorem3_closed_in
#print axioms theorem2_closed

end Mettapedia.GSLT.Dedukti.LeanMinus
