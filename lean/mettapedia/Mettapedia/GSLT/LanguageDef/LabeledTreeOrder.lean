import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mathlib.Order.RelClasses

/-!
# Labeled trees, ordered by first-order rules

Finitely branching trees with natural-number labels carry the data of any one-sorted
first-order calculus: a constructor becomes a label and its arguments become children.
Seven first-order rules order these trees: labels compare as unary numerals, and two nodes
with one label compare by their children, lexicographically. The order is strict and total,
so disequality is the order in either direction, and finite sets of trees have a canonical
sorted listing.

* **The order.** `TreeLt` is irreflexive, transitive and trichotomous on trees
  (`TreeLt.irrefl`, `TreeLt.trans`, `TreeLt.trichotomous`); `ltB` decides it (`ltB_iff`).
  Trees therefore form a linear order.
* **The rules** (`orderRules`), over the constructors `tree.zero`, `tree.succ`, `tree.nil`,
  `tree.cons` and `tree.node`: `tree.Below` on numerals, `tree.Lt` on trees and `tree.LtList`
  on child lists.
* **What they mean.** Every application of an order rule preserves any meaning that reads
  the three judgments as the pattern relations `PBelow`, `PLt` and `PLtList`
  (`orderRule_closed`), `orderMeaning` among them. On encoded trees these are exactly the order of numerals and of trees
  (`pBelow_numeral_iff`, `pLt_toPattern_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.LabeledTreeOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! ## Labeled trees and their order -/

/-- A finitely branching tree whose nodes carry natural-number labels. -/
inductive LabeledTree where
  | node (label : Nat) (children : List LabeledTree)
deriving Repr

/-! ## Trees as patterns -/

def zeroP : Pattern := .apply "tree.zero" []
def succP (numeral : Pattern) : Pattern := .apply "tree.succ" [numeral]
def nilP : Pattern := .apply "tree.nil" []
def consP (head tail : Pattern) : Pattern := .apply "tree.cons" [head, tail]
def nodeP (label children : Pattern) : Pattern := .apply "tree.node" [label, children]

/-- Unary numerals. -/
def numeralP : Nat → Pattern
  | 0 => zeroP
  | count + 1 => succP (numeralP count)

/-- Lists of patterns. -/
def listP : List Pattern → Pattern
  | [] => nilP
  | head :: tail => consP head (listP tail)

mutual
  /-- A tree as a constructor pattern: its label as a numeral, its children as a list. -/
  def LabeledTree.toPattern : LabeledTree → Pattern
    | .node label children => nodeP (numeralP label) (LabeledTree.toPatternList children)

  def LabeledTree.toPatternList : List LabeledTree → Pattern
    | [] => nilP
    | head :: tail => consP head.toPattern (LabeledTree.toPatternList tail)
end

theorem numeralP_injective : Function.Injective numeralP := by
  intro first
  induction first with
  | zero => intro second same; cases second <;> simp_all [numeralP, zeroP, succP]
  | succ count ih =>
      intro second same
      cases second with
      | zero => simp [numeralP, zeroP, succP] at same
      | succ other =>
          simp only [numeralP, succP, Pattern.apply.injEq, List.cons.injEq, and_true,
            true_and] at same
          rw [ih same]

mutual
  theorem LabeledTree.toPattern_injective : ∀ (first second : LabeledTree),
      first.toPattern = second.toPattern → first = second
    | .node firstLabel firstChildren, .node secondLabel secondChildren, same => by
        simp only [LabeledTree.toPattern, nodeP, Pattern.apply.injEq, List.cons.injEq,
          and_true, true_and] at same
        rw [numeralP_injective same.1,
          LabeledTree.toPatternList_injective firstChildren secondChildren same.2]

  theorem LabeledTree.toPatternList_injective : ∀ (first second : List LabeledTree),
      LabeledTree.toPatternList first = LabeledTree.toPatternList second → first = second
    | [], [], _ => rfl
    | [], _ :: _, same => by simp [LabeledTree.toPatternList, nilP, consP] at same
    | _ :: _, [], same => by simp [LabeledTree.toPatternList, nilP, consP] at same
    | firstHead :: firstTail, secondHead :: secondTail, same => by
        simp only [LabeledTree.toPatternList, consP, Pattern.apply.injEq, List.cons.injEq,
          and_true, true_and] at same
        rw [LabeledTree.toPattern_injective firstHead secondHead same.1,
          LabeledTree.toPatternList_injective firstTail secondTail same.2]
end

instance : DecidableEq LabeledTree := fun first second =>
  decidable_of_iff (first.toPattern = second.toPattern)
    ⟨LabeledTree.toPattern_injective first second, fun same => same ▸ rfl⟩

namespace LabeledTree

mutual
  /-- Labels first; equal labels compare their children lexicographically. -/
  inductive TreeLt : LabeledTree → LabeledTree → Prop where
    | label {first second : Nat} {firstChildren secondChildren : List LabeledTree} :
        first < second → TreeLt (.node first firstChildren) (.node second secondChildren)
    | children {label : Nat} {firstChildren secondChildren : List LabeledTree} :
        ListLt firstChildren secondChildren →
          TreeLt (.node label firstChildren) (.node label secondChildren)

  /-- Lexicographic order of child lists; a proper prefix comes first. -/
  inductive ListLt : List LabeledTree → List LabeledTree → Prop where
    | nil {head : LabeledTree} {tail : List LabeledTree} : ListLt [] (head :: tail)
    | head {first second : LabeledTree} {firstTail secondTail : List LabeledTree} :
        TreeLt first second → ListLt (first :: firstTail) (second :: secondTail)
    | tail {head : LabeledTree} {firstTail secondTail : List LabeledTree} :
        ListLt firstTail secondTail → ListLt (head :: firstTail) (head :: secondTail)
end

mutual
  theorem TreeLt.irrefl : ∀ (tree : LabeledTree), ¬ TreeLt tree tree
    | .node label children, smaller => by
        cases smaller with
        | label lower => exact Nat.lt_irrefl label lower
        | children lower => exact ListLt.irrefl children lower

  theorem ListLt.irrefl : ∀ (trees : List LabeledTree), ¬ ListLt trees trees
    | [], smaller => by cases smaller
    | head :: tail, smaller => by
        cases smaller with
        | head lower => exact TreeLt.irrefl head lower
        | tail lower => exact ListLt.irrefl tail lower
end

mutual
  theorem TreeLt.trans : ∀ (first : LabeledTree) {second third : LabeledTree},
      TreeLt first second → TreeLt second third → TreeLt first third
    | .node label children, second, third, firstStep, secondStep => by
        cases firstStep with
        | label lower =>
            cases secondStep with
            | label upper => exact .label (Nat.lt_trans lower upper)
            | children _ => exact .label lower
        | children lower =>
            cases secondStep with
            | label upper => exact .label upper
            | children upper => exact .children (ListLt.trans children lower upper)

  theorem ListLt.trans : ∀ (first : List LabeledTree) {second third : List LabeledTree},
      ListLt first second → ListLt second third → ListLt first third
    | [], second, third, firstStep, secondStep => by
        cases firstStep
        cases secondStep with
        | head _ => exact .nil
        | tail _ => exact .nil
    | head :: tail, second, third, firstStep, secondStep => by
        cases firstStep with
        | head lower =>
            cases secondStep with
            | head upper => exact .head (TreeLt.trans head lower upper)
            | tail _ => exact .head lower
        | tail lower =>
            cases secondStep with
            | head upper => exact .head upper
            | tail upper => exact .tail (ListLt.trans tail lower upper)
end

mutual
  theorem TreeLt.trichotomous : ∀ (first second : LabeledTree),
      TreeLt first second ∨ first = second ∨ TreeLt second first
    | .node firstLabel firstChildren, .node secondLabel secondChildren => by
        rcases Nat.lt_trichotomy firstLabel secondLabel with lower | same | upper
        · exact Or.inl (.label lower)
        · subst same
          rcases ListLt.trichotomous firstChildren secondChildren with lower | same | upper
          · exact Or.inl (.children lower)
          · exact Or.inr (Or.inl (by rw [same]))
          · exact Or.inr (Or.inr (.children upper))
        · exact Or.inr (Or.inr (.label upper))

  theorem ListLt.trichotomous : ∀ (first second : List LabeledTree),
      ListLt first second ∨ first = second ∨ ListLt second first
    | [], [] => Or.inr (Or.inl rfl)
    | [], _ :: _ => Or.inl .nil
    | _ :: _, [] => Or.inr (Or.inr .nil)
    | firstHead :: firstTail, secondHead :: secondTail => by
        rcases TreeLt.trichotomous firstHead secondHead with lower | same | upper
        · exact Or.inl (.head lower)
        · subst same
          rcases ListLt.trichotomous firstTail secondTail with lower | same | upper
          · exact Or.inl (.tail lower)
          · exact Or.inr (Or.inl (by rw [same]))
          · exact Or.inr (Or.inr (.tail upper))
        · exact Or.inr (Or.inr (.head upper))
end

mutual
  /-- The decision procedure of the order. -/
  def ltB : LabeledTree → LabeledTree → Bool
    | .node firstLabel firstChildren, .node secondLabel secondChildren =>
        if firstLabel < secondLabel then true
        else if firstLabel = secondLabel then listLtB firstChildren secondChildren
        else false

  def listLtB : List LabeledTree → List LabeledTree → Bool
    | [], [] => false
    | [], _ :: _ => true
    | _ :: _, [] => false
    | firstHead :: firstTail, secondHead :: secondTail =>
        if ltB firstHead secondHead then true
        else if firstHead = secondHead then listLtB firstTail secondTail
        else false
end

mutual
  theorem ltB_iff : ∀ (first second : LabeledTree), ltB first second = true ↔ TreeLt first second
    | .node firstLabel firstChildren, .node secondLabel secondChildren => by
        constructor
        · intro decided
          unfold ltB at decided
          by_cases lower : firstLabel < secondLabel
          · exact .label lower
          · rw [if_neg lower] at decided
            by_cases same : firstLabel = secondLabel
            · subst same
              rw [if_pos rfl] at decided
              exact .children ((listLtB_iff firstChildren secondChildren).mp decided)
            · rw [if_neg same] at decided
              exact absurd decided Bool.false_ne_true
        · intro smaller
          unfold ltB
          cases smaller with
          | label lower => rw [if_pos lower]
          | children lower =>
              rw [if_neg (Nat.lt_irrefl _), if_pos rfl]
              exact (listLtB_iff firstChildren secondChildren).mpr lower

  theorem listLtB_iff : ∀ (first second : List LabeledTree),
      listLtB first second = true ↔ ListLt first second
    | [], [] => by
        simp only [listLtB, Bool.false_eq_true, false_iff]
        intro smaller
        cases smaller
    | [], _ :: _ => by simp only [listLtB, true_iff]; exact .nil
    | _ :: _, [] => by
        simp only [listLtB, Bool.false_eq_true, false_iff]
        intro smaller
        cases smaller
    | firstHead :: firstTail, secondHead :: secondTail => by
        constructor
        · intro decided
          unfold listLtB at decided
          by_cases lower : ltB firstHead secondHead = true
          · exact .head ((ltB_iff firstHead secondHead).mp lower)
          · rw [if_neg lower] at decided
            by_cases same : firstHead = secondHead
            · subst same
              rw [if_pos rfl] at decided
              exact .tail ((listLtB_iff firstTail secondTail).mp decided)
            · rw [if_neg same] at decided
              exact absurd decided Bool.false_ne_true
        · intro smaller
          unfold listLtB
          cases smaller with
          | head lower => rw [if_pos ((ltB_iff firstHead secondHead).mpr lower)]
          | tail lower =>
              have notLower : ¬ ltB firstHead firstHead = true := fun decided =>
                TreeLt.irrefl firstHead ((ltB_iff firstHead firstHead).mp decided)
              rw [if_neg notLower, if_pos rfl]
              exact (listLtB_iff firstTail secondTail).mpr lower
end

instance : LT LabeledTree := ⟨TreeLt⟩

instance decidableLt : DecidableRel (α := LabeledTree) (· < ·) :=
  fun first second => decidable_of_iff _ (ltB_iff first second)

instance : IsStrictTotalOrder LabeledTree (· < ·) where
  irrefl := TreeLt.irrefl
  trans := fun first _ _ => TreeLt.trans first
  trichotomous := fun first second notLower notUpper => by
    rcases TreeLt.trichotomous first second with lower | same | upper
    · exact absurd lower notLower
    · exact same
    · exact absurd upper notUpper

/-- Labeled trees in their structural order. -/
instance linearOrder : LinearOrder LabeledTree := linearOrderOfSTO (· < ·)

end LabeledTree

/-! ## The pattern relations the rules derive -/

/-- The order of unary numerals, on arbitrary patterns. -/
inductive PBelow : Pattern → Pattern → Prop where
  | zero (numeral : Pattern) : PBelow zeroP (succP numeral)
  | succ {first second : Pattern} : PBelow first second → PBelow (succP first) (succP second)

mutual
  /-- The tree order, on arbitrary patterns. -/
  inductive PLt : Pattern → Pattern → Prop where
    | label {first second firstChildren secondChildren : Pattern} :
        PBelow first second → PLt (nodeP first firstChildren) (nodeP second secondChildren)
    | children {label firstChildren secondChildren : Pattern} :
        PLtList firstChildren secondChildren →
          PLt (nodeP label firstChildren) (nodeP label secondChildren)

  /-- The lexicographic order of lists, on arbitrary patterns. -/
  inductive PLtList : Pattern → Pattern → Prop where
    | nil (head tail : Pattern) : PLtList nilP (consP head tail)
    | head {first second firstTail secondTail : Pattern} :
        PLt first second → PLtList (consP first firstTail) (consP second secondTail)
    | tail {head firstTail secondTail : Pattern} :
        PLtList firstTail secondTail → PLtList (consP head firstTail) (consP head secondTail)
end

theorem PBelow.inv {first second : Pattern} (below : PBelow first second) :
    (first = zeroP ∧ ∃ numeral, second = succP numeral) ∨
      ∃ smaller larger, first = succP smaller ∧ second = succP larger ∧ PBelow smaller larger := by
  cases below with
  | zero numeral => exact Or.inl ⟨rfl, numeral, rfl⟩
  | succ inner => exact Or.inr ⟨_, _, rfl, rfl, inner⟩

theorem PLt.inv {first second : Pattern} (smaller : PLt first second) :
    (∃ firstLabel secondLabel firstChildren secondChildren,
        first = nodeP firstLabel firstChildren ∧ second = nodeP secondLabel secondChildren ∧
          PBelow firstLabel secondLabel) ∨
      ∃ label firstChildren secondChildren,
        first = nodeP label firstChildren ∧ second = nodeP label secondChildren ∧
          PLtList firstChildren secondChildren := by
  cases smaller with
  | label below => exact Or.inl ⟨_, _, _, _, rfl, rfl, below⟩
  | children lower => exact Or.inr ⟨_, _, _, rfl, rfl, lower⟩

theorem PLtList.inv {first second : Pattern} (smaller : PLtList first second) :
    (first = nilP ∧ ∃ head tail, second = consP head tail) ∨
      (∃ firstHead secondHead firstTail secondTail,
        first = consP firstHead firstTail ∧ second = consP secondHead secondTail ∧
          PLt firstHead secondHead) ∨
      ∃ head firstTail secondTail,
        first = consP head firstTail ∧ second = consP head secondTail ∧
          PLtList firstTail secondTail := by
  cases smaller with
  | nil head tail => exact Or.inl ⟨rfl, head, tail, rfl⟩
  | head lower => exact Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, lower⟩)
  | tail lower => exact Or.inr (Or.inr ⟨_, _, _, rfl, rfl, lower⟩)

theorem pBelow_numeral_iff : ∀ (first second : Nat),
    PBelow (numeralP first) (numeralP second) ↔ first < second
  | 0, 0 => by
      simp only [numeralP, Nat.lt_irrefl, iff_false]
      intro below
      rcases below.inv with ⟨_, numeral, same⟩ | ⟨_, _, wrong, _, _⟩
      · simp [zeroP, succP] at same
      · simp [zeroP, succP] at wrong
  | 0, second + 1 => by simp only [numeralP, Nat.zero_lt_succ, iff_true]; exact .zero _
  | first + 1, 0 => by
      simp only [numeralP, Nat.not_lt_zero, iff_false]
      intro below
      rcases below.inv with ⟨wrong, _⟩ | ⟨_, _, _, wrong, _⟩
      · simp [zeroP, succP] at wrong
      · simp [zeroP, succP] at wrong
  | first + 1, second + 1 => by
      constructor
      · intro below
        rcases below.inv with ⟨wrong, _⟩ | ⟨smaller, larger, firstSame, secondSame, inner⟩
        · simp [numeralP, zeroP, succP] at wrong
        · simp only [numeralP, succP, Pattern.apply.injEq, List.cons.injEq, and_true,
            true_and] at firstSame secondSame
          rw [← firstSame, ← secondSame] at inner
          exact Nat.succ_lt_succ ((pBelow_numeral_iff first second).mp inner)
      · intro lower
        exact .succ ((pBelow_numeral_iff first second).mpr (Nat.lt_of_succ_lt_succ lower))

mutual
  theorem pLt_toPattern_iff : ∀ (first second : LabeledTree),
      PLt first.toPattern second.toPattern ↔ first < second
    | .node firstLabel firstChildren, .node secondLabel secondChildren => by
        constructor
        · intro smaller
          simp only [LabeledTree.toPattern] at smaller
          rcases smaller.inv with
            ⟨l, m, cs, ds, firstSame, secondSame, below⟩ | ⟨l, cs, ds, firstSame, secondSame, lower⟩
          · simp only [nodeP, Pattern.apply.injEq, List.cons.injEq, and_true,
              true_and] at firstSame secondSame
            rw [← firstSame.1, ← secondSame.1] at below
            exact .label ((pBelow_numeral_iff _ _).mp below)
          · simp only [nodeP, Pattern.apply.injEq, List.cons.injEq, and_true,
              true_and] at firstSame secondSame
            have labels := numeralP_injective (firstSame.1.trans secondSame.1.symm)
            subst labels
            rw [← firstSame.2, ← secondSame.2] at lower
            exact .children ((pLtList_toPatternList_iff _ _).mp lower)
        · intro smaller
          simp only [LabeledTree.toPattern]
          cases smaller with
          | label lower => exact .label ((pBelow_numeral_iff _ _).mpr lower)
          | children lower => exact .children ((pLtList_toPatternList_iff _ _).mpr lower)

  theorem pLtList_toPatternList_iff : ∀ (first second : List LabeledTree),
      PLtList (LabeledTree.toPatternList first) (LabeledTree.toPatternList second) ↔
        LabeledTree.ListLt first second
    | [], [] => by
        simp only [LabeledTree.toPatternList]
        constructor
        · intro smaller
          rcases smaller.inv with ⟨_, _, _, wrong⟩ | ⟨_, _, _, _, wrong, _⟩ | ⟨_, _, _, wrong, _⟩
          · simp [nilP, consP] at wrong
          · simp [nilP, consP] at wrong
          · simp [nilP, consP] at wrong
        · intro smaller
          cases smaller
    | [], _ :: _ => by
        simp only [LabeledTree.toPatternList]
        exact ⟨fun _ => .nil, fun _ => .nil _ _⟩
    | _ :: _, [] => by
        simp only [LabeledTree.toPatternList]
        constructor
        · intro smaller
          rcases smaller.inv with ⟨wrong, _⟩ | ⟨_, _, _, _, _, wrong, _⟩ | ⟨_, _, _, _, wrong, _⟩
          · simp [nilP, consP] at wrong
          · simp [nilP, consP] at wrong
          · simp [nilP, consP] at wrong
        · intro smaller
          cases smaller
    | firstHead :: firstTail, secondHead :: secondTail => by
        simp only [LabeledTree.toPatternList]
        constructor
        · intro smaller
          rcases smaller.inv with ⟨wrong, _⟩ |
              ⟨x, y, xs, ys, firstSame, secondSame, lower⟩ | ⟨x, xs, ys, firstSame, secondSame, lower⟩
          · simp [nilP, consP] at wrong
          · simp only [consP, Pattern.apply.injEq, List.cons.injEq, and_true,
              true_and] at firstSame secondSame
            rw [← firstSame.1, ← secondSame.1] at lower
            exact .head ((pLt_toPattern_iff _ _).mp lower)
          · simp only [consP, Pattern.apply.injEq, List.cons.injEq, and_true,
              true_and] at firstSame secondSame
            have heads := LabeledTree.toPattern_injective _ _ (firstSame.1.trans secondSame.1.symm)
            subst heads
            rw [← firstSame.2, ← secondSame.2] at lower
            exact .tail ((pLtList_toPatternList_iff _ _).mp lower)
        · intro smaller
          cases smaller with
          | head lower => exact .head ((pLt_toPattern_iff _ _).mpr lower)
          | tail lower => exact .tail ((pLtList_toPatternList_iff _ _).mpr lower)
end

/-! ## The pattern relations are irreflexive -/

theorem PBelow.ne {first second : Pattern} (below : PBelow first second) : first ≠ second := by
  induction below with
  | zero tail => simp [zeroP, succP]
  | succ inner ih =>
      intro same
      simp only [succP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
      exact ih same

theorem PBelow.irrefl {numeral : Pattern} : ¬ PBelow numeral numeral := fun below => below.ne rfl

mutual
  theorem PLt.ne : ∀ {first second : Pattern}, PLt first second → first ≠ second
    | _, _, .label below, same => by
        simp only [nodeP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
        exact below.ne same.1
    | _, _, .children lower, same => by
        simp only [nodeP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
        exact PLtList.ne lower same

  theorem PLtList.ne : ∀ {first second : Pattern}, PLtList first second → first ≠ second
    | _, _, .nil _ _, same => by simp [nilP, consP] at same
    | _, _, .head lower, same => by
        simp only [consP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
        exact PLt.ne lower same.1
    | _, _, .tail lower, same => by
        simp only [consP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
        exact PLtList.ne lower same
end

/-! ## The rules -/

def belowJudgment (first second : Pattern) : Pattern := .apply "tree.Below" [first, second]
def ltJudgment (first second : Pattern) : Pattern := .apply "tree.Lt" [first, second]
def ltListJudgment (first second : Pattern) : Pattern := .apply "tree.LtList" [first, second]

private def mv (name : String) : Pattern := .fvar name

def belowZeroRule : RuleSchema where
  id := ⟨"tree.below-zero"⟩
  metavariables := [("n", 0)]
  premises := []
  conclusion := belowJudgment zeroP (succP (mv "n"))

def belowSuccRule : RuleSchema where
  id := ⟨"tree.below-succ"⟩
  metavariables := [("m", 0), ("n", 0)]
  premises := [belowJudgment (mv "m") (mv "n")]
  conclusion := belowJudgment (succP (mv "m")) (succP (mv "n"))

def ltLabelRule : RuleSchema where
  id := ⟨"tree.lt-label"⟩
  metavariables := [("l", 0), ("m", 0), ("cs", 0), ("ds", 0)]
  premises := [belowJudgment (mv "l") (mv "m")]
  conclusion := ltJudgment (nodeP (mv "l") (mv "cs")) (nodeP (mv "m") (mv "ds"))

def ltChildrenRule : RuleSchema where
  id := ⟨"tree.lt-children"⟩
  metavariables := [("l", 0), ("cs", 0), ("ds", 0)]
  premises := [ltListJudgment (mv "cs") (mv "ds")]
  conclusion := ltJudgment (nodeP (mv "l") (mv "cs")) (nodeP (mv "l") (mv "ds"))

def ltListNilRule : RuleSchema where
  id := ⟨"tree.ltlist-nil"⟩
  metavariables := [("x", 0), ("xs", 0)]
  premises := []
  conclusion := ltListJudgment nilP (consP (mv "x") (mv "xs"))

def ltListHeadRule : RuleSchema where
  id := ⟨"tree.ltlist-head"⟩
  metavariables := [("x", 0), ("y", 0), ("xs", 0), ("ys", 0)]
  premises := [ltJudgment (mv "x") (mv "y")]
  conclusion := ltListJudgment (consP (mv "x") (mv "xs")) (consP (mv "y") (mv "ys"))

def ltListTailRule : RuleSchema where
  id := ⟨"tree.ltlist-tail"⟩
  metavariables := [("x", 0), ("xs", 0), ("ys", 0)]
  premises := [ltListJudgment (mv "xs") (mv "ys")]
  conclusion := ltListJudgment (consP (mv "x") (mv "xs")) (consP (mv "x") (mv "ys"))

/-- The seven order rules. -/
def orderRules : List RuleSchema :=
  [belowZeroRule, belowSuccRule, ltLabelRule, ltChildrenRule, ltListNilRule, ltListHeadRule,
    ltListTailRule]

/-- The constructors the order rules use, with their arities. -/
def orderConstructors : List (String × Nat) :=
  [("tree.zero", 0), ("tree.succ", 1), ("tree.nil", 0), ("tree.cons", 2), ("tree.node", 2)]

/-- The three order judgments. -/
def orderJudgments : List JudgmentDecl :=
  [{ head := "tree.Below", arity := 2 }, { head := "tree.Lt", arity := 2 },
    { head := "tree.LtList", arity := 2 }]

/-- The order judgments read as the pattern relations; other judgments are unconstrained. -/
def orderMeaning : Pattern → Prop
  | .apply "tree.Below" [first, second] => PBelow first second
  | .apply "tree.Lt" [first, second] => PLt first second
  | .apply "tree.LtList" [first, second] => PLtList first second
  | _ => True

/-- Lists of arguments as long as a rule's formals. -/
private theorem arguments_of_valid {formals : List (String × Nat)} {arguments : List Pattern}
    (valid : argumentsValidAt formals arguments = true) : arguments.length = formals.length :=
  (argumentsValidAt_length valid).symm

/-- **Every application of an order rule preserves the meaning of the order judgments.** -/
theorem orderRule_closed {meaning : Pattern → Prop}
    (below : ∀ first second, meaning (belowJudgment first second) ↔ PBelow first second)
    (lt : ∀ first second, meaning (ltJudgment first second) ↔ PLt first second)
    (ltList : ∀ first second, meaning (ltListJudgment first second) ↔ PLtList first second)
    {rule : RuleSchema} (member : rule ∈ orderRules)
    {arguments premises : List Pattern} {conclusion : Pattern}
    (valid : argumentsValidAt rule.metavariables arguments = true)
    (premisesInstantiate : InstantiatesList rule.metavariables arguments rule.premises premises)
    (conclusionInstantiates : Instantiates rule.metavariables arguments rule.conclusion conclusion)
    (premisesHold : ∀ premise ∈ premises, meaning premise) :
    meaning conclusion := by
  have lengths := arguments_of_valid valid
  have conclusionValue := instantiateSchemaAt?_eq_some_iff_instantiates.mpr conclusionInstantiates
  have premisesValue := instantiateSchemasAt?_complete premisesInstantiate
  simp only [orderRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · match arguments, lengths with
    | [n], _ =>
        simp [belowZeroRule, belowJudgment, zeroP, succP, mv, instantiateSchemaAt?,
          instantiateSchemasAt?, lookupArgumentAt?] at conclusionValue
        subst conclusionValue
        exact (below _ _).mpr (.zero n)
  · match arguments, lengths with
    | [m, n], _ =>
        simp [belowSuccRule, belowJudgment, succP, mv, instantiateSchemaAt?,
          instantiateSchemasAt?, lookupArgumentAt?] at conclusionValue premisesValue
        subst conclusionValue premisesValue
        have premise := (below m n).mp (premisesHold (.apply "tree.Below" [m, n]) (by simp))
        exact (below _ _).mpr (.succ premise)
  · match arguments, lengths with
    | [l, m, cs, ds], _ =>
        simp [ltLabelRule, ltJudgment, belowJudgment, nodeP, mv, instantiateSchemaAt?,
          instantiateSchemasAt?, lookupArgumentAt?] at conclusionValue premisesValue
        subst conclusionValue premisesValue
        have premise := (below l m).mp (premisesHold (.apply "tree.Below" [l, m]) (by simp))
        exact (lt _ _).mpr (.label premise)
  · match arguments, lengths with
    | [l, cs, ds], _ =>
        simp [ltChildrenRule, ltJudgment, ltListJudgment, nodeP, mv, instantiateSchemaAt?,
          instantiateSchemasAt?, lookupArgumentAt?] at conclusionValue premisesValue
        subst conclusionValue premisesValue
        have premise := (ltList cs ds).mp (premisesHold (.apply "tree.LtList" [cs, ds]) (by simp))
        exact (lt _ _).mpr (.children premise)
  · match arguments, lengths with
    | [x, xs], _ =>
        simp [ltListNilRule, ltListJudgment, nilP, consP, mv, instantiateSchemaAt?,
          instantiateSchemasAt?, lookupArgumentAt?] at conclusionValue
        subst conclusionValue
        exact (ltList _ _).mpr (.nil x xs)
  · match arguments, lengths with
    | [x, y, xs, ys], _ =>
        simp [ltListHeadRule, ltListJudgment, ltJudgment, consP, mv, instantiateSchemaAt?,
          instantiateSchemasAt?, lookupArgumentAt?] at conclusionValue premisesValue
        subst conclusionValue premisesValue
        have premise := (lt x y).mp (premisesHold (.apply "tree.Lt" [x, y]) (by simp))
        exact (ltList _ _).mpr (.head premise)
  · match arguments, lengths with
    | [x, xs, ys], _ =>
        simp [ltListTailRule, ltListJudgment, consP, mv, instantiateSchemaAt?,
          instantiateSchemasAt?, lookupArgumentAt?] at conclusionValue premisesValue
        subst conclusionValue premisesValue
        have premise := (ltList xs ys).mp (premisesHold (.apply "tree.LtList" [xs, ys]) (by simp))
        exact (ltList _ _).mpr (.tail premise)

end Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
