import Mettapedia.GSLT.Dedukti.LeanMinusLevelAdequacy

/-!
# The level codes of the theory with explicit substitution compute a normal form

For every level `l`, with any level variables, the code `|l|` reduces in the
level theory `pureTheoryExplicit`, hence in every theory that contains it, to
`normalCode (normalSet l)` (`code_reduces_normalSet`),
where `normalSet` is computed by Lean functions that follow the rules of `ΣU`,
corrected, one for one: sorted insertion and union of guard sets
(`insertSorted`, `unionSorted`), comparison of sets (`cmpList`), comparison and
dominance of sublevels (`cmpSub`, `leSub`), `addguard`, `incr`, and the
insertion with dominance test `addSub` (the corrected `Add`).

Each rule of `ΣU` is computed once on a term whose free variables stand for
its arguments (`reducesPure_inst`); the recursive calls are reduced by induction
and put back by `Reduces.instantiate`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig lift subst subst0 lookupBody)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-- Rewrite an instance of a term with free variables into a term. -/
syntax "inst_simp" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| inst_simp $[$location]?) =>
    `(tactic| simp only [inst_app, inst_con, inst_var, assign, List.getD_cons_zero,
      List.getD_cons_succ, ap, apT, List.foldl] $[$location]?)

/-! ## Mirror functions -/

/-- A sublevel: `cst G c` or `var G x k`, with its guard `G`. -/
inductive Sublevel where
  | cst (guard : List Nat) (constant : Nat)
  | var (guard : List Nat) (index offset : Nat)
  deriving DecidableEq, Repr

/-- Sorted insertion, without duplicates, following the rules on `add`. -/
def insertSorted {α : Type} (compare : α → α → Ordering) (element : α) : List α → List α
  | [] => [element]
  | head :: rest =>
      match compare element head with
      | .lt => element :: head :: rest
      | .eq => head :: rest
      | .gt => head :: insertSorted compare element rest

/-- Sorted union, following the rules on `union`. -/
def unionSorted {α : Type} (compare : α → α → Ordering) : List α → List α → List α
  | [], other => other
  | head :: rest, other => insertSorted compare head (unionSorted compare rest other)

/-- Inclusion of sorted sets of naturals, following the rules on `incl`. -/
def inclNat : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | head :: rest, head' :: rest' =>
      match cmpNat head head' with
      | .lt => false
      | .eq => inclNat rest rest'
      | .gt => inclNat (head :: rest) rest'

/-- Comparison of sorted sets, following the rules on `cmpset`. -/
def cmpList {α : Type} (compare : α → α → Ordering) : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | head :: rest, head' :: rest' =>
      match compare head head' with
      | .lt => .lt
      | .eq => cmpList compare rest rest'
      | .gt => .gt

/-- Comparison of sublevels, following the rules on `cmpS`. -/
def cmpSub : Sublevel → Sublevel → Ordering
  | .cst _ _, .var _ _ _ => .lt
  | .var _ _ _, .cst _ _ => .gt
  | .cst guard constant, .cst guard' constant' =>
      match cmpList cmpNat guard guard' with
      | .lt => .lt
      | .eq => cmpNat constant constant'
      | .gt => .gt
  | .var guard index offset, .var guard' index' offset' =>
      match cmpList cmpNat guard guard' with
      | .lt => .lt
      | .eq =>
          match cmpNat index index' with
          | .lt => .lt
          | .eq => cmpNat offset offset'
          | .gt => .gt
      | .gt => .gt

/-- Dominance of sublevels, following the rules on `leS`. -/
def leSub : Sublevel → Sublevel → Bool
  | .var _ _ _, .cst _ _ => false
  | .cst guard constant, .cst guard' constant' => inclNat guard' guard && decide (constant ≤ constant')
  | .cst guard constant, .var guard' _ offset' =>
      inclNat guard' guard && decide (constant ≤ offset' + 1)
  | .var guard index offset, .var guard' index' offset' =>
      inclNat guard' guard && (decide (index = index') && decide (offset ≤ offset'))

/-- The guard of a sublevel. -/
def guardOfSub : Sublevel → List Nat
  | .cst guard _ => guard
  | .var guard _ _ => guard

/-- `addguard u v`: the guard of `v` added to that of `u`. -/
def addguardSub (first second : Sublevel) : Sublevel :=
  match first with
  | .cst guard constant => .cst (unionSorted cmpNat guard (guardOfSub second)) constant
  | .var guard index offset => .var (unionSorted cmpNat guard (guardOfSub second)) index offset

/-- `incr`. -/
def incrSub : Sublevel → Sublevel
  | .cst guard constant => .cst guard (constant + 1)
  | .var guard index offset => .var guard index (offset + 1)

/-- **`Add`, corrected**: insert a sublevel, dropping it if dominated and
dropping the elements it dominates. -/
def addSub (sublevel : Sublevel) : List Sublevel → List Sublevel
  | [] => [sublevel]
  | head :: rest =>
      if leSub sublevel head then head :: rest
      else if leSub head sublevel then addSub sublevel rest
      else insertSorted cmpSub head (addSub sublevel rest)

/-- The set of `succ`. -/
def succSet (set : List Sublevel) : List Sublevel := addSub (.cst [] 1) (set.map incrSub)

/-- The set of `max`. -/
def maxSet (first second : List Sublevel) : List Sublevel :=
  first.foldl (fun accumulated element => addSub element accumulated) second

/-- The set of `imax u v`, `v` given by the nonempty set `second`. -/
def guardedSet (first second accumulated : List Sublevel) : List Sublevel :=
  first.foldl (fun accumulated' element =>
    second.foldl (fun accumulated'' other => addSub (addguardSub element other) accumulated'')
      accumulated') accumulated

/-- The set of `imax`. -/
def imaxSet (first second : List Sublevel) : List Sublevel :=
  match second with
  | [] => []
  | _ :: _ => guardedSet first second second

/-- **The set of sublevels that the rules compute for a level.** -/
def normalSet : LeanLevel → List Sublevel
  | .zero => []
  | .succ level => succSet (normalSet level)
  | .max first second => maxSet (normalSet first) (normalSet second)
  | .imax first second => imaxSet (normalSet first) (normalSet second)
  | .param index => [.var [index] index 0]

/-! ## Codes -/

def natListCode : List Nat → Term
  | [] => ap "nil" [.con "N_code"]
  | head :: rest => ap "cons" [.con "N_code", numeral head, natListCode rest]

def sublevelCode : Sublevel → Term
  | .cst guard constant => ap "cst" [natListCode guard, numeral constant]
  | .var guard index offset => ap "var" [natListCode guard, numeral index, numeral offset]

def setCode : List Sublevel → Term
  | [] => ap "nil" [.con "S_code"]
  | head :: rest => ap "cons" [.con "S_code", sublevelCode head, setCode rest]

/-- The level whose set of sublevels is `set`. -/
def normalCode (set : List Sublevel) : Term := ap "Max" [setCode set]

theorem natListCode_closed : ∀ list : List Nat, Closed (natListCode list)
  | [] => .app .con .con
  | head :: rest => .app (.app (.app .con .con) (numeral_closed head)) (natListCode_closed rest)

theorem sublevelCode_closed : ∀ sublevel : Sublevel, Closed (sublevelCode sublevel)
  | .cst guard constant => .app (.app .con (natListCode_closed guard)) (numeral_closed constant)
  | .var guard index offset =>
      .app (.app (.app .con (natListCode_closed guard)) (numeral_closed index)) (numeral_closed offset)

theorem setCode_closed : ∀ set : List Sublevel, Closed (setCode set)
  | [] => .app .con .con
  | head :: rest => .app (.app (.app .con .con) (sublevelCode_closed head)) (setCode_closed rest)

/-! ## Putting reductions of the values back -/

theorem assign_pointwise {values values' : List Term}
    (pointwise : List.Forall₂ (Reduces pureTheoryExplicit) values values') :
    ∀ index, Reduces pureTheoryExplicit (assign values index) (assign values' index) := by
  induction pointwise with
  | nil => intro index; exact .refl
  | cons head _ ih =>
      intro index
      cases index with
      | zero => simpa [assign] using head
      | succ index => simpa [assign] using ih index

/-- Reduce the values of an instance, all at once. -/
theorem reduces_values {values values' : List Term}
    (pointwise : List.Forall₂ (Reduces pureTheoryExplicit) values values') (skeleton : Term) :
    Reduces pureTheoryExplicit (inst (assign values) skeleton) (inst (assign values') skeleton) :=
  Reduces.instantiate pureTheoryExplicit_orthogonal.closedBodies (assign_pointwise pointwise) skeleton 0

theorem closed_list {values : List Term} (closed : ∀ value ∈ values, Closed value) :
    ∀ value ∈ values, Closed value := closed

/-! ## Naturals -/

/-- `eqN` compares two numerals. -/
theorem eqN_reduces (first second : Nat) :
    Reduces pureTheoryExplicit (ap "eqN" [numeral first, numeral second])
      (boolCode (decide (first = second))) := by
  have unfolded := reducesPure_inst (skeleton := ap "eqN" [.var 0, .var 1])
    (result := ap "case" [.con "B_code", ap "cmpN" [.var 0, .var 1], .con "false", .con "true",
      .con "false"]) (fuel := 10) (by decide +kernel) [numeral first, numeral second]
    (fun value member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact numeral_closed _) rfl rfl
  inst_simp at unfolded
  refine unfolded.trans ?_
  have compared : Reduces pureTheoryExplicit
      (ap "case" [.con "B_code", ap "cmpN" [numeral first, numeral second], .con "false", .con "true",
        .con "false"])
      (ap "case" [.con "B_code", cmpCode (cmpNat first second), .con "false", .con "true",
        .con "false"]) :=
    Reduces.app (Reduces.app (Reduces.app (Reduces.app .refl (cmpN_reduces first second)) .refl) .refl)
      .refl
  refine (by simpa [ap, apT] using compared : Reduces pureTheoryExplicit _ _).trans
    ((case_reduces _ _ _ _ _).trans ?_)
  rcases outcome : cmpNat first second with _ | _ | _
  · have below := cmpNat_eq_lt.mp outcome
    simp [boolCode, show first ≠ second by omega, Relation.ReflTransGen.refl]
  · have same := cmpNat_eq_eq.mp outcome
    simp [boolCode, same, Relation.ReflTransGen.refl]
  · have above := cmpNat_eq_gt.mp outcome
    simp [boolCode, show first ≠ second by omega, Relation.ReflTransGen.refl]

/-- `incl` decides inclusion of sorted sets of naturals. -/
theorem incl_reduces :
    ∀ first second : List Nat,
      Reduces pureTheoryExplicit
        (ap "incl" [.con "N_code", .con "cmpN", natListCode first, natListCode second])
        (boolCode (inclNat first second))
  | [], second => by
      have computed := reducesPure_inst (skeleton := ap "incl" [.con "N_code", .con "cmpN",
        ap "nil" [.con "N_code"], .var 0]) (result := .con "true") (fuel := 1) (by decide +kernel)
        [natListCode second] (fun value member => by
          rw [List.mem_singleton.mp member]; exact natListCode_closed _) rfl rfl
      inst_simp at computed
      simpa [natListCode, inclNat, boolCode, ap, apT] using computed
  | head :: rest, [] => by
      have computed := reducesPure_inst (skeleton := ap "incl" [.con "N_code", .con "cmpN",
        ap "cons" [.con "N_code", .var 0, .var 1], ap "nil" [.con "N_code"]]) (result := .con "false")
        (fuel := 1) (by decide +kernel) [numeral head, natListCode rest] (fun value member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact numeral_closed _
          · exact natListCode_closed _) rfl rfl
      inst_simp at computed
      simpa [natListCode, inclNat, boolCode, ap, apT] using computed
  | head :: rest, head' :: rest' => by
      have computed := reducesPure_inst (skeleton := ap "incl" [.con "N_code", .con "cmpN",
          ap "cons" [.con "N_code", .var 0, .var 1], ap "cons" [.con "N_code", .var 2, .var 3]])
        (result := ap "case" [.con "B_code", ap "cmpN" [.var 0, .var 2], .con "false",
          ap "incl" [.con "N_code", .con "cmpN", .var 1, .var 3],
          ap "incl" [.con "N_code", .con "cmpN", ap "cons" [.con "N_code", .var 0, .var 1], .var 3]])
        (fuel := 1) (by decide +kernel) [numeral head, natListCode rest, numeral head', natListCode rest']
        (fun value member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl
          · exact numeral_closed _
          · exact natListCode_closed _
          · exact numeral_closed _
          · exact natListCode_closed _) rfl rfl
      have inner := reduces_values
        (values := [ap "cmpN" [numeral head, numeral head'],
          ap "incl" [.con "N_code", .con "cmpN", natListCode rest, natListCode rest'],
          ap "incl" [.con "N_code", .con "cmpN", natListCode (head :: rest), natListCode rest']])
        (values' := [cmpCode (cmpNat head head'), boolCode (inclNat rest rest'),
          boolCode (inclNat (head :: rest) rest')])
        (.cons (cmpN_reduces head head') (.cons (incl_reduces rest rest')
          (.cons (incl_reduces (head :: rest) rest') .nil)))
        (ap "case" [.con "B_code", .var 0, .con "false", .var 1, .var 2])
      inst_simp at computed inner
      simp only [natListCode] at inner ⊢
      refine computed.trans (by simpa [ap, apT] using inner) |>.trans ?_
      refine (case_reduces _ _ _ _ _).trans ?_
      rcases outcome : cmpNat head head' with _ | _ | _ <;> simp [inclNat, outcome, boolCode,
        Relation.ReflTransGen.refl]

/-! ## Sorted insertion, union and comparison of sets -/

/-- **`add` inserts into a sorted set**, for any type code and comparison
whose computation is known. -/
theorem insert_reduces {α : Type} (typeCode comparison : Term) (code : α → Term)
    (listCode : List α → Term) (compare : α → α → Ordering)
    (typeCodeClosed : Closed typeCode) (comparisonClosed : Closed comparison)
    (codeClosed : ∀ element, Closed (code element)) (listClosed : ∀ list, Closed (listCode list))
    (listNil : listCode [] = ap "nil" [typeCode])
    (listCons : ∀ head rest, listCode (head :: rest) = ap "cons" [typeCode, code head, listCode rest])
    (compared : ∀ first second,
      Reduces pureTheoryExplicit (apT comparison [code first, code second]) (cmpCode (compare first second))) :
    ∀ (element : α) (list : List α),
      Reduces pureTheoryExplicit (ap "add" [typeCode, comparison, code element, listCode list])
        (listCode (insertSorted compare element list))
  | element, [] => by
      have computed := reducesPure_inst (skeleton := ap "add" [.var 0, .var 1, .var 2, ap "nil" [.var 0]])
        (result := ap "cons" [.var 0, .var 2, ap "nil" [.var 0]]) (fuel := 1) (by decide +kernel)
        [typeCode, comparison, code element] (fun value member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact typeCodeClosed
          · exact comparisonClosed
          · exact codeClosed _) rfl rfl
      inst_simp at computed
      rw [listNil, insertSorted, listCons, listNil]
      simpa [ap, apT] using computed
  | element, head :: rest => by
      have computed := reducesPure_inst
        (skeleton := ap "add" [.var 0, .var 1, .var 2, ap "cons" [.var 0, .var 3, .var 4]])
        (result := ap "case" [ap "set" [.var 0], apT (.var 1) [.var 2, .var 3],
          ap "cons" [.var 0, .var 2, ap "cons" [.var 0, .var 3, .var 4]],
          ap "cons" [.var 0, .var 3, .var 4],
          ap "cons" [.var 0, .var 3, ap "add" [.var 0, .var 1, .var 2, .var 4]]])
        (fuel := 1) (by decide +kernel) [typeCode, comparison, code element, code head, listCode rest]
        (fun value member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl
          · exact typeCodeClosed
          · exact comparisonClosed
          · exact codeClosed _
          · exact codeClosed _
          · exact listClosed _) rfl rfl
      have inner := reduces_values
        (values := [apT comparison [code element, code head],
          ap "add" [typeCode, comparison, code element, listCode rest], typeCode, code element,
          code head, listCode rest])
        (values' := [cmpCode (compare element head), listCode (insertSorted compare element rest),
          typeCode, code element, code head, listCode rest])
        (.cons (compared element head) (.cons (insert_reduces typeCode comparison code listCode compare
          typeCodeClosed comparisonClosed codeClosed listClosed listNil listCons compared element rest)
          (.cons .refl (.cons .refl (.cons .refl (.cons .refl .nil))))))
        (ap "case" [ap "set" [.var 2], .var 0, ap "cons" [.var 2, .var 3, ap "cons" [.var 2, .var 4, .var 5]],
          ap "cons" [.var 2, .var 4, .var 5], ap "cons" [.var 2, .var 4, .var 1]])
      inst_simp at computed inner
      rw [listCons]
      refine computed.trans (by simpa [ap, apT] using inner) |>.trans ?_
      refine (case_reduces _ _ _ _ _).trans ?_
      rcases outcome : compare element head with _ | _ | _
      · simp [insertSorted, outcome, listCons, ap, apT, Relation.ReflTransGen.refl]
      · simp [insertSorted, outcome, listCons, ap, apT, Relation.ReflTransGen.refl]
      · simp [insertSorted, outcome, listCons, ap, apT, Relation.ReflTransGen.refl]

/-- `add` on sorted sets of naturals. -/
theorem insertNat_reduces (element : Nat) (list : List Nat) :
    Reduces pureTheoryExplicit (ap "add" [.con "N_code", .con "cmpN", numeral element, natListCode list])
      (natListCode (insertSorted cmpNat element list)) :=
  insert_reduces (.con "N_code") (.con "cmpN") numeral natListCode cmpNat .con .con numeral_closed
    natListCode_closed rfl (fun _ _ => rfl) (fun first second => by
      simpa [ap, apT] using cmpN_reduces first second) element list

/-- **`union` of sorted sets of naturals.** -/
theorem union_reduces :
    ∀ first second : List Nat,
      Reduces pureTheoryExplicit
        (ap "union" [.con "N_code", .con "cmpN", natListCode first, natListCode second])
        (natListCode (unionSorted cmpNat first second))
  | [], second => by
      have computed := reducesPure_inst (skeleton := ap "union" [.con "N_code", .con "cmpN",
          ap "nil" [.con "N_code"], .var 0]) (result := .var 0) (fuel := 1) (by decide +kernel)
        [natListCode second] (fun value member => by
          rw [List.mem_singleton.mp member]; exact natListCode_closed _) rfl rfl
      inst_simp at computed
      simpa [natListCode, unionSorted, ap, apT] using computed
  | head :: rest, second => by
      have computed := reducesPure_inst (skeleton := ap "union" [.con "N_code", .con "cmpN",
          ap "cons" [.con "N_code", .var 0, .var 1], .var 2])
        (result := ap "add" [.con "N_code", .con "cmpN", .var 0,
          ap "union" [.con "N_code", .con "cmpN", .var 1, .var 2]]) (fuel := 1) (by decide +kernel)
        [numeral head, natListCode rest, natListCode second] (fun value member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact numeral_closed _
          · exact natListCode_closed _
          · exact natListCode_closed _) rfl rfl
      inst_simp at computed
      have inner := union_reduces rest second
      have plugged : Reduces pureTheoryExplicit
          (ap "add" [.con "N_code", .con "cmpN", numeral head,
            ap "union" [.con "N_code", .con "cmpN", natListCode rest, natListCode second]])
          (ap "add" [.con "N_code", .con "cmpN", numeral head, natListCode (unionSorted cmpNat rest second)]) :=
        Reduces.app .refl inner
      simp only [natListCode, unionSorted]
      exact (by simpa [ap, apT] using computed : Reduces pureTheoryExplicit _ _).trans
        (plugged.trans (insertNat_reduces head _))

/-- **`cmpset` compares sorted sets of naturals.** -/
theorem cmpset_reduces :
    ∀ first second : List Nat,
      Reduces pureTheoryExplicit
        (ap "cmpset" [.con "N_code", .con "cmpN", natListCode first, natListCode second])
        (cmpCode (cmpList cmpNat first second))
  | [], [] => reducesPure_of_evaluate (fuel := 1) (by decide +kernel)
  | [], head :: rest => by
      have computed := reducesPure_inst (skeleton := ap "cmpset" [.con "N_code", .con "cmpN",
          ap "nil" [.con "N_code"], ap "cons" [.con "N_code", .var 0, .var 1]]) (result := .con "lt")
        (fuel := 1) (by decide +kernel) [numeral head, natListCode rest] (fun value member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact numeral_closed _
          · exact natListCode_closed _) rfl rfl
      inst_simp at computed
      simpa [natListCode, cmpList, cmpCode, ap, apT] using computed
  | head :: rest, [] => by
      have computed := reducesPure_inst (skeleton := ap "cmpset" [.con "N_code", .con "cmpN",
          ap "cons" [.con "N_code", .var 0, .var 1], ap "nil" [.con "N_code"]]) (result := .con "gt")
        (fuel := 1) (by decide +kernel) [numeral head, natListCode rest] (fun value member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact numeral_closed _
          · exact natListCode_closed _) rfl rfl
      inst_simp at computed
      simpa [natListCode, cmpList, cmpCode, ap, apT] using computed
  | head :: rest, head' :: rest' => by
      have computed := reducesPure_inst (skeleton := ap "cmpset" [.con "N_code", .con "cmpN",
          ap "cons" [.con "N_code", .var 0, .var 1], ap "cons" [.con "N_code", .var 2, .var 3]])
        (result := ap "case" [.con "C_code", ap "cmpN" [.var 0, .var 2], .con "lt",
          ap "cmpset" [.con "N_code", .con "cmpN", .var 1, .var 3], .con "gt"])
        (fuel := 1) (by decide +kernel) [numeral head, natListCode rest, numeral head', natListCode rest']
        (fun value member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl
          · exact numeral_closed _
          · exact natListCode_closed _
          · exact numeral_closed _
          · exact natListCode_closed _) rfl rfl
      have inner := reduces_values
        (values := [ap "cmpN" [numeral head, numeral head'],
          ap "cmpset" [.con "N_code", .con "cmpN", natListCode rest, natListCode rest']])
        (values' := [cmpCode (cmpNat head head'), cmpCode (cmpList cmpNat rest rest')])
        (.cons (cmpN_reduces head head') (.cons (cmpset_reduces rest rest') .nil))
        (ap "case" [.con "C_code", .var 0, .con "lt", .var 1, .con "gt"])
      inst_simp at computed inner
      simp only [natListCode] at inner ⊢
      refine computed.trans (by simpa [ap, apT] using inner) |>.trans ?_
      refine (case_reduces _ _ _ _ _).trans ?_
      rcases outcome : cmpNat head head' with _ | _ | _ <;>
        simp [cmpList, outcome, cmpCode, Relation.ReflTransGen.refl]

/-- `cmpG` is `cmpset N_code cmpN`. -/
theorem cmpG_reduces (first second : List Nat) :
    Reduces pureTheoryExplicit (ap "cmpG" [natListCode first, natListCode second])
      (cmpCode (cmpList cmpNat first second)) := by
  have unfolded := reducesPure_inst (skeleton := ap "cmpG" [.var 0, .var 1])
    (result := ap "cmpset" [.con "N_code", .con "cmpN", .var 0, .var 1]) (fuel := 1) (by decide +kernel)
    [natListCode first, natListCode second] (fun value member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact natListCode_closed _) rfl rfl
  inst_simp at unfolded
  exact (by simpa [ap, apT] using unfolded : Reduces pureTheoryExplicit _ _).trans
    (cmpset_reduces first second)

/-! ## Sublevels -/

/-- Membership in a short list of values, for the closedness side conditions. -/
theorem closed_of_mem {values : List Term} (closed : List.Forall Closed values) :
    ∀ value ∈ values, Closed value :=
  List.forall_iff_forall_mem.mp closed

/-- **`cmpS` compares sublevels.** -/
theorem cmpS_reduces (first second : Sublevel) :
    Reduces pureTheoryExplicit (ap "cmpS" [sublevelCode first, sublevelCode second])
      (cmpCode (cmpSub first second)) := by
  cases first with
  | cst guard constant =>
      cases second with
      | var guard' index' offset' =>
          have computed := reducesPure_inst (skeleton := ap "cmpS" [ap "cst" [.var 0, .var 1],
              ap "var" [.var 2, .var 3, .var 4]]) (result := .con "lt") (fuel := 1) (by decide +kernel)
            [natListCode guard, numeral constant, natListCode guard', numeral index', numeral offset']
            (closed_of_mem (by simp [natListCode_closed, numeral_closed])) rfl rfl
          inst_simp at computed
          simpa [sublevelCode, cmpSub, cmpCode, ap, apT] using computed
      | cst guard' constant' =>
          have computed := reducesPure_inst (skeleton := ap "cmpS" [ap "cst" [.var 0, .var 1],
              ap "cst" [.var 2, .var 3]])
            (result := ap "case" [.con "C_code", ap "cmpG" [.var 0, .var 2], .con "lt",
              ap "cmpN" [.var 1, .var 3], .con "gt"]) (fuel := 1) (by decide +kernel)
            [natListCode guard, numeral constant, natListCode guard', numeral constant']
            (closed_of_mem (by simp [natListCode_closed, numeral_closed])) rfl rfl
          have inner := reduces_values
            (values := [ap "cmpG" [natListCode guard, natListCode guard'],
              ap "cmpN" [numeral constant, numeral constant']])
            (values' := [cmpCode (cmpList cmpNat guard guard'), cmpCode (cmpNat constant constant')])
            (.cons (cmpG_reduces guard guard') (.cons (cmpN_reduces constant constant') .nil))
            (ap "case" [.con "C_code", .var 0, .con "lt", .var 1, .con "gt"])
          inst_simp at computed inner
          refine (by simpa [sublevelCode, ap, apT] using computed : Reduces pureTheoryExplicit _ _).trans
            ((by simpa [ap, apT] using inner : Reduces pureTheoryExplicit _ _).trans
              ((case_reduces _ _ _ _ _).trans ?_))
          rcases outcome : cmpList cmpNat guard guard' with _ | _ | _ <;>
            simp [cmpSub, outcome, cmpCode, Relation.ReflTransGen.refl]
  | var guard index offset =>
      cases second with
      | cst guard' constant' =>
          have computed := reducesPure_inst (skeleton := ap "cmpS" [ap "var" [.var 0, .var 1, .var 2],
              ap "cst" [.var 3, .var 4]]) (result := .con "gt") (fuel := 1) (by decide +kernel)
            [natListCode guard, numeral index, numeral offset, natListCode guard', numeral constant']
            (closed_of_mem (by simp [natListCode_closed, numeral_closed])) rfl rfl
          inst_simp at computed
          simpa [sublevelCode, cmpSub, cmpCode, ap, apT] using computed
      | var guard' index' offset' =>
          have computed := reducesPure_inst (skeleton := ap "cmpS" [ap "var" [.var 0, .var 1, .var 2],
              ap "var" [.var 3, .var 4, .var 5]])
            (result := ap "case" [.con "C_code", ap "cmpG" [.var 0, .var 3], .con "lt",
              ap "case" [.con "C_code", ap "cmpN" [.var 1, .var 4], .con "lt", ap "cmpN" [.var 2, .var 5],
                .con "gt"], .con "gt"]) (fuel := 1) (by decide +kernel)
            [natListCode guard, numeral index, numeral offset, natListCode guard', numeral index',
              numeral offset'] (closed_of_mem (by simp [natListCode_closed, numeral_closed])) rfl rfl
          have inner := reduces_values
            (values := [ap "cmpG" [natListCode guard, natListCode guard'],
              ap "cmpN" [numeral index, numeral index'], ap "cmpN" [numeral offset, numeral offset']])
            (values' := [cmpCode (cmpList cmpNat guard guard'), cmpCode (cmpNat index index'),
              cmpCode (cmpNat offset offset')])
            (.cons (cmpG_reduces guard guard') (.cons (cmpN_reduces index index')
              (.cons (cmpN_reduces offset offset') .nil)))
            (ap "case" [.con "C_code", .var 0, .con "lt",
              ap "case" [.con "C_code", .var 1, .con "lt", .var 2, .con "gt"], .con "gt"])
          inst_simp at computed inner
          refine (by simpa [sublevelCode, ap, apT] using computed : Reduces pureTheoryExplicit _ _).trans
            ((by simpa [ap, apT] using inner : Reduces pureTheoryExplicit _ _).trans
              ((case_reduces _ _ _ _ _).trans ?_))
          rcases outcome : cmpList cmpNat guard guard' with _ | _ | _
          · simp [cmpSub, outcome, cmpCode, Relation.ReflTransGen.refl]
          · simp only [cmpSub, outcome]
            have nested := case_reduces (.con "C_code") (cmpNat index index') (.con "lt")
              (cmpCode (cmpNat offset offset')) (.con "gt")
            refine (by simpa [ap, apT] using nested : Reduces pureTheoryExplicit _ _).trans ?_
            rcases inner' : cmpNat index index' with _ | _ | _ <;>
              simp [cmpCode, Relation.ReflTransGen.refl]
          · simp [cmpSub, outcome, cmpCode, Relation.ReflTransGen.refl]

/-- **`leS` tests dominance of sublevels.** -/
theorem leS_reduces (first second : Sublevel) :
    Reduces pureTheoryExplicit (ap "leS" [sublevelCode first, sublevelCode second])
      (boolCode (leSub first second)) := by
  cases first with
  | var guard index offset =>
      cases second with
      | cst guard' constant' =>
          have computed := reducesPure_inst (skeleton := ap "leS" [ap "var" [.var 0, .var 1, .var 2],
              ap "cst" [.var 3, .var 4]]) (result := .con "false") (fuel := 1) (by decide +kernel)
            [natListCode guard, numeral index, numeral offset, natListCode guard', numeral constant']
            (closed_of_mem (by simp [natListCode_closed, numeral_closed])) rfl rfl
          inst_simp at computed
          simpa [sublevelCode, leSub, boolCode, ap, apT] using computed
      | var guard' index' offset' =>
          have computed := reducesPure_inst (skeleton := ap "leS" [ap "var" [.var 0, .var 1, .var 2],
              ap "var" [.var 3, .var 4, .var 5]])
            (result := ap "and" [ap "incl" [.con "N_code", .con "cmpN", .var 3, .var 0],
              ap "and" [ap "eqN" [.var 1, .var 4], ap "leN" [.var 2, .var 5]]]) (fuel := 1)
            (by decide +kernel)
            [natListCode guard, numeral index, numeral offset, natListCode guard', numeral index',
              numeral offset'] (closed_of_mem (by simp [natListCode_closed, numeral_closed])) rfl rfl
          have inner := reduces_values
            (values := [ap "incl" [.con "N_code", .con "cmpN", natListCode guard', natListCode guard],
              ap "eqN" [numeral index, numeral index'], ap "leN" [numeral offset, numeral offset']])
            (values' := [boolCode (inclNat guard' guard), boolCode (decide (index = index')),
              boolCode (decide (offset ≤ offset'))])
            (.cons (incl_reduces guard' guard) (.cons (eqN_reduces index index')
              (.cons (leN_reduces offset offset') .nil)))
            (ap "and" [.var 0, ap "and" [.var 1, .var 2]])
          inst_simp at computed inner
          refine (by simpa [sublevelCode, ap, apT] using computed : Reduces pureTheoryExplicit _ _).trans
            ((by simpa [ap, apT] using inner : Reduces pureTheoryExplicit _ _).trans ?_)
          have innerAnd := and_reduces (decide (index = index')) (decide (offset ≤ offset'))
          refine (Reduces.app .refl (by simpa [ap, apT] using innerAnd)).trans ?_
          simpa [leSub, ap, apT] using and_reduces (inclNat guard' guard)
            (decide (index = index') && decide (offset ≤ offset'))
  | cst guard constant =>
      cases second with
      | cst guard' constant' =>
          have computed := reducesPure_inst (skeleton := ap "leS" [ap "cst" [.var 0, .var 1],
              ap "cst" [.var 2, .var 3]])
            (result := ap "and" [ap "incl" [.con "N_code", .con "cmpN", .var 2, .var 0],
              ap "leN" [.var 1, .var 3]]) (fuel := 1) (by decide +kernel)
            [natListCode guard, numeral constant, natListCode guard', numeral constant']
            (closed_of_mem (by simp [natListCode_closed, numeral_closed])) rfl rfl
          have inner := reduces_values
            (values := [ap "incl" [.con "N_code", .con "cmpN", natListCode guard', natListCode guard],
              ap "leN" [numeral constant, numeral constant']])
            (values' := [boolCode (inclNat guard' guard), boolCode (decide (constant ≤ constant'))])
            (.cons (incl_reduces guard' guard) (.cons (leN_reduces constant constant') .nil))
            (ap "and" [.var 0, .var 1])
          inst_simp at computed inner
          refine (by simpa [sublevelCode, ap, apT] using computed : Reduces pureTheoryExplicit _ _).trans
            ((by simpa [ap, apT] using inner : Reduces pureTheoryExplicit _ _).trans ?_)
          simpa [leSub, ap, apT] using and_reduces (inclNat guard' guard) (decide (constant ≤ constant'))
      | var guard' index' offset' =>
          have computed := reducesPure_inst (skeleton := ap "leS" [ap "cst" [.var 0, .var 1],
              ap "var" [.var 2, .var 3, .var 4]])
            (result := ap "and" [ap "incl" [.con "N_code", .con "cmpN", .var 2, .var 0],
              ap "leN" [.var 1, ap "s" [.var 4]]]) (fuel := 1) (by decide +kernel)
            [natListCode guard, numeral constant, natListCode guard', numeral index', numeral offset']
            (closed_of_mem (by simp [natListCode_closed, numeral_closed])) rfl rfl
          have inner := reduces_values
            (values := [ap "incl" [.con "N_code", .con "cmpN", natListCode guard', natListCode guard],
              ap "leN" [numeral constant, ap "s" [numeral offset']]])
            (values' := [boolCode (inclNat guard' guard), boolCode (decide (constant ≤ offset' + 1))])
            (.cons (incl_reduces guard' guard) (.cons (leN_reduces constant (offset' + 1) :
              Reduces pureTheoryExplicit (ap "leN" [numeral constant, ap "s" [numeral offset']]) _) .nil))
            (ap "and" [.var 0, .var 1])
          inst_simp at computed inner
          refine (by simpa [sublevelCode, ap, apT] using computed : Reduces pureTheoryExplicit _ _).trans
            ((by simpa [ap, apT] using inner : Reduces pureTheoryExplicit _ _).trans ?_)
          simpa [leSub, ap, apT] using and_reduces (inclNat guard' guard) (decide (constant ≤ offset' + 1))

theorem guard_reduces (sublevel : Sublevel) :
    Reduces pureTheoryExplicit (ap "guard" [sublevelCode sublevel]) (natListCode (guardOfSub sublevel)) := by
  cases sublevel with
  | cst guard constant =>
      have computed := reducesPure_inst (skeleton := ap "guard" [ap "cst" [.var 0, .var 1]]) (result := .var 0)
        (fuel := 1) (by decide +kernel) [natListCode guard, numeral constant]
        (closed_of_mem (by simp [natListCode_closed, numeral_closed])) rfl rfl
      inst_simp at computed
      simpa [sublevelCode, guardOfSub, ap, apT] using computed
  | var guard index offset =>
      have computed := reducesPure_inst (skeleton := ap "guard" [ap "var" [.var 0, .var 1, .var 2]])
        (result := .var 0) (fuel := 1) (by decide +kernel) [natListCode guard, numeral index, numeral offset]
        (closed_of_mem (by simp [natListCode_closed, numeral_closed])) rfl rfl
      inst_simp at computed
      simpa [sublevelCode, guardOfSub, ap, apT] using computed

/-- **`addguard` extends the guard.** -/
theorem addguard_reduces (first second : Sublevel) :
    Reduces pureTheoryExplicit (ap "addguard" [sublevelCode first, sublevelCode second])
      (sublevelCode (addguardSub first second)) := by
  cases first with
  | cst guard constant =>
      have computed := reducesPure_inst (skeleton := ap "addguard" [ap "cst" [.var 0, .var 1], .var 2])
        (result := ap "cst" [ap "union" [.con "N_code", .con "cmpN", .var 0, ap "guard" [.var 2]], .var 1])
        (fuel := 1) (by decide +kernel) [natListCode guard, numeral constant, sublevelCode second]
        (closed_of_mem (by simp [natListCode_closed, numeral_closed, sublevelCode_closed])) rfl rfl
      have guarded := reduces_values
        (values := [ap "guard" [sublevelCode second], natListCode guard, numeral constant])
        (values' := [natListCode (guardOfSub second), natListCode guard, numeral constant])
        (.cons (guard_reduces second) (.cons .refl (.cons .refl .nil)))
        (ap "cst" [ap "union" [.con "N_code", .con "cmpN", .var 1, .var 0], .var 2])
      have united := reduces_values
        (values := [ap "union" [.con "N_code", .con "cmpN", natListCode guard, natListCode (guardOfSub second)],
          numeral constant])
        (values' := [natListCode (unionSorted cmpNat guard (guardOfSub second)), numeral constant])
        (.cons (union_reduces guard (guardOfSub second)) (.cons .refl .nil)) (ap "cst" [.var 0, .var 1])
      inst_simp at computed guarded united
      refine (computed : Reduces pureTheoryExplicit
        (ap "addguard" [sublevelCode (.cst guard constant), sublevelCode second])
        (ap "cst" [ap "union" [.con "N_code", .con "cmpN", natListCode guard,
          ap "guard" [sublevelCode second]], numeral constant])).trans ?_
      refine (guarded : Reduces pureTheoryExplicit _
        (ap "cst" [ap "union" [.con "N_code", .con "cmpN", natListCode guard,
          natListCode (guardOfSub second)], numeral constant])).trans ?_
      exact united
  | var guard index offset =>
      have computed := reducesPure_inst
        (skeleton := ap "addguard" [ap "var" [.var 0, .var 1, .var 2], .var 3])
        (result := ap "var" [ap "union" [.con "N_code", .con "cmpN", .var 0, ap "guard" [.var 3]], .var 1,
          .var 2]) (fuel := 1) (by decide +kernel)
        [natListCode guard, numeral index, numeral offset, sublevelCode second]
        (closed_of_mem (by simp [natListCode_closed, numeral_closed, sublevelCode_closed])) rfl rfl
      have guarded := reduces_values
        (values := [ap "guard" [sublevelCode second], natListCode guard, numeral index, numeral offset])
        (values' := [natListCode (guardOfSub second), natListCode guard, numeral index, numeral offset])
        (.cons (guard_reduces second) (.cons .refl (.cons .refl (.cons .refl .nil))))
        (ap "var" [ap "union" [.con "N_code", .con "cmpN", .var 1, .var 0], .var 2, .var 3])
      have united := reduces_values
        (values := [ap "union" [.con "N_code", .con "cmpN", natListCode guard, natListCode (guardOfSub second)],
          numeral index, numeral offset])
        (values' := [natListCode (unionSorted cmpNat guard (guardOfSub second)), numeral index,
          numeral offset])
        (.cons (union_reduces guard (guardOfSub second)) (.cons .refl (.cons .refl .nil)))
        (ap "var" [.var 0, .var 1, .var 2])
      inst_simp at computed guarded united
      refine (computed : Reduces pureTheoryExplicit
        (ap "addguard" [sublevelCode (.var guard index offset), sublevelCode second])
        (ap "var" [ap "union" [.con "N_code", .con "cmpN", natListCode guard,
          ap "guard" [sublevelCode second]], numeral index, numeral offset])).trans ?_
      refine (guarded : Reduces pureTheoryExplicit _
        (ap "var" [ap "union" [.con "N_code", .con "cmpN", natListCode guard,
          natListCode (guardOfSub second)], numeral index, numeral offset])).trans ?_
      exact united

theorem incr_reduces (sublevel : Sublevel) :
    Reduces pureTheoryExplicit (ap "incr" [sublevelCode sublevel]) (sublevelCode (incrSub sublevel)) := by
  cases sublevel with
  | cst guard constant =>
      have computed := reducesPure_inst (skeleton := ap "incr" [ap "cst" [.var 0, .var 1]])
        (result := ap "cst" [.var 0, ap "s" [.var 1]]) (fuel := 1) (by decide +kernel)
        [natListCode guard, numeral constant]
        (closed_of_mem (by simp [natListCode_closed, numeral_closed])) rfl rfl
      inst_simp at computed
      simpa [sublevelCode, incrSub, numeral, ap, apT] using computed
  | var guard index offset =>
      have computed := reducesPure_inst (skeleton := ap "incr" [ap "var" [.var 0, .var 1, .var 2]])
        (result := ap "var" [.var 0, .var 1, ap "s" [.var 2]]) (fuel := 1) (by decide +kernel)
        [natListCode guard, numeral index, numeral offset]
        (closed_of_mem (by simp [natListCode_closed, numeral_closed])) rfl rfl
      inst_simp at computed
      simpa [sublevelCode, incrSub, numeral, ap, apT] using computed

/-! ## Sets of sublevels -/

/-- `add` on sorted sets of sublevels. -/
theorem insertSub_reduces (sublevel : Sublevel) (set : List Sublevel) :
    Reduces pureTheoryExplicit (ap "add" [.con "S_code", .con "cmpS", sublevelCode sublevel, setCode set])
      (setCode (insertSorted cmpSub sublevel set)) :=
  insert_reduces (.con "S_code") (.con "cmpS") sublevelCode setCode cmpSub .con .con sublevelCode_closed
    setCode_closed rfl (fun _ _ => rfl) (fun first second => by
      simpa [ap, apT] using cmpS_reduces first second) sublevel set

/-- `Incr` increments every sublevel. -/
theorem Incr_reduces :
    ∀ set : List Sublevel,
      Reduces pureTheoryExplicit (ap "Incr" [setCode set]) (setCode (set.map incrSub))
  | [] => reducesPure_of_evaluate (fuel := 1) (by decide +kernel)
  | head :: rest => by
      have computed := reducesPure_inst (skeleton := ap "Incr" [ap "cons" [.con "S_code", .var 0, .var 1]])
        (result := ap "cons" [.con "S_code", ap "incr" [.var 0], ap "Incr" [.var 1]]) (fuel := 1)
        (by decide +kernel) [sublevelCode head, setCode rest]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      have inner := reduces_values (values := [ap "incr" [sublevelCode head], ap "Incr" [setCode rest]])
        (values' := [sublevelCode (incrSub head), setCode (rest.map incrSub)])
        (.cons (incr_reduces head) (.cons (Incr_reduces rest) .nil))
        (ap "cons" [.con "S_code", .var 0, .var 1])
      inst_simp at computed inner
      exact (computed : Reduces pureTheoryExplicit (ap "Incr" [setCode (head :: rest)]) _).trans inner

/-- **`Add`, corrected, computes `addSub`.** -/
theorem Add_reduces (sublevel : Sublevel) :
    ∀ set : List Sublevel,
      Reduces pureTheoryExplicit (ap "Add" [sublevelCode sublevel, setCode set])
        (setCode (addSub sublevel set))
  | [] => by
      have computed := reducesPure_inst (skeleton := ap "Add" [.var 0, ap "nil" [.con "S_code"]])
        (result := ap "cons" [.con "S_code", .var 0, ap "nil" [.con "S_code"]]) (fuel := 1)
        (by decide +kernel) [sublevelCode sublevel]
        (closed_of_mem (by simp [sublevelCode_closed])) rfl rfl
      inst_simp at computed
      exact computed
  | head :: rest => by
      have computed := reducesPure_inst
        (skeleton := ap "Add" [.var 0, ap "cons" [.con "S_code", .var 1, .var 2]])
        (result := ap "if" [ap "set" [.con "S_code"], ap "leS" [.var 0, .var 1],
          ap "cons" [.con "S_code", .var 1, .var 2],
          ap "if" [ap "set" [.con "S_code"], ap "leS" [.var 1, .var 0], ap "Add" [.var 0, .var 2],
            ap "add" [.con "S_code", .con "cmpS", .var 1, ap "Add" [.var 0, .var 2]]]]) (fuel := 1)
        (by decide +kernel) [sublevelCode sublevel, sublevelCode head, setCode rest]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      have inner := reduces_values
        (values := [ap "leS" [sublevelCode sublevel, sublevelCode head],
          ap "leS" [sublevelCode head, sublevelCode sublevel], ap "Add" [sublevelCode sublevel, setCode rest],
          sublevelCode head, setCode rest])
        (values' := [boolCode (leSub sublevel head), boolCode (leSub head sublevel),
          setCode (addSub sublevel rest), sublevelCode head, setCode rest])
        (.cons (leS_reduces sublevel head) (.cons (leS_reduces head sublevel)
          (.cons (Add_reduces sublevel rest) (.cons .refl (.cons .refl .nil)))))
        (ap "if" [ap "set" [.con "S_code"], .var 0, ap "cons" [.con "S_code", .var 3, .var 4],
          ap "if" [ap "set" [.con "S_code"], .var 1, .var 2,
            ap "add" [.con "S_code", .con "cmpS", .var 3, .var 2]]])
      inst_simp at computed inner
      refine (computed : Reduces pureTheoryExplicit (ap "Add" [sublevelCode sublevel, setCode (head :: rest)])
        _).trans (inner.trans ?_)
      refine (if_reduces _ _ _ _).trans ?_
      by_cases dominated : leSub sublevel head
      · simp only [dominated, if_true, addSub]
        exact .refl
      · simp only [dominated, Bool.false_eq_true, if_false]
        refine (if_reduces _ _ _ _).trans ?_
        by_cases dominates : leSub head sublevel
        · simp only [dominates, if_true, addSub, dominated, Bool.false_eq_true, if_false]
          exact .refl
        · simp only [dominates, Bool.false_eq_true, if_false, addSub, dominated]
          exact insertSub_reduces head (addSub sublevel rest)

/-- **`fold … Add` inserts the elements of the first set into the second.** -/
theorem foldAdd_reduces :
    ∀ first second : List Sublevel,
      Reduces pureTheoryExplicit
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], .con "Add", setCode first, setCode second])
        (setCode (maxSet first second))
  | [], second => by
      have computed := reducesPure_inst (skeleton := ap "fold" [.con "S_code", ap "set" [.con "S_code"],
          .con "Add", ap "nil" [.con "S_code"], .var 0]) (result := .var 0) (fuel := 1) (by decide +kernel)
        [setCode second] (closed_of_mem (by simp [setCode_closed])) rfl rfl
      inst_simp at computed
      exact computed
  | head :: rest, second => by
      have computed := reducesPure_inst (skeleton := ap "fold" [.con "S_code", ap "set" [.con "S_code"],
          .con "Add", ap "cons" [.con "S_code", .var 0, .var 1], .var 2])
        (result := ap "fold" [.con "S_code", ap "set" [.con "S_code"], .con "Add", .var 1,
          ap "Add" [.var 0, .var 2]]) (fuel := 1) (by decide +kernel)
        [sublevelCode head, setCode rest, setCode second]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      have inner := reduces_values (values := [ap "Add" [sublevelCode head, setCode second], setCode rest])
        (values' := [setCode (addSub head second), setCode rest])
        (.cons (Add_reduces head second) (.cons .refl .nil))
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], .con "Add", .var 1, .var 0])
      inst_simp at computed inner
      exact (computed : Reduces pureTheoryExplicit
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], .con "Add", setCode (head :: rest),
          setCode second]) _).trans (inner.trans (foldAdd_reduces rest (addSub head second)))

/-- `fold … (Addguard u)` inserts `addguard u v` for every `v`. -/
theorem foldAddguard_reduces (sublevel : Sublevel) :
    ∀ set accumulated : List Sublevel,
      Reduces pureTheoryExplicit
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "Addguard" [sublevelCode sublevel],
          setCode set, setCode accumulated])
        (setCode (set.foldl (fun accumulated' other => addSub (addguardSub sublevel other) accumulated')
          accumulated))
  | [], accumulated => by
      have computed := reducesPure_inst (skeleton := ap "fold" [.con "S_code", ap "set" [.con "S_code"],
          ap "Addguard" [.var 0], ap "nil" [.con "S_code"], .var 1]) (result := .var 1) (fuel := 1)
        (by decide +kernel) [sublevelCode sublevel, setCode accumulated]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      inst_simp at computed
      exact computed
  | head :: rest, accumulated => by
      have computed := reducesPure_inst (skeleton := ap "fold" [.con "S_code", ap "set" [.con "S_code"],
          ap "Addguard" [.var 0], ap "cons" [.con "S_code", .var 1, .var 2], .var 3])
        (result := ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "Addguard" [.var 0], .var 2,
          ap "Addguard" [.var 0, .var 1, .var 3]]) (fuel := 1) (by decide +kernel)
        [sublevelCode sublevel, sublevelCode head, setCode rest, setCode accumulated]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      have unfolded := reducesPure_inst (skeleton := ap "Addguard" [.var 0, .var 1, .var 2])
        (result := ap "Add" [ap "addguard" [.var 0, .var 1], .var 2]) (fuel := 3) (by decide +kernel)
        [sublevelCode sublevel, sublevelCode head, setCode accumulated]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      have guarded := reduces_values
        (values := [ap "addguard" [sublevelCode sublevel, sublevelCode head], setCode accumulated])
        (values' := [sublevelCode (addguardSub sublevel head), setCode accumulated])
        (.cons (addguard_reduces sublevel head) (.cons .refl .nil)) (ap "Add" [.var 0, .var 1])
      inst_simp at computed unfolded guarded
      have step : Reduces pureTheoryExplicit
          (ap "Addguard" [sublevelCode sublevel, sublevelCode head, setCode accumulated])
          (setCode (addSub (addguardSub sublevel head) accumulated)) :=
        (unfolded.trans guarded).trans (Add_reduces _ _)
      have inner := reduces_values
        (values := [ap "Addguard" [sublevelCode sublevel, sublevelCode head, setCode accumulated],
          sublevelCode sublevel, setCode rest])
        (values' := [setCode (addSub (addguardSub sublevel head) accumulated), sublevelCode sublevel,
          setCode rest])
        (.cons step (.cons .refl (.cons .refl .nil)))
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "Addguard" [.var 1], .var 2, .var 0])
      inst_simp at inner
      exact (computed : Reduces pureTheoryExplicit
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "Addguard" [sublevelCode sublevel],
          setCode (head :: rest), setCode accumulated]) _).trans
        (inner.trans (foldAddguard_reduces sublevel rest _))

/-- `fold … (FoldAddguard F)` computes `guardedSet`. -/
theorem foldFoldAddguard_reduces (guards : List Sublevel) :
    ∀ set accumulated : List Sublevel,
      Reduces pureTheoryExplicit
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "FoldAddguard" [setCode guards],
          setCode set, setCode accumulated])
        (setCode (guardedSet set guards accumulated))
  | [], accumulated => by
      have computed := reducesPure_inst (skeleton := ap "fold" [.con "S_code", ap "set" [.con "S_code"],
          ap "FoldAddguard" [.var 0], ap "nil" [.con "S_code"], .var 1]) (result := .var 1) (fuel := 1)
        (by decide +kernel) [setCode guards, setCode accumulated]
        (closed_of_mem (by simp [setCode_closed])) rfl rfl
      inst_simp at computed
      exact computed
  | head :: rest, accumulated => by
      have computed := reducesPure_inst (skeleton := ap "fold" [.con "S_code", ap "set" [.con "S_code"],
          ap "FoldAddguard" [.var 0], ap "cons" [.con "S_code", .var 1, .var 2], .var 3])
        (result := ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "FoldAddguard" [.var 0], .var 2,
          ap "FoldAddguard" [.var 0, .var 1, .var 3]]) (fuel := 1) (by decide +kernel)
        [setCode guards, sublevelCode head, setCode rest, setCode accumulated]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      have unfolded := reducesPure_inst (skeleton := ap "FoldAddguard" [.var 0, .var 1, .var 2])
        (result := ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "Addguard" [.var 1], .var 0, .var 2])
        (fuel := 4) (by decide +kernel) [setCode guards, sublevelCode head, setCode accumulated]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      inst_simp at computed unfolded
      have step : Reduces pureTheoryExplicit
          (ap "FoldAddguard" [setCode guards, sublevelCode head, setCode accumulated])
          (setCode (guards.foldl (fun accumulated' other => addSub (addguardSub head other) accumulated')
            accumulated)) :=
        unfolded.trans (foldAddguard_reduces head guards accumulated)
      have inner := reduces_values
        (values := [ap "FoldAddguard" [setCode guards, sublevelCode head, setCode accumulated],
          setCode guards, setCode rest])
        (values' := [setCode (guards.foldl (fun accumulated' other =>
            addSub (addguardSub head other) accumulated') accumulated), setCode guards, setCode rest])
        (.cons step (.cons .refl (.cons .refl .nil)))
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "FoldAddguard" [.var 1], .var 2, .var 0])
      inst_simp at inner
      exact (computed : Reduces pureTheoryExplicit
        (ap "fold" [.con "S_code", ap "set" [.con "S_code"], ap "FoldAddguard" [setCode guards],
          setCode (head :: rest), setCode accumulated]) _).trans
        (inner.trans (foldFoldAddguard_reduces guards rest _))

/-! ## Levels -/

theorem succ_reduces (set : List Sublevel) :
    Reduces pureTheoryExplicit (succ (normalCode set)) (normalCode (succSet set)) := by
  have computed := reducesPure_inst (skeleton := succ (ap "Max" [.var 0]))
    (result := ap "Max" [ap "Add" [ap "cst" [ap "nil" [.con "N_code"], ap "s" [zeroN]], ap "Incr" [.var 0]]])
    (fuel := 1) (by decide +kernel) [setCode set] (closed_of_mem (by simp [setCode_closed])) rfl rfl
  have inner := reduces_values (values := [ap "Incr" [setCode set]]) (values' := [setCode (set.map incrSub)])
    (.cons (Incr_reduces set) .nil)
    (ap "Max" [ap "Add" [ap "cst" [ap "nil" [.con "N_code"], ap "s" [zeroN]], .var 0]])
  simp only [succ, zeroN] at computed inner
  inst_simp at computed inner
  exact (computed : Reduces pureTheoryExplicit (succ (normalCode set)) _).trans
    (inner.trans (Reduces.app .refl (Add_reduces (.cst [] 1) (set.map incrSub))))

theorem max_reduces (first second : List Sublevel) :
    Reduces pureTheoryExplicit (ap "max" [normalCode first, normalCode second])
      (normalCode (maxSet first second)) := by
  have computed := reducesPure_inst (skeleton := ap "max" [ap "Max" [.var 0], ap "Max" [.var 1]])
    (result := ap "Max" [ap "fold" [.con "S_code", ap "set" [.con "S_code"], .con "Add", .var 0, .var 1]])
    (fuel := 2) (by decide +kernel) [setCode first, setCode second]
    (closed_of_mem (by simp [setCode_closed])) rfl rfl
  inst_simp at computed
  exact (computed : Reduces pureTheoryExplicit (ap "max" [normalCode first, normalCode second]) _).trans
    (Reduces.app .refl (foldAdd_reduces first second))

theorem imax_reduces (first second : List Sublevel) :
    Reduces pureTheoryExplicit (imax (normalCode first) (normalCode second))
      (normalCode (imaxSet first second)) := by
  cases second with
  | nil =>
      have computed := reducesPure_inst (skeleton := imax (ap "Max" [.var 0]) (ap "Max" [ap "nil" [.con "S_code"]]))
        (result := ap "Max" [ap "nil" [.con "S_code"]]) (fuel := 1) (by decide +kernel) [setCode first]
        (closed_of_mem (by simp [setCode_closed])) rfl rfl
      simp only [imax] at computed
      inst_simp at computed
      exact computed
  | cons head rest =>
      have computed := reducesPure_inst
        (skeleton := imax (ap "Max" [.var 0]) (ap "Max" [ap "cons" [.con "S_code", .var 1, .var 2]]))
        (result := ap "Max" [ap "fold" [.con "S_code", ap "set" [.con "S_code"],
          ap "FoldAddguard" [ap "cons" [.con "S_code", .var 1, .var 2]], .var 0,
          ap "cons" [.con "S_code", .var 1, .var 2]]]) (fuel := 2) (by decide +kernel)
        [setCode first, sublevelCode head, setCode rest]
        (closed_of_mem (by simp [sublevelCode_closed, setCode_closed])) rfl rfl
      simp only [imax] at computed
      inst_simp at computed
      exact (computed : Reduces pureTheoryExplicit (imax (normalCode first) (normalCode (head :: rest))) _).trans
        (Reduces.app .refl (foldFoldAddguard_reduces (head :: rest) first (head :: rest)))

/-- **The normalization theorem for level codes**: for every level, with any
level variables, its code reduces to the code of `normalSet`. -/
theorem code_reduces_normalSet :
    ∀ level : LeanLevel, Reduces pureTheoryExplicit (code level) (normalCode (normalSet level))
  | .zero => zero_reduces_pureExplicit
  | .succ level => (Reduces.app .refl (code_reduces_normalSet level)).trans (succ_reduces _)
  | .max first second =>
      (Reduces.app (Reduces.app .refl (code_reduces_normalSet first)) (code_reduces_normalSet second)).trans
        (max_reduces _ _)
  | .imax first second =>
      (Reduces.app (Reduces.app .refl (code_reduces_normalSet first)) (code_reduces_normalSet second)).trans
        (imax_reduces _ _)
  | .param _ => .refl

/-! ## Conversion of level codes is equality of the computed sets -/

/-- The constants of codes of sets of sublevels. -/
def setConstructors : List String := levelConstructors ++ ["var"]

/-- A theory given by a signature and rules defines none of the constants of
the codes of sets, when none of them has a body or heads a rule. -/
theorem setConstructors_rigid {signature : Sig} {rules : List RewriteRule}
    (checked : ∀ name ∈ setConstructors, lookupBody signature name = none ∧
      rules.all (fun rule => headConst rule.lhs != some name) = true) :
    ∀ name ∈ setConstructors, ¬ (Theory.ofSig signature rules).Defines name := by
  intro name member defines
  obtain ⟨undefined, unheaded⟩ := checked name member
  rcases defines with defined | ⟨rule, ruleMember, head⟩
  · exact defined undefined
  · have absent := List.all_eq_true.mp unheaded rule ruleMember
    simp [head] at absent

theorem numeral_setConstructors (count : Nat) :
    ∀ name ∈ constantsOf (numeral count), name ∈ setConstructors := fun name member =>
  List.mem_append_left _ (numeral_constants count name member)

theorem natListCode_constants : ∀ (list : List Nat), ∀ name ∈ constantsOf (natListCode list),
    name ∈ setConstructors
  | [], name, member => by
      simp [natListCode, ap, apT, constantsOf] at member
      rcases member with rfl | rfl <;> simp [setConstructors, levelConstructors]
  | head :: rest, name, member => by
      simp only [natListCode, ap, apT, List.foldl, constantsOf, List.mem_append, List.mem_singleton] at member
      rcases member with ((rfl | rfl) | inner) | inner
      · simp [setConstructors, levelConstructors]
      · simp [setConstructors, levelConstructors]
      · exact numeral_setConstructors head name inner
      · exact natListCode_constants rest name inner

theorem sublevelCode_constants : ∀ (sublevel : Sublevel), ∀ name ∈ constantsOf (sublevelCode sublevel),
    name ∈ setConstructors
  | .cst guard constant, name, member => by
      simp only [sublevelCode, ap, apT, List.foldl, constantsOf, List.mem_append, List.mem_singleton] at member
      rcases member with (rfl | inner) | inner
      · simp [setConstructors, levelConstructors]
      · exact natListCode_constants guard name inner
      · exact numeral_setConstructors constant name inner
  | .var guard index offset, name, member => by
      simp only [sublevelCode, ap, apT, List.foldl, constantsOf, List.mem_append, List.mem_singleton] at member
      rcases member with ((rfl | inner) | inner) | inner
      · simp [setConstructors]
      · exact natListCode_constants guard name inner
      · exact numeral_setConstructors index name inner
      · exact numeral_setConstructors offset name inner

theorem setCode_constants : ∀ (set : List Sublevel), ∀ name ∈ constantsOf (setCode set),
    name ∈ setConstructors
  | [], name, member => by
      simp [setCode, ap, apT, constantsOf] at member
      rcases member with rfl | rfl <;> simp [setConstructors, levelConstructors]
  | head :: rest, name, member => by
      simp only [setCode, ap, apT, List.foldl, constantsOf, List.mem_append, List.mem_singleton] at member
      rcases member with ((rfl | rfl) | inner) | inner
      · simp [setConstructors, levelConstructors]
      · simp [setConstructors, levelConstructors]
      · exact sublevelCode_constants head name inner
      · exact setCode_constants rest name inner

theorem natListCode_flat : ∀ list : List Nat, flatBelow 0 (natListCode list) = true
  | [] => rfl
  | head :: rest => by simp [natListCode, ap, apT, flatBelow, numeral_flat, natListCode_flat rest]

theorem sublevelCode_flat : ∀ sublevel : Sublevel, flatBelow 0 (sublevelCode sublevel) = true
  | .cst guard constant => by simp [sublevelCode, ap, apT, flatBelow, numeral_flat, natListCode_flat]
  | .var guard index offset => by simp [sublevelCode, ap, apT, flatBelow, numeral_flat, natListCode_flat]

theorem setCode_flat : ∀ set : List Sublevel, flatBelow 0 (setCode set) = true
  | [] => rfl
  | head :: rest => by simp [setCode, ap, apT, flatBelow, sublevelCode_flat, setCode_flat rest]

/-- **The code of every set of sublevels is normal**, in every theory with
headed rules that defines none of its constants. -/
theorem normalCode_normal {theory : Theory} (headed : theory.Headed)
    (rigid : ∀ name ∈ setConstructors, ¬ theory.Defines name) (set : List Sublevel) :
    IsNormal (Step theory) (normalCode set) := by
  refine normal_of_rigidConstants headed _ ?_ ?_
  · simp [normalCode, ap, apT, flatBelow, setCode_flat]
  · intro name member
    apply rigid
    simp only [normalCode, ap, apT, List.foldl, constantsOf, List.mem_append, List.mem_singleton] at member
    rcases member with rfl | inner
    · simp [setConstructors, levelConstructors]
    · exact setCode_constants set name inner

theorem natListCode_injective : ∀ {first second : List Nat}, natListCode first = natListCode second →
    first = second
  | [], [], _ => rfl
  | [], _ :: _, same => by simp [natListCode, ap, apT] at same
  | _ :: _, [], same => by simp [natListCode, ap, apT] at same
  | head :: rest, head' :: rest', same => by
      simp only [natListCode, ap, apT, List.foldl, Term.app.injEq, true_and] at same
      rw [numeral_injective same.1, natListCode_injective same.2]

theorem sublevelCode_injective : ∀ {first second : Sublevel}, sublevelCode first = sublevelCode second →
    first = second
  | .cst _ _, .cst _ _, same => by
      simp only [sublevelCode, ap, apT, List.foldl, Term.app.injEq, true_and] at same
      rw [natListCode_injective same.1, numeral_injective same.2]
  | .var _ _ _, .var _ _ _, same => by
      simp only [sublevelCode, ap, apT, List.foldl, Term.app.injEq, true_and] at same
      rw [natListCode_injective same.1.1, numeral_injective same.1.2, numeral_injective same.2]
  | .cst _ _, .var _ _ _, same => by simp [sublevelCode, ap, apT] at same
  | .var _ _ _, .cst _ _, same => by simp [sublevelCode, ap, apT] at same

theorem setCode_injective : ∀ {first second : List Sublevel}, setCode first = setCode second →
    first = second
  | [], [], _ => rfl
  | [], _ :: _, same => by simp [setCode, ap, apT] at same
  | _ :: _, [], same => by simp [setCode, ap, apT] at same
  | head :: rest, head' :: rest', same => by
      simp only [setCode, ap, apT, List.foldl, Term.app.injEq, true_and] at same
      rw [sublevelCode_injective same.1, setCode_injective same.2]

theorem normalCode_injective {first second : List Sublevel} (same : normalCode first = normalCode second) :
    first = second := by
  simp only [normalCode, ap, apT, List.foldl, Term.app.injEq, true_and] at same
  exact setCode_injective same

/-- **The conversion of the theory, on level codes, is equality of the
computed sets**, for all levels, with any level variables. -/
theorem conv_code_iff_normalSet {first second : LeanLevel} :
    Conv leanTheoryExplicit (code first) (code second) ↔ normalSet first = normalSet second := by
  have rigid : ∀ name ∈ setConstructors, ¬ leanTheoryExplicit.Defines name :=
    setConstructors_rigid (by decide +kernel)
  constructor
  · intro convertible
    by_contra distinct
    exact not_conv_of_normal leanTheoryExplicit_confluent
      (normalCode_normal leanTheoryExplicit_headed rigid _)
      (normalCode_normal leanTheoryExplicit_headed rigid _)
      (fun same => distinct (normalCode_injective same))
      (.trans _ _ _ (.symm _ _ ((code_reduces_normalSet first).mono pureTheoryExplicit_extends).conv)
        (.trans _ _ _ convertible ((code_reduces_normalSet second).mono pureTheoryExplicit_extends).conv))
  · intro same
    exact Joinable.conv ⟨_, (code_reduces_normalSet first).mono pureTheoryExplicit_extends,
      same ▸ (code_reduces_normalSet second).mono pureTheoryExplicit_extends⟩

#print axioms cmpS_reduces
#print axioms leS_reduces
#print axioms addguard_reduces
#print axioms Add_reduces
#print axioms code_reduces_normalSet
#print axioms normalCode_normal
#print axioms normalCode_injective
#print axioms conv_code_iff_normalSet

end Mettapedia.GSLT.Dedukti.LeanMinus
