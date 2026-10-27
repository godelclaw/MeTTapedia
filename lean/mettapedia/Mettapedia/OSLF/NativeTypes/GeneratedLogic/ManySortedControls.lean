import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySorted
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Controls: sorted verdicts at the front door

A language with two sorts (`courier`): names `A`, `B` and `Next(n)`; processes `Nil`, `Send(n, p)` and `Fwd(n, p)`, with
the rule `Fwd(n, p) ⇒ Send(Next(n), p)`. Sorted formulas are asked at the front door through their guarded translation,
and the exact reduction turns each answer into a verdict about the sorted structure of the language's reference
structure (`sorted_of_proved`, `not_sorted_of_refuted`):

- the process `Fwd(A, Nil)` steps to a `Send` whose name is `Next(A)` and whose process is `Nil` (`forward_sends`), and
  it eventually reaches `Send(Next(A), Nil)`, as a fixed point over processes (`forward_reaches`);
- the same term is not a name, so the formula fails there at the sort of names (`forward_not_a_name`);
- the name `Next(A)` is built by `Next` from the name `A` (`next_built`);
- `Send(A, Nil)` is not built by `Send` from a process and a name, in that order (`send_sorts_checked`);
- the process `Send(A, Nil)` has no step (`send_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySorted.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

def name (label : String) (arity : ℕ) : GrammarRule :=
  { label := label, category := "Name", params := (List.range arity).map fun i => .simple s!"n{i}" (.base "Name"),
    syntaxPattern := [] }

def process (label : String) (withName : Bool) : GrammarRule :=
  { label := label, category := "Proc",
    params := if withName then [.simple "n" (.base "Name"), .simple "p" (.base "Proc")] else [], syntaxPattern := [] }

/-- `Fwd(n, p) ⇒ Send(Next(n), p)`. -/
def forwardRule : RewriteRule :=
  { name := "Forward", typeContext := [("n", .base "Name"), ("p", .base "Proc")], premises := [],
    left := .apply "Fwd" [.fvar "n", .fvar "p"], right := .apply "Send" [.apply "Next" [.fvar "n"], .fvar "p"],
    bindings := none }

def courier : LanguageDef :=
  { name := "Courier", types := ["Name", "Proc"],
    terms := [name "A" 0, name "B" 0, name "Next" 1, process "Nil" false, process "Send" true, process "Fwd" true],
    equations := [], rewrites := [forwardRule] }

def a : Pattern := .apply "A" []
def next (n : Pattern) : Pattern := .apply "Next" [n]
def nil : Pattern := .apply "Nil" []
def send (n p : Pattern) : Pattern := .apply "Send" [n, p]
def fwd (n p : Pattern) : Pattern := .apply "Fwd" [n, p]

abbrev Reference := referenceStructure RelationEnv.empty courier

/-- The sorted structure of the language: the elements of a sort are those typed at its base type. -/
abbrev Sorted := restrict Reference TypeExpr.base

/-- An element of a sort. -/
abbrev at' (sort : String) (term : Pattern) (typed : Reference.typed term (.base sort)) : Sorted.Element :=
  lift (T := Reference) (toType := TypeExpr.base) sort term typed

/-- The sorted answer of the front door: the guarded translation of a closed sorted formula at a sort. -/
def answer (formula : SFormula String []) (sort : String) (term : Pattern) : Answer :=
  ask RelationEnv.empty [] courier 2 (guard TypeExpr.base formula sort) term none 4

/-- **A proved sorted answer is a verdict about the sorted structure.** -/
theorem sorted_of_proved {formula : SFormula String []} {sort : String} {term : Pattern} {evidence : Evidence}
    (answered : answer formula sort term = .proved evidence) :
    ∃ typed, Sorted.ssat Env.closed formula (at' sort term typed) :=
  (guard_iff_closed formula sort term).mp (ask_proved answered)

/-- **So is a refuted one.** -/
theorem not_sorted_of_refuted {formula : SFormula String []} {sort : String} {term : Pattern} {evidence : Evidence}
    (answered : answer formula sort term = .refuted evidence) :
    ¬ ∃ typed, Sorted.ssat Env.closed formula (at' sort term typed) :=
  fun holds => ask_refuted answered ((guard_iff_closed formula sort term).mpr holds)

/-! ## Steps and constructors across sorts -/

/-- Steps to a `Send` whose name is `Next(A)` and whose process is `Nil`. -/
def sendsNextA : SFormula String [] :=
  .possibly .any (.built "Send" (.cons "Name" (.built "Next" (.cons "Name" (.is a) .nil)) (.cons "Proc" (.is nil) .nil)))

theorem forward_sends_answer : answer sendsNextA "Proc" (fwd a nil) = .proved (.closedRegion 4) := by
  decide +kernel

/-- **The process `Fwd(A, Nil)` steps to `Send(Next(A), Nil)`, read through the sorts of its parts.** -/
theorem forward_sends : ∃ typed, Sorted.ssat Env.closed sendsNextA (at' "Proc" (fwd a nil) typed) :=
  sorted_of_proved forward_sends_answer

theorem forward_not_a_name_answer : answer sendsNextA "Name" (fwd a nil) = .refuted (.closedRegion 4) := by
  decide +kernel

/-- **`Fwd(A, Nil)` is not a name**, so the formula fails there at the sort of names. -/
theorem forward_not_a_name : ¬ ∃ typed, Sorted.ssat Env.closed sendsNextA (at' "Name" (fwd a nil) typed) :=
  not_sorted_of_refuted forward_not_a_name_answer

/-- Eventually `Send(Next(A), Nil)`, as a least fixed point over processes. -/
def reachesSend : SFormula String [] :=
  .mu "Proc" (.or (.is (send (next a) nil)) (.possibly .any (.var ⟨0, by decide⟩)))

theorem forward_reaches_answer : answer reachesSend "Proc" (fwd a nil) = .proved (.exploration 4) := by
  decide +kernel

/-- **`Fwd(A, Nil)` eventually reaches `Send(Next(A), Nil)`.** -/
theorem forward_reaches : ∃ typed, Sorted.ssat Env.closed reachesSend (at' "Proc" (fwd a nil) typed) :=
  sorted_of_proved forward_reaches_answer

def nextOfA : SFormula String [] := .built "Next" (.cons "Name" (.is a) .nil)

theorem next_built_answer : answer nextOfA "Name" (next a) = .proved (.closedRegion 4) := by
  decide +kernel

/-- **The name `Next(A)` is built by `Next` from the name `A`.** -/
theorem next_built : ∃ typed, Sorted.ssat Env.closed nextOfA (at' "Name" (next a) typed) :=
  sorted_of_proved next_built_answer

/-- Built by `Send` from a process and then a name. -/
def sendWrongSorts : SFormula String [] := .built "Send" (.cons "Proc" .top (.cons "Name" .top .nil))

theorem send_sorts_checked_answer : answer sendWrongSorts "Proc" (send a nil) = .refuted (.closedRegion 4) := by
  decide +kernel

/-- **`Send(A, Nil)` is not built from a process and then a name**: its parts have the other sorts. -/
theorem send_sorts_checked :
    ¬ ∃ typed, Sorted.ssat Env.closed sendWrongSorts (at' "Proc" (send a nil) typed) :=
  not_sorted_of_refuted send_sorts_checked_answer

/-- Some step. -/
def steps : SFormula String [] := .possibly .any .top

theorem send_stuck_answer : answer steps "Proc" (send a nil) = .refuted (.closedRegion 4) := by
  decide +kernel

/-- **The process `Send(A, Nil)` has no step.** -/
theorem send_stuck : ¬ ∃ typed, Sorted.ssat Env.closed steps (at' "Proc" (send a nil) typed) :=
  not_sorted_of_refuted send_stuck_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySorted.Controls
