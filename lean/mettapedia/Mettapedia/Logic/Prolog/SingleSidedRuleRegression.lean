import Mettapedia.Logic.Prolog.ReaderProgram
import Mettapedia.Logic.Prolog.SourceRuntimeRegression

/-!
# Single-sided rule execution regressions

These fixtures enter through the concrete Prolog reader and execute on the
one canonical `Logic.LP.RuntimeQuery` machine.  They distinguish SWI-style
single-sided head matching from ordinary unification and pin guard-delayed
commitment without introducing a rule evaluator.
-/

namespace Mettapedia.Logic.Prolog.SingleSidedRuleRegression

open ReaderOperator SourceSignature

private def emptyImports : ReaderDirective.ImportProfile Unit :=
  fun _ => .ok []

private def load (source : String) : Option SourceSignature.Program :=
  (ReaderProgram.loadSourceWith
    (ReaderDirective.effectWith emptyImports) defaults source).toOption.map
      (fun result => result.program)

def rulesSource : String :=
  "specific(a, Y) => Y = specific.\n\
   specific(_, Y) => Y = fallback.\n\
   guarded(a, Y), fail => Y = first.\n\
   guarded(_, Y) => Y = second.\n\
   committed(a, Y), true => Y = first.\n\
   committed(_, Y) => Y = second.\n\
   shape(pair(A, B), Y) => Y = matched.\n\
   shape(_, Y) => Y = fallback.\n\
   ordinary(a)."

def rulesProgram : SourceSignature.Program :=
  (load rulesSource).getD []

private def x : SourceSignature.Term := var "X" 0
private def y : SourceSignature.Term := var "Y" 0

def answersForY (goal : SourceSignature.Goal) :
    Option (List String × Nat × Nat) :=
  SourceRuntimeRegression.runAtomsFor rulesProgram goal { spelling := "Y", occurrence := 0 }

/-- Ordinary unification would bind caller `X = a` and select the first rule.
SSU must reject that head and reach the generic fallback with `X` untouched. -/
def callerBindingAnswers : Option (List String × Nat × Nat) :=
  answersForY (SourceSignature.call "specific" [x, y])

def callerBindingIsRejected : Bool :=
  callerBindingAnswers ==
    some (["fallback"], 0, 0)

/-- A ground caller matches the specific rule, whose inserted cut commits it
before the generic fallback can run. -/
def groundMatchAnswers : Option (List String × Nat × Nat) :=
  answersForY (SourceSignature.call "specific" [atom "a", y])

def groundMatchCommits : Bool :=
  groundMatchAnswers ==
    some (["specific"], 0, 0)

/-- Guard failure occurs before the rule cut, so the later rule remains live. -/
def failedGuardAnswers : Option (List String × Nat × Nat) :=
  answersForY (SourceSignature.call "guarded" [atom "a", y])

def failedGuardDoesNotCommit : Bool :=
  failedGuardAnswers ==
    some (["second"], 0, 0)

/-- Guard success reaches the cut and prunes both guard alternatives and
later rules before the body produces its output. -/
def successfulGuardAnswers : Option (List String × Nat × Nat) :=
  answersForY (SourceSignature.call "committed" [atom "a", y])

def successfulGuardCommits : Bool :=
  successfulGuardAnswers ==
    some (["first"], 0, 0)

/-- Matching may bind fresh variables in the copied head.  Rejecting every
trail growth (rather than only caller-prefix writes) would fail this case. -/
def freshHeadBindingAnswers : Option (List String × Nat × Nat) :=
  answersForY (SourceSignature.call "shape"
    [compound "pair" [atom "a", atom "b"], y])

def freshHeadBindingsAreAllowed : Bool :=
  freshHeadBindingAnswers ==
    some (["matched"], 0, 0)

/-- The extension does not weaken ordinary clause heads: they still bind a
caller variable by symmetric unification. -/
def ordinaryHeadAnswers : Option (List String × Nat × Nat) :=
  SourceRuntimeRegression.runAtomsFor rulesProgram
      (SourceSignature.call "ordinary" [x])
      { spelling := "X", occurrence := 0 }

def ordinaryHeadStillBindsCaller : Bool :=
  ordinaryHeadAnswers ==
    some (["a"], 0, 0)

#guard rulesProgram.length == 9
#guard callerBindingIsRejected
#guard groundMatchCommits
#guard failedGuardDoesNotCommit
#guard successfulGuardCommits
#guard freshHeadBindingsAreAllowed
#guard ordinaryHeadStillBindsCaller

end Mettapedia.Logic.Prolog.SingleSidedRuleRegression
