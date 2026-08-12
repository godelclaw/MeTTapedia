import Mettapedia.Logic.Prolog.ReaderConditional

namespace Mettapedia.Logic.Prolog.ReaderConditionalRegression

open ReaderConditional ReaderDirective ReaderLoader ReaderOperator ReaderSource
  SourceSignature

inductive ProfileError where
  | unexpectedlyEvaluated
  | unknown
deriving DecidableEq, Repr

private def emptyImports : ReaderDirective.ImportProfile Unit :=
  fun _ => .ok []

private def profile : ReaderConditional.ConditionProfile ProfileError
  | .call atom =>
      match atom.symbol.name, List.ofFn atom.args with
      | "on", [] => .ok true
      | "off", [] => .ok false
      | "explode", [] => .error .unexpectedlyEvaluated
      | _, _ => .error .unknown
  | _ => .error .unknown

private def clauseName? : ReaderSource.Form -> Option String
  | .clause clause => some clause.head.symbol.name
  | _ => none

private def loadedClauseNames (source : String) : Option (List String) :=
  match ReaderConditional.loadSourceWith profile
      (ReaderDirective.effectWith emptyImports) defaults source with
  | .ok loaded => some (loaded.forms.filterMap clauseName?)
  | .error _ => none

def trueArmOnly : Bool :=
  loadedClauseNames
      ":- if(on). true_arm. :- else. false_arm. :- endif." =
    some ["true_arm"]

#guard trueArmOnly

def falseArmOnly : Bool :=
  loadedClauseNames
      ":- if(off). true_arm. :- else. false_arm. :- endif." =
    some ["false_arm"]

#guard falseArmOnly

def elifSelectsFirstSuccessfulArm : Bool :=
  loadedClauseNames
      ":- if(off). first. :- elif(on). second. :- else. third. :- endif." =
    some ["second"]

#guard elifSelectsFirstSuccessfulArm

/-- The `explode` condition would fail loading if evaluated.  The outer
inactive arm therefore discriminates real nesting from a flat directive
filter. -/
def inactiveNestedConditionIsNotEvaluated : Bool :=
  loadedClauseNames
      ":- if(off). :- if(explode). bad. :- else. also_bad. :- endif. \
       :- else. good. :- endif." =
    some ["good"]

#guard inactiveNestedConditionIsNotEvaluated

/-- An operator declaration in an inactive arm must not affect parsing after
the arm.  A processor that merely filtered forms after running their effects
would incorrectly accept this source. -/
def inactiveOperatorHasNoReadTimeEffect : Bool :=
  match ReaderConditional.loadSourceWith profile
      (ReaderDirective.effectWith emptyImports) defaults
      ":- if(off). :- op(500, xfy, likes). :- endif. a likes b." with
  | .error (.term _) => true
  | _ => false

#guard inactiveOperatorHasNoReadTimeEffect

def unterminatedFailsClosed : Bool :=
  match ReaderConditional.loadSourceWith profile noEffect defaults
      ":- if(on). retained." with
  | .error (.effect .unterminated) => true
  | _ => false

#guard unterminatedFailsClosed

def unmatchedElseFailsClosed : Bool :=
  match ReaderConditional.loadSourceWith profile noEffect defaults
      ":- else. retained." with
  | .error (.effect (.noIf "else")) => true
  | _ => false

#guard unmatchedElseFailsClosed

def duplicateElseFailsClosed : Bool :=
  match ReaderConditional.loadSourceWith profile noEffect defaults
      ":- if(on). first. :- else. second. :- else. third. :- endif." with
  | .error (.effect .duplicateElse) => true
  | _ => false

#guard duplicateElseFailsClosed

end Mettapedia.Logic.Prolog.ReaderConditionalRegression
