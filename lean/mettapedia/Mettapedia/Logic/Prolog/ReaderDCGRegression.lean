import Mettapedia.Logic.Prolog.ReaderProgram
import Mettapedia.Logic.Prolog.SourceRuntimeRegression

namespace Mettapedia.Logic.Prolog.ReaderDCGRegression

open ReaderOperator SourceSignature

private def emptyImports : ReaderDirective.ImportProfile Unit :=
  fun _ => .ok []

private def load (source : String) : Option SourceSignature.Program :=
  (ReaderProgram.loadSourceWith
    (ReaderDirective.effectWith emptyImports) defaults source).toOption.map
      (fun result => result.program)

private def succeeds (source : String) (goal : SourceSignature.Goal) : Bool :=
  match load source with
  | none => false
  | some program =>
      SourceRuntimeRegression.runCount program goal == some (1, 0, 0)

def terminalSharingExecutes : Bool :=
  succeeds "pair(X) --> [X, X]."
    (SourceSignature.call "pair"
      [atom "a", list [atom "a", atom "a"], nil])

def bracedGoalExecutes : Bool :=
  succeeds "guarded(X) --> {X = a}, [X]."
    (SourceSignature.call "guarded" [atom "a", list [atom "a"], nil])

def disjunctionExecutes : Bool :=
  succeeds "choice --> [a] ; [b]."
    (SourceSignature.call "choice" [list [atom "b"], nil])

def stringTerminalExecutes : Bool :=
  succeeds "hello --> \"ab\"."
    (SourceSignature.call "hello"
      [list [integer 97, integer 98], nil])

/-- Generated state variables start above source occurrences, even when a
source variable uses the expander's diagnostic spelling. -/
def generatedStatesDoNotCaptureSource : Bool :=
  match load "same(_DCG) --> [_DCG]." with
  | some [clause] =>
      match List.ofFn clause.head.args with
      | [.var source, .var input, .var output] =>
          source != input && source != output && input != output
      | _ => false
  | _ => false

/-- Variable grammar bodies are represented by the ordinary `phrase/3`
predicate rather than interpreted by a hidden DCG executor. -/
def variableBodyUsesPhrase : Bool :=
  match load "delegate(G) --> G." with
  | some [clause] =>
      match clause.body with
      | .call atom => atom.symbol.name = "phrase" && atom.symbol.arity = 3
      | _ => false
  | _ => false

#guard terminalSharingExecutes
#guard bracedGoalExecutes
#guard disjunctionExecutes
#guard stringTerminalExecutes
#guard generatedStatesDoNotCaptureSource
#guard variableBodyUsesPhrase

end Mettapedia.Logic.Prolog.ReaderDCGRegression
