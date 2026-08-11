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

/-- The first three clauses are SWI 10.1.9 `library(lists):member/2`; the
remaining clauses are local discriminators for the `memberchk/2` expansion. -/
def memberRegressionSource : String :=
  "member(El, [H|T]) :- member_(T, El, H).\n\
   member_(_, El, El).\n\
   member_([H|T], El, _) :- member_(T, El, H).\n\
   ordinary(X) :- memberchk(X, [a,b]).\n\
   dynamic(X) :- call(memberchk(X, [a,b])).\n\
   restored(X) :- memberchk(pair(X,X), [pair(a,b),pair(c,c)])."

def memberRegressionProgram : SourceSignature.Program :=
  load memberRegressionSource |>.getD []

def memberchkOrdinaryGoal : SourceSignature.Goal :=
  SourceSignature.call "ordinary" [var "X" 0]

def memberchkDynamicGoal : SourceSignature.Goal :=
  SourceSignature.call "dynamic" [var "X" 0]

def memberchkRestoredGoal : SourceSignature.Goal :=
  SourceSignature.call "restored" [var "X" 0]

/-- Source `memberchk/2` commits to the first answer of the real loaded
`member/2` definition instead of installing a second list scanner. -/
def memberchkUsesLoadedMemberOnce : Bool :=
  SourceRuntimeRegression.runAtoms
      memberRegressionProgram memberchkOrdinaryGoal ==
    some (["a"], 0, 0)

/-- Heap-built meta-calls use the same typed expansion as written source. -/
def dynamicMemberchkUsesSameExpansion : Bool :=
  SourceRuntimeRegression.runAtoms
      memberRegressionProgram memberchkDynamicGoal ==
    some (["a"], 0, 0)

/-- A failed earlier member candidate cannot leak trial bindings into the
selected candidate; the canonical choice checkpoint restores `X` first. -/
def memberchkRestoresBeforeSelectedCandidate : Bool :=
  SourceRuntimeRegression.runAtoms
      memberRegressionProgram memberchkRestoredGoal ==
    some (["c"], 0, 0)

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

/-- A variable grammar body bound to a proper list is interpreted as DCG
terminals at runtime.  Ordinary `call/N` would instead attempt `[|]/4`, so
this is the anti-shortcut discriminator for the dynamic phrase seam. -/
def variableListBodyExecutes : Bool :=
  succeeds "emit(Cs) --> Cs."
    (SourceSignature.call "emit"
      [list [atom "a", atom "b"], list [atom "a", atom "b"], nil])

/-- Repeated variables inside the runtime list body remain one heap identity;
the decoder must not read back and rematerialize its elements independently. -/
def variableListBodyPreservesSharing : Bool :=
  SourceRuntimeRegression.runCount
      (load "emit(Cs) --> Cs." |>.getD [])
      (SourceSignature.call "emit"
        [list [var "X" 0, var "X" 0],
          list [atom "a", atom "b"], nil]) == some (0, 0, 0)

/-- Dynamic string grammar bodies consume their character codes through
engine-owned allocation rather than source-time expansion. -/
def variableStringBodyExecutes : Bool :=
  succeeds "emit(S) --> S."
    (SourceSignature.call "emit"
      [string "ab", list [integer 97, integer 98], nil])

/-- Source `phrase/2` elaborates to the same `phrase/3` engine request with an
explicit empty rest list. -/
def sourcePhraseTwoExecutes : Bool :=
  succeeds "one --> [a]. via(Input) :- phrase(one, Input)."
    (SourceSignature.call "via" [list [atom "a"]])

/-- `phrase/3` preserves the caller-supplied rest root exactly. -/
def sourcePhraseThreeRetainsRest : Bool :=
  succeeds "one --> [a]. via(Input, Rest) :- phrase(one, Input, Rest)."
    (SourceSignature.call "via"
      [list [atom "a", atom "b"], list [atom "b"]])

/-- Braced goals in a dynamic grammar body re-enter the ordinary typed goal
loop and preserve the DCG state. -/
def variableBracedBodyExecutes : Bool :=
  succeeds "delegate(G) --> G."
    (SourceSignature.call "delegate"
      [compound "{}" [compound "=" [atom "a", atom "a"]], nil, nil])

/-- A cut dynamically supplied to `phrase/2` is contained by phrase's own
entry boundary and cannot prune a later clause of its caller. -/
def dynamicCutRetainsCallerClause : Bool :=
  SourceRuntimeRegression.runAtoms
      (load "outer(a) :- phrase(!, []), fail. outer(c)." |>.getD [])
      (SourceSignature.call "outer" [var "X" 0]) ==
    some (["c"], 0, 0)

/-- Ordinary meta-call does not silently acquire DCG list semantics. -/
def ordinaryCallDoesNotInterpretListAsDcg : Bool :=
  SourceRuntimeRegression.runCount []
      (SourceSignature.call "call"
        [list [atom "a"], list [atom "a"], nil]) == some (0, 0, 0)

/-- An unbound dynamic grammar body is a typed runtime error, not silent
failure or an invented empty grammar. -/
def unboundVariableBodyFailsClosed : Bool :=
  match load "delegate(G) --> G." with
  | none => false
  | some program =>
      match SourceRuntimeRegression.runQueryError? program
          (SourceSignature.call "delegate"
            [var "G" 0, nil, nil]) with
      | some .dcgBodyUnbound => true
      | _ => false

/-- `phrase/3` rejects a non-list state before the grammar body can run. -/
def invalidPhraseStateFailsClosed : Bool :=
  match load "one --> [a]." with
  | none => false
  | some program =>
      match SourceRuntimeRegression.runQueryError? program
          (SourceSignature.call "phrase" [atom "one", atom "not_a_list", nil]) with
      | some .invalidDcgState => true
      | _ => false

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
#guard memberchkUsesLoadedMemberOnce
#guard dynamicMemberchkUsesSameExpansion
#guard memberchkRestoresBeforeSelectedCandidate
#guard bracedGoalExecutes
#guard disjunctionExecutes
#guard stringTerminalExecutes
#guard variableListBodyExecutes
#guard variableListBodyPreservesSharing
#guard variableStringBodyExecutes
#guard sourcePhraseTwoExecutes
#guard sourcePhraseThreeRetainsRest
#guard variableBracedBodyExecutes
#guard dynamicCutRetainsCallerClause
#guard ordinaryCallDoesNotInterpretListAsDcg
#guard unboundVariableBodyFailsClosed
#guard invalidPhraseStateFailsClosed
#guard generatedStatesDoNotCaptureSource
#guard variableBodyUsesPhrase

end Mettapedia.Logic.Prolog.ReaderDCGRegression
