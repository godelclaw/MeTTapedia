import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveJudgmentReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode

/-!
# Constructor-source emission of finite structural evidence

The printer shares data and theorem source, including data for the maintained
replay interfaces with a supplied printer for declaration-root codes. Emitted
source is untrusted: consumers must elaborate its proofs or replay its data
against the original requested judgment.
This is an internal evidence-emission utility, not a portable wire protocol
or a correctness theorem for a source parser.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralEvidenceSource

variable {Head : Type} {RootCode : Nat → Type} [Repr Head]

/-- Type names refer to aliases declared by the emitting client. Scope is
part of every interned key, so distinct binder arities cannot share a node. -/
structure Types where
  head : String
  term : String
  root : String
  step : String
  conversion : String
  typing : String
  context : String

structure Document where
  names : Std.HashMap (String × String) String := {}
  definitions : Array String := #[]

private def indexed (type : String) (n : Nat) : String := type ++ " " ++ toString n

private def internDeclaration (keyword type body : String) : StateM Document String := do
  let document ← get
  let key := (keyword ++ " " ++ type, body)
  if let some name := document.names[key]? then return name
  let name := "e" ++ toString document.definitions.size
  set (Document.mk (document.names.insert key name)
    (document.definitions.push ("private " ++ keyword ++ " " ++ name ++ " : " ++ type ++ " :=\n" ++ body)))
  return name

/-- Share emitted data nodes between producers using the same document. -/
def intern (type body : String) : StateM Document String := internDeclaration "def" type body

/-- Proof source is emitted as a theorem and checked by the receiving kernel.
This printer does not validate the supplied proposition or proof text. -/
def internTheorem (type body : String) : StateM Document String := internDeclaration "theorem" type body

private def app (type name : String) (arguments : List (StateM Document String)) :
    StateM Document String := do
  let arguments ← arguments.mapM id
  intern type (name ++ String.join (arguments.map fun argument => " (" ++ argument ++ ")"))

variable (types : Types) (root : {n : Nat} → RootCode n → String)

private def head (value : Head) : StateM Document String := intern types.head (reprStr value)
private def term {n : Nat} (value : Tm Head n) : StateM Document String :=
  intern (indexed types.term n) (reprStr value)

def step : {n : Nat} → StructuralConversionCode.StepCode Head RootCode n → StateM Document String
  | n, .betaPi body argument => app (indexed types.step n) ".betaPi" [term types body, term types argument]
  | n, .betaSigmaFst first second => app (indexed types.step n) ".betaSigmaFst" [term types first, term types second]
  | n, .betaSigmaSnd first second => app (indexed types.step n) ".betaSigmaSnd" [term types first, term types second]
  | n, .head first second => app (indexed types.step n) ".head" [head types first, head types second]
  | n, .root code => app (indexed types.step n) ".root" [intern (indexed types.root n) (root code)]
  | n, .congPiDom code body => app (indexed types.step n) ".congPiDom" [step code, term types body]
  | n, .congPiCod domain code => app (indexed types.step n) ".congPiCod" [term types domain, step code]
  | n, .congSigmaDom code body => app (indexed types.step n) ".congSigmaDom" [step code, term types body]
  | n, .congSigmaCod domain code => app (indexed types.step n) ".congSigmaCod" [term types domain, step code]
  | n, .congIdTy code first second => app (indexed types.step n) ".congIdTy" [step code, term types first, term types second]
  | n, .congIdLeft type code second => app (indexed types.step n) ".congIdLeft" [term types type, step code, term types second]
  | n, .congIdRight type first code => app (indexed types.step n) ".congIdRight" [term types type, term types first, step code]
  | n, .congLam code => app (indexed types.step n) ".congLam" [step code]
  | n, .congAppFun code argument => app (indexed types.step n) ".congAppFun" [step code, term types argument]
  | n, .congAppArg function code => app (indexed types.step n) ".congAppArg" [term types function, step code]
  | n, .congPairFst code second => app (indexed types.step n) ".congPairFst" [step code, term types second]
  | n, .congPairSnd first code => app (indexed types.step n) ".congPairSnd" [term types first, step code]
  | n, .congFst code => app (indexed types.step n) ".congFst" [step code]
  | n, .congSnd code => app (indexed types.step n) ".congSnd" [step code]
  | n, .congRefl code => app (indexed types.step n) ".congRefl" [step code]

def conversion : {n : Nat} → StructuralConversionCode.Code Head RootCode n → StateM Document String
  | n, .single code => app (indexed types.conversion n) ".single" [step types root code]
  | n, .refl value => app (indexed types.conversion n) ".refl" [term types value]
  | n, .symm code => app (indexed types.conversion n) ".symm" [conversion code]
  | n, .trans first second => app (indexed types.conversion n) ".trans" [conversion first, conversion second]

def typing : {n : Nat} → StructuralTypingReplay.Code Head
    (StructuralConversionCode.Code Head RootCode) n → StateM Document String
  | n, .headType => app (indexed types.typing n) ".headType" []
  | n, .var => app (indexed types.typing n) ".var" []
  | n, .const level formation => app (indexed types.typing n) ".const" [head types level, typing formation]
  | n, .piForm u v first second => app (indexed types.typing n) ".piForm" [head types u, head types v, typing first, typing second]
  | n, .sigmaForm u v first second => app (indexed types.typing n) ".sigmaForm" [head types u, head types v, typing first, typing second]
  | n, .lamIntro level formation body => app (indexed types.typing n) ".lamIntro" [head types level, typing formation, typing body]
  | n, .appElim domain body function argument =>
      app (indexed types.typing n) ".appElim" [term types domain, term types body, typing function, typing argument]
  | n, .pairIntro level formation first second =>
      app (indexed types.typing n) ".pairIntro" [head types level, typing formation, typing first, typing second]
  | n, .fstElim body pair => app (indexed types.typing n) ".fstElim" [term types body, typing pair]
  | n, .sndElim domain body pair => app (indexed types.typing n) ".sndElim" [term types domain, term types body, typing pair]
  | n, .idForm level formation first second =>
      app (indexed types.typing n) ".idForm" [head types level, typing formation, typing first, typing second]
  | n, .reflIntro type value => app (indexed types.typing n) ".reflIntro" [term types type, typing value]
  | n, .cumul level value => app (indexed types.typing n) ".cumul" [head types level, typing value]
  | n, .convert source level value formation code =>
      app (indexed types.typing n) ".convert" [term types source, head types level, typing value,
        typing formation, conversion types root code]

def context : {n : Nat} → StructuralTypingReplay.ContextCode Head
    (StructuralConversionCode.Code Head RootCode) n → StateM Document String
  | _, .nil => app (indexed types.context 0) ".nil" []
  | _, @StructuralTypingReplay.ContextCode.snoc _ _ n prior level formation =>
      app (indexed types.context (n + 1)) ".snoc" [context prior, head types level, typing types root formation]

end StructuralEvidenceSource
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
