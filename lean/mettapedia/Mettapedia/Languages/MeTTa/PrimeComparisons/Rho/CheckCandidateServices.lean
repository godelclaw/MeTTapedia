import Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.ScopedSharedEvidence

/-!
# Executable optional declared-calculus rho comparison

The request and response alphabet is `0`, `1`, `e`, `a`, `p`, without
whitespace. Requests bind the installed declarations, complete source context,
service role and actual native fields. Successful execution returns the
original request together with the computed result. Equality evidence and
selected native execution remain distinct requests.
-/

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.CheckCandidateServices

open Mettapedia.OSLF.Binding RhoSchema
open Mettapedia.OSLF.Binding.WireCodec Binary
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId Presentation
open ScopedRepresentation ScopedRepresentation.DeclarationProfile
open ScopedServices
open ScopedServiceWire

namespace ExplicitRuntime
open ScopedRepresentation.Operations ScopedRepresentation.Conversion
open Mettapedia.OSLF.NativeTypes.Certificates

private def require (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError ("explicit rho: " ++ name))

private def z {n : Nat} : NativeTerm n := .const zeroName
private def qz {n : Nat} : NativeTerm n := quote z
private def dz {n : Nat} : NativeTerm n := drop qz

private def proofs : List (Σ claim : Explicit.Claim, Explicit.Derivation claim) :=
  [ ⟨_, Explicit.reflexivity (context := []) (sort := .pr) z⟩
  , ⟨_, Explicit.symmetry (Explicit.unit (context := []) z)⟩
  , ⟨_, Explicit.transitivity (Explicit.unit (context := []) z) (Explicit.reflexivity z)⟩
  , ⟨_, Explicit.commutativity (context := []) z dz⟩
  , ⟨_, Explicit.associativity (context := []) z z dz⟩
  , ⟨_, Explicit.unit (context := []) z⟩
  , ⟨_, Explicit.eta (context := []) qz⟩
  , ⟨_, Explicit.parallelCongruence (Explicit.unit (context := []) z) (Explicit.reflexivity dz)⟩
  , ⟨_, Explicit.outputCongruence (Explicit.eta (context := []) qz) (Explicit.unit z)⟩
  , ⟨_, Explicit.inputCongruence (Explicit.eta (context := []) qz)
      (Explicit.reflexivity (context := [.nm]) (sort := .pr) (drop (.var 0) : NativeTerm 1))⟩
  , ⟨_, Explicit.quoteCongruence (Explicit.unit (context := []) z)⟩
  , ⟨_, Explicit.dropCongruence (Explicit.eta (context := []) qz)⟩
  ]

private def captureSource : NativeTerm 1 :=
  input (.var 0) (parallel (drop (.var 0)) (drop (quote (drop (.var 1)))))
private def captureDestination : NativeTerm 1 :=
  input (.var 0) (parallel (drop (.var 0)) (drop (.var 1)))
private def captureProof : Explicit.Derivation
    ⟨[.nm], .pr, captureSource, captureDestination⟩ :=
  Explicit.inputCongruence (Explicit.reflexivity (.var 0))
    (Explicit.parallelCongruence (Explicit.reflexivity (drop (.var 0)))
      (Explicit.dropCongruence (Explicit.eta (.var 1))))
private def captureAction : Presentation.Sub Tower.Head 1 0 := fun _ => qz
private def captureAfterSource : NativeTerm 0 :=
  input qz (parallel (drop (.var 0)) (drop (quote (drop qz))))
private def captureAfterTarget : NativeTerm 0 :=
  input qz (parallel (drop (.var 0)) (drop qz))
private def capturedCounterfeit : NativeTerm 0 :=
  input qz (parallel (drop qz) (drop qz))

private def termRequest (context : Mettapedia.OSLF.Binding.Ctx sig) (sort : Srt)
    (term : NativeTerm context.length) : TermRequest context.length where
  context := BindingSignatureEmbedding.context names context
  type := BindingSignatureEmbedding.sortType names sort
  term := term

private def binary (first second : Explicit.Certificate) : Fin 2 → Explicit.Certificate :=
  Fin.cases first (fun smaller => Fin.cases second (fun impossible => Fin.elim0 impossible) smaller)

private def forgedMiddle : Explicit.Certificate :=
  .node (.trans [] .pr (parallel z z) z dz)
    (binary (Tree.erase (Explicit.unit (context := []) z))
      (Tree.erase (Explicit.reflexivity (context := []) (sort := .pr) dz)))

private def compactMismatch : EquationEvidence [] .pr :=
  .trans (.refl (.op .nil .nil)) (.refl (.op .drp (.cons (.op .quo (.cons (.op .nil .nil) .nil)) .nil)))

private def sourceZero {context : Mettapedia.OSLF.Binding.Ctx sig} : Term sig context .pr :=
  .op .nil .nil
private def sourceQuoteZero {context : Mettapedia.OSLF.Binding.Ctx sig} : Term sig context .nm :=
  .op .quo (.cons sourceZero .nil)
private def sourceDropZero {context : Mettapedia.OSLF.Binding.Ctx sig} : Term sig context .pr :=
  .op .drp (.cons sourceQuoteZero .nil)
private def bodies : EqualityCertificates.Bodies sig [] metas := .cons sourceZero .nil
private def etaProof {context : Mettapedia.OSLF.Binding.Ctx sig} (name : Term sig context .nm) :
    EquationEvidence context .nm := .axiom ⟨3, by decide⟩ bodies .nil (.cons name .nil)
private def commProof : EquationEvidence [] .pr :=
  .axiom ⟨0, by decide⟩ bodies .nil (.cons sourceZero (.cons sourceDropZero .nil))
private def assocProof : EquationEvidence [] .pr :=
  .axiom ⟨1, by decide⟩ bodies .nil
    (.cons sourceZero (.cons sourceDropZero
      (.cons (.op .par (.cons sourceZero (.cons sourceZero .nil))) .nil)))
private def unitProof : EquationEvidence [] .pr :=
  .axiom ⟨2, by decide⟩ bodies .nil (.cons sourceDropZero .nil)

private def compactCapture : EquationEvidence [.nm] .pr :=
  .cong .inp (.cons (.refl (.var .zero))
    (.cons (.cong .par (.cons (.refl (.op .drp (.cons (.var .zero) .nil)))
      (.cons (.cong .drp (.cons (etaProof (.var (.succ .zero))) .nil)) .nil))) .nil))
private def compactCaptureClosed : EquationEvidence [] .pr :=
  .substitute (.cons sourceQuoteZero .nil) compactCapture

private def closedCompact : List (Σ sort : Srt, EquationEvidence [] sort) :=
  [ ⟨.pr, commProof⟩, ⟨.pr, assocProof⟩, ⟨.pr, unitProof⟩,
    ⟨.nm, etaProof sourceQuoteZero⟩,
    ⟨.pr, .cong .par (.cons assocProof (.cons unitProof .nil))⟩,
    ⟨.pr, .cong .out (.cons (etaProof sourceQuoteZero) (.cons unitProof .nil))⟩,
    ⟨.nm, .cong .quo (.cons commProof .nil)⟩,
    ⟨.pr, .cong .drp (.cons (etaProof sourceQuoteZero) .nil)⟩,
    ⟨.pr, .symm commProof⟩,
    ⟨.pr, .trans unitProof (.symm unitProof)⟩ ]

/-- Actual external packets exercise each explicit native structural rule. -/
def externalControls : List (String × Packet × Option Data) :=
  (proofs.mapIdx fun index sample =>
    let input := (termRequest sample.1.context sample.1.sort sample.1.first,
      termRequest sample.1.context sample.1.sort sample.1.second)
    (s!"native-rule-{index}",
      ⟨sample.1.context, .nativeEquation,
        ⟨sample.1.sort, input, Tree.encodeDerivation sample.2⟩⟩, some (.atom 0))) ++
  [ ("native-open-name", ⟨[.nm], .nativeEquation, ⟨.nm,
      (termRequest [.nm] .nm (.var 0), termRequest [.nm] .nm (.var 0)),
      Tree.encodeDerivation (Explicit.reflexivity (context := [.nm]) (sort := .nm) (.var 0))⟩⟩,
      some (.atom 0))
  , ("native-capture-aware", ⟨[], .nativeEquation, ⟨.pr,
      (termRequest [] .pr captureAfterSource, termRequest [] .pr captureAfterTarget),
      Tree.encodeDerivation (Explicit.substitute captureProof [] captureAction)⟩⟩, some (.atom 0))
  , ("native-capture-forgery", ⟨[], .nativeEquation, ⟨.pr,
      (termRequest [] .pr captureAfterSource, termRequest [] .pr capturedCounterfeit),
      Tree.encodeDerivation (Explicit.substitute captureProof [] captureAction)⟩⟩, none)
  , ("native-wrong-displayed-type", ⟨[], .nativeEquation, ⟨.pr,
      (termRequest [] .nm z, termRequest [] .pr z),
      Tree.encodeDerivation (Explicit.reflexivity (context := []) (sort := .pr) z)⟩⟩, none)
  , ("native-wrong-sort", ⟨[], .nativeEquation, ⟨.nm,
      (termRequest [] .pr z, termRequest [] .pr z),
      Tree.encodeDerivation (Explicit.reflexivity (context := []) (sort := .pr) z)⟩⟩, none)
  , ("native-wrong-metadata-context", ⟨[.pr], .nativeEquation, ⟨.pr,
      (termRequest [.nm] .pr z, termRequest [.nm] .pr z),
      Tree.encodeDerivation (Explicit.reflexivity (context := [.pr]) (sort := .pr) z)⟩⟩, none)
  , ("native-wrong-proof-context", ⟨[.pr], .nativeEquation, ⟨.pr,
      (termRequest [.pr] .pr z, termRequest [.pr] .pr z),
      Tree.encodeDerivation (Explicit.reflexivity (context := [.nm]) (sort := .pr) z)⟩⟩, none)
  , ("native-unknown-head", ⟨[], .nativeEquation, ⟨.pr,
      (termRequest [] .pr (.const `rho.unknown), termRequest [] .pr (.const `rho.unknown)),
      Tree.encodeDerivation (Explicit.reflexivity (context := []) (sort := .pr) (.const `rho.unknown))⟩⟩, none)
  , ("native-directed-drop-is-no-equation", ⟨[], .nativeEquation, ⟨.pr,
      (termRequest [] .pr dz, termRequest [] .pr z),
      Tree.encodeDerivation (Explicit.reflexivity (context := []) (sort := .pr) dz)⟩⟩, none)
  , ("native-forged-intermediate", ⟨[], .nativeEquation, ⟨.pr,
      (termRequest [] .pr (parallel z z), termRequest [] .pr dz),
      .node (.trans [] .pr (parallel z z) z dz)
        [Tree.encodeDerivation (Explicit.unit (context := []) z),
          Tree.encodeDerivation (Explicit.reflexivity (context := []) (sort := .pr) dz)]⟩⟩, none)
  , ("native-missing-child", ⟨[], .nativeEquation, ⟨.pr,
      (termRequest [] .pr z, termRequest [] .pr z), .node (.symm [] .pr z z) []⟩⟩, none)
  , ("native-extra-child", ⟨[], .nativeEquation, ⟨.pr,
      (termRequest [] .pr z, termRequest [] .pr z), .node (.refl [] .pr z)
        [Tree.encodeDerivation (Explicit.reflexivity (context := []) (sort := .pr) z)]⟩⟩, none)
  ]

def run : IO Nat := do
  let mut count := 0
  for sample in proofs do
    let proof := Tree.erase sample.2
    require "original rule" (Explicit.check sample.1 proof)
    let wrong := { sample.1 with sort := match sample.1.sort with | .nm => .pr | .pr => .nm }
    require "wrong literal sort" (!(Explicit.check wrong proof))
    let input := (termRequest sample.1.context sample.1.sort sample.1.first,
      termRequest sample.1.context sample.1.sort sample.1.second)
    require "registered native proof route"
      ((invokeRouted (nativeEquationRequest (sort := sample.1.sort) input proof)).acceptedValue.isSome)
    let wire := Tree.encodeDerivation sample.2
    require "literal rule codec"
      ((NativeEquations.rule.get (NativeEquations.rule.put (match proof with | .node code _ => code))).map NativeEquations.rule.put ==
        some (NativeEquations.rule.put (match proof with | .node code _ => code)))
    require "original proof history through wire"
      ((Tree.decodeDerivation wire).map (fun original => NativeEquations.proof.put
        (Tree.encodeDerivation original.2)) == some (NativeEquations.proof.put wire))
    count := count + 5
  require "forged middle" (!(Explicit.check ⟨[], .pr, parallel z z, dz⟩ forgedMiddle))
  let variableProof := Tree.erase (Explicit.reflexivity (context := [.nm]) (sort := .nm) (.var 0))
  require "wrong context with equal length" (!(Explicit.check ⟨[.pr], .nm, .var 0, .var 0⟩ variableProof))
  require "directed drop refused as equality"
    (!(Explicit.check ⟨[], .pr, dz, z⟩ (Tree.erase (Explicit.reflexivity (context := []) (sort := .pr) dz))))
  count := count + 3
  let substituted := Tree.erase (Explicit.substitute captureProof [] captureAction)
  require "lifted capture result" (Explicit.check ⟨[], .pr, captureAfterSource, captureAfterTarget⟩ substituted)
  require "bound variable not captured" (!(Explicit.check ⟨[], .pr, captureAfterSource, capturedCounterfeit⟩ substituted))
  require "substitution keeps proof occurrences" (decide (substituted.nodeCount = 6))
  let pair := (termRequest [] .pr captureAfterSource, termRequest [] .pr captureAfterTarget)
  require "native proof service capture" (ExplicitEquations.check [] .pr pair substituted)
  require "native proof invocation capture"
    (Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation.invoke
      (ExplicitEquations.request (sort := .pr) pair substituted)).acceptedValue.isSome
  count := count + 5
  let reflexivity := Tree.erase (Explicit.reflexivity (context := []) (sort := .pr) z)
  let good := termRequest [] .pr z
  require "native explicit service" (ExplicitEquations.check [] .pr (good, good) reflexivity)
  let wrongType := { good with type := BindingSignatureEmbedding.sortType names .nm }
  require "native proof wrong displayed type"
    (!(ExplicitEquations.check [] .pr (wrongType, good) reflexivity))
  let unknown : NativeTerm 0 := .const (Lean.Name.str .anonymous "unknown-rho-head")
  let unknownRequest := termRequest [] .pr unknown
  let unknownProof := Tree.erase (Explicit.reflexivity (context := []) (sort := .pr) unknown)
  require "independent structural refl on arbitrary syntax" (Explicit.check ⟨[], .pr, unknown, unknown⟩ unknownProof)
  require "native proof unknown head refuses"
    (!(ExplicitEquations.check [] .pr (unknownRequest, unknownRequest) unknownProof))
  require "compact mismatch refuses expansion" ((Explicit.expand? compactMismatch).isNone)
  count := count + 5
  match readback [] .pr captureAfterSource, readback [] .pr captureAfterTarget with
  | some first, some second =>
      require "compact substitution under native input"
        (EqualityCertificates.check compactCaptureClosed first second)
      match Explicit.expand? compactCaptureClosed with
      | none => throw (IO.userError "explicit rho: compact capture expansion failed")
      | some output =>
          require "compiled binder-lifted literal output"
            (Explicit.check ⟨[], .pr, captureAfterSource, captureAfterTarget⟩ output)
          require "compiled capture counterfeit refused"
            (!(Explicit.check ⟨[], .pr, captureAfterSource, capturedCounterfeit⟩ output))
          require "compiled capture admitted native proof"
            (ExplicitEquations.check [] .pr pair output)
  | _, _ => throw (IO.userError "explicit rho: capture source readback failed")
  count := count + 4
  for sample in closedCompact do
    match EqualityCertificates.replay sample.2 with
    | none => throw (IO.userError "explicit rho: original closed sample refused")
    | some result =>
        match Explicit.expand? sample.2 with
        | none => throw (IO.userError "explicit rho: closed template expansion failed")
        | some output =>
            let actual := Explicit.sourceClaim result.left result.right
            let wrong := { actual with sort := match sample.1 with | .nm => .pr | .pr => .nm }
            require "closed axiom/congruence expansion" (Explicit.check actual output)
            require "closed expansion wrong-sort refusal" (!(Explicit.check wrong output))
            require "closed expansion native proof service"
              (ExplicitEquations.check [] sample.1
                (sourceRequest result.left, sourceRequest result.right) output)
    count := count + 3
  for n in List.range 9 do
    let source := Explicit.ExpansionControls.doubled n
    let compact := Explicit.ExpansionControls.compact n
    require "compact original endpoints" (EqualityCertificates.check compact source source)
    match Explicit.expand? compact with
    | none => throw (IO.userError "explicit rho: compact expansion failed")
    | some output =>
        require "compiled literal endpoints" (Explicit.check (Explicit.sourceClaim source source) output)
        require "proof-node count excludes term payload" (decide (output.nodeCount = 1))
        require "exponential literal source payload" (decide (termSize source + 1 = 2^(n+1)))
        require "compiled native proof service"
          (ExplicitEquations.check [.pr] .pr (sourceRequest source, sourceRequest source) output)
    count := count + 5
  return count

end ExplicitRuntime

private def nilP {context : Mettapedia.OSLF.Binding.Ctx sig} : Term sig context Srt.pr := .op .nil .nil
private def par {context : Mettapedia.OSLF.Binding.Ctx sig}
    (first second : Term sig context Srt.pr) : Term sig context Srt.pr :=
  .op .par (.cons first (.cons second .nil))
private def quo {context : Mettapedia.OSLF.Binding.Ctx sig}
    (process : Term sig context Srt.pr) : Term sig context Srt.nm := .op .quo (.cons process .nil)
private def drp {context : Mettapedia.OSLF.Binding.Ctx sig}
    (name : Term sig context Srt.nm) : Term sig context Srt.pr := .op .drp (.cons name .nil)

private def closedUnitProof : EquationEvidence [] Srt.pr :=
  .axiom ⟨2, by decide⟩ (.cons nilP .nil) .nil (.cons nilP .nil)

private def openChannel : Term sig [Srt.nm, Srt.pr] Srt.nm := .var .zero
private def openPayload : Term sig [Srt.nm, Srt.pr] Srt.pr := .var (.succ .zero)
private def openBody : Term sig [Srt.nm, Srt.nm, Srt.pr] Srt.pr :=
  par (drp (.var .zero)) (drp (quo (drp (.var (.succ .zero)))))
private def openCommunication : OperationRequest [Srt.nm, Srt.pr] :=
  AuthoredAdapter.communicationRequest openChannel openPayload openBody
private def openResult : Operations.NativeTerm 2 :=
  Inversion.E (RhoSemanticRulePolynomial.commTarget
    (BindingCloneAlgebra.terms sig) openPayload openBody)

private def controls : List (String × Packet × Option Data) :=
  [ ("empty-admission", ⟨[], .admission, ⟨.pr, Controls.emptyRequest⟩⟩, some (.atom 0))
  , ("open-quoted-admission", ⟨[.nm], .admission, ⟨.pr, Controls.openRequest⟩⟩, some (.atom 0))
  , ("wrong-sort", ⟨[], .admission, ⟨.pr, Controls.wrongSortRequest⟩⟩, none)
  , ("wrong-context", ⟨[.nm], .admission, ⟨.pr, Controls.wrongContextRequest⟩⟩, none)
  , ("unknown-head", ⟨[], .admission, ⟨.pr, Controls.unknownHeadRequest⟩⟩, none)
  , ("unicode-unknown-head", ⟨[], .admission, ⟨.pr,
        { Controls.emptyRequest with term := .const (.str .anonymous "ρ-🌈") }⟩⟩, none)
  , ("sort-labeled-name", ⟨[], .admission, ⟨.nm, sourceRequest (quo nilP)⟩⟩, some (.atom 0))
  , ("sort-label-mismatch", ⟨[], .admission, ⟨.pr, sourceRequest (quo nilP)⟩⟩, none)
  , ("reflexivity", ⟨[], .equation, ⟨.pr,
        (Controls.emptyRequest, Controls.emptyRequest), .refl nilP⟩⟩, some (.atom 0))
  , ("unit-equation", ⟨[], .equation, ⟨.pr,
        (sourceRequest (par nilP nilP), Controls.emptyRequest), closedUnitProof⟩⟩, some (.atom 0))
  , ("forged-reflexivity", ⟨[], .equation, ⟨.pr,
        (sourceRequest (par nilP nilP), Controls.emptyRequest), .refl nilP⟩⟩, none)
  , ("wrong-equation-sort", ⟨[], .equation, ⟨.pr,
        (sourceRequest (quo nilP), sourceRequest (quo nilP)), .refl nilP⟩⟩, none)
  , ("directed-drop", ⟨[], .execution, Controls.dropRequest⟩,
        some ((nativeTerm 0).put (.const zeroName)))
  , ("drop-is-no-equation", ⟨[], .equation, ⟨.pr,
        (Controls.dropRequest.argument, Controls.emptyRequest), .refl nilP⟩⟩, none)
  , ("open-communication", ⟨[.nm, .pr], .execution, openCommunication⟩,
        some ((nativeTerm 2).put openResult))
  , ("actual-proposed-result", ⟨[.nm, .pr], .proposedResult, (openCommunication, openResult)⟩,
        some (.atom 0))
  , ("forged-result", ⟨[.nm, .pr], .proposedResult,
        (openCommunication, .const `rho.unknown)⟩, none)
  , ("wrong-address", ⟨[], .execution, { Controls.dropRequest with address := [false] }⟩, none)
  , ("quoted-redex", ⟨[], .execution,
        ⟨sourceRequest (quo (drp (quo nilP))), []⟩⟩, none)
  , ("unadmitted-execution", ⟨[], .execution, ⟨Controls.unknownHeadRequest, []⟩⟩, none)
  ] ++ ExplicitRuntime.externalControls

private def nativeExample : Packet :=
  ⟨[], .nativeEquation, ⟨.pr, (Controls.emptyRequest, Controls.emptyRequest),
    Mettapedia.OSLF.NativeTypes.Certificates.Tree.encodeDerivation
      (ScopedRepresentation.Conversion.Explicit.reflexivity (context := []) (sort := .pr)
        (.const zeroName))⟩⟩

private def withRole (value : Packet) (role : Nat) : List Alphabet :=
  match packet.put value with
  | .pair header (.pair context (.pair _ fields)) =>
      encodeData (.pair header (.pair context (.pair (.atom role) fields)))
  | _ => encodeRequest value

private def withForeignHeader (value : Packet) : List Alphabet :=
  match packet.put value with
  | .pair _ fields => encodeData (.pair (.atom 999) fields)
  | _ => encodeRequest value

private def withRawNativeProof (proof : Data) : List Alphabet :=
  match packet.put nativeExample with
  | .pair header (.pair context (.pair role (.pair sort (.pair input _)))) =>
      encodeData (.pair header (.pair context (.pair role (.pair sort (.pair input proof)))))
  | _ => encodeRequest nativeExample

private def badBodyScope : Data :=
  let name : Operations.NativeTerm 0 := Operations.quote (.const zeroName)
  let body : Operations.NativeTerm 1 := Operations.drop (.var 0)
  let original := NativeEquations.rule.put (.inputCong [] name name body body)
  match original with
  | .pair context (.pair kind (.pair name (.pair name' (.pair _ remaining)))) =>
      let outside : Operations.NativeTerm 2 := .var ⟨1, by decide⟩
      .pair context (.pair kind (.pair name (.pair name' (.pair ((nativeTerm 2).put outside) remaining))))
  | _ => original

private def extraRuleField : Data :=
  let original := NativeEquations.rule.put (.refl [] .pr (.const zeroName))
  match original with
  | .pair context (.pair kind (.pair sort (.pair term _))) =>
      .pair context (.pair kind (.pair sort (.pair term (.pair (.atom 0) (.atom 0)))))
  | _ => original

private def malformedWords : List (String × List Alphabet) :=
  let word := encodeRequest ⟨[], .admission, ⟨.pr, Controls.emptyRequest⟩⟩
  [ ("empty-word", [])
  , ("truncated-word", word.take (word.length - 1))
  , ("trailing-word", word ++ [0])
  , ("foreign-environment", encodeData (.pair (.atom 999) (.atom 0)))
  , ("wrong-service-fields", encodeData (.pair declarationHeader (.atom 0)))
  , ("extra-packet-field", encodeData (.pair (.pair declarationHeader (.atom 0)) (.atom 0)))
  , ("native-as-compact", withRole nativeExample 1)
  , ("native-as-execution", withRole nativeExample 2)
  , ("native-as-proposed-result", withRole nativeExample 3)
  , ("native-unknown-role", withRole nativeExample 99)
  , ("native-foreign-header", withForeignHeader nativeExample)
  , ("compact-as-native", withRole
      ⟨[], .equation, ⟨.pr, (Controls.emptyRequest, Controls.emptyRequest), .refl nilP⟩⟩ 4)
  , ("native-body-outside-scope", withRawNativeProof (.pair badBodyScope (.atom 0)))
  , ("native-extra-rule-field", withRawNativeProof (.pair extraRuleField (.atom 0)))
  ]

private def require (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError ("failed: " ++ name))

namespace SharedRuntime
open ScopedRepresentation.Operations ScopedRepresentation.Conversion
open Mettapedia.OSLF.NativeTypes.Certificates

private def fromDerivation
    (sample : Σ claim : Explicit.Claim, Explicit.Derivation claim) :
    ScopedSharedEvidence.Storage.Packet :=
  ⟨sample.1.context, sample.1.sort,
    (ExplicitRuntime.termRequest sample.1.context sample.1.sort sample.1.first,
      ExplicitRuntime.termRequest sample.1.context sample.1.sort sample.1.second),
    Shared.emit sample.2⟩

private def z {n : Nat} : NativeTerm n := .const zeroName
private def qz {n : Nat} : NativeTerm n := quote z
private def nilRow : ScopedSharedEvidence.Row :=
  ⟨.refl [] .pr z, fun impossible => Fin.elim0 impossible⟩
private def symmetryRow (reference : Nat) : ScopedSharedEvidence.Row :=
  ⟨.symm [] .pr z z, fun _ => reference⟩
private def identity : ScopedSharedEvidence.Storage.Packet :=
  fromDerivation ⟨_, Explicit.reflexivity (context := []) (sort := .pr) z⟩
private def withProof (proof : ScopedSharedEvidence.Proof) :
    ScopedSharedEvidence.Storage.Packet :=
  ⟨[], .pr, identity.2.2.1, proof⟩

private def graphCases : List (String × ScopedSharedEvidence.Storage.Packet × Bool) :=
  (ExplicitRuntime.proofs.mapIdx fun index sample =>
    (s!"graph-rule-{index}", fromDerivation sample, true)) ++
  [("graph-under-binder", fromDerivation ⟨_, ExplicitRuntime.captureProof⟩, true),
   ("graph-open-name", fromDerivation ⟨_,
      Explicit.reflexivity (context := [.nm]) (sort := .nm) (.var 0)⟩, true),
   ("graph-unused-valid-row", withProof ⟨[nilRow, symmetryRow 0], 0⟩, true),
   ("graph-shared-child", withProof ⟨[nilRow,
      ⟨.trans [] .pr z z z, Fin.cases 0 (fun _ => 0)⟩], 1⟩, true),
   ("graph-unused-invalid-row", withProof ⟨[nilRow, symmetryRow 99], 0⟩, false),
   ("graph-forward-reference", withProof ⟨[symmetryRow 1, nilRow], 1⟩, false),
   ("graph-cyclic-reference", withProof ⟨[symmetryRow 0], 0⟩, false),
   ("graph-empty-table", withProof ⟨[], 0⟩, false),
   ("graph-root-outside-table", withProof ⟨[nilRow], 1⟩, false),
   ("graph-wrong-sort", ⟨[], .nm, identity.2.2.1, identity.2.2.2⟩, false),
   ("graph-wrong-endpoint", ⟨[], .pr,
      (identity.2.2.1.1, ExplicitRuntime.termRequest [] .pr (output qz z)), identity.2.2.2⟩, false),
   ("graph-wrong-native-type", ⟨[], .pr,
      ({identity.2.2.1.1 with type := BindingSignatureEmbedding.sortType names .nm}, identity.2.2.1.2), identity.2.2.2⟩, false)]

private def malformed : List (String × List Alphabet) :=
  let encoded := ScopedSharedEvidence.Storage.encodeRequest identity
  [("graph-empty-input", []), ("graph-truncated", encoded.dropLast),
   ("graph-trailing", encoded ++ [0]),
   ("graph-old-header", match ScopedSharedEvidence.Storage.packet.put identity with
      | .pair _ body => encodeData (.pair declarationHeader body)
      | other => encodeData other),
   ("graph-stale-header", match ScopedSharedEvidence.Storage.packet.put identity with
      | .pair _ body => encodeData (.pair (.atom 999) body)
      | other => encodeData other)]

def runControls : IO UInt32 := do
  let mut count : Nat := 0
  for (name, request, expected) in graphCases do
    let word := ScopedSharedEvidence.Storage.encodeRequest request
    let result := ScopedSharedEvidence.Storage.runRouted word
    require (name ++ " admission") (result.isSome == expected)
    require (name ++ " reply")
      (result == if expected then some (ScopedSharedEvidence.Storage.reply request) else none)
    require (name ++ " distinct role") ((ScopedServiceWire.decodeRequest word).isNone)
    require (name ++ " exact text") (Text.parse (Text.render word) == some word)
    count := count + 4
  for (name, word) in malformed do
    require name ((ScopedSharedEvidence.Storage.runRouted word).isNone)
    count := count + 1
  for (name, request, _) in controls do
    let word := ScopedServiceWire.encodeRequest request
    require (name ++ " original reply")
      (ScopedSharedEvidence.Storage.runRouted word == ScopedServiceWire.run word)
    require (name ++ " original role")
      ((ScopedSharedEvidence.Storage.decodeRequest word).isNone)
    count := count + 2
  IO.println s!"shared declared-calculus rho comparison: {count} controls PASS"
  return 0

def exportControls (directory : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll directory
  let mut rows := ["file\texpected"]
  for (name, request, expected) in graphCases do
    let file := name ++ ".rho-service"
    IO.FS.writeFile (directory / file) (Text.render (ScopedSharedEvidence.Storage.encodeRequest request))
    rows := rows ++ [file ++ "\t" ++ if expected then "accepted" else "refused"]
  for (name, word) in malformed do
    let file := name ++ ".rho-service"
    IO.FS.writeFile (directory / file) (Text.render word)
    rows := rows ++ [file ++ "\trefused"]
  IO.FS.writeFile (directory / "controls.tsv") (String.intercalate "\n" rows ++ "\n")
  IO.println s!"exported {graphCases.length + malformed.length} graph requests"
  return 0
end SharedRuntime

private def runControls : IO UInt32 := do
  let mut count := 0
  for (name, request, expected) in controls do
    let word := encodeRequest request
    require (name ++ " text") (Text.parse (Text.render word) == some word)
    require (name ++ " complete packet")
      ((decodeRequest word).map packet.put == some (packet.put request))
    require (name ++ " result")
      (ScopedServiceWire.run word == expected.map (fun output => encodeData (.pair (packet.put request) output)))
    require (name ++ " trailing") ((ScopedServiceWire.run (word ++ [0])).isNone)
    count := count + 4
  for (name, word) in malformedWords do
    require name ((ScopedServiceWire.run word).isNone)
    count := count + 1
  let wideVariable : Operations.NativeTerm 257 := .var ⟨256, by decide⟩
  require "wide scoped index" ((nativeTerm 257).get ((nativeTerm 257).put wideVariable) == some wideVariable)
  require "scope is checked" (((nativeTerm 256).get ((nativeTerm 257).put wideVariable)).isNone)
  let unicodeConstant : Operations.NativeTerm 0 := .const (.num (.str .anonymous "ρ-🌈") (2 ^ 64))
  require "unicode and large name" ((nativeTerm 0).get ((nativeTerm 0).put unicodeConstant) == some unicodeConstant)
  require "compact unicode storage" ((encodeWith (nativeTerm 0) unicodeConstant).length < 20000)
  let legacy := Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec.put
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec.encodeTm
      Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec.towerHeadCodec wideVariable)
  require "mixed scalar format is refused" (((nativeTerm 257).get legacy).isNone)
  require "unsafe authored adapter refuses" ((AuthoredAdapter.execute? AuthoredAdapter.unsafeArguments).isNone)
  require "same intrinsic operation executes"
    ((invokeOperation? (AuthoredAdapter.request AuthoredAdapter.unsafeArguments)).isSome)
  require "invalid alphabet" ((Text.parse "?").isNone)
  require "whitespace is refused" ((Text.parse " ").isNone)
  count := count + 9
  require "seven required service roles" (decide (requiredServices.length = 7))
  require "name native-proof role required" (requiredServices.contains (.nativeEquation .nm))
  require "process native-proof role required" (requiredServices.contains (.nativeEquation .pr))
  require "native name interface retained"
    (decide ((requiredInterface [] (.nativeEquation .nm)).face = .nativeProof))
  require "native process interface retained"
    (decide ((requiredInterface [] (.nativeEquation .pr)).face = .nativeProof))
  require "compact equation interface retained"
    (decide ((requiredInterface [] (.equation .pr)).face = .certificateBoundary))
  require "native input body scope checked" ((NativeEquations.rule.get badBodyScope).isNone)
  require "native rule extra field checked" ((NativeEquations.rule.get extraRuleField).isNone)
  count := count + 8
  let explicit ← ExplicitRuntime.run
  count := count + explicit
  IO.println s!"declared-calculus rho comparison: {count} controls PASS"
  return 0

private def exportControls (directory : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll directory
  let mut rows := ["file\texpected"]
  for (name, request, expected) in controls do
    let file := name ++ ".rho-service"
    IO.FS.writeFile (directory / file) (Text.render (encodeRequest request))
    rows := rows ++ [file ++ "\t" ++ if expected.isSome then "accepted" else "refused"]
  for (name, word) in malformedWords do
    let file := name ++ ".rho-service"
    IO.FS.writeFile (directory / file) (Text.render word)
    rows := rows ++ [file ++ "\trefused"]
  IO.FS.writeFile (directory / "controls.tsv") (String.intercalate "\n" rows ++ "\n")
  IO.println s!"exported {controls.length + malformedWords.length} requests"
  return 0

private def checkFile (file : System.FilePath) (replyFile : Option System.FilePath) : IO UInt32 := do
  match Text.parse (← IO.FS.readFile file) with
  | none => IO.eprintln "invalid request alphabet"; return 2
  | some word =>
      match ScopedSharedEvidence.Storage.runRouted word with
      | none => IO.println "refused"; return 1
      | some reply =>
          if let some destination := replyFile then IO.FS.writeFile destination (Text.render reply)
          IO.println "accepted"
          return 0

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["controls"] => runControls
  | ["graph-controls"] => SharedRuntime.runControls
  | ["export-graph-controls", directory] => SharedRuntime.exportControls directory
  | ["export-controls", directory] => exportControls directory
  | ["check", file] => checkFile file none
  | ["run", file, reply] => checkFile file (some reply)
  | _ =>
      IO.println "rhoCandidateServices controls | graph-controls | export-controls <directory> | export-graph-controls <directory> | check <request> | run <request> <reply>"
      return 2

end Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.CheckCandidateServices

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.MeTTa.PrimeComparisons.Rho.CheckCandidateServices.run arguments
