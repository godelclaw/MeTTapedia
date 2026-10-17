import Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeKernel

/-!
# Executable client for native rho evidence

The file format is the finite alphabet `0`, `1`, `e`, `a`, `p`, without
whitespace. A request retains its goal and every rule payload and child.
Acceptance establishes the existing raw rho judgment; sorted source admission
is a separate boundary. This client does not claim a verified C compiler or
an executed asymptotic checking bound.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CheckNativeEvidence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open NativeEvidence

open Mettapedia.OSLF.Binding.WireCodec.Binary.Text

private def zero : Pattern := .apply "PZero" []
private def atom : Pattern := .fvar "different"
private def channel : Pattern := .apply "NQuote" [zero]
private def body : Pattern := .apply "PDrop" [.bvar 0]
private def leaf : Wire := .node (.structuralRefl zero) []

private def controls : List (String × Judgment × Wire × Bool) :=
  [ ("reflexivity", .structural zero zero, leaf, true)
  , ("communication", .step
      (.collection .hashBag [.apply "POutput" [channel, zero],
        .apply "PInput" [channel, .lambda none body]] none)
      (.collection .hashBag [zero] none), .node (.comm channel zero body []) [], true)
  , ("wrong-goal", .structural zero atom, leaf, false)
  , ("extra-child", .structural zero zero,
      .node (.structuralRefl zero) [leaf], false)
  , ("missing-child", .structural zero zero,
      .node (.structuralTrans zero zero zero) [leaf], false)
  , ("repeated-premises", .structural zero zero,
      .node (.structuralTrans zero zero zero) [leaf, leaf], true)
  ]

private def ruleControls : List Rule :=
  [ .structuralRefl atom, .structuralSymm atom zero, .structuralTrans atom zero channel
  , .parSingleton atom, .parNilLeft atom, .parNilRight atom, .parComm atom zero
  , .parAssoc atom zero channel, .parFlatten [atom, zero] [zero, atom]
  , .parPerm [atom, zero] [zero, atom], .setPerm [atom, zero] [zero, atom]
  , .applyCong "λ-label" [(atom, zero), (zero, atom)]
  , .collectionCong .hashBag (some "tail") [(atom, zero)]
  , .lambdaCong (some "x") atom zero
  , .multiLambdaCong 2 ["x", "y"] (.bvar 0) (.bvar 1)
  , .substCong atom zero channel body, .quoteDrop channel, .parEmpty
  , .nameRefl channel, .nameQuoteDrop channel, .nameStructural atom zero
  , .nameSymm atom zero, .nameTrans atom zero channel
  , .comm channel zero body [atom, zero]
  , .stepEquiv atom zero channel body, .stepPar atom zero [channel]
  , .stepParAny atom zero [channel] [body], .stepsRefl atom
  , .stepsCons atom zero channel, .permNil, .permCons atom [zero] [channel]
  , .permSwap atom zero [channel], .permTrans [atom] [zero] [channel]
  ]

private def require (name : String) (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError ("failed: " ++ name))

private def runControls : IO UInt32 := do
  let mut assertions := 0
  for code in ruleControls do
    let raw := Storage.putRule code
    let decoded := Storage.getRule raw
    require "complete rule fields" (decoded.map Storage.putRule == some raw)
    assertions := assertions + 1
  for (name, claim, wire, expected) in controls do
    let word := Storage.encodeRequest claim wire
    require (name ++ " text") (parse (render word) == some word)
    require (name ++ " authority") ((Storage.checkRequest word == some claim) == expected)
    require (name ++ " truncated") (Storage.checkRequest (word.take (word.length - 1)) == none)
    require (name ++ " trailing") (Storage.checkRequest (word ++ [0]) == none)
    assertions := assertions + 4
  require "unknown rule tag" ((Storage.getRule (.pair (.atom 99) (.atom 0))).isNone)
  require "extra rule field" ((Storage.getRule
    (.pair (.atom 17) (.pair (.atom 0) (.atom 0)))).isNone)
  require "unknown alphabet symbol" ((parse "?").isNone)
  require "whitespace is not a symbol" ((parse " ").isNone)
  assertions := assertions + 4
  IO.println s!"native rho evidence: {assertions} controls PASS"
  return 0

private def closedContext : NativeKernel.Context := ⟨[], []⟩
private def commSource (name : Pattern) : Pattern := .collection .hashBag
  [.apply "POutput" [name, zero], .apply "PInput" [name, .lambda none body]] none
private def commTarget : Pattern := .collection .hashBag [zero] none
private def formationControls : List (String × NativeKernel.Claim × Wire × Bool) :=
  let proc (context : NativeKernel.Context) (p : Pattern) : NativeKernel.Claim :=
    ⟨context, .proc, .structural p p⟩
  let name (context : NativeKernel.Context) (p : Pattern) : NativeKernel.Claim :=
    ⟨context, .name, .structural p p⟩
  let reflexivity (p : Pattern) : Wire := .node (.structuralRefl p) []
  let communicate (name : Pattern) : Wire := .node (.comm name zero body []) []
  let opened : NativeKernel.Context := ⟨[("c", .name)], []⟩
  let ambient : NativeKernel.Context := ⟨[], [.name]⟩
  [ ("formed-reflexivity", proc closedContext zero, reflexivity zero, true)
  , ("formed-name", name closedContext channel, reflexivity channel, true)
  , ("formed-comm", ⟨closedContext, .proc, .step (commSource channel) commTarget⟩,
      communicate channel, true)
  , ("formed-open-comm", ⟨opened, .proc, .step (commSource (.fvar "c")) commTarget⟩,
      communicate (.fvar "c"), true)
  , ("formed-free-process", proc ⟨[("p", .proc)], []⟩ (.fvar "p"),
      reflexivity (.fvar "p"), true)
  , ("formed-wrong-free-sort", ⟨⟨[("c", .proc)], []⟩, .proc,
      .step (commSource (.fvar "c")) commTarget⟩, communicate (.fvar "c"), false)
  , ("formed-undeclared-free", proc closedContext (.fvar "p"), reflexivity (.fvar "p"), false)
  , ("formed-dangling", proc closedContext body, reflexivity body, false)
  , ("formed-ambient-name", proc ambient body, reflexivity body, true)
  , ("formed-ambient-wrong-sort", proc ⟨[], [.proc]⟩ body, reflexivity body, false)
  , ("formed-quote-capture", name ambient (.apply "NQuote" [body]),
      reflexivity (.apply "NQuote" [body]), false)
  , ("formed-unknown-head", proc closedContext (.apply "unknown" []),
      reflexivity (.apply "unknown" []), false)
  , ("formed-set-is-not-parallel", proc closedContext (.collection .hashSet [zero] none),
      reflexivity (.collection .hashSet [zero] none), false)
  , ("formed-name-as-process", proc closedContext channel, reflexivity channel, false)
  , ("formed-step-as-name", ⟨closedContext, .name, .step (commSource channel) commTarget⟩,
      communicate channel, false)
  , ("formed-wrong-goal", ⟨closedContext, .proc, .structural zero (.collection .hashBag [] none)⟩,
      reflexivity zero, false)
  , ("formed-free-drop-stays-inert", ⟨closedContext, .proc,
      .step (.apply "PDrop" [channel]) zero⟩, communicate channel, false)
  , ("formed-quote-drop-equation", ⟨closedContext, .name,
      .structural (.apply "NQuote" [.apply "PDrop" [channel]]) channel⟩,
      .node (.quoteDrop channel) [], true)
  ]

private def runFormationControls : IO UInt32 := do
  let mut assertions := 0
  for (name, claim, wire, expected) in formationControls do
    let word := NativeKernel.Storage.encodeRawRequest claim wire
    require (name ++ " text") (parse (render word) == some word)
    require (name ++ " authority")
      ((NativeKernel.Storage.checkRawRequest word == some claim) == expected)
    require (name ++ " truncated")
      ((NativeKernel.Storage.checkRawRequest (word.take (word.length - 1))).isNone)
    require (name ++ " trailing")
      ((NativeKernel.Storage.checkRawRequest (word ++ [0])).isNone)
    require (name ++ " mixed raw protocol") ((NativeEvidence.Storage.checkRequest word).isNone)
    assertions := assertions + 5
  let old := NativeEvidence.Storage.encodeRequest (.structural zero zero) leaf
  require "old packet not a formed packet" ((NativeKernel.Storage.checkRawRequest old).isNone)
  require "alpha display names"
    (NativeFormation.checkAlpha (.lambda (some "x") (.bvar 0)) (.lambda (some "y") (.bvar 0)))
  require "alpha preserves indices"
    (!NativeFormation.checkAlpha (.lambda none (.bvar 0)) (.lambda none (.bvar 1)))
  require "ordinary sorting does not seal quotes"
    (NativeFormation.checkName (fun _ => none) ["Name"] (.apply "NQuote" [body]))
  require "admission seals quotes"
    (!NativeFormation.checkAdmittedName (fun _ => none) ["Name"] (.apply "NQuote" [body]))
  assertions := assertions + 5
  IO.println s!"native rho formed evidence: {assertions} controls PASS"
  return 0

private def checkFormedFile (file : System.FilePath) : IO UInt32 := do
  let text ← IO.FS.readFile file
  match parse text with
  | none => IO.eprintln "invalid request alphabet"; return 2
  | some word =>
      match NativeKernel.Storage.checkRawRequest word with
      | none => IO.println "refused"; return 1
      | some claim => IO.println s!"accepted: {repr claim}"; return 0

private def exportFormationControls (directory : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll directory
  let mut rows := ["file\texpected"]
  for (name, claim, wire, expected) in formationControls do
    let file := name ++ ".rho-formed-proof"
    IO.FS.writeFile (directory / file) (render (NativeKernel.Storage.encodeRawRequest claim wire))
    rows := rows ++ [file ++ "\t" ++ if expected then "accepted" else "refused"]
  IO.FS.writeFile (directory / "controls.tsv") (String.intercalate "\n" rows ++ "\n")
  IO.println s!"exported {formationControls.length} formed requests"
  return 0

mutual
  private def explicitArticle : Wire → NativeKernel.Explicit.Evidence
    | .node rule children => .node (NativeKernel.Explicit.annotateRule rule) (explicitArticles children)
  private def explicitArticles : List Wire → List NativeKernel.Explicit.Evidence
    | [] => []
    | child :: children => explicitArticle child :: explicitArticles children
end

private def rewriteComputationRoot (evidence : NativeKernel.Explicit.Evidence)
    (change : SemanticSubstitutionEvidence.Certificate → SemanticSubstitutionEvidence.Certificate) :
    NativeKernel.Explicit.Evidence :=
  match evidence with
  | .node (rule, some receipt) children =>
      .node (rule, some ⟨receipt.result, change receipt.computation⟩) children
  | other => other

private def explicitControls :
    List (String × NativeKernel.RequestGoal × NativeKernel.Explicit.Evidence × Bool) :=
  let regular := controls.map fun (name, goal, article, expected) =>
    ("explicit-raw-" ++ name, NativeKernel.RequestGoal.raw goal, explicitArticle article, expected)
  let formed := formationControls.map fun (name, goal, article, expected) =>
    ("explicit-" ++ name, NativeKernel.RequestGoal.formed goal, explicitArticle article, expected)
  let comm := explicitArticle (.node (.comm channel zero body []) [])
  let goal : NativeKernel.RequestGoal := .raw (.step (commSource channel) commTarget)
  let receipt : NativeKernel.Explicit.CommReceipt :=
    ⟨zero, SemanticSubstitutionEvidence.certificate body zero⟩
  let customComm (name : String) (body payload expected : Pattern) :=
    (name, NativeKernel.RequestGoal.raw (.step
      (.collection .hashBag [.apply "POutput" [channel, payload],
        .apply "PInput" [channel, .lambda none body]] none)
      (.collection .hashBag [expected] none)),
      explicitArticle (.node (.comm channel payload body []) []), true)
  regular ++ formed ++
  [ ("explicit-missing-comm-history", goal, .node (.comm channel zero body [], none) [], false)
  , ("explicit-extra-noncomm-history", .raw (.structural zero zero),
      .node (.structuralRefl zero, some receipt) [], false)
  , ("explicit-forged-contractum", goal,
      .node (.comm channel zero body [], some ⟨atom, receipt.computation⟩) [], false)
  , ("explicit-bare-result-is-not-computation", goal,
      rewriteComputationRoot comm (fun _ => .node (.pattern zero) []), false)
  , ("explicit-swapped-computation-calls", goal,
      rewriteComputationRoot comm (fun | .node result children => .node result children.reverse), false)
  , ("explicit-extra-computation-call", goal,
      rewriteComputationRoot comm (fun | .node result children => .node result (children ++ [.node (.pattern zero) []])), false)
  , ("explicit-missing-computation-call", goal,
      rewriteComputationRoot comm (fun | .node result children => .node result (children.take 1)), false)
  , customComm "explicit-literal-drop-stays-inert" (.apply "PDrop" [channel]) zero (.apply "PDrop" [channel])
  , customComm "explicit-quoted-code-is-opaque" (.apply "NQuote" [body]) zero (.apply "NQuote" [body])
  , customComm "explicit-normalized-name-matches" (.apply "PDrop" [.apply "NQuote" [body]]) zero zero
  , customComm "explicit-unknown-application-is-opaque" (.apply "opaque" [.bvar 0]) zero (.apply "opaque" [.bvar 0])
  , customComm "explicit-named-input-is-original-fallback"
      (.apply "PInput" [channel, .lambda (some "x") (.apply "PDrop" [.bvar 1])]) zero
      (.apply "PInput" [channel, .lambda (some "x") (.apply "PDrop" [.bvar 1])])
  , customComm "explicit-multiple-binders-retain-metadata"
      (.multiLambda 2 ["x", "y"] (.apply "PDrop" [.bvar 2])) zero (.multiLambda 2 ["x", "y"] zero)
  , customComm "explicit-substitution-node-shifts-only-body"
      (.subst (.apply "PDrop" [.bvar 1]) body) zero (.subst zero zero)
  , customComm "explicit-collection-retains-kind-and-rest"
      (.collection .vec [body] (some "rest")) zero (.collection .vec [zero] (some "rest"))
  , customComm "explicit-input-increments-depth"
      (.apply "PInput" [channel, .lambda none (.apply "PDrop" [.bvar 1])]) zero
      (.apply "PInput" [channel, .lambda none zero])
  , customComm "explicit-payload-name-normalization" body
      (.apply "POutput" [.apply "NQuote" [.apply "PDrop" [channel]], zero])
      (.apply "POutput" [channel, zero])
  ]

private def runExplicitControls : IO UInt32 := do
  let mut assertions := 0
  for (name, goal, article, expected) in explicitControls do
    let word := NativeKernel.Storage.encodeExplicitRequest goal article
    require (name ++ " text") (parse (render word) == some word)
    require (name ++ " authority")
      ((NativeKernel.Storage.checkExplicitRequest word == some goal) == expected)
    require (name ++ " truncated")
      ((NativeKernel.Storage.checkExplicitRequest (word.take (word.length - 1))).isNone)
    require (name ++ " trailing")
      ((NativeKernel.Storage.checkExplicitRequest (word ++ [0])).isNone)
    require (name ++ " mixed formed protocol") ((NativeKernel.Storage.checkRawRequest word).isNone)
    require (name ++ " mixed legacy protocol") ((NativeEvidence.Storage.checkRequest word).isNone)
    assertions := assertions + 6
  require "unknown computation result tag"
    ((NativeKernel.Storage.computationResult.get (.pair (.atom 3) (.atom 0))).isNone)
  require "invalid computation match bit"
    ((NativeKernel.Storage.computationResult.get (.pair (.atom 2) (.pair
      (Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec.put zero) (.atom 2)))).isNone)
  let old := NativeEvidence.Storage.encodeRequest (.structural zero zero) leaf
  let formed := NativeKernel.Storage.encodeRawRequest ⟨closedContext, .proc, .structural zero zero⟩ leaf
  require "legacy packet not an explicit packet" ((NativeKernel.Storage.checkExplicitRequest old).isNone)
  require "formed packet not an explicit packet" ((NativeKernel.Storage.checkExplicitRequest formed).isNone)
  assertions := assertions + 4
  IO.println s!"native rho explicit evidence: {assertions} controls PASS"
  return 0

private def checkExplicitFile (file : System.FilePath) : IO UInt32 := do
  let text ← IO.FS.readFile file
  match parse text with
  | none => IO.eprintln "invalid request alphabet"; return 2
  | some word =>
      match NativeKernel.Storage.checkExplicitRequest word with
      | none => IO.println "refused"; return 1
      | some goal => IO.println s!"accepted: {repr goal}"; return 0

private def exportExplicitControls (directory : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll directory
  let mut rows := ["file\texpected"]
  for (name, goal, article, expected) in explicitControls do
    let file := name ++ ".rho-explicit-proof"
    IO.FS.writeFile (directory / file) (render (NativeKernel.Storage.encodeExplicitRequest goal article))
    rows := rows ++ [file ++ "\t" ++ if expected then "accepted" else "refused"]
  IO.FS.writeFile (directory / "controls.tsv") (String.intercalate "\n" rows ++ "\n")
  IO.println s!"exported {explicitControls.length} explicit requests"
  return 0

private def exportControls (directory : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll directory
  let mut rows := ["file\texpected"]
  for (name, claim, wire, expected) in controls do
    let file := name ++ ".rho-proof"
    IO.FS.writeFile (directory / file) (render (Storage.encodeRequest claim wire))
    rows := rows ++ [file ++ "\t" ++ if expected then "accepted" else "refused"]
  IO.FS.writeFile (directory / "controls.tsv") (String.intercalate "\n" rows ++ "\n")
  IO.println s!"exported {controls.length} requests"
  return 0

private def checkFile (file : System.FilePath) : IO UInt32 := do
  let text ← IO.FS.readFile file
  match parse text with
  | none => IO.eprintln "invalid request alphabet"; return 2
  | some word =>
      match Storage.checkRequest word with
      | none => IO.println "refused"; return 1
      | some claim => IO.println s!"accepted: {repr claim}"; return 0

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["controls"] => runControls
  | ["formed-controls"] => runFormationControls
  | ["explicit-controls"] => runExplicitControls
  | ["check-explicit", file] => checkExplicitFile file
  | ["export-explicit-controls", directory] => exportExplicitControls directory
  | ["check-formed", file] => checkFormedFile file
  | ["export-formed-controls", directory] => exportFormationControls directory
  | ["export-controls", directory] => exportControls directory
  | ["check", file] => checkFile file
  | _ =>
      IO.println "rhoNativeCheck controls | formed-controls | explicit-controls | export-controls <directory> | export-formed-controls <directory> | export-explicit-controls <directory> | check <request-file> | check-formed <request-file> | check-explicit <request-file>"
      return 2

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CheckNativeEvidence

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.ProcessCalculi.RhoCalculus.CheckNativeEvidence.run arguments
