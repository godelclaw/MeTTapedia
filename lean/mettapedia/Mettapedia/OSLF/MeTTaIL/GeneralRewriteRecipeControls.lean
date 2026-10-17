import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeWire
import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeExpansion
import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeComposition

/-!
# Authored rewrite-recipe acceptance and refusal controls

The fixtures retain their authored declarations, selected choices and literal
expected results. Control construction does not enumerate rewrite successors.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeControls
open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralExecutionAdmission GeneralOccurrenceSemantics GeneralTypedSites
open GeneralRewriteRecipeWire
open Mettapedia.OSLF.Binding.WireCodec

def type : TypeExpr := .base "Term"
def a : Pattern := .apply "A" []
def b : Pattern := .apply "B" []
def c : Pattern := .apply "C" []
def d : Pattern := .apply "D" []
def language : LanguageDef :=
  { name := "StepTrace-wire-λ"
    types := ["Term"]
    terms := [
      { label := "A", category := "Term", params := [], syntaxPattern := [] },
      { label := "B", category := "Term", params := [], syntaxPattern := [] },
      { label := "C", category := "Term", params := [], syntaxPattern := [] },
      { label := "D", category := "Term", params := [], syntaxPattern := [] }]
    equations := [
      { name := "a-b", typeContext := [], premises := [], left := a, right := b },
      { name := "c-d", typeContext := [], premises := [], left := c, right := d }]
    rewrites := [
      { name := "b-c", typeContext := [], premises := [], left := b, right := c },
      { name := "a-c", typeContext := [], premises := [], left := a, right := c }] }
def snapshot : Snapshot := ⟨language, [], ⟨[], [], []⟩⟩
def permissions : Permissions := { equationDirections := [.forward], includeDerivedEquations := false }
def plan : Plan := compile snapshot permissions

def equation (position : Nat) (source target : Pattern) : Option GeneralEquationJobs.Receipt := do
  let declaration ← plan.equations[position]?
  pure { job := ⟨position, declaration, .here [] type source⟩, matcherTrace := [], captured := [], completed := [], premiseHistory := [], rawReduct := target, target }

def firing (position : Nat) (source target : Pattern) : Option GeneralRuleJobs.Receipt := do
  let declaration ← plan.rules[position]?
  pure { job := ⟨position, declaration, .here [] type source⟩, matcherTrace := [], captured := [], completed := [], premiseHistory := [], localTarget := target, target }

def fixture : Option Request := do
  let pre ← equation 0 a b
  let post ← equation 1 c d
  let fire ← firing 0 b c
  pure ⟨snapshot, permissions, [], type, a, d, ⟨⟨b, [.forward pre], fire⟩, [.forward post]⟩⟩

def reverseFixture : Option Request := do
  let pre ← equation 0 a b
  let post ← equation 1 c d
  let fire ← firing 1 a c
  pure ⟨snapshot, permissions, [], type, b, d, ⟨⟨a, [.reverse pre], fire⟩, [.forward post]⟩⟩

def directFixture : Option Request := do
  let fire ← firing 0 b c
  pure ⟨snapshot, permissions, [], type, b, c, ⟨⟨b, [], fire⟩, []⟩⟩

def observed (request : Request) : Bool :=
  match decodeRequest (encodeRequest request) with
  | none => false
  | some decoded => decide (requestCodec.put decoded = requestCodec.put request)

def accepted (request : Request) : Bool := checkWord (encodeRequest request)
def refused (request : Request) : Bool := !accepted request

def mapBefore (request : Request) (edit : GeneralOccurrenceSemantics.Receipt → GeneralOccurrenceSemantics.Receipt) : Request :=
  { request with step := { request.step with before := edit request.step.before } }
def mapFiring (request : Request) (edit : GeneralRuleJobs.Receipt → GeneralRuleJobs.Receipt) : Request :=
  mapBefore request fun before => { before with firing := edit before.firing }
def mapPre (request : Request) (edit : GeneralEquationJobs.Receipt → GeneralEquationJobs.Receipt) : Request :=
  mapBefore request fun before => { before with conversions := before.conversions.map fun
    | .forward value => .forward (edit value)
    | .reverse value => .reverse (edit value) }

/-- A high zero before the first scalar terminator decodes to the same
number, but canonical whole-word storage must reject this alias. -/
def scalarAlias : List Binary.Alphabet → List Binary.Alphabet
  | [] => []
  | symbol :: rest => if symbol = 2 then 0 :: symbol :: rest else symbol :: scalarAlias rest

def falseHistory : List GeneralPremise.Event := [
  .query 2 3 11 [(0, [{ path := [8, 7], selected := 5 }])],
  .freshness 4 5 "fresh-空" (.lambda (some "display") (.bvar 0)),
  .quantified 6 7 .hashBag [
    (0, a, [.query 8 9 12 []]), (1, a, [.freshness 10 11 "another" b])],
  .child 12 13 99 [type, .arrow type type] a d
    [{ path := [1], selected := 0 }] [{ path := [2], selected := 1 }]
    [("captured", ⟨[type], 2, .bvar 0⟩)] [("completed", ⟨[], 2, c⟩)]
    [.quantified 14 15 .vec [(0, b, [.freshness 16 17 "inner" c])]] ]

def controlsFor (request : Request) : List (String × Bool) :=
  let badTag : Data := .pair (Codec.string.put "wrong-protocol") (requestFieldsCodec.put request)
  let word := encodeRequest request
  let aliasWord := scalarAlias word
  [
    ("source-valid-pre-firing-post", accepted request),
    ("all-original-fields-roundtrip", observed request),
    ("canonical-data-check", checkData (requestCodec.put request)),
    ("wrong-protocol-tag", (decodeData badTag).isNone),
    ("wrong-tag-source-check", !checkData badTag),
    ("wrong-tag-word", (decodeRequest (Binary.encodeData badTag)).isNone),
    ("bare-data-atom", (decodeData (.atom 0)).isNone),
    ("empty-word", (decodeRequest []).isNone),
    ("bad-root-symbol", (decodeRequest [0, 1, 2]).isNone),
    ("truncated-word", (decodeRequest (word.take (word.length - 1))).isNone),
    ("trailing-symbol-refused", (decodeRequest (word ++ [0])).isNone),
    ("trailing-packet-refused", (decodeRequest (word ++ word)).isNone),
    ("scalar-alias-changes-physical-word", decide (aliasWord ≠ word)),
    ("scalar-alias-still-decodes-with-ordinary-reader", (Binary.decodeWith requestCodec aliasWord).isSome),
    ("scalar-alias-canonical-refusal", (decodeRequest aliasWord).isNone),
    ("wrong-context", refused { request with bound := [type] }),
    ("wrong-sort", refused { request with type := .base "Undeclared" }),
    ("wrong-source", refused { request with source := .bvar 99 }),
    ("wrong-target", refused { request with target := a }),
    ("stale-rule-header", refused { request with snapshot := { request.snapshot with language :=
      { request.snapshot.language with rewrites := request.snapshot.language.rewrites.reverse } } }),
    ("stale-equation-header", refused { request with snapshot := { request.snapshot with language :=
      { request.snapshot.language with equations := request.snapshot.language.equations.reverse } } }),
    ("rule-permission-revoked", refused { request with permissions := { request.permissions with ruleIndices := some [] } }),
    ("equation-permission-revoked", refused { request with permissions := { request.permissions with equationIndices := some [] } }),
    ("site-permission-revoked", refused { request with permissions := { request.permissions with sites := .stopped } }),
    ("forged-representative", refused (mapBefore request fun before => { before with representative := c })),
    ("forged-rule-position", refused (mapFiring request fun fire => { fire with job := { fire.job with ordinal := 1 } })),
    ("unknown-rule-position", refused (mapFiring request fun fire => { fire with job := { fire.job with ordinal := 99 } })),
    ("forged-rule-annotation", refused (mapFiring request fun fire => { fire with job :=
      { fire.job with declaration := { fire.job.declaration with authored := { fire.job.declaration.authored with name := "forged" } } } })),
    ("forged-site-address", refused (mapFiring request fun fire => { fire with job :=
      { fire.job with site := { fire.job.site with address := [0] } } })),
    ("extra-matcher-choice", refused (mapFiring request fun fire =>
      { fire with matcherTrace := [{ path := [0], selected := 0 }] })),
    ("forged-captured-assignment", refused (mapFiring request fun fire =>
      { fire with captured := [("unknown", ⟨[], 0, a⟩)] })),
    ("forged-completed-assignment", refused (mapFiring request fun fire =>
      { fire with completed := [("unknown", ⟨[], 0, a⟩)] })),
    ("forged-premise-history", refused (mapFiring request fun fire => { fire with premiseHistory := falseHistory })),
    ("all-event-forms-lossless", observed (mapFiring request fun fire => { fire with premiseHistory := falseHistory })),
    ("forged-local-rule-result", refused (mapFiring request fun fire => { fire with localTarget := d })),
    ("forged-filled-rule-result", refused (mapFiring request fun fire => { fire with target := d })),
    ("forged-equation-position", refused (mapPre request fun receipt =>
      { receipt with job := { receipt.job with planPosition := 1 } })),
    ("unknown-equation-position", refused (mapPre request fun receipt =>
      { receipt with job := { receipt.job with planPosition := 99 } })),
    ("forged-equation-raw-result", refused (mapPre request fun receipt => { receipt with rawReduct := d })),
    ("forged-equation-observed-result", refused (mapPre request fun receipt => { receipt with target := a })),
    ("forged-equation-match-guidance", refused (mapPre request fun receipt =>
      { receipt with matcherTrace := [{ path := [], selected := 0 }] })),
    ("forged-equation-history", refused (mapPre request fun receipt => { receipt with premiseHistory := falseHistory })),
    ("missing-post-conversion", refused { request with step := { request.step with after := [] } }),
    ("unknown-conversion-tag", (conversionCodec.get (.pair (.atom 2) (requestFieldsCodec.put request))).isNone),
    ("missing-conversion-receipt", (conversionCodec.get (.pair (.atom 0) (.atom 0))).isNone),
    ("missing-equation-fields", (equationReceiptCodec.get (.atom 0)).isNone),
    ("missing-recipe-fields", (stepTraceCodec.get (.atom 0)).isNone),
    ("changed-target-physical-code", decide (encodeRequest { request with target := a } ≠ word)),
    ("changed-bound-physical-code", decide (encodeRequest { request with bound := [type] } ≠ word)),
    ("changed-permissions-physical-code", decide (encodeRequest { request with permissions :=
      { request.permissions with sites := .stopped } } ≠ word)) ]

def loopRequest (request : Request) : Request :=
  { request with step := { request.step with after := request.step.after ++ request.step.after.map GeneralRewriteRecipe.Conversion.reversed ++ request.step.after } }

def wireChecks : List (String × Bool) :=
  match fixture with
  | none => [("compiled original fixture", false)]
  | some request =>
    let loop := loopRequest request
    controlsFor request ++ [
      ("equation-loop-accepted", accepted loop),
      ("equation-loop-lossless", observed loop),
      ("equation-loop-retained-as-distinct-article", decide (encodeRequest request ≠ encodeRequest loop)),
      ("reverse-pre-conversion", reverseFixture.any accepted),
      ("reverse-conversion-roundtrip", reverseFixture.any observed),
      ("direct-rule-without-equations", directFixture.any accepted)]

namespace Arithmetic

open GeneralRewriteRecipe GeneralRewriteRecipeComposition

def nat : TypeExpr := .base "Nat"
def zero : Pattern := .apply "Z" []
def successor (value : Pattern) : Pattern := .apply "S" [value]
def add (left right : Pattern) : Pattern := .apply "Add" [left, right]
def pair (left right : Pattern) : Pattern := .apply "Pair" [left, right]

def language : LanguageDef where
  name := "authored-arithmetic-recipes"
  types := ["Nat"]
  terms := [
    {label := "Z", category := "Nat", params := [], syntaxPattern := []},
    {label := "S", category := "Nat", params := [.simple "n" nat], syntaxPattern := []},
    {label := "Add", category := "Nat", params := [.simple "m" nat, .simple "n" nat], syntaxPattern := []},
    {label := "Pair", category := "Nat", params := [.simple "m" nat, .simple "n" nat], syntaxPattern := []},
    {label := "Bag", category := "Nat", params := [.simple "elements" (.collection .hashBag nat)], syntaxPattern := []}]
  equations := []
  rewrites := [
    {name := "add-zero", typeContext := [("n", nat)], premises := [],
      left := add zero (.fvar "n"), right := .fvar "n"},
    {name := "bag-pair", typeContext := [("x", nat), ("y", nat)], premises := [],
      left := .collection .hashBag [.fvar "x", .fvar "y"] none,
      right := pair (.fvar "x") (.fvar "y")}]

def snapshot : Snapshot := ⟨language, [], {signatures := [], rows := []}⟩
def permissions : Permissions := {includeDerivedEquations := false}
def plan : Plan := compile snapshot permissions

def invocation (address : List Nat) (frames : List TypingFrame) : Recipe :=
  ⟨0, address, frames, [], []⟩

def root : Recipe := invocation [] []
def insideSuccessor : Recipe := invocation [0] [.application 1 0]
def insideBinder : Recipe := invocation [0] [.lambda nat]
def leftPair : Recipe := invocation [0] [.application 3 0]
def rightPair : Recipe := invocation [1] [.application 3 1]

def request? (bound : List TypeExpr) (type : TypeExpr) (source target : Pattern)
    (choices : Recipe) : Option Request := do
  let firing ← expand plan bound type source choices
  pure ⟨snapshot, permissions, bound, type, source, target, ⟨⟨source, [], firing⟩, []⟩⟩

def nestedSource : Pattern := successor (add zero zero)
def nestedTarget : Pattern := successor zero
def nestedRequest? : Option Request := request? [] nat nestedSource nestedTarget insideSuccessor
def binderSource : Pattern := .lambda none (add zero (.bvar 0))
def binderTarget : Pattern := .lambda none (.bvar 0)
def binderRequest? : Option Request :=
  request? [] (.arrow nat nat) binderSource binderTarget insideBinder

def pairSource : Pattern := pair (add zero zero) (add zero zero)
def pairTarget : Pattern := pair zero zero
def leftMiddle : Pattern := pair zero (add zero zero)
def rightMiddle : Pattern := pair (add zero zero) zero

def parallelTrace? (leftFirst : Bool) : Option Trace := do
  let middle := if leftFirst then leftMiddle else rightMiddle
  let first ← request? [] nat pairSource middle (if leftFirst then leftPair else rightPair)
  let second ← request? [] nat middle pairTarget (if leftFirst then rightPair else leftPair)
  pure [⟨middle, first.step⟩, ⟨pairTarget, second.step⟩]

def bagSource : Pattern := .collection .hashBag [zero, zero] none
def bagChoices (first : Nat) : Recipe :=
  {root with
    rulePosition := 1
    matching := [{path := [0], selected := first}, {path := [1], selected := 0}]}
def bagRequest? (first : Nat) : Option Request :=
  request? [] nat bagSource (pair zero zero) (bagChoices first)

def bagObservationsAgree : Bool :=
  match expand plan [] nat bagSource (bagChoices 0), expand plan [] nat bagSource (bagChoices 1) with
  | some first, some second =>
      decide (first.job.ordinal = second.job.ordinal ∧ first.job.site = second.job.site ∧
        first.captured = second.captured ∧ first.completed = second.completed ∧
        first.premiseHistory = second.premiseHistory ∧ first.target = second.target)
  | _, _ => false

def checks : List (String × Bool) := [
  ("arithmetic rules admitted", decide (plan.rules.length = 2)),
  ("nested selected occurrence", nestedRequest?.any accepted),
  ("binder-aware selected occurrence", binderRequest?.any accepted),
  ("under-binder ambient retained", (expand plan [] (.arrow nat nat) binderSource insideBinder).any
    fun value => decide (value.job.site.focusBound = [nat])),
  ("independent left-then-right", (parallelTrace? true).any
    (Trace.check plan [] nat pairSource pairTarget)),
  ("independent right-then-left", (parallelTrace? false).any
    (Trace.check plan [] nat pairSource pairTarget)),
  ("two rewrite occurrences retained", (parallelTrace? true).any fun value => decide (value.length = 2)),
  ("wrong nested goal refused", (request? [] nat nestedSource zero insideSuccessor).any refused),
  ("wrong intermediate join refused", (parallelTrace? true).any fun value =>
    match value with
    | first :: second :: [] => !Trace.check plan [] nat pairSource pairTarget
        [{first with next := rightMiddle}, second]
    | _ => false),
  ("nonexistent site refused", (expand plan [] nat nestedSource
    (invocation [1] [.application 1 1])).isNone),
  ("wrong grammar declaration refused", (expand plan [] nat nestedSource
    (invocation [0] [.application 2 0])).isNone),
  ("missing typing frame refused", (expand plan [] nat nestedSource (invocation [0] [])).isNone),
  ("wrong rule refused", (expand plan [] nat nestedSource {insideSuccessor with rulePosition := 8}).isNone),
  ("unused match choice refused", (expand plan [] nat nestedSource
    {insideSuccessor with matching := [{path := [], selected := 0}]}).isNone),
  ("unused premise evidence refused", (expand plan [] nat nestedSource
    {insideSuccessor with premises := [.query 0 0 0 []]}).isNone),
  ("dangling binder reference refused", (expand plan [] (.arrow nat nat)
    (.lambda none (add zero (.bvar 1))) insideBinder).isNone),
  ("forged binder sort refused", (expand plan [] (.arrow nat nat) binderSource
    (invocation [0] [.lambda (.base "Missing")])).isNone),
  ("no implicit root search", (expand plan [] nat nestedSource root).isNone),
  ("equal bag elements first permutation", (bagRequest? 0).any accepted),
  ("equal bag elements second permutation", (bagRequest? 1).any accepted),
  ("equal bag elements same firing observation", bagObservationsAgree),
  ("equal bag elements distinct replay words", (bagRequest? 0).any fun first =>
    (bagRequest? 1).any fun second => decide (encodeRequest first ≠ encodeRequest second)),
  ("bag multiplicity cannot be dropped", (expand plan [] nat
    (.collection .hashBag [zero] none) (bagChoices 0)).isNone),
  ("bag residual index checked", (expand plan [] nat bagSource
    {root with
      rulePosition := 1
      matching := [{path := [0], selected := 0}, {path := [1], selected := 1}]}).isNone)]

theorem nested_expansion :
    (expand plan [] nat nestedSource insideSuccessor).map GeneralRuleJobs.Receipt.target =
      some nestedTarget := by cbv

theorem binder_expansion :
    (expand plan [] (.arrow nat nat) binderSource insideBinder).map GeneralRuleJobs.Receipt.target =
      some binderTarget := by cbv

theorem equal_bag_observation : bagObservationsAgree = true := by cbv

theorem equal_bag_firing_identity :
    (expand plan [] nat bagSource (bagChoices 0)).map GeneralOccurrenceKeys.firingIdentity =
      (expand plan [] nat bagSource (bagChoices 1)).map GeneralOccurrenceKeys.firingIdentity := by cbv

theorem dangling_binder_refused :
    expand plan [] (.arrow nat nat) (.lambda none (add zero (.bvar 1))) insideBinder = none := by
  apply Option.isNone_iff_eq_none.mp
  cbv

end Arithmetic

def checks : List (String × Bool) := wireChecks ++ Arithmetic.checks

#guard checks.all Prod.snd

end Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeControls
