import Mettapedia.GSLT.LanguageDef.GeneralPremiseNativeEvidence
import Mettapedia.GSLT.LanguageDef.BindingSignatureWire
import Mettapedia.GSLT.LanguageDef.CertificateDataEncoding

/-!
# Exact finite data for original authored premise receipts

The wire carries original declarations, plans, typed occurrences, assignments
and finite events. It does not serialize an arbitrary dynamic provider
function: the consumer fixes that service independently. Full plan data and
literal scope/source/result fields remain available for authorization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GeneralPremiseReceiptWire

open Mettapedia.OSLF.MeTTaIL
open Syntax RuleBinding ScopedRuleMatching GeneralPremise GeneralExecutionAdmission GeneralTypedSites
open Mettapedia.OSLF.Binding.WireCodec


def patternCodec : Codec Pattern := CertificateDataEncoding.patternCodec

def booleanCodec : Codec Bool := BindingSyntax.Wire.physicalCodec.mapped
  InferenceCettaWire.ContextObservation.booleanTerm InferenceCettaWire.ContextObservation.decodeBoolean? InferenceCettaWire.ContextObservation.decodeBoolean?_booleanTerm

def bindingCodec : Codec RuleBindingSpec := BindingSyntax.Wire.physicalCodec.mapped
  InferenceCettaWire.AuthoredRule.bindingSpecTerm InferenceCettaWire.AuthoredRule.decodeBindingSpec? InferenceCettaWire.AuthoredRule.decodeBindingSpec?_bindingSpecTerm

def rewriteCodec : Codec RewriteRule := BindingSyntax.Wire.physicalCodec.mapped
  InferenceCettaWire.AuthoredRule.rewriteTerm InferenceCettaWire.AuthoredRule.decodeRewrite? InferenceCettaWire.AuthoredRule.decodeRewrite?_rewriteTerm

def valueCodec : Codec ContextualValue := BindingSyntax.Wire.physicalCodec.mapped
  InferenceCettaWire.AuthoredRule.contextualValueTerm InferenceCettaWire.AuthoredRule.decodeContextualValue? InferenceCettaWire.AuthoredRule.decodeContextualValue?_contextualValueTerm

def assignmentCodec : Codec Assignment := Codec.list (Codec.prod Codec.string valueCodec)

def contextCodec : Codec DerivedContexts.OneHoleContext := BindingSyntax.Wire.physicalCodec.mapped
  InferenceCettaWire.ContextObservation.contextTerm InferenceCettaWire.ContextObservation.decodeContext? InferenceCettaWire.ContextObservation.decodeContext?_contextTerm

def typeBindingCodec : Codec (String × TypeExpr) := Codec.prod Codec.string BindingSyntax.Wire.typeCodec

def modeCodec : Codec RelationArgMode := Codec.nat.mapped
  (fun mode => match mode with | .input => 0 | .output => 1)
  (fun value => match value with | 0 => some .input | 1 => some .output | _ => none)
  (fun mode => by cases mode <;> rfl)

def orientationCodec : Codec ScopedEquationExecution.Orientation := Codec.nat.mapped
  (fun direction => match direction with | .forward => 0 | .reverse => 1)
  (fun value => match value with | 0 => some .forward | 1 => some .reverse | _ => none)
  (fun direction => by cases direction <;> rfl)

private def putSelection : Option (List Nat) → Data
  | none => .atom 0
  | some values => .pair (.atom 1) ((Codec.list Codec.nat).put values)
private def getSelection : Data → Option (Option (List Nat))
  | .atom 0 => some none
  | .pair (.atom 1) values => ((Codec.list Codec.nat).get values).map some
  | _ => none

def selectionCodec : Codec (Option (List Nat)) := ⟨putSelection, getSelection, fun value => by
  cases value with
  | none => rfl
  | some values => simp only [putSelection, getSelection, Codec.get_put]; rfl⟩

private def putOrigin : GeneralRuleBindingInference.Origin → Data
  | .authored => .atom 0
  | .inferredRootInputs => .atom 1
  | .inferredGrammar values => .pair (.atom 2) ((Codec.list typeBindingCodec).put values)
private def getOrigin : Data → Option GeneralRuleBindingInference.Origin
  | .atom 0 => some .authored
  | .atom 1 => some .inferredRootInputs
  | .pair (.atom 2) values => ((Codec.list typeBindingCodec).get values).map .inferredGrammar
  | _ => none

def originCodec : Codec GeneralRuleBindingInference.Origin := ⟨putOrigin, getOrigin, fun value => by
  cases value with
  | authored | inferredRootInputs => rfl
  | inferredGrammar values => simp only [putOrigin, getOrigin, Codec.get_put]; rfl⟩

def bindingPlanCodec : Codec GeneralRuleBindingInference.BindingPlan :=
  (Codec.prod bindingCodec originCodec).mapped
    (fun value => (value.spec, value.origin))
    (fun fields => some ⟨fields.1, fields.2⟩)
    (fun _ => rfl)

def rulePlanCodec : Codec RulePlan :=
  (Codec.prod Codec.nat (Codec.prod rewriteCodec bindingPlanCodec)).mapped
    (fun value => (value.declarationIndex, value.authored, value.binding))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2⟩)
    (fun _ => rfl)

def equationCodec : Codec Equation := rewriteCodec.mapped
  (fun equation => ⟨equation.name, equation.typeContext, equation.premises, equation.left, equation.right, equation.bindings⟩)
  (fun rule => some ⟨rule.name, rule.typeContext, rule.premises, rule.left, rule.right, rule.bindings⟩)
  (fun _ => rfl)

def equationPlanCodec : Codec EquationPlan :=
  (Codec.prod Codec.nat (Codec.prod equationCodec (Codec.prod orientationCodec (Codec.prod bindingPlanCodec booleanCodec)))).mapped
    (fun value => (value.declarationIndex, value.authored, value.direction, value.binding, value.coverageReady))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2⟩)
    (fun _ => rfl)

/-- All five original language fields are retained, including complete
source syntax/algebra metadata and every equation/conditional rewrite. -/
def languageCodec : Codec LanguageDef :=
  (Codec.prod BindingSyntax.Wire.Header.codec (Codec.prod (Codec.list equationCodec) (Codec.list rewriteCodec))).mapped
    (fun language => (BindingSyntax.Wire.Header.value language, language.equations, language.rewrites))
    (fun fields => some ⟨fields.1.1, fields.1.2.1, fields.1.2.2, fields.2.1, fields.2.2⟩)
    (fun _ => rfl)

def signatureCodec : Codec GeneralPremise.Signature :=
  (Codec.prod Codec.string (Codec.prod (Codec.list BindingSyntax.Wire.typeCodec) (Codec.list modeCodec))).mapped
    (fun value => (value.relation, value.argumentTypes, value.modes))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2⟩)
    (fun _ => rfl)

def providerRowCodec : Codec ProviderRow :=
  (Codec.prod Codec.string (Codec.list patternCodec)).mapped
    (fun value => (value.relation, value.values))
    (fun fields => some ⟨fields.1, fields.2⟩)
    (fun _ => rfl)

def providerCodec : Codec ProviderSnapshot :=
  (Codec.prod (Codec.list signatureCodec) (Codec.prod (Codec.list providerRowCodec) (Codec.list Codec.string))).mapped
    (fun value => (value.signatures, value.rows, value.dynamicRelations))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2⟩)
    (fun _ => rfl)

def snapshotCodec : Codec Snapshot :=
  (Codec.prod languageCodec (Codec.prod (Codec.list typeBindingCodec) providerCodec)).mapped
    (fun value => (value.language, value.freeTypes, value.provider))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2⟩)
    (fun _ => rfl)

def presentationCodec : Codec ReflectivePresentationDecl := BindingSyntax.Wire.physicalCodec.mapped
  InferenceCettaWire.AuthoredRule.reflectivePresentationTerm InferenceCettaWire.AuthoredRule.decodeReflectivePresentation? InferenceCettaWire.AuthoredRule.decodeReflectivePresentation?_reflectivePresentationTerm

def reflectiveRuleCodec : Codec ReflectiveRuleDecl :=
  (Codec.prod Codec.string (Codec.prod Codec.string (Codec.prod Codec.string Codec.string))).mapped
    (fun value => (value.name, value.rewriteRule, value.matchingPresentation, value.substitutionPresentation))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩)
    (fun _ => rfl)

def reflectionCodec : Codec Reflection.ReflectionProfile :=
  (Codec.prod (Codec.list presentationCodec) (Codec.list reflectiveRuleCodec)).mapped
    (fun value => (value.presentations, value.rules))
    (fun fields => some ⟨fields.1, fields.2⟩)
    (fun _ => rfl)

def sitePermissionsCodec : Codec OperationalPermissions := BindingSyntax.Wire.physicalCodec.mapped
  InferenceCettaWire.ContextObservation.permissionsTerm InferenceCettaWire.ContextObservation.decodePermissions? InferenceCettaWire.ContextObservation.decodePermissions?_permissionsTerm

def permissionsCodec : Codec Permissions :=
  (Codec.prod sitePermissionsCodec (Codec.prod selectionCodec (Codec.prod selectionCodec (Codec.prod (Codec.list orientationCodec) (Codec.prod booleanCodec reflectionCodec))))).mapped
    (fun value => (value.sites, value.ruleIndices, value.equationIndices, value.equationDirections, value.includeDerivedEquations, value.reflection))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1, fields.2.2.2.2.2⟩)
    (fun _ => rfl)

private def putObligation : Obligation → Data
  | .invalidLanguage  => .atom 0
  | .invalidFreeContext  => .atom 1
  | .invalidProvider  => .atom 2
  | .invalidReflection  => .atom 3
  | .missingRule index => .pair (.atom 4) (.atom index)
  | .missingEquation index => .pair (.atom 5) (.atom index)
  | .ruleBinding index => .pair (.atom 6) (.atom index)
  | .rulePremises index => .pair (.atom 7) (.atom index)
  | .ruleCanonical index => .pair (.atom 8) (.atom index)
  | .equationBinding index direction => .pair (.atom 9) (.pair (.atom index) (orientationCodec.put direction))
  | .equationPremises index direction => .pair (.atom 10) (.pair (.atom index) (orientationCodec.put direction))
  | .equationCanonical index direction => .pair (.atom 11) (.pair (.atom index) (orientationCodec.put direction))
  | .equationBound index direction => .pair (.atom 12) (.pair (.atom index) (orientationCodec.put direction))
  | .childStratification  => .atom 13
  | .derivedEquationCoverage  => .atom 14
private def getObligation : Data → Option Obligation
  | .atom 0 => some .invalidLanguage
  | .atom 1 => some .invalidFreeContext
  | .atom 2 => some .invalidProvider
  | .atom 3 => some .invalidReflection
  | .pair (.atom 4) (.atom index) => some (.missingRule index)
  | .pair (.atom 5) (.atom index) => some (.missingEquation index)
  | .pair (.atom 6) (.atom index) => some (.ruleBinding index)
  | .pair (.atom 7) (.atom index) => some (.rulePremises index)
  | .pair (.atom 8) (.atom index) => some (.ruleCanonical index)
  | .pair (.atom 9) (.pair (.atom index) direction) => (orientationCodec.get direction).map (.equationBinding index)
  | .pair (.atom 10) (.pair (.atom index) direction) => (orientationCodec.get direction).map (.equationPremises index)
  | .pair (.atom 11) (.pair (.atom index) direction) => (orientationCodec.get direction).map (.equationCanonical index)
  | .pair (.atom 12) (.pair (.atom index) direction) => (orientationCodec.get direction).map (.equationBound index)
  | .atom 13 => some .childStratification
  | .atom 14 => some .derivedEquationCoverage
  | _ => none

def obligationCodec : Codec Obligation := ⟨putObligation, getObligation, fun value => by
  cases value <;> simp only [putObligation, getObligation, Codec.get_put] <;> rfl⟩

def planCodec : Codec Plan :=
  (Codec.prod snapshotCodec (Codec.prod permissionsCodec (Codec.prod (Codec.list rulePlanCodec) (Codec.prod (Codec.list equationPlanCodec) (Codec.list obligationCodec))))).mapped
    (fun value => (value.snapshot, value.permissions, value.rules, value.equations, value.obligations))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2⟩)
    (fun _ => rfl)

/-- A matching wire header determines the original entire finite plan. It
contains no assertion about the identity of a separately installed handler. -/
theorem plan_header_exact (first second : Plan) :
    planCodec.put first = planCodec.put second ↔ first = second := planCodec.put_injective.eq_iff

private def putFrame : TypingFrame → Data
  | .application declaration argument => .pair (.atom 0) ((Codec.prod Codec.nat Codec.nat).put (declaration, argument))
  | .lambda domain => .pair (.atom 1) (BindingSyntax.Wire.typeCodec.put domain)
  | .multiLambda arity domain => .pair (.atom 2) ((Codec.prod Codec.nat BindingSyntax.Wire.typeCodec).put (arity, domain))
  | .directCollection kind => .pair (.atom 3) (BindingSyntax.Wire.kindCodec.put kind)
  | .authoredCollection declaration => .pair (.atom 4) (.atom declaration)
private def getFrame : Data → Option TypingFrame
  | .pair (.atom 0) fields => ((Codec.prod Codec.nat Codec.nat).get fields).map (fun fields => .application fields.1 fields.2)
  | .pair (.atom 1) domain => BindingSyntax.Wire.typeCodec.get domain |>.map .lambda
  | .pair (.atom 2) fields => ((Codec.prod Codec.nat BindingSyntax.Wire.typeCodec).get fields).map (fun fields => .multiLambda fields.1 fields.2)
  | .pair (.atom 3) kind => BindingSyntax.Wire.kindCodec.get kind |>.map .directCollection
  | .pair (.atom 4) (.atom declaration) => some (.authoredCollection declaration)
  | _ => none

def frameCodec : Codec TypingFrame := ⟨putFrame, getFrame, fun value => by
  cases value <;> simp only [putFrame, getFrame, Codec.get_put] <;> rfl⟩

def siteCodec : Codec SiteData :=
  (Codec.prod (Codec.list Codec.nat) (Codec.prod contextCodec (Codec.prod patternCodec (Codec.prod (Codec.list BindingSyntax.Wire.typeCodec) (Codec.prod BindingSyntax.Wire.typeCodec (Codec.list frameCodec)))))).mapped
    (fun value => (value.address, value.context, value.focus, value.focusBound, value.focusType, value.typingFrames))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1, fields.2.2.2.2.2⟩)
    (fun _ => rfl)

def jobCodec : Codec GeneralRuleJobs.Job :=
  (Codec.prod Codec.nat (Codec.prod rulePlanCodec siteCodec)).mapped
    (fun value => (value.ordinal, value.declaration, value.site))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2⟩)
    (fun _ => rfl)

def bagChoiceCodec : Codec GeneralScopedMatchMachine.BagChoice :=
  (Codec.prod (Codec.list Codec.nat) Codec.nat).mapped
    (fun value => (value.path, value.selected))
    (fun fields => some ⟨fields.1, fields.2⟩)
    (fun _ => rfl)

def traceCodec : Codec (List GeneralScopedMatchMachine.BagChoice) := Codec.list bagChoiceCodec

private def queryFields := Codec.prod Codec.nat (Codec.prod Codec.nat (Codec.prod Codec.nat (Codec.list (Codec.prod Codec.nat traceCodec))))

private def freshnessFields := Codec.prod Codec.nat (Codec.prod Codec.nat (Codec.prod Codec.string patternCodec))

private def quantifiedFields := Codec.prod Codec.nat (Codec.prod Codec.nat BindingSyntax.Wire.kindCodec)

private def childFields := Codec.prod Codec.nat (Codec.prod Codec.nat (Codec.prod Codec.nat (Codec.prod (Codec.list BindingSyntax.Wire.typeCodec) (Codec.prod patternCodec (Codec.prod patternCodec (Codec.prod traceCodec (Codec.prod traceCodec (Codec.prod assignmentCodec assignmentCodec))))))))


mutual
/-- Full original child histories, including query row/argument origins. -/
def putEvent : Event → Data
  | .query p q row origins => .pair (.atom 0) (queryFields.put (p, q, row, origins))
  | .freshness p q atom subject => .pair (.atom 1) (freshnessFields.put (p, q, atom, subject))
  | .quantified p q kind elements =>
      .pair (.atom 2) (.pair (quantifiedFields.put (p, q, kind)) (putQuantifiedEvents elements))
  | .child p q index bound source target trace targetTrace captured completed history =>
      .pair (.atom 3) (.pair (childFields.put (p, q, index, bound, source, target, trace, targetTrace, captured, completed))
        (putEvents history))

def putEvents : List Event → Data
  | [] => .atom 0
  | event :: events => .pair (putEvent event) (putEvents events)

def putQuantifiedEvents : List (Nat × Pattern × List Event) → Data
  | [] => .atom 0
  | (index, element, events) :: later =>
      .pair (.pair (.atom index) (.pair (patternCodec.put element) (putEvents events))) (putQuantifiedEvents later)
end

mutual
def getEvent : Data → Option Event
  | .pair (.atom 0) fields => (queryFields.get fields).map (fun fields =>
      .query fields.1 fields.2.1 fields.2.2.1 fields.2.2.2)
  | .pair (.atom 1) fields => (freshnessFields.get fields).map (fun fields =>
      .freshness fields.1 fields.2.1 fields.2.2.1 fields.2.2.2)
  | .pair (.atom 2) (.pair fields elements) => do
      let fields ← quantifiedFields.get fields
      return .quantified fields.1 fields.2.1 fields.2.2 (← getQuantifiedEvents elements)
  | .pair (.atom 3) (.pair fields history) => do
      let fields ← childFields.get fields
      return .child fields.1 fields.2.1 fields.2.2.1 fields.2.2.2.1 fields.2.2.2.2.1
        fields.2.2.2.2.2.1 fields.2.2.2.2.2.2.1 fields.2.2.2.2.2.2.2.1
        fields.2.2.2.2.2.2.2.2.1 fields.2.2.2.2.2.2.2.2.2 (← getEvents history)
  | _ => none

def getEvents : Data → Option (List Event)
  | .atom 0 => some []
  | .pair event events => do return (← getEvent event) :: (← getEvents events)
  | _ => none

def getQuantifiedEvents : Data → Option (List (Nat × Pattern × List Event))
  | .atom 0 => some []
  | .pair (.pair (.atom index) (.pair element events)) later => do
      return (index, ← patternCodec.get element, ← getEvents events) :: (← getQuantifiedEvents later)
  | _ => none
end

mutual
theorem get_putEvent : ∀ event, getEvent (putEvent event) = some event
  | .query p q row origins => by simp only [putEvent, getEvent, Codec.get_put]; rfl
  | .freshness p q atom subject => by simp only [putEvent, getEvent, Codec.get_put]; rfl
  | .quantified p q kind elements => by
      simp only [putEvent, getEvent, Codec.get_put, get_putQuantifiedEvents elements]; rfl
  | .child p q index bound source target trace targetTrace captured completed history => by
      simp only [putEvent, getEvent, Codec.get_put, get_putEvents history]; rfl

theorem get_putEvents : ∀ events, getEvents (putEvents events) = some events
  | [] => rfl
  | event :: events => by simp only [putEvents, getEvents, get_putEvent event, get_putEvents events]; rfl

theorem get_putQuantifiedEvents : ∀ events, getQuantifiedEvents (putQuantifiedEvents events) = some events
  | [] => rfl
  | (index, element, events) :: later => by
      simp only [putQuantifiedEvents, getQuantifiedEvents, Codec.get_put, get_putEvents events,
        get_putQuantifiedEvents later]; rfl
end

def eventCodec : Codec Event := ⟨putEvent, getEvent, get_putEvent⟩
def eventsCodec : Codec (List Event) := ⟨putEvents, getEvents, get_putEvents⟩

def receiptCodec : Codec GeneralRuleJobs.Receipt :=
  (Codec.prod jobCodec (Codec.prod traceCodec (Codec.prod assignmentCodec (Codec.prod assignmentCodec (Codec.prod eventsCodec (Codec.prod patternCodec patternCodec)))))).mapped
    (fun value => (value.job, value.matcherTrace, value.captured, value.completed, value.premiseHistory, value.localTarget, value.target))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1, fields.2.2.2.2.2.1, fields.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-- Canonical binary storage reuses the common finite-alphabet codec. -/
def encodeReceipt (value : GeneralRuleJobs.Receipt) : List Binary.Alphabet := Binary.encodeWith receiptCodec value

def decodeReceipt (word : List Binary.Alphabet) : Option GeneralRuleJobs.Receipt :=
  Binary.canonicalDecodeWith receiptCodec word

theorem decodeReceipt_encodeReceipt (value : GeneralRuleJobs.Receipt) :
    decodeReceipt (encodeReceipt value) = some value := Binary.canonicalDecodeWith_encodeWith receiptCodec value

theorem decodeReceipt_exact (word : List Binary.Alphabet) (value : GeneralRuleJobs.Receipt) :
    decodeReceipt word = some value ↔ encodeReceipt value = word := Binary.canonicalDecodeWith_exact receiptCodec word value


/-- The finite authorization payload excludes the independently installed
dynamic function, while retaining its selected registry coordinate. -/
abbrev Header := Lean.Name × Lean.Name × Plan × List TypeExpr × TypeExpr

def headerCodec : Codec Header := Codec.prod Codec.name (Codec.prod Codec.name
  (Codec.prod planCodec (Codec.prod (Codec.list BindingSyntax.Wire.typeCodec) BindingSyntax.Wire.typeCodec)))

def header (scope handler : Lean.Name) (plan : Plan) (bound : List TypeExpr) (type : TypeExpr) : Header :=
  (scope, handler, plan, bound, type)

private def tagged {Value : Type} (tag : String) (codec : Codec Value) : Codec Value :=
  (Codec.prod Codec.string codec).mapped
    (fun value => (tag, value))
    (fun value => if value.1 = tag then some value.2 else none)
    (fun _ => by simp only [ite_true])

def claimCodec : Codec GeneralPremiseNativeEvidence.Claim := Codec.prod patternCodec patternCodec

def requestCodec : Codec (Header × GeneralPremiseNativeEvidence.Claim) :=
  tagged "GSLT.AuthoredFiring.Request.v1" (Codec.prod headerCodec claimCodec)

def proofCodec : Codec (Header × GeneralRuleJobs.Receipt) :=
  tagged "GSLT.AuthoredFiring.Proof.v1" (Codec.prod headerCodec receiptCodec)

end Mettapedia.GSLT.LanguageDef.GeneralPremiseReceiptWire
