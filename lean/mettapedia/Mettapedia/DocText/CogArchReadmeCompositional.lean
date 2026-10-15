import Mettapedia.Languages.GF.HandCrafted.English.Examples
import Mettapedia.Languages.GF.HandCrafted.English.Pronouns
import Mettapedia.DocText.ReadmeGFHelpers
import Mettapedia.DocText.ReadmeTree
import Mettapedia.DocText.ReadmeStructuredParse

namespace Mettapedia.DocText.CogArchReadmeCompositional

open Mettapedia.Languages.GF.HandCrafted.English
open Mettapedia.Languages.GF.HandCrafted.English.Nouns
open Mettapedia.Languages.GF.HandCrafted.English.Verbs
open Mettapedia.Languages.GF.HandCrafted.English.Adjectives
open Mettapedia.Languages.GF.HandCrafted.English.Syntax
open Mettapedia.Languages.GF.HandCrafted.English.Pronouns
open Mettapedia.DocText.ReadmeGFHelpers
open Mettapedia.DocText.ReadmeTree
open Mettapedia.DocText.ReadmeStructuredParse

private def framework_N := regN "framework"
private def module_N := regN "module"
private def result_N := regN "result"
private def status_N := regN "status"

inductive CogArchClaim where
  | titleScope
  | fileCountAndSorryStatus
  | metamoSummary
  | openPsiSummary
  | microPsiSummary
  | bridgesSummary
  | valuesSummary
  | metamoBasicRole
  | metamoAppraisalRole
  | metamoDecisionRole
  | metamoCommutativityRole
  | metamoDynamicsRole
  | metamoMainRole
  | openPsiBasicRole
  | openPsiFuzzyLogicRole
  | openPsiActionSelectionRole
  | openPsiMetaMoInstanceRole
  | microPsiBasicRole
  | microPsiMetaMoInstanceRole
  | bridgePlnMetaMoRole
  | bridgeOpenPsiMicroPsiRole
  | bridgeModelExpressivenessRole
  | bridgeMissingValueSystemsRole
  | valueSchwartzRole
  | valueMoralFoundationsRole
  | valueDeontologicalLayerRole
  | valueRelationalValuesRole
  | valueTemporalValuesRole
  | valueMetaValuesRole
  | valueFoetBridgeRole
  | keyResultBothQModules
  | keyResultCommutativity
  | keyResultBanach
  | keyResultConsequentialistGap
  deriving Repr, DecidableEq, BEq

def renderCogArchClaim : CogArchClaim → String
  | .titleScope =>
      mkPresPos (properNameNP "Mettapedia/CogArch")
        (complV2 (mkV2 (regV "formalize")) (properNameNP "MetaMo, OpenPsi, MicroPsi, and their mathematical bridges"))
  | .fileCountAndSorryStatus =>
      mkPresNeg (properNameNP "This module")
        (complV2 (mkV2 (regV "contain")) (properNameNP "sorries across thirty-one files"))
  | .metamoSummary =>
      mkPresPos (properNameNP "MetaMo")
        (copulaNP (properNameNP "a six-file motivational Q-module framework"))
  | .openPsiSummary =>
      mkPresPos (properNameNP "OpenPsi")
        (copulaNP (properNameNP "a five-file formalization of Dorner Psi with six demands and four modulators"))
  | .microPsiSummary =>
      mkPresPos (properNameNP "MicroPsi")
        (copulaNP (properNameNP "a three-file formalization with seven demands and PAD decomposition"))
  | .bridgesSummary =>
      mkPresPos (properNameNP "Bridges" .AgP3Pl)
        (copulaNP (properNameNP "five files of cross-architecture comparison and limits"))
  | .valuesSummary =>
      mkPresPos (properNameNP "Values" .AgP3Pl)
        (copulaNP (properNameNP "nine files extending beyond consequentialism"))
  | .metamoBasicRole =>
      mkPresPos (properNameNP "MetaMo/Basic.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "Q-module structure with scalar multiplication"))
  | .metamoAppraisalRole =>
      mkPresPos (properNameNP "MetaMo/Appraisal.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "environmental stimulus appraisal functors"))
  | .metamoDecisionRole =>
      mkPresPos (properNameNP "MetaMo/Decision.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "action selection functors"))
  | .metamoCommutativityRole =>
      mkPresPos (properNameNP "MetaMo/Commutativity.lean")
        (complV2 (mkV2 (regV "prove")) (properNameNP "appraisal-decision commutativity"))
  | .metamoDynamicsRole =>
      mkPresPos (properNameNP "MetaMo/Dynamics.lean")
        (complV2 (mkV2 (regV "prove")) (properNameNP "stability via Banach fixed-point arguments"))
  | .metamoMainRole =>
      mkPresPos (properNameNP "MetaMo/Main.lean")
        (complV2 (mkV2 (regV "aggregate")) (properNameNP "the MetaMo module API"))
  | .openPsiBasicRole =>
      mkPresPos (properNameNP "OpenPsi/Basic.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "demands, modulators, and action-selection rules"))
  | .openPsiFuzzyLogicRole =>
      mkPresPos (properNameNP "OpenPsi/FuzzyLogic.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "fuzzy satisfaction computation"))
  | .openPsiActionSelectionRole =>
      mkPresPos (properNameNP "OpenPsi/ActionSelection.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "demand-driven action selection"))
  | .openPsiMetaMoInstanceRole =>
      mkPresPos (properNameNP "OpenPsi/MetaMoInstance.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "OpenPsi as a QModule over ENNReal"))
  | .microPsiBasicRole =>
      mkPresPos (properNameNP "MicroPsi/Basic.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "demands, PAD model, and utility action selection"))
  | .microPsiMetaMoInstanceRole =>
      mkPresPos (properNameNP "MicroPsi/MetaMoInstance.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "MicroPsi as a QModule over ENNReal"))
  | .bridgePlnMetaMoRole =>
      mkPresPos (properNameNP "Bridges/PLNMetaMoBridge.lean")
        (complV2 (mkV2 (regV "connect")) (properNameNP "PLN evidence quantales to MetaMo"))
  | .bridgeOpenPsiMicroPsiRole =>
      mkPresPos (properNameNP "Bridges/OpenPsiMicroPsiBridge.lean")
        (complV2 (mkV2 (regV "compare")) (properNameNP "OpenPsi and MicroPsi as MetaMo instances"))
  | .bridgeModelExpressivenessRole =>
      mkPresPos (properNameNP "Bridges/ModelExpressiveness.lean")
        (complV2 (mkV2 (regV "analyze")) (properNameNP "expressiveness boundaries"))
  | .bridgeMissingValueSystemsRole =>
      mkPresPos (properNameNP "Bridges/MissingValueSystems.lean")
        (complV2 (mkV2 (regV "prove")) (properNameNP "value-system gaps outside consequentialism"))
  | .valueSchwartzRole =>
      mkPresPos (properNameNP "Values/SchwartzValues.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "Schwartz ten-value circumplex structure"))
  | .valueMoralFoundationsRole =>
      mkPresPos (properNameNP "Values/MoralFoundations.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "Haidt six moral foundations"))
  | .valueDeontologicalLayerRole =>
      mkPresPos (properNameNP "Values/DeontologicalLayer.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "duty constraints above consequential utility"))
  | .valueRelationalValuesRole =>
      mkPresPos (properNameNP "Values/RelationalValues.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "individual-dependent relational values"))
  | .valueTemporalValuesRole =>
      mkPresPos (properNameNP "Values/TemporalValues.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "legacy and future-generation value structure"))
  | .valueMetaValuesRole =>
      mkPresPos (properNameNP "Values/MetaValues.lean")
        (complV2 (mkV2 (regV "define")) (properNameNP "values about values including corrigibility"))
  | .valueFoetBridgeRole =>
      mkPresPos (properNameNP "Values/FOETBridge.lean")
        (complV2 (mkV2 (regV "connect")) (properNameNP "value formalization to FOET"))
  | .keyResultBothQModules =>
      mkPresPos (properNameNP "OpenPsi and MicroPsi" .AgP3Pl)
        (copulaNP (properNameNP "MetaMo QModule instances"))
  | .keyResultCommutativity =>
      mkPresPos (properNameNP "Appraisal-decision commutativity")
        (copulaNP (properNameNP "proven when the quantale is commutative"))
  | .keyResultBanach =>
      mkPresPos (properNameNP "Contractivity")
        (copulaNP (properNameNP "a sufficient condition for unique motivational equilibrium"))
  | .keyResultConsequentialistGap =>
      mkPresPos (properNameNP "Gap analysis")
        (complV2 (mkV2 (regV "show")) (properNameNP "that both base architectures are fundamentally consequentialist"))

def allCogArchClaims : List CogArchClaim :=
  [ .titleScope
  , .fileCountAndSorryStatus
  , .metamoSummary
  , .openPsiSummary
  , .microPsiSummary
  , .bridgesSummary
  , .valuesSummary
  , .metamoBasicRole
  , .metamoAppraisalRole
  , .metamoDecisionRole
  , .metamoCommutativityRole
  , .metamoDynamicsRole
  , .metamoMainRole
  , .openPsiBasicRole
  , .openPsiFuzzyLogicRole
  , .openPsiActionSelectionRole
  , .openPsiMetaMoInstanceRole
  , .microPsiBasicRole
  , .microPsiMetaMoInstanceRole
  , .bridgePlnMetaMoRole
  , .bridgeOpenPsiMicroPsiRole
  , .bridgeModelExpressivenessRole
  , .bridgeMissingValueSystemsRole
  , .valueSchwartzRole
  , .valueMoralFoundationsRole
  , .valueDeontologicalLayerRole
  , .valueRelationalValuesRole
  , .valueTemporalValuesRole
  , .valueMetaValuesRole
  , .valueFoetBridgeRole
  , .keyResultBothQModules
  , .keyResultCommutativity
  , .keyResultBanach
  , .keyResultConsequentialistGap
  ]

def parseCogArchClaimLine? (line : String) : Option CogArchClaim :=
  let norm := stripTerminalPeriod line
  allCogArchClaims.find? (fun c => renderCogArchClaim c = norm)

inductive CogArchHeading where
  | title
  | modules
  | metamo
  | openPsi
  | microPsi
  | bridges
  | values
  | keyResults
  deriving Repr, DecidableEq, BEq

def renderCogArchHeading : CogArchHeading → String
  | .title =>
      headingNP (linAdjCN (linPositA (regA "cognitive architecture")) (linUseN framework_N))
  | .modules =>
      headingPlNP (linUseN module_N)
  | .metamo =>
      headingNP (linUseN (regN "MetaMo"))
  | .openPsi =>
      headingNP (linUseN (regN "OpenPsi"))
  | .microPsi =>
      headingNP (linUseN (regN "MicroPsi"))
  | .bridges =>
      headingPlNP (linUseN (regN "bridge"))
  | .values =>
      headingPlNP (linUseN (regN "value"))
  | .keyResults =>
      headingPlNP (linAdjCN (linPositA (regA "key")) (linUseN result_N))

def allCogArchHeadings : List CogArchHeading :=
  [ .title, .modules, .metamo, .openPsi, .microPsi, .bridges, .values, .keyResults ]

def parseCogArchHeadingLine? (line : String) : Option CogArchHeading :=
  allCogArchHeadings.find? (fun h => renderCogArchHeading h = line)

private def claimBullet (c : CogArchClaim) : ClaimBullet :=
  { text := renderCogArchClaim c }

def cognitiveArchitectureReadmeBlocks : List ReadmeBlock :=
  [ .heading 1 (renderCogArchHeading .title)
  , .paragraph
      [ renderCogArchClaim .titleScope
      , renderCogArchClaim .fileCountAndSorryStatus
      ]
  , .heading 2 (renderCogArchHeading .modules)
  , .heading 3 (renderCogArchHeading .metamo)
  , .paragraph [renderCogArchClaim .metamoSummary]
  , .fileRef "MetaMo/Basic.lean" (renderCogArchClaim .metamoBasicRole)
  , .fileRef "MetaMo/Appraisal.lean" (renderCogArchClaim .metamoAppraisalRole)
  , .fileRef "MetaMo/Decision.lean" (renderCogArchClaim .metamoDecisionRole)
  , .fileRef "MetaMo/Commutativity.lean" (renderCogArchClaim .metamoCommutativityRole)
  , .fileRef "MetaMo/Dynamics.lean" (renderCogArchClaim .metamoDynamicsRole)
  , .fileRef "MetaMo/Main.lean" (renderCogArchClaim .metamoMainRole)
  , .heading 3 (renderCogArchHeading .openPsi)
  , .paragraph [renderCogArchClaim .openPsiSummary]
  , .fileRef "OpenPsi/Basic.lean" (renderCogArchClaim .openPsiBasicRole)
  , .fileRef "OpenPsi/FuzzyLogic.lean" (renderCogArchClaim .openPsiFuzzyLogicRole)
  , .fileRef "OpenPsi/ActionSelection.lean" (renderCogArchClaim .openPsiActionSelectionRole)
  , .fileRef "OpenPsi/MetaMoInstance.lean" (renderCogArchClaim .openPsiMetaMoInstanceRole)
  , .heading 3 (renderCogArchHeading .microPsi)
  , .paragraph [renderCogArchClaim .microPsiSummary]
  , .fileRef "MicroPsi/Basic.lean" (renderCogArchClaim .microPsiBasicRole)
  , .fileRef "MicroPsi/MetaMoInstance.lean" (renderCogArchClaim .microPsiMetaMoInstanceRole)
  , .heading 3 (renderCogArchHeading .bridges)
  , .paragraph [renderCogArchClaim .bridgesSummary]
  , .fileRef "Bridges/PLNMetaMoBridge.lean" (renderCogArchClaim .bridgePlnMetaMoRole)
  , .fileRef "Bridges/OpenPsiMicroPsiBridge.lean" (renderCogArchClaim .bridgeOpenPsiMicroPsiRole)
  , .fileRef "Bridges/ModelExpressiveness.lean" (renderCogArchClaim .bridgeModelExpressivenessRole)
  , .fileRef "Bridges/MissingValueSystems.lean" (renderCogArchClaim .bridgeMissingValueSystemsRole)
  , .heading 3 (renderCogArchHeading .values)
  , .paragraph [renderCogArchClaim .valuesSummary]
  , .fileRef "Values/SchwartzValues.lean" (renderCogArchClaim .valueSchwartzRole)
  , .fileRef "Values/MoralFoundations.lean" (renderCogArchClaim .valueMoralFoundationsRole)
  , .fileRef "Values/DeontologicalLayer.lean" (renderCogArchClaim .valueDeontologicalLayerRole)
  , .fileRef "Values/RelationalValues.lean" (renderCogArchClaim .valueRelationalValuesRole)
  , .fileRef "Values/TemporalValues.lean" (renderCogArchClaim .valueTemporalValuesRole)
  , .fileRef "Values/MetaValues.lean" (renderCogArchClaim .valueMetaValuesRole)
  , .fileRef "Values/FOETBridge.lean" (renderCogArchClaim .valueFoetBridgeRole)
  , .heading 2 (renderCogArchHeading .keyResults)
  , .claimBullets
      [ claimBullet .keyResultBothQModules
      , claimBullet .keyResultCommutativity
      , claimBullet .keyResultBanach
      , claimBullet .keyResultConsequentialistGap
      ]
  ]

def cognitiveArchitectureReadmeMarkdown : String :=
  renderDoc cognitiveArchitectureReadmeBlocks

#eval cognitiveArchitectureReadmeMarkdown

inductive ParsedCogArchStructuredLine where
  | technical (line : ParsedTechnicalLine)
  | claimBullet (claim : CogArchClaim)
  | claimLine (claim : CogArchClaim)
  deriving Repr

def parseSelectedStructuredCogArchLine? (line : String) : Option ParsedCogArchStructuredLine :=
  match parseTechnicalLine? cognitiveArchitectureReadmeBlocks line with
  | some t => some (.technical t)
  | none =>
      if (claimBulletLines cognitiveArchitectureReadmeBlocks).contains line then
        match parseClaimBulletLine? parseCogArchClaimLine? line with
        | some c => some (.claimBullet c)
        | none => none
      else
        match parseCogArchClaimLine? line with
        | some c => some (.claimLine c)
        | none => none

def selectedStructuredCogArchLines : List String :=
  technicalLines cognitiveArchitectureReadmeBlocks ++
  claimBulletLines cognitiveArchitectureReadmeBlocks ++
  [ ensurePeriod (renderCogArchClaim .titleScope)
  , ensurePeriod (renderCogArchClaim .fileCountAndSorryStatus)
  , ensurePeriod (renderCogArchClaim .metamoSummary)
  ]

def cognitiveArchitectureHardAuditPasses : Bool :=
  cognitiveArchitectureReadmeBlocks.all (blockPassesHardAuditWith parseCogArchClaimLine? parseCogArchHeadingLine?)

theorem cognitiveArchitecture_hard_audit :
    cognitiveArchitectureHardAuditPasses = true := by
  native_decide

def cognitiveArchitectureHeadingImageCheck : Bool :=
  headingRenderImageCheck parseCogArchHeadingLine? renderCogArchHeading cognitiveArchitectureReadmeBlocks

theorem cognitiveArchitecture_heading_images :
    cognitiveArchitectureHeadingImageCheck = true := by
  native_decide

theorem cognitiveArchitecture_heading_image_witness
    {lvl : Nat} {txt : String}
    (hMem : (lvl, txt) ∈ headingEntries cognitiveArchitectureReadmeBlocks) :
    ∃ h, parseCogArchHeadingLine? txt = some h ∧ renderCogArchHeading h = txt := by
  exact headingRenderImageWitness
    parseCogArchHeadingLine? renderCogArchHeading cognitiveArchitectureReadmeBlocks
    cognitiveArchitecture_heading_images hMem

private def insertRenderedBucket (acc : List (String × List CogArchClaim)) (rendered : String)
    (c : CogArchClaim) : List (String × List CogArchClaim) :=
  match acc with
  | [] => [(rendered, [c])]
  | (k, cs) :: rest =>
      if k = rendered then
        (k, c :: cs) :: rest
      else
        (k, cs) :: insertRenderedBucket rest rendered c

def claimRenderedBuckets : List (String × List CogArchClaim) :=
  allCogArchClaims.foldl
    (fun acc c => insertRenderedBucket acc (renderCogArchClaim c) c) []

def ambiguousClaimRenderings : List (String × List CogArchClaim) :=
  claimRenderedBuckets.filter (fun p => p.snd.length > 1)

#eval
  let fails := allCogArchClaims.filter (fun c =>
    parseCogArchClaimLine? (renderCogArchClaim c) != some c)
  if fails.isEmpty then
    "CogArch parse-back check: all claim lines roundtrip"
  else
    s!"CogArch parse-back failures: {repr fails}"

#eval
  if cognitiveArchitectureHardAuditPasses then
    "CogArch hard audit: no prose-bearing bypass blocks detected"
  else
    "CogArch hard audit: violation detected"

#eval
  let fails := selectedStructuredCogArchLines.filter
    (fun line =>
      match parseSelectedStructuredCogArchLine? line with
      | none => true
      | _ => false)
  if fails.isEmpty then
    "CogArch parse-back check: selected headings + bullet families roundtrip"
  else
    s!"CogArch structured parse failures: {repr fails}"

#eval
  if ambiguousClaimRenderings.isEmpty then
    "CogArch ambiguity diagnostic: no duplicate renderings across distinct claims"
  else
    s!"CogArch ambiguity diagnostic: duplicate renderings found: {repr ambiguousClaimRenderings}"

end Mettapedia.DocText.CogArchReadmeCompositional
