import Mettapedia.OSLF.NativeTypes.Generation.AuthoredControls
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeDisplay
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeReceiptControls

/-!
# Original language consumers of one generated native interface

The same installation, native checker, retained fair search and operational
executor serve all presentations. Structural and dependent certificates are
checked in the actual shared cube-enriched signature. Logical falsehood
formation and failed membership remain distinct from proving negation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf

/-- Structural graphs use full native predicate equality. Removing a required
logical feature refuses the certificate, rather than refuting the type. -/
def structuralVocabulary (language : LanguageDef) (enabled : NativeLogic.Fragment) :
    Option NativeLogic.CheckResult := do
  let logic := {BindingPipeline.Controls.fullLogic with native := enabled}
  let installed ← (generateLanguage language .star BindingPipeline.Controls.fragment logic).toOption
  let constructor ← (List.finRange installed.operational.declarations.headers.length).head?
  let certificate := Certificates.Refinement.erase (installed.structuralEvidence constructor)
  return installed.check certificate certificate.root.conclusion

def runVocabulary : IO Unit := do
  for (label, fragment, expected) in
      [("full", NativeLogic.full, NativeLogic.CheckResult.accepted),
       ("functions disabled", ⟨NativeLogic.full.enabled.filter (· != .functions)⟩, .vocabularyRefused),
       ("universal disabled", ⟨NativeLogic.full.enabled.filter (· != .universal)⟩, .vocabularyRefused)] do
    IO.eprintln ("Checking vocabulary: " ++ label)
    if structuralVocabulary BindingPipeline.Controls.originalLambda fragment != some expected then
      throw (IO.userError ("Structural vocabulary control failed: " ++ label))
    IO.eprintln ("Checked vocabulary: " ++ label)

def checkGeneratedEvidence (language : LanguageDef) : Bool :=
  match generateLanguage language with
  | .error _ => false
  | .ok installed =>
      let structural := (List.finRange installed.operational.declarations.headers.length).all fun constructor =>
        let tree := installed.structuralEvidence constructor
        let certificate := Certificates.Refinement.erase tree
        installed.check certificate certificate.root.conclusion == .accepted
      let responses := (List.finRange installed.operational.modal.length).all fun index =>
        let tree := installed.responseEvidence index
        let certificate := Certificates.Refinement.erase tree
        installed.check certificate certificate.root.conclusion == .accepted
      let cube := installed.formerList.all fun former =>
        let tree := installed.cubeDerivation
          (CubeNativeClosedFormation.primitiveFormation installed.vertex (.formation former))
        let certificate := Certificates.Refinement.erase tree
        installed.check certificate certificate.root.conclusion == .accepted
      structural && responses && cube

def searchStructural (language : LanguageDef) : Bool :=
  match generateLanguage language with
  | .error _ => false
  | .ok installed =>
      let prepared := installed.prepare
      (List.finRange installed.operational.declarations.headers.length).all fun constructor =>
        let certificate := Certificates.Refinement.erase (installed.structuralEvidence constructor)
        (prepared.search certificate.root.conclusion prepared.factories.length).found.isSome

def nativeAnswers (language : LanguageDef) :
    Option (BindingPipeline.Installed.NativeAnswer × BindingPipeline.Installed.NativeAnswer ×
      NativeLogic.CheckResult) := do
  let installed ← (generateLanguage language).toOption
  let prepared := installed.prepare
  let empty := deriveList (D := installed.signature) .contextNil .nil
  let truth := deriveList (.truthIntroduction .nil) (.cons empty .nil)
  let certificate := Certificates.Refinement.erase truth
  return (prepared.query (.entails .nil .truth) 0,
    prepared.query (.entails .nil .truth) prepared.factories.length,
    installed.check certificate (.entails .nil .falsehood))

def emitChecked {installed : Installed} {judgment : Judgment installed.symbols}
    (label : String) (tree : Derivation installed.signature judgment) : IO Unit := do
  let certificate := Certificates.Refinement.erase tree
  let result := installed.check certificate judgment
  if result != .accepted then
    throw (IO.userError (label ++ ": " ++ reprStr result))
  IO.eprintln ("Checked " ++ label)
  IO.println (label ++ " : " ++ installed.renderNative judgment ++
    "; certificate=" ++ reprStr result ++
    "; certificate nodes=" ++ toString (Installed.evidenceNodes certificate))

def runConstructors (installed : Installed) (prepared : installed.Prepared) : IO Unit := do
  for constructor in List.finRange installed.operational.declarations.headers.length do
    IO.eprintln ("Building structural " ++ installed.formerName (.inl constructor))
    let tree := installed.structuralEvidence constructor
    emitChecked ("Structural " ++ installed.formerName (.inl constructor)) tree
    let certificate := Certificates.Refinement.erase tree
    IO.eprintln ("Searching structural " ++ installed.formerName (.inl constructor))
    if !(prepared.search certificate.root.conclusion prepared.factories.length).found.isSome then
      throw (IO.userError ("Structural search failed: " ++ installed.formerName (.inl constructor)))
    IO.eprintln ("Found structural " ++ installed.formerName (.inl constructor))

def runResponses (installed : Installed) : IO Unit := do
  for index in List.finRange installed.operational.modal.length do
    emitChecked ("Response " ++ installed.formerName (.inr index)) (installed.responseEvidence index)

def runProjections (installed : Installed) : IO Unit := do
  let mut projectionNumber := 0
  for projection in NativeModalSignature.projections
      (BindingPipeline.plan installed.operational.generated) installed.operational.modal do
    emitChecked ("Projection #" ++ toString projectionNumber) (installed.operationalDerivation
      (NativeModalSignature.projectionFormation (BindingPipeline.plan installed.operational.generated)
        installed.operational.declarations installed.operational.modal projection))
    projectionNumber := projectionNumber + 1

def runCubeBatch (installed : Installed) (start count : Nat) : IO Unit := do
  for former in (installed.formerList.drop start).take count do
    IO.eprintln ("Building cube " ++ installed.formerName former)
    emitChecked ("Cube " ++ installed.formerName former) (installed.cubeDerivation
      (CubeNativeClosedFormation.primitiveFormation installed.vertex (.formation former)))

def runAnswers (installed : Installed) (prepared : installed.Prepared) : IO Unit := do
  let empty := deriveList (D := installed.signature) .contextNil .nil
  let truth := deriveList (.truthIntroduction .nil) (.cons empty .nil)
  let answers := (prepared.query (.entails .nil .truth) 0,
    prepared.query (.entails .nil .truth) prepared.factories.length,
    installed.check (Certificates.Refinement.erase truth) (.entails .nil .falsehood))
  if answers != (.unknown, .proved, .certificateRejected) then
    throw (IO.userError ("Native answers failed: " ++ reprStr answers))
  IO.println ("Native answers checked; unknown/proof/bad-certificate=" ++ reprStr answers)

/-- Each actual certificate is checked and displayed once. A failed check or
search result fails the executable consumer matrix. -/
def runGenerated (installed : Installed) : IO Unit := do
  IO.eprintln ("Checking language " ++ installed.operational.authored.name)
  IO.println ("Language " ++ installed.operational.authored.name)
  let prepared := installed.prepare
  runConstructors installed prepared
  runResponses installed
  runProjections installed
  runCubeBatch installed 0 installed.formerList.length
  runAnswers installed prepared
  IO.println "Generated evidence checked=true; structural judgments discovered=true"

/-- Operational receipts are decoded and checked in the generated position
families. Complete parameters and ordered execution evidence are displayed
alongside the checked native projection judgments. -/
def runReceipts (installed : Installed) (ambient : List String) (sort : String)
    (pattern : Pattern) (budget : Nat) (expectFrames : Bool) : IO Unit := do
  let frames := ReceiptControls.execute installed ambient sort pattern budget
  if (!frames.isEmpty != expectFrames) || !frames.all ReceiptControls.frameComplete then
    throw (IO.userError ("Native receipt checking failed: " ++ installed.operational.authored.name))
  IO.println ("Native frames " ++ installed.operational.authored.name ++
    "; checked=" ++ toString frames.length ++ "; complete parameters=true")
  for frame in frames do
    IO.println (ReceiptControls.renderFrame frame)

structure Fixture where
  language : LanguageDef
  sort : String
  pattern : Pattern
  budget : Nat

def fixtures : List Fixture :=
  [⟨BindingPipeline.Controls.originalLambda, "Term", BindingPipeline.Controls.lambdaSource.term, 2000⟩,
   ⟨BindingPipeline.Controls.originalMachine, "Cfg", BindingPipeline.Controls.machineSource.term, 500⟩,
   ⟨BindingPipeline.Controls.originalLetCase, "Computation", BindingPipeline.Controls.letCaseSource.term, 2000⟩]

def withLanguage (language : LanguageDef) (action : Installed → IO Unit) : IO Unit := do
  match generateLanguage language with
  | .error reason => throw (IO.userError ("Generation refused: " ++ reprStr reason))
  | .ok installed => action installed

def withFixture (index : Nat) (action : Fixture → Installed → IO Unit) : IO Unit := do
  let some fixture := fixtures[index]?
    | throw (IO.userError ("Missing native fixture #" ++ toString index))
  withLanguage fixture.language (action fixture)

def runConstructorsFixture (index : Nat) : IO Unit :=
  withFixture index fun _ installed => runConstructors installed installed.prepare

def runResponsesFixture (index : Nat) : IO Unit :=
  withFixture index fun _ installed => runResponses installed

def runProjectionsFixture (index : Nat) : IO Unit :=
  withFixture index fun _ installed => runProjections installed

/-- The scheduled runtime slices retain the complete generated former list.
The independent coverage control rejects a catalogue exceeding this schedule. -/
def cubeBatchSize : Nat := 8
def cubeBatchCount : Nat := 20
def cubeBatchIndices : List Nat := List.range cubeBatchCount

def cubeSlices (installed : Installed) : List (List (NativeCubeProfile.Former installed.operational)) :=
  cubeBatchIndices.map fun batch =>
    (installed.formerList.drop (batch * cubeBatchSize)).take cubeBatchSize

def cubeCoverage (installed : Installed) : Bool :=
  decide (installed.formerList.length ≤ cubeBatchCount * cubeBatchSize) &&
    decide ((cubeSlices installed).flatten = installed.formerList)

theorem cubeCoverage_exact (installed : Installed) :
    cubeCoverage installed = true ↔
      installed.formerList.length ≤ cubeBatchCount * cubeBatchSize ∧
        (cubeSlices installed).flatten = installed.formerList := by
  simp only [cubeCoverage, Bool.and_eq_true, decide_eq_true_eq]

def checkCubeCoverage (installed : Installed) : IO Unit := do
  if !cubeCoverage installed then
    throw (IO.userError ("Cube runtime schedule incomplete: " ++ installed.operational.authored.name ++
      "; generated formers=" ++ toString installed.formerList.length))
  IO.println ("Cube runtime coverage " ++ installed.operational.authored.name ++
    "; generated formers=" ++ toString installed.formerList.length ++
    "; complete ordered slices=true")

def runCubeCoverage : IO Unit := do
  for fixture in fixtures do
    withLanguage fixture.language checkCubeCoverage

def runCubeFixturesBatch (batch : Nat) : IO Unit := do
  if !(batch ∈ cubeBatchIndices) then
    throw (IO.userError ("Unscheduled cube runtime batch #" ++ toString batch))
  for fixture in fixtures do
    withLanguage fixture.language fun installed => do
      checkCubeCoverage installed
      runCubeBatch installed (batch * cubeBatchSize) cubeBatchSize

def runAnswersFixtures : IO Unit := do
  for fixture in fixtures do
    withLanguage fixture.language fun installed => runAnswers installed installed.prepare

def runPrimaryReceipts : IO Unit := do
  for fixture in fixtures do
    withLanguage fixture.language fun installed =>
      runReceipts installed [] fixture.sort fixture.pattern fixture.budget true

def runAdditionalReceipts : IO Unit := do
  withLanguage BindingPipeline.Controls.originalLambda fun installed => do
    runReceipts installed [] "Term" ReceiptControls.relySource 2000 true
    runReceipts installed [] "Term" ReceiptControls.underBinderSource 2000 true
    runReceipts installed [] "Term" ReceiptControls.relySource 0 false
  withLanguage BindingPipeline.Controls.originalMachine fun installed =>
    runReceipts installed [] "Cfg" BindingPipeline.Controls.stoppedMachine.term 500 false

def main : IO Unit := do
  runVocabulary
  for fixture in fixtures do
    withLanguage fixture.language fun installed => do
      runGenerated installed
      runReceipts installed [] fixture.sort fixture.pattern fixture.budget true
  runAdditionalReceipts

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls
