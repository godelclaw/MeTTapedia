import Mettapedia.Logic.ProofSharingBounds
import Mettapedia.Logic.PropositionalHilbertChecking
import Mettapedia.Logic.PropositionalExtension
import Mettapedia.Logic.IntuitionisticDecision
import Mettapedia.Logic.EqualityRecipe
import Mettapedia.GSLT.Logic.PropositionalLRAT
import Mettapedia.Languages.Lean.HintedHeadConversion
import Mettapedia.Languages.MeTTa.EquationKernel.Execution
import Mettapedia.Languages.MeTTa.EquationKernel.Controls
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeExecution
import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeExecution
import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeCompositionControls
import Mettapedia.Languages.VibeITP.CheckingMachine
import Mettapedia.GSLT.Logic.KripkeTruthChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.TowerChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.IndexedFamilyChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.InductiveElaboration
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorProgramChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorComputationProfiles
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorCheckingProfiles
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedAppend
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ScopedSubstitutionInversion
import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendSource
import Mettapedia.Languages.Megalodon.NaturalClosure
import Mettapedia.Languages.MM0.NaturalClosure
import Mettapedia.Languages.MM0.NaturalInduction
import Mettapedia.Languages.MM0.NaturalCarrier
import Mettapedia.Languages.MM0.NaturalType
import Mettapedia.Languages.MM0.NaturalRecursion
import Mettapedia.Languages.MM0.NaturalFactsMeaning
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorRawPreservation
import Mettapedia.Languages.MM0.HOLTypeDefinitionBoundary
import Mettapedia.Languages.HOLLight.NaturalFacts
import Mettapedia.Languages.Megalodon.NaturalRecursion
import Mettapedia.Languages.Megalodon.NaturalTheoryProfile
import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendChecking
import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLComparison
import Mettapedia.Logic.HOL.ConversionRecipeControls

/-! # Executable integration controls for native inference checking -/

set_option autoImplicit false

namespace Mettapedia.Logic.CheckNativeInference

open Mettapedia.Languages.MeTTa.EquationKernel

def equationChecks : List (String × Bool) :=
  let certificate := Controls.incTerm
  let worked := Execution.advance Controls.incProgram certificate.rows.length (Execution.start certificate)
  let first := Execution.advance Controls.incProgram 1 (Execution.start certificate)
  let resumed := Execution.advance Controls.incProgram (certificate.rows.length - 1) first
  let bad : Certificate := { certificate with rows := certificate.rows ++ [.trans certificate.rows.length 0] }
  [("equation nested application", Execution.verdict certificate Controls.incClaim worked),
   ("equation exact resume", decide (worked.accumulator = resumed.accumulator) &&
      decide (worked.pending = resumed.pending) && (worked.refused == resumed.refused)),
   ("equation missing theory", !(Execution.verdict certificate Controls.incClaim
      (Execution.advance [] certificate.rows.length (Execution.start certificate)))),
   ("equation unused invalid row", !(Execution.verdict bad Controls.incClaim
      (Execution.advance Controls.incProgram bad.rows.length (Execution.start bad))))]

def recipeChecks : List (String × Bool) :=
  match Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeCompositionControls.DAG.sharedFixture with
  | none => [("authored fixture construction", false)]
  | some request =>
      let plan := Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.compile
        request.header.snapshot request.header.permissions
      let run := Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeExecution.advance
        plan request.header.bound request.header.type
      let start := Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeExecution.start
      let verdict := Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeExecution.verdict
      let wanted := (request.header.source, request.header.target)
      let worked := run request.graph.nodes.length (start request.graph)
      let first := run 1 (start request.graph)
      let resumed := run (request.graph.nodes.length - 1) first
      let bad := { request.graph with nodes := request.graph.nodes ++
        [.trans request.header.source request.header.target request.header.target request.graph.nodes.length 0] }
      [("authored shared DAG", verdict request.graph wanted worked),
       ("authored exact resume", decide (worked.accumulator = resumed.accumulator) &&
         decide (worked.pending.length = resumed.pending.length) && (worked.refused == resumed.refused)),
       ("authored unused invalid row", !(verdict bad wanted (run bad.nodes.length (start bad))))]

def hilbertChecks : List (String × Bool) :=
  let proof := PropositionalHilbertChecking.Controls.emCertificate
  let claim := PropositionalHilbertChecking.Controls.em
  [("classical excluded middle", (PropositionalHilbertChecking.checker .classical).check claim proof),
   ("intuitionistic rule boundary", !((PropositionalHilbertChecking.checker .intuitionistic).check claim proof)),
   ("Hilbert changed conclusion", !((PropositionalHilbertChecking.checker .classical).check .falsum proof)),
   ("retained classical proof term", (PropositionalHilbertChecking.elaborate? .classical claim proof).isSome),
   ("retained intuitionistic rule refusal", (PropositionalHilbertChecking.elaborate? .intuitionistic claim proof).isNone),
   ("retained changed goal refusal", (PropositionalHilbertChecking.elaborate? .classical .falsum proof).isNone),
   ("Hilbert missing premise", !(PropositionalHilbertChecking.checkRule .classical
      (.mp .falsum .falsum) [.falsum] .falsum))]

def hintChecks : List (String × Bool) :=
  let beta := Mettapedia.Languages.Lean.HintedHeadConversion.Controls.betaSource
  let check := (Mettapedia.Languages.Lean.HintedHeadConversion.checker [] 0).check
  let omega := Mettapedia.Languages.Lean.HintedHeadConversion.Controls.omega
  [("head strategy normalizes beta", check (beta, .sort .zero) [⟨2, (.sort .zero, true)⟩]),
   ("head strategy pending is not normal", !(check (beta, .sort .zero) [⟨1, (.sort .zero, false)⟩])),
   ("head strategy forged terminal flag", !(check (omega, omega) [⟨10, (omega, true)⟩]))]

def refusalChecks : List (String × Bool) :=
  let consume := fun accumulator item : Nat => if item = 2 then none else some (accumulator + item)
  let result := Mettapedia.Machines.ProductiveCoreAdapters.RetainedFold.advance consume 3
    (Mettapedia.Machines.ProductiveCoreAdapters.RetainedFold.start [1, 2, 3] 0)
  [("refusal keeps accepted prefix", result.accumulator == 1),
   ("refusal keeps entire suffix", decide (result.pending = [2, 3])),
   ("refusal cannot publish", result.result.isNone),
   ("refusal stops work", result.inspected == 2)]

def equalityChecks : List (String × Bool) :=
  let compare := EqualityRecipe.Controls.adjacent
  let check := (EqualityRecipe.checker compare).check
  let composed := EqualityRecipe.Controls.composed
  [("comparison need not be transitive", !(compare.check (0, 2) ())),
   ("explicit equality composes", check (0, 2) composed),
   ("explicit equality reverses", check (2, 0) (.symm composed)),
   ("equality mismatched join refuses", !(check (0, 3)
      (.trans (.leaf 0 1 ()) (.leaf 2 3 ())))),
   ("equality wrong claim refuses", !(check (0, 3) composed))]

def extensionChecks : List (String × Bool) :=
  let claim := PropositionalExtension.Controls.oldClaim
  let worked := PropositionalExtension.Controls.worked
  let fresh := PropositionalExtension.Controls.fresh
  let validate := PropositionalExtension.validate (PropositionalExtension.atoms claim)
  [("extension used by native DAG", PropositionalExtension.checkDAG claim worked),
   ("extension changed root refuses", !(PropositionalExtension.checkDAG .falsum worked)),
   ("extension missing declaration refuses", !(PropositionalExtension.checkDAG claim
      { worked with definitions := [] })),
   ("extension goal-symbol collision", !(validate [⟨0, .falsum⟩])),
   ("extension recursive definition", !(validate [PropositionalExtension.Controls.cyclic])),
   ("extension forward dependency", !(validate [⟨1, .atom 2⟩, ⟨2, .atom 0⟩])),
   ("extension repeated definition", !(validate [fresh, fresh])),
   ("extension literal expansion", PropositionalExtension.formulaNodes
      (PropositionalExtension.unfold (PropositionalExtension.chainFrom 0 5) (.atom 5)) == 63)]

def intuitionisticChecks : List (String × Bool) :=
  let model := IntuitionisticDecision.Controls.fork
  let em := IntuitionisticDecision.Controls.excludedMiddle
  let truth := IntuitionisticDecision.Controls.truth
  let proof := IntuitionisticDecision.Controls.truthProof
  [("intuitionistic finite countermodel", IntuitionisticDecision.checkCountermodel em model),
   ("intuitionistic true claim cannot be refuted", !(IntuitionisticDecision.checkCountermodel truth model)),
   ("intuitionistic malformed order", !(IntuitionisticDecision.checkCountermodel em { model with edges := [(0, 1)] })),
   ("intuitionistic nonpersistent valuation", !(IntuitionisticDecision.checkCountermodel em { model with values := [(0, 0)] })),
   ("intuitionistic out of bounds world", !(IntuitionisticDecision.checkCountermodel em { model with root := 2 })),
   ("intuitionistic proof packet", IntuitionisticDecision.checkProof truth proof),
   ("intuitionistic changed proof claim", !(IntuitionisticDecision.checkProof .falsum proof)),
   ("intuitionistic encoded proof candidate", IntuitionisticDecision.searchCheck truth
      (IntuitionisticDecision.encodeWitness (.inl proof))),
   ("intuitionistic encoded countermodel candidate", IntuitionisticDecision.searchCheck em
      (IntuitionisticDecision.encodeWitness (.inr model))),
   ("intuitionistic exhaustive negative decision", !(IntuitionisticDecision.decideFormula .falsum)),
   ("intuitionistic hinted positive decision", IntuitionisticDecision.decideHinted truth [.inl proof]),
   ("intuitionistic hinted negative decision", !(IntuitionisticDecision.decideHinted em [.inr model])),
   ("intuitionistic invalid hint falls back", !(IntuitionisticDecision.decideHinted .falsum [.inl proof]))]

def checks : List (String × Bool) :=
  Mettapedia.Languages.HOLLight.NaturalFacts.verdicts ++
  Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.Annotated.verdicts ++
  Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.ComputationProfiles.NaturalConversion.Controls.verdicts ++
  Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.Annotated.metadataVerdicts ++
  Mettapedia.GSLT.LanguageDef.IndexedInductive.AppendChecking.verdicts ++
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.SchemaTableConversionCode.Linking.Controls.verdicts ++
  Mettapedia.Languages.Megalodon.NaturalClosure.verdicts ++
  Mettapedia.Languages.MM0.NaturalClosure.verdicts ++
  Mettapedia.Languages.MM0.NaturalInduction.verdicts ++
  Mettapedia.Languages.MM0.NaturalCarrier.verdicts ++
  Mettapedia.Languages.MM0.NaturalType.verdicts ++
  Mettapedia.Languages.MM0.NaturalRecursion.verdicts ++
  Mettapedia.Languages.MM0.NaturalFactsMeaning.verdicts ++
  Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.ComputationProfiles.NaturalConversion.RawPreservation.verdicts ++
  Mettapedia.Languages.MM0.HOLTypeDefinitionBoundary.verdicts ++
  Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.Annotated.Functions.verdicts ++
  Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.Annotated.Append.verdicts ++
  Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.Annotated.Append.computationVerdicts ++
  Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.Annotated.Append.profileVerdicts ++
  Mettapedia.Languages.Megalodon.NaturalRecursion.verdicts ++
  Mettapedia.Languages.Megalodon.NaturalTheoryProfile.verdicts ++
  Mettapedia.GSLT.LanguageDef.IndexedInductive.OperationSource.Controls.verdicts ++
  Mettapedia.GSLT.LanguageDef.IndexedInductive.OperationSource.Controls.clauseVerdicts ++
  Mettapedia.GSLT.LanguageDef.IndexedInductive.AppendSource.verdicts ++
  Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.ComputationProfiles.verdicts ++
  Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.CheckingProfiles.verdicts ++
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ScopedSubstitutionInversion.Controls.verdicts ++
  Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.Computation.verdicts ++
  Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.Programs.verdicts ++
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.InductiveElaborationControls.verdicts ++
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.IndexedFamilyCheckingControls.verdicts ++
  HOL.ConversionRecipes.Controls.verdicts ++
  Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.HOLComparison.Controls.verdicts ++
  Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tower.Checking.Controls.verdicts ++
    Mettapedia.GSLT.Logic.PropositionalLRAT.Controls.verdicts ++
    equationChecks ++ recipeChecks ++ hilbertChecks ++ hintChecks ++ refusalChecks ++ equalityChecks ++
    extensionChecks ++ intuitionisticChecks ++
    Mettapedia.Languages.VibeITP.CheckingMachine.CursorControls.verdicts ++
    Mettapedia.GSLT.KripkeTruth.Checking.Controls.verdicts ++
    [("sharing level three", Mettapedia.OSLF.NativeTypes.Certificates.Shared.checkJudgments
      (ProofSharingBounds.certificate 3) 3),
     ("sharing wrong level", !(Mettapedia.OSLF.NativeTypes.Certificates.Shared.checkJudgments
      (ProofSharingBounds.certificate 3) 4))]

end Mettapedia.Logic.CheckNativeInference

def main : IO UInt32 := do
  let checks := Mettapedia.Logic.CheckNativeInference.checks
  let mut failed := 0
  for (label, passed) in checks do
    unless passed do
      IO.eprintln s!"FAIL {label}"
      failed := failed + 1
  IO.println s!"Native inference integration: {checks.length - failed}/{checks.length} controls passed"
  return if failed = 0 then 0 else 1
