import Mettapedia.OSLF.NativeTypes.Structural.DecompositionReadout
import Mettapedia.OSLF.MeTTaIL.GeneralEquationSeparators
import Mettapedia.OSLF.MeTTaIL.GeneralRhoBinding
import Mettapedia.OSLF.MeTTaIL.GeneralRhoFrontierControls
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceUniversalCompletion

open Mettapedia.OSLF.Framework

/-!
# Execution controls for generated positional and spatial judgments

The free binary language checks its actual ordered components. Rho checks
partitions of its real hash-bag carrier, including its generated unit former.
Unfinished and modal component questions retain unknown answers.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open GeneralOccurrenceFrontier
open Mettapedia.GSLT.LanguageDef.WellSorted

private def readoutLanguage : LanguageDef :=
  { GeneralEquationSeparators.unitLanguage with equations := [] }

private def readoutSnapshot : GeneralExecutionAdmission.Snapshot :=
  ⟨readoutLanguage, [], ⟨[], [], []⟩⟩

private def readoutPermissions : GeneralExecutionAdmission.Permissions where
  includeDerivedEquations := false

private def readoutSource : Pattern :=
  .apply "Parallel" [.apply "Atom" [], .apply "Zero" []]

private def readoutPlan : GeneralExecutionAdmission.Plan :=
  ⟨readoutSnapshot, readoutPermissions, [], [], []⟩

private theorem readout_compiled :
    GeneralExecutionAdmission.compile readoutSnapshot readoutPermissions = readoutPlan := by
  cbv

private def readoutRequest : Request :=
  ⟨readoutPlan, [], .base "Proc", readoutSource⟩

private def discoveredFree : State readoutRequest := run _ 1 (start _)

private theorem readout_admitted : Admitted readoutRequest := by
  refine ⟨readout_compiled.symm, rfl, checkOpenPatternWellSorted_sound ?_⟩
  cbv

private def completedFree : State readoutRequest := finish _ readout_admitted

private def readoutBinary : GrammarRule := readoutLanguage.terms[2]'(by decide)
private def readoutBinaryShape : BinaryShape :=
  ⟨.simple "P" (.base "Proc"), .simple "Q" (.base "Proc"), .base "Proc", .base "Proc"⟩
private def atomValue : Pattern := .apply "Atom" []
private def zeroValue : Pattern := .apply "Zero" []

private theorem source_same : readoutRequest.root = readoutSource := by
  simp [readoutRequest, Request.root, readoutSource, Pattern.eraseBinderMetadata]

private theorem first_case_checked :
    splitCase? readoutRequest readoutBinary readoutSource =
      some ⟨readoutSource, atomValue, zeroValue⟩ := by
  simp [splitCase?, constructorArguments?, readoutRequest, readoutPlan, readoutSnapshot,
    readoutBinary, readoutLanguage, GeneralEquationSeparators.unitLanguage, readoutSource,
    atomValue, zeroValue, checkArgumentsHaveTypes, checkHasType,
    parameterType?, matchesParameterRepresentation?, usesBareCollection?]

private theorem discovered_cases : splitCases readoutRequest discoveredFree readoutBinary =
    [⟨readoutSource, atomValue, zeroValue⟩] := by
  unfold splitCases discoveredFree
  rw [first_represented _ (checkOpenPatternWellSorted_complete readout_admitted.rootSorted), source_same]
  simp only [List.filterMap_cons, List.filterMap_nil, first_case_checked]

private theorem first_atom : readComponentFormula readoutRequest (.base "Proc") atomValue 1
    (.root 0) = some true := by
  apply first_component_root (declaration := readoutLanguage.terms[0]'(by decide)) (arguments := [])
  · cbv
  · rfl
  · rfl
  · cbv

private theorem first_zero : readComponentFormula readoutRequest (.base "Proc") zeroValue 1
    (.root 1) = some true := by
  apply first_component_root (declaration := readoutLanguage.terms[1]'(by decide)) (arguments := [])
  · cbv
  · rfl
  · rfl
  · cbv

private theorem same_free_representative {state : State readoutRequest} {term : Pattern}
    (member : term ∈ representedPatterns readoutRequest state) : term = readoutSource := by
  have related := representedPattern_equivalent member
  have noEquation : ∀ first second,
      GeneralOccurrenceSemantics.Equation readoutRequest.plan readoutRequest.bound
        readoutRequest.expected first second → False := by
    intro first second equation
    obtain ⟨receipt, completed, _⟩ := equation
    have occurrence := completed.job.1
    change _ ∈ ([] : List (GeneralExecutionAdmission.EquationPlan × Nat)) at occurrence
    cases occurrence
  have every : ∀ first second, frontierEquation readoutRequest readoutRequest.expected
      first second → first = second := by
    intro first second conversion
    induction conversion with
    | rel first second equation => exact False.elim (noEquation first second equation)
    | refl term => rfl
    | symm first second _ equality => exact equality.symm
    | trans first middle last _ _ firstEqual secondEqual => exact firstEqual.trans secondEqual
  have same := every _ _ related
  exact same.symm.trans source_same

private theorem all_free_cases_same {state : State readoutRequest} {candidate : SplitCase}
    (member : candidate ∈ splitCases readoutRequest state readoutBinary) :
    candidate = ⟨readoutSource, atomValue, zeroValue⟩ := by
  obtain ⟨term, represented, checked⟩ := List.mem_filterMap.mp member
  have same := same_free_representative represented
  rw [same, first_case_checked] at checked
  exact (Option.some.inj checked).symm

private theorem false_free_case :
    readSplitCase readoutRequest readoutBinaryShape .top .bottom 0
      ⟨readoutSource, atomValue, zeroValue⟩ = some false := by
  cbv

/-- The output is obtained by inspecting and executing the actual two
components, without reading a constructor-mode flag in their place. -/
theorem free_positional_readout_executes :
    readGeneratedFormula readoutRequest discoveredFree 1 (.split 2 (.root 0) (.root 1)) =
      some true := by
  change readSplitCases readoutRequest discoveredFree readoutBinary readoutBinaryShape
    (.root 0) (.root 1) 1 = some true
  unfold readSplitCases splitAnswers
  rw [discovered_cases]
  simp only [List.map_cons, List.map_nil, readSplitCase, readoutBinaryShape, first_atom,
    first_zero, readBinary, Bool.and_self, readExistential, List.any_cons, List.any_nil, beq_self_eq_true,
    Bool.or_false, if_true]

theorem free_positional_readout_semantics :
    Holds readoutLanguage readoutSnapshot.free [] (frontierEquation readoutRequest)
      (fun _ _ _ => False) (.base "Proc") (.split 2 (.root 0) (.root 1)) readoutSource := by
  have result := (readGeneratedFormula_sound readout_admitted (fun _ _ _ => False) 1
    (.split 2 (.root 0) (.root 1)) true free_positional_readout_executes).mp rfl
  change Holds _ _ _ _ _ _ _ readoutSource.eraseBinderMetadata at result
  simpa [readoutRequest, readoutPlan, readoutSnapshot, readoutSource,
    Pattern.eraseBinderMetadata] using result

theorem free_frontier_coverage_checked : checkCertificate readoutRequest completedFree = true := by
  apply finish_certificate_of_generic_admission readout_admitted
  decide +kernel

theorem free_wrong_position_refuted :
    ¬ Holds readoutLanguage readoutSnapshot.free [] (fun _ => Eq) (fun _ _ _ => False)
      (.base "Proc") (.split 2 (.root 1) (.root 0)) readoutSource := by
  intro holds
  obtain ⟨_, value, same, left, right, arguments, firstHolds, secondHolds⟩ :=
    (holds_split_exact (declaration := readoutBinary) (index := 2) (by rfl)
      (by rfl) (by rfl) (by rfl) (.root 1) (.root 0) readoutSource).mp holds
  cases value with
  | ordinary actual ordinary typed =>
      change readoutSource = .apply "Parallel" actual at same
      change actual = [left, right] at arguments
      simp only [readoutSource, Pattern.apply.injEq, true_and] at same
      have pair := same.trans arguments
      simp only [List.cons.injEq, and_true] at pair
      rcases pair with ⟨first, second⟩
      obtain ⟨_, value, wrong⟩ := (holds_root_exact (declaration := readoutLanguage.terms[1]'(by decide))
        (index := 1) (by rfl) left).mp firstHolds
      cases value <;> simp [ConstructorValue.pattern, readoutLanguage,
        GeneralEquationSeparators.unitLanguage, ← first] at wrong
  | collection name kind sort elements rest shape typed =>
      change readoutBinary.params = [.simple name (.collection kind sort)] at shape
      cases shape

theorem free_false_component_refuted :
    readGeneratedFormula readoutRequest completedFree 0 (.split 2 .top .bottom) =
      some false := by
  unfold readGeneratedFormula readFrontierSplit
  change readSplitCases readoutRequest completedFree readoutBinary readoutBinaryShape .top .bottom 0 = some false
  unfold readSplitCases readExistential
  have certificate := free_frontier_coverage_checked
  simp only [certificate, Bool.true_and]
  split
  · rename_i impossible
    obtain ⟨candidate, member, observed⟩ := List.any_eq_true.mp impossible
    obtain ⟨a, present, same⟩ := List.mem_map.mp member
    subst candidate
    have sound := readSplitCase_sound readout_admitted (fun _ _ _ => False)
      readoutBinaryShape .top .bottom 0 a
    have positive : readSplitCase readoutRequest readoutBinaryShape .top .bottom 0 a = some true := by
      simpa only [beq_iff_eq] using observed
    exact False.elim ((sound true positive).mp rfl).2
  · have all : (splitAnswers readoutRequest completedFree readoutBinary readoutBinaryShape
        .top .bottom 0).all Option.isSome = true := by
      apply List.all_eq_true.mpr
      intro answer member
      obtain ⟨candidate, inside, same⟩ := List.mem_map.mp member
      rw [all_free_cases_same inside, false_free_case] at same
      rw [← same]
      rfl
    rw [if_pos all]

theorem unfinished_false_component_unknown :
    readGeneratedFormula readoutRequest discoveredFree 0 (.split 2 .top .bottom) = none := by
  change readSplitCases readoutRequest discoveredFree readoutBinary readoutBinaryShape .top .bottom 0 = none
  unfold readSplitCases splitAnswers
  rw [discovered_cases]
  have unfinished := first_unfinished readoutRequest
    (checkOpenPatternWellSorted_complete readout_admitted.rootSorted)
  have rejected := unfinished_certificate_rejected readoutRequest discoveredFree unfinished
  simp only [List.map_cons, List.map_nil, false_free_case, readExistential, List.any_cons,
    List.any_nil, Bool.or_false, rejected, Bool.false_and]
  rfl

theorem unfinished_component_unknown :
    readGeneratedFormula readoutRequest discoveredFree 0 (.split 2 (.root 0) (.root 1)) = none := by
  change readSplitCases readoutRequest discoveredFree readoutBinary readoutBinaryShape
    (.root 0) (.root 1) 0 = none
  unfold readSplitCases splitAnswers
  rw [discovered_cases]
  have unfinished := first_unfinished readoutRequest
    (checkOpenPatternWellSorted_complete readout_admitted.rootSorted)
  have rejected := unfinished_certificate_rejected readoutRequest discoveredFree unfinished
  have component : readSplitCase readoutRequest readoutBinaryShape (.root 0) (.root 1) 0
      ⟨readoutSource, atomValue, zeroValue⟩ = none := by
    cbv
  simp only [List.map_cons, List.map_nil, component, readExistential, List.any_cons,
    List.any_nil, Bool.or_false, rejected, Bool.false_and]
  rfl

theorem resuming_component_discovers_its_constructor :
    readComponentFormula readoutRequest (.base "Proc") (.apply "Atom" []) 0 (.root 0) = none ∧
      readComponentFormula readoutRequest (.base "Proc") (.apply "Atom" []) 1 (.root 0) =
        some true := by
  constructor
  · cbv
  · exact first_atom

private def rhoPartitionSource : Pattern :=
  .collection .hashBag [.apply "PZero" [], .apply "PZero" []] none

private def rhoPartitionRequest : Request :=
  GeneralRho.FrontierControls.literalRequest rhoPartitionSource

private def discoveredRhoPartition : State rhoPartitionRequest := run _ 1 (start _)

private theorem rho_partition_admitted : Admitted rhoPartitionRequest :=
  ⟨GeneralRho.FrontierControls.runtime_plan_actual.symm, rfl,
    checkOpenPatternWellSorted_sound (by cbv)⟩

private def rhoZeroValue : Pattern := .apply "PZero" []

private theorem rho_first_zero : readComponentFormula rhoPartitionRequest (.base "Proc")
    rhoZeroValue 1 (.root 0) = some true := by
  apply first_component_root (declaration := GeneralRho.language.terms[0]'(by decide))
    (arguments := [])
  · cbv
  · rfl
  · rfl
  · cbv

private theorem rho_discovered_cases : spatialCases rhoPartitionRequest discoveredRhoPartition =
    [⟨rhoPartitionSource, rhoZeroValue, rhoZeroValue⟩] := by
  have rootSame : rhoPartitionRequest.root = rhoPartitionSource := by
    simp [rhoPartitionRequest, GeneralRho.FrontierControls.literalRequest,
      Request.root, rhoPartitionSource, Pattern.eraseBinderMetadata]
  have represented : representedPatterns rhoPartitionRequest discoveredRhoPartition =
      [rhoPartitionSource] := by
    change representedPatterns rhoPartitionRequest (run _ 1 (start _)) = [rhoPartitionSource]
    rw [first_represented _ (checkOpenPatternWellSorted_complete rho_partition_admitted.rootSorted), rootSame]
  have zeroTyped : checkHasType rhoPartitionRequest.plan.snapshot.language
      rhoPartitionRequest.plan.snapshot.free rhoPartitionRequest.bound rhoZeroValue
      rhoPartitionRequest.expected = true := by cbv
  change checkHasType rhoPartitionRequest.plan.snapshot.language rhoPartitionRequest.plan.snapshot.free
    rhoPartitionRequest.bound (.apply "PZero" []) rhoPartitionRequest.expected = true at zeroTyped
  unfold spatialCases
  rw [represented]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, spatialCasesFrom, rhoPartitionSource]
  change (List.range 3).filterMap
    (spatialCase? rhoPartitionRequest discoveredRhoPartition [rhoZeroValue, rhoZeroValue]) = _
  rw [show List.range 3 = [0, 1, 2] from by decide]
  simp only [List.filterMap_cons, List.filterMap_nil, spatialCase?, represented]
  simp [spatialPart, rhoPartitionSource, rhoZeroValue, zeroTyped]

theorem rho_real_bag_partition_executes :
    readGeneratedFormula rhoPartitionRequest discoveredRhoPartition 1
      (.spatial 3 (.root 0) (.conj .top (.root 0))) = some true := by
  change readSpatialCases rhoPartitionRequest discoveredRhoPartition (.root 0)
    (.conj .top (.root 0)) 1 = some true
  unfold readSpatialCases spatialAnswers
  rw [rho_discovered_cases]
  have conjoint : readComponentFormula rhoPartitionRequest (.base "Proc") rhoZeroValue 1
      (.conj .top (.root 0)) = some true := by
    have zeroRead := rho_first_zero
    unfold readComponentFormula at zeroRead ⊢
    split at zeroRead
    · rename_i checked
      rw [if_pos checked]
      change readBinary Bool.and (some true)
        (readFrontierFormula (componentRequest rhoPartitionRequest (.base "Proc") rhoZeroValue)
          (componentState rhoPartitionRequest (.base "Proc") rhoZeroValue 1) (.root 0)) = some true
      rw [zeroRead]
      rfl
    · cases zeroRead
  simp only [List.map_cons, List.map_nil, show rhoPartitionRequest.expected = .base "Proc" from rfl,
    rho_first_zero, conjoint, readBinary, Bool.and_self, readExistential, List.any_cons,
    List.any_nil, beq_self_eq_true, Bool.or_false, if_true]

theorem rho_real_bag_partition_semantics :
    Holds GeneralRho.language GeneralRho.snapshot.free [] (frontierEquation rhoPartitionRequest)
      (fun _ _ _ => False) (.base "Proc") (.spatial 3 (.root 0) (.conj .top (.root 0)))
      rhoPartitionSource := by
  have result := (readGeneratedFormula_sound rho_partition_admitted (fun _ _ _ => False) 1
    (.spatial 3 (.root 0) (.conj .top (.root 0))) true rho_real_bag_partition_executes).mp rfl
  change Holds _ _ _ _ _ _ _ rhoPartitionSource.eraseBinderMetadata at result
  simpa [rhoPartitionRequest, GeneralRho.FrontierControls.literalRequest,
    GeneralRho.FrontierControls.runtimePlan,
    GeneralRho.snapshot, rhoPartitionSource, Pattern.eraseBinderMetadata] using result

theorem rho_spatial_false_without_coverage_unknown :
    readGeneratedFormula rhoPartitionRequest discoveredRhoPartition 0
      (.spatial 3 .top .bottom) = none := by
  change readSpatialCases rhoPartitionRequest discoveredRhoPartition .top .bottom 0 = none
  unfold readSpatialCases spatialAnswers
  rw [rho_discovered_cases]
  have unfinished := first_unfinished rhoPartitionRequest
    (checkOpenPatternWellSorted_complete rho_partition_admitted.rootSorted)
  have rejected := unfinished_certificate_rejected rhoPartitionRequest discoveredRhoPartition unfinished
  have component : readBinary Bool.and
      (readComponentFormula rhoPartitionRequest rhoPartitionRequest.expected rhoZeroValue 0 .top)
      (readComponentFormula rhoPartitionRequest rhoPartitionRequest.expected rhoZeroValue 0 .bottom) =
      some false := by cbv
  simp only [List.map_cons, List.map_nil, component, readExistential, List.any_cons,
    List.any_nil, Bool.or_false, rejected, Bool.false_and]
  rfl

theorem modal_component_not_fabricated :
    readGeneratedFormula rhoPartitionRequest discoveredRhoPartition 1
      (.spatial 3 .top (.atom 0)) = none := by
  change readSpatialCases rhoPartitionRequest discoveredRhoPartition .top (.atom 0) 1 = none
  unfold readSpatialCases spatialAnswers
  rw [rho_discovered_cases]
  have unfinished := first_unfinished rhoPartitionRequest
    (checkOpenPatternWellSorted_complete rho_partition_admitted.rootSorted)
  have rejected := unfinished_certificate_rejected rhoPartitionRequest discoveredRhoPartition unfinished
  have component : readBinary Bool.and
      (readComponentFormula rhoPartitionRequest rhoPartitionRequest.expected rhoZeroValue 1 .top)
      (readComponentFormula rhoPartitionRequest rhoPartitionRequest.expected rhoZeroValue 1 (.atom 0)) =
      none := by cbv
  simp only [List.map_cons, List.map_nil, component, readExistential, List.any_cons,
    List.any_nil, Bool.or_false, rejected, Bool.false_and]
  rfl

end Mettapedia.OSLF.NativeTypes.Structural.Controls
