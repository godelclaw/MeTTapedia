import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllResultUniverseEvidence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllResultUniverseComputation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllResultsChecking

/-!
# Checked independent caller universes for native Vector results

The complete finite certificate is replayed against the actual program and
its independently bounded function type. The same certificate is refused
under the original native All profile. This is a certificate-refusal control,
not a completeness or non-derivability theorem for that original calculus.
The original two-position input control also has transported typing and
computation. Its conversion code is checked by the enlarged profile, including
refusal when the proposed output swaps the independent witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ResultView.Universes

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open RussellTarski TypedEquality.Normalization NativeNaturalVectorFamilies
open NativeVectorAll.CanonicalAdequacy

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

set_option maxRecDepth 8192 in
theorem replay_checked : FormationSensitiveElaboration.replay rules decoder
    .nil program programType Evidence.submission = true := by
  decide +kernel

theorem program_formed : FormationSensitive.Judgment rules .nil program programType :=
  FormationSensitiveElaboration.replay_sound rules decoder replay_checked

local instance : DecidableRel NativeVectorAll.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred NativeVectorAll.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (NativeVectorAll.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel NativeVectorAll.rules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel NativeVectorAll.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

set_option maxRecDepth 8192 in
theorem original_certificate_refused : FormationSensitiveElaboration.replay
    NativeVectorAll.rules NativeVectorAll.decoder .nil program programType
    Evidence.submission = false := by
  decide +kernel

theorem qualified_profile : signature.Formed Tower.rules ∧
    FormationSensitive.Judgment rules .nil program programType :=
  ⟨signature_formed, program_formed⟩

theorem mapped_input_formed : FormationSensitive.Judgment rules
    (substLevelsCtx programLevels ResultView.proofContext)
    (substLevelsTm programLevels ResultView.independentBundle)
    (substLevelsTm programLevels ResultView.independentType) :=
  judgment_map ResultView.independent_formed

def mappedIndependentRun : Tower.Tm 3 :=
  appSpine (liftClosed program)
    [substLevelsTm programLevels natTm, substLevelsTm programLevels unitType,
     substLevelsTm programLevels (numeral ResultView.repeatedValues.length),
     substLevelsTm programLevels (encodeVector natTm ResultView.repeatedValues),
     substLevelsTm programLevels ResultView.independentBundle]

def mappedIndependentResult : Tower.Tm 3 :=
  substLevelsTm programLevels ResultView.independentResult

theorem mapped_independent_steps :
    TypedEquality.Reduces rules mappedIndependentRun mappedIndependentResult :=
  program_computes_mapped_witnesses natTm unitType ResultView.repeatedValues
    ResultView.independentWitnesses (.var 2) rfl

def mappedSwappedResult : Tower.Tm 3 :=
  substLevelsTm programLevels (encodeVector unitType [.var 1, .var 0])

def mappedConversionCode : Option (StructuralConversionCode.Code Tower.Head decoder.Code 3) :=
  NativeVectorAll.choices.conversion 64 mappedIndependentRun mappedIndependentResult

def mappedResultCheck (code : StructuralConversionCode.Code Tower.Head decoder.Code 3) : Bool :=
  code.check rules.headEq decoder.decode mappedIndependentRun mappedIndependentResult

def mappedSwappedCheck (code : StructuralConversionCode.Code Tower.Head decoder.Code 3) : Bool :=
  code.check rules.headEq decoder.decode mappedIndependentRun mappedSwappedResult

def mappedConversionAccepted : Bool := mappedConversionCode.any mappedResultCheck

def mappedSwappedRefused : Bool := mappedConversionCode.any (fun code => !(mappedSwappedCheck code))

set_option maxRecDepth 8192 in
theorem mapped_conversion_accepted : mappedConversionCode.any mappedResultCheck = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem mapped_swapped_refused :
    mappedConversionCode.any (fun code => !(mappedSwappedCheck code)) = true := by
  decide +kernel

private theorem checked_code_witness {Code : Type} (candidate : Option Code)
    (check changed : Code → Bool)
    (accepted : candidate.any check = true)
    (refused : candidate.any (fun code => !(changed code)) = true) :
    ∃ code, candidate = some code ∧ check code = true ∧ changed code = false := by
  cases candidate with
  | none => simp [Option.any] at accepted
  | some code =>
      simp only [Option.any] at accepted refused
      refine ⟨code, rfl, accepted, ?_⟩
      simpa using refused

theorem mapped_code_controls : ∃ code : StructuralConversionCode.Code Tower.Head decoder.Code 3,
    mappedConversionCode = some code ∧
    mappedResultCheck code = true ∧ mappedSwappedCheck code = false :=
  checked_code_witness (Code := StructuralConversionCode.Code Tower.Head decoder.Code 3) mappedConversionCode
    mappedResultCheck mappedSwappedCheck
    mapped_conversion_accepted mapped_swapped_refused

def annotationChanged : Bool := decide (program ≠ ResultView.program)

theorem annotation_changed : annotationChanged = true := by
  simpa only [annotationChanged, decide_eq_true_eq] using program_annotation_changes

def verdicts : List (String × Bool) :=
  [("Vector results check with independent caller universe bounds",
      FormationSensitiveElaboration.replay rules decoder .nil program programType Evidence.submission),
   ("the original Vector profile refuses the enlarged result certificate",
      !(FormationSensitiveElaboration.replay NativeVectorAll.rules NativeVectorAll.decoder
        .nil program programType Evidence.submission)),
   ("the enlarged Vector result program preserves independent witness order", mappedConversionAccepted),
   ("the same conversion code refuses swapped result witnesses", mappedSwappedRefused),
   ("the result program's universe annotation changes", annotationChanged)]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp [verdicts, replay_checked, original_certificate_refused, mappedConversionAccepted, mappedSwappedRefused,
    mapped_conversion_accepted, mapped_swapped_refused, annotation_changed]

#print axioms signature_formed
#print axioms program_formed
#print axioms original_certificate_refused
#print axioms mapped_input_formed
#print axioms mapped_independent_steps
#print axioms mapped_conversion_accepted
#print axioms mapped_swapped_refused
#print axioms mapped_code_controls

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ResultView.Universes
