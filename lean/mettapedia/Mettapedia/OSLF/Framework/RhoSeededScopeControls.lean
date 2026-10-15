import Mettapedia.OSLF.Framework.RhoSeededScopeAdmission
import Mettapedia.OSLF.Framework.RhoCanonicalPairSubstitution

/-!
# Positive and separating controls for actual seeded rho scopes

Atomic seeds, unordered pairs and repeated children exercise the actual source
quotient. Input names and a different output name lie outside this scope even
though they are legitimate rho names. Ordered derivation receipts remain
distinct when commutativity identifies their name readouts. The displayed
atomic-part generator retains its previously proved different base stage.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoSeededScopeControls

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoCanonicalNamePairs
open RhoSchema.IntrinsicEncoding RhoIntrinsicReadback
open MeTTaIL.Syntax
open RhoSeededScopeStages RhoSeededScopeInterpretation RhoSeededScopeParser RhoSeededScopeReceipts

def nullName : Name [] := quote (zero [])
def outputName : Name [] := quote visible
def mixedName : Name [] := combine nullName outputName
def repeatedName : Name [] := combine nullName nullName

theorem mixed_depth : depth (encodeEquationClass mixedName) = some 1 :=
  depth_combine_some depth_null_seed depth_output_seed

theorem repeated_depth : depth (encodeEquationClass repeatedName) = some 1 :=
  depth_combine_some depth_null_seed depth_null_seed

theorem mixed_and_repeated_differ : mixedName ≠ repeatedName := by
  intro same
  rcases (combine_equality_iff nullName outputName nullName nullName).mp same with direct | swapped
  · exact RhoScopeSeedReadings.seed_names_distinct direct.2.symm
  · exact RhoScopeSeedReadings.seed_names_distinct swapped.2.symm

theorem mixed_not_atomic : mixedName ∉ stage 0 := by
  rw [depth_is_minimum mixed_depth]
  exact Nat.not_succ_le_zero 0

theorem repeated_member : repeatedName ∈ stage 1 := class_depth_sound repeated_depth

def leftReceipt : Receipt mixedName := ⟨.pair .nullSeed .outputSeed, rfl⟩
def rightReceipt : Receipt mixedName :=
  ⟨.pair .outputSeed .nullSeed, ordered_pair_readouts_agree.symm⟩

theorem same_readout_distinct_receipts : leftReceipt ≠ rightReceipt := by
  intro same
  exact ordered_pair_derivations_differ (congrArg Subtype.val same)

theorem actual_authored_readout :
    (authoredReceipt mixedName leftReceipt).val.val = encodeEquationClass mixedName :=
  authoredReceipt_pattern mixedName leftReceipt

def inputName : Name [] :=
  quote (project (inputRaw (quoteRaw null) (null : Term sig [Srt.nm] Srt.pr)))

theorem input_depth_absent : depth (encodeEquationClass inputName) = none := by
  change depth (.apply "NQuote" [.apply "PInput"
    [.apply "NQuote" [.apply "PZero" []], .lambda none (.apply "PZero" [])]]) = none
  rw [depth] <;> simp

theorem input_not_in_scope : ¬ finiteScope inputName := (depth_none_iff _).mp input_depth_absent

theorem excluded_input_is_admitted_name : HasQuoteSafeRepresentative inputName :=
  ⟨quoteRaw (inputRaw (quoteRaw null) (null : Term sig [Srt.nm] Srt.pr)), rfl, rfl⟩

theorem input_has_no_receipt : receipt? inputName = none := (receipt?_none_iff _).mpr input_not_in_scope

def otherOutputName : Name [] := quote (outputClass nullName visible)

theorem other_output_depth_absent : depth (encodeEquationClass otherOutputName) = none := by
  change depth (.apply "NQuote" [.apply "POutput"
    [.apply "NQuote" [.apply "PZero" []], .apply "POutput"
      [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []]]]) = none
  rw [depth] <;> simp

theorem other_output_not_in_scope : ¬ finiteScope otherOutputName :=
  (depth_none_iff _).mp other_output_depth_absent

theorem actual_seeded_base_two_displayed_base_one :
    (stage 0).card = 2 ∧
      Nat.card {name : Name [] // RhoGeneratedScopeStrata.Bounded
        RhoScopeSeedReadings.leftAtom RhoScopeSeedReadings.rightAtom 0 name} = 1 :=
  ⟨stage_zero_card, RhoScopeSeedReadings.displayed_zero_stage_cardinality⟩

end Mettapedia.OSLF.Framework.RhoSeededScopeControls
