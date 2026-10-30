import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenApplication

/-! # Open rule programs with ordered premise occurrences -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

def a : Pattern := .apply "A" []
def b : Pattern := .apply "B" []
def c : Pattern := .apply "C" []

def ab : RuleSchema := ⟨⟨"ab"⟩, [], [a], b, []⟩
def bc : RuleSchema := ⟨⟨"bc"⟩, [], [b], c, []⟩
def combine : RuleSchema := ⟨⟨"combine"⟩, [], [a, b], c, []⟩

def presentation : CalculusLanguageDef :=
  CalculusLanguageDef.extend (LanguageDef.empty "open-rule-programs")
    { judgments := [⟨"A", 0⟩, ⟨"B", 0⟩, ⟨"C", 0⟩]
      rules := [ab, bc, combine] }

private theorem empty_valid (name : String) : (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

theorem presentation_valid : presentation.isValid = true := by
  simp [presentation, CalculusLanguageDef.extend, CalculusLanguageDef.isValid,
    CalculusLanguageDef.judgmentSignatureValid, CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.hasValidLocalRules, CalculusLanguageDef.ruleIds, empty_valid,
    ab, bc, combine, a, b, c, RuleSchema.isValidIn,
    CalculusLanguageDef.judgmentSchemaValid, CalculusLanguageDef.lookupJudgment?,
    fixedConstructorListsValid, RuleSchema.isLocallyValid, RuleSchema.metavariableNames,
    RuleSchema.occurrences, RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, patternHasNoCollectionRest,
    patternsHaveNoCollectionRest, Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
  decide

def definition : ValidatedCalculusLanguageDef := ⟨presentation, presentation_valid⟩

def abProgram : RawOpenProof := .node ⟨⟨"ab"⟩, []⟩ [.premise 0]
def bcProgram : RawOpenProof := .node ⟨⟨"bc"⟩, []⟩ [.premise 0]
def combined : RawOpenProof := .node ⟨⟨"combine"⟩, []⟩ [.premise 0, .premise 1]
def composite : RawOpenProof := bcProgram.substitute [abProgram]

theorem ab_checks : checkOpenRaw definition [a] b abProgram = true := by decide +kernel
theorem bc_checks : checkOpenRaw definition [b] c bcProgram = true := by decide +kernel

theorem composite_checks : checkOpenRaw definition [a] c composite = true :=
  checkOpenRaw_substitute bc_checks (by simpa [checkOpenRawChildren] using ab_checks)

theorem composite_exact :
    applyOpen? definition [b] [a] c bcProgram [abProgram] = some composite :=
  applyOpen?_eq_some_iff.mpr ⟨bc_checks,
    by simpa [checkOpenRawChildren] using ab_checks, rfl⟩

/-- A rule that returns its first premise still requires the complete
declared argument vector. -/
theorem unused_argument_required :
    applyOpen? definition [a, b] [a] a (.premise 0) [.premise 0] = none := by decide +kernel

theorem extra_argument_refused :
    applyOpen? definition [a] [a] a (.premise 0) [.premise 0, .premise 0] = none := by decide +kernel

theorem distinct_equal_premises :
    applyOpen? definition [a] [a, a] a (.premise 0) [.premise 0] ≠
      applyOpen? definition [a] [a, a] a (.premise 0) [.premise 1] := by
  simp [applyOpen?, checkOpenRaw, checkOpenRawChildren,
    RawOpenProof.substitute, List.getD]

theorem composite_count : composite.ruleCount = 2 := by
  simp [composite, bcProgram, abProgram, RawOpenProof.substitute,
    RawOpenProof.substituteList, List.getD, RawOpenProof.ruleCount_node,
    RawOpenProof.ruleCount]

def controls : List (String × Bool) := [
  ("open rule accepted", checkOpenRaw definition [a] b abProgram),
  ("application accepted", (applyOpen? definition [b] [a] c bcProgram [abProgram]).isSome),
  ("composite proof accepted", checkOpenRaw definition [a] c composite),
  ("missing unused argument refused", (applyOpen? definition [a, b] [a] a (.premise 0) [.premise 0]).isNone),
  ("extra argument refused", (applyOpen? definition [a] [a] a (.premise 0) [.premise 0, .premise 0]).isNone),
  ("wrong premise refused", (applyOpen? definition [b] [a] c bcProgram [.premise 0]).isNone),
  ("swapped premise positions refused", (applyOpen? definition [a, b] [a, b] c combined [.premise 1, .premise 0]).isNone),
  ("correct premise positions accepted", (applyOpen? definition [a, b] [a, b] c combined [.premise 0, .premise 1]).isSome),
  ("out of range premise refused", !(checkOpenRaw definition [a] a (.premise 1))),
  ("forged conclusion refused", !(checkOpenRaw definition [a] c abProgram)),
  ("unknown rule refused", !(checkOpenRaw definition [a] a (.node ⟨⟨"unknown"⟩, []⟩ []))),
  ("composition retains both rule occurrences", composite.ruleCount == 2)]

theorem controls_pass : controls.all Prod.snd = true := by
  simp only [controls, composite_count]
  decide +kernel

#eval controls
#print axioms presentation_valid
#print axioms composite_checks
#print axioms composite_exact
#print axioms unused_argument_required
#print axioms extra_argument_refused
#print axioms distinct_equal_premises
#print axioms controls_pass

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls
