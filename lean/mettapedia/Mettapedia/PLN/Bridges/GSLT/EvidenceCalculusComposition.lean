import Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusSemantics
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenChecker

/-!
# Combined settings and checked evidence-calculus proof templates

The nine schemas have one combined interpretation without identifying their
four model carriers. Open proof templates retain externally supplied contracts
and observations. The checker controls below distinguish legitimate chaining
from attempts to use likelihoods as counts or count readouts as frequencies.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusComposition

open Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SemanticSettings
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule
open Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusSemantics

def ModelAt : SemanticSetting → Type 1
  | .ledger => Ledger.Model
  | .samples => Paired.Model
  | .reports => Reports.Model
  | .population => Population.Model

def reading : (setting : SemanticSetting) → ModelAt setting → Pattern → Prop
  | .ledger => Ledger.Model.holds
  | .samples => Paired.Model.holds
  | .reports => Reports.Model.holds
  | .population => Population.Model.holds

/-- A model family keeps each setting's interpretation independent. -/
abbrev Model := (setting : SemanticSetting) → ModelAt setting

def meaning : Model → Pattern → Prop := combinedHolds settingOf reading

/-- Every actual source schema is sound in the combined interpretation.
The independent soundness theorem of its own setting supplies the meaning. -/
theorem schemas_sound : ∀ schema ∈ evidenceCalculus.rules, SchemaSound meaning schema := by
  intro schema member
  apply combine_schema_sound settingOf reading schema (evidenceRules_homogeneous schema member)
  intro setting declared
  simp only [evidenceCalculus, evidenceRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    cases setting <;>
      simp only [rule, observationCounts, observationLowerBound, sampleCounts, reportLikelihoods,
        countReadout, populationReadout, app, settingOf, Option.some.injEq, reduceCtorEq] at declared
  all_goals first
    | exact revise_sound _ (by simp [evidenceCalculus, evidenceRules]) rfl
    | exact reviseUnknownOverlap_sound _ (by simp [evidenceCalculus, evidenceRules]) rfl
    | exact negate_sound _ (by simp [evidenceCalculus, evidenceRules]) rfl
    | exact fuse_sound _ (by simp [evidenceCalculus, evidenceRules]) rfl
    | exact conjoinIndependent_sound _ (by simp [evidenceCalculus, evidenceRules]) rfl
    | exact conjoinOneWorld_sound _ (by simp [evidenceCalculus, evidenceRules]) rfl
    | exact deduce_sound _ (by simp [evidenceCalculus, evidenceRules]) rfl
    | exact readStrength_sound _ (by simp [evidenceCalculus, evidenceRules]) rfl
    | exact readInterval_sound _ (by simp [evidenceCalculus, evidenceRules]) rfl

namespace Controls

/-- Ground premise handles are supplied by the surrounding interpretation;
they are not free schema metavariables. -/
def q : Pattern := app "query-input" []
def first : Pattern := app "first-input" []
def second : Pattern := app "second-input" []
def merged : Pattern := app "revise" [first, second]
def fused : Pattern := app "fuse" [first, second]

def countContext : List Pattern :=
  [observationCounts q first, observationCounts q second,
    ledgerHolds (app "disjoint" [first, second])]

def reportContext : List Pattern :=
  [reportLikelihoods q first, reportLikelihoods q second,
    reportHolds (app "reports" [q, first, second])]

def reviseProof : RawOpenProof :=
  .node ⟨⟨"revise"⟩, [q, first, second]⟩ [.premise 0, .premise 1, .premise 2]

def reviseThenReadProof : RawOpenProof :=
  .node ⟨⟨"read-strength"⟩, [q, merged]⟩ [reviseProof]

def fuseProof : RawOpenProof :=
  .node ⟨⟨"fuse"⟩, [q, first, second]⟩ [.premise 0, .premise 1, .premise 2]

def fuseThenCountReadProof : RawOpenProof :=
  .node ⟨⟨"read-strength"⟩, [q, fused]⟩ [fuseProof]

theorem revision_then_read_checks :
    checkOpenRaw evidenceCalculusValidated countContext
      (countReadout q (app "strength" [merged])) reviseThenReadProof = true := by decide +kernel

theorem report_fusion_checks :
    checkOpenRaw evidenceCalculusValidated reportContext
      (reportLikelihoods q fused) fuseProof = true := by decide +kernel

theorem reports_cannot_be_pooled_as_counts :
    checkOpenRaw evidenceCalculusValidated reportContext
      (observationCounts q merged) reviseProof = false := by decide +kernel

theorem fused_likelihoods_cannot_feed_count_readout :
    checkOpenRaw evidenceCalculusValidated reportContext
      (countReadout q (app "strength" [fused])) fuseThenCountReadProof = false := by decide +kernel

theorem count_readout_is_not_population_readout :
    checkOpenRaw evidenceCalculusValidated countContext
      (populationReadout q (app "strength" [merged])) reviseThenReadProof = false := by decide +kernel

/-- A missing semantic contract is not manufactured by structural checking. -/
theorem revision_without_contract_does_not_check :
    checkOpenRaw evidenceCalculusValidated (countContext.take 2)
      (observationCounts q merged) reviseProof = false := by decide +kernel

end Controls

end Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusComposition
