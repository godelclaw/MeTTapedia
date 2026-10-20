import Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable
import Mettapedia.GSLT.LanguageDef.SemanticSettings

/-!
# The PLN evidence calculus as a coGSLT module

This module presents the judgment and rule structure of the PLN spine as a
calculus language definition, renders it as portable module text and reads it
back through the verified module reader.

The calculus distinguishes the semantic settings of its judgments:

- `ObservationCounts` and `ObservationLowerBound` retain identified observations;
- `SampleCounts` records paired samples; `ReportLikelihoods` records likelihoods;
- `CountReadout` and `PopulationReadout` retain their distinct value meanings;
- each setting has its own contract judgment.

Exact evidence and under-counts are different judgments because the readouts
need exact counts: an under-count can have any strength.

Each rule names the spine theorem that justifies it:

| Rule | Contract premise | Lean theorem |
|---|---|---|
| `revise` | `disjoint e₁ e₂` | `EvidenceContracts.additive_revision_exact_iff_disjoint` |
| `revise-unknown-overlap` | none; concludes `ObservationLowerBound` | `EvidenceContracts.unknown_overlap_bounds` |
| `negate` | none | `EvidenceContracts.against_add` (negation is presence) |
| `fuse` | `reports q e₁ e₂` (reports on `q`, independent given `q`) | `EvidenceContracts.strength_fuse_uniform` |
| `conjoin-independent` | `independent a b` | `EvidenceSpaces.strength_mul` |
| `conjoin-one-world` | `oneWorld e₁ e₂` (same observations) | `EvidenceContracts.conjunction_counts_iff` |
| `deduce` | `screens a b c` | `PLNDerivation.pln_deduction_from_total_probability` |
| `read-strength` | none | `BinaryEvidence.toStrength` |
| `read-interval` | none | `WalleyBinaryIDM.credal_envelope_matches_Walley_ITV_bounds` |

What the module format carries, and what it does not:

- It carries the judgment forms, the rule schemas and, as ordinary premises,
  the contract each rule needs.  `rules_with_two_evidence_premises_have_contracts`
  checks that discipline on the module data.
- It does not check a contract.  Rule side conditions in the format are
  syntactic (substitution, binder removal); disjointness of ledgers,
  conditional independence and screening off are properties of the observed
  worlds.  A setting-specific contract judgment therefore enters a derivation as an assumption
  supplied from outside the calculus.  What a contract means is fixed by a
  semantics of the judgments: `EvidenceCalculusSemantics` interprets the
  revision fragment over identified observations and proves the `revise`
  schema of this module sound with its contract and unsound without it, and
  gives every other rule its semantics in the same way.
- It does not compute counts or readouts.  Terms are first-order syntax; the
  value of `strength e` or `deduction s₁ s₂ s₃ s₄` is computed by the Lean
  definitions the table names.
- It cannot state a counterexample.  A calculus of derivable judgments has no
  way to say that a rule fails without its contract; those statements stay in
  Lean (`EvidenceContracts.Controls`).
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.FirstOrderCalculus

/-- Counts, report likelihoods and their readouts have distinct sorts.
The same pair of numbers does not identify their semantic interpretation. -/
def evidenceTerms : List GrammarRule :=
  [ term "and" "Query" [("left", "Query"), ("right", "Query")],
    term "probability" "PopulationRequest" [("query", "Query")],
    term "conditional" "PopulationRequest" [("source", "Query"), ("target", "Query")],
    term "not" "Query" [("query", "Query")],
    term "revise" "ObservationCounts" [("first", "ObservationCounts"), ("second", "ObservationCounts")],
    term "lowerMerge" "ObservationCounts" [("first", "ObservationCounts"), ("second", "ObservationCounts")],
    term "swap" "ObservationCounts" [("counts", "ObservationCounts")],
    term "fuse" "ReportLikelihoods" [("first", "ReportLikelihoods"), ("second", "ReportLikelihoods")],
    term "pair" "SampleCounts" [("first", "SampleCounts"), ("second", "SampleCounts")],
    term "disjoint" "LedgerContract" [("first", "ObservationCounts"), ("second", "ObservationCounts")],
    term "reports" "ReportContract" [("hypothesis", "Query"), ("first", "ReportLikelihoods"),
      ("second", "ReportLikelihoods")],
    term "independent" "SampleContract" [("left", "Query"), ("right", "Query")],
    term "oneWorld" "LedgerContract" [("first", "ObservationCounts"), ("second", "ObservationCounts")],
    term "screens" "PopulationContract" [("source", "Query"), ("middle", "Query"),
      ("target", "Query")],
    term "strength" "CountValue" [("counts", "ObservationCounts")],
    term "interval" "CountValue" [("counts", "ObservationCounts")],
    term "frechet" "CountValue" [("first", "ObservationCounts"), ("second", "ObservationCounts")],
    term "deduction" "PopulationValue" [("sourceMiddle", "PopulationValue"),
      ("middleTarget", "PopulationValue"), ("middle", "PopulationValue"),
      ("target", "PopulationValue")] ]

/-- Exact counts over retained observation identities. -/
def observationCounts (q e : Pattern) : Pattern := app "ObservationCounts" [q, e]
/-- A coordinate-wise lower bound on observation counts. -/
def observationLowerBound (q e : Pattern) : Pattern := app "ObservationLowerBound" [q, e]
/-- Counts of separately drawn samples and their paired products. -/
def sampleCounts (q e : Pattern) : Pattern := app "SampleCounts" [q, e]
/-- Likelihoods of a report under a hypothesis and its negation. -/
def reportLikelihoods (q e : Pattern) : Pattern := app "ReportLikelihoods" [q, e]
/-- Disjointness or common-population contracts on identified observations. -/
def ledgerHolds (c : Pattern) : Pattern := app "LedgerHolds" [c]
/-- The separability contract of paired sample construction. -/
def sampleHolds (c : Pattern) : Pattern := app "SampleHolds" [c]
/-- Conditional-independence contracts on reports. -/
def reportHolds (c : Pattern) : Pattern := app "ReportHolds" [c]
/-- Screening contracts on one population. -/
def populationHolds (c : Pattern) : Pattern := app "PopulationHolds" [c]
/-- A readout carrying the observation scope on which it is based. -/
def countReadout (q v : Pattern) : Pattern := app "CountReadout" [q, v]
/-- A marginal or conditional request in one population, with its readout. -/
def populationReadout (request v : Pattern) : Pattern := app "PopulationReadout" [request, v]

/-- The rules of the spine, each with its observation contract as a premise. -/
def evidenceRules : List RuleSchema :=
  [ rule "revise" ["q", "e1", "e2"]
      [observationCounts (fv "q") (fv "e1"), observationCounts (fv "q") (fv "e2"),
        ledgerHolds (app "disjoint" [fv "e1", fv "e2"])]
      (observationCounts (fv "q") (app "revise" [fv "e1", fv "e2"])),
    rule "revise-unknown-overlap" ["q", "e1", "e2"]
      [observationCounts (fv "q") (fv "e1"), observationCounts (fv "q") (fv "e2")]
      (observationLowerBound (fv "q") (app "lowerMerge" [fv "e1", fv "e2"])),
    rule "negate" ["q", "e"]
      [observationCounts (fv "q") (fv "e")]
      (observationCounts (app "not" [fv "q"]) (app "swap" [fv "e"])),
    rule "fuse" ["q", "e1", "e2"]
      [reportLikelihoods (fv "q") (fv "e1"), reportLikelihoods (fv "q") (fv "e2"),
        reportHolds (app "reports" [fv "q", fv "e1", fv "e2"])]
      (reportLikelihoods (fv "q") (app "fuse" [fv "e1", fv "e2"])),
    rule "conjoin-independent" ["a", "b", "e1", "e2"]
      [sampleCounts (fv "a") (fv "e1"), sampleCounts (fv "b") (fv "e2"),
        sampleHolds (app "independent" [fv "a", fv "b"])]
      (sampleCounts (app "and" [fv "a", fv "b"]) (app "pair" [fv "e1", fv "e2"])),
    rule "conjoin-one-world" ["a", "b", "e1", "e2"]
      [observationCounts (fv "a") (fv "e1"), observationCounts (fv "b") (fv "e2"),
        ledgerHolds (app "oneWorld" [fv "e1", fv "e2"])]
      (countReadout (app "and" [fv "a", fv "b"]) (app "frechet" [fv "e1", fv "e2"])),
    rule "deduce" ["a", "b", "c", "s1", "s2", "s3", "s4"]
      [populationReadout (app "conditional" [fv "a", fv "b"]) (fv "s1"),
        populationReadout (app "conditional" [fv "b", fv "c"]) (fv "s2"),
        populationReadout (app "probability" [fv "b"]) (fv "s3"), populationReadout (app "probability" [fv "c"]) (fv "s4"),
        populationHolds (app "screens" [fv "a", fv "b", fv "c"])]
      (populationReadout (app "conditional" [fv "a", fv "c"])
        (app "deduction" [fv "s1", fv "s2", fv "s3", fv "s4"])),
    rule "read-strength" ["q", "e"]
      [observationCounts (fv "q") (fv "e")]
      (countReadout (fv "q") (app "strength" [fv "e"])),
    rule "read-interval" ["q", "e"]
      [observationCounts (fv "q") (fv "e")]
      (countReadout (fv "q") (app "interval" [fv "e"])) ]

/-- The PLN evidence calculus: one flat calculus language definition. -/
def evidenceCalculus : CalculusLanguageDef where
  name := "pln-evidence-calculus"
  types := ["Query", "ObservationCounts", "SampleCounts", "ReportLikelihoods",
    "LedgerContract", "SampleContract", "ReportContract", "PopulationContract",
    "CountValue", "PopulationValue", "PopulationRequest"].map TypeDecl.plain
  terms := evidenceTerms
  equations := []
  rewrites := []
  judgments := [{ head := "ObservationCounts", arity := 2 },
    { head := "ObservationLowerBound", arity := 2 }, { head := "SampleCounts", arity := 2 },
    { head := "ReportLikelihoods", arity := 2 }, { head := "LedgerHolds", arity := 1 },
    { head := "SampleHolds", arity := 1 }, { head := "ReportHolds", arity := 1 },
    { head := "PopulationHolds", arity := 1 }, { head := "CountReadout", arity := 2 },
    { head := "PopulationReadout", arity := 2 }]
  rules := evidenceRules

theorem evidenceCalculus_admitted : evidenceCalculus.isAdmitted = true := by
  have validate : evidenceCalculus.toLanguageDef.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [evidenceCalculus, evidenceTerms, term, LanguageDef.typeNames,
        TypeDecl.plain, TermParam.typeExpr, TypeExpr.baseNames]
  unfold isAdmitted CalculusLanguageDef.isValid
    CalculusLanguageDef.hasValidLocalRules
  rw [validate]
  simp [evidenceCalculus, evidenceTerms, evidenceRules, term, rule, observationCounts, observationLowerBound, sampleCounts, reportLikelihoods,
    ledgerHolds, sampleHolds, reportHolds, populationHolds, countReadout, populationReadout,
    fv, app,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads,
    CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
    Pattern.zipHead, Pattern.mapHead, Pattern.evalHead]
  decide

/-- The admitted calculus, as consumed by the checker. -/
def evidenceCalculusValidated : ValidatedCalculusLanguageDef :=
  evidenceCalculus.validated evidenceCalculus_admitted

/-- Its portable module text, produced by the verified renderer. -/
def evidenceCalculusModule : String :=
  ModuleFormat.Portable.renderCalculus evidenceCalculusValidated.val

/-- Reading the module text through the verified reader and the original
validator returns exactly the admitted calculus. -/
theorem evidenceCalculusModule_read :
    ModuleFormat.Portable.readValidatedCalculus? evidenceCalculusModule =
      some evidenceCalculusValidated :=
  ModuleFormat.Portable.readValidatedCalculus_renderCalculus _

/-- Whether a rule premise is an evidence judgment. -/
def isSummaryPremise : Pattern → Bool
  | .apply "ObservationCounts" _ | .apply "SampleCounts" _ | .apply "ReportLikelihoods" _ => true
  | _ => false

/-- Whether a rule premise is a contract judgment. -/
def isContractPremise : Pattern → Bool
  | .apply "LedgerHolds" _ | .apply "SampleHolds" _ | .apply "ReportHolds" _ |
      .apply "PopulationHolds" _ => true
  | _ => false

/-- Contract discipline on the module data: every rule that combines two bodies
of evidence has a contract premise, except the unknown-overlap revision, whose
conclusion is an under-count and needs none. -/
theorem rules_with_two_evidence_premises_have_contracts :
    ∀ r ∈ evidenceCalculus.rules,
      r.premises.countP isSummaryPremise = 2 → r.id.value ≠ "revise-unknown-overlap" →
        r.premises.any isContractPremise = true := by
  decide

/-- The discipline is not vacuous: dropping the contract premise of `revise`
breaks it. -/
theorem revise_without_contract_violates :
    ¬ ∀ r ∈ (rule "revise" ["q", "e1", "e2"]
        [observationCounts (fv "q") (fv "e1"), observationCounts (fv "q") (fv "e2")]
        (observationCounts (fv "q") (app "revise" [fv "e1", fv "e2"])) :: evidenceRules.tail),
      r.premises.countP isSummaryPremise = 2 → r.id.value ≠ "revise-unknown-overlap" →
        r.premises.any isContractPremise = true := by
  decide

/-- The semantic settings deliberately distinguish the two count populations
as well as likelihood and readout meanings. -/
inductive SemanticSetting where
  | ledger | samples | reports | population
  deriving DecidableEq, Repr

def settingOf : Pattern → Option SemanticSetting
  | .apply "ObservationCounts" _ | .apply "ObservationLowerBound" _ |
      .apply "LedgerHolds" _ | .apply "CountReadout" _ => some .ledger
  | .apply "SampleCounts" _ | .apply "SampleHolds" _ => some .samples
  | .apply "ReportLikelihoods" _ | .apply "ReportHolds" _ => some .reports
  | .apply "PopulationReadout" _ | .apply "PopulationHolds" _ => some .population
  | _ => none

/-- Every actual schema in the portable module remains within its declared
interpretation. Cross-setting conversions require their own bridge rules. -/
theorem evidenceRules_homogeneous :
    ∀ schema ∈ evidenceCalculus.rules,
      SemanticSettings.homogeneous? settingOf schema = true := by decide

/-- A report fusion fed observation counts violates the setting discipline,
even though both summaries happen to have two coordinates. -/
theorem count_likelihood_mix_not_homogeneous :
    SemanticSettings.homogeneous? settingOf
      (rule "mixed-fusion" ["q", "e1", "e2"]
        [observationCounts (fv "q") (fv "e1"), observationCounts (fv "q") (fv "e2")]
        (reportLikelihoods (fv "q") (app "fuse" [fv "e1", fv "e2"]))) = false := by decide

end Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule
