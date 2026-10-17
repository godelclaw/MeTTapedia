import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable

/-!
# The PLN evidence calculus as a coGSLT module

This module presents the judgment and rule structure of the PLN spine as a
calculus language definition, renders it as portable module text and reads it
back through the verified module reader.

The calculus has three judgment forms:

- `Evidence q e`: the query `q` has the body of evidence `e`;
- `Holds c`: the observation contract `c` holds;
- `Reads q v`: the readout `v` is licensed for `q`.

Each rule names the spine theorem that justifies it:

| Rule | Contract premise | Lean theorem |
|---|---|---|
| `revise` | `disjoint e₁ e₂` | `EvidenceContracts.additive_revision_exact_iff_disjoint` |
| `revise-unknown-overlap` | none; gives the lower end | `EvidenceContracts.unknown_overlap_bounds` |
| `negate` | none | `EvidenceContracts.against_add` (negation is presence) |
| `fuse` | `reports e₁ e₂` (conditionally independent reports) | `EvidenceContracts.strength_fuse_uniform` |
| `conjoin-independent` | `independent a b` | `EvidenceSpaces.strength_mul` |
| `conjoin-one-world` | `oneWorld a b` | `EvidenceContracts.conjunction_counts_iff` |
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
  worlds.  A `Holds` judgment therefore enters a derivation as an assumption
  supplied from outside the calculus.  What a contract means is fixed by a
  semantics of the judgments: `EvidenceCalculusSemantics` interprets the
  revision fragment over identified observations and proves the `revise`
  schema of this module sound with its contract and unsound without it.
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

/-- A grammar rule with simple sorted parameters and no surface syntax. -/
def term (label category : String) (params : List (String × String)) :
    GrammarRule :=
  { label, category,
    params := params.map fun (name, sort) => TermParam.simple name (.base sort),
    syntaxPattern := [] }

/-- A metavariable pattern. -/
def fv (name : String) : Pattern := .fvar name

/-- A constructor or judgment application pattern. -/
def app (head : String) (args : List Pattern) : Pattern := .apply head args

/-- Queries, bodies of evidence, contracts and readout values, as syntax. -/
def evidenceTerms : List GrammarRule :=
  [ term "and" "Query" [("left", "Query"), ("right", "Query")],
    term "link" "Query" [("source", "Query"), ("target", "Query")],
    term "not" "Query" [("query", "Query")],
    term "revise" "Evidence" [("first", "Evidence"), ("second", "Evidence")],
    term "lowerMerge" "Evidence" [("first", "Evidence"), ("second", "Evidence")],
    term "swap" "Evidence" [("evidence", "Evidence")],
    term "fuse" "Evidence" [("first", "Evidence"), ("second", "Evidence")],
    term "pair" "Evidence" [("first", "Evidence"), ("second", "Evidence")],
    term "disjoint" "Contract" [("first", "Evidence"), ("second", "Evidence")],
    term "reports" "Contract" [("first", "Evidence"), ("second", "Evidence")],
    term "independent" "Contract" [("left", "Query"), ("right", "Query")],
    term "oneWorld" "Contract" [("left", "Query"), ("right", "Query")],
    term "screens" "Contract" [("source", "Query"), ("middle", "Query"),
      ("target", "Query")],
    term "strength" "Value" [("evidence", "Evidence")],
    term "interval" "Value" [("evidence", "Evidence")],
    term "frechet" "Value" [("first", "Evidence"), ("second", "Evidence")],
    term "deduction" "Value" [("sourceMiddle", "Value"), ("middleTarget", "Value"),
      ("middle", "Value"), ("target", "Value")] ]

/-- The evidence judgment `Evidence q e`. -/
def ev (q e : Pattern) : Pattern := app "Evidence" [q, e]
/-- The contract judgment `Holds c`. -/
def holds (c : Pattern) : Pattern := app "Holds" [c]
/-- The readout judgment `Reads q v`. -/
def reads (q v : Pattern) : Pattern := app "Reads" [q, v]

/-- A rule schema whose metavariables all live at depth zero. -/
def rule (id : String) (vars : List String) (premises : List Pattern)
    (conclusion : Pattern) : RuleSchema :=
  { id := ⟨id⟩, metavariables := vars.map (·, 0), premises, conclusion }

/-- The rules of the spine, each with its observation contract as a premise. -/
def evidenceRules : List RuleSchema :=
  [ rule "revise" ["q", "e1", "e2"]
      [ev (fv "q") (fv "e1"), ev (fv "q") (fv "e2"),
        holds (app "disjoint" [fv "e1", fv "e2"])]
      (ev (fv "q") (app "revise" [fv "e1", fv "e2"])),
    rule "revise-unknown-overlap" ["q", "e1", "e2"]
      [ev (fv "q") (fv "e1"), ev (fv "q") (fv "e2")]
      (ev (fv "q") (app "lowerMerge" [fv "e1", fv "e2"])),
    rule "negate" ["q", "e"]
      [ev (fv "q") (fv "e")]
      (ev (app "not" [fv "q"]) (app "swap" [fv "e"])),
    rule "fuse" ["q", "e1", "e2"]
      [ev (fv "q") (fv "e1"), ev (fv "q") (fv "e2"),
        holds (app "reports" [fv "e1", fv "e2"])]
      (ev (fv "q") (app "fuse" [fv "e1", fv "e2"])),
    rule "conjoin-independent" ["a", "b", "e1", "e2"]
      [ev (fv "a") (fv "e1"), ev (fv "b") (fv "e2"),
        holds (app "independent" [fv "a", fv "b"])]
      (ev (app "and" [fv "a", fv "b"]) (app "pair" [fv "e1", fv "e2"])),
    rule "conjoin-one-world" ["a", "b", "e1", "e2"]
      [ev (fv "a") (fv "e1"), ev (fv "b") (fv "e2"),
        holds (app "oneWorld" [fv "a", fv "b"])]
      (reads (app "and" [fv "a", fv "b"]) (app "frechet" [fv "e1", fv "e2"])),
    rule "deduce" ["a", "b", "c", "s1", "s2", "s3", "s4"]
      [reads (app "link" [fv "a", fv "b"]) (fv "s1"),
        reads (app "link" [fv "b", fv "c"]) (fv "s2"),
        reads (fv "b") (fv "s3"), reads (fv "c") (fv "s4"),
        holds (app "screens" [fv "a", fv "b", fv "c"])]
      (reads (app "link" [fv "a", fv "c"])
        (app "deduction" [fv "s1", fv "s2", fv "s3", fv "s4"])),
    rule "read-strength" ["q", "e"]
      [ev (fv "q") (fv "e")]
      (reads (fv "q") (app "strength" [fv "e"])),
    rule "read-interval" ["q", "e"]
      [ev (fv "q") (fv "e")]
      (reads (fv "q") (app "interval" [fv "e"])) ]

/-- The PLN evidence calculus: one flat calculus language definition. -/
def evidenceCalculus : CalculusLanguageDef where
  name := "pln-evidence-calculus"
  types := [TypeDecl.plain "Query", TypeDecl.plain "Evidence",
    TypeDecl.plain "Contract", TypeDecl.plain "Value"]
  terms := evidenceTerms
  equations := []
  rewrites := []
  judgments := [{ head := "Evidence", arity := 2 }, { head := "Holds", arity := 1 },
    { head := "Reads", arity := 2 }]
  rules := evidenceRules

theorem evidenceCalculus_admitted : evidenceCalculus.isAdmitted = true := by
  have validate : evidenceCalculus.toLanguageDef.validate = [] := by
    apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
      simp [evidenceCalculus, evidenceTerms, term, LanguageDef.typeNames,
        TypeDecl.plain, TermParam.typeExpr, TypeExpr.baseNames]
  unfold isAdmitted CalculusLanguageDef.isValid
    CalculusLanguageDef.hasValidLocalRules
  rw [validate]
  simp [evidenceCalculus, evidenceTerms, evidenceRules, term, rule, ev, holds, reads,
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
def isEvidencePremise : Pattern → Bool
  | .apply "Evidence" _ => true
  | _ => false

/-- Whether a rule premise is a contract judgment. -/
def isContractPremise : Pattern → Bool
  | .apply "Holds" _ => true
  | _ => false

/-- Contract discipline on the module data: every rule that combines two bodies
of evidence has a contract premise, except the unknown-overlap revision, whose
conclusion is the conservative lower end and needs none. -/
theorem rules_with_two_evidence_premises_have_contracts :
    ∀ r ∈ evidenceCalculus.rules,
      r.premises.countP isEvidencePremise = 2 → r.id.value ≠ "revise-unknown-overlap" →
        r.premises.any isContractPremise = true := by
  decide

/-- The discipline is not vacuous: dropping the contract premise of `revise`
breaks it. -/
theorem revise_without_contract_violates :
    ¬ ∀ r ∈ (rule "revise" ["q", "e1", "e2"]
        [ev (fv "q") (fv "e1"), ev (fv "q") (fv "e2")]
        (ev (fv "q") (app "revise" [fv "e1", fv "e2"])) :: evidenceRules.tail),
      r.premises.countP isEvidencePremise = 2 → r.id.value ≠ "revise-unknown-overlap" →
        r.premises.any isContractPremise = true := by
  decide

end Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule
