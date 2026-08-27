import Mettapedia.Computability.PNP.V13ConditionalClash

/-!
# PNP v13 faithfulness audit

This module records a Lean-side audit table for the abstract v13 interface.
Each row maps a Phase A/B definition or one of the nine
`GaugeBufferedLockedInterface` fields to the section of the v13 red-team note
it formalizes, with an explicit mismatch verdict.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

inductive V13AuditKind where
  | phaseA
  | phaseB
  | ledgerField
deriving DecidableEq, Repr

inductive V13FaithfulnessVerdict where
  | faithful
  | weakerThanNote
  | strongerThanNote
  | differentButConservative
  | reportableFinding
deriving DecidableEq, Repr

structure V13FaithfulnessRow where
  name : String
  kind : V13AuditKind
  noteSection : String
  verdict : V13FaithfulnessVerdict
  mismatch : String
deriving Repr

def v13PhaseAFaithfulnessRows : List V13FaithfulnessRow := [
  {
    name := "FiniteRationalLaw"
    kind := .phaseA
    noteSection := "Section 4 and Section 8.1"
    verdict := .faithful
    mismatch := "Finite world law over a Fintype with rational weights; deliberately no measure theory."
  },
  {
    name := "Gap"
    kind := .phaseA
    noteSection := "Section 8.1"
    verdict := .faithful
    mismatch := "Matches the half absolute conditional-probability target gap for a finite observer transcript."
  },
  {
    name := "StaticPairwiseCapture"
    kind := .phaseA
    noteSection := "Section 4 and Section 8.1"
    verdict := .weakerThanNote
    mismatch := "Stores the capture inequality as a certificate field rather than deriving phase marginals of a concrete coupling."
  },
  {
    name := "DerivativeTelescoping"
    kind := .phaseA
    noteSection := "Section 4 and Section 8.1"
    verdict := .weakerThanNote
    mismatch := "Records finite derivative accounting abstractly; it does not construct manuscript trace derivatives."
  },
  {
    name := "EvidenceSpineBound"
    kind := .phaseA
    noteSection := "Section 8.1"
    verdict := .faithful
    mismatch := "Combines pairwise capture and derivative telescoping to bound the finite target gap."
  }
]

def v13PhaseBFaithfulnessRows : List V13FaithfulnessRow := [
  {
    name := "RawEvidence"
    kind := .phaseB
    noteSection := "Section 5.6 and Section 8.2"
    verdict := .strongerThanNote
    mismatch := "The type forbids an opaque observer-output constructor outright."
  },
  {
    name := "NormalEvidence"
    kind := .phaseB
    noteSection := "Section 3, Section 6.2, and Section 8.2"
    verdict := .faithful
    mismatch := "Normal leaves are exactly neutral, safe-buffer, and hidden-gauge leaves plus Boolean structure."
  },
  {
    name := "EvidenceSemantics"
    kind := .phaseB
    noteSection := "Section 8.2"
    verdict := .faithful
    mismatch := "Gives finite-world satisfaction semantics for raw and normal evidence."
  },
  {
    name := "CDENF"
    kind := .phaseB
    noteSection := "Section 6.2 and Section 8.2"
    verdict := .faithful
    mismatch := "Recursive normalizer to the N/S/G normal evidence surface; no confluence claim is made."
  },
  {
    name := "CDENF_semantics"
    kind := .phaseB
    noteSection := "Section 8.2"
    verdict := .faithful
    mismatch := "First theorem is semantic preservation Sat(CDENF E) = Sat E."
  },
  {
    name := "ObserverEvidenceInterface"
    kind := .phaseB
    noteSection := "Section 5.6 and Section 7.6"
    verdict := .faithful
    mismatch := "Observer outputs must expand through observerToEvidence with a semantics theorem."
  }
]

def v13LedgerFaithfulnessRows : List V13FaithfulnessRow := [
  {
    name := "singleMessage"
    kind := .ledgerField
    noteSection := "Section 4, Section 5.1, and Section 8.3"
    verdict := .faithful
    mismatch := "Formalizes that the target bit is fixed by the full public instance on the supported interface."
  },
  {
    name := "gaugePredicateTotal"
    kind := .ledgerField
    noteSection := "Section 8.3"
    verdict := .weakerThanNote
    mismatch := "Records fairness as universal gauge satisfaction in the abstract ledger; concrete product independence remains Phase E work."
  },
  {
    name := "noPublicTargetTags"
    kind := .ledgerField
    noteSection := "Section 6.1, Section 6.3, and Section 7.7"
    verdict := .faithful
    mismatch := "Bundles pair-neutral skeleton, an opposite pair, and non-sufficiency of the neutral skeleton."
  },
  {
    name := "atomCompleteness"
    kind := .ledgerField
    noteSection := "Section 6.2 and Section 8.3"
    verdict := .weakerThanNote
    mismatch := "States semantic completeness of CDENF for all raw evidence; it does not enumerate target-relevant trace atoms."
  },
  {
    name := "gaugeFaithfulness"
    kind := .ledgerField
    noteSection := "Section 6.4 and Section 8.3"
    verdict := .weakerThanNote
    mismatch := "Ensures gauge leaves preserve gauge semantics; quotient expansion for concrete gauge coordinates is deferred to Phase E."
  },
  {
    name := "safeQSSM"
    kind := .ledgerField
    noteSection := "Section 3 and Section 8.3"
    verdict := .weakerThanNote
    mismatch := "Abstract safe-cost budget only; it does not prove max-qSSM for a concrete SAT ensemble."
  },
  {
    name := "boundedGaugeIncidence"
    kind := .ledgerField
    noteSection := "Section 3 and Section 8.3"
    verdict := .faithful
    mismatch := "Records bounded incidence of gauge charges against target coordinates."
  },
  {
    name := "boundaryMixing"
    kind := .ledgerField
    noteSection := "Section 5.5, Section 6.5, and Section 8.3"
    verdict := .weakerThanNote
    mismatch := "Finite unconditional pivot-summary mixing; the note's conditional-history version is stronger."
  },
  {
    name := "admissibleHistories"
    kind := .ledgerField
    noteSection := "Section 5.4 and Section 8.3"
    verdict := .faithful
    mismatch := "Records target balance and balanced conditioning for the current finite history field."
  }
]

def v13FaithfulnessAudit : List V13FaithfulnessRow :=
  v13PhaseAFaithfulnessRows ++
    v13PhaseBFaithfulnessRows ++
      v13LedgerFaithfulnessRows

theorem v13PhaseAFaithfulnessRows_length :
    v13PhaseAFaithfulnessRows.length = 5 := by
  rfl

theorem v13PhaseBFaithfulnessRows_length :
    v13PhaseBFaithfulnessRows.length = 6 := by
  rfl

theorem v13LedgerFaithfulnessRows_length :
    v13LedgerFaithfulnessRows.length = 9 := by
  rfl

theorem v13FaithfulnessAudit_length :
    v13FaithfulnessAudit.length = 20 := by
  rfl

theorem v13FaithfulnessAudit_has_no_reportable_findings :
    ∀ row ∈ v13FaithfulnessAudit,
      row.verdict ≠ .reportableFinding := by
  intro row hmem
  simp [v13FaithfulnessAudit, v13PhaseAFaithfulnessRows,
    v13PhaseBFaithfulnessRows, v13LedgerFaithfulnessRows] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst row; decide

end Mettapedia.Computability.PNP
