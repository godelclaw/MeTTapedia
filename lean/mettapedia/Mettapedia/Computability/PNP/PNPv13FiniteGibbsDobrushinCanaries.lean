/-!
# PNP v13 finite Gibbs/Dobrushin mixing canaries

This module mirrors the finite private validation lab for Dobrushin-style
boundary-law checks.  The finite gate is strict max-row contraction: average
row mass, equality at the critical value, and sampled rows that miss an
unsampled violation are not enough.
-/

namespace Mettapedia.Computability.PNP

/-- Recursive sum used by the finite Dobrushin canaries. -/
def finiteGibbsNatSum : List Nat → Nat
  | [] => 0
  | n :: ns => n + finiteGibbsNatSum ns

/-- Recursive maximum with zero as the empty-list value. -/
def finiteGibbsMaxNat : List Nat → Nat
  | [] => 0
  | n :: ns => max n (finiteGibbsMaxNat ns)

/-- Row sums of a scaled finite influence matrix. -/
def finiteGibbsRowSums : List (List Nat) → List Nat
  | [] => []
  | row :: rows => finiteGibbsNatSum row :: finiteGibbsRowSums rows

/-- Total row mass of a scaled finite influence matrix. -/
def finiteGibbsTotalRowMass (rows : List (List Nat)) : Nat :=
  finiteGibbsNatSum (finiteGibbsRowSums rows)

/-- The scaled max-qSSM/Dobrushin constant for a finite influence matrix. -/
def finiteGibbsMaxQSSMConstantScaled (rows : List (List Nat)) : Nat :=
  finiteGibbsMaxNat (finiteGibbsRowSums rows)

/-- Every influence row is strictly below the scaling denominator. -/
def finiteGibbsRowsStrictBelow (scale : Nat) :
    List (List Nat) → Bool
  | [] => true
  | row :: rows =>
      decide (finiteGibbsNatSum row < scale) &&
        finiteGibbsRowsStrictBelow scale rows

/-- Every influence row is at most the scaling denominator. -/
def finiteGibbsRowsNonStrictBelow (scale : Nat) :
    List (List Nat) → Bool
  | [] => true
  | row :: rows =>
      decide (finiteGibbsNatSum row ≤ scale) &&
        finiteGibbsRowsNonStrictBelow scale rows

/-- Average row mass is below the scaling denominator. -/
def finiteGibbsAverageRowMassClears
    (scale : Nat) (rows : List (List Nat)) : Bool :=
  decide (finiteGibbsTotalRowMass rows < scale * rows.length)

/-- Strict max-row Dobrushin contraction gate. -/
def finiteGibbsStrictMaxRowContractionClears
    (scale : Nat) (rows : List (List Nat)) : Bool :=
  decide (finiteGibbsMaxQSSMConstantScaled rows < scale)

/-- Non-strict max-row boundedness, useful only as a negative canary. -/
def finiteGibbsNonStrictMaxRowBoundClears
    (scale : Nat) (rows : List (List Nat)) : Bool :=
  decide (finiteGibbsMaxQSSMConstantScaled rows ≤ scale)

/-- Strict contraction margin, when the max-row gate clears. -/
def finiteGibbsBoundaryContractionMargin?
    (scale : Nat) (rows : List (List Nat)) : Option Nat :=
  if finiteGibbsStrictMaxRowContractionClears scale rows then
    some (scale - finiteGibbsMaxQSSMConstantScaled rows)
  else
    none

/-- Lookup a row by index. -/
def finiteGibbsRowAt? :
    List (List Nat) → Nat → Option (List Nat)
  | [], _ => none
  | row :: _, 0 => some row
  | _ :: rows, n + 1 => finiteGibbsRowAt? rows n

/-- Sampled-row strictness check.  This is not a full all-row certificate. -/
def finiteGibbsSampledRowsStrictBelowAux
    (scale : Nat) (rows : List (List Nat)) :
    List Nat → Bool
  | [] => true
  | index :: indices =>
      match finiteGibbsRowAt? rows index with
      | some row =>
          decide (finiteGibbsNatSum row < scale) &&
            finiteGibbsSampledRowsStrictBelowAux scale rows indices
      | none => false

/-- Whether a concrete indexed row violates the scaled max-row gate. -/
def finiteGibbsRowViolatesAt
    (scale : Nat) (rows : List (List Nat)) (index : Nat) : Bool :=
  match finiteGibbsRowAt? rows index with
  | some row => decide (scale ≤ finiteGibbsNatSum row)
  | none => false

/-- Finite Gibbs/Dobrushin audit surface. -/
structure FiniteGibbsDobrushinAudit where
  scale : Nat
  influenceRows : List (List Nat)
  sampledRows : List Nat
deriving DecidableEq, Repr

namespace FiniteGibbsDobrushinAudit

/-- Row sums of the audit matrix. -/
def rowSums (audit : FiniteGibbsDobrushinAudit) : List Nat :=
  finiteGibbsRowSums audit.influenceRows

/-- Total row mass of the audit matrix. -/
def totalRowMass (audit : FiniteGibbsDobrushinAudit) : Nat :=
  finiteGibbsTotalRowMass audit.influenceRows

/-- Scaled max-qSSM/Dobrushin constant of the audit matrix. -/
def maxQSSMConstantScaled (audit : FiniteGibbsDobrushinAudit) : Nat :=
  finiteGibbsMaxQSSMConstantScaled audit.influenceRows

/-- Strict max-row contraction gate for the audit. -/
def strictMaxRowContractionClears
    (audit : FiniteGibbsDobrushinAudit) : Bool :=
  finiteGibbsStrictMaxRowContractionClears audit.scale audit.influenceRows

/-- Non-strict max-row boundedness for the audit. -/
def nonStrictMaxRowBoundClears
    (audit : FiniteGibbsDobrushinAudit) : Bool :=
  finiteGibbsNonStrictMaxRowBoundClears audit.scale audit.influenceRows

/-- Average row-mass check for the audit. -/
def averageRowMassClears (audit : FiniteGibbsDobrushinAudit) : Bool :=
  finiteGibbsAverageRowMassClears audit.scale audit.influenceRows

/-- Strict contraction margin, when available. -/
def boundaryContractionMargin?
    (audit : FiniteGibbsDobrushinAudit) : Option Nat :=
  finiteGibbsBoundaryContractionMargin? audit.scale audit.influenceRows

/-- Sampled-row strictness check. -/
def sampledRowsStrictBelow (audit : FiniteGibbsDobrushinAudit) : Bool :=
  finiteGibbsSampledRowsStrictBelowAux
    audit.scale audit.influenceRows audit.sampledRows

/-- Concrete indexed row violation report. -/
def rowViolatesAt (audit : FiniteGibbsDobrushinAudit) (index : Nat) : Bool :=
  finiteGibbsRowViolatesAt audit.scale audit.influenceRows index

end FiniteGibbsDobrushinAudit

/-- Positive canary: every row is strictly below scale. -/
def finiteGibbsDobrushinStrictContractionAudit :
    FiniteGibbsDobrushinAudit where
  scale := 100
  influenceRows := [[0, 25], [35, 0]]
  sampledRows := [0, 1]

/-- Negative canary: average below one, but one row exceeds one. -/
def finiteGibbsDobrushinAverageOnlyAudit :
    FiniteGibbsDobrushinAudit where
  scale := 100
  influenceRows := [[0, 150], [0, 0]]
  sampledRows := [0, 1]

/-- Negative canary: equality at one is not strict contraction. -/
def finiteGibbsDobrushinEqualityAudit :
    FiniteGibbsDobrushinAudit where
  scale := 100
  influenceRows := [[0, 100], [0, 0]]
  sampledRows := [0, 1]

/-- Negative canary: sampled rows miss a hidden max-row violation. -/
def finiteGibbsDobrushinSampledRowsAudit :
    FiniteGibbsDobrushinAudit where
  scale := 100
  influenceRows := [[0, 20, 0], [0, 0, 20], [150, 0, 0]]
  sampledRows := [0, 1]

/-- Positive lab canary: strict max-row contraction gives a finite margin. -/
theorem finiteGibbsDobrushinStrictContraction_lab_positive_canary :
    finiteGibbsDobrushinStrictContractionAudit.rowSums = [25, 35] ∧
      finiteGibbsDobrushinStrictContractionAudit.maxQSSMConstantScaled = 35 ∧
      finiteGibbsDobrushinStrictContractionAudit.strictMaxRowContractionClears = true ∧
      finiteGibbsDobrushinStrictContractionAudit.boundaryContractionMargin? =
        some 65 ∧
      finiteGibbsDobrushinStrictContractionAudit.sampledRowsStrictBelow = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Negative lab canary: average row mass below one is not max-row contraction. -/
theorem finiteGibbsDobrushinAverageOnly_negative_canary :
    finiteGibbsDobrushinAverageOnlyAudit.averageRowMassClears = true ∧
      finiteGibbsDobrushinAverageOnlyAudit.maxQSSMConstantScaled = 150 ∧
      finiteGibbsDobrushinAverageOnlyAudit.strictMaxRowContractionClears = false ∧
      finiteGibbsDobrushinAverageOnlyAudit.boundaryContractionMargin? = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Negative lab canary: non-strict equality at one is not a strict margin. -/
theorem finiteGibbsDobrushinEquality_negative_canary :
    finiteGibbsDobrushinEqualityAudit.nonStrictMaxRowBoundClears = true ∧
      finiteGibbsDobrushinEqualityAudit.maxQSSMConstantScaled = 100 ∧
      finiteGibbsDobrushinEqualityAudit.strictMaxRowContractionClears = false ∧
      finiteGibbsDobrushinEqualityAudit.boundaryContractionMargin? = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Negative lab canary: sampled rows can miss an unsampled violation. -/
theorem finiteGibbsDobrushinSampledRows_negative_canary :
    finiteGibbsDobrushinSampledRowsAudit.sampledRowsStrictBelow = true ∧
      finiteGibbsDobrushinSampledRowsAudit.rowViolatesAt 2 = true ∧
      finiteGibbsDobrushinSampledRowsAudit.maxQSSMConstantScaled = 150 ∧
      finiteGibbsDobrushinSampledRowsAudit.strictMaxRowContractionClears = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The finite canaries separate weak estimates from strict max-row contraction. -/
theorem finiteGibbsDobrushinCanaries_guardrails :
    finiteGibbsDobrushinStrictContractionAudit.strictMaxRowContractionClears = true ∧
      finiteGibbsDobrushinAverageOnlyAudit.averageRowMassClears = true ∧
      finiteGibbsDobrushinAverageOnlyAudit.strictMaxRowContractionClears = false ∧
      finiteGibbsDobrushinEqualityAudit.nonStrictMaxRowBoundClears = true ∧
      finiteGibbsDobrushinEqualityAudit.strictMaxRowContractionClears = false ∧
      finiteGibbsDobrushinSampledRowsAudit.sampledRowsStrictBelow = true ∧
      finiteGibbsDobrushinSampledRowsAudit.strictMaxRowContractionClears = false := by
  exact
    ⟨finiteGibbsDobrushinStrictContraction_lab_positive_canary.2.2.1,
      finiteGibbsDobrushinAverageOnly_negative_canary.1,
      finiteGibbsDobrushinAverageOnly_negative_canary.2.2.1,
      finiteGibbsDobrushinEquality_negative_canary.1,
      finiteGibbsDobrushinEquality_negative_canary.2.2.1,
      finiteGibbsDobrushinSampledRows_negative_canary.1,
      finiteGibbsDobrushinSampledRows_negative_canary.2.2.2⟩

end Mettapedia.Computability.PNP
