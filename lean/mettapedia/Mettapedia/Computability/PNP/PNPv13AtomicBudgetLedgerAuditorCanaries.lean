import Mettapedia.Computability.PNP.PNPv13AtomicEvidenceBudgetExactnessReduction

/-!
# PNP v13 atomic-budget ledger auditor canaries

This module mirrors the finite private validation lab for the structural
atomic-budget ledger.  Scalar equality is not enough: the ledger must pass
no-double-counting, positive-cost coverage, fresh-gauge, incidence, and
safe-budget checks.
-/

namespace Mettapedia.Computability.PNP

/-- Coordinates in the finite structural budget canaries. -/
inductive AtomicBudgetLedgerCoord where
  | c0
  | c1
  | c2
deriving DecidableEq, Repr

/-- Evidence atoms in the finite structural budget canaries. -/
inductive AtomicBudgetLedgerAtom where
  | safeA
  | safeB
  | gaugeA
  | residualA
deriving DecidableEq, Repr

/-- Structural atom classes for the finite ledger auditor. -/
inductive AtomicBudgetLedgerAtomKind where
  | safe
  | gauge
  | residual
deriving DecidableEq, Repr

/-- Charge classes recorded by coordinates. -/
inductive AtomicBudgetLedgerChargeKind where
  | safe
  | gauge
  | residual
deriving DecidableEq, Repr

/-- Atom metadata used by the structural budget auditor. -/
structure AtomicBudgetLedgerAtomInfo where
  cost : Nat
  kind : AtomicBudgetLedgerAtomKind
  freshGauge : Bool
deriving DecidableEq, Repr

/-- One coordinate-to-atom charge in the structural budget auditor. -/
structure AtomicBudgetLedgerCharge where
  coord : AtomicBudgetLedgerCoord
  atom : AtomicBudgetLedgerAtom
  kind : AtomicBudgetLedgerChargeKind
deriving DecidableEq, Repr

/-- A concrete safe-budget excess report. -/
structure AtomicBudgetSafeBudgetExcess where
  limit : Nat
  total : Nat
deriving DecidableEq, Repr

/-- Finite atomic-budget ledger audited by the canaries. -/
structure AtomicBudgetLedger where
  atomInfo : AtomicBudgetLedgerAtom → AtomicBudgetLedgerAtomInfo
  charges : List AtomicBudgetLedgerCharge
  incidenceBound : Nat
  safeBudget : Nat

/-- Finite atom universe used by the auditor. -/
def atomicBudgetLedgerAtoms : List AtomicBudgetLedgerAtom :=
  [.safeA, .safeB, .gaugeA, .residualA]

/-- Finite coordinate universe used by the auditor. -/
def atomicBudgetLedgerCoords : List AtomicBudgetLedgerCoord :=
  [.c0, .c1, .c2]

/-- A zero-cost default atom. -/
def atomicBudgetZeroInfo (kind : AtomicBudgetLedgerAtomKind) :
    AtomicBudgetLedgerAtomInfo where
  cost := 0
  kind := kind
  freshGauge := false

/-- A positive-cost safe atom. -/
def atomicBudgetSafeInfo : AtomicBudgetLedgerAtomInfo where
  cost := 1
  kind := .safe
  freshGauge := false

/-- A positive-cost fresh gauge atom. -/
def atomicBudgetFreshGaugeInfo : AtomicBudgetLedgerAtomInfo where
  cost := 1
  kind := .gauge
  freshGauge := true

/-- A positive-cost stale gauge atom. -/
def atomicBudgetStaleGaugeInfo : AtomicBudgetLedgerAtomInfo where
  cost := 1
  kind := .gauge
  freshGauge := false

/-- A positive-cost residual atom. -/
def atomicBudgetResidualInfo : AtomicBudgetLedgerAtomInfo where
  cost := 1
  kind := .residual
  freshGauge := false

/-- Standard safe charge on atom `safeA`. -/
def atomicBudgetChargeSafeA (coord : AtomicBudgetLedgerCoord) :
    AtomicBudgetLedgerCharge where
  coord := coord
  atom := .safeA
  kind := .safe

/-- Standard safe charge on atom `safeB`. -/
def atomicBudgetChargeSafeB (coord : AtomicBudgetLedgerCoord) :
    AtomicBudgetLedgerCharge where
  coord := coord
  atom := .safeB
  kind := .safe

/-- Standard gauge charge on atom `gaugeA`. -/
def atomicBudgetChargeGaugeA (coord : AtomicBudgetLedgerCoord) :
    AtomicBudgetLedgerCharge where
  coord := coord
  atom := .gaugeA
  kind := .gauge

/-- Standard residual charge on atom `residualA`. -/
def atomicBudgetChargeResidualA (coord : AtomicBudgetLedgerCoord) :
    AtomicBudgetLedgerCharge where
  coord := coord
  atom := .residualA
  kind := .residual

namespace AtomicBudgetLedger

/-- Number of charges incident on one atom. -/
def atomChargeCount (L : AtomicBudgetLedger)
    (atom : AtomicBudgetLedgerAtom) : Nat :=
  (L.charges.filter fun charge => charge.atom = atom).length

/-- Number of charges emitted by one coordinate. -/
def coordChargeCount (L : AtomicBudgetLedger)
    (coord : AtomicBudgetLedgerCoord) : Nat :=
  (L.charges.filter fun charge => charge.coord = coord).length

  /-- Recursive once-per-atom scalar budget. -/
  def atomBudgetAux (L : AtomicBudgetLedger) :
      List AtomicBudgetLedgerAtom → Nat
    | [] => 0
    | atom :: atoms => (L.atomInfo atom).cost + atomBudgetAux L atoms

  /-- Once-per-atom scalar budget. -/
  def atomBudget (L : AtomicBudgetLedger) : Nat :=
    L.atomBudgetAux atomicBudgetLedgerAtoms

  /-- Recursive coordinate-summed scalar cost. -/
  def coordinateSummedCostAux (L : AtomicBudgetLedger) :
      List AtomicBudgetLedgerCharge → Nat
    | [] => 0
    | charge :: charges =>
        (L.atomInfo charge.atom).cost + coordinateSummedCostAux L charges

  /-- Coordinate-summed scalar cost. -/
  def coordinateSummedCost (L : AtomicBudgetLedger) : Nat :=
    L.coordinateSummedCostAux L.charges

/-- Positive-cost atoms charged by more than one coordinate. -/
def overchargedAtoms (L : AtomicBudgetLedger) :
    List AtomicBudgetLedgerAtom :=
  atomicBudgetLedgerAtoms.filter fun atom =>
    decide (0 < (L.atomInfo atom).cost ∧ 1 < L.atomChargeCount atom)

/-- Positive-cost atoms charged by no coordinate. -/
def missingPositiveCostAtoms (L : AtomicBudgetLedger) :
    List AtomicBudgetLedgerAtom :=
  atomicBudgetLedgerAtoms.filter fun atom =>
    decide (0 < (L.atomInfo atom).cost ∧ L.atomChargeCount atom = 0)

/-- Positive-cost residual atoms charged by no coordinate. -/
def missingResidualPositiveCostAtoms (L : AtomicBudgetLedger) :
    List AtomicBudgetLedgerAtom :=
  atomicBudgetLedgerAtoms.filter fun atom =>
    decide
      (0 < (L.atomInfo atom).cost ∧
        L.atomChargeCount atom = 0 ∧
        (L.atomInfo atom).kind = .residual)

/-- Gauge charges whose atom is not a fresh gauge atom. -/
def staleGaugeCharges (L : AtomicBudgetLedger) :
    List AtomicBudgetLedgerCharge :=
  L.charges.filter fun charge =>
    decide
      (charge.kind = .gauge ∧
        ¬ ((L.atomInfo charge.atom).kind = .gauge ∧
          (L.atomInfo charge.atom).freshGauge = true))

/-- Coordinates whose outgoing incidence exceeds the ledger bound. -/
def incidenceOverflowCoords (L : AtomicBudgetLedger) :
    List AtomicBudgetLedgerCoord :=
  atomicBudgetLedgerCoords.filter fun coord =>
    decide (L.incidenceBound < L.coordChargeCount coord)

/-- Safe charges against atoms outside the safe-buffer class. -/
def unsafeSafeCharges (L : AtomicBudgetLedger) :
    List AtomicBudgetLedgerCharge :=
  L.charges.filter fun charge =>
    decide
      (charge.kind = .safe ∧ (L.atomInfo charge.atom).kind ≠ .safe)

/-- Recursive total positive cost carried by safe charges. -/
def safeChargeTotalAux (L : AtomicBudgetLedger) :
    List AtomicBudgetLedgerCharge → Nat
  | [] => 0
  | charge :: charges =>
      match charge.kind with
      | .safe => (L.atomInfo charge.atom).cost + safeChargeTotalAux L charges
      | .gauge => safeChargeTotalAux L charges
      | .residual => safeChargeTotalAux L charges

/-- Total positive cost carried by safe charges. -/
def safeChargeTotal (L : AtomicBudgetLedger) : Nat :=
  L.safeChargeTotalAux L.charges

/-- Safe-budget excess report, if the safe total exceeds the safe bound. -/
def safeBudgetExcess? (L : AtomicBudgetLedger) :
    Option AtomicBudgetSafeBudgetExcess :=
  if L.safeBudget < L.safeChargeTotal then
    some { limit := L.safeBudget, total := L.safeChargeTotal }
  else
    none

/-- Structural no-double-counting check. -/
def NoDoubleCounting (L : AtomicBudgetLedger) : Prop :=
  L.overchargedAtoms = []

/-- Structural positive-cost coverage check. -/
def AllPositiveCostAtomsCharged (L : AtomicBudgetLedger) : Prop :=
  L.missingPositiveCostAtoms = []

/-- Structural fresh-gauge check. -/
def FreshGaugeOnly (L : AtomicBudgetLedger) : Prop :=
  L.staleGaugeCharges = []

/-- Structural bounded-incidence check. -/
def BoundedIncidence (L : AtomicBudgetLedger) : Prop :=
  L.incidenceOverflowCoords = []

/-- Structural safe-budget check. -/
def SafeBudget (L : AtomicBudgetLedger) : Prop :=
  L.unsafeSafeCharges = [] ∧ L.safeBudgetExcess? = none

/-- Full structural exactness side condition for this finite auditor. -/
def ClearsAllStructuralChecks (L : AtomicBudgetLedger) : Prop :=
  L.NoDoubleCounting ∧
    L.AllPositiveCostAtomsCharged ∧
    L.FreshGaugeOnly ∧
    L.BoundedIncidence ∧
    L.SafeBudget

end AtomicBudgetLedger

/-- Positive canary ledger: every named structural check clears. -/
def atomicBudgetGoodLedger : AtomicBudgetLedger where
  atomInfo
    | .safeA => atomicBudgetSafeInfo
    | .safeB => atomicBudgetZeroInfo .safe
    | .gaugeA => atomicBudgetFreshGaugeInfo
    | .residualA => atomicBudgetResidualInfo
  charges :=
    [atomicBudgetChargeSafeA .c0,
      atomicBudgetChargeGaugeA .c1,
      atomicBudgetChargeResidualA .c2]
  incidenceBound := 1
  safeBudget := 1

/-- Negative canary ledger: one positive atom is charged twice. -/
def atomicBudgetOverchargeLedger : AtomicBudgetLedger where
  atomInfo
    | .safeA => atomicBudgetZeroInfo .safe
    | .safeB => atomicBudgetZeroInfo .safe
    | .gaugeA => atomicBudgetZeroInfo .gauge
    | .residualA => atomicBudgetResidualInfo
  charges :=
    [atomicBudgetChargeResidualA .c0,
      atomicBudgetChargeResidualA .c1]
  incidenceBound := 1
  safeBudget := 0

/-- Negative canary ledger: one positive residual atom is not charged. -/
def atomicBudgetUnderchargeLedger : AtomicBudgetLedger where
  atomInfo
    | .safeA => atomicBudgetSafeInfo
    | .safeB => atomicBudgetZeroInfo .safe
    | .gaugeA => atomicBudgetZeroInfo .gauge
    | .residualA => atomicBudgetResidualInfo
  charges := [atomicBudgetChargeSafeA .c0]
  incidenceBound := 1
  safeBudget := 1

/-- Negative canary ledger: scalar equality hides a double count and omission. -/
def atomicBudgetCancellationLedger : AtomicBudgetLedger where
  atomInfo
    | .safeA => atomicBudgetSafeInfo
    | .safeB => atomicBudgetZeroInfo .safe
    | .gaugeA => atomicBudgetZeroInfo .gauge
    | .residualA => atomicBudgetResidualInfo
  charges :=
    [atomicBudgetChargeSafeA .c0,
      atomicBudgetChargeSafeA .c1]
  incidenceBound := 1
  safeBudget := 2

/-- Negative canary ledger: a gauge charge uses a stale gauge atom. -/
def atomicBudgetStaleGaugeLedger : AtomicBudgetLedger where
  atomInfo
    | .safeA => atomicBudgetZeroInfo .safe
    | .safeB => atomicBudgetZeroInfo .safe
    | .gaugeA => atomicBudgetStaleGaugeInfo
    | .residualA => atomicBudgetZeroInfo .residual
  charges := [atomicBudgetChargeGaugeA .c0]
  incidenceBound := 1
  safeBudget := 0

/-- Negative canary ledger: one coordinate exceeds the incidence bound. -/
def atomicBudgetIncidenceOverflowLedger : AtomicBudgetLedger where
  atomInfo
    | .safeA => atomicBudgetSafeInfo
    | .safeB => atomicBudgetZeroInfo .safe
    | .gaugeA => atomicBudgetFreshGaugeInfo
    | .residualA => atomicBudgetResidualInfo
  charges :=
    [atomicBudgetChargeSafeA .c0,
      atomicBudgetChargeGaugeA .c0,
      atomicBudgetChargeResidualA .c0]
  incidenceBound := 2
  safeBudget := 1

/-- Negative canary ledger: safe charges exceed the safe budget. -/
def atomicBudgetSafeBudgetOverflowLedger : AtomicBudgetLedger where
  atomInfo
    | .safeA => atomicBudgetSafeInfo
    | .safeB => atomicBudgetSafeInfo
    | .gaugeA => atomicBudgetZeroInfo .gauge
    | .residualA => atomicBudgetZeroInfo .residual
  charges :=
    [atomicBudgetChargeSafeA .c0,
      atomicBudgetChargeSafeB .c1]
  incidenceBound := 1
  safeBudget := 1

/-- Positive lab canary: all structural budget checks clear. -/
theorem atomicBudgetLedger_lab_positive_canary :
    atomicBudgetGoodLedger.ClearsAllStructuralChecks ∧
      atomicBudgetGoodLedger.atomBudget = 3 ∧
      atomicBudgetGoodLedger.coordinateSummedCost = 3 := by
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

/-- Negative lab canary: a positive atom charged twice blocks no-double-counting. -/
theorem atomicBudgetLedger_overcharge_negative_canary :
    atomicBudgetOverchargeLedger.overchargedAtoms =
        [AtomicBudgetLedgerAtom.residualA] ∧
      atomicBudgetOverchargeLedger.atomBudget = 1 ∧
      atomicBudgetOverchargeLedger.coordinateSummedCost = 2 ∧
      ¬ atomicBudgetOverchargeLedger.NoDoubleCounting := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro hno
  change [AtomicBudgetLedgerAtom.residualA] = [] at hno
  cases hno

/-- Negative lab canary: an uncharged positive residual is reported directly. -/
theorem atomicBudgetLedger_undercharge_negative_canary :
    atomicBudgetUnderchargeLedger.missingPositiveCostAtoms =
        [AtomicBudgetLedgerAtom.residualA] ∧
      atomicBudgetUnderchargeLedger.missingResidualPositiveCostAtoms =
        [AtomicBudgetLedgerAtom.residualA] ∧
      ¬ atomicBudgetUnderchargeLedger.AllPositiveCostAtomsCharged := by
  refine ⟨rfl, rfl, ?_⟩
  intro hall
  change [AtomicBudgetLedgerAtom.residualA] = [] at hall
  cases hall

/-- Negative lab canary: scalar equality can hide structural cancellation. -/
theorem atomicBudgetLedger_cancellation_negative_canary :
      atomicBudgetCancellationLedger.atomBudget = 2 ∧
      atomicBudgetCancellationLedger.coordinateSummedCost = 2 ∧
      atomicBudgetCancellationLedger.overchargedAtoms =
        [AtomicBudgetLedgerAtom.safeA] ∧
      atomicBudgetCancellationLedger.missingPositiveCostAtoms =
        [AtomicBudgetLedgerAtom.residualA] ∧
      ¬ atomicBudgetCancellationLedger.ClearsAllStructuralChecks := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro hclear
  have hno : atomicBudgetCancellationLedger.NoDoubleCounting := hclear.1
  change [AtomicBudgetLedgerAtom.safeA] = [] at hno
  cases hno

/-- Negative lab canary: stale gauge usage blocks the fresh-gauge check. -/
theorem atomicBudgetLedger_staleGauge_negative_canary :
    atomicBudgetStaleGaugeLedger.staleGaugeCharges =
        [atomicBudgetChargeGaugeA .c0] ∧
      ¬ atomicBudgetStaleGaugeLedger.FreshGaugeOnly := by
  refine ⟨rfl, ?_⟩
  intro hfresh
  change [atomicBudgetChargeGaugeA .c0] = [] at hfresh
  cases hfresh

/-- Negative lab canary: incidence overflow is structural even with coverage. -/
theorem atomicBudgetLedger_incidence_negative_canary :
    atomicBudgetIncidenceOverflowLedger.incidenceOverflowCoords =
        [AtomicBudgetLedgerCoord.c0] ∧
      ¬ atomicBudgetIncidenceOverflowLedger.BoundedIncidence := by
  refine ⟨rfl, ?_⟩
  intro hbounded
  change [AtomicBudgetLedgerCoord.c0] = [] at hbounded
  cases hbounded

/-- Negative lab canary: safe charges can exceed the safe budget. -/
theorem atomicBudgetLedger_safeBudget_negative_canary :
    atomicBudgetSafeBudgetOverflowLedger.safeBudgetExcess? =
        some ({ limit := 1, total := 2 } : AtomicBudgetSafeBudgetExcess) ∧
      ¬ atomicBudgetSafeBudgetOverflowLedger.SafeBudget := by
  refine ⟨rfl, ?_⟩
  intro hsafe
  have hexcess : atomicBudgetSafeBudgetOverflowLedger.safeBudgetExcess? = none :=
    hsafe.2
  change some ({ limit := 1, total := 2 } : AtomicBudgetSafeBudgetExcess) =
    none at hexcess
  cases hexcess

/-- The structural auditor separates scalar equality from exact side checks. -/
theorem atomicBudgetLedgerStructuralCanaries_separate_scalarEquality_from_structuralExactness :
    atomicBudgetCancellationLedger.atomBudget =
        atomicBudgetCancellationLedger.coordinateSummedCost ∧
      ¬ atomicBudgetCancellationLedger.ClearsAllStructuralChecks := by
  refine ⟨?_, ?_⟩
  · rw [show atomicBudgetCancellationLedger.atomBudget = 2 by rfl]
    rw [show atomicBudgetCancellationLedger.coordinateSummedCost = 2 by rfl]
  · exact atomicBudgetLedger_cancellation_negative_canary.2.2.2.2

end Mettapedia.Computability.PNP
