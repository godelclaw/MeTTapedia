import Mettapedia.Computability.PNP.PNPv13ChargedPublicBudgetObstruction

/-!
# PNP v13: finite charged-public transport certificates

These certificates mirror exact transportation problems on Boolean public
strings.  The target is a truth table, the charged mask selects the public
coordinates allowed to differ, and all complementary coordinates must agree.
The coupling is scaled by the product of the two phase cardinalities, making
the marginal and objective checks integral.

The three certificates realize charged Hamming objective one on public cubes
of dimensions one, two, and three.  The checker also verifies the universal
dual lower bound: every allowed opposite-target edge has charged distance at
least one.  Thus each displayed primal certificate is optimal.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-- One positive integral entry of a scaled finite transport plan. -/
structure V13ChargedPublicFlowEntry where
  left : Nat
  right : Nat
  amount : Nat
deriving DecidableEq, Repr

/-- Exact integral certificate for one charged-public transport problem. -/
structure V13ChargedPublicTransportCertificate where
  publicBitCount : Nat
  targetTable : Nat
  chargedMask : Nat
  scale : Nat
  objectiveNumerator : Nat
  dualNumerator : Nat
  flow : List V13ChargedPublicFlowEntry
deriving DecidableEq, Repr

namespace V13ChargedPublicTransportCertificate

/-- Number of Boolean public worlds. -/
def worldCount (certificate : V13ChargedPublicTransportCertificate) : Nat :=
  2 ^ certificate.publicBitCount

/-- Truth-table value at one Boolean public world. -/
def target (certificate : V13ChargedPublicTransportCertificate)
    (world : Nat) : Bool :=
  certificate.targetTable.testBit world

/-- Public worlds in the false target phase. -/
def leftWorlds (certificate : V13ChargedPublicTransportCertificate) : List Nat :=
  (List.range certificate.worldCount).filter fun world =>
    !certificate.target world

/-- Public worlds in the true target phase. -/
def rightWorlds (certificate : V13ChargedPublicTransportCertificate) : List Nat :=
  (List.range certificate.worldCount).filter certificate.target

/-- Agreement on every public coordinate outside the charged mask. -/
def neutralAgree (certificate : V13ChargedPublicTransportCertificate)
    (left right : Nat) : Bool :=
  (List.range certificate.publicBitCount).all fun coordinate =>
    certificate.chargedMask.testBit coordinate ||
      (left.testBit coordinate == right.testBit coordinate)

/-- Hamming disagreement restricted to charged public coordinates. -/
def chargedDistance (certificate : V13ChargedPublicTransportCertificate)
    (left right : Nat) : Nat :=
  (List.range certificate.publicBitCount).foldl
    (fun total coordinate =>
      if certificate.chargedMask.testBit coordinate &&
          (left.testBit coordinate != right.testBit coordinate) then
        total + 1
      else
        total)
    0

/-- Total scaled mass leaving one false-phase world. -/
def outgoing (certificate : V13ChargedPublicTransportCertificate)
    (world : Nat) : Nat :=
  (certificate.flow.map fun entry =>
    if entry.left == world then entry.amount else 0).sum

/-- Total scaled mass entering one true-phase world. -/
def incoming (certificate : V13ChargedPublicTransportCertificate)
    (world : Nat) : Nat :=
  (certificate.flow.map fun entry =>
    if entry.right == world then entry.amount else 0).sum

/-- Scaled charged-Hamming objective of the displayed flow. -/
def objective (certificate : V13ChargedPublicTransportCertificate) : Nat :=
  (certificate.flow.map fun entry =>
    entry.amount * certificate.chargedDistance entry.left entry.right).sum

/-- Every displayed flow entry lies on an allowed positive opposite-phase
edge. -/
def supportValid (certificate : V13ChargedPublicTransportCertificate) : Bool :=
  certificate.flow.all fun entry =>
    decide (entry.left < certificate.worldCount) &&
      decide (entry.right < certificate.worldCount) &&
      !certificate.target entry.left &&
      certificate.target entry.right &&
      certificate.neutralAgree entry.left entry.right &&
      decide (0 < entry.amount)

/-- Exact scaled conditional marginals. -/
def marginalsValid (certificate : V13ChargedPublicTransportCertificate) : Bool :=
  certificate.leftWorlds.all (fun world =>
      certificate.outgoing world == certificate.rightWorlds.length) &&
    certificate.rightWorlds.all (fun world =>
      certificate.incoming world == certificate.leftWorlds.length)

/-- The constant potentials `u = 1`, `v = 0` are dual feasible on every
neutral-compatible opposite-phase edge. -/
def coefficientOneDualValid
    (certificate : V13ChargedPublicTransportCertificate) : Bool :=
  certificate.leftWorlds.all fun left =>
    certificate.rightWorlds.all fun right =>
      !certificate.neutralAgree left right ||
        decide (1 <= certificate.chargedDistance left right)

/-- Complete exact checker for a sharp coefficient-one transport
certificate. -/
def check (certificate : V13ChargedPublicTransportCertificate) : Bool :=
  decide (0 < certificate.leftWorlds.length) &&
    decide (0 < certificate.rightWorlds.length) &&
    decide (certificate.chargedMask < certificate.worldCount) &&
    decide (certificate.targetTable < 2 ^ certificate.worldCount) &&
    certificate.supportValid &&
    certificate.marginalsValid &&
    decide (certificate.scale =
      certificate.leftWorlds.length * certificate.rightWorlds.length) &&
    decide (certificate.objectiveNumerator = certificate.objective) &&
    decide (certificate.objectiveNumerator = certificate.scale) &&
    certificate.coefficientOneDualValid &&
    decide (certificate.dualNumerator = certificate.scale)

end V13ChargedPublicTransportCertificate

/-- Sharp one-bit transport: one unit from public world `1` to world `0`. -/
def v13ChargedPublicOneBitCertificate :
    V13ChargedPublicTransportCertificate where
  publicBitCount := 1
  targetTable := 1
  chargedMask := 1
  scale := 1
  objectiveNumerator := 1
  dualNumerator := 1
  flow := [{ left := 1, right := 0, amount := 1 }]

/-- Sharp two-bit transport, padded by one exactly matched neutral bit. -/
def v13ChargedPublicTwoBitCertificate :
    V13ChargedPublicTransportCertificate where
  publicBitCount := 2
  targetTable := 3
  chargedMask := 2
  scale := 4
  objectiveNumerator := 4
  dualNumerator := 4
  flow := [
    { left := 2, right := 0, amount := 2 },
    { left := 3, right := 1, amount := 2 }
  ]

/-- Sharp three-bit transport, padded by two exactly matched neutral bits. -/
def v13ChargedPublicThreeBitCertificate :
    V13ChargedPublicTransportCertificate where
  publicBitCount := 3
  targetTable := 15
  chargedMask := 4
  scale := 16
  objectiveNumerator := 16
  dualNumerator := 16
  flow := [
    { left := 4, right := 0, amount := 4 },
    { left := 5, right := 1, amount := 4 },
    { left := 6, right := 2, amount := 4 },
    { left := 7, right := 3, amount := 4 }
  ]

/-- Kernel-checked validity of all externally generated sharp transport
certificates. -/
theorem v13ChargedPublicTransportCertificates_valid :
    v13ChargedPublicOneBitCertificate.check = true ∧
      v13ChargedPublicTwoBitCertificate.check = true ∧
      v13ChargedPublicThreeBitCertificate.check = true := by
  decide

/-- Reusing a single charged public atom for every target does not localize
the coordinate sum: one unit is paid once per target coordinate. -/
def v13SharedChargedAtomCoordinateSum (targetCount : Nat) : Nat :=
  (Finset.range targetCount).sum fun _ => 1

theorem v13SharedChargedAtomCoordinateSum_eq (targetCount : Nat) :
    v13SharedChargedAtomCoordinateSum targetCount = targetCount := by
  simp [v13SharedChargedAtomCoordinateSum]

end Mettapedia.Computability.PNP
