import Mettapedia.Computability.PNP.CruxLedger

/-!
# PNP randomized-residual subrepair ledger

Static subrepair taxonomy and covered-subrepair list for this branch of
the PNP crux ledger.  The theorem-backed coverage proofs live in the
corresponding semantic coverage modules.
-/

namespace Mettapedia.Computability.PNP

/-- Narrow randomized-residual subrepair classes covered by the current
finite-coin product-space obstruction.  These do not close arbitrary randomized
residual repairs; they force any positive finite-coin advantage claim to expose
a positive joint-support resolving coin. -/
inductive PNPRandomizedResidualSubrepairClass where
  /-- A finite-coin randomized residual is an ordinary side channel on the
  source/coin product. -/
  | productSideChannelBudget
  /-- If the residual is unresolved on every positive joint-support pair, its
  joint resolving mass is zero. -/
  | supportwiseUnresolvedZeroMass
  /-- A supportwise-unresolved finite-coin residual cannot produce positive
  doubled advantage. -/
  | supportwiseUnresolvedNoAdvantage
  /-- Positive finite-coin randomized-residual advantage exposes a
  positive-weight source/coin pair where the residual changes across the
  involution. -/
  | positiveAdvantageResolutionWitness
  /-- Positive finite-coin randomized-residual advantage already exposes a
  deterministic positive-weight coin slice with positive ordinary resolving
  mass. -/
  | positiveAdvantageDeterministicCoinSliceWitness
  /-- Even strict half-accuracy finite-coin randomized-residual advantage is
  already witnessed by a deterministic positive-weight coin slice with
  positive ordinary resolving mass. -/
  | strictHalfDeterministicCoinSliceWitness
  /-- Even strict half-accuracy finite-coin randomized-residual advantage is
  already witnessed by a deterministic positive-weight coin slice carrying the
  ordinary invariant-base residual-side-information obstruction package. -/
  | strictHalfDeterministicCoinSliceResidualObstructionPackage
  /-- The exact post-switch invariant-projection surface inherits the same
  supportwise-unresolved blocker. -/
  | postSwitchSupportwiseUnresolvedNoAdvantage
  /-- On the exact post-switch surface, exact-input-invariant support blocks
  strict half-accuracy finite-coin randomized-residual advantage. -/
  | postSwitchExactSupportNoStrictHalfAdvantage
  /-- On the exact post-switch surface, positive finite-coin advantage exposes
  a positive-weight input/coin pair resolving the local-input switch. -/
  | postSwitchPositiveAdvantageResolutionWitness
  /-- On the exact post-switch surface, positive finite-coin advantage already
  exposes a deterministic positive-weight coin slice with positive ordinary
  resolving mass. -/
  | postSwitchPositiveAdvantageDeterministicCoinSliceWitness
  /-- On the exact post-switch surface, even strict half-accuracy finite-coin
  advantage already exposes a deterministic positive-weight coin slice with
  positive ordinary resolving mass. -/
  | postSwitchStrictHalfDeterministicCoinSliceWitness
  /-- On the exact post-switch surface, even strict half-accuracy finite-coin
  advantage already exposes a deterministic positive-weight coin slice
  carrying the ordinary invariant-projection residual obstruction package. -/
  | postSwitchStrictHalfDeterministicCoinSliceResidualObstructionPackage
  deriving DecidableEq, Repr

/-- The exact narrow randomized-residual subrepairs covered by the current
finite-coin product-space obstruction stack. -/
def currentPNPRandomizedResidualCoveredSubrepairs :
    List PNPRandomizedResidualSubrepairClass :=
  [.productSideChannelBudget,
    .supportwiseUnresolvedZeroMass,
    .supportwiseUnresolvedNoAdvantage,
    .positiveAdvantageResolutionWitness,
    .positiveAdvantageDeterministicCoinSliceWitness,
    .strictHalfDeterministicCoinSliceWitness,
    .strictHalfDeterministicCoinSliceResidualObstructionPackage,
    .postSwitchSupportwiseUnresolvedNoAdvantage,
    .postSwitchExactSupportNoStrictHalfAdvantage,
    .postSwitchPositiveAdvantageResolutionWitness,
    .postSwitchPositiveAdvantageDeterministicCoinSliceWitness,
    .postSwitchStrictHalfDeterministicCoinSliceWitness,
    .postSwitchStrictHalfDeterministicCoinSliceResidualObstructionPackage]

/-- The narrow randomized-residual subrepair coverage list is exact. -/
theorem currentPNPRandomizedResidualCoveredSubrepairs_exact
    (repair : PNPRandomizedResidualSubrepairClass) :
    repair ∈ currentPNPRandomizedResidualCoveredSubrepairs := by
  cases repair <;> simp [currentPNPRandomizedResidualCoveredSubrepairs]

end Mettapedia.Computability.PNP
