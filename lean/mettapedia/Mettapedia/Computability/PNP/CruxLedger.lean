/-!
# PNP crux ledger primitives

This module contains the route-repair ledger vocabulary used by the PNP crux
synthesis files.  It deliberately contains only the coarse repair taxonomy and
packet interface, leaving theorem-backed coverage proofs in the synthesis
modules that import it.
-/

namespace Mettapedia.Computability.PNP

/-- Coarse repair classes that matter to the current PNP crux-status audit. -/
inductive PNPRepairClass where
  /-- Same-source Boolean recodings of a conditioned bit. -/
  | sameSourceBooleanRecoding
  /-- Same-source deterministic fibers into an arbitrary decidable codomain. -/
  | sameSourceDeterministicFiber
  /-- Repeated positive-mass pivot in the v13 fielded switching route. -/
  | repeatedPositiveFieldedPivot
  /-- Positive-mass accumulated histories whose next success event is already
  logically forced, even without literal event repetition. -/
  | forcedPositiveFieldedStep
  /-- Concrete fixed-field bad cell in the v13 switching route. -/
  | fixedFieldBadCell
  /-- Refining a bad field cell without changing the underlying balance defect. -/
  | fieldRefinementOfBadCell
  /-- Invariant-projection or invariant-score advantage repairs. -/
  | invariantScoreRepair
  /-- Bounded side-channel resolution repairs. -/
  | boundedSideChannelRepair
  /-- Short global decoder repairs without local readout constancy. -/
  | shortGlobalDecoderRepair
  /-- v13 CD evidence-normalization repairs that must classify every
  target-relevant non-neutral atom as safe-buffer or hidden-gauge. -/
  | cdEvidenceNormalization
  /-- v13 trace-capture repairs that replace target-relevant observers by
  finite traces. -/
  | traceCaptureFactorization
  /-- v13 atomic-evidence budget repairs that bound coordinate-summed cost
  without double-counting positive-cost atoms. -/
  | atomicEvidenceBudget
  /-- v13 ACCEI/PNLD repairs that must instantiate finite Markov pruning and
  the finite sequential product skeleton. -/
  | acceiEnvelopeProduct
  /-- Finite counting kernel for a clocked `s`-bit decoder family. -/
  | clockedFiniteUniformKernel
  /-- Residual side information not determined by the conditioned source bit. -/
  | residualSideInformation
  /-- Randomized post-conditioning residual objects. -/
  | randomizedResidual
  /-- Finite-count approximate decorrelation on same-source coupled,
  anti-coupled, or deterministic distinguishing-fiber surfaces. -/
  | sameSourceFiniteCountApproximation
  /-- Quantitatively approximate decorrelation replacing exact finite counting. -/
  | approximateDecorrelation
  /-- Remaining manuscript-specific exact-visible / clocked `Kpoly` bridge
  from product success. -/
  | kpolyCompressionBridge
  deriving DecidableEq, Repr

/-- A crux packet is represented by the repair classes it covers. -/
structure PNPCruxPacket where
  covers : PNPRepairClass → Prop

/-- A packet is stop-grade only if it covers every repair class in this ledger. -/
def PNPCruxPacket.StopGrade (packet : PNPCruxPacket) : Prop :=
  ∀ repair : PNPRepairClass, packet.covers repair

/-- One packet extends another when it covers every repair class covered by the
base packet. -/
def PNPCruxPacket.Extends (extension base : PNPCruxPacket) : Prop :=
  ∀ repair : PNPRepairClass, base.covers repair → extension.covers repair

/-- A packet covers every repair class in a named finite list. -/
def PNPCruxPacket.CoversList (packet : PNPCruxPacket)
    (repairs : List PNPRepairClass) : Prop :=
  ∀ repair : PNPRepairClass, repair ∈ repairs → packet.covers repair

/-- Missing any ledger repair class rules out stop-grade status. -/
theorem PNPCruxPacket.not_stopGrade_of_not_covers
    {packet : PNPCruxPacket} {repair : PNPRepairClass}
    (hmiss : ¬ packet.covers repair) :
    ¬ packet.StopGrade := by
  intro hstop
  exact hmiss (hstop repair)

end Mettapedia.Computability.PNP
