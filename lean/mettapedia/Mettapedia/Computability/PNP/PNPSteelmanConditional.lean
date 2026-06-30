import Mettapedia.Computability.PNP.KernelFlipInvolution
import Mettapedia.Computability.PNP.NoThreadingLemma

/-!
# PNP steelman conditional after the kernel-flip repair

The repaired lower-bound side has two finite components:

* `KernelFlipInvolution` gives exact local neutrality by a kernel-vector flip in
  the Valiant-Vazirani linear layer.
* `NoThreadingLemma` shows why a neutral local statistic cannot also be
  sufficient for the full deterministic witness bit.

What remains is the single open input named here as
`StarSWAverageCaseWitnessBitHardness`: average-case witness-bit hardness for
short predictors on the masked isolated ensemble.  The theorem
`pnp_steelman_conditional` proves only the conditional plumbing from exact
kernel-flip neutrality plus this open SW/hardness input through the
pivot/independence, compression-from-success, and self-reduction clash
interfaces.  It does not assert an unconditional P versus NP separation.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/--
An abstract finite bookkeeping interface for the non-SW part of the repaired PNP
chain.

The fields are deliberately small: `pivotIndependenceStep` is the finite
pivot/independence product bound, `compressionFromSuccessStep` is the
enumerative coding step, and `selfReductionClashStep` is the final upper/lower
clash.  The only open route input is represented separately by
`StarSWAverageCaseWitnessBitHardness`.
-/
structure PNPConditionalFramework where
  Predictor : Type
  short : Predictor -> Prop
  uLocal : Predictor -> Prop
  pivotSuccess : Predictor -> Nat
  tupleSuccess : Predictor -> Nat
  halfBudget : Nat
  halfPlusSlackBudget : Nat
  smallSuccessBudget : Nat
  targetBlocks : Nat
  etaTimes : Nat -> Nat
  kpolyAt : Nat -> Nat
  pNeNPClaim : Prop
  pivotIndependenceStep :
    ∀ A : Predictor,
      pivotSuccess A ≤ halfPlusSlackBudget ->
        tupleSuccess A ≤ smallSuccessBudget
  compressionFromSuccessStep :
    (∀ A : Predictor, short A -> tupleSuccess A ≤ smallSuccessBudget) ->
      etaTimes targetBlocks ≤ kpolyAt targetBlocks
  selfReductionClashStep :
    etaTimes targetBlocks ≤ kpolyAt targetBlocks -> pNeNPClaim

/--
The exact local half-bound supplied by the kernel-flip involution.  In the
intended model, this comes from `kernelFlip_exactNeutrality_card`: every
`u`-local predictor is paired across the witness-bit fibers and therefore has no
better than half pivot success.
-/
structure KernelFlipNeutrality (F : PNPConditionalFramework) where
  exactLocalHalfBound :
    ∀ A : F.Predictor, F.uLocal A -> F.pivotSuccess A ≤ F.halfBudget
  halfBudget_le_starBudget :
    F.halfBudget ≤ F.halfPlusSlackBudget

/--
The single open input: the SW/average-case witness-bit hardness principle.

It says that the exact half-bound for `u`-local predictors transfers to all
short predictors.  This is the irreducible average-case hardness hypothesis; it
is not proved here.
-/
structure StarSWAverageCaseWitnessBitHardness
    (F : PNPConditionalFramework) where
  transferLocalNeutralityToShortPredictors :
    (∀ A : F.Predictor, F.uLocal A -> F.pivotSuccess A ≤ F.halfBudget) ->
      ∀ A : F.Predictor, F.short A -> F.pivotSuccess A ≤ F.halfBudget

/-- Kernel-flip neutrality plus the open SW input gives the short-predictor
pivot bound used by the rest of the chain. -/
theorem pivotBound_of_kernelFlipNeutrality_starSW
    {F : PNPConditionalFramework}
    (hKernel : KernelFlipNeutrality F)
    (hSW : StarSWAverageCaseWitnessBitHardness F)
    (A : F.Predictor) (hshort : F.short A) :
    F.pivotSuccess A ≤ F.halfPlusSlackBudget :=
  le_trans
    (hSW.transferLocalNeutralityToShortPredictors
      hKernel.exactLocalHalfBound A hshort)
    hKernel.halfBudget_le_starBudget

/-- Step 3: pivot/independence converts the SW pivot bound into small tuple
success for every short predictor. -/
theorem smallSuccess_of_kernelFlipNeutrality_starSW
    {F : PNPConditionalFramework}
    (hKernel : KernelFlipNeutrality F)
    (hSW : StarSWAverageCaseWitnessBitHardness F) :
    ∀ A : F.Predictor, F.short A ->
      F.tupleSuccess A ≤ F.smallSuccessBudget := by
  intro A hshort
  exact
    F.pivotIndependenceStep A
      (pivotBound_of_kernelFlipNeutrality_starSW hKernel hSW A hshort)

/-- Step 4: compression from success gives the distributional `K^poly` lower
bound. -/
theorem kpolyLowerBound_of_kernelFlipNeutrality_starSW
    {F : PNPConditionalFramework}
    (hKernel : KernelFlipNeutrality F)
    (hSW : StarSWAverageCaseWitnessBitHardness F) :
    F.etaTimes F.targetBlocks ≤ F.kpolyAt F.targetBlocks :=
  F.compressionFromSuccessStep
    (smallSuccess_of_kernelFlipNeutrality_starSW hKernel hSW)

/--
The repaired steelman conditional: exact kernel-flip neutrality plus the open
average-case witness-bit hardness input implies the abstract PNP separation
endpoint supplied by the framework.

No unconditional separation is asserted; the `StarSWAverageCaseWitnessBitHardness`
field is the explicit remaining hypothesis.
-/
theorem pnp_steelman_conditional
    {F : PNPConditionalFramework}
    (hKernel : KernelFlipNeutrality F)
    (hSW : StarSWAverageCaseWitnessBitHardness F) :
    F.pNeNPClaim :=
  F.selfReductionClashStep
    (kpolyLowerBound_of_kernelFlipNeutrality_starSW hKernel hSW)

/-! ## Toy inhabitant for the conditional interface -/

def toyPNPConditionalFramework : PNPConditionalFramework where
  Predictor := Unit
  short := fun A => A = ()
  uLocal := fun A => A = ()
  pivotSuccess := fun _ => 1
  tupleSuccess := fun _ => 1
  halfBudget := 1
  halfPlusSlackBudget := 1
  smallSuccessBudget := 1
  targetBlocks := 2
  etaTimes := fun _ => 1
  kpolyAt := fun _ => 1
  pNeNPClaim := Unit = Unit
  pivotIndependenceStep := by
    intro A hA
    exact Nat.le_refl 1
  compressionFromSuccessStep := by
    intro hsmall
    exact Nat.le_refl 1
  selfReductionClashStep := by
    intro hlower
    rfl

def toyPNPKernelFlipNeutrality :
    KernelFlipNeutrality toyPNPConditionalFramework where
  exactLocalHalfBound := by
    intro A hLocal
    cases A
    exact Nat.le_refl 1
  halfBudget_le_starBudget := Nat.le_refl 1

def toyPNPStarSW :
    StarSWAverageCaseWitnessBitHardness toyPNPConditionalFramework where
  transferLocalNeutralityToShortPredictors := by
    intro hLocalHalf A hshort
    exact hLocalHalf A hshort

theorem toyPNP_smallSuccess_nonvacuous :
    ∀ A : toyPNPConditionalFramework.Predictor,
      toyPNPConditionalFramework.short A ->
        toyPNPConditionalFramework.tupleSuccess A ≤
          toyPNPConditionalFramework.smallSuccessBudget :=
  smallSuccess_of_kernelFlipNeutrality_starSW
    toyPNPKernelFlipNeutrality toyPNPStarSW

theorem toyPNP_kpolyLowerBound_nonvacuous :
    toyPNPConditionalFramework.etaTimes
        toyPNPConditionalFramework.targetBlocks ≤
      toyPNPConditionalFramework.kpolyAt
        toyPNPConditionalFramework.targetBlocks :=
  kpolyLowerBound_of_kernelFlipNeutrality_starSW
    toyPNPKernelFlipNeutrality toyPNPStarSW

theorem toy_pnp_steelman_conditional_nonvacuous :
    toyPNPConditionalFramework.pNeNPClaim :=
  pnp_steelman_conditional
    toyPNPKernelFlipNeutrality toyPNPStarSW

end Mettapedia.Computability.PNP
