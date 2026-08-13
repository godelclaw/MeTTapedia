import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalFamily
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16JointTraceRankTransfer

/-!
# OUR field-eight kernel theorem for the complete physical three-cut family

The finite `210`-label family is already realized as actual fundamental-trace
generators and mapped into the coordinate-free joint relation submodule.  This
module proves a semantic field-sector fact about that realization: every
linear combination of its Reynolds-averaged physical rows has zero exact
field-eight projection.  The proof is symbolic rather than a quotient
equality computation: all six row terms remain seven-field terms under trace
rewiring, and exact field-eight projection therefore removes each one.

This leaves the genuinely relevant seven-field trace-order coordinates open.
In particular, it neither proves annihilation by the cycle-profile correction
nor identifies a complete physical relation census or Wilson-functional
coordinates.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalFieldEight

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16FundamentalTracePhysicalFamily
open HypercubicDimension16JointTraceRankTransfer

/-- On a basis vector of OUR complete physical three-cut family, the induced
coordinate-free relation has zero field-eight invariant component. -/
theorem ourJointFieldEightInvariantProjection_fundamentalTraceSingle_zero
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ourJointFieldEightInvariantProjection policy
      (ourFundamentalTraceToJointRelation policy
        (Finsupp.single labels 1)) = 0 := by
  apply Subtype.ext
  change exactFieldEightProjection
      ((ourFundamentalTraceToJointRelation policy
        (Finsupp.single labels 1)).1).1 = 0
  rw [ourFundamentalTraceToJointRelation_single_val,
    ourExactFieldEightProjection_exactFieldOrbitReynolds,
    ourExactFieldEightProjection_fundamentalTraceGenerator_zero]
  simp

/-- The complete finite physical three-cut cochain family lies in the kernel
of OUR exact field-eight invariant projection, for either relation policy. -/
theorem ourJointFieldEightInvariantProjection_fundamentalTrace_zero
    (policy : PhysicalRelationPolicy)
    (cochain : OurFundamentalTraceCochainSpace) :
    ourJointFieldEightInvariantProjection policy
      (ourFundamentalTraceToJointRelation policy cochain) = 0 := by
  let combined := (ourJointFieldEightInvariantProjection policy).comp
    (ourFundamentalTraceToJointRelation policy)
  change combined cochain = 0
  induction cochain using Finsupp.induction_linear with
  | zero => simp [combined]
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single labels coefficient =>
      rw [show Finsupp.single labels coefficient =
          coefficient • Finsupp.single labels 1 by simp]
      simp only [map_smul]
      change coefficient •
        (ourJointFieldEightInvariantProjection policy
          (ourFundamentalTraceToJointRelation policy
            (Finsupp.single labels 1))) = 0
      rw [ourJointFieldEightInvariantProjection_fundamentalTraceSingle_zero]
      simp

#print axioms ourJointFieldEightInvariantProjection_fundamentalTraceSingle_zero
#print axioms ourJointFieldEightInvariantProjection_fundamentalTrace_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalFieldEight
