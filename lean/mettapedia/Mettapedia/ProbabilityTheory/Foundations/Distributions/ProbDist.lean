import ProbabilityTheory.Foundations.Distributions.ProbDist

/-! The canonical probability and valuation infrastructure is provided by the
standalone inference foundation. This namespace exposes the same declarations
to MeTTapedia consumers, without defining a second carrier or proof suite. -/

namespace Mettapedia.ProbabilityTheory.Foundations.Distributions
export _root_.ProbabilityTheory.Foundations.Distributions
  (ProbDist ProbDist.casesOn ProbDist.ctorIdx ProbDist.eq_one_implies_others_zero ProbDist.ext
   ProbDist.ext_iff ProbDist.le_one ProbDist.mk ProbDist.mk.inj ProbDist.mk.injEq
   ProbDist.mk.noConfusion ProbDist.mk.sizeOf_spec ProbDist.noConfusion ProbDist.noConfusionType ProbDist.nonneg
   ProbDist.p ProbDist.pointMass ProbDist.pointMass_apply ProbDist.rec ProbDist.recOn
   ProbDist.sum_one)
end Mettapedia.ProbabilityTheory.Foundations.Distributions
