import KrennCollapseComponentContainmentCertificates
import KrennCollapseFeasibility
import KrennCollapseReductionDataAgreement

/-!
The top-down/bottom-up connector for the reduced C6 all-collapse locus.

The raw eighteen determinant equations first imply the fourteen reduced
binomial equations.  Their nonzero support is therefore Boolean-feasible,
so the kernel-checked support cover selects a stratum.  The concrete
certificate attached to that same stratum then makes every generator of its
selected component vanish at the original reduced valuation.

This is deliberately a component-membership theorem, not yet a claim that
all component ideals have been refuted by the carrier-tree corpus.
-/

namespace Krenn.CollapseStratumSound

open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.CollapseReductionDataAgreement
open Krenn.CollapseFeasibility
open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData
open Krenn.CollapseComponentContainmentCertificates

/-- Every raw all-collapse valuation belongs to a component selected by the
same support stratum certified by the global cover. -/
theorem raw_collapse_stratum_sound
    {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (values : Fin 30 → R) (collapse : SatisfiesRawCollapse values) :
    ∃ stratum ∈ strata,
      Covers stratum (supportPattern (reduceRaw values)) ∧
        ∀ generator ∈ componentGenerators stratum.component,
          generatorEval (reduceRaw values) generator = 0 := by
  have feasible : Feasible (supportPattern (reduceRaw values)) :=
    feasible_of_raw_collapse values collapse
  have support : ∀ coordinate,
      supportPattern (reduceRaw values) coordinate ↔
        reduceRaw values coordinate ≠ 0 := by
    intro coordinate
    exact supportPattern_iff (reduceRaw values) coordinate
  exact exists_covered_component_generators_vanish
    (supportPattern (reduceRaw values)) feasible (reduceRaw values)
    support (containment_relations_of_raw_collapse values collapse)

end Krenn.CollapseStratumSound

#print axioms Krenn.CollapseStratumSound.raw_collapse_stratum_sound
