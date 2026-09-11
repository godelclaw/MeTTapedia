import Mettapedia.GraphTheory.FourColor.BoundedCubicRotationTrace
import Mettapedia.GraphTheory.FourColor.GoertzelV24SphericalRouteNativeBaseReflection

/-!
# The constructed bounded spherical-code audit at the existing base consumer

This instantiates the finite-base reflection with concrete numerical data:
the rotation-code carrier, its executable admissibility filter, and its
executable colouring test. Trace coverage and colouring adequacy have been
proved for every bounded target map. Only the actual empty-bad-set audit is
left as an input to this base consumer; no successful audit at a reduction
threshold is asserted. The uncompressed finite carrier is not a claim of an
efficient enumeration or an optimized interface closure.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundedCubicColourTrace

open GoertzelV24TwoEdgeCutMinimality GoertzelV24SphericalReductiveAssembly
open GoertzelV24SphericalRouteNativeBaseReflection SimpleGraphDartRotation

instance (n m : Nat) : DecidableEq (RotationCode n m) := by
  letI : DecidableEq (Code n m) :=
    inferInstanceAs (DecidableEq (Fin n → Fin 3 → Fin m))
  letI : DecidableEq (Equiv.Perm (Position n) × Equiv.Perm (Position n)) :=
    inferInstanceAs (DecidableEq (Equiv.Perm (Fin n × Fin 3) × Equiv.Perm (Fin n × Fin 3)))
  exact instDecidableEqProd

instance (bound : Nat) : DecidableEq (BoundedRotationCode bound) := by
  unfold BoundedRotationCode
  infer_instance

/-- The actual numerical codes that pass structural sphere checks but fail
the actual colouring test. -/
def badSphericalCodes (bound : Nat) : Finset (BoundedRotationCode bound) :=
  (sphericalEnvelope bound).filter fun code =>
    hasColouring code.2.2.incidence = false

def baseAudit (bound : Nat) : Bool := decide (badSphericalCodes bound = ∅)

universe u

noncomputable def sphericalBaseReflection (bound : Nat) :
    TaitBaseReflection.{u, 0} bound (BoundedRotationCode bound) where
  Necessary code := hasColouring code.2.2.incidence = false
  reachable := sphericalEnvelope bound
  trace {V} _ _ {G} _ rotation mapData hbound := by
    classical
    letI : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
    exact rotationTrace rotation.toRotationSystem mapData.spherical.cubic hbound
  trace_mem_reachable {V} _ _ {G} _ rotation mapData hbound := by
    classical
    letI : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
    exact rotationTrace_mem_sphericalEnvelope rotation.toRotationSystem mapData hbound
  necessary_of_not_colorable {V} _ _ {G} _ rotation mapData hbound hnot := by
    classical
    letI : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
    exact (rotationTrace_bad_iff rotation.toRotationSystem mapData.spherical.cubic hbound).2 hnot

/-- The existing base consumer, now with coverage and adequacy discharged
by the numerical encoding rather than left as hypotheses. -/
theorem taitBaseVerifiedAt_of_badSphericalCodes_eq_empty (bound : Nat)
    (haudit : badSphericalCodes bound = ∅) : TaitBaseVerifiedAt.{u} bound := by
  letI : DecidablePred (sphericalBaseReflection.{u} bound).Necessary :=
    fun code => inferInstanceAs (Decidable (hasColouring code.2.2.incidence = false))
  exact @TaitBaseReflection.taitBaseVerifiedAt_of_filter_eq_empty
    bound (BoundedRotationCode bound) _ (sphericalBaseReflection.{u} bound) _ haudit

theorem taitBaseVerifiedAt_of_baseAudit (bound : Nat)
    (haudit : baseAudit bound = true) : TaitBaseVerifiedAt.{u} bound := by
  apply taitBaseVerifiedAt_of_badSphericalCodes_eq_empty bound
  exact of_decide_eq_true haudit

/-! Vacuous tiny-domain controls: no connected loopless cubic map has at most
one vertex. These test the complete evaluator, not the substantive base. -/

theorem baseAudit_zero : baseAudit 0 = true := by decide +kernel
theorem baseAudit_one : baseAudit 1 = true := by decide +kernel

end Mettapedia.GraphTheory.FourColor.BoundedCubicColourTrace
