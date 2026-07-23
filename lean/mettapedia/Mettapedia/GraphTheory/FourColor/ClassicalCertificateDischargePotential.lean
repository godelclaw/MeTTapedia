import Mettapedia.GraphTheory.FourColor.ClassicalCertificateDischargeRuleData
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateRotationHubProfile

/-!
# The classical rule-count potential on a rotation system

Each applicable discharging rule contributes one unit.  Rule multiplicities
are retained by counting the list rather than its underlying set.  The match
anchor is shifted two steps backwards around its face, exactly as in the
classical formulation, while the resulting potential is an ordinary integer
function on darts and therefore plugs directly into score conservation.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateDischargePotential

open ClassicalCertificateDischargeRuleData
open ClassicalCertificateDischargingScore
open ClassicalCertificateDischargingHubcapJoin
open ClassicalCertificatePresentationPattern
open ClassicalCertificateRotationHubProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

instance (profile : SectorProfile) (sector : Sector) :
    Decidable (SectorProfile.Fits profile sector) := by
  unfold SectorProfile.Fits FaceRange.Contains
  infer_instance

instance (profile : HubProfile) (pattern : Pattern) :
    Decidable (Pattern.Fits profile pattern) := by
  unfold Pattern.Fits
  infer_instance

noncomputable section

/-- Boolean test that an observed hub has exactly the central arity of a rule
and satisfies all of its second-neighborhood ranges. -/
def ruleMatches (profile : HubProfile) (rule : Pattern) : Bool :=
  decide (Pattern.Fits profile rule)

theorem ruleMatches_eq_true_iff
    (profile : HubProfile) (rule : Pattern) :
    ruleMatches profile rule = true ↔ Pattern.Fits profile rule := by
  simp [ruleMatches]

/-- Applicable-rule count, retaining deliberate duplicate rules. -/
def ruleCount (ruleList : List Pattern) (profile : HubProfile) : Nat :=
  ruleList.countP (ruleMatches profile)

/-- Move an anchor two steps backwards around its facial cycle. -/
def inverseFaceTwoDart (RS : RotationSystem V E) (dart : RS.D) : RS.D :=
  ((RS.phi.symm : RS.D → RS.D)^[2]) dart

/-- Integer potential supplied by a list of local rules. -/
def dartRulePotential (RS : RotationSystem V E)
    (ruleList : List Pattern) (dart : RS.D) : Int :=
  ruleCount ruleList (hubProfile RS (inverseFaceTwoDart RS dart))

/-- The 71-entry symmetrized classical potential. -/
def classicalPotential (RS : RotationSystem V E) (dart : RS.D) : Int :=
  dartRulePotential RS rules dart

theorem dartRulePotential_nonnegative
    (RS : RotationSystem V E) (ruleList : List Pattern) (dart : RS.D) :
    0 ≤ dartRulePotential RS ruleList dart := by
  exact Int.natCast_nonneg _

theorem classicalPotential_nonnegative
    (RS : RotationSystem V E) (dart : RS.D) :
    0 ≤ classicalPotential RS dart :=
  dartRulePotential_nonnegative RS rules dart

/-- A semantic bound on the finite rule count is exactly the potential bound
needed by the global discharging argument. -/
theorem classicalPotential_le_five_of_ruleCount
    (RS : RotationSystem V E)
    (hcount : ∀ root : RS.D, ruleCount rules (hubProfile RS root) ≤ 5)
    (dart : RS.D) : classicalPotential RS dart ≤ 5 := by
  unfold classicalPotential dartRulePotential
  exact_mod_cast hcount (inverseFaceTwoDart RS dart)

/-- Once the local rule-count checker supplies its sharp bound, global score
conservation selects a positive actual hub in the finite presentation range. -/
theorem exists_positive_small_classical_hub
    (RS : RotationSystem V E) (hsphere : OrbitSphericalCubicMapData RS)
    (hminimum : ∀ dart : RS.D, 5 ≤ faceArity RS dart)
    (hcount : ∀ root : RS.D, ruleCount rules (hubProfile RS root) ≤ 5) :
    ∃ root : RS.D,
      0 < hubScore RS (classicalPotential RS) root ∧
        5 ≤ (RS.faceOrbit root).card ∧
          (RS.faceOrbit root).card < 12 ∧
            Pattern.Fits (hubProfile RS root)
              (Pattern.free (RS.faceOrbit root).card) := by
  exact exists_positive_small_hubProfile_fits_free RS hsphere
    (classicalPotential RS) (classicalPotential_nonnegative RS)
    (classicalPotential_le_five_of_ruleCount RS hcount) hminimum

end

end ClassicalCertificateDischargePotential

end Mettapedia.GraphTheory.FourColor
