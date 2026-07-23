import Mettapedia.GraphTheory.FourColor.ClassicalCertificateDischargeRuleBoundData

/-!
# Sharp local bound modulo nine discharge obstructions

The generated split trees isolate every profile on which six classical
discharging rules can apply.  Outside nine explicit boxes, the classical
potential is therefore at most five.  This theorem is independent of any
particular rotation system; later geometric lemmas exclude the nine boxes on
an actual minimal map.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateDischargeRuleBound

open ClassicalCertificateDischargePotential
open ClassicalCertificateDischargeRuleBoundData
open ClassicalCertificateDischargeRuleData
open ClassicalCertificatePresentationPattern
open ClassicalCertificateRuleBound

/-- Every extracted rule has central arity at most eight. -/
theorem rule_length_le_eight :
    ∀ rule ∈ rules, rule.length ≤ 8 := by
  decide

/-- A matched rule has the same central arity as the observed hub. -/
theorem profile_length_eq_rule_length_of_ruleMatches
    {profile : HubProfile} {rule : Pattern}
    (hmatch : ruleMatches profile rule = true) :
    profile.length = rule.length := by
  exact (ruleMatches_eq_true_iff profile rule).1 hmatch |>.length_eq

/-- No extracted rule applies to a hub of arity at least nine. -/
theorem ruleCount_eq_zero_of_eight_lt_length
    {profile : HubProfile} (hlength : 8 < profile.length) :
    ruleCount rules profile = 0 := by
  unfold ruleCount
  apply List.countP_eq_zero.mpr
  intro rule hrule hmatch
  have hmatchTrue : ruleMatches profile rule = true := by
    exact hmatch
  have heq :=
    profile_length_eq_rule_length_of_ruleMatches hmatchTrue
  have hle := rule_length_le_eight rule hrule
  omega

/-- The arity-five split tree proves the sharp dichotomy. -/
theorem ruleCount_le_five_or_obstruction_of_fits_free_five
    {profile : HubProfile}
    (hfits : Pattern.Fits profile (Pattern.free 5)) :
    ruleCount rules profile ≤ 5 ∨
      ∃ obstruction ∈ obstructions,
        Pattern.Fits profile obstruction := by
  exact BoundCode.check_sound check5_eq_true hfits

/-- The arity-six split tree proves the sharp dichotomy. -/
theorem ruleCount_le_five_or_obstruction_of_fits_free_six
    {profile : HubProfile}
    (hfits : Pattern.Fits profile (Pattern.free 6)) :
    ruleCount rules profile ≤ 5 ∨
      ∃ obstruction ∈ obstructions,
        Pattern.Fits profile obstruction := by
  exact BoundCode.check_sound check6_eq_true hfits

/-- The arity-seven split tree proves the sharp dichotomy. -/
theorem ruleCount_le_five_or_obstruction_of_fits_free_seven
    {profile : HubProfile}
    (hfits : Pattern.Fits profile (Pattern.free 7)) :
    ruleCount rules profile ≤ 5 ∨
      ∃ obstruction ∈ obstructions,
        Pattern.Fits profile obstruction := by
  exact BoundCode.check_sound check7_eq_true hfits

/-- The arity-eight split tree proves the sharp dichotomy; its obstruction
branch is empty, but retaining the common statement makes composition easy. -/
theorem ruleCount_le_five_or_obstruction_of_fits_free_eight
    {profile : HubProfile}
    (hfits : Pattern.Fits profile (Pattern.free 8)) :
    ruleCount rules profile ≤ 5 ∨
      ∃ obstruction ∈ obstructions,
        Pattern.Fits profile obstruction := by
  exact BoundCode.check_sound check8_eq_true hfits

/-- For every hub in the minimum-face-size range, six applicable rules force
one of exactly nine explicit local obstruction boxes. -/
theorem ruleCount_le_five_or_obstruction_of_fits_free
    {profile : HubProfile} {arity : Nat}
    (hfive : 5 ≤ arity)
    (hfits : Pattern.Fits profile (Pattern.free arity)) :
    ruleCount rules profile ≤ 5 ∨
      ∃ obstruction ∈ obstructions,
        Pattern.Fits profile obstruction := by
  by_cases h5 : arity = 5
  · subst arity
    exact ruleCount_le_five_or_obstruction_of_fits_free_five hfits
  by_cases h6 : arity = 6
  · subst arity
    exact ruleCount_le_five_or_obstruction_of_fits_free_six hfits
  by_cases h7 : arity = 7
  · subst arity
    exact ruleCount_le_five_or_obstruction_of_fits_free_seven hfits
  by_cases h8 : arity = 8
  · subst arity
    exact ruleCount_le_five_or_obstruction_of_fits_free_eight hfits
  left
  have hprofileLength : profile.length = arity := by
    simpa [Pattern.free] using hfits.length_eq
  have hlarge : 8 < profile.length := by
    omega
  rw [ruleCount_eq_zero_of_eight_lt_length hlarge]
  omega

end ClassicalCertificateDischargeRuleBound

end Mettapedia.GraphTheory.FourColor
