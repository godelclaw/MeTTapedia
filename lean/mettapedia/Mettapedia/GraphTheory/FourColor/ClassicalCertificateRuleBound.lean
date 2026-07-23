import Mettapedia.GraphTheory.FourColor.ClassicalCertificateDischargePotential

/-!
# Finite split certificates for local rule-count bounds

A context is a box of face-size ranges.  Rules disjoint from that box cannot
match any profile in it, so counting the remaining rules gives a computable
upper bound.  A split certificate recursively partitions a context until this
bound is small, or records that the whole context lies in one of a finite list
of explicit obstruction boxes.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateRuleBound

open ClassicalCertificateDischargePotential
open ClassicalCertificatePresentationPattern

namespace FaceRange

/-- Two ranges have no common arity, respecting nine as the unbounded upper
endpoint. -/
def disjointChecker (left right : FaceRange) : Bool :=
  decide ((left.upper ≠ 9 ∧ left.upper < right.lower) ∨
    (right.upper ≠ 9 ∧ right.upper < left.lower))

theorem not_both_contains_of_disjointChecker
    {left right : FaceRange} {arity : Nat}
    (hcheck : disjointChecker left right = true)
    (hleft : left.Contains arity) :
    ¬ right.Contains arity := by
  simp only [disjointChecker, decide_eq_true_eq] at hcheck
  intro hright
  rcases hcheck with ⟨hleftFinite, hbefore⟩ |
      ⟨hrightFinite, hafter⟩
  · have hleftUpper := hleft.2.resolve_left hleftFinite
    have hrightLower := hright.1
    omega
  · have hrightUpper := hright.2.resolve_left hrightFinite
    have hleftLower := hleft.1
    omega

end FaceRange

namespace Sector

/-- Pointwise range-disjointness for one sector. -/
def disjointChecker (left right : Sector) : Bool :=
  FaceRange.disjointChecker left.spoke right.spoke ||
    (FaceRange.disjointChecker left.hat right.hat ||
      (FaceRange.disjointChecker left.fan1 right.fan1 ||
        (FaceRange.disjointChecker left.fan2 right.fan2 ||
          FaceRange.disjointChecker left.fan3 right.fan3)))

theorem not_both_fits_of_disjointChecker
    {left right : Sector} {profile : SectorProfile}
    (hcheck : disjointChecker left right = true)
    (hleft : profile.Fits left) :
    ¬ profile.Fits right := by
  simp only [disjointChecker, Bool.or_eq_true] at hcheck
  intro hright
  rcases hcheck with hspoke | hhat | hfan1 | hfan2 | hfan3
  · exact FaceRange.not_both_contains_of_disjointChecker
      hspoke hleft.1 hright.1
  · exact FaceRange.not_both_contains_of_disjointChecker
      hhat hleft.2.1 hright.2.1
  · exact FaceRange.not_both_contains_of_disjointChecker
      hfan1 hleft.2.2.1 hright.2.2.1
  · exact FaceRange.not_both_contains_of_disjointChecker
      hfan2 hleft.2.2.2.1 hright.2.2.2.1
  · exact FaceRange.not_both_contains_of_disjointChecker
      hfan3 hleft.2.2.2.2 hright.2.2.2.2

end Sector

namespace Pattern

/-- Two patterns are visibly disjoint either by length or at one aligned
sector. -/
def disjointChecker : Pattern → Pattern → Bool
  | [], [] => false
  | left :: lefts, right :: rights =>
      Sector.disjointChecker left right || disjointChecker lefts rights
  | _, _ => true

theorem not_both_fits_of_disjointChecker
    {left right : Pattern} {profile : HubProfile}
    (hcheck : disjointChecker left right = true)
    (hleft : ClassicalCertificatePresentationPattern.Pattern.Fits
      profile left) :
    ¬ ClassicalCertificatePresentationPattern.Pattern.Fits
      profile right := by
  induction left generalizing right profile with
  | nil =>
      cases right with
      | nil => simp [disjointChecker] at hcheck
      | cons right rights =>
          intro hright
          cases hleft
          cases hright
  | cons left lefts ih =>
      cases right with
      | nil =>
          intro hright
          cases hright
          cases hleft
      | cons right rights =>
          cases profile with
          | nil => cases hleft
          | cons observed rest =>
              cases hleft with
              | cons hleftHead hleftTail =>
                  simp only [disjointChecker, Bool.or_eq_true] at hcheck
                  intro hrightFits
                  cases hrightFits with
                  | cons hrightHead hrightTail =>
                      rcases hcheck with hhead | htail
                      · exact Sector.not_both_fits_of_disjointChecker
                          hhead hleftHead hrightHead
                      · exact ih htail hleftTail hrightTail

end Pattern

/-- Number of rules not visibly disjoint from a context. -/
def possibleRuleCount (ruleList : List Pattern) (context : Pattern) : Nat :=
  ruleList.countP (fun rule => !Pattern.disjointChecker context rule)

/-- A matching profile can activate no more rules than remain possible in
its containing context. -/
theorem ruleCount_le_possibleRuleCount
    (ruleList : List Pattern) {profile : HubProfile} {context : Pattern}
    (hcontext : Pattern.Fits profile context) :
    ruleCount ruleList profile ≤ possibleRuleCount ruleList context := by
  induction ruleList with
  | nil => simp [ruleCount, possibleRuleCount]
  | cons rule rules ih =>
      simp only [ruleCount, possibleRuleCount, List.countP_cons] at ih ⊢
      by_cases hmatch : ruleMatches profile rule = true
      · have hfits : Pattern.Fits profile rule :=
          (ruleMatches_eq_true_iff profile rule).1 hmatch
        have hdisjoint : Pattern.disjointChecker context rule = false := by
          apply Bool.eq_false_of_not_eq_true
          intro htrue
          exact Pattern.not_both_fits_of_disjointChecker
            htrue hcontext hfits
        simpa [hmatch, hdisjoint] using Nat.add_le_add_right ih 1
      · have hmatchFalse : ruleMatches profile rule = false :=
          Bool.eq_false_of_not_eq_true hmatch
        cases hpossible : (!Pattern.disjointChecker context rule)
        · simpa [hmatchFalse, hpossible] using ih
        · simpa [hmatchFalse, hpossible] using
            (le_trans ih (Nat.le_add_right _ 1))

/-- A proof tree either closes by a numeric bound, identifies a listed
obstruction box, or performs one legal binary range split. -/
inductive BoundCode where
  | bounded
  | obstruction (pattern : Pattern)
  | split (code : Pattern.SplitCode) (left right : BoundCode)
deriving Repr

/-- Kernel-reducible checker for a rule-bound proof tree. -/
def BoundCode.check (ruleList obstructions : List Pattern) (limit : Nat)
    (context : Pattern) : BoundCode → Bool
  | .bounded => decide (possibleRuleCount ruleList context ≤ limit)
  | .obstruction pattern =>
      decide (pattern ∈ obstructions) && context.subsetChecker pattern
  | .split code left right =>
      context.goodSplitChecker code &&
        (left.check ruleList obstructions limit (context.split code) &&
          right.check ruleList obstructions limit
            (context.split code.complement))

/-- Every accepted proof tree establishes the advertised dichotomy for every
actual profile in its root context. -/
theorem BoundCode.check_sound
    {ruleList obstructions : List Pattern} {limit : Nat}
    {context : Pattern} {code : BoundCode}
    (hcheck : code.check ruleList obstructions limit context = true) :
    ∀ {profile : HubProfile}, Pattern.Fits profile context →
      ruleCount ruleList profile ≤ limit ∨
        ∃ obstruction ∈ obstructions,
          Pattern.Fits profile obstruction := by
  induction code generalizing context with
  | bounded =>
      intro profile hcontext
      left
      have hbound : possibleRuleCount ruleList context ≤ limit := by
        simpa [BoundCode.check] using of_decide_eq_true hcheck
      exact le_trans (ruleCount_le_possibleRuleCount ruleList hcontext) hbound
  | obstruction pattern =>
      intro profile hcontext
      right
      simp only [BoundCode.check, Bool.and_eq_true] at hcheck
      refine ⟨pattern, ?_, hcontext.mono
        (Pattern.subsetChecker_sound hcheck.2)⟩
      simpa using of_decide_eq_true hcheck.1
  | split splitCode left right ihLeft ihRight =>
      intro profile hcontext
      simp only [BoundCode.check, Bool.and_eq_true] at hcheck
      rcases Pattern.fits_split_or profile context splitCode hcheck.1
          hcontext with hleft | hright
      · exact ihLeft hcheck.2.1 hleft
      · exact ihRight hcheck.2.2 hright

end ClassicalCertificateRuleBound

end Mettapedia.GraphTheory.FourColor
