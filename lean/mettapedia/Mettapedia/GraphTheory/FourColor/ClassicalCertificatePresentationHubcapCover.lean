import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationCertificate
import Mathlib.Tactic

/-!
# Linear cover certificates for presentation hubcaps

A hubcap is a short list of one-sector and two-sector upper bounds.  Its
cover certificate assigns each listed bound weight one or two so that every
sector occurs with total coefficient two.  The weighted upper bounds then
contradict the strictly positive central score.

This formulation separates the universal linear argument from the local
discharging computation that supplies each listed upper bound.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificatePresentationHubcapCover

open scoped BigOperators

open ClassicalCertificatePresentationCertificate
open ClassicalCertificatePresentationLogic

/-- Multiplicity of a sector in one singleton or pair term. -/
def termIncidence (term : HubcapTerm) (sector : Nat) : Nat :=
  (if sector = term.first then 1 else 0) +
    match term.second with
    | none => 0
    | some second => if sector = second then 1 else 0

/-- Every sector named by a term belongs to the hub. -/
def TermReferencesBelow (hubSize : Nat) (term : HubcapTerm) : Prop :=
  term.first < hubSize ∧
    match term.second with
    | none => True
    | some second => second < hubSize

instance (hubSize : Nat) (term : HubcapTerm) :
    Decidable (TermReferencesBelow hubSize term) := by
  unfold TermReferencesBelow
  cases term.second <;> infer_instance

/-- Linear expression bounded by one hubcap term. -/
def termValue (localScore : Nat → Int) (term : HubcapTerm) : Int :=
  localScore term.first +
    match term.second with
    | none => 0
    | some second => localScore second

/-- Number of appearances of one sector in a hubcap. -/
def occurrenceCount (terms : List HubcapTerm) (sector : Nat) : Nat :=
  (terms.map fun term => termIncidence term sector).sum

/-- Classical hubcap weight: a once-covered sector contributes twice, while
a twice-covered sector contributes once through each incident term. -/
def termWeight (terms : List HubcapTerm) (term : HubcapTerm) : Nat :=
  if occurrenceCount terms term.first = 1 then 2 else 1

/-- Total coefficient of one sector in the weighted hubcap. -/
def sectorCoefficient (terms : List HubcapTerm) (sector : Nat) : Int :=
  ∑ index : Fin terms.length,
    (termWeight terms (terms.get index) : Int) *
      termIncidence (terms.get index) sector

/-- The arity-dependent constant in the classical score bound. -/
def hubConstant (hubSize : Nat) : Int :=
  match hubSize - 5 with
  | 0 => 10
  | amount + 1 => -((amount * 10 : Nat) : Int)

/-- Weighted sum of the asserted local upper bounds. -/
def weightedBound (terms : List HubcapTerm) : Int :=
  ∑ index : Fin terms.length,
    (termWeight terms (terms.get index) : Int) *
      (terms.get index).bound

/-- Check that every referenced sector lies inside the hub. -/
def referencesCheck (hubSize : Nat) (terms : List HubcapTerm) : Bool :=
  terms.all fun term => decide (TermReferencesBelow hubSize term)

/-- Check that the weighted terms cover every sector exactly twice. -/
def coefficientCheck (hubSize : Nat) (terms : List HubcapTerm) : Bool :=
  (List.range hubSize).all fun sector =>
    decide (sectorCoefficient terms sector = 2)

/-- Check the final strict integer inequality.  The subtraction of one turns
the desired strict contradiction into a non-strict executable comparison. -/
def boundCheck (hubSize : Nat) (terms : List HubcapTerm) : Bool :=
  decide (2 * hubConstant hubSize - 1 + weightedBound terms ≤ 0)

/-- Complete linear cover check for one hubcap. -/
def coverCheck (hubSize : Nat) (terms : List HubcapTerm) : Bool :=
  referencesCheck hubSize terms &&
    (coefficientCheck hubSize terms && boundCheck hubSize terms)

/-- Semantic local-bound obligation associated to one hubcap term. -/
def TermBound (localScore : Nat → Int) (term : HubcapTerm) : Prop :=
  termValue localScore term ≤ term.bound

theorem referencesBelow_of_referencesCheck_eq_true
    {hubSize : Nat} {terms : List HubcapTerm}
    (hcheck : referencesCheck hubSize terms = true)
    {term : HubcapTerm} (hterm : term ∈ terms) :
    TermReferencesBelow hubSize term := by
  have haccepted := (List.all_eq_true.mp hcheck) term hterm
  exact of_decide_eq_true haccepted

theorem sectorCoefficient_eq_two_of_coefficientCheck_eq_true
    {hubSize : Nat} {terms : List HubcapTerm}
    (hcheck : coefficientCheck hubSize terms = true)
    {sector : Nat} (hsector : sector < hubSize) :
    sectorCoefficient terms sector = 2 := by
  have haccepted := (List.all_eq_true.mp hcheck) sector
    (List.mem_range.mpr hsector)
  exact of_decide_eq_true haccepted

theorem bound_inequality_of_boundCheck_eq_true
    {hubSize : Nat} {terms : List HubcapTerm}
    (hcheck : boundCheck hubSize terms = true) :
    2 * hubConstant hubSize - 1 + weightedBound terms ≤ 0 := by
  exact of_decide_eq_true hcheck

private theorem termValue_eq_incidenceSum
    {hubSize : Nat} {term : HubcapTerm}
    (hrefs : TermReferencesBelow hubSize term)
    (localScore : Nat → Int) :
    termValue localScore term =
      ∑ sector ∈ Finset.range hubSize,
        (termIncidence term sector : Int) * localScore sector := by
  rcases hrefs with ⟨hfirst, hsecond⟩
  cases hoption : term.second with
  | none =>
      simp [termValue, termIncidence, hoption, hfirst]
  | some second =>
      have hsecondLt : second < hubSize := by
        simpa [hoption] using hsecond
      simp only [termValue, termIncidence, hoption, Nat.cast_add,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero, add_mul,
        Finset.sum_add_distrib]
      simp [hfirst, hsecondLt]

private theorem weightedValue_eq_coefficientSum
    {hubSize : Nat} {terms : List HubcapTerm}
    (hrefs : referencesCheck hubSize terms = true)
    (localScore : Nat → Int) :
    (∑ index : Fin terms.length,
        (termWeight terms (terms.get index) : Int) *
          termValue localScore (terms.get index)) =
      ∑ sector ∈ Finset.range hubSize,
        sectorCoefficient terms sector * localScore sector := by
  classical
  calc
    (∑ index : Fin terms.length,
        (termWeight terms (terms.get index) : Int) *
          termValue localScore (terms.get index)) =
        ∑ index : Fin terms.length,
          ∑ sector ∈ Finset.range hubSize,
            (termWeight terms (terms.get index) : Int) *
              (termIncidence (terms.get index) sector : Int) *
                localScore sector := by
      apply Finset.sum_congr rfl
      intro index _hindex
      rw [termValue_eq_incidenceSum
        (referencesBelow_of_referencesCheck_eq_true hrefs
          (List.get_mem terms index))]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sector _hsector
      ring
    _ = ∑ sector ∈ Finset.range hubSize,
        ∑ index : Fin terms.length,
          (termWeight terms (terms.get index) : Int) *
            (termIncidence (terms.get index) sector : Int) *
              localScore sector := by
      rw [Finset.sum_comm]
    _ = ∑ sector ∈ Finset.range hubSize,
        sectorCoefficient terms sector * localScore sector := by
      apply Finset.sum_congr rfl
      intro sector _hsector
      unfold sectorCoefficient
      rw [Finset.sum_mul]

private theorem weightedValue_le_weightedBound
    {terms : List HubcapTerm} {localScore : Nat → Int}
    (hterms : ∀ term ∈ terms, TermBound localScore term) :
    (∑ index : Fin terms.length,
        (termWeight terms (terms.get index) : Int) *
          termValue localScore (terms.get index)) ≤
      weightedBound terms := by
  unfold weightedBound
  apply Finset.sum_le_sum
  intro index _hindex
  apply Int.mul_le_mul_of_nonneg_left
  · exact hterms (terms.get index) (List.get_mem terms index)
  · exact Int.natCast_nonneg _

/-- Soundness of the linear hubcap cover.  Local term bounds and an accepted
cover force the central score expression to be nonpositive. -/
theorem hubConstant_add_sum_nonpositive_of_coverCheck
    {hubSize : Nat} {terms : List HubcapTerm}
    {localScore : Nat → Int}
    (hcheck : coverCheck hubSize terms = true)
    (hterms : ∀ term ∈ terms, TermBound localScore term) :
    hubConstant hubSize +
        ∑ sector ∈ Finset.range hubSize, localScore sector ≤ 0 := by
  rcases Bool.and_eq_true_iff.mp hcheck with ⟨hrefs, hrest⟩
  rcases Bool.and_eq_true_iff.mp hrest with ⟨hcoefficients, hbound⟩
  have hweightedValue :
      (∑ index : Fin terms.length,
          (termWeight terms (terms.get index) : Int) *
            termValue localScore (terms.get index)) =
        2 * ∑ sector ∈ Finset.range hubSize, localScore sector := by
    rw [weightedValue_eq_coefficientSum hrefs]
    calc
      (∑ sector ∈ Finset.range hubSize,
          sectorCoefficient terms sector * localScore sector) =
          ∑ sector ∈ Finset.range hubSize, 2 * localScore sector := by
        apply Finset.sum_congr rfl
        intro sector hsector
        rw [sectorCoefficient_eq_two_of_coefficientCheck_eq_true
          hcoefficients (Finset.mem_range.mp hsector)]
      _ = 2 * ∑ sector ∈ Finset.range hubSize, localScore sector := by
        rw [Finset.mul_sum]
  have hlocalBound :
      2 * ∑ sector ∈ Finset.range hubSize, localScore sector ≤
        weightedBound terms := by
    rw [← hweightedValue]
    exact weightedValue_le_weightedBound hterms
  have hfinal := bound_inequality_of_boundCheck_eq_true hbound
  omega

/-- Traverse a presentation while checking only its hubcap cover data. -/
def allHubcapsCover (hubSize : Nat) : Code → Bool
  | .terminal .reducible => true
  | .terminal (.hubcap terms) => coverCheck hubSize terms
  | .similar _depth _similarity => true
  | .split _retainLeft _split left right =>
      allHubcapsCover hubSize left && allHubcapsCover hubSize right

end ClassicalCertificatePresentationHubcapCover

end Mettapedia.GraphTheory.FourColor
