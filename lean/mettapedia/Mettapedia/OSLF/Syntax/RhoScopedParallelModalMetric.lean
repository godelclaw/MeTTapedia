import Mettapedia.OSLF.Syntax.RhoScopedParallelModalEnumeration
import Mettapedia.OSLF.Syntax.RhoScopedParallelModalControls
import Mettapedia.GSLT.Logic.EnumerationMetric
import Mettapedia.OSLF.Framework.LogicalMetric

/-!
# Original rho interaction questions and FM's enumerated logical metric

Every finite parallel-context question occurs in the earned enumeration.
The independently computed firing interpretation supplies the answers. Its
dyadic weighted distance agrees with the first-difference observation metric,
so the existing observation quotient carries a genuine metric space.

Zero distance means agreement on all finite questions. It means actual IPO
bisimilarity under the explicit finite successor-cover hypothesis. Complete
conjunction adequacy, established separately, needs no such hypothesis.
Numerical ranks depend on the enumeration, and no runtime decidability,
communication-cost interpretation or funding statement is inferred.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoScopedParallelModalMetric

open Classical RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedParallelEvents RhoScopedParallelReactiveSystem RhoScopedParallelReactiveControls
open RhoScopedEquationEventControls
open RhoScopedParallelModalAdequacy RhoScopedParallelModalEnumeration
open Mettapedia.GSLT.Logic
open Mettapedia.OSLF.Framework.LogicalMetric

universe u

variable {Index : Type u} (rules : Index → ProcessRule) (admitted : Index → Prop)
  {context : Ctx sig}

def observations (context : Ctx sig) : BudgetedObservations (Process context) :=
  enumeratedTests (fun index => Finitary.Holds rules admitted (enumeration context index))

def scheme (context : Ctx sig) : ObservationScheme (Process context) (fun _ => Bool) where
  satisfies index first := decide (Finitary.Holds rules admitted (enumeration context index) first)

theorem answer_eq_iff (index : Nat) (first second : Process context) :
    (scheme rules admitted context).satisfies index first =
      (scheme rules admitted context).satisfies index second ↔
      (Finitary.Holds rules admitted (enumeration context index) first ↔
        Finitary.Holds rules admitted (enumeration context index) second) := by
  simp only [scheme, decide_eq_decide]

theorem indistinguishable_iff (first second : Process context) :
    (scheme rules admitted context).Indistinguishable first second ↔
      Finitary.LogicallyEquivalent rules admitted first second := by
  rw [ObservationScheme.Indistinguishable, funext_iff]
  change (∀ index, (scheme rules admitted context).satisfies index first =
    (scheme rules admitted context).satisfies index second) ↔ _
  constructor
  · intro same formula
    obtain ⟨index, rfl⟩ := enumeration_covers context formula
    exact (answer_eq_iff rules admitted index first second).mp (same index)
  · intro same index
    exact (answer_eq_iff rules admitted index first second).mpr (same _)

theorem distance_eq_zero_iff (first second : Process context) :
    (observations rules admitted context).distance first second = 0 ↔
      Finitary.LogicallyEquivalent rules admitted first second :=
  enumerated_zero_iff (Finitary.Holds rules admitted) (enumeration context)
    (enumeration_covers context) first second

theorem distance_eq_zero_iff_bisimilar
    (finite : Finitary.FiniteSuccessorCover rules admitted context) (first second : Process context) :
    (observations rules admitted context).distance first second = 0 ↔
      Bisimilar (rules := rules) (admitted := admitted) first second :=
  (distance_eq_zero_iff rules admitted first second).trans
    (Finitary.logicallyEquivalent_iff_bisimilar rules admitted finite first second)

theorem distance_first (first second : Process context) (index : Nat)
    (different : ¬ (Finitary.Holds rules admitted (enumeration context index) first ↔
      Finitary.Holds rules admitted (enumeration context index) second))
    (before : ∀ earlier, earlier < index →
      (Finitary.Holds rules admitted (enumeration context earlier) first ↔
        Finitary.Holds rules admitted (enumeration context earlier) second)) :
    (observations rules admitted context).distance first second = (1 / 2 : ℝ) ^ index :=
  enumerated_distance_first _ first second index different before

/-- The weighted and first-difference constructions agree on actual firing answers. -/
theorem distance_eq_scheme (first second : Process context) :
    (observations rules admitted context).distance first second =
      (scheme rules admitted context).distance first second := by
  classical
  by_cases same : (scheme rules admitted context).Indistinguishable first second
  · rw [(distance_eq_zero_iff rules admitted first second).mpr
      ((indistinguishable_iff rules admitted first second).mp same),
      ((scheme rules admitted context).distance_eq_zero_iff first second).mpr same]
  · rw [(scheme rules admitted context).distance_eq first second same]
    apply distance_first
    · intro agreement
      exact PiNat.apply_firstDiff_ne same
        ((answer_eq_iff rules admitted _ first second).mpr agreement)
    · intro earlier before
      exact (answer_eq_iff rules admitted earlier first second).mp
        (PiNat.apply_eq_of_lt_firstDiff before)

theorem distance_congr {first first' second second' : Process context}
    (left : Bisimilar (rules := rules) (admitted := admitted) first first')
    (right : Bisimilar (rules := rules) (admitted := admitted) second second') :
    (observations rules admitted context).distance first second =
      (observations rules admitted context).distance first' second' :=
  (observations rules admitted context).distance_congr
    (fun index => Finitary.logicallyEquivalent_of_bisimilar rules admitted left
      (enumeration context index))
    (fun index => Finitary.logicallyEquivalent_of_bisimilar rules admitted right
      (enumeration context index))

/-- The quotient metric uses the independently earned complete question reading. -/
def Space (context : Ctx sig) := (scheme rules admitted context).Space

@[instance_reducible]
def metricSpace (context : Ctx sig) : MetricSpace (Space rules admitted context) :=
  (scheme rules admitted context).quotientMetricSpace

theorem quotient_eq_iff_bisimilar
    (finite : Finitary.FiniteSuccessorCover rules admitted context) (first second : Process context) :
    Quotient.mk (scheme rules admitted context).setoid first =
      Quotient.mk (scheme rules admitted context).setoid second ↔
        Bisimilar (rules := rules) (admitted := admitted) first second :=
  ((scheme rules admitted context).space_mk_eq_iff first second).trans
    ((indistinguishable_iff rules admitted first second).trans
      (Finitary.logicallyEquivalent_iff_bisimilar rules admitted finite first second))

theorem quotient_distance_readout (first second : Process context) :
    @dist _ (metricSpace rules admitted context).toDist
      (Quotient.mk (scheme rules admitted context).setoid first)
      (Quotient.mk (scheme rules admitted context).setoid second) =
      (observations rules admitted context).distance first second :=
  (distance_eq_scheme rules admitted first second).symm

/-- A genuine finite interaction question forces positive distance without a branching premise. -/
theorem input_zero_positive_distance :
    0 < (observations sourceRules core []).distance (project waitingInput) (zero []) := by
  have separated : (observations sourceRules core []).distance (project waitingInput) (zero []) ≠ 0 :=
    fun zeroDistance => RhoScopedParallelModalControls.input_zero_not_finitary_equivalent
      ((distance_eq_zero_iff sourceRules core _ _).mp zeroDistance)
  exact lt_of_le_of_ne
    ((observations sourceRules core []).distance_nonneg _ _) separated.symm

theorem input_zero_distinct_metric_classes :
    Quotient.mk (scheme sourceRules core []).setoid (project waitingInput) ≠
      Quotient.mk (scheme sourceRules core []).setoid (zero []) := by
  intro same
  exact RhoScopedParallelModalControls.input_zero_not_finitary_equivalent
    ((indistinguishable_iff sourceRules core _ _).mp
      (((scheme sourceRules core []).space_mk_eq_iff _ _).mp same))

end Mettapedia.OSLF.Binding.RhoScopedParallelModalMetric
