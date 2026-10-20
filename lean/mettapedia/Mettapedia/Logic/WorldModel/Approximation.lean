import Mettapedia.Logic.WorldModel.Observation
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Approximate world-model observations

An approximation translates states, requests and complete values, and bounds
the distance between the two resulting observations. The metric is declared
by the consumer; an error budget does not replace the observed value.

Composition must account for how the second value interpretation amplifies
the first error. A Lipschitz interpretation supplies exactly that bound.
No additive state revision or probabilistic independence is assumed.
-/

namespace Mettapedia.Logic.WorldModel

open scoped NNReal

universe uS uQ uV uT uR uW uU uP uX

variable {S : Type uS} {Q : Type uQ} {V : Type uV}
  {T : Type uT} {R : Type uR} {W : Type uW}
  {U : Type uU} {P : Type uP} {X : Type uX}
  [WorldModel S Q V] [WorldModel T R W] [WorldModel U P X]

/-- A bound on a declared observation, with the full value map retained. -/
structure ApproximationMap (S : Type uS) (Q : Type uQ) (V : Type uV)
    (T : Type uT) (R : Type uR) (W : Type uW)
    [WorldModel S Q V] [WorldModel T R W] [PseudoMetricSpace W] where
  state : S → T
  query : Q → R
  value : V → W
  error : S → Q → ℝ≥0
  observe : ∀ source request,
    dist (WorldModel.extract (state source) (query request))
      (value (WorldModel.extract source request)) ≤ error source request

namespace ApproximationMap

variable [PseudoMetricSpace W]

@[ext] theorem ext {first second : ApproximationMap S Q V T R W}
    (state : first.state = second.state) (query : first.query = second.query)
    (value : first.value = second.value) (error : first.error = second.error) : first = second := by
  cases first
  cases second
  cases state
  cases query
  cases value
  cases error
  rfl

/-- An exact commuting map has zero observation error. No metric on the
source value carrier is needed for this construction. -/
def ofExact (map : ObservationMap S Q V T R W) : ApproximationMap S Q V T R W where
  state := map.state
  query := map.query
  value := map.value
  error _ _ := 0
  observe source request := by rw [map.observe]; simp

/-- The second interpretation can magnify error. Its Lipschitz constant
therefore scales the first budget before adding the second budget. -/
def comp [PseudoMetricSpace X]
    (first : ApproximationMap S Q V T R W) (second : ApproximationMap T R W U P X)
    (K : ℝ≥0) (stable : LipschitzWith K second.value) : ApproximationMap S Q V U P X where
  state := second.state ∘ first.state
  query := second.query ∘ first.query
  value := second.value ∘ first.value
  error source request := second.error (first.state source) (first.query request) +
    K * first.error source request
  observe source request := by
    change dist (WorldModel.extract (second.state (first.state source))
      (second.query (first.query request)))
      (second.value (first.value (WorldModel.extract source request))) ≤ _
    calc
      _ ≤ dist (WorldModel.extract (second.state (first.state source))
          (second.query (first.query request)))
          (second.value (WorldModel.extract (first.state source) (first.query request))) +
          dist (second.value (WorldModel.extract (first.state source) (first.query request)))
            (second.value (first.value (WorldModel.extract source request))) := dist_triangle _ _ _
      _ ≤ (second.error (first.state source) (first.query request) : ℝ) +
          (K : ℝ) * first.error source request :=
        add_le_add (second.observe _ _)
          ((stable.dist_le_mul _ _).trans
            (mul_le_mul_of_nonneg_left (first.observe _ _) K.coe_nonneg))
      _ = _ := by simp

/-- Three-stage bounds compose associatively, including their amplification
factors. The equality retains the whole pointwise budget function. -/
theorem comp_assoc [PseudoMetricSpace X]
    {A B C : Type*} [WorldModel A B C] [PseudoMetricSpace C]
    (first : ApproximationMap S Q V T R W) (second : ApproximationMap T R W U P X)
    (third : ApproximationMap U P X A B C) (K L : ℝ≥0)
    (secondStable : LipschitzWith K second.value) (thirdStable : LipschitzWith L third.value) :
    comp (comp first second K secondStable) third L thirdStable =
      comp first (comp second third L thirdStable) (L * K) (thirdStable.comp secondStable) := by
  apply ext
  · rfl
  · rfl
  · rfl
  · funext source request
    simp only [comp, Function.comp_apply]
    ring

/-- Every Lipschitz measurement of the retained value inherits a bound. -/
theorem measured_error {Y : Type*} [PseudoMetricSpace Y]
    (map : ApproximationMap S Q V T R W) (measure : W → Y) (K : ℝ≥0)
    (stable : LipschitzWith K measure) (source : S) (request : Q) :
    dist (measure (WorldModel.extract (map.state source) (map.query request)))
      (measure (map.value (WorldModel.extract source request))) ≤
        (K : ℝ) * map.error source request :=
  (stable.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (map.observe source request) K.coe_nonneg)

end ApproximationMap

namespace ApproximationMap

variable [MetricSpace W]

/-- In a metric value space a zero budget recovers the exact observation
contract. A pseudometric alone would recover only distance-zero agreement. -/
def toExact (map : ApproximationMap S Q V T R W)
    (zero : ∀ source request, map.error source request = 0) : ObservationMap S Q V T R W where
  state := map.state
  query := map.query
  value := map.value
  observe source request := by
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    simpa only [zero, NNReal.coe_zero] using map.observe source request

end ApproximationMap

namespace ApproximationControls

local instance : WorldModel ℝ Unit ℝ where
  revise _ later := later
  empty := 0
  extract source _ := source

def shift : ApproximationMap ℝ Unit ℝ ℝ Unit ℝ where
  state source := source + 1
  query := id
  value := id
  error _ _ := 1
  observe source _ := by
    change dist (source + 1) source ≤ (1 : ℝ)
    norm_num [Real.dist_eq]

def double : ObservationMap ℝ Unit ℝ ℝ Unit ℝ where
  state source := 2 * source
  query := id
  value source := 2 * source
  observe _ _ := rfl

theorem double_lipschitz : LipschitzWith 2 double.value := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  change |2 * first - 2 * second| ≤ (2 : ℝ) * |first - second|
  rw [← mul_sub, abs_mul]
  norm_num

/-- Merely adding the two unscaled budgets is unsound: a later exact map can
double an earlier approximation error. -/
theorem unscaled_error_addition_fails :
    dist ((shift.comp (ApproximationMap.ofExact double) 2 double_lipschitz).state 0)
      ((shift.comp (ApproximationMap.ofExact double) 2 double_lipschitz).value 0) = (2 : ℝ) ∧
      (shift.error 0 () : ℝ) + (ApproximationMap.ofExact double).error (shift.state 0) () < 2 := by
  norm_num [ApproximationMap.comp, ApproximationMap.ofExact, shift, double, Real.dist_eq]

theorem scaled_composition_attains_budget :
    dist ((shift.comp (ApproximationMap.ofExact double) 2 double_lipschitz).state 0)
      ((shift.comp (ApproximationMap.ofExact double) 2 double_lipschitz).value 0) =
        (shift.comp (ApproximationMap.ofExact double) 2 double_lipschitz).error 0 () := by
  norm_num [ApproximationMap.comp, ApproximationMap.ofExact, shift, double, Real.dist_eq]

end ApproximationControls

end Mettapedia.Logic.WorldModel
