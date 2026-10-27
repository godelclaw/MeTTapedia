/-
Knuth–Skilling slice of the probability hypercube. See the aggregator
`Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling.lean` for the overview.
-/
import KnuthSkilling.Core.Algebra
import Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets
import Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.SequentialSemantics
import Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.ScaleDichotomy
import Mettapedia.ProbabilityTheory.Hypercube.Basic
import Mettapedia.ProbabilityTheory.Hypercube.ThetaSemantics
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Families of representations and interval observations

A family of additive readouts gives interval envelopes under the stated
boundedness and nonemptiness conditions. The complete-lattice version allows
infinite endpoints. Completeness alone fixes no calibration: the identity and
twice the identity remain distinct additive scales. A shared positive anchor
makes canonical representations agree and hence gives a point envelope.

The small inference-level enumeration is a toy vocabulary, not a proof that
particular axioms supply algorithms, measures, conditioning or integration.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Neighbors

open Classical
-- `_root_.` forces the standalone K&S package; the enclosing
-- `…Hypercube.KnuthSkilling` namespace would otherwise shadow `KnuthSkilling`.
open _root_.KnuthSkilling
open Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets
open _root_.KnuthSkilling.Additive
open _root_.KnuthSkilling.Additive.Proofs.GridInduction
open _root_.KnuthSkilling.KnuthSkillingAlgebra
open _root_.KnuthSkilling.KnuthSkillingAlgebraBase

/-- Authored labels, without a realizability or capability theorem. -/
inductive ToyInferenceLevel
  | None       -- No probabilistic inference (non-commutative)
  | Discrete   -- Exact but finite (ℤ-like)
  | Imprecise  -- Interval bounds (ℚ-like)
  | Classical  -- Full measure theory (ℝ)
  deriving DecidableEq, Repr

/-- Descriptions attached to the toy labels. -/
def toyInferenceDescription : ToyInferenceLevel → String
  | .None => "Sequential combination"
  | .Discrete => "Finite rational calculations"
  | .Imprecise => "Interval-valued operations (robust bounds)"
  | .Classical => "Measure-theoretic models"

section CanonicalIntervals

variable {α : Type*}

/-- From any nonempty family of additive real-valued completions `Θ`, we get an interval semantics
for `op` satisfying Minkowski containment. -/
noncomputable def intervalSemantics_ofThetaFamily (op : α → α → α)
    (ι : Type*) [Nonempty ι]
    (Θ : ι → α → ℝ)
    (hAssoc : ∀ x y z, op (op x y) z = op x (op y z))
    (hAdd : ∀ i x y, Θ i (op x y) = Θ i x + Θ i y)
    (hBddBelow : ∀ x, BddBelow (Set.range fun i => Θ i x))
    (hBddAbove : ∀ x, BddAbove (Set.range fun i => Θ i x)) :
    IntervalAddSemantics α :=
  IntervalAddSemantics.ofThetaFamily op ι Θ hAssoc hAdd hBddBelow hBddAbove

/-- A concrete “imprecise” consequence: widths are subadditive for the canonical interval semantics
induced by any family of additive completions. -/
theorem intervalSemantics_width_subadditive (op : α → α → α)
    (ι : Type*) [Nonempty ι]
    (Θ : ι → α → ℝ)
    (hAssoc : ∀ x y z, op (op x y) z = op x (op y z))
    (hAdd : ∀ i x y, Θ i (op x y) = Θ i x + Θ i y)
    (hBddBelow : ∀ x, BddBelow (Set.range fun i => Θ i x))
    (hBddAbove : ∀ x, BddAbove (Set.range fun i => Θ i x))
    (x y : α) :
    ((intervalSemantics_ofThetaFamily op ι Θ hAssoc hAdd hBddBelow hBddAbove).μ (op x y)).width ≤
      ((intervalSemantics_ofThetaFamily op ι Θ hAssoc hAdd hBddBelow hBddAbove).μ x).width +
        ((intervalSemantics_ofThetaFamily op ι Θ hAssoc hAdd hBddBelow hBddAbove).μ y).width := by
  simpa [intervalSemantics_ofThetaFamily, IntervalAddSemantics.ofThetaFamily] using
    IntervalAddSemantics.width_subadditive
      (S := IntervalAddSemantics.ofThetaFamily op ι Θ hAssoc hAdd hBddBelow hBddAbove) x y

end CanonicalIntervals

section ThetaFamilyIntervals

open Mettapedia.ProbabilityTheory.Hypercube
open Mettapedia.ProbabilityTheory.Hypercube.ThetaSemantics

variable {α : Type*}

abbrev ThetaCL : Type := WithTop (WithBot ℝ)

/-- Lift a real-valued completion to the complete lattice `WithTop (WithBot ℝ)`. -/
noncomputable def liftRealCompletion (Θ : α → ℝ) : α → ThetaCL :=
  fun x => ((Θ x : WithBot ℝ) : ThetaCL)

/-- Interval envelope induced by a **set** of real-valued completions, computed in `WithTop ℝ`. -/
noncomputable def intervalOfRealFamily (Θs : Set (α → ℝ)) :
    ThetaSemantics.IntervalSemantics α ThetaCL :=
  ThetaSemantics.intervalOfFamily (β := ThetaCL) (liftRealCompletion '' Θs)

/-- If the real-valued completion family is subsingleton, the induced interval envelope is point-valued. -/
theorem intervalOfRealFamily_lower_eq_upper_of_subsingleton {Θs : Set (α → ℝ)}
    (hsub : Θs.Subsingleton) (hne : Θs.Nonempty) (x : α) :
    (intervalOfRealFamily (α := α) Θs).lower x = (intervalOfRealFamily (α := α) Θs).upper x := by
  exact ThetaSemantics.lower_eq_upper_of_subsingleton (hsub.image _) (hne.image _) x

/-- Nonempty families with a shared positive anchor have point-valued envelopes. -/
theorem calibrated_family_point {α : Type*} [_root_.KnuthSkilling.KnuthSkillingMonoidBase α]
    (rs : Set (_root_.KnuthSkilling.Additive.NormalizedRepresentationResult α))
    (hne : rs.Nonempty) (a : α) (ha : _root_.KnuthSkilling.KnuthSkillingMonoidBase.ident < a)
    (hcal : ∀ r ∈ rs, r.Θ a = 1) (x : α) :
    (intervalOfRealFamily ((fun r => r.Θ) '' rs)).lower x =
      (intervalOfRealFamily ((fun r => r.Θ) '' rs)).upper x := by
  apply intervalOfRealFamily_lower_eq_upper_of_subsingleton
    (hne := hne.image (fun r => r.Θ))
  rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
  exact Mettapedia.ProbabilityTheory.OrderedCombination.calibrated_unique r s a ha
    ((hcal r hr).trans (hcal s hs).symm)

/-- Two valid additive scales, both normalized at zero, can have different units. -/
def scaleFamily : Set (ℝ → ℝ) := {id, fun x => 2 * x}

theorem scaleFamily_additive {f : ℝ → ℝ} (hf : f ∈ scaleFamily) (x y : ℝ) :
    f (x + y) = f x + f y := by
  rcases hf with rfl | hf
  · rfl
  · simp only [Set.mem_singleton_iff] at hf
    subst f; dsimp; ring

theorem scaleFamily_order {f : ℝ → ℝ} (hf : f ∈ scaleFamily) : StrictMono f := by
  rcases hf with rfl | hf
  · exact strictMono_id
  · simp only [Set.mem_singleton_iff] at hf
    subst f; exact strictMono_mul_left_of_pos (by norm_num)

theorem scaleFamily_zero {f : ℝ → ℝ} (hf : f ∈ scaleFamily) : f 0 = 0 := by
  rcases hf with rfl | hf
  · rfl
  · simp only [Set.mem_singleton_iff] at hf
    subst f; exact mul_zero _

/-- A complete codomain can retain a strict interval of possible observations. -/
theorem scaleFamily_envelope_at_one :
    (intervalOfRealFamily scaleFamily).lower 1 = (1 : ThetaCL) ∧
      (intervalOfRealFamily scaleFamily).upper 1 = (2 : ThetaCL) := by
  norm_num [intervalOfRealFamily, ThetaSemantics.intervalOfFamily, ThetaSemantics.lower,
    ThetaSemantics.upper, ThetaSemantics.thetaValues, scaleFamily, liftRealCompletion,
    Set.image_insert_eq, Set.image_singleton, min_def, max_def]

/-- Empty families do not satisfy the point-envelope conclusion. -/
theorem empty_family_not_point :
    (intervalOfRealFamily (∅ : Set (Unit → ℝ))).lower () ≠
      (intervalOfRealFamily (∅ : Set (Unit → ℝ))).upper () := by
  simp [intervalOfRealFamily, ThetaSemantics.intervalOfFamily, ThetaSemantics.lower,
    ThetaSemantics.upper, ThetaSemantics.thetaValues]

end ThetaFamilyIntervals

/-- An imprecise probability assignment -/
structure ImpreciseProb where
  lower : ℝ
  upper : ℝ
  valid : lower ≤ upper
  nonneg : 0 ≤ lower
  le_one : upper ≤ 1

/-- Combine independent imprecise probabilities -/
def ImpreciseProb.mul (p q : ImpreciseProb) : ImpreciseProb where
  lower := p.lower * q.lower
  upper := p.upper * q.upper
  valid := by
    apply mul_le_mul p.valid q.valid q.nonneg
    exact le_trans p.nonneg p.valid
  nonneg := mul_nonneg p.nonneg q.nonneg
  le_one := by
    have h1 : p.upper ≤ 1 := p.le_one
    have h2 : q.upper ≤ 1 := q.le_one
    have h3 : 0 ≤ q.upper := le_trans q.nonneg q.valid
    calc p.upper * q.upper ≤ 1 * q.upper := by apply mul_le_mul_of_nonneg_right h1 h3
      _ = q.upper := one_mul _
      _ ≤ 1 := h2

/-- Classical conditioning collapses to a point -/
noncomputable def classicalCondition (pAB pB : ℝ) (_hB : pB ≠ 0) : ℝ := pAB / pB

end Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Neighbors
