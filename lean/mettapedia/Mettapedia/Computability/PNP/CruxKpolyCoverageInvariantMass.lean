import Mettapedia.Computability.PNP.ABVisibleInvariantSurjectivityObstructionCore
import Mettapedia.Computability.PNP.ABVisibleInvariantSurjectivityObstructionSupport
import Mettapedia.Computability.PNP.ABVisibleInvariantSurjectivityObstructionBoolZ
import Mettapedia.Computability.PNP.ABVisibleInvariantSurjectivityObstructionSurjectivity
import Mettapedia.Computability.PNP.ABVisibleInvariantSurjectivityObstructionRouteWrappers

/-!
# PNP `Kpoly` coverage anchors: AB-visible invariant mass barriers

AB-visible invariant family barriers, positive-mass disagreement, agreement-mass, and non-surjectivity anchors.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: an exact family invariant under raw `(a,b)` cannot
select any target rule that separates a same-`(a,b)` exact fiber. -/
theorem kpolyCoverage_anchor_not_exists_predict_eq_of_abVisibleInvariant_of_abFiberSeparatingRule
    {Z : Type*} {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hsep : ABFiberSeparatingRule (Z := Z) (k := k) rule) :
    ¬ ∃ i, G.predict i = rule :=
  not_exists_predict_eq_of_abVisibleInvariant_of_abFiberSeparatingRule
    (Z := Z) (k := k) hinv hsep

/-- Route-coverage anchor: a raw `(a,b)`-invariant exact family cannot select
the concrete hidden-`z` projection rule. -/
theorem kpolyCoverage_anchor_not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G) :
    ¬ ∃ i, G.predict i = boolZProjectionRule (k := k) :=
  not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant
    (k := k) hinv

/-- Route-coverage anchor: a raw `(a,b)`-invariant exact predictor must have a
positive-mass disagreement whenever the target separates two positive-mass
points in one same-`(a,b)` exact fiber. -/
theorem kpolyCoverage_anchor_exists_pos_mass_disagreement_of_abVisibleInvariant_predict_of_abFiberSeparation
    {Z : Type*} {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    (i : Index)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ target x :=
  exists_pos_mass_disagreement_of_abVisibleInvariant_predict_of_abFiberSeparation
    (Z := Z) (k := k) hinv (μ := μ) (target := target) i
    hab hsep huμ hvμ

/-- Route-coverage anchor: on any distribution that puts positive mass on the
two default same-`(a,b)` hidden-bit points, a raw `(a,b)`-invariant predictor
must disagree with the hidden-`z` projection on positive mass. -/
theorem kpolyCoverage_anchor_exists_pos_mass_disagreement_boolZProjectionRule_of_abVisibleInvariant
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ boolZProjectionRule (k := k) x :=
  exists_pos_mass_disagreement_of_abVisibleInvariant_predict_boolZProjectionRule
    (k := k) hinv (μ := μ) i hfalse htrue

/-- Route-coverage anchor: positive-mass same-`(a,b)` target separation forces
agreement mass below one for every raw `(a,b)`-invariant exact predictor. -/
theorem kpolyCoverage_anchor_agreementMass_lt_one_of_abVisibleInvariant_predict_of_abFiberSeparation
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    (i : Index)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    agreementMass μ target (G.predict i) < 1 :=
  agreementMass_lt_one_of_abVisibleInvariant_predict_of_abFiberSeparation
    (Z := Z) (k := k) hinv (μ := μ) (target := target) i
    hab hsep huμ hvμ

/-- Route-coverage anchor: on a distribution supporting both default
hidden-bit sides of one same-`(a,b)` fiber, a raw `(a,b)`-invariant exact
predictor has agreement mass below one against the hidden-`z` projection. -/
theorem kpolyCoverage_anchor_agreementMass_lt_one_boolZProjectionRule_of_abVisibleInvariant
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) < 1 :=
  agreementMass_lt_one_of_abVisibleInvariant_predict_boolZProjectionRule
    (k := k) hinv (μ := μ) i hfalse htrue

/-- Route-coverage anchor: positive-mass same-`(a,b)` target separation rules
out every perfect-agreement member of a raw `(a,b)`-invariant exact family. -/
theorem kpolyCoverage_anchor_not_exists_agreementMass_eq_one_of_abVisibleInvariant_of_abFiberSeparation
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ¬ ∃ i, agreementMass μ target (G.predict i) = 1 :=
  not_exists_agreementMass_eq_one_of_abVisibleInvariant_of_abFiberSeparation
    (Z := Z) (k := k) hinv (μ := μ) (target := target)
    hab hsep huμ hvμ

/-- Route-coverage anchor: on a distribution supporting both default hidden-bit
sides of one same-`(a,b)` fiber, a raw `(a,b)`-invariant exact family has no
member with perfect agreement against the hidden-`z` projection. -/
theorem kpolyCoverage_anchor_not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) = 1 :=
  not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
    (k := k) hinv (μ := μ) hfalse htrue

/-- Route-coverage anchor: a raw `(a,b)`-invariant exact family is not
surjective onto exact visible Boolean rules when `Z` is nontrivial. -/
theorem kpolyCoverage_anchor_not_surjective_predict_of_abVisibleInvariant_of_nontrivial
    {Z : Type*} [Nontrivial Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G) :
    ¬ Function.Surjective G.predict :=
  not_surjective_predict_of_abVisibleInvariant_of_nontrivial
    (Z := Z) (k := k) hinv


end Mettapedia.Computability.PNP
