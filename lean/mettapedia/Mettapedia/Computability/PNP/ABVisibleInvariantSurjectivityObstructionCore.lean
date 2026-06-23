import Mettapedia.Computability.PNP.CanonicalABCodeWitness
import Mettapedia.Computability.PNP.FiniteIIDAgreement
import Mettapedia.Computability.PNP.SharedABRecoveryInterfaceSparseThreshold
import Mettapedia.Computability.PNP.SharedExactABFeatureERMInterfaceAffine
import Mettapedia.Computability.PNP.SharedExactABFeatureERMInterfaceSparseThreshold
import Mettapedia.Computability.PNP.SharedExactABERMInterfaceConsequences

/-!
# P vs NP crux: raw `(a, b)` fiber invariance

This module contains the core observation: predictors invariant under the raw
visible quotient `(z, a, b) ↦ (a, b)` cannot realize rules that separate a
single raw `(a,b)` fiber.
-/

namespace Mettapedia.Computability.PNP
section Core

variable {Z : Type*} {k : ℕ}

/-- A Boolean rule on the exact visible surface is invariant on every raw
`(a,b)` fiber when it gives equal outputs to exact inputs with the same
`abVisibleData`. -/
def ABFiberInvariantRule (rule : ExactVisiblePostSwitchSurface Z k → Bool) : Prop :=
  ∀ u v, abVisibleData u = abVisibleData v → rule u = rule v

/-- A Boolean rule separates the raw `(a,b)` quotient when it distinguishes two
exact inputs with the same raw `(a,b)` data. -/
def ABFiberSeparatingRule (rule : ExactVisiblePostSwitchSurface Z k → Bool) : Prop :=
  ∃ u v, abVisibleData u = abVisibleData v ∧ rule u ≠ rule v

theorem not_abFiberSeparatingRule_of_abFiberInvariantRule
    {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hrule : ABFiberInvariantRule (Z := Z) (k := k) rule) :
    ¬ ABFiberSeparatingRule (Z := Z) (k := k) rule := by
  rintro ⟨u, v, hab, hneq⟩
  exact hneq (hrule u v hab)

theorem abFiberInvariantRule_of_eq_predict_of_abVisibleInvariant
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {i : Index} {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hi : G.predict i = rule) :
    ABFiberInvariantRule (Z := Z) (k := k) rule := by
  intro u v hab
  simpa [← hi] using hinv i u v hab

theorem not_exists_predict_eq_of_abVisibleInvariant_of_abFiberSeparatingRule
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hsep : ABFiberSeparatingRule (Z := Z) (k := k) rule) :
    ¬ ∃ i, G.predict i = rule := by
  rintro ⟨i, hi⟩
  exact
    not_abFiberSeparatingRule_of_abFiberInvariantRule
      (abFiberInvariantRule_of_eq_predict_of_abVisibleInvariant
        (Z := Z) (k := k) hinv hi)
      hsep

theorem abVisibleInvariant_of_factorsThrough_abVisibleData
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H) :
    ABVisibleInvariant (Z := Z) (k := k) G := by
  intro i u v huv
  calc
    G.predict i u = H.predict i (abVisibleData u) := hfactor i u
    _ = H.predict i (abVisibleData v) := by simpa using congrArg (H.predict i) huv
    _ = G.predict i v := (hfactor i v).symm

theorem not_exists_predict_eq_of_factorsThrough_abVisibleData_of_abFiberSeparatingRule
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hsep : ABFiberSeparatingRule (Z := Z) (k := k) rule) :
    ¬ ∃ i, G.predict i = rule :=
  not_exists_predict_eq_of_abVisibleInvariant_of_abFiberSeparatingRule
    (Z := Z) (k := k)
    (abVisibleInvariant_of_factorsThrough_abVisibleData
      (Z := Z) (k := k) hfactor)
    hsep

/-- The concrete rule reading the hidden `z` bit on the exact visible surface. -/
def boolZProjectionRule (u : ExactVisiblePostSwitchSurface Bool k) : Bool := u.z

theorem boolZProjectionRule_abFiberSeparatingRule :
    ABFiberSeparatingRule (Z := Bool) (k := k)
      (boolZProjectionRule (k := k)) := by
  let a : BitVec k := default
  let b : BitVec k := default
  refine ⟨⟨false, a, b⟩, ⟨true, a, b⟩, rfl, ?_⟩
  simp [boolZProjectionRule]

theorem not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G) :
    ¬ ∃ i, G.predict i = boolZProjectionRule (k := k) :=
  not_exists_predict_eq_of_abVisibleInvariant_of_abFiberSeparatingRule
    (Z := Bool) (k := k) hinv
    (boolZProjectionRule_abFiberSeparatingRule (k := k))

theorem not_exists_predict_eq_boolZProjectionRule_of_factorsThrough_abVisibleData
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ ∃ i, G.predict i = boolZProjectionRule (k := k) :=
  not_exists_predict_eq_of_factorsThrough_abVisibleData_of_abFiberSeparatingRule
    (Z := Bool) (k := k) hfactor
    (boolZProjectionRule_abFiberSeparatingRule (k := k))

end Core

end Mettapedia.Computability.PNP
