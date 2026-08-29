import KrennFrozenCase0CollapseLayer

/-!
The top-level assembly interface for the frozen C6 all-collapse branch.

`Krenn.FrozenCase0CollapseLayer.base_common_zero_stratum_sound` proves that a
common zero of the frozen system belongs to one of the certified support
strata.  This file packages the remaining finite obligation precisely: a
refutation for the selected component of every certified stratum eliminates
the frozen all-collapse system.
-/

namespace Krenn.FrozenCase0AllCollapseAssembly

open MvPolynomial
open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.FrozenCase0CollapseLayer

/-- A component-level connector sufficient for one frozen case-0 valuation. -/
def RefutesSelectedComponent {R : Type*} [Field R] [CharZero R]
    (component : Fin 67) : Prop :=
  ∀ (full : Fin 75 → R), Krenn.FrozenCase0System.CommonZero full →
    (∀ generator ∈ componentGenerators component,
      generatorEval (reduceRaw (rawValues full)) generator = 0) → False

/-- The all-collapse branch reduces to the finite family of selected-component
connectors supplied by the support-cover theorem. -/
theorem no_base_common_zero_of_stratum_refutations
    {R : Type*} [Field R] [CharZero R]
    (refute : ∀ (stratum : Krenn.CollapseSupportCover.GlobalFormula.Stratum),
      stratum ∈ Krenn.CollapseSupportCover.GlobalFormula.strata →
      RefutesSelectedComponent (R := R) stratum.component)
    (full : Fin 75 → R) (base : Krenn.FrozenCase0System.CommonZero full) : False := by
  obtain ⟨stratum, hstratum, _cover, selectedVanish⟩ :=
    base_common_zero_stratum_sound full base
  exact refute stratum hstratum full base selectedVanish

end Krenn.FrozenCase0AllCollapseAssembly

#print axioms
  Krenn.FrozenCase0AllCollapseAssembly.no_base_common_zero_of_stratum_refutations
