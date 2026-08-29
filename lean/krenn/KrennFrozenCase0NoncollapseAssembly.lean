import KrennAllCollapseAssembly
import KrennFrozenCase0UniformStarConnector
import Mathlib

/-!
The exact non-collapse interface for the frozen C6 case-0 system.

The all-collapse side is already reduced to the finite component table.  On
the complementary side, a nonzero adjugate determinant selects one of
eighteen `(vertex, colour)` slots.  The uniform star connector proves that
three explicitly named chord co-sum kills at that slot contradict the
monochromatic normalization.

This file records that reduction without asserting the missing balanced-layer
harvest.  It makes the remaining non-collapse task a finite table of eighteen
slot obligations, each with three named chord targets.
-/

namespace Krenn.FrozenCase0NoncollapseAssembly

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0UniformStarConnector
open Krenn.FrozenCase0AllCollapseAssembly
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.DoilyPotential

/-- A contradiction for one explicit non-collapse determinant slot. -/
def RefutesNoncollapseSlot {R : Type*} [Field R] [CharZero R]
    (slot : Fin 18) : Prop :=
  ∀ (values : Fin 75 → R), BaseCommonZero values →
    slotDeterminant values slot ≠ 0 → False

/-- The precise balanced-layer harvest required at one non-collapse slot.
The two cycle-side kills are supplied by the adjugate identities; these are
the remaining three chord-side kills in the same vertex star. -/
def HarvestsStarChords {R : Type*} [Field R] [CharZero R]
    (slot : Fin 18) : Prop :=
  ∀ (values : Fin 75 → R) (_base : BaseCommonZero values),
    slotDeterminant values slot ≠ 0 →
      ∀ chord,
        coSum (diagonal values (slotColour slot))
          (slotChordEdge slot chord) = 0

/-- One proved star-harvest entry refutes its corresponding non-collapse
slot. -/
theorem refutes_noncollapse_slot_of_star_chord_harvest
    {R : Type*} [Field R] [CharZero R]
    (slot : Fin 18) (harvest : HarvestsStarChords (R := R) slot) :
    RefutesNoncollapseSlot (R := R) slot := by
  intro values base hdet
  exact no_base_witness_of_noncollapse_and_star_chord_kills
    values base slot hdet (harvest values base hdet)

/-- The frozen base system is impossible once both its all-collapse branch
and all eighteen non-collapse slots are refuted. -/
theorem no_base_common_zero_of_allcollapse_and_noncollapse_refutations
    {R : Type*} [Field R] [CharZero R]
    (allCollapse : ∀ values : Fin 75 → R,
      Krenn.FrozenCase0System.CommonZero values → False)
    (noncollapse : ∀ slot : Fin 18,
      RefutesNoncollapseSlot (R := R) slot)
    (values : Fin 75 → R) (base : BaseCommonZero values) : False := by
  rcases base_allCollapse_or_exists_noncollapse_slot values base with full | ⟨slot, hdet⟩
  · exact allCollapse values full
  · exact noncollapse slot values base hdet

/-- The complete finite interface for frozen C6 case 0: selected-component
refutations for the all-collapse strata, plus the 18 star-harvest entries,
refute the base system. -/
theorem no_base_common_zero_of_component_refutations_and_star_harvest
    {R : Type*} [Field R] [CharZero R]
    (componentRefute : ∀
      (stratum : Krenn.CollapseSupportCover.GlobalFormula.Stratum),
      stratum ∈ Krenn.CollapseSupportCover.GlobalFormula.strata →
        RefutesSelectedComponent (R := R) stratum.component)
    (harvest : ∀ slot : Fin 18, HarvestsStarChords (R := R) slot)
    (values : Fin 75 → R) (base : BaseCommonZero values) : False := by
  apply no_base_common_zero_of_allcollapse_and_noncollapse_refutations
    (allCollapse := fun full collapse =>
      no_base_common_zero_of_stratum_refutations componentRefute full collapse)
    (noncollapse := fun slot =>
      refutes_noncollapse_slot_of_star_chord_harvest slot (harvest slot))
    values base

#print axioms
  Krenn.FrozenCase0NoncollapseAssembly.refutes_noncollapse_slot_of_star_chord_harvest
#print axioms
  Krenn.FrozenCase0NoncollapseAssembly.no_base_common_zero_of_allcollapse_and_noncollapse_refutations
#print axioms
  Krenn.FrozenCase0NoncollapseAssembly.no_base_common_zero_of_component_refutations_and_star_harvest

end Krenn.FrozenCase0NoncollapseAssembly
