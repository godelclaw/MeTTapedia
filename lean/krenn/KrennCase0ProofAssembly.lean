import KrennAllCollapseAssembly
import KrennFrozenCase0AdjugateLayer

/-!
The final branch-level assembly interface for the frozen C6 case-0 system.

The adjugate layer reduces every base-system witness to either the all-collapse
system or one named left-deflated-amplitude kill.  The all-collapse interface
then reduces its side to the finite selected-component table.  This file makes
the remaining P-kill obligation a separate finite table with no implicit case
gap.
-/

namespace Krenn.FrozenCase0ProofAssembly

open Krenn.FrozenCase0AdjugateLayer
open Krenn.FrozenCase0AllCollapseAssembly

/-- A refutation of one explicit left-kill branch of the frozen base system. -/
def RefutesLeftKillBranch {R : Type*} [Field R] [CharZero R]
    (slot : Fin 18) : Prop :=
  ∀ (values : Fin 75 → R), BaseCommonZero values →
    slotLeft values slot = 0 → False

/-- If both children of the adjugate split are refuted, the frozen base system
has no common zero. -/
theorem no_base_common_zero_of_allcollapse_and_leftkill_refutations
    {R : Type*} [Field R] [CharZero R]
    (allCollapse : ∀ values : Fin 75 → R,
      Krenn.FrozenCase0System.CommonZero values → False)
    (leftKill : ∀ slot : Fin 18, RefutesLeftKillBranch (R := R) slot)
    (values : Fin 75 → R) (base : BaseCommonZero values) : False := by
  rcases base_all_collapse_or_exists_left_kill values base with collapse | kill
  · exact allCollapse values collapse
  · rcases kill with ⟨slot, hkill⟩
    exact leftKill slot values base hkill

/-- The fully factored final interface: populate the support-cover component
table and the adjugate left-kill table, and the frozen case-0 base system is
impossible. -/
theorem no_base_common_zero_of_complete_branch_refutations
    {R : Type*} [Field R] [CharZero R]
    (componentRefute : ∀
      (stratum : Krenn.CollapseSupportCover.GlobalFormula.Stratum),
      stratum ∈ Krenn.CollapseSupportCover.GlobalFormula.strata →
        RefutesSelectedComponent (R := R) stratum.component)
    (leftKill : ∀ slot : Fin 18, RefutesLeftKillBranch (R := R) slot)
    (values : Fin 75 → R) (base : BaseCommonZero values) : False := by
  exact no_base_common_zero_of_allcollapse_and_leftkill_refutations
    (allCollapse := fun full collapse =>
      no_base_common_zero_of_stratum_refutations componentRefute full collapse)
    (leftKill := leftKill) values base

end Krenn.FrozenCase0ProofAssembly

#print axioms
  Krenn.FrozenCase0ProofAssembly.no_base_common_zero_of_allcollapse_and_leftkill_refutations
#print axioms
  Krenn.FrozenCase0ProofAssembly.no_base_common_zero_of_complete_branch_refutations
