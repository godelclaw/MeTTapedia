import Mettapedia.OSLF.Syntax.RhoScopedParallelEvents

/-!
# Least-context transitions of the actual scoped rho event system

Original root instances define reaction rules in the original process-class
category. Least labels are computed from the typed multiset difference,
rather than supplied by an execution. Every competing bound has the same
least label and reaction residue. Identity-labelled transitions agree in
both directions with the independently authored permitted-path events.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoScopedParallelReactiveSystem

open _root_.CategoryTheory RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedParallelInventory RhoScopedParallelContexts RhoScopedParallelEvents
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence

universe u

local instance (context : Ctx sig) : DecidableEq (Prime context) := Classical.decEq _

variable {Index : Type u} (rules : Index → ProcessRule) (admitted : Index → Prop)

def rootRule {context : Ctx sig} (root : Root rules admitted context) :
    ReactionRule (interface context) where
  codomain := interface context
  redex := arrow root.source
  reactum := arrow root.target

def reactionRules {context : Ctx sig} : ReactionRule (interface context) → Prop :=
  fun rule => ∃ root : Root rules admitted context, rootRule rules admitted root = rule

variable {rules admitted}

/-- A receipt retains the actual root, complete reaction context and leastness readout. -/
structure Firing {context : Ctx sig} (first label second : Process context) where
  root : Root rules admitted context
  surrounding : Process context
  square : join first label = join root.source surrounding
  least : read label ∩ read surrounding = 0
  target : second = join root.target surrounding

theorem firing_iff_actIPO {context : Ctx sig} (first label second : Process context) :
    Nonempty (Firing (rules := rules) (admitted := admitted) first label second) ↔
      ActIPO (reactionRules rules admitted) (arrow label) (arrow first) (arrow second) := by
  constructor
  · rintro ⟨receipt⟩
    have square : arrow first ≫ arrow label =
        (rootRule rules admitted receipt.root).redex ≫ arrow receipt.surrounding := by
      change arrow first ≫ arrow label = arrow receipt.root.source ≫ arrow receipt.surrounding
      rw [arrow_comp, arrow_comp]
      exact congrArg arrow receipt.square
    refine ⟨rootRule rules admitted receipt.root, ⟨receipt.root, rfl⟩,
      arrow receipt.surrounding, square,
      (idemPushout_iff _ _ _ _ square).mpr receipt.least, ?_⟩
    exact (congrArg arrow receipt.target).trans (arrow_comp _ _).symm
  · rintro ⟨rule, ⟨root, rfl⟩, surrounding, square, minimal, output⟩
    refine ⟨⟨root, surrounding.process, ?_, ?_, ?_⟩⟩
    · exact arrow_injective ((arrow_comp _ _).symm.trans
        (square.trans (arrow_comp _ _)))
    · exact (idemPushout_iff _ _ _ _ square).mp minimal
    · exact arrow_injective (output.trans (arrow_comp _ _))

def leastLabel {context : Ctx sig} (first : Process context) (root : Root rules admitted context) :
    Process context := write (read root.source - read first)

def reactionRemainder {context : Ctx sig} (first : Process context)
    (root : Root rules admitted context) : Process context := write (read first - read root.source)

theorem difference_square {context : Ctx sig} (first : Process context)
    (root : Root rules admitted context) :
    join first (leastLabel first root) = join root.source (reactionRemainder first root) := by
  apply read_injective context
  simp only [read_join, leastLabel, reactionRemainder, read_write]
  ext component
  simp only [Multiset.count_add, Multiset.count_sub]
  omega

theorem differences_disjoint {context : Ctx sig} (first : Process context)
    (root : Root rules admitted context) :
    read (leastLabel first root) ∩ read (reactionRemainder first root) = 0 := by
  simp only [leastLabel, reactionRemainder, read_write]
  ext component
  simp only [Multiset.count_inter, Multiset.count_sub, Multiset.count_zero]
  omega

/-- The least firing is constructed for every supplied process and authored root. -/
def leastFiring {context : Ctx sig} (first : Process context) (root : Root rules admitted context) :
    Firing (rules := rules) (admitted := admitted) first (leastLabel first root)
      (join root.target (reactionRemainder first root)) where
  root := root
  surrounding := reactionRemainder first root
  square := difference_square first root
  least := differences_disjoint first root
  target := rfl

theorem least_transition {context : Ctx sig} (first : Process context)
    (root : Root rules admitted context) :
    ActIPO (reactionRules rules admitted) (arrow (leastLabel first root)) (arrow first)
      (arrow (join root.target (reactionRemainder first root))) :=
  (firing_iff_actIPO _ _ _).mp ⟨leastFiring first root⟩

/-- All minimal competitors reconstruct the computed label and complete residue. -/
theorem firing_normal_form {context : Ctx sig} {first label second : Process context}
    (receipt : Firing (rules := rules) (admitted := admitted) first label second) :
    label = leastLabel first receipt.root ∧
      receipt.surrounding = reactionRemainder first receipt.root := by
  have square := congrArg read receipt.square
  simp only [read_join] at square
  have left := Multiset.inter_add_sub_of_add_eq_add square
  have right := Multiset.inter_add_sub_of_add_eq_add square.symm
  rw [receipt.least, zero_add] at left
  rw [Multiset.inter_comm, receipt.least, zero_add] at right
  exact ⟨read_injective context ((read_write _).trans left).symm,
    read_injective context ((read_write _).trans right).symm⟩

theorem actIPO_iff_computed {context : Ctx sig} (first label second : Process context) :
    ActIPO (reactionRules rules admitted) (arrow label) (arrow first) (arrow second) ↔
      ∃ root : Root rules admitted context,
        label = leastLabel first root ∧
          second = join root.target (reactionRemainder first root) := by
  constructor
  · intro step
    obtain ⟨receipt⟩ := (firing_iff_actIPO _ _ _).mpr step
    obtain ⟨labelRead, contextRead⟩ := firing_normal_form receipt
    exact ⟨receipt.root, labelRead, contextRead ▸ receipt.target⟩
  · rintro ⟨root, rfl, rfl⟩
    exact least_transition first root

/-- Actual original event reduction is exactly an identity-labelled IPO transition. -/
theorem step_iff_actIPO_identity {context : Ctx sig} (first second : Process context) :
    RhoScopedParallelEvents.Step (rules := rules) (admitted := admitted) first second ↔
      ActIPO (reactionRules rules admitted) (𝟙 (interface context)) (arrow first) (arrow second) := by
  rw [← arrow_zero, ← firing_iff_actIPO, step_iff_root_surrounding]
  constructor
  · rintro ⟨root, surrounding, sourceRead, targetRead⟩
    refine ⟨⟨root, surrounding, ?_, ?_, targetRead⟩⟩
    · exact (join_zero_right first).trans sourceRead
    · rw [read_zero, Multiset.zero_inter]
  · rintro ⟨receipt⟩
    exact ⟨receipt.root, receipt.surrounding,
      (join_zero_right first).symm.trans receipt.square, receipt.target⟩

def Bisimilar {context : Ctx sig} (first second : Process context) : Prop :=
  IPOBisimilar (reactionRules rules admitted) (arrow first) (arrow second)

theorem context_congruence {context : Ctx sig} {first second : Process context}
    (related : Bisimilar (rules := rules) (admitted := admitted) first second)
    (surrounding : Process context) :
    Bisimilar (rules := rules) (admitted := admitted)
      (join first surrounding) (join second surrounding) :=
  bisimilar_join (reactionRules rules admitted) related surrounding

end Mettapedia.OSLF.Binding.RhoScopedParallelReactiveSystem
