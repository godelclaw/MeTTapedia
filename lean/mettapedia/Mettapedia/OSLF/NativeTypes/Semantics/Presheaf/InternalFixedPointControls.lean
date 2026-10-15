import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.InternalFixedPoints
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.MonotoneControls
import Mettapedia.GSLT.Topos.NativePowerEquality

/-!
# Local-predicate controls and the printed fixed-point corrections

The literal existential-implication reading of mu is full even when its
independent least fixed point is empty. The printed universal-implication
reading of nu computes the least fixed point. Both controls use the actual
local power presheaf, rather than quantifying only over global predicates.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.InternalFixedPointControls

open _root_.CategoryTheory Mettapedia.GSLT.Topos
open NativePowerPredicates NativeFixedPointEncodingsControls
open InternalFixedPoints MonotoneControls

universe u z
variable {C : Type u} [Category.{u} C] {A : Cᵒᵖ ⥤ Type u} {Atom : Type z}

/-- Literal source mu: existential implication, with the postfixed guard. -/
noncomputable def printedLeast (atoms : Atom → Subfunctor A)
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    Subfunctor A :=
  ((postGuard atoms body checked).preimage (second A) ⇨ membership A).image (first A)

/-- Literal source nu: universal implication, with the prefixed guard. -/
noncomputable def printedGreatest (atoms : Atom → Subfunctor A)
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    Subfunctor A :=
  forallAlong (first A) ((preGuard atoms body checked).preimage (second A) ⇨ membership A)

theorem printedLeast_full (atoms : Atom → Subfunctor A)
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    printedLeast atoms body checked = ⊤ := by
  apply le_antisymm le_top
  intro world value _
  refine ⟨(value, name A ⊤ world), ?_, rfl⟩
  rw [← himpPointwise_eq_himp]
  intro future restriction _
  have restricts := name_restrict A (⊤ : Subfunctor A) restriction
  change (A.map restriction value, (power A).map restriction (name A ⊤ world)) ∈
    (membership A).obj future
  rw [restricts]
  change A.map restriction value ∈ ((membership A).preimage (pairName A ⊤)).obj future
  rw [membership_pairName]
  trivial

theorem printedGreatest_is_least (atoms : Atom → Subfunctor A)
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    printedGreatest atoms body checked = Monotone.inductiveMeaning atoms body checked :=
  least_eq_meaning atoms body checked

abbrev localValues : Worldᵒᵖ ⥤ Type := (Functor.const _).obj Bool
abbrev localSpot : Worldᵒᵖ := Opposite.op spot

def localSeed : Subfunctor localValues where
  obj _ := {value | value = true}
  map _ _ member := member

theorem local_inductive_seed :
    Monotone.inductiveMeaning (fun _ : Unit => localSeed) seedBody seed_checked = localSeed := by
  apply le_antisymm
  · exact NativeFixedPointEncodings.least_induction _ localSeed (sup_le le_rfl le_rfl)
  · have unfolds := Monotone.inductive_unfold (fun _ : Unit => localSeed) seedBody seed_checked
    exact unfolds ▸ (le_sup_left : localSeed ≤ localSeed ⊔
      Monotone.inductiveMeaning (fun _ : Unit => localSeed) seedBody seed_checked)

theorem local_coinductive_full :
    Monotone.coinductiveMeaning (fun _ : Unit => localSeed) seedBody seed_checked = ⊤ := by
  apply le_antisymm le_top
  exact NativeFixedPointEncodings.greatest_coinduction _ ⊤ le_sup_right

theorem seeded_local_least_exact :
    least (C := World) (fun _ : Unit => localSeed) seedBody seed_checked = localSeed := by
  rw [least_eq_meaning, local_inductive_seed]

theorem seeded_local_greatest_exact :
    greatest (C := World) (fun _ : Unit => localSeed) seedBody seed_checked = ⊤ := by
  rw [greatest_eq_meaning, local_coinductive_full]

theorem printed_mu_refuted_locally :
    printedLeast (C := World) (fun _ : Unit => localSeed) seedBody seed_checked ≠
      Monotone.inductiveMeaning (fun _ : Unit => localSeed) seedBody seed_checked := by
  intro same
  rw [printedLeast_full, local_inductive_seed] at same
  have impossible : false ∈ localSeed.obj localSpot := same ▸ trivial
  exact Bool.false_ne_true impossible

theorem printed_nu_refuted_locally :
    printedGreatest (C := World) (fun _ : Unit => localSeed) seedBody seed_checked ≠
      Monotone.coinductiveMeaning (fun _ : Unit => localSeed) seedBody seed_checked := by
  intro same
  rw [printedGreatest_is_least, local_inductive_seed, local_coinductive_full] at same
  have impossible : false ∈ localSeed.obj localSpot := same.symm ▸ trivial
  exact Bool.false_ne_true impossible

theorem local_least_positive :
    true ∈ (least (C := World) (fun _ : Unit => localSeed) seedBody seed_checked).obj localSpot := by
  rw [seeded_local_least_exact]
  rfl

theorem local_least_negative :
    false ∉ (least (C := World) (fun _ : Unit => localSeed) seedBody seed_checked).obj localSpot := by
  rw [seeded_local_least_exact]
  exact Bool.false_ne_true

theorem internal_equality_positive :
    (true, true) ∈ (NativePowerEquality.leibniz (C := World) localValues).obj localSpot :=
  (NativePowerEquality.leibniz_iff (C := World) localValues localSpot true true).mpr rfl

theorem internal_equality_negative :
    (true, false) ∉ (NativePowerEquality.leibniz (C := World) localValues).obj localSpot := by
  intro held
  exact Bool.false_ne_true
    ((NativePowerEquality.leibniz_iff (C := World) localValues localSpot true false).mp held).symm

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.InternalFixedPointControls
