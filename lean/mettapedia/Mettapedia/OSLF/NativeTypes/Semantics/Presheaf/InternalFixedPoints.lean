import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.Monotone
import Mettapedia.GSLT.Topos.NativePowerPredicates

/-!
# Internal fixed points quantified over actual local native predicates

The variable ranges over the real power presheaf, including coherent local
predicate sections at every future restriction. The prefixed/postfixed guards
are universal quantifiers along argument projection. Least/greatest formulas
are computed using the two actual quantifiers along predicate projection.
Their meanings are compared to independent monotone fixed-point semantics.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.InternalFixedPoints

open _root_.CategoryTheory Mettapedia.GSLT.Topos
open NativePowerPredicates NativeFixedPointEncodings Logic

universe u z

variable {C : Type u} [Category.{u} C] {A : Cᵒᵖ ⥤ Type u} {Atom : Type z}

noncomputable def transformed (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    Subfunctor (product A) :=
  Monotone.operator (fun atom => (atoms atom).preimage (first A)) body checked (membership A)

noncomputable def preGuard (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    Subfunctor (power A) :=
  forallAlong (second A) (transformed atoms body checked ⇨ membership A)

noncomputable def postGuard (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    Subfunctor (power A) :=
  forallAlong (second A) (membership A ⇨ transformed atoms body checked)

/-- The corrected internal universal-implication formula for mu. -/
noncomputable def least (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    Subfunctor A :=
  forallAlong (first A) ((preGuard atoms body checked).preimage (second A) ⇨ membership A)

/-- The corrected internal existential-conjunction formula for nu. -/
noncomputable def greatest (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    Subfunctor A :=
  ((postGuard atoms body checked).preimage (second A) ⊓ membership A).image (first A)

theorem transformed_name (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (candidate : Subfunctor A) :
    (transformed atoms body checked).preimage (pairName A candidate) =
      Monotone.operator atoms body checked candidate := by
  unfold transformed
  rw [Monotone.operator_reindex, membership_pairName]
  have atomsSame : (fun atom => ((atoms atom).preimage (first A)).preimage
      (pairName A candidate)) = atoms := by
    funext atom
    ext world value
    rfl
  rw [atomsSame]

theorem named_preGuard (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (candidate : Subfunctor A)
    (closed : Monotone.operator atoms body checked candidate ≤ candidate)
    (world : Cᵒᵖ) : name A candidate world ∈ (preGuard atoms body checked).obj world := by
  intro future restriction pair over
  rw [← himpPointwise_eq_himp]
  intro target arrow held
  have named : pair.2 = name A candidate future := over.trans (name_restrict A candidate restriction)
  have nextNamed : ((product A).map arrow pair).2 = name A candidate target := by
    change (power A).map arrow pair.2 = _
    rw [named, name_restrict]
  have same : (product A).map arrow pair =
      (pairName A candidate).app target (A.map arrow pair.1) := Prod.ext rfl nextNamed
  rw [same] at held ⊢
  have reduced : A.map arrow pair.1 ∈
      (Monotone.operator atoms body checked candidate).obj target := by
    rw [← transformed_name atoms body checked candidate]
    exact held
  have accepted := closed target reduced
  change A.map arrow pair.1 ∈ ((membership A).preimage (pairName A candidate)).obj target
  rw [membership_pairName]
  exact accepted

theorem named_postGuard (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (candidate : Subfunctor A)
    (closed : candidate ≤ Monotone.operator atoms body checked candidate)
    (world : Cᵒᵖ) : name A candidate world ∈ (postGuard atoms body checked).obj world := by
  intro future restriction pair over
  rw [← himpPointwise_eq_himp]
  intro target arrow held
  have named : pair.2 = name A candidate future := over.trans (name_restrict A candidate restriction)
  have nextNamed : ((product A).map arrow pair).2 = name A candidate target := by
    change (power A).map arrow pair.2 = _
    rw [named, name_restrict]
  have same : (product A).map arrow pair =
      (pairName A candidate).app target (A.map arrow pair.1) := Prod.ext rfl nextNamed
  rw [same] at held ⊢
  have accepted : A.map arrow pair.1 ∈ candidate.obj target := by
    rw [← membership_pairName A candidate]
    exact held
  have reduced := closed target accepted
  change A.map arrow pair.1 ∈
    ((transformed atoms body checked).preimage (pairName A candidate)).obj target
  rw [transformed_name]
  exact reduced

theorem least_le_meaning (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    least atoms body checked ≤ Monotone.inductiveMeaning atoms body checked := by
  intro world value held
  let candidate := Monotone.inductiveMeaning atoms body checked
  have closed : Monotone.operator atoms body checked candidate ≤ candidate :=
    (Monotone.inductive_unfold atoms body checked).le
  have function := held world (𝟙 world) (value, name A candidate world)
    (by exact (A.map_id_apply world value).symm)
  rw [← himpPointwise_eq_himp] at function
  have result := function world (𝟙 world)
  have self : (product A).map (𝟙 world) (value, name A candidate world) =
      (value, name A candidate world) := (product A).map_id_apply world _
  rw [self] at result
  have member := result (named_preGuard atoms body checked candidate closed world)
  change value ∈ ((membership A).preimage (pairName A candidate)).obj world at member
  rw [membership_pairName] at member
  exact member

theorem meaning_le_greatest (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    Monotone.coinductiveMeaning atoms body checked ≤ greatest atoms body checked := by
  intro world value held
  let candidate := Monotone.coinductiveMeaning atoms body checked
  have closed : candidate ≤ Monotone.operator atoms body checked candidate :=
    (Monotone.coinductive_unfold atoms body checked).ge
  refine ⟨(value, name A candidate world), ⟨?_, ?_⟩, rfl⟩
  · exact named_postGuard atoms body checked candidate closed world
  · change value ∈ ((membership A).preimage (pairName A candidate)).obj world
    rw [membership_pairName]
    exact held

theorem transformed_guard (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (guard : Subfunctor (power A)) :
    (transformed atoms body checked).preimage (inclusion A guard) =
      Monotone.operator (fun atom => (atoms atom).preimage (guardedFirst A guard))
        body checked ((membership A).preimage (inclusion A guard)) := by
  unfold transformed
  rw [Monotone.operator_reindex]
  have atomsSame : (fun atom => ((atoms atom).preimage (first A)).preimage
      (inclusion A guard)) = (fun atom => (atoms atom).preimage (guardedFirst A guard)) := by
    funext atom
    ext world value
    rfl
  rw [atomsSame]

theorem guarded_pre_closed (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    Monotone.operator
      (fun atom => (atoms atom).preimage (guardedFirst A (preGuard atoms body checked)))
      body checked ((membership A).preimage (inclusion A (preGuard atoms body checked))) ≤
        (membership A).preimage (inclusion A (preGuard atoms body checked)) := by
  rw [← transformed_guard]
  have guardLaw := (galois_preimage_forallAlong (second A)).l_u_le
    (transformed atoms body checked ⇨ membership A)
  have deduction := le_himp_iff.mp guardLaw
  intro world value held
  exact deduction world ⟨value.2.property, held⟩

theorem guarded_post_closed (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    (membership A).preimage (inclusion A (postGuard atoms body checked)) ≤
      Monotone.operator
        (fun atom => (atoms atom).preimage (guardedFirst A (postGuard atoms body checked)))
        body checked ((membership A).preimage (inclusion A (postGuard atoms body checked))) := by
  rw [← transformed_guard]
  have guardLaw := (galois_preimage_forallAlong (second A)).l_u_le
    (membership A ⇨ transformed atoms body checked)
  have deduction := le_himp_iff.mp guardLaw
  intro world value held
  exact deduction world ⟨value.2.property, held⟩

theorem meaning_le_least (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    Monotone.inductiveMeaning atoms body checked ≤ least atoms body checked := by
  apply (preimage_le_iff_le_forallAlong (first A) _ _).mp
  apply le_himp_iff.mpr
  apply guarded_inequality
  change (Monotone.inductiveMeaning atoms body checked).preimage
    (guardedFirst A (preGuard atoms body checked)) ≤ _
  rw [Monotone.inductive_substitution]
  exact least_induction _ _ (guarded_pre_closed atoms body checked)

theorem greatest_le_meaning (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    greatest atoms body checked ≤ Monotone.coinductiveMeaning atoms body checked := by
  apply (Subfunctor.image_le_iff _ (first A) _).mpr
  rw [inf_comm]
  apply guarded_inequality
  change (membership A).preimage (inclusion A (postGuard atoms body checked)) ≤
    (Monotone.coinductiveMeaning atoms body checked).preimage
      (guardedFirst A (postGuard atoms body checked))
  rw [Monotone.coinductive_substitution]
  exact greatest_coinduction _ _ (guarded_post_closed atoms body checked)

/-- Actual universal quantification over the whole power presheaf equals
independent least fixed-point semantics, including every local predicate. -/
theorem least_eq_meaning (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    least atoms body checked = Monotone.inductiveMeaning atoms body checked :=
  le_antisymm (least_le_meaning atoms body checked) (meaning_le_least atoms body checked)

/-- Actual existential quantification over local postfixed predicates equals
independent greatest fixed-point semantics. -/
theorem greatest_eq_meaning (atoms : Atom → Subfunctor A)
    (body : Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    greatest atoms body checked = Monotone.coinductiveMeaning atoms body checked :=
  le_antisymm (greatest_le_meaning atoms body checked) (meaning_le_greatest atoms body checked)

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.InternalFixedPoints
