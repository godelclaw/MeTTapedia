import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.PredicateNaming
import Mettapedia.GSLT.Topos.PresheafPredicateQuantifierBaseChange

/-!
# Independent fixed-point comparison for dependent native predicates

The induction and coinduction arguments restrict to the actual subobject
where the generic local predicate satisfies its guard. They therefore cover
all local predicate components of the native dependent product.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeFixedPointComparison

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open PredicateVariables PredicateNaming FixedPointEvaluation
open NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open NativeFixedPointEncodings

universe u z
variable {C : Type u} [Category.{u} C] {P : Cᵒᵖ ⥤ Type u} {Atom : Type z}

theorem preimage_meet {X Y : Cᵒᵖ ⥤ Type u} (left right : Subfunctor Y) (map : X ⟶ Y) :
    (left ⊓ right).preimage map = left.preimage map ⊓ right.preimage map := rfl

theorem guarded_inequality {X : Cᵒᵖ ⥤ Type u}
    (guard left right : Subfunctor X)
    (restricted : left.preimage guard.ι ≤ right.preimage guard.ι) :
    left ⊓ guard ≤ right := by
  intro world value held
  exact restricted world (show (⟨value, held.2⟩ : guard.obj world) ∈
    (left.preimage guard.ι).obj world from held.1)

theorem tester_square (A : NativeType P) (value : A.decoded.sections) :
    sectionLift (argumentType A).decoded
      (ContextualLocalUniverses.substituteTerm (type := A) value
        (totalProjection (predicate A).decoded)) ≫ atomProjection A =
      totalProjection (predicate A).decoded ≫ sectionLift A.decoded value :=
  Mettapedia.TypeTheory.ContextualTypeOperations.selfExtend_substitution
    (C := (Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.NativeModel C).toCwf)
    (totalProjection (predicate A).decoded) value

theorem guarded_pre_closed (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    let guard := (preGuard A atoms body checked).preimage
      (totalProjection (argumentType A).decoded)
    Monotone.operator (fun atom => (atoms atom).preimage (guard.ι ≫ atomProjection A))
      body checked ((boundMembership A).preimage guard.ι) ≤
        (boundMembership A).preimage guard.ι := by
  dsimp only
  have deduction := le_himp_iff.mp ((galois_preimage_forallAlong
    (totalProjection (argumentType A).decoded)).l_u_le
      (transformed A atoms body checked ⇨ boundMembership A))
  have transformedGuard := Monotone.operator_reindex
    (fun atom => (atoms atom).preimage (atomProjection A))
    (((preGuard A atoms body checked).preimage
      (totalProjection (argumentType A).decoded)).ι) body checked (boundMembership A)
  simp only [← Subfunctor.preimage_comp] at transformedGuard
  rw [← transformedGuard]
  intro world value held
  exact deduction world ⟨value.property, held⟩

theorem guarded_post_closed (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    let guard := (postGuard A atoms body checked).preimage
      (totalProjection (argumentType A).decoded)
    (boundMembership A).preimage guard.ι ≤
      Monotone.operator (fun atom => (atoms atom).preimage (guard.ι ≫ atomProjection A))
        body checked ((boundMembership A).preimage guard.ι) := by
  dsimp only
  have deduction := le_himp_iff.mp ((galois_preimage_forallAlong
    (totalProjection (argumentType A).decoded)).l_u_le
      (boundMembership A ⇨ transformed A atoms body checked))
  have transformedGuard := Monotone.operator_reindex
    (fun atom => (atoms atom).preimage (atomProjection A))
    (((postGuard A atoms body checked).preimage
      (totalProjection (argumentType A).decoded)).ι) body checked (boundMembership A)
  simp only [← Subfunctor.preimage_comp] at transformedGuard
  rw [← transformedGuard]
  intro world value held
  exact deduction world ⟨value.property, held⟩

theorem inductive_guard (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    (Monotone.inductiveMeaning atoms body checked).preimage (atomProjection A) ⊓
      (preGuard A atoms body checked).preimage (totalProjection (argumentType A).decoded) ≤
        boundMembership A := by
  apply guarded_inequality
  rw [← Subfunctor.preimage_comp, Monotone.inductive_substitution]
  exact least_induction _ _ (guarded_pre_closed A atoms body checked)

theorem coinductive_guard (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true) :
    boundMembership A ⊓
      (postGuard A atoms body checked).preimage (totalProjection (argumentType A).decoded) ≤
        (Monotone.coinductiveMeaning atoms body checked).preimage (atomProjection A) := by
  apply guarded_inequality
  rw [← Subfunctor.preimage_comp, Monotone.coinductive_substitution]
  exact greatest_coinduction _ _ (guarded_post_closed A atoms body checked)

theorem meaning_le_least (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (value : A.decoded.sections) :
    (Monotone.inductiveMeaning atoms body checked).preimage (sectionLift A.decoded value) ≤
      least A atoms body checked value := by
  apply (preimage_le_iff_le_forallAlong (totalProjection (predicate A).decoded) _ _).mp
  apply le_himp_iff.mpr
  have comparison := inductive_guard A atoms body checked
  let tester := sectionLift (argumentType A).decoded
    (ContextualLocalUniverses.substituteTerm (type := A) value
      (totalProjection (predicate A).decoded))
  have pulled : ((Monotone.inductiveMeaning atoms body checked).preimage (atomProjection A) ⊓
      (preGuard A atoms body checked).preimage (totalProjection (argumentType A).decoded)).preimage
        tester ≤ (boundMembership A).preimage tester := fun world _ held => comparison world held
  dsimp only [tester] at pulled
  simp only [preimage_meet, bound_tested, ← Subfunctor.preimage_comp,
    tester_square, projection_section] at pulled
  exact pulled

theorem greatest_le_meaning (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (value : A.decoded.sections) :
    greatest A atoms body checked value ≤
      (Monotone.coinductiveMeaning atoms body checked).preimage (sectionLift A.decoded value) := by
  apply (Subfunctor.image_le_iff _ (totalProjection (predicate A).decoded) _).mpr
  have comparison := coinductive_guard A atoms body checked
  let tester := sectionLift (argumentType A).decoded
    (ContextualLocalUniverses.substituteTerm (type := A) value
      (totalProjection (predicate A).decoded))
  have pulled : (boundMembership A ⊓
      (postGuard A atoms body checked).preimage (totalProjection (argumentType A).decoded)).preimage
        tester ≤ ((Monotone.coinductiveMeaning atoms body checked).preimage
          (atomProjection A)).preimage tester := fun world _ held => comparison world held
  dsimp only [tester] at pulled
  simp only [preimage_meet, bound_tested, ← Subfunctor.preimage_comp,
    tester_square, projection_section] at pulled
  rw [inf_comm]
  exact pulled

theorem transformed_named (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (candidate : Subfunctor (totalSpace A.decoded)) :
    (transformed A atoms body checked).preimage
      (totalReindexMap (sectionLift (predicate A).decoded
        (NativeLocalTypeOperations.lam (nativeQuote candidate))) (argumentType A).decoded) =
      (Monotone.operator atoms body checked candidate).preimage
        (typeContext (named_argument_type A (NativeLocalTypeOperations.lam (nativeQuote candidate)))).hom := by
  rw [transformed, Monotone.operator_reindex, named_body]
  simp only [← Subfunctor.preimage_comp, named_argument_projection]
  exact (Monotone.operator_reindex atoms _ body checked candidate).symm

theorem named_preGuard (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (candidate : Subfunctor (totalSpace A.decoded))
    (closed : Monotone.operator atoms body checked candidate ≤ candidate) :
    (preGuard A atoms body checked).preimage (sectionLift (predicate A).decoded
      (NativeLocalTypeOperations.lam (nativeQuote candidate))) = ⊤ := by
  rw [preGuard, forallAlong_beckChevalley _ _ _ _
    (totalReindexMap_isPullback _ (argumentType A).decoded).flip,
    preimage_himp, transformed_named, named_body, ← preimage_himp,
    himp_eq_top_iff.mpr closed]
  have topPullback : (⊤ : Subfunctor (totalSpace A.decoded)).preimage
      (typeContext (named_argument_type A
        (NativeLocalTypeOperations.lam (nativeQuote candidate)))).hom = ⊤ := by
    ext world value
    rfl
  rw [topPullback, forallAlong_top]

theorem named_postGuard (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (candidate : Subfunctor (totalSpace A.decoded))
    (closed : candidate ≤ Monotone.operator atoms body checked candidate) :
    (postGuard A atoms body checked).preimage (sectionLift (predicate A).decoded
      (NativeLocalTypeOperations.lam (nativeQuote candidate))) = ⊤ := by
  rw [postGuard, forallAlong_beckChevalley _ _ _ _
    (totalReindexMap_isPullback _ (argumentType A).decoded).flip,
    preimage_himp, transformed_named, named_body, ← preimage_himp,
    himp_eq_top_iff.mpr closed]
  have topPullback : (⊤ : Subfunctor (totalSpace A.decoded)).preimage
      (typeContext (named_argument_type A
        (NativeLocalTypeOperations.lam (nativeQuote candidate)))).hom = ⊤ := by
    ext world value
    rfl
  rw [topPullback, forallAlong_top]

theorem least_le_meaning (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (value : A.decoded.sections) :
    least A atoms body checked value ≤
      (Monotone.inductiveMeaning atoms body checked).preimage (sectionLift A.decoded value) := by
  let candidate := Monotone.inductiveMeaning atoms body checked
  let naming := sectionLift (predicate A).decoded (NativeLocalTypeOperations.lam (nativeQuote candidate))
  have guard : (preGuard A atoms body checked).preimage naming = ⊤ :=
    named_preGuard A atoms body checked candidate (Monotone.inductive_unfold atoms body checked).le
  have application : (testedMembership A value).preimage naming =
      candidate.preimage (sectionLift A.decoded value) := tested_reified A value candidate
  have deduction := (galois_preimage_forallAlong (totalProjection (predicate A).decoded)).l_u_le
    (preGuard A atoms body checked ⇨ testedMembership A value)
  intro world parameter held
  have result : parameter ∈ ((preGuard A atoms body checked ⇨ testedMembership A value).preimage
      naming).obj world := deduction world (show naming.app world parameter ∈
        ((least A atoms body checked value).preimage (totalProjection (predicate A).decoded)).obj
          world from held)
  rw [preimage_himp, guard, application, top_himp] at result
  exact result

theorem meaning_le_greatest (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (value : A.decoded.sections) :
    (Monotone.coinductiveMeaning atoms body checked).preimage (sectionLift A.decoded value) ≤
      greatest A atoms body checked value := by
  let candidate := Monotone.coinductiveMeaning atoms body checked
  let naming := sectionLift (predicate A).decoded (NativeLocalTypeOperations.lam (nativeQuote candidate))
  have guard : (postGuard A atoms body checked).preimage naming = ⊤ :=
    named_postGuard A atoms body checked candidate (Monotone.coinductive_unfold atoms body checked).ge
  have application : (testedMembership A value).preimage naming =
      candidate.preimage (sectionLift A.decoded value) := tested_reified A value candidate
  intro world parameter held
  refine ⟨naming.app world parameter, ⟨?_, ?_⟩, rfl⟩
  · change parameter ∈ ((postGuard A atoms body checked).preimage naming).obj world
    rw [guard]
    trivial
  · change parameter ∈ ((testedMembership A value).preimage naming).obj world
    rw [application]
    exact held

/-- The emitted universal-implication formula denotes the independent least
fixed point at the supplied argument, for arbitrary dependent native carriers. -/
theorem least_eq_meaning (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (value : A.decoded.sections) :
    least A atoms body checked value =
      (Monotone.inductiveMeaning atoms body checked).preimage (sectionLift A.decoded value) :=
  le_antisymm (least_le_meaning A atoms body checked value)
    (meaning_le_least A atoms body checked value)

/-- The actual existential predicate witness denotes the independent greatest
fixed point; its guard covers every argument and future restriction. -/
theorem greatest_eq_meaning (A : NativeType P)
    (atoms : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (value : A.decoded.sections) :
    greatest A atoms body checked value =
      (Monotone.coinductiveMeaning atoms body checked).preimage (sectionLift A.decoded value) :=
  le_antisymm (greatest_le_meaning A atoms body checked value)
    (meaning_le_greatest A atoms body checked value)

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeFixedPointComparison
