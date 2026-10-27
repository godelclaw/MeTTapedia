import Mettapedia.Logic.HOL.RecursiveSpacePredicate
import Mettapedia.Logic.HOL.PredicateFixedPointSemantics
import Mettapedia.TypeTheory.IndexedPolynomialMappedPredicate

/-!
# HOL least predicates for encoded indexed families

The reading states the structural interpretation of the constructor and its
three guards. It contains no fixed-point or family-membership premise. Their
operator agreement and exact least-predicate membership follow from the
indexed family's induction and the actual recursive payload map.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.MappedFamilyPredicate
open Mettapedia.TypeTheory
open IndexedPolynomial.RecursiveSpaceRepresentation
open RecursiveSpacePredicate.Signature
universe u v w b i s p
variable {Sorts : Type u} {Const : Ty Sorts → Type v}
variable {Context : Type b} {Index : Context → Type i}
variable (presentation : Presentation.{b,i,s,p} (Base := Context) (Index := Index))
  (environment : Context) (signature : RecursiveSpacePredicate.Signature Const)
  (model : HenkinModel.{u,v,w} Sorts Const)
  (mapping : RecursivePayload presentation environment → Ty.denote model.Carrier signature.payload)

structure Reading where
  numbers : Nat ≃ Ty.denote model.Carrier signature.number
  trees : RecursiveSpace.Tree (Ty.denote model.Carrier signature.payload) ≃ Ty.denote model.Carrier signature.space
  bottom : trees RecursiveSpace.bottom = denotes model signature.bottom
  construct : ∀ tag payload children,
    trees (RecursiveSpace.construct tag payload children) =
      denotes model signature.construct (numbers tag) payload (fun n => trees (children (numbers.symm n)))
  shape_iff : ∀ tag payload,
    (denotes model signature.validShape (numbers tag) payload).down ↔
      Mapped.ShapeGuard presentation environment mapping tag payload
  active_iff : ∀ payload slot,
    (denotes model signature.active payload (numbers slot)).down ↔
      Mapped.ActiveGuard presentation environment mapping payload slot
  edge_iff : ∀ payload slot child,
    (denotes model signature.validEdge payload (numbers slot) (trees child)).down ↔
      Mapped.EdgeGuard presentation environment mapping payload slot child

namespace Reading
variable (reading : Reading presentation environment signature model mapping) (full : model.FullDomains)
include full

theorem operator_iff
    (predicate : Ty.denote model.Carrier (signature.space ⇒ .prop))
    (tree : RecursiveSpace.Tree (Ty.denote model.Carrier signature.payload)) :
    (denotes model signature.operator predicate (reading.trees tree)).down ↔
      Mapped.GuardedStep presentation environment mapping
        (fun child => (predicate (reading.trees child)).down) tree := by
  rw [signature.operator_meaning model full]
  constructor
  · rintro ⟨tag, payload, children, shape, same, conditions⟩
    let decoded := fun n => reading.trees.symm (children (reading.numbers n))
    refine ⟨reading.numbers.symm tag, payload, decoded, ?_, ?_, ?_⟩
    · apply (reading.shape_iff _ payload).mp
      simpa only [Equiv.apply_symm_apply] using shape
    · apply reading.trees.injective
      have constructor := reading.construct (reading.numbers.symm tag) payload decoded
      simp only [decoded, Equiv.apply_symm_apply] at constructor
      exact same.trans constructor.symm
    · intro n
      constructor
      · intro active
        obtain ⟨edge, present⟩ := (conditions (reading.numbers n)).1 ((reading.active_iff payload n).mpr active)
        constructor
        · apply (reading.edge_iff payload n (decoded n)).mp
          simpa only [decoded, Equiv.apply_symm_apply] using edge
        · simpa only [decoded, Equiv.apply_symm_apply] using present
      · intro inactive
        have padding := (conditions (reading.numbers n)).2
          (fun active => inactive ((reading.active_iff payload n).mp active))
        apply reading.trees.injective
        simpa only [decoded, Equiv.apply_symm_apply, reading.bottom] using padding
  · rintro ⟨tag, payload, children, shape, same, conditions⟩
    refine ⟨reading.numbers tag, payload,
      (fun n => reading.trees (children (reading.numbers.symm n))),
      (reading.shape_iff tag payload).mpr shape, ?_, ?_⟩
    · exact (congrArg reading.trees same).trans (reading.construct tag payload children)
    · intro n
      constructor
      · intro active
        have sourceActive : Mapped.ActiveGuard presentation environment mapping payload (reading.numbers.symm n) := by
          apply (reading.active_iff payload (reading.numbers.symm n)).mp
          simpa only [Equiv.apply_symm_apply] using active
        obtain ⟨edge, present⟩ := (conditions (reading.numbers.symm n)).1 sourceActive
        refine ⟨?_, present⟩
        have native := (reading.edge_iff payload (reading.numbers.symm n) (children (reading.numbers.symm n))).mpr edge
        simpa only [Equiv.apply_symm_apply] using native
      · intro inactive
        have sourceInactive : ¬ Mapped.ActiveGuard presentation environment mapping payload (reading.numbers.symm n) := by
          intro active
          apply inactive
          have native := (reading.active_iff payload (reading.numbers.symm n)).mpr active
          simpa only [Equiv.apply_symm_apply] using native
        exact (congrArg reading.trees ((conditions _).2 sourceInactive)).trans reading.bottom

def member (tree : RecursiveSpace.Tree (Ty.denote model.Carrier signature.payload)) : Prop :=
  (denotes model (PredicateFixedPoint.least signature.operator) (reading.trees tree)).down

theorem member_iff (injective : Function.Injective mapping)
    (tree : RecursiveSpace.Tree (Ty.denote model.Carrier signature.payload)) :
    member presentation environment signature model mapping reading tree ↔
      Mapped.FamilyValid presentation environment mapping tree := by
  rw [member, denotes, PredicateFixedPoint.least_denote]
  constructor
  · intro present
    let property := fun value => ULift.up
      (Mapped.FamilyValid presentation environment mapping (reading.trees.symm value))
    have result := present property (full _ _) (by
      intro value _ generated
      have step := (operator_iff presentation environment signature model mapping reading full property (reading.trees.symm value)).mp
        (by simpa only [Equiv.apply_symm_apply, denote_closed] using generated)
      simp only [property, Equiv.symm_apply_apply] at step
      exact (Mapped.familyValid_fixed_point presentation environment mapping injective _).mpr step)
    simpa only [property, Equiv.symm_apply_apply] using result
  · intro valid predicate _ closed
    apply Mapped.familyValid_least presentation environment mapping injective
      (fun tree => (predicate (reading.trees tree)).down) ?_ tree valid
    intro value generated
    exact closed (reading.trees value) (full _ _)
      ((operator_iff presentation environment signature model mapping reading full predicate value).mpr generated)

#print axioms operator_iff
#print axioms member_iff
end Reading
end Mettapedia.Logic.HOL.MappedFamilyPredicate
