import Mettapedia.OSLF.Syntax.SortedCommutativeGroundFactorData
import Mathlib.Data.Finite.Sigma

/-!
# Finite complete ground factorizations of sorted AC1 values

The outer residue is bounded by the independently read ground inventory.
Every genuine outer frame selects an occurring free head and one of its
finite argument positions; the complete inner factor is recovered in that
actual child. Structural induction earns finiteness for all factors, retaining
both the whole context and input, including unit-valued ground collisions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative.GroundFactors

open Mettapedia.OSLF.SortedConstructors

universe u v

variable {signature : Signature.{u,v}} {Parallel : signature.Srt → Prop}

abbrev ParallelFactor (source : signature.Srt) {target : signature.Srt}
    (whole : Class signature Parallel target) :=
  {factor : Factor source whole // factor.val.1.frameCount = 0}

abbrev FramedFactor (source : signature.Srt) {target : signature.Srt}
    (whole : Class signature Parallel target) :=
  {factor : Factor source whole // 0 < factor.val.1.frameCount}

theorem parallel_outer_injective {source target : signature.Srt}
    (whole : Class signature Parallel target) :
    Function.Injective (fun factor : ParallelFactor source whole => outerResidue factor.val) := by
  rintro ⟨⟨⟨first, before⟩, firstRead⟩, firstCount⟩
    ⟨⟨⟨second, after⟩, secondRead⟩, secondCount⟩ same
  cases first with
  | parallel firstBag =>
    cases second with
    | parallel secondBag =>
      have bags : firstBag = secondBag := congrArg Subtype.val same
      subst secondBag
      have inputs : before = after := residue_injective firstBag (firstRead.trans secondRead.symm)
      subst after
      rfl
    | frame bag frame inner =>
      simp only [Mettapedia.CategoryTheory.MixedResidue.Context.frameCount] at secondCount
      omega
  | frame bag frame inner =>
    simp only [Mettapedia.CategoryTheory.MixedResidue.Context.frameCount] at firstCount
    omega

theorem parallelFactor_finite {source target : signature.Srt}
    (whole : Class signature Parallel target) : Finite (ParallelFactor source whole) := by
  let _ := boundedResidue_finite whole
  exact Finite.of_injective _ (parallel_outer_injective whole)

def framedCode {source target : signature.Srt} {whole : Class signature Parallel target}
    (supplied : FramedFactor source whole) : FrameCode source whole := by
  obtain ⟨⟨⟨context, input⟩, read⟩, framed⟩ := supplied
  cases context with
  | parallel bag =>
    simp only [Mettapedia.CategoryTheory.MixedResidue.Context.frameCount] at framed
    omega
  | @frame middle _ bag edge inner =>
    cases middle with
    | mk middleSort =>
      cases edge with
      | slot constructor position siblings =>
        let selected := (mixedAction signature Parallel).read inner input
        let head := SortedCommutative.Head.node constructor (Frame.insert constructor position siblings selected)
        have inventoryRead : bag.map Subtype.val + {head} = inventoryQ whole := by
          have actual := congrArg inventoryQ read
          change inventoryQ (residue bag head.class) = inventoryQ whole at actual
          rw [residue_inventory, SortedCommutative.Head.inventory_class] at actual
          exact actual
        have member : head ∈ inventoryQ whole := by
          rw [← inventoryRead]
          exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self head))
        have childRead : evaluate (inner, input) = Head.child head position := by
          change selected = Frame.insert constructor position siblings selected position
          simp only [Frame.insert, dite_true]
        exact ⟨⟨bag, (Multiset.le_add_right _ _).trans_eq inventoryRead⟩,
          ⟨⟨head, member⟩, position, ⟨(inner, input), childRead⟩⟩⟩

theorem framedCode_reading {source target : signature.Srt} {whole : Class signature Parallel target}
    (supplied : FramedFactor source whole) : (framedCode supplied).reading = supplied.val.val := by
  obtain ⟨⟨⟨context, input⟩, read⟩, framed⟩ := supplied
  cases context with
  | parallel bag =>
    simp only [Mettapedia.CategoryTheory.MixedResidue.Context.frameCount] at framed
    omega
  | @frame middle _ bag edge inner =>
    cases middle with
    | mk middleSort =>
      cases edge with
      | slot constructor position siblings =>
        dsimp only [framedCode, FrameCode.reading, Head.frame]
        apply congrArg (fun frame : Frame signature Parallel
            (signature.input constructor position) (signature.output constructor) =>
          ((.frame bag frame inner, input) : Reading (Parallel := Parallel) source (signature.output constructor)))
        apply congrArg (Frame.slot constructor position)
        funext other absent
        simp only [Frame.insert, dif_neg absent]

theorem framedCode_injective {source target : signature.Srt} {whole : Class signature Parallel target} :
    Function.Injective (framedCode (source := source) (whole := whole)) := by
  intro first second same
  apply Subtype.ext
  apply Subtype.ext
  exact (framedCode_reading first).symm.trans
    ((congrArg FrameCode.reading same).trans (framedCode_reading second))

theorem factor_finite_of_children {source target : signature.Srt}
    (whole : Class signature Parallel target)
    (children : ∀ head ∈ inventoryQ whole, ∀ position : Head.Position head,
      Finite (Factor source (Head.child head position))) : Finite (Factor source whole) := by
  classical
  let _ := boundedResidue_finite whole
  let _ := occurringHead_finite whole
  let _ : ∀ head : OccurringHead whole, ∀ position : Head.Position head.val,
      Finite (Factor source (Head.child head.val position)) :=
    fun head position => children head.val head.property position
  let _ : Finite (FrameCode source whole) := inferInstance
  let _ : Finite (FramedFactor source whole) := Finite.of_injective _ framedCode_injective
  let _ := parallelFactor_finite (source := source) whole
  apply Finite.of_surjective
    (Sum.elim (Subtype.val : ParallelFactor source whole → Factor source whole)
      (Subtype.val : FramedFactor source whole → Factor source whole))
  intro supplied
  by_cases noFrame : supplied.val.1.frameCount = 0
  · exact ⟨.inl ⟨supplied, noFrame⟩, rfl⟩
  · exact ⟨.inr ⟨supplied, Nat.pos_of_ne_zero noFrame⟩, rfl⟩

private theorem term_factor_and_children_finite (source : signature.Srt)
    {target : signature.Srt} (supplied : Term signature Parallel target) :
    Finite (Factor source (classOf supplied)) ∧
      (∀ head ∈ inventory supplied, ∀ position : Head.Position head,
        Finite (Factor source (Head.child head position))) := by
  induction supplied with
  | zero parallel =>
    have children : ∀ head ∈ inventory (Term.zero parallel : Term signature Parallel _),
        ∀ position : Head.Position head, Finite (Factor source (Head.child head position)) := by
      intro head member
      exact (Multiset.notMem_zero head member).elim
    exact ⟨factor_finite_of_children _ children, children⟩
  | cut parallel first second firstIH secondIH =>
    have children : ∀ head ∈ inventory (.cut parallel first second),
        ∀ position : Head.Position head, Finite (Factor source (Head.child head position)) := by
      intro head member
      rcases Multiset.mem_add.mp member with firstMember | secondMember
      · exact firstIH.2 head firstMember
      · exact secondIH.2 head secondMember
    exact ⟨factor_finite_of_children _ children, children⟩
  | node constructor arguments inductionHypothesis =>
    have children : ∀ head ∈ inventory (.node constructor arguments),
        ∀ position : Head.Position head, Finite (Factor source (Head.child head position)) := by
      intro head member
      have same : head = SortedCommutative.Head.node constructor (fun position => classOf (arguments position)) :=
        Multiset.mem_singleton.mp member
      subst head
      intro position
      exact (inductionHypothesis position).1
    exact ⟨factor_finite_of_children _ children, children⟩

theorem factor_finite (source : signature.Srt) {target : signature.Srt}
    (whole : Class signature Parallel target) : Finite (Factor source whole) := by
  induction whole using Quotient.inductionOn with
  | _ representative => exact (term_factor_and_children_finite source representative).1

theorem contexts_filling_value_finite {source target : signature.Srt}
    (input : Class signature Parallel source) (whole : Class signature Parallel target) :
    Set.Finite {context : MixedContext signature Parallel source target |
      (mixedAction signature Parallel).read context input = whole} := by
  let _ := factor_finite source whole
  exact Finite.of_injective
    (fun supplied => (⟨(supplied.val, input), supplied.property⟩ : Factor source whole))
    (fun first second same => Subtype.ext (congrArg (fun factor : Factor source whole => factor.val.1) same))

end Mettapedia.OSLF.SortedCommutative.GroundFactors
