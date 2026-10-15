import Mettapedia.OSLF.Syntax.SortedCommutativeGroundFactorFinite

/-!
# Finite ground factors across all original hole sorts

The sort set may be infinite. A parallel factor has the output's own sort;
a genuine frame selects one of finitely many occurring constructor slots.
Its inner factor supplies the original hole sort. The actual reconstruction
therefore bounds the complete dependent sum of factors without assuming a
finite signature, an inhabited sort, or injective ground context evaluation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative.GroundFactors

open Mettapedia.OSLF.SortedConstructors

universe u v

variable {signature : Signature.{u,v}} {Parallel : signature.Srt → Prop}

abbrev TotalFactor {target : signature.Srt} (whole : Class signature Parallel target) :=
  Σ source : signature.Srt, Factor source whole

abbrev TotalReading (target : signature.Srt) :=
  Σ source : signature.Srt, Reading (Parallel := Parallel) source target

def totalReading {target : signature.Srt} {whole : Class signature Parallel target}
    (supplied : TotalFactor whole) : TotalReading (Parallel := Parallel) target :=
  ⟨supplied.1, supplied.2.val⟩

theorem totalReading_injective {target : signature.Srt} {whole : Class signature Parallel target} :
    Function.Injective (totalReading (whole := whole)) := by
  rintro ⟨firstSort, first⟩ ⟨secondSort, second⟩ same
  obtain ⟨sorts, readings⟩ := Sigma.mk.inj_iff.mp same
  change firstSort = secondSort at sorts
  change HEq first.val second.val at readings
  subst secondSort
  have values : first.val = second.val := eq_of_heq readings
  have factors : first = second := Subtype.ext values
  subst second
  rfl

abbrev TotalParallelFactor {target : signature.Srt} (whole : Class signature Parallel target) :=
  {supplied : TotalFactor whole // supplied.2.val.1.frameCount = 0}

abbrev TotalFramedFactor {target : signature.Srt} (whole : Class signature Parallel target) :=
  {supplied : TotalFactor whole // 0 < supplied.2.val.1.frameCount}

theorem totalParallel_outer_injective {target : signature.Srt}
    (whole : Class signature Parallel target) :
    Function.Injective (fun supplied : TotalParallelFactor whole => outerResidue supplied.val.2) := by
  rintro ⟨⟨firstSort, ⟨⟨first, before⟩, firstRead⟩⟩, firstCount⟩
    ⟨⟨secondSort, ⟨⟨second, after⟩, secondRead⟩⟩, secondCount⟩ same
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

theorem totalParallelFactor_finite {target : signature.Srt}
    (whole : Class signature Parallel target) : Finite (TotalParallelFactor whole) := by
  let _ := boundedResidue_finite whole
  exact Finite.of_injective _ (totalParallel_outer_injective whole)

abbrev TotalFrameCode {target : signature.Srt} (whole : Class signature Parallel target) :=
  BoundedResidue whole ×
    (Σ head : OccurringHead whole, Σ position : Head.Position head.val,
      TotalFactor (Head.child head.val position))

def TotalFrameCode.reading {target : signature.Srt} {whole : Class signature Parallel target}
    (code : TotalFrameCode whole) : TotalReading (Parallel := Parallel) target :=
  ⟨code.2.2.2.1,
    (.frame code.1.val (Head.frame code.2.1.val code.2.2.1) code.2.2.2.2.val.1, code.2.2.2.2.val.2)⟩

def totalFramedCode {target : signature.Srt} {whole : Class signature Parallel target}
    (supplied : TotalFramedFactor whole) : TotalFrameCode whole :=
  let code := framedCode (⟨supplied.val.2, supplied.property⟩ : FramedFactor supplied.val.1 whole)
  ⟨code.1, ⟨code.2.1, code.2.2.1, ⟨supplied.val.1, code.2.2.2⟩⟩⟩

theorem totalFramedCode_reading {target : signature.Srt} {whole : Class signature Parallel target}
    (supplied : TotalFramedFactor whole) :
    (totalFramedCode supplied).reading = totalReading supplied.val :=
  congrArg (Sigma.mk supplied.val.1)
    (framedCode_reading (⟨supplied.val.2, supplied.property⟩ : FramedFactor supplied.val.1 whole))

theorem totalFramedCode_injective {target : signature.Srt} {whole : Class signature Parallel target} :
    Function.Injective (totalFramedCode (whole := whole)) := by
  intro first second same
  apply Subtype.ext
  apply totalReading_injective
  exact (totalFramedCode_reading first).symm.trans
    ((congrArg TotalFrameCode.reading same).trans (totalFramedCode_reading second))

theorem totalFactor_finite_of_children {target : signature.Srt}
    (whole : Class signature Parallel target)
    (children : ∀ head ∈ inventoryQ whole, ∀ position : Head.Position head,
      Finite (TotalFactor (Head.child head position))) : Finite (TotalFactor whole) := by
  classical
  let _ := boundedResidue_finite whole
  let _ := occurringHead_finite whole
  let _ : ∀ head : OccurringHead whole, ∀ position : Head.Position head.val,
      Finite (TotalFactor (Head.child head.val position)) :=
    fun head position => children head.val head.property position
  let _ : Finite (TotalFrameCode whole) := inferInstance
  let _ : Finite (TotalFramedFactor whole) := Finite.of_injective _ totalFramedCode_injective
  let _ := totalParallelFactor_finite whole
  apply Finite.of_surjective
    (Sum.elim (Subtype.val : TotalParallelFactor whole → TotalFactor whole)
      (Subtype.val : TotalFramedFactor whole → TotalFactor whole))
  intro supplied
  by_cases noFrame : supplied.2.val.1.frameCount = 0
  · exact ⟨.inl ⟨supplied, noFrame⟩, rfl⟩
  · exact ⟨.inr ⟨supplied, Nat.pos_of_ne_zero noFrame⟩, rfl⟩

private theorem term_totalFactor_and_children_finite
    {target : signature.Srt} (supplied : Term signature Parallel target) :
    Finite (TotalFactor (classOf supplied)) ∧
      (∀ head ∈ inventory supplied, ∀ position : Head.Position head,
        Finite (TotalFactor (Head.child head position))) := by
  induction supplied with
  | zero parallel =>
    have children : ∀ head ∈ inventory (Term.zero parallel : Term signature Parallel _),
        ∀ position : Head.Position head, Finite (TotalFactor (Head.child head position)) := by
      intro head member
      exact (Multiset.notMem_zero head member).elim
    exact ⟨totalFactor_finite_of_children _ children, children⟩
  | cut parallel first second firstIH secondIH =>
    have children : ∀ head ∈ inventory (.cut parallel first second),
        ∀ position : Head.Position head, Finite (TotalFactor (Head.child head position)) := by
      intro head member
      rcases Multiset.mem_add.mp member with firstMember | secondMember
      · exact firstIH.2 head firstMember
      · exact secondIH.2 head secondMember
    exact ⟨totalFactor_finite_of_children _ children, children⟩
  | node constructor arguments inductionHypothesis =>
    have children : ∀ head ∈ inventory (.node constructor arguments),
        ∀ position : Head.Position head, Finite (TotalFactor (Head.child head position)) := by
      intro head member
      have same : head = SortedCommutative.Head.node constructor (fun position => classOf (arguments position)) :=
        Multiset.mem_singleton.mp member
      subst head
      intro position
      exact (inductionHypothesis position).1
    exact ⟨totalFactor_finite_of_children _ children, children⟩

theorem totalFactor_finite {target : signature.Srt}
    (whole : Class signature Parallel target) : Finite (TotalFactor whole) := by
  induction whole using Quotient.inductionOn with
  | _ representative => exact (term_totalFactor_and_children_finite representative).1

end Mettapedia.OSLF.SortedCommutative.GroundFactors
