import Mettapedia.GraphTheory.FourColor.FrozenPhysicalCount
import Mettapedia.GraphTheory.FourColor.FrozenDartTransport

/-! # Observations of original ambient darts on sewn vertex sides

Each side observes exactly the named darts based at its vertices. On the
sewn map, these are read through the literal carrier reassociation. The
complementary-shore specialization identifies the result with prescribed
Tait colourability of the original ambient map.
-/

namespace Mettapedia.GraphTheory.FourColor.FrozenVertexSideCount

open GoertzelV24RotationCutDartDecomposition GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24VertexSideReassembly GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open FrozenCountSupport FrozenPhysicalCount

noncomputable section
universe u v
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {M : Type v} (RS : RotationSystem.{u,u,u} V E)

/-- An original ambient name is observed exactly on sides containing its base. -/
def sideObservation (keep : V → Prop) (mark : M → RS.D) (m : M) :
    Option (InternalDart RS keep ⊕ BoundaryDart RS keep) := by
  classical
  exact if h : keep (RS.vertOf (mark m)) then
    some (retainedDartEquivInternalSumBoundary RS keep ⟨mark m, h⟩) else none

theorem sideObservation_some_iff (keep : V → Prop) (mark : M → RS.D) (m : M)
    (d : InternalDart RS keep ⊕ BoundaryDart RS keep) :
    sideObservation RS keep mark m = some d ↔
      ((retainedDartEquivInternalSumBoundary RS keep).symm d).val = mark m := by
  classical
  let e := retainedDartEquivInternalSumBoundary RS keep
  by_cases h : keep (RS.vertOf (mark m))
  · simp only [sideObservation, dif_pos h, Option.some.injEq]
    constructor
    · intro hd
      have he : e.symm d = ⟨mark m, h⟩ := by rw [← hd]; exact e.symm_apply_apply _
      exact congrArg Subtype.val he
    · intro hd
      apply e.symm.injective
      rw [Equiv.symm_apply_apply]
      exact Subtype.ext hd.symm
  · simp only [sideObservation, dif_neg h, reduceCtorEq, false_iff]
    intro hd
    exact h (hd ▸ (e.symm d).property)

variable {RS}

/-- The literal ambient name of every dart of a sewn pair of vertex sides. -/
def ambientDart {A B : V → Prop} (a : RetainedDart RS A) (b : RetainedDart RS B)
    (matching : BoundaryDart RS A ≃ BoundaryDart RS B) :
    ((ofVertexSide RS A a).composeRotationSystem (ofVertexSide RS B b) matching).D → RS.D
  | Sum.inl (Sum.inl d) => d.val.val
  | Sum.inl (Sum.inr d) => d.val.val
  | Sum.inr (Sum.inl d) => d.val.val
  | Sum.inr (Sum.inr d) => d.val.val

theorem ambientDart_left {A B : V → Prop} (a : RetainedDart RS A) (b : RetainedDart RS B)
    (matching : BoundaryDart RS A ≃ BoundaryDart RS B)
    (d : InternalDart RS A ⊕ BoundaryDart RS A) :
    ambientDart a b matching (composeDartEquiv (Sum.inl d)) =
      ((retainedDartEquivInternalSumBoundary RS A).symm d).val := by
  cases d <;> rfl

theorem ambientDart_right {A B : V → Prop} (a : RetainedDart RS A) (b : RetainedDart RS B)
    (matching : BoundaryDart RS A ≃ BoundaryDart RS B)
    (d : InternalDart RS B ⊕ BoundaryDart RS B) :
    ambientDart a b matching (composeDartEquiv (Sum.inr d)) =
      ((retainedDartEquivInternalSumBoundary RS B).symm d).val := by
  cases d <;> rfl

/-- The side observations are precisely the prescription on every surviving
ambient-named dart of the actual sewn map. Existence of each named dart is
a separate geometric property; complementary shores supply it automatically. -/
theorem physicalAccepts_iff_ambient {A B : V → Prop}
    (a : RetainedDart RS A) (b : RetainedDart RS B)
    (matching : BoundaryDart RS A ≃ BoundaryDart RS B) (mark : M → RS.D) (value : M → Color) :
    PhysicalAccepts (ofVertexSide RS A a) (ofVertexSide RS B b) matching
      (sideObservation RS A mark) (sideObservation RS B mark) value ↔
      ∃ c : ((ofVertexSide RS A a).composeRotationSystem (ofVertexSide RS B b) matching).EdgeColoring Color,
        ((ofVertexSide RS A a).composeRotationSystem (ofVertexSide RS B b) matching).IsTaitEdgeColoring c ∧
        ∀ m d, ambientDart a b matching d = mark m →
          c (((ofVertexSide RS A a).composeRotationSystem (ofVertexSide RS B b) matching).edgeOf d) = value m := by
  constructor
  · rintro ⟨c, hc, hl, hr⟩
    refine ⟨c, hc, ?_⟩
    intro m d hd
    obtain ⟨e, rfl⟩ := composeDartEquiv.surjective d
    rcases e with e | e
    · exact hl m e ((sideObservation_some_iff RS A mark m e).mpr
        ((ambientDart_left a b matching e).symm.trans hd))
    · exact hr m e ((sideObservation_some_iff RS B mark m e).mpr
        ((ambientDart_right a b matching e).symm.trans hd))
  · rintro ⟨c, hc, hm⟩
    refine ⟨c, hc, ?_, ?_⟩
    · intro m d hd
      exact hm m (composeDartEquiv (Sum.inl d))
        ((ambientDart_left a b matching d).trans ((sideObservation_some_iff RS A mark m d).mp hd))
    · intro m d hd
      exact hm m (composeDartEquiv (Sum.inr d))
        ((ambientDart_right a b matching d).trans ((sideObservation_some_iff RS B mark m d).mp hd))

/-- The outside-first complementary reassembly uses literal ambient names. -/
def reassemblyEquiv (deleted : Finset V)
    (outside : RetainedDart RS (deletedSideKeep deleted))
    (inside : RetainedDart RS (deletedRegionKeep deleted)) :
    (swappedComplementaryCompositeRS RS deleted outside inside).D ≃ RS.D :=
  (swappedCompositeDartEquiv RS deleted outside inside).trans
    (complementaryDartEquiv RS deleted inside outside)

theorem reassemblyEquiv_name (deleted : Finset V)
    (outside : RetainedDart RS (deletedSideKeep deleted))
    (inside : RetainedDart RS (deletedRegionKeep deleted))
    (d : (swappedComplementaryCompositeRS RS deleted outside inside).D) :
    reassemblyEquiv deleted outside inside d =
      ambientDart outside inside (complementBoundaryAlphaEquiv RS deleted).symm d := by
  rcases d with (d | d) | (d | d) <;> rfl

/-- Prescribed colours, not merely ordinary colourability, reassemble on
the old ambient edge involution. -/
theorem physicalAccepts_reassembly_iff (deleted : Finset V)
    (outside : RetainedDart RS (deletedSideKeep deleted))
    (inside : RetainedDart RS (deletedRegionKeep deleted))
    (mark : M → RS.D) (value : M → Color) :
    PhysicalAccepts (ofVertexSide RS (deletedSideKeep deleted) outside)
      (ofVertexSide RS (deletedRegionKeep deleted) inside)
      (complementBoundaryAlphaEquiv RS deleted).symm
      (sideObservation RS (deletedSideKeep deleted) mark)
      (sideObservation RS (deletedRegionKeep deleted) mark) value ↔
      FrozenDartTransport.Accepts RS mark value := by
  rw [physicalAccepts_iff_ambient]
  let e := reassemblyEquiv deleted outside inside
  let f := (Equiv.sumComm {v : V // deletedSideKeep deleted v}
    {v : V // deletedRegionKeep deleted v}).trans (complementaryVertexEquiv deleted)
  have ha : ∀ d, e ((swappedComplementaryCompositeRS RS deleted outside inside).alpha d) =
      RS.alpha (e d) := by
    intro d
    change complementaryDartEquiv RS deleted inside outside
      (swappedCompositeDartEquiv RS deleted outside inside
        ((swappedComplementaryCompositeRS RS deleted outside inside).alpha d)) = _
    rw [swappedCompositeDartEquiv_alpha, complementaryDartEquiv_alpha]
    rfl
  have hv : ∀ d, f ((swappedComplementaryCompositeRS RS deleted outside inside).vertOf d) =
      RS.vertOf (e d) := by
    intro d
    change complementaryVertexEquiv deleted
      ((Equiv.sumComm _ _) ((swappedComplementaryCompositeRS RS deleted outside inside).vertOf d)) = _
    rw [swappedCompositeDartEquiv_vertOf, complementaryDartEquiv_vertOf]
    rfl
  have h := FrozenDartTransport.accepts_iff_named
    (swappedComplementaryCompositeRS RS deleted outside inside) RS e f ha hv mark value
  simpa only [e, reassemblyEquiv_name] using h

end
end Mettapedia.GraphTheory.FourColor.FrozenVertexSideCount
