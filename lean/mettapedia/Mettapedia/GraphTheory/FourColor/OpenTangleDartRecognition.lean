import Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphism

/-!
# Recognizing a vertex side from all of its actual darts

A vertex bijection and a bijection of the entire dart carrier suffice to
construct an open-tangle isomorphism. The dart map must classify exposed
half-edges correctly and commute with actual edge and vertex permutations.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphism

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition

noncomputable section
variable {W I B V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (P : OpenTangleData W I B) (RS : RotationSystem V E) (keep : V → Prop)
  (root : RetainedDart RS keep)
  (vertices : W ≃ {v // keep v})
  (darts : I ⊕ B ≃ RetainedDart RS keep)
  (hi : ∀ i, keep (RS.vertOf (RS.alpha (darts (.inl i)).1)))
  (hb : ∀ b, ¬ keep (RS.vertOf (RS.alpha (darts (.inr b)).1)))

def internalCoordinate : I ≃ InternalDart RS keep :=
  Equiv.ofBijective (fun i => ⟨darts (.inl i), hi i⟩) ⟨by
    intro i j h
    exact Sum.inl.inj (darts.injective (congrArg Subtype.val h)), by
    intro d
    obtain ⟨i | b, hd⟩ := darts.surjective d.1
    · exact ⟨i, Subtype.ext hd⟩
    · exact (hb b (hd.symm ▸ d.2)).elim⟩

def boundaryCoordinate : B ≃ BoundaryDart RS keep :=
  Equiv.ofBijective (fun b => ⟨darts (.inr b), hb b⟩) ⟨by
    intro b c h
    exact Sum.inr.inj (darts.injective (congrArg Subtype.val h)), by
    intro d
    obtain ⟨i | b, hd⟩ := darts.surjective d.1
    · exact (d.2 (hd ▸ hi i)).elim
    · exact ⟨b, Subtype.ext hd⟩⟩

theorem sumCoordinate (d : I ⊕ B) :
    Equiv.sumCongr (internalCoordinate RS keep darts hi hb)
      (boundaryCoordinate RS keep darts hi hb) d =
        retainedDartEquivInternalSumBoundary RS keep (darts d) := by
  cases d with
  | inl i => exact ((retainedDartEquivInternalSumBoundary RS keep).apply_symm_apply
      (.inl (internalCoordinate RS keep darts hi hb i))).symm
  | inr b => exact ((retainedDartEquivInternalSumBoundary RS keep).apply_symm_apply
      (.inr (boundaryCoordinate RS keep darts hi hb b))).symm

/-- All fields describe independently checkable incidence equations. The
result can be sewn into every context using the existing isomorphism laws. -/
def ofRetainedDarts
    (ha : ∀ i, (darts (.inl (P.interiorAlpha i))).1 = RS.alpha (darts (.inl i)).1)
    (hv : ∀ d, vertices (P.vertOf d) = vertexSideVertex RS keep (darts d))
    (hr : ∀ d, darts (P.rho d) = retainedRho RS keep (darts d)) :
    Iso P (ofVertexSide RS keep root) where
  vertex := vertices
  interior := internalCoordinate RS keep darts hi hb
  boundary := boundaryCoordinate RS keep darts hi hb
  alpha i := by
    apply Subtype.ext
    apply Subtype.ext
    exact ha i
  vert d := by
    rw [sumCoordinate]
    change vertices (P.vertOf d) = openTangleVertOf
      (fun i : InternalDart RS keep => vertexSideVertex RS keep i.1)
      (fun b : BoundaryDart RS keep => vertexSideVertex RS keep b.1) _
    rw [openTangleVertOf_vertexSide_partition_symm, Equiv.symm_apply_apply]
    exact hv d
  rotation d := by
    rw [sumCoordinate, sumCoordinate]
    change retainedDartEquivInternalSumBoundary RS keep (darts (P.rho d)) =
      retainedDartEquivInternalSumBoundary RS keep (retainedRho RS keep
        ((retainedDartEquivInternalSumBoundary RS keep).symm
          (retainedDartEquivInternalSumBoundary RS keep (darts d))))
    rw [Equiv.symm_apply_apply, hr]

end
end Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphism
