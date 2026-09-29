import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideReassembly
import Mettapedia.GraphTheory.FourColor.RotationSystemExactTransport

/-! # Geometric reassembly of complementary vertex shores

The canonical reassembly also intertwines rotations, so every field of the
bridgeless spherical cubic class transports from the original map.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexSideExactReassembly

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24VertexSideReassembly GoertzelV24RotationCutDartDecomposition
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24TwoEdgeCutMinimality

noncomputable section
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E) (deleted : Finset V)
  (outside : RetainedDart RS (deletedRegionKeep deleted))
  (inside : RetainedDart RS (deletedSideKeep deleted))

theorem left (d : InternalDart RS (deletedRegionKeep deleted) ⊕
    BoundaryDart RS (deletedRegionKeep deleted)) :
    complementaryDartEquiv RS deleted outside inside (composeDartEquiv (.inl d)) =
      ((retainedDartEquivInternalSumBoundary RS (deletedRegionKeep deleted)).symm d).1 := by
  cases d <;> rfl

theorem right (d : InternalDart RS (deletedSideKeep deleted) ⊕
    BoundaryDart RS (deletedSideKeep deleted)) :
    complementaryDartEquiv RS deleted outside inside (composeDartEquiv (.inr d)) =
      ((retainedDartEquivInternalSumBoundary RS (deletedSideKeep deleted)).symm d).1 := by
  cases d <;> rfl

theorem rotation (d : (complementaryCompositeRS RS deleted outside inside).D) :
    complementaryDartEquiv RS deleted outside inside
      ((complementaryCompositeRS RS deleted outside inside).rho d) =
      RS.rho (complementaryDartEquiv RS deleted outside inside d) := by
  obtain ⟨x, rfl⟩ := composeDartEquiv.surjective d
  change complementaryDartEquiv RS deleted outside inside (composeDartEquiv
    ((Equiv.sumCongr (ofVertexSide RS _ outside).rho (ofVertexSide RS _ inside).rho)
      (composeDartEquiv.symm (composeDartEquiv x)))) = _
  rw [Equiv.symm_apply_apply]
  cases x with
  | inl x =>
    simp only [Equiv.sumCongr_apply, Sum.map_inl, left, ofVertexSide_rho_underlying]
    rfl
  | inr x =>
    simp only [Equiv.sumCongr_apply, Sum.map_inr, right, ofVertexSide_rho_underlying]
    rfl

theorem mapClass (h : BridgelessSphericalCubicMapData RS) :
    BridgelessSphericalCubicMapData (complementaryCompositeRS RS deleted outside inside) := by
  let d := complementaryDartEquiv RS deleted outside inside
  let v := complementaryVertexEquiv deleted
  apply RotationSystemExactTransport.mapClass RS _ d.symm v.symm _ _ _ h
  · intro x
    apply d.injective
    rw [Equiv.apply_symm_apply, complementaryDartEquiv_alpha, Equiv.apply_symm_apply]
  · intro x
    apply v.injective
    rw [Equiv.apply_symm_apply, complementaryDartEquiv_vertOf, Equiv.apply_symm_apply]
  · intro x
    apply d.injective
    rw [Equiv.apply_symm_apply, rotation, Equiv.apply_symm_apply]

end
end Mettapedia.GraphTheory.FourColor.VertexSideExactReassembly
