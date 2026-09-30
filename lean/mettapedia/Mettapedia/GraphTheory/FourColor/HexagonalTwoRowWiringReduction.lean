import Mettapedia.GraphTheory.FourColor.ZigzagTwoRowWiringFaces
import Mettapedia.GraphTheory.FourColor.HexagonalTubeTwistReduction
import Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryReindexWitness

/-!
# Free-wire reduction of an actual embedded two-row slab

The existing slab recognizer gives the literal rows, their entire exterior,
and an exact reassembly of the original map. Boundary reindexing puts that
exterior on the physical row coordinates. The two-shore and opposite-return
conditions then supply the strict free-wire reduction. These conditions
remain explicit; this module does not assert universal row occurrence.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.SlabOf

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24VertexSideReassembly
open GoertzelV24TwoEdgeCutMinimality SerialTangleSmallCutTransfer
open ZigzagRing OpenTanglePortReplacement

noncomputable section
universe u
attribute [local instance] Classical.propDecidable tubeVertexFintype tubeInteriorFintype
set_option backward.isDefEq.respectTransparency false
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {inner : V → Prop} {k : ℕ} [NeZero k]
  (S : SlabOf RS (tube k 1).data inner)

abbrev wireExterior := S.exterior.reindexBoundary S.outsideBoundaryEquiv
abbrev wireOriginal := ShiftedWiring.Geometry.original k S.wireExterior

def wireOldDarts : S.wireOriginal.D ≃ S.reassembled.D :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr S.outsideBoundaryEquiv (Equiv.refl _))

theorem wireOldDarts_reassoc (d) :
    S.wireOldDarts (composeDartEquiv d) = composeDartEquiv
      (Equiv.sumCongr (boundaryReindexDartEquiv S.outsideBoundaryEquiv) (Equiv.refl _) d) := by
  rcases d with (i | b) | (j | p) <;> rfl

theorem wireOldDarts_alpha (d : S.wireOriginal.D) :
    S.wireOldDarts (S.wireOriginal.alpha d) = S.reassembled.alpha (S.wireOldDarts d) := by
  rcases d with (a | i) | (b | p)
  · rfl
  · rfl
  · change Sum.inr (Sum.inr b) = Sum.inr (Sum.inr
      (S.outsideBoundaryEquiv.symm (S.outsideBoundaryEquiv b)))
    rw [Equiv.symm_apply_apply]
  · rfl

theorem wireOldDarts_vert (d : S.wireOriginal.D) :
    S.wireOriginal.vertOf d = S.reassembled.vertOf (S.wireOldDarts d) := by
  rcases d with (a | i) | (b | p) <;> rfl

theorem wireOldDarts_rho (d : S.wireOriginal.D) :
    S.wireOldDarts (S.wireOriginal.rho d) = S.reassembled.rho (S.wireOldDarts d) := by
  obtain ⟨x, rfl⟩ := composeDartEquiv.surjective d
  change S.wireOldDarts (composeDartEquiv ((Equiv.sumCongr S.wireExterior.rho
    (asOpen (tube k 1).data).rho) (composeDartEquiv.symm (composeDartEquiv x)))) =
    composeDartEquiv ((Equiv.sumCongr S.exterior.rho (asOpen (tube k 1).data).rho)
      (composeDartEquiv.symm (S.wireOldDarts (composeDartEquiv x))))
  rw [Equiv.symm_apply_apply, wireOldDarts_reassoc, wireOldDarts_reassoc, Equiv.symm_apply_apply]
  cases x with
  | inl d =>
    exact congrArg (composeDartEquiv ∘ Sum.inl)
      ((OpenTangleIsomorphism.boundaryReindex S.exterior S.outsideBoundaryEquiv).rotation d)
  | inr d => rfl

theorem wireOriginal_class (hS : S.RotationCompatible)
    (h : BridgelessSphericalCubicMapData RS) :
    BridgelessSphericalCubicMapData S.wireOriginal := by
  apply RotationSystemExactTransport.mapClass S.reassembled S.wireOriginal
    S.wireOldDarts.symm (Equiv.refl _) _ _ _ (S.reassembled_class hS h)
  · intro d
    apply S.wireOldDarts.injective
    simp only [Equiv.apply_symm_apply, wireOldDarts_alpha]
  · intro d
    exact ((S.wireOldDarts_vert (S.wireOldDarts.symm d)).trans
      (congrArg S.reassembled.vertOf (S.wireOldDarts.apply_symm_apply d))).symm
  · intro d
    apply S.wireOldDarts.injective
    simp only [Equiv.apply_symm_apply, wireOldDarts_rho]

abbrev wireShortened (H : ShiftedWiring.Geometry.TwoShores k S.wireExterior) :=
  ShiftedWiring.Geometry.closed k S.wireExterior H.separated

theorem wire_vertex_loss : Fintype.card V =
    Fintype.card {v : V // S.outsideKeep v} + 4 * k := by
  rw [← Fintype.card_congr S.exteriorVertexEquiv]
  exact ShiftedWiring.Geometry.vertex_loss k

theorem wire_reconstruct (hk : 3 ≤ k)
    (H : ShiftedWiring.Geometry.TwoShores k S.wireExterior)
    (c : (S.wireShortened H).EdgeColoring Color)
    (hc : (S.wireShortened H).IsTaitEdgeColoring c) :
    ∃ result : RS.EdgeColoring Color, RS.IsTaitEdgeColoring result ∧
      ∀ d, result (RS.edgeOf (S.exteriorDart (boundaryReindexDartEquiv S.outsideBoundaryEquiv d))) =
        c ((S.wireShortened H).edgeOf d) := by
  obtain ⟨old, hold, hout⟩ := ShiftedWiring.Geometry.reconstruct_colour k S.wireExterior
    hk H.separated c hc
  let e := S.wireOldDarts.trans S.reassemblyDartEquiv
  have ha (d) : e (S.wireOriginal.alpha d) = RS.alpha (e d) := by
    simp only [e, Equiv.trans_apply, wireOldDarts_alpha, reassemblyDartEquiv_alpha]
  have hv (d) : S.exteriorVertexEquiv (S.wireOriginal.vertOf d) = RS.vertOf (e d) := by
    rw [wireOldDarts_vert, reassemblyDartEquiv_vert]
    rfl
  obtain ⟨result, hresult, he⟩ := exists_taitColoring_of_dartEquiv S.wireOriginal RS
    e S.exteriorVertexEquiv ha hv old hold
  refine ⟨result, hresult, ?_⟩
  intro d
  have hh := he (composeDartEquiv (.inl d))
  simp only [e, Equiv.trans_apply, wireOldDarts_reassoc, Equiv.sumCongr_apply,
    Sum.map_inl, reassemblyDartEquiv_left] at hh
  exact hh.trans (hout d)

/-- The actual embedded rows disappear, with every exterior vertex retained. -/
theorem wire_reduction (hk : 3 ≤ k) (hS : S.RotationCompatible)
    (H : ShiftedWiring.Geometry.TwoShores k S.wireExterior)
    (hr : returnCode S.wireExterior = (boundaryPerm k)⁻¹)
    (h : BridgelessSphericalCubicMapData RS) :
    Fintype.card {v : V // S.outsideKeep v} < Fintype.card V ∧
      BridgelessSphericalCubicMapData (S.wireShortened H) ∧
      (RotationSystemTaitColorable (S.wireShortened H) → RotationSystemTaitColorable RS) := by
  refine ⟨?_, ShiftedWiring.Geometry.replacement_class k S.wireExterior
    (by omega) H hr (S.wireOriginal_class hS h), ?_⟩
  · have hh := S.wire_vertex_loss
    omega
  · rintro ⟨c, hc⟩
    obtain ⟨result, hresult, _⟩ := S.wire_reconstruct hk H c hc
    exact ⟨result, hresult⟩

variable {G : SimpleGraph V} [DecidableRel G.Adj]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- A minimal counterexample cannot contain a two-row slab with these
derived-or-supplied exterior conditions. No occurrence theorem is inferred. -/
theorem no_two_row_wire_domain (hk : 3 ≤ k) (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {inner : V → Prop} (S : SlabOf rotation.toRotationSystem (tube k 1).data inner)
    (hS : S.RotationCompatible)
    (H : ShiftedWiring.Geometry.TwoShores k S.wireExterior)
    (hr : returnCode S.wireExterior = (boundaryPerm k)⁻¹) : False := by
  obtain ⟨hcard, hclass, hcolour⟩ := S.wire_reduction hk hS H hr
    minimal.toBridgelessSphericalCubicMapData
  exact minimal.notColorable (hcolour (minimal.smallerColorable (S.wireShortened H) hcard hclass))

end
end Mettapedia.GraphTheory.FourColor.TubeSlab.SlabOf
