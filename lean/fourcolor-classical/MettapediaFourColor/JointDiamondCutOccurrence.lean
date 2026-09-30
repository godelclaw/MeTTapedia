import MettapediaFourColor.JointDiamondWiredOccurrence
import MettapediaFourColor.JointDiamondCutLifting

/-! # Actual source cuts behind the coupled diamond wiring

The source reassembly transports both dart cut cost and vertex counts.
Consequently the original internal-six normal form applies to the cut
extensions of the literal coupled replacement.
-/

namespace FourColor.JointDiamondPatch.Tangle.Occurrence
open Mettapedia.GraphTheory.FourColor
open SimpleGraphDartRotation GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24VertexSideReassembly
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24CompositeSeamMultigraph GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality GoertzelV24WeightedOrbitFaceCorridor
open GoertzelV24CubicSmallBoundaryCycle RotationCutDartSum
open OpenTangleBoundaryConnectivity GoertzelV24SimpleGraphFaceDualConnectedness

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (deleted : Finset V)
  (root : RetainedDart rotation.toRotationSystem (deletedSideKeep deleted))
  (R : OpenTangleIsomorphism.Iso piece
    (ofVertexSide rotation.toRotationSystem (deletedSideKeep deleted) root))

abbrev original := CutLifting.original (normalizedOutside rotation deleted root R)

def sourceVertices : ({v // deletedRegionKeep deleted v} ⊕ Fin 14) ≃ V :=
  (Equiv.sumCongr (Equiv.refl _) R.vertex).trans (complementaryVertexEquiv deleted)

def sourceDarts : (original rotation deleted root R).D ≃ rotation.toRotationSystem.D :=
  (Equiv.sumCongr (Equiv.sumCongr (Equiv.refl _) R.interior)
    (Equiv.sumCongr (ports rotation deleted root R) R.boundary)).trans
      (complementaryDartEquiv rotation.toRotationSystem deleted
        ((ports rotation deleted root R 0).1) root)

theorem sourceDarts_alpha (d : (original rotation deleted root R).D) :
    sourceDarts rotation deleted root R ((original rotation deleted root R).alpha d) =
      rotation.toRotationSystem.alpha (sourceDarts rotation deleted root R d) := by
  rcases d with (i | j) | (b | c)
  · rfl
  · exact actual_alpha rotation.toRotationSystem (deletedSideKeep deleted) root R j
  · have hp : complementBoundaryAlphaEquiv rotation.toRotationSystem deleted
        (ports rotation deleted root R b) = R.boundary b := by simp [ports]
    have hh := complementBoundaryAlphaEquiv_val rotation.toRotationSystem deleted
      (ports rotation deleted root R b)
    rw [hp] at hh
    exact hh
  · exact complementBoundaryAlphaEquiv_symm_val rotation.toRotationSystem deleted (R.boundary c)

theorem sourceDarts_vertex (d : (original rotation deleted root R).D) :
    sourceVertices rotation deleted root R ((original rotation deleted root R).vertOf d) =
      rotation.toRotationSystem.vertOf (sourceDarts rotation deleted root R d) := by
  rcases d with (i | j) | (b | c)
  · rfl
  · exact congrArg Subtype.val (R.vert (.inl j))
  · rfl
  · exact congrArg Subtype.val (R.vert (.inr c))

theorem sourceDarts_left (d : InternalDart rotation.toRotationSystem (deletedRegionKeep deleted) ⊕ Fin 8) :
    sourceDarts rotation deleted root R (composeDartEquiv (.inl d)) =
      ((retainedDartEquivInternalSumBoundary rotation.toRotationSystem
        (deletedRegionKeep deleted)).symm
        (boundaryReindexDartEquiv (ports rotation deleted root R) d)).1 := by
  cases d <;> rfl

theorem sourceDarts_right (d : Dart) :
    sourceDarts rotation deleted root R (composeDartEquiv (.inr d)) =
      actual rotation.toRotationSystem (deletedSideKeep deleted) root R d := by
  cases d <;> rfl

theorem sourceDarts_rotation (d : (original rotation deleted root R).D) :
    sourceDarts rotation deleted root R ((original rotation deleted root R).rho d) =
      rotation.toRotationSystem.rho (sourceDarts rotation deleted root R d) := by
  obtain ⟨x, rfl⟩ := composeDartEquiv.surjective d
  change sourceDarts rotation deleted root R (composeDartEquiv
    ((Equiv.sumCongr (normalizedOutside rotation deleted root R).rho piece.rho)
      (composeDartEquiv.symm (composeDartEquiv x)))) = _
  rw [Equiv.symm_apply_apply]
  cases x with
  | inl d =>
    simp only [Equiv.sumCongr_apply, Sum.map_inl, sourceDarts_left]
    have he := (OpenTangleIsomorphism.boundaryReindex (outside rotation deleted root R)
      (ports rotation deleted root R)).rotation d
    change boundaryReindexDartEquiv (ports rotation deleted root R)
      ((normalizedOutside rotation deleted root R).rho d) =
      (outside rotation deleted root R).rho
        (boundaryReindexDartEquiv (ports rotation deleted root R) d) at he
    rw [he, ofVertexSide_rho_underlying]
    rfl
  | inr d =>
    simp only [Equiv.sumCongr_apply, Sum.map_inr, sourceDarts_right, actual_rho]

theorem source_cost (s : {v // deletedRegionKeep deleted v} ⊕ Fin 14 → Bool) :
    cost (original rotation deleted root R) s = cost rotation.toRotationSystem
      (s ∘ (sourceVertices rotation deleted root R).symm) := by
  have hh := cost_transport (original rotation deleted root R) rotation.toRotationSystem
    (sourceDarts rotation deleted root R) (sourceVertices rotation deleted root R)
    (sourceDarts_alpha rotation deleted root R) (sourceDarts_vertex rotation deleted root R)
    (s ∘ (sourceVertices rotation deleted root R).symm)
  simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using hh

variable (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
  (hminimum : OrbitFaceMinimumFive rotation.toRotationSystem)
  (hinternal : CubicDualInternallySixConnected G)

/-- Actual cut lifting rules out every new bridge, including old exterior
bridges that might otherwise be separated by the two free wires. -/
theorem wired_structural :
    (GoertzelV24FaceDualConnectedness.rotationPrimalGraph
      (wired rotation deleted root R h hminimum hinternal)).Connected ∧
    GoertzelV24RotationEdgeBridge.EdgeBridgeFree
      (wired rotation deleted root R h hminimum hinternal) := by
  have hcubic : G.IsRegularOfDegree 3 := fun v =>
    (degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp h.spherical.cubic) v)
  let e := sourceVertices rotation deleted root R
  have hthree (s : {v // deletedRegionKeep deleted v} ⊕ Fin 14 → Bool)
      (hy : 3 ≤ selected s) (hn : 3 ≤ selected (fun v => !(s v))) :
      10 ≤ cost (original rotation deleted root R) s := by
    rw [source_cost]
    apply InternalSixCutCost.ten_le_selected rotation hcubic hinternal
    · rwa [selected_transport]
    · change 3 ≤ selected ((fun v => !(s v)) ∘ e.symm)
      rwa [selected_transport]
  have hfive (s : {v // deletedRegionKeep deleted v} ⊕ Fin 14 → Bool)
      (hs : cost (original rotation deleted root R) s ≤ 10) :
      selected s ≤ 5 ∨ selected (fun v => !(s v)) ≤ 5 := by
    rw [source_cost] at hs
    have hh := InternalSixCutCost.small_selected rotation hcubic hinternal _ hs
    change selected (s ∘ e.symm) ≤ 5 ∨ selected ((fun v => !(s v)) ∘ e.symm) ≤ 5 at hh
    simpa only [selected_transport] using hh
  have hlow (s : {v // deletedRegionKeep deleted v} ⊕ Fin 14 → Bool)
      (hs : cost (original rotation deleted root R) s ≤ 2) (u v) : s u = s v := by
    rw [source_cost] at hs
    have hh := constant_of_structural rotation.toRotationSystem h.primalConnected
      h.edgeBridgeFree (s ∘ e.symm) hs (e u) (e v)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hh
  have hspace : 3 ≤ Fintype.card {v // deletedRegionKeep deleted v} := by
    have hh := exterior_card rotation deleted root R
    have ht := twenty_lt_vertices rotation.toRotationSystem (deletedSideKeep deleted)
      root R h.spherical hminimum
    omega
  apply CutLifting.structural (normalizedOutside rotation deleted root R)
    hthree hfive hspace hlow
  intro u v
  apply sideReach_of_induce_reachable rotation.toRotationSystem (deletedRegionKeep deleted)
    ((ports rotation deleted root R 0).1)
  have hh := (exterior_connected rotation deleted root R h hminimum hinternal).preconnected u v
  simpa only [VertexSideCappedComponents.SideGraph, rotationPrimalGraph_toRotationSystem_eq] using hh

end
end FourColor.JointDiamondPatch.Tangle.Occurrence
