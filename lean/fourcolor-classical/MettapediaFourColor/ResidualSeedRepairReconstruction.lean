import MettapediaFourColor.ResidualSeedRepairChecked
import MettapediaFourColor.ThreeBlockReconstruction
import MettapediaFourColor.GraphTraceAlignment
import MettapediaFourColor.OpenTangleKempeClosure

/-!
# Witness consumers of the compact D0092 seed repair

The open-tangle consumer obtains closure from genuine physical components
with noncrossing boundary pairings. It returns both an actual exterior
colouring and an actual source colouring on the same complete trace.

The embedded-graph consumer aligns source and exterior colours and fills
the seven deleted vertices. For that vertex-graph representation, closure
remains explicit: this file does not identify the two representations or
prove geometric supply of the seed boundary class.
-/

namespace FourColor.ResidualSeedRepairCertificate

open Color FiveTriangleCollapseObstruction KempeBoundarySplit
open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition
open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity
open Compositional.BoundaryKempeSwitch Compositional.CyclicBoundaryMatching
open PhysicalKempeBoundary (palette)

noncomputable section
universe u

/-- The same actual exterior, with its joint boundary observation, supplies
a compatible witness; no successful preparation or individual move is assumed. -/
theorem physical_exterior
    {V I B : Type u} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
    (T : OpenTangleData V I B) (order : Fin 11 ≃ B)
    (cubic : IsCubic (ofOpenTangleData T))
    (noncrossing : ∀ (c : PortTangle.Coloring (ofOpenTangleData T)) (hc : IsProper c),
      IsNoncrossingMatching (physicalMateInCoordinates order
        (ofOpenTangleData T) cubic c hc .bluePurple))
    (C : PortTangle.Coloring (ofOpenTangleData T)) (proper : IsProper C)
    (initial : List.ofFn (fun i => palette.symm (C.color (.inr (order i)))) = seedTrace) :
    ∃ k : upper.graph.Coloring Color,
      ∃ D : PortTangle.Coloring (ofOpenTangleData T), IsProper D ∧
        trace (upper.boundary.map k) =
          List.ofFn (fun i => palette.symm (D.color (.inr (order i)))) := by
  have closed := OpenTangleKempeRepair.closed_of_physical_noncrossing T order cubic noncrossing
  have start : OpenTangleKempeRepair.Trace T order seedTrace :=
    (OpenTangleKempeRepair.trace_iff_coloring T order).mpr ⟨C, proper, initial⟩
  obtain ⟨et, ⟨k, hk⟩, he⟩ := seed_repair _ closed start
  obtain ⟨D, hD, hd⟩ := (OpenTangleKempeRepair.trace_iff_coloring T order).mp he
  exact ⟨k, D, hD, hk.symm.trans hd.symm⟩

theorem source_boundary : upper.boundary = (List.finRange 11).map (Fin.castAdd 7) := by
  decide +kernel

/-- The seed cannot simply be filled while its boundary stays fixed. -/
theorem seed_not_direct : ¬ Supports seedTrace := by
  rintro ⟨k, ht⟩
  obtain ⟨D, hD⟩ := GraphTraceAlignment.align upper.boundary k
    ((List.finRange 11).map (ThreeBlockCore.word false false false))
    (by simp [source_boundary]) ht.symm
  have boundary (j : Fin 11) :
      D (j.castAdd 7) = ThreeBlockCore.word false false false j := by
    rw [source_boundary, List.map_map] at hD
    exact (List.map_eq_map_iff.mp hD) j (by simp)
  exact (ThreeBlockCore.necessary false false false D boundary).2 rfl

open SimpleGraph SimpleGraphDartRotation GoertzelV24FaceOrbitIncidence

/-- Closure in the vertex-graph representation plus this checked seed repair
reconstructs the complete ambient graph. Only the repaired exterior is fixed. -/
theorem whole_repair
    {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W}
    {data : Data G} {s : ThreeBlockGeometry.Patch data}
    (e : ThreeBlockGeometry.ExteriorReading s H)
    (covers : ∀ v, s.Exterior v → ∃ w, e.embedding w = v)
    (stars : ∀ i : Fin 18, 11 ≤ i.val → ∀ v, G.Adj (s.point i) v →
      ∃ j, s.point j = v ∧ upper.graph.Adj i j)
    (closed : KempeClosed (GraphTrace H ((List.finRange 11).map e.ports)))
    (C : H.Coloring Color)
    (initial : ∀ j, C (e.ports j) = ThreeBlockCore.word false false false j) :
    ∃ D : H.Coloring Color, ∃ K : G.Coloring Color,
      ∀ w, K (e.embedding w) = D w := by
  have start : GraphTrace H ((List.finRange 11).map e.ports) seedTrace := by
    refine ⟨C, ?_⟩
    simp only [seedTrace, List.map_map, Function.comp_def, initial]
  obtain ⟨et, ⟨inside, hins⟩, D, hout⟩ := seed_repair _ closed start
  have ht : trace (upper.boundary.map inside) =
      trace ((List.finRange 11).map (fun j => D (e.ports j))) := by
    simpa only [List.map_map, Function.comp_def] using hins.symm.trans hout
  obtain ⟨k, agree⟩ := GraphTraceAlignment.align upper.boundary inside
    ((List.finRange 11).map (fun j => D (e.ports j)))
    (by simp [source_boundary]) ht
  have boundary (j : Fin 11) : k (j.castAdd 7) = D (e.ports j) := by
    rw [source_boundary, List.map_map] at agree
    exact (List.map_eq_map_iff.mp agree) j (by simp)
  obtain ⟨K, he, _⟩ := e.reconstruct covers stars D k boundary
  exact ⟨D, K, he⟩

end
end FourColor.ResidualSeedRepairCertificate
