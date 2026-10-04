import MettapediaFourColor.StripSixBarrierRepair
import MettapediaFourColor.StripSixReleaseExample
import MettapediaFourColor.GraphSphericalEuler

/-! # The preserved path repair on the existing 32-vertex sphere

Reuse the actual sphere and initial colouring. Starting-state components
and the old path are checked; geometry derives the second component's
protected ports, and the shared core formula reconstructs the whole map.
-/

namespace FourColor.StripSixBarrierExample

open SimpleGraph Color StripResponseSummary StripSixReleaseExample
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24SimpleGraphFaceDualConnectedness
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

set_option maxRecDepth 10000

theorem face_data : ∀ a b c, (a,b,c) ∈ StripSixBarrierGeometry.triangles →
    ambient.Adj (sourceVertex a) (sourceVertex b) ∧
    ambient.Adj (sourceVertex b) (sourceVertex c) ∧
    ambient.Adj (sourceVertex c) (sourceVertex a) ∧
    faceStep (sourceVertex a,sourceVertex b) = (sourceVertex b,sourceVertex c) ∧
    faceStep (sourceVertex b,sourceVertex c) = (sourceVertex c,sourceVertex a) ∧
    faceStep (sourceVertex c,sourceVertex a) = (sourceVertex a,sourceVertex b) := by
  decide +kernel

def patch : StripSixBarrierGeometry.Patch rotation where
  point := sourceVertex
  injective := source_injective
  adjacent := source_edges
  facial := by
    intro a b c h
    obtain ⟨ab,bc,ca,hab,hbc,hca⟩ := face_data a b c h
    refine ⟨ab,bc,ca,?_,?_,?_⟩
    · apply Dart.ext; exact hab
    · apply Dart.ext; exact hbc
    · apply Dart.ext; exact hca

def exteriorEmbedding : exterior ↪g ambient where
  toFun := includeExterior
  inj' := by intro u v h; exact Fin.ext (congrArg (fun x : Fin 32 => x.val) h)
  map_rel_iff' := fun {_ _} => (exterior_adj _ _).symm

def reading : StripSixBarrierGeometry.ExteriorReading patch exterior where
  embedding := exteriorEmbedding
  outside := by
    intro w i hi h
    change includeExterior w = sourceVertex i at h
    have shape : ∀ i : Fin 19, 11 ≤ i.val → 24 ≤ (sourceVertex i).val := by decide +kernel
    have eq := congrArg (fun x : Fin 32 => x.val) h
    have bound := shape i hi
    change w.val = (sourceVertex i).val at eq
    omega
  ports := StripSixReleaseExample.port
  boundary := fun i => (boundary_aligned i).symm

def eightChain : List (Fin 24) := [8,20,16,20,8]
theorem eight_checked : (8 : Fin 24) ∈ eightChain ∧ eightChain.IsChain exterior.Adj ∧
    (∀ x ∈ eightChain, state 0 x = c0 ∨ state 0 x = c1) ∧
    (∀ x ∈ eightChain, ∀ y, exterior.Adj x y →
      (state 0 y = c0 ∨ state 0 y = c1) → y ∈ eightChain) := by decide +kernel

def eight : KempeSeparatedChains.Certificate (state 0) c0 c1 where
  vertices := eightChain
  root := 8
  root_mem := eight_checked.1
  connected := eight_checked.2.1
  active := eight_checked.2.2.1
  closed := eight_checked.2.2.2

theorem eight_members : ∀ i, StripSixReleaseExample.port i ∈
    (state 0).kempeComponentSet c0 c1 eight.component ↔ i = 8 :=
  StripSixBarrierRepair.eight_members (state 0) StripSixReleaseExample.port port_edges
    initial_form first.component eight.component at_one at_six avoids_eight
    ((eight.component_mem _).mpr (by decide +kernel))

def connectionVertices : List (Fin 24) := [2,15,22,4]
theorem connection_chain : connectionVertices.IsChain exterior.Adj := by decide +kernel

def connection : exterior.Walk (StripSixReleaseExample.port 2)
    (StripSixReleaseExample.port 4) :=
  (Walk.ofSupport connectionVertices (by decide +kernel) connection_chain).copy rfl rfl

theorem connection_active : ∀ x ∈ connection.support, state 0 x = c0 ∨ state 0 x = c2 := by
  decide +kernel

theorem connection_apart : ∀ x ∈ connection.support,
    x ∉ (state 0).kempeComponentSet c0 c1 eight.component := by
  intro x hx
  rw [eight.component_mem]
  exact (by decide +kernel : ∀ x ∈ connection.support, x ∉ eightChain) x hx

/-- The second component's geometry and core colours are derived. -/
theorem source : ∃ D : exterior.Coloring Color, ∃ h : History (state 0) D,
    h.length = 2 ∧ ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      ∀ i, k (StripResponseSummary.port i) = D (StripSixReleaseExample.port i) :=
  reading.repair_of_preserved_path
    (hasCyclicVertexRotations_implies_vertexRotationCyclic ambient rotation cyclic)
    (GoertzelV24NonisolatedFaceDualConnectedness.orbitFaceInteriorDual_connected_of_simpleGraph
      rotation connected cyclic)
    connected
    (GraphSphericalEuler.balance rotation cyclic connected
      (GraphTriangulationEuler.covered connected) planar)
    (state 0) false connection connection_active initial_form eight.component
    eight_members connection_apart

theorem reconstructed : ∃ D : exterior.Coloring Color, ∃ h : History (state 0) D,
    h.length = 2 ∧ ∃ whole : ambient.Coloring Color,
      ∀ v, whole (includeExterior v) = D v := by
  obtain ⟨D,h,two,k,agree⟩ := source
  exact ⟨D,h,two,assemble D k agree⟩

end FourColor.StripSixBarrierExample
