import MettapediaFourColor.StripComplementaryRepair
import MettapediaFourColor.StripSixMixedExample
import MettapediaFourColor.GraphSphericalEuler

/-! # Both geometric repair branches on one existing sphere

The graph and its embedding are reused. Two proper exterior colourings
exercise respectively separate and joined zero/one components at ports
six and eight. The geometric theorem supplies the repair and the source
witness reconstructs the whole colouring.
-/

namespace FourColor.StripComplementaryExample

open SimpleGraph Color StripSixMixedExample
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24SimpleGraphFaceDualConnectedness
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

set_option maxRecDepth 10000

def values : Bool → Fin 33 → Color
  | false => ![
    c0,c1,c3,c0,c2,c3,c1,c2,c1,c3,c1,c0,c1,c0,c0,c3,
    c0,c2,c3,c2,c2,c2,c3,c3,c1,c1,c3,c0,c1,c1,c2,c1,
    c0]
  | true => ![
    c0,c1,c3,c0,c2,c3,c1,c2,c1,c3,c1,c0,c1,c0,c0,c3,
    c0,c2,c3,c1,c2,c2,c3,c3,c1,c1,c3,c0,c2,c1,c2,c1,
    c0]

theorem proper : ∀ s u v, exterior.Adj u v → values s u ≠ values s v := by decide +kernel
def state (s : Bool) : exterior.Coloring Color := .mk (values s) (fun h => proper s _ _ h)
theorem initial : ∀ s i, state s (port i) = StripComplementaryRepair.input i := by decide +kernel

def chain : Bool → List (Fin 33)
  | false => [6,27,31,11,24,11,31,27,6]
  | true => [6,27,31,11,19,16,12,3,12,16,25,13,1,0,10,32,8,32,10,0,29,14,29,0,1,13,25,16,19,11,24,11,31,27,6]

theorem chain_checked : ∀ s, (6 : Fin 33) ∈ chain s ∧
    (chain s).IsChain exterior.Adj ∧
    (∀ x ∈ chain s, state s x = c0 ∨ state s x = c1) ∧
    (∀ x ∈ chain s, ∀ y, exterior.Adj x y →
      (state s y = c0 ∨ state s y = c1) → y ∈ chain s) := by decide +kernel

def component (s : Bool) : KempeSeparatedChains.Certificate (state s) c0 c1 :=
  ⟨chain s,6,(chain_checked s).1,(chain_checked s).2.1,
    (chain_checked s).2.2.1,(chain_checked s).2.2.2⟩

theorem both_branches :
    port 8 ∉ (state false).kempeComponentSet c0 c1 (component false).component ∧
    port 1 ∉ (state false).kempeComponentSet c0 c1 (component false).component ∧
    port 6 ∈ (state true).kempeComponentSet c0 c1 (component true).component ∧
    port 8 ∈ (state true).kempeComponentSet c0 c1 (component true).component := by
  simp only [KempeSeparatedChains.Certificate.component_mem]
  decide +kernel

theorem ear_sides : StripComplementaryGeometry.EarSides patch := by
  constructor <;> apply Dart.ext <;> decide +kernel

/-- Both cases use geometric supply rather than a prechecked final component. -/
theorem source (s : Bool) :
    ∃ D : exterior.Coloring Color, ∃ h : History (state s) D, h.length = 1 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (StripResponseSummary.port i) = D (port i) :=
  StripComplementaryGeometry.repair patch ear_sides
    (hasCyclicVertexRotations_implies_vertexRotationCyclic ambient rotation cyclic)
    (GoertzelV24NonisolatedFaceDualConnectedness.orbitFaceInteriorDual_connected_of_simpleGraph
      rotation connected cyclic)
    connected
    (GraphSphericalEuler.balance rotation cyclic connected
      (GraphTriangulationEuler.covered connected) planar)
    reading (state s) (initial s)

theorem reconstructed (s : Bool) :
    ∃ D : exterior.Coloring Color, ∃ h : History (state s) D, h.length = 1 ∧
      ∃ whole : ambient.Coloring Color, ∀ v, whole (includeExterior v) = D v := by
  obtain ⟨D,h,one,k,agree⟩ := source s
  exact ⟨D,h,one,assemble D k agree⟩

end FourColor.StripComplementaryExample
