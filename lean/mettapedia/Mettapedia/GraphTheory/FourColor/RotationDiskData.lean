import Mettapedia.GraphTheory.FourColor.BoundaryChains
import Mettapedia.GraphTheory.FourColor.RotationSystem

namespace Mettapedia.GraphTheory.FourColor

open Relation

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Abstract disk-style data built over a bare rotation system and the modern
zero-boundary algebra. This ports the useful data surface from the old
`DiskTypes.lean` without importing the old gap-bearing planar-geometry layer. -/
structure RotationDiskData (V E : Type*) [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] where
  rotation : RotationSystem V E
  zeroBoundarySet : Set (E → Color)
  asZeroBoundary : ZeroBoundaryData V E
  boundary_compat : asZeroBoundary.boundaryEdges = rotation.boundaryEdges
  incident_compat :
    ∀ v : V, ∀ e : E, e ∈ asZeroBoundary.incident v ↔
      ∃ d : rotation.D, rotation.edgeOf d = e ∧ rotation.vertOf d = v
  face_cycle_parity :
    ∀ {f : Finset E}, f ∈ rotation.internalFaces →
      ∀ v : V, Even (asZeroBoundary.incident v ∩ f).card

namespace RotationDiskData

/-- Face adjacency in the interior dual graph: two internal faces are adjacent
when they share an interior edge. -/
def dualAdjacent (G : RotationDiskData V E) (f g : Finset E) : Prop :=
  f ∈ G.rotation.internalFaces ∧
  g ∈ G.rotation.internalFaces ∧
  f ≠ g ∧
  ∃ e, e ∉ G.rotation.boundaryEdges ∧ e ∈ f ∧ e ∈ g

/-- A spanning forest witness for the interior dual graph, represented by the
selected primal edges. -/
structure SpanningForest (G : RotationDiskData V E) where
  tree_edges : Finset E
  tree_edges_interior : ∀ e ∈ tree_edges, e ∉ G.rotation.boundaryEdges
  dichotomy :
    ∀ e, e ∉ G.rotation.boundaryEdges →
      e ∈ tree_edges ∨
        (∃ f g, G.dualAdjacent f g ∧ e ∈ f ∧ e ∈ g ∧
          ReflTransGen
            (fun f' g' =>
              ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ f' ∧ e' ∈ g') f g)

/-- No two distinct internal faces share two distinct interior edges. -/
def NoDigons (G : RotationDiskData V E) : Prop :=
  G.rotation.NoInteriorDigons

/-- The no-digons condition can be used through the rotation-system vocabulary. -/
theorem noInteriorDigons_of_noDigons (G : RotationDiskData V E) :
    G.NoDigons → G.rotation.NoInteriorDigons :=
  id

/-- Direct disk-data form of the old no-digons elimination lemma: under the
explicit no-digons hypothesis, two distinct internal faces cannot share two
distinct interior edges. -/
theorem faces_share_at_most_one_interior_edge
    (G : RotationDiskData V E) (hNoDigons : G.NoDigons)
    {f g : Finset E} (hf : f ∈ G.rotation.internalFaces)
    (hg : g ∈ G.rotation.internalFaces) (hfg : f ≠ g)
    {e₁ e₂ : E} (he₁₂ : e₁ ≠ e₂)
    (he₁Interior : e₁ ∉ G.rotation.boundaryEdges)
    (he₂Interior : e₂ ∉ G.rotation.boundaryEdges)
    (he₁f : e₁ ∈ f) (he₁g : e₁ ∈ g)
    (he₂f : e₂ ∈ f) (he₂g : e₂ ∈ g) :
    False :=
  G.rotation.faces_share_at_most_one_interior_edge
    hNoDigons hf hg hfg he₁₂ he₁Interior he₂Interior
    he₁f he₁g he₂f he₂g

/-- Edge endpoints for disk data, inherited from its rotation system. -/
def edgeEndpoints (G : RotationDiskData V E) (e : E) : Finset V :=
  G.rotation.endpoints e

@[simp]
theorem mem_edgeEndpoints_iff (G : RotationDiskData V E) {e : E} {v : V} :
    v ∈ G.edgeEndpoints e ↔ e ∈ G.asZeroBoundary.incident v := by
  constructor
  · intro hv
    rcases (RotationSystem.mem_endpoints_iff (RS := G.rotation)).1 hv with ⟨d, hd, hdv⟩
    exact (G.incident_compat v e).2
      ⟨d, (RotationSystem.mem_dartsOn (RS := G.rotation)).1 hd, hdv⟩
  · intro he
    rcases (G.incident_compat v e).1 he with ⟨d, hde, hdv⟩
    exact (RotationSystem.mem_endpoints_iff (RS := G.rotation)).2
      ⟨d, (RotationSystem.mem_dartsOn (RS := G.rotation)).2 hde, hdv⟩

theorem edgeEndpoints_card_two (G : RotationDiskData V E) (e : E) :
    (G.edgeEndpoints e).card = 2 :=
  G.rotation.endpoints_card_two e

theorem asZeroBoundary_incident_eq_rotation_incidentEdges
    (G : RotationDiskData V E) (v : V) :
    G.asZeroBoundary.incident v = G.rotation.incidentEdges v := by
  ext e
  constructor
  · intro he
    rcases (G.incident_compat v e).1 he with ⟨d, hde, hdv⟩
    exact (RotationSystem.mem_incidentEdges_iff (RS := G.rotation)).2
      ⟨d, hde, hdv⟩
  · intro he
    rcases (RotationSystem.mem_incidentEdges_iff (RS := G.rotation)).1 he with
      ⟨d, hde, hdv⟩
    exact (G.incident_compat v e).2 ⟨d, hde, hdv⟩

end RotationDiskData

end Mettapedia.GraphTheory.FourColor
