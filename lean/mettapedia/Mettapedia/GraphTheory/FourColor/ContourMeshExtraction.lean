import Mettapedia.GraphTheory.FourColor.GoertzelV24InjectiveMeshWidthExclusion
import Mettapedia.GraphTheory.FourColor.FaceDistanceFrontiers

/-!
# Contours and a linkage construct an injective mesh

The mesh used by `RawDecompositionOfNoInjectiveMesh` needs neither a grid
minor model nor an order of crossings. Two families of paths, vertex-disjoint
within each family and meeting on every row-column pair, construct that exact
mesh. The chosen branch vertices are automatically distinct. Closed contour
walks are permitted by the existing `MeshPath` carrier.

The second constructor derives the intersections from complete edge-frontier
data and paths passing from the inside to the outside of each region. It does
not assume the branch vertices, and places no restrictions on lateral edges.
It does not construct the contours or the disjoint linkage from planarity;
those geometric obligations remain separate from this extraction step.
-/

namespace Mettapedia.GraphTheory.FourColor.ContourMeshExtraction

open GoertzelV24BoundaryEssentialGluing GoertzelV24MeshIsoperimetry
open GoertzelV24InjectiveMeshWidthExclusion

variable {V E : Type*} {g : Multigraph V E}

/-- Both endpoints of an edge appearing in a path occur on that path. -/
theorem edge_endpoints (p : MeshPath g) (t : Fin p.len) :
    (∃ s, p.vert s = g.fst (p.edge t)) ∧
      (∃ s, p.vert s = g.snd (p.edge t)) := by
  rcases p.edge_ends t with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨⟨t.castSucc, h₁.symm⟩, ⟨t.succ, h₂.symm⟩⟩
  · exact ⟨⟨t.succ, h₁.symm⟩, ⟨t.castSucc, h₂.symm⟩⟩

/-- Vertex-disjoint families are edge-disjoint, including in multigraphs. -/
theorem edges_disjoint {I : Type*} (paths : I → MeshPath g)
    (hdisjoint : ∀ i j, i ≠ j → ∀ s t, (paths i).vert s ≠ (paths j).vert t) :
    ∀ i j, i ≠ j → ∀ s t, (paths i).edge s ≠ (paths j).edge t := by
  intro i j hij s t heq
  obtain ⟨u, hu⟩ := (edge_endpoints (paths i) s).1
  obtain ⟨v, hv⟩ := (edge_endpoints (paths j) t).1
  exact hdisjoint i j hij u v (hu.trans ((congrArg g.fst heq).trans hv.symm))

/-- Choose actual row-column intersections and package the existing mesh. -/
noncomputable def ofPaths {a b : ℕ}
    (rows : Fin a → MeshPath g) (cols : Fin b → MeshPath g)
    (hr : ∀ i j, i ≠ j → ∀ s t, (rows i).vert s ≠ (rows j).vert t)
    (hc : ∀ i j, i ≠ j → ∀ s t, (cols i).vert s ≠ (cols j).vert t)
    (hmeet : ∀ i j, ∃ s t, (rows i).vert s = (cols j).vert t) : Mesh g a b where
  row := rows
  col := cols
  branch i j := (rows i).vert (hmeet i j).choose
  branch_mem_row i j := ⟨(hmeet i j).choose, rfl⟩
  branch_mem_col i j := ⟨(hmeet i j).choose_spec.choose,
    (hmeet i j).choose_spec.choose_spec.symm⟩
  row_edges_disjoint := edges_disjoint rows hr
  col_edges_disjoint := edges_disjoint cols hc

/-- Disjoint rows and columns force the chosen branch positions to be injective. -/
theorem ofPaths_isVertexInjective {a b : ℕ}
    (rows : Fin a → MeshPath g) (cols : Fin b → MeshPath g)
    (hr : ∀ i j, i ≠ j → ∀ s t, (rows i).vert s ≠ (rows j).vert t)
    (hc : ∀ i j, i ≠ j → ∀ s t, (cols i).vert s ≠ (cols j).vert t)
    (hmeet : ∀ i j, ∃ s t, (rows i).vert s = (cols j).vert t) :
    IsVertexInjective (ofPaths rows cols hr hc hmeet) := by
  intro p q hpq
  let M := ofPaths rows cols hr hc hmeet
  obtain ⟨s, hs⟩ := M.branch_mem_row p.1 p.2
  obtain ⟨t, ht⟩ := M.branch_mem_row q.1 q.2
  obtain ⟨u, hu⟩ := M.branch_mem_col p.1 p.2
  obtain ⟨v, hv⟩ := M.branch_mem_col q.1 q.2
  have hrow : p.1 = q.1 := by
    by_contra hne
    exact hr _ _ hne s t (hs.trans (hpq.trans ht.symm))
  have hcol : p.2 = q.2 := by
    by_contra hne
    exact hc _ _ hne u v (hu.trans (hpq.trans hv.symm))
  exact Prod.ext hrow hcol

/-- Construct the exact existential consumed by fixed injective-mesh exclusion. -/
theorem exists_injectiveMesh_of_paths {a b : ℕ}
    (rows : Fin a → MeshPath g) (cols : Fin b → MeshPath g)
    (hr : ∀ i j, i ≠ j → ∀ s t, (rows i).vert s ≠ (rows j).vert t)
    (hc : ∀ i j, i ≠ j → ∀ s t, (cols i).vert s ≠ (cols j).vert t)
    (hmeet : ∀ i j, ∃ s t, (rows i).vert s = (cols j).vert t) :
    ∃ M : Mesh g a b, IsVertexInjective M :=
  ⟨ofPaths rows cols hr hc hmeet, ofPaths_isVertexInjective rows cols hr hc hmeet⟩

section Frontier

variable [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A contour contains the outside endpoint of every edge leaving a region.
This is checked on all ambient edges, not only edges in the selected paths. -/
def CoversOuterFrontier (row : MeshPath g) (S : Finset V) : Prop :=
  ∀ e, (g.fst e ∈ S → g.snd e ∉ S → ∃ t, row.vert t = g.snd e) ∧
    (g.snd e ∈ S → g.fst e ∉ S → ∃ t, row.vert t = g.fst e)

/-- Every path exiting a region meets a contour covering its outer frontier. -/
theorem meets_of_frontier (row col : MeshPath g) (S : Finset V)
    (hfrontier : CoversOuterFrontier row S)
    (hin : ∃ s, col.vert s ∈ S) (hout : ∃ t, col.vert t ∉ S) :
    ∃ s t, row.vert s = col.vert t := by
  obtain ⟨s, hs⟩ := hin
  obtain ⟨t, ht⟩ := hout
  obtain ⟨e, he⟩ := col.exists_boundary_edge S hs ht
  rcases he with ⟨hf, hn⟩ | ⟨hf, hn⟩
  · obtain ⟨r, hr⟩ := (hfrontier (col.edge e)).1 hf hn
    obtain ⟨c, hc⟩ := (edge_endpoints col e).2
    exact ⟨r, c, hr.trans hc.symm⟩
  · obtain ⟨r, hr⟩ := (hfrontier (col.edge e)).2 hn hf
    obtain ⟨c, hc⟩ := (edge_endpoints col e).1
    exact ⟨r, c, hr.trans hc.symm⟩

/-- Region-frontier data supplies all crossings, including paths whose
terminal is already on a contour. No ordered crossing hypothesis is needed. -/
theorem exists_injectiveMesh_of_frontiers {a b : ℕ}
    (rows : Fin a → MeshPath g) (cols : Fin b → MeshPath g)
    (regions : Fin a → Finset V)
    (hr : ∀ i j, i ≠ j → ∀ s t, (rows i).vert s ≠ (rows j).vert t)
    (hc : ∀ i j, i ≠ j → ∀ s t, (cols i).vert s ≠ (cols j).vert t)
    (hfrontier : ∀ i, CoversOuterFrontier (rows i) (regions i))
    (hin : ∀ i j, (∃ s t, (rows i).vert s = (cols j).vert t) ∨
      ∃ s, (cols j).vert s ∈ regions i)
    (hout : ∀ i j, ∃ t, (cols j).vert t ∉ regions i) :
    ∃ M : Mesh g a b, IsVertexInjective M := by
  apply exists_injectiveMesh_of_paths rows cols hr hc
  intro i j
  rcases hin i j with h | h
  · exact h
  · exact meets_of_frontier (rows i) (cols j) (regions i) (hfrontier i) h (hout i j)

end Frontier

/-- When rows enumerate actual distance frontiers, the metric construction
discharges their vertex-disjointness. Only the column family needs a disjoint
linkage proof. This feeds the exact injective-mesh existential, not a new
replacement notion of wall. -/
theorem exists_injectiveMesh_of_distanceFrontiers {F : Type*} {a b : ℕ}
    (H : SimpleGraph F) (root far : F) (incident : V → Set F)
    (hclique : ∀ v f h, f ∈ incident v → h ∈ incident v → f = h ∨ H.Adj f h)
    (depths : Fin a → ℕ) (hdepths : Function.Injective depths)
    (rows : Fin a → MeshPath g) (cols : Fin b → MeshPath g)
    (hrows : ∀ i s, FaceDistanceFrontiers.Mixed incident
      (FaceDistanceFrontiers.deepRegion H root far (depths i)) ((rows i).vert s))
    (hc : ∀ i j, i ≠ j → ∀ s t, (cols i).vert s ≠ (cols j).vert t)
    (hmeet : ∀ i j, ∃ s t, (rows i).vert s = (cols j).vert t) :
    ∃ M : Mesh g a b, IsVertexInjective M := by
  apply exists_injectiveMesh_of_paths rows cols ?_ hc hmeet
  intro i j hij s t heq
  have hd := FaceDistanceFrontiers.mixed_disjoint H root far incident hclique
    (fun h => hij (hdepths h))
  exact Set.disjoint_left.mp hd (hrows i s) (heq ▸ hrows j t)

end Mettapedia.GraphTheory.FourColor.ContourMeshExtraction
