import Mettapedia.GraphTheory.FourColor.ContourMeshExtraction
import Mettapedia.GraphTheory.FourColor.SimultaneousMonotoneThinning
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedInjectiveMeshWidthFactorization

/-!
# Ordered meshes by thinning a linkage across simple contour rows

The column branch positions are already strictly increasing, for example
by the first-hit construction. Row orders need not agree. Simultaneous
monotone thinning chooses common columns; reversing individual rows then
gives the exact ordered mesh. Shared row--column path segments are allowed,
as in the existing ordered-mesh carrier, but each family is vertex-disjoint.
-/

namespace Mettapedia.GraphTheory.FourColor.OrderedContourExtraction

open GoertzelV24BoundaryEssentialGluing GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization ContourMeshExtraction

variable {V E : Type*} {g : Multigraph V E}

/-- Reverse both vertex and original-edge sequences. -/
def reversePath (p : MeshPath g) : MeshPath g where
  len := p.len
  vert t := p.vert t.rev
  edge t := p.edge t.rev
  edge_ends t := by
    simpa only [Fin.rev_castSucc, Fin.rev_succ, or_comm] using p.edge_ends t.rev

/-- Orient a simple path so the selected positions are increasing, retaining
every vertex and the exact selected branch vertices. -/
theorem orient_positions {b : ℕ} (p : MeshPath g)
    (hp : Function.Injective p.vert) (pos : Fin b → Fin (p.len + 1))
    (hpos : StrictMono pos ∨ StrictAnti pos) :
    ∃ q : MeshPath g, ∃ idx : Fin b → Fin (q.len + 1),
      Function.Injective q.vert ∧ StrictMono idx ∧
      (∀ j, q.vert (idx j) = p.vert (pos j)) ∧
      (∀ t, ∃ s, q.vert t = p.vert s) := by
  rcases hpos with hm | hm
  · exact ⟨p, pos, hp, hm, fun _ => rfl, fun t => ⟨t, rfl⟩⟩
  · refine ⟨reversePath p, fun j => (pos j).rev,
      hp.comp Fin.rev_injective, ?_, ?_, fun t => ⟨t.rev, rfl⟩⟩
    · intro i j hij
      exact Fin.rev_lt_rev.mpr (hm hij)
    · intro j
      simp [reversePath]

variable [DecidableEq V] [DecidableEq E] [Fintype E]

/-- Complete extraction on the original multigraph, with explicit dimension
loss. No common row order or simplicity of the chosen intersections is
assumed beyond the stated simple, disjoint path families. -/
theorem exists_orderedMesh_of_paths {a b N : ℕ}
    (rows : Fin a → MeshPath g) (cols : Fin N → MeshPath g)
    (hr : ∀ i j, i ≠ j → ∀ s t, (rows i).vert s ≠ (rows j).vert t)
    (hc : ∀ i j, i ≠ j → ∀ s t, (cols i).vert s ≠ (cols j).vert t)
    (hrs : ∀ i, Function.Injective (rows i).vert)
    (hcs : ∀ j, Function.Injective (cols j).vert)
    (rpos : ∀ i (_j : Fin N), Fin ((rows i).len + 1))
    (cpos : ∀ (_i : Fin a) j, Fin ((cols j).len + 1))
    (hmeet : ∀ i j, (rows i).vert (rpos i j) = (cols j).vert (cpos i j))
    (horder : ∀ j, StrictMono (fun i => cpos i j))
    (hn : b ^ (2 ^ a) < N) : Nonempty (OrderedInjectiveMesh g a b) := by
  classical
  have hinj (i) : Function.Injective (fun j => (rpos i j).val) := by
    intro j k hjk
    by_contra hne
    exact hc j k hne (cpos i j) (cpos i k)
      ((hmeet i j).symm.trans ((congrArg (rows i).vert (Fin.ext hjk)).trans (hmeet i k)))
  obtain ⟨e, he⟩ := SimultaneousMonotoneThinning.exists_orderEmbedding a b N
    (fun i j => (rpos i j).val) hinj hn
  let selected : Fin b ↪o Fin N := (Fin.castLEOrderEmb (Nat.le_succ b)).trans e
  have hmono (i) : StrictMono (fun j => rpos i (selected j)) ∨
      StrictAnti (fun j => rpos i (selected j)) := by
    rcases he i with hm | hm
    · exact Or.inl (fun j k hjk => hm ((Fin.castLEOrderEmb (Nat.le_succ b)).strictMono hjk))
    · exact Or.inr (fun j k hjk => hm ((Fin.castLEOrderEmb (Nat.le_succ b)).strictMono hjk))
  have hrows (i) := orient_positions (rows i) (hrs i)
    (fun j => rpos i (selected j)) (hmono i)
  choose rs rp hrs' hmono' hbranch hvertices using hrows
  have hdr : ∀ i j, i ≠ j → ∀ s t, (rs i).vert s ≠ (rs j).vert t := by
    intro i j hij s t heq
    obtain ⟨u, hu⟩ := hvertices i s
    obtain ⟨v, hv⟩ := hvertices j t
    exact hr i j hij u v (hu.symm.trans (heq.trans hv))
  have hdc : ∀ i j, i ≠ j → ∀ s t,
      (cols (selected i)).vert s ≠ (cols (selected j)).vert t := by
    intro i j hij
    exact hc _ _ (fun h => hij (selected.injective h))
  let M : Mesh g a b := {
    row := rs
    col := fun j => cols (selected j)
    branch := fun i j => (rs i).vert (rp i j)
    branch_mem_row := fun i j => ⟨rp i j, rfl⟩
    branch_mem_col := fun i j => ⟨cpos i (selected j),
      (hmeet i (selected j)).symm.trans (hbranch i j).symm⟩
    row_edges_disjoint := edges_disjoint rs hdr
    col_edges_disjoint := edges_disjoint (fun j => cols (selected j)) hdc }
  refine ⟨{
    toMesh := M
    rowVertexInjective := hrs'
    colVertexInjective := fun j => hcs (selected j)
    branchInjective := ?_
    rowBranchPosition := rp
    colBranchPosition := fun i j => cpos i (selected j)
    rowBranchPosition_spec := fun _ _ => rfl
    colBranchPosition_spec := ?_
    rowBranchPosition_strictMono := hmono'
    colBranchPosition_strictMono := fun j => horder (selected j) }⟩
  · intro x y hxy
    have hi : x.1 = y.1 := by
      by_contra hne
      exact hdr _ _ hne (rp x.1 x.2) (rp y.1 y.2) hxy
    have hj : x.2 = y.2 := by
      by_contra hne
      obtain ⟨s, hs⟩ := M.branch_mem_col x.1 x.2
      obtain ⟨t, ht⟩ := M.branch_mem_col y.1 y.2
      exact hdc _ _ hne s t (hs.trans (hxy.trans ht.symm))
    exact Prod.ext hi hj
  · intro i j
    exact (hmeet i (selected j)).symm.trans (hbranch i j).symm

end Mettapedia.GraphTheory.FourColor.OrderedContourExtraction
