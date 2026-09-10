import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedInjectiveMeshWidthFactorization

/-!
# An explicit two-dimensional split-grid family

Each grid position has two vertices joined by an internal edge. Horizontal
and vertical edges join its second vertex to the first vertex of the next
position. The complete vertex carrier has no unaccounted subdivisions or
attached components. These are open walls, not closed counterexamples.
-/

namespace Mettapedia.GraphTheory.FourColor.SplitGridMesh

open GoertzelV24BoundaryEssentialGluing GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization

abbrev Position (n : Nat) := Fin (n + 1) × Fin (n + 1)
abbrev Vertex (n : Nat) := Position n × Fin 2
abbrev Edge (n : Nat) := Position n ⊕ (Fin (n + 1) × Fin n) ⊕ (Fin n × Fin (n + 1))

def graph (n : Nat) : Multigraph (Vertex n) (Edge n) where
  fst
    | .inl p => (p, 0)
    | .inr (.inl (i, j)) => ((i, j.castSucc), 1)
    | .inr (.inr (i, j)) => ((i.castSucc, j), 1)
  snd
    | .inl p => (p, 1)
    | .inr (.inl (i, j)) => ((i, j.succ), 0)
    | .inr (.inr (i, j)) => ((i.succ, j), 0)

instance (n : Nat) : Nonempty (Edge n) := ⟨.inl (0, 0)⟩

def slot {n : Nat} (t : Fin (2 * n + 2)) : Fin (n + 1) × Fin 2 :=
  (⟨t.val / 2, by omega⟩, ⟨t.val % 2, Nat.mod_lt _ (by decide)⟩)

theorem slot_injective {n : Nat} : Function.Injective (@slot n) := by
  intro s t h
  have hq := congrArg (fun p => p.1.val) h
  have hr := congrArg (fun p => p.2.val) h
  dsimp [slot] at hq hr
  apply Fin.ext
  omega

def rowEdge {n : Nat} (i : Fin (n + 1)) (t : Fin (2 * n + 1)) : Edge n :=
  if h : t.val % 2 = 0 then .inl (i, ⟨t.val / 2, by omega⟩)
  else .inr (.inl (i, ⟨t.val / 2, by omega⟩))

def colEdge {n : Nat} (j : Fin (n + 1)) (t : Fin (2 * n + 1)) : Edge n :=
  if h : t.val % 2 = 0 then .inl (⟨t.val / 2, by omega⟩, j)
  else .inr (.inr (⟨t.val / 2, by omega⟩, j))

def row {n : Nat} (i : Fin (n + 1)) : MeshPath (graph n) where
  len := 2 * n + 1
  vert t := ((i, (slot t).1), (slot t).2)
  edge := rowEdge i
  edge_ends := by
    intro t
    left
    dsimp [rowEdge]
    split_ifs with h
    all_goals
      constructor <;> apply Prod.ext
      all_goals first
        | apply Prod.ext
        | apply Fin.ext
      all_goals try apply Fin.ext
      all_goals first | rfl | (dsimp [graph, slot]; omega)

def col {n : Nat} (j : Fin (n + 1)) : MeshPath (graph n) where
  len := 2 * n + 1
  vert t := (((slot t).1, j), (slot t).2)
  edge := colEdge j
  edge_ends := by
    intro t
    left
    dsimp [colEdge]
    split_ifs with h
    all_goals
      constructor <;> apply Prod.ext
      all_goals first
        | apply Prod.ext
        | apply Fin.ext
      all_goals try apply Fin.ext
      all_goals first | rfl | (dsimp [graph, slot]; omega)

def mesh (n : Nat) : Mesh (graph n) (n + 1) (n + 1) where
  row := row
  col := col
  branch i j := ((i, j), 0)
  branch_mem_row := by
    intro i j
    refine ⟨⟨2 * j.val, by have := j.isLt; dsimp [row]; omega⟩, ?_⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Fin.ext; simp [row, slot]
    · apply Fin.ext; simp [row, slot]
  branch_mem_col := by
    intro i j
    refine ⟨⟨2 * i.val, by have := i.isLt; dsimp [col]; omega⟩, ?_⟩
    apply Prod.ext
    · apply Prod.ext
      · apply Fin.ext; simp [col, slot]
      · rfl
    · apply Fin.ext; simp [col, slot]
  row_edges_disjoint := by
    intro i j hne s t h
    dsimp [row, rowEdge] at h
    split_ifs at h <;> simp_all
  col_edges_disjoint := by
    intro i j hne s t h
    dsimp [col, colEdge] at h
    split_ifs at h <;> simp_all

def branchPosition {n : Nat} (i : Fin (n + 1)) : Fin (2 * n + 2) :=
  ⟨2 * i.val, by have := i.isLt; omega⟩

theorem slot_branchPosition {n : Nat} (i : Fin (n + 1)) :
    slot (branchPosition i) = (i, 0) := by
  apply Prod.ext <;> apply Fin.ext <;> simp [slot, branchPosition]

theorem branchPosition_strictMono {n : Nat} : StrictMono (@branchPosition n) := by
  intro i j h
  change i.val < j.val at h
  change 2 * i.val < 2 * j.val
  omega

/-- The explicit family inhabits the route's actual ordered-mesh carrier. -/
def ordered (n : Nat) : OrderedInjectiveMesh (graph n) (n + 1) (n + 1) where
  toMesh := mesh n
  rowVertexInjective := by
    intro i s t h
    apply slot_injective
    exact congrArg (fun v : Vertex n => (v.1.2, v.2)) h
  colVertexInjective := by
    intro j s t h
    apply slot_injective
    exact congrArg (fun v : Vertex n => (v.1.1, v.2)) h
  branchInjective := by
    intro s t h
    exact congrArg Prod.fst h
  rowBranchPosition := fun _ j => branchPosition j
  colBranchPosition := fun i _ => branchPosition i
  rowBranchPosition_spec := by intro i j; simp [mesh, row, slot_branchPosition]
  colBranchPosition_spec := by intro i j; simp [mesh, col, slot_branchPosition]
  rowBranchPosition_strictMono := fun _ => branchPosition_strictMono
  colBranchPosition_strictMono := fun _ => branchPosition_strictMono

theorem vertex_card (n : Nat) : Fintype.card (Vertex n) = 2 * ((n + 1) * (n + 1)) := by
  simp [Vertex, Position, Nat.mul_comm]

/-- Internal, horizontal and vertical edges carry distinct colours. -/
def edgeKind {n : Nat} : Edge n → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

/-- The entire family has a proper three-edge-colouring. This prevents
confusing the geometric obstruction with a non-colourable specimen. -/
theorem edgeKind_proper {n : Nat} (e f : Edge n) (v : Vertex n)
    (he : (graph n).fst e = v ∨ (graph n).snd e = v)
    (hf : (graph n).fst f = v ∨ (graph n).snd f = v)
    (hne : e ≠ f) : edgeKind e ≠ edgeKind f := by
  intro hc
  rcases e with p | (p | p) <;> rcases f with q | (q | q) <;>
    simp only [edgeKind] at hc
  all_goals try { norm_num at hc }
  all_goals
    rcases p with ⟨i, j⟩
    rcases q with ⟨i', j'⟩
    rcases he with he | he <;> rcases hf with hf | hf
    all_goals have hh := he.trans hf.symm
    all_goals clear he hf
    all_goals simp_all [graph]

theorem loopless (n : Nat) (e : Edge n) : (graph n).fst e ≠ (graph n).snd e := by
  rcases e with p | (p | p) <;> simp [graph]

theorem degree_le_three {n : Nat} (v : Vertex n) :
    (Finset.univ.filter fun e => (graph n).fst e = v ∨ (graph n).snd e = v).card ≤ 3 := by
  classical
  let es := Finset.univ.filter fun e => (graph n).fst e = v ∨ (graph n).snd e = v
  have hinj : Function.Injective (fun e : es => edgeKind e.1) := by
    intro e f h
    apply Subtype.ext
    by_contra hne
    exact edgeKind_proper e.1 f.1 v (Finset.mem_filter.mp e.2).2
      (Finset.mem_filter.mp f.2).2 hne h
  have h := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_coe, Fintype.card_fin] at h
  exact h

end Mettapedia.GraphTheory.FourColor.SplitGridMesh
