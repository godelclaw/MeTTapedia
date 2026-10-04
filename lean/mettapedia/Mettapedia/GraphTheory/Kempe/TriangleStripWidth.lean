import Mettapedia.GraphTheory.Kempe.TriangleAnchors

/-!
# The anchor cost of an arbitrarily long triangle strip

Join vertices whose indices differ by one or two. The consecutive triples
form a strip of triangles, each new triangle attached along the preceding
edge. A reverse-index elimination order and the index modulo three give
the structural anchor contract for every length.

For a strip on `3 * k` vertices, every set whose deletion leaves a forest
has at least `k` vertices: it must hit each of the `k` disjoint consecutive
triangles. Thus a constant number of cycle-breaking anchors cannot handle
all lengths. This is not a lower bound on proof length, symbolic summaries,
Kempe classes, or other compositional repair mechanisms.
-/

namespace SimpleGraph.KempeTriangleStripWidth

open KempeTriangleAnchors

def strip (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ x.val ≤ y.val + 2 ∧ y.val ≤ x.val + 2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def rank {n : ℕ} (x : Fin n) : ℕ := n - x.val

theorem rank_injective (n : ℕ) : Function.Injective (rank (n := n)) := by
  intro x y h
  apply Fin.ext
  dsimp [rank] at h
  omega

theorem later_clique (n : ℕ) : ∀ v x y,
    (strip n).Adj v x → (strip n).Adj v y →
    rank v < rank x → rank v < rank y → x ≠ y → (strip n).Adj x y := by
  intro v x y hx hy rx ry ne
  change v ≠ x ∧ v.val ≤ x.val + 2 ∧ x.val ≤ v.val + 2 at hx
  change v ≠ y ∧ v.val ≤ y.val + 2 ∧ y.val ≤ v.val + 2 at hy
  refine ⟨ne, ?_, ?_⟩ <;> dsimp [rank] at rx ry <;> omega

def structuralColour (n : ℕ) : (strip n).Coloring (Fin 3) :=
  .mk (fun x => ⟨x.val % 3, Nat.mod_lt _ (by decide)⟩) (by
    intro x y h eq
    have e := congrArg Fin.val eq
    have ne : x.val ≠ y.val := fun he => h.1 (Fin.ext he)
    change x.val % 3 = y.val % 3 at e
    change x ≠ y ∧ x.val ≤ y.val + 2 ∧ y.val ≤ x.val + 2 at h
    omega)

/-- The anchor construction works at every strip length. -/
theorem forest (n : ℕ) (a : Fin 3) :
    ((strip n).induce {x | structuralColour n x ≠ a}).IsAcyclic :=
  delete_class_acyclic rank (rank_injective n) (later_clique n) (structuralColour n) a

private theorem no_triangle {V : Type*} {G : SimpleGraph V} (h : G.IsAcyclic)
    {x y z : V} (xy : G.Adj x y) (yz : G.Adj y z) (zx : G.Adj z x) : False := by
  let p : G.Walk x z := .cons xy (.cons yz .nil)
  have hp : p.IsPath := by
    rw [Walk.isPath_def]
    simp [p, xy.ne, yz.ne, zx.ne.symm]
  have eq : z = y := h.eq_snd_of_adj_start hp zx.symm p.end_mem_support
  exact yz.ne eq.symm

def vertex {k : ℕ} (i : Fin k) (j : Fin 3) : Fin (3 * k) :=
  ⟨3 * i.val + j.val, by omega⟩

private theorem block_edge {k : ℕ} (i : Fin k) (a b : Fin 3) (ne : a ≠ b) :
    (strip (3 * k)).Adj (vertex i a) (vertex i b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply ne
    apply Fin.ext
    have h' := congrArg Fin.val h
    dsimp [vertex] at h'
    omega
  · dsimp [vertex]; omega
  · dsimp [vertex]; omega

/-- Any cycle-breaking anchor scheme for these strips has unbounded size,
even though their triangle attachments and elimination law are uniform. -/
theorem anchors_required (k : ℕ) (K : Set (Fin (3 * k)))
    (acyclic : ((strip (3 * k)).induce Kᶜ).IsAcyclic) : k ≤ Nat.card K := by
  classical
  have hit (i : Fin k) : ∃ j : Fin 3, vertex i j ∈ K := by
    by_contra h
    simp only [not_exists] at h
    let v (j : Fin 3) : ↥(Kᶜ) := ⟨vertex i j, h j⟩
    exact no_triangle acyclic
      (show ((strip (3 * k)).induce Kᶜ).Adj (v 0) (v 1) from block_edge i 0 1 (by decide))
      (show ((strip (3 * k)).induce Kᶜ).Adj (v 1) (v 2) from block_edge i 1 2 (by decide))
      (show ((strip (3 * k)).induce Kᶜ).Adj (v 2) (v 0) from block_edge i 2 0 (by decide))
  let f : Fin k → K := fun i => ⟨vertex i (hit i).choose, (hit i).choose_spec⟩
  have inject : Function.Injective f := by
    intro i j h
    have eq := congrArg (fun x : K => x.val.val) h
    change 3 * i.val + ((hit i).choose).val = 3 * j.val + ((hit j).choose).val at eq
    have hi := ((hit i).choose).isLt
    have hj := ((hit j).choose).isLt
    apply Fin.ext
    omega
  simpa using Nat.card_le_card_of_injective f inject

end SimpleGraph.KempeTriangleStripWidth
