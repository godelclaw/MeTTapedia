import Mettapedia.GraphTheory.FourColor.SplitGridChainObstruction

/-!
# Branching does not remove the bounded-interface generation obstruction

This audits an alternative to a corridor decomposition: arbitrary binary
composition trees, with bounded-size atoms and complete vertex interfaces.
The intermediate pieces need not be connected, the tree need not be balanced,
and atoms may overlap. Every intermediate carrier is the union of its children.

A balanced-subtree argument, applied to the existing split-grid small-cut
theorem, rules out such a uniformly bounded presentation of all these open,
colourable graphs. This is not a refutation for a minimal-counterexample class,
an edge-middle-set treewidth theorem, or a ban on growing interfaces or rewrites
which do not retain intermediate carriers as subsets of the final graph.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace BranchingInterfaceObstruction

open GoertzelV24ConnectedBranchDecompositionForest

variable {V : Type*} [DecidableEq V]

/-- The actual ambient vertices carried by a compositional subtree. -/
def vertices : EdgeLeafTree (Finset V) → Finset V
  | .leaf S => S
  | .fork left right => vertices left ∪ vertices right

/-- A bounded atom presentation, with the property checked on every subtree. -/
def Presented (atomBound : Nat) (P : Finset V → Prop) :
    EdgeLeafTree (Finset V) → Prop
  | .leaf S => S.card ≤ atomBound ∧ P S
  | .fork left right => P (vertices left ∪ vertices right) ∧
      Presented atomBound P left ∧ Presented atomBound P right

theorem Presented.mono {a : Nat} {P Q : Finset V → Prop}
    {tree : EdgeLeafTree (Finset V)} (h : Presented a P tree)
    (hpq : ∀ S, P S → Q S) : Presented a Q tree := by
  induction tree with
  | leaf S => exact ⟨h.1, hpq S h.2⟩
  | fork left right ihl ihr => exact ⟨hpq _ h.1, ihl h.2.1, ihr h.2.2⟩

/-- A large union tree has a piece between one and two atom thresholds.
No assumptions on shape, disjointness, or graph geometry are used. -/
theorem exists_intermediate {a t : Nat} {P : Finset V → Prop}
    (tree : EdgeLeafTree (Finset V)) (hp : Presented a P tree)
    (hat : a ≤ t) (hlarge : t < (vertices tree).card) :
    ∃ S : Finset V, P S ∧ t < S.card ∧ S.card ≤ 2 * t := by
  induction tree with
  | leaf S =>
      change t < S.card at hlarge
      have ha := hp.1
      omega
  | fork left right ihl ihr =>
      by_cases hl : t < (vertices left).card
      · exact ihl hp.2.1 hl
      by_cases hr : t < (vertices right).card
      · exact ihr hp.2.2 hr
      refine ⟨vertices left ∪ vertices right, hp.1, hlarge, ?_⟩
      have h := Finset.card_union_le (vertices left) (vertices right)
      omega

/-- If every intermediate cut has a uniformly small side, no branching
presentation by bounded atoms can cover an arbitrarily large carrier. -/
theorem card_le_three_max [Fintype V] {a b : Nat}
    (tree : EdgeLeafTree (Finset V))
    (hp : Presented a (fun S => S.card ≤ b ∨ Sᶜ.card ≤ b) tree)
    (hcover : vertices tree = Finset.univ) :
    Fintype.card V ≤ 3 * max a b := by
  by_contra hbig
  have hlarge : max a b < (vertices tree).card := by
    rw [hcover, Finset.card_univ]
    omega
  obtain ⟨S, hs, hlo, hhi⟩ := exists_intermediate tree hp (Nat.le_max_left _ _) hlarge
  have hb : b ≤ max a b := Nat.le_max_right _ _
  have hc := Finset.card_add_card_compl S
  rcases hs with hs | hs <;> omega

open GoertzelV24MeshIsoperimetry SplitGridMesh

/-- A bounded full-interface binary presentation of a split grid implies
a bound on its entire vertex carrier, irrespective of the branching shape. -/
theorem splitGrid_size_bound {n a k : Nat} (hk : k < n + 1)
    (tree : EdgeLeafTree (Finset (Vertex n)))
    (hp : Presented a (fun S => (boundaryEdges (graph n) S).card ≤ k) tree)
    (hcover : vertices tree = Finset.univ) :
    2 * ((n + 1) * (n + 1)) ≤ 3 * max a (2 * (k * k) + k) := by
  have hs := hp.mono (fun S h => small_side_of_cut S hk h)
  have h := card_le_three_max tree hs hcover
  simpa only [vertex_card] using h

/-- At arbitrary fixed atom size and full-interface width, a larger explicit
open colourable graph defeats every binary union-tree presentation. -/
theorem no_uniform_bounded_presentation (a k N : Nat) :
    ∃ n, N < Fintype.card (Vertex n) ∧
      ¬ ∃ tree : EdgeLeafTree (Finset (Vertex n)),
        Presented a (fun S => (boundaryEdges (graph n) S).card ≤ k) tree ∧
        vertices tree = Finset.univ := by
  let n := N + k + 3 * max a (2 * (k * k) + k) + 1
  refine ⟨n, ?_, ?_⟩
  · rw [vertex_card]
    have hn : N < n := by dsimp [n]; omega
    nlinarith [Nat.zero_le (n * n)]
  · rintro ⟨tree, hp, hcover⟩
    have hk : k < n + 1 := by dsimp [n]; omega
    have h := splitGrid_size_bound hk tree hp hcover
    have hn : 3 * max a (2 * (k * k) + k) < n := by dsimp [n]; omega
    nlinarith [Nat.zero_le (n * n)]

end BranchingInterfaceObstruction
end Mettapedia.GraphTheory.FourColor
