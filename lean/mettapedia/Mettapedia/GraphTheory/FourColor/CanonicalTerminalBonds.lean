import Mettapedia.GraphTheory.FourColor.CanonicalTerminalCuts
import Mettapedia.GraphTheory.FourColor.VertexSeparatorBond

/-!
# Minimum complete cuts between connected terminals are bonds

Canonical minimum cuts already exist and nest. Here their connectivity is
proved, not imposed: a minimum cut in a connected graph between connected
terminal sets has two connected shores. Flooding the source inside the
chosen side cannot add cut edges; minimality makes the full boundaries
equal, and connectedness identifies the two sides. Repeat on the complement.

The multigraph edge carrier retains multiplicities. Its adjacency is related
explicitly to a simple graph only for walks. No uniform width is inferred.
-/

namespace Mettapedia.GraphTheory.FourColor.CanonicalTerminalBonds

open SimpleGraph GoertzelV24BoundaryEssentialGluing GoertzelV24MeshIsoperimetry
open CanonicalTerminalCuts VertexSeparatorBond
open scoped Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (g : Multigraph V E) (G : SimpleGraph V)
  (hstep : ∀ u v, g.Step u v ↔ G.Adj u v)

omit [DecidableEq E] in
theorem boundary_compl (S : Finset V) : boundaryEdges g Sᶜ = boundaryEdges g S := by
  ext e
  simp only [boundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    IsBoundaryEdge, Finset.mem_compl, not_not]
  tauto

include hstep

omit [Fintype V] [DecidableEq E] in
/-- Equal complete boundaries propagate equality of side membership along walks. -/
theorem walk_mem_iff {S T : Finset V} (hcut : boundaryEdges g S = boundaryEdges g T)
    {u v : V} (p : G.Walk u v) (hu : u ∈ S ↔ u ∈ T) : v ∈ S ↔ v ∈ T := by
  induction p with
  | nil => exact hu
  | @cons u w v hadj p ih =>
    apply ih
    obtain ⟨e, _, he⟩ := (hstep u w).mpr hadj
    have hc : IsBoundaryEdge g S e ↔ IsBoundaryEdge g T e := by
      have := congrArg (fun s => e ∈ s) hcut
      simpa [boundaryEdges] using this
    rcases he with ⟨he₁, he₂⟩ | ⟨he₁, he₂⟩ <;>
      simp only [IsBoundaryEdge, he₁, he₂] at hc <;> tauto

omit [Fintype V] [DecidableEq E] in
/-- The complement ambiguity of equal cuts disappears at a shared vertex. -/
theorem eq_of_boundary_eq (hG : G.Connected) {S T : Finset V}
    (hcut : boundaryEdges g S = boundaryEdges g T)
    {a : V} (ha : a ∈ S) (ha' : a ∈ T) : S = T := by
  ext v
  obtain ⟨p⟩ := hG a v
  exact walk_mem_iff g G hstep hcut p (by simp [ha, ha'])

omit [DecidableEq E] in
/-- Flooding cannot create a new edge boundary inside the allowed side. -/
theorem boundary_flood_subset (S A : Finset V) :
    boundaryEdges g (flood G (↑S) (↑A)).toFinset ⊆ boundaryEdges g S := by
  classical
  intro e he
  have he' : IsBoundaryEdge g (flood G (↑S) (↑A)).toFinset e :=
    (Finset.mem_filter.mp he).2
  have hadj : G.Adj (g.fst e) (g.snd e) :=
    (hstep _ _).mp ⟨e, by simp, Or.inl ⟨rfl, rfl⟩⟩
  have hc : IsBoundaryEdge g S e := by
    simp only [IsBoundaryEdge, Set.mem_toFinset] at he'
    rcases he' with ⟨hf, hn⟩ | ⟨hn, hf⟩
    · exact Or.inl ⟨flood_subset G (↑S) (↑A) hf,
        fun h => hn (flood_adj G hf hadj h)⟩
    · exact Or.inr ⟨fun h => hn (flood_adj G hf hadj.symm h),
        flood_subset G (↑S) (↑A) hf⟩
  simpa [boundaryEdges] using hc

omit [DecidableEq E] in
/-- Any minimum full cut has a connected source shore. No tie-break is needed. -/
theorem minimum_connected (hG : G.Connected) {A B S : Finset V}
    (hA : (G.induce (↑A : Set V)).Connected) (hf : Feasible A B S)
    (hmin : ∀ T, Feasible A B T → (boundaryEdges g S).card ≤ (boundaryEdges g T).card) :
    (G.induce (↑S : Set V)).Connected := by
  classical
  let R := (flood G (↑S) (↑A)).toFinset
  have hRS : R ⊆ S := fun v hv => flood_subset G (↑S) (↑A) (by simpa [R] using hv)
  have hAR : (↑A : Set V) ⊆ flood G (↑S) (↑A) :=
    fun v hv => mem_flood G (↑S) (↑A) (hf.1 hv) hv
  have hRf : Feasible A B R :=
    ⟨fun v hv => by simpa [R] using hAR hv, hf.2.mono_left hRS⟩
  have hcuts : boundaryEdges g R = boundaryEdges g S :=
    Finset.eq_of_subset_of_card_le (boundary_flood_subset g G hstep S A) (hmin R hRf)
  obtain ⟨a⟩ := hA.nonempty
  have heq : R = S := eq_of_boundary_eq g G hstep hG hcuts (hRf.1 a.property) (hf.1 a.property)
  have hc := basin_connected G (↑S) (↑A) hA
  rw [Set.union_eq_right.mpr hAR] at hc
  have hRset : (↑R : Set V) = flood G (↑S) (↑A) := by
    ext v
    simp [R]
  have hr : (G.induce (↑R : Set V)).Connected := hRset ▸ hc
  exact heq ▸ hr

omit hstep [Fintype E] [DecidableEq E] in
theorem feasible_compl {A B S : Finset V} (h : Feasible A B S) : Feasible B A Sᶜ := by
  refine ⟨?_, ?_⟩
  · intro v hv
    exact Finset.mem_compl.mpr (fun hs => Finset.disjoint_left.mp h.2 hs hv)
  · apply Finset.disjoint_left.mpr
    intro v hv ha
    exact Finset.mem_compl.mp hv (h.1 ha)

omit [DecidableEq E] in
/-- A minimum cut also has a connected sink shore. -/
theorem minimum_bond (hG : G.Connected) {A B S : Finset V}
    (hA : (G.induce (↑A : Set V)).Connected) (hB : (G.induce (↑B : Set V)).Connected)
    (hf : Feasible A B S)
    (hmin : ∀ T, Feasible A B T → (boundaryEdges g S).card ≤ (boundaryEdges g T).card) :
    (G.induce (↑S : Set V)).Connected ∧ (G.induce (↑Sᶜ : Set V)).Connected := by
  refine ⟨minimum_connected g G hstep hG hA hf hmin, ?_⟩
  apply minimum_connected g G hstep hG hB (feasible_compl hf) (S := Sᶜ)
  intro T hT
  have h := hmin Tᶜ (feasible_compl hT)
  simpa only [boundary_compl] using h

/-- Actual canonical cuts, now with both connected shores. -/
theorem canonical_bond (hG : G.Connected) (A B : Finset V)
    (hA : (G.induce (↑A : Set V)).Connected) (hB : (G.induce (↑B : Set V)).Connected)
    (hAB : Disjoint A B) :
    (G.induce (↑(canonical g A B hAB) : Set V)).Connected ∧
      (G.induce (↑(canonical g A B hAB)ᶜ : Set V)).Connected :=
  minimum_bond g G hstep hG hA hB
    (canonical_spec g A B hAB).feasible (canonical_spec g A B hAB).width_min

end Mettapedia.GraphTheory.FourColor.CanonicalTerminalBonds
