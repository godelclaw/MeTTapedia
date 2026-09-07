import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The deep face component and its disjoint distance frontiers

Construct the component of a far face using walks lying strictly beyond a
given distance from the root. The components nest as the depth increases.
If the incident faces at each vertex form a clique in the facial dual, a
vertex meeting both a component and its complement has minimum incident-face
distance exactly the depth. Consequently different depths have disjoint
vertex frontiers. This is a local metric argument, not a Jordan-curve axiom.

In the cubic spherical application the clique comes from the three incident
face sectors. Identifying each complete frontier with one primal cycle is a
further planar separation step, not an assumption hidden in `deepRegion`.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceDistanceFrontiers

variable {F V : Type*} (H : SimpleGraph F) (root far : F)

/-- The actual component of `far` in faces strictly beyond `depth`. -/
def deepRegion (depth : ℕ) : Set F :=
  {f | ∃ w : H.Walk far f, ∀ v ∈ w.support, depth < H.dist root v}

theorem dist_gt_of_mem {depth : ℕ} {f : F}
    (hf : f ∈ deepRegion H root far depth) : depth < H.dist root f := by
  obtain ⟨w, hw⟩ := hf
  exact hw f w.end_mem_support

theorem far_mem {depth : ℕ} (hfar : depth < H.dist root far) :
    far ∈ deepRegion H root far depth := by
  refine ⟨.nil, ?_⟩
  simpa using hfar

theorem deepRegion_antitone : Antitone (deepRegion H root far) := by
  intro i j hij f ⟨w, hw⟩
  exact ⟨w, fun v hv => lt_of_le_of_lt hij (hw v hv)⟩

/-- Closure within the same distance layer is proved by extending the walk. -/
theorem mem_of_adj {depth : ℕ} {f h : F}
    (hf : f ∈ deepRegion H root far depth) (hadj : H.Adj f h)
    (hh : depth < H.dist root h) : h ∈ deepRegion H root far depth := by
  obtain ⟨w, hw⟩ := hf
  refine ⟨w.concat hadj, ?_⟩
  intro v hv
  simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | rfl
  · exact hw v hv
  · exact hh

/-- Every edge of the complete dual cut crosses from depth+1 to depth. -/
theorem cut_distance {depth : ℕ} {f h : F}
    (hf : f ∈ deepRegion H root far depth)
    (hh : h ∉ deepRegion H root far depth) (hadj : H.Adj f h) :
    H.dist root f = depth + 1 ∧ H.dist root h = depth := by
  have hfd := dist_gt_of_mem H root far hf
  have hhd : H.dist root h ≤ depth := by
    by_contra h
    exact hh (mem_of_adj H root far hf hadj (by omega))
  have hdiff := hadj.diff_dist_adj (u := root)
  omega

/-- A shortest walk supplies an adjacent face strictly closer to the root. -/
theorem exists_closer (hconnected : H.Connected) {f : F} (hne : f ≠ root) :
    ∃ h, H.Adj f h ∧ H.dist root h < H.dist root f := by
  obtain ⟨w, hw⟩ := hconnected.exists_walk_length_eq_dist f root
  cases w with
  | nil => exact (hne rfl).elim
  | @cons f h root hadj w =>
    refine ⟨h, hadj, ?_⟩
    have hle := H.dist_le w
    simp only [SimpleGraph.Walk.length_cons] at hw
    rw [H.dist_comm] at hle hw
    omega

/-- Every face outside the deep component has a path to the root which
stays outside. This constructs complementary connectivity, even when the
whole distance superlevel has several components. -/
theorem exists_outside_walk (hconnected : H.Connected) (depth : ℕ)
    {f : F} (hf : f ∉ deepRegion H root far depth) :
    ∃ w : H.Walk f root, ∀ v ∈ w.support, v ∉ deepRegion H root far depth := by
  classical
  suffices ∀ n f, H.dist root f = n → f ∉ deepRegion H root far depth →
      ∃ w : H.Walk f root, ∀ v ∈ w.support, v ∉ deepRegion H root far depth by
    exact this _ f rfl hf
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hdist hf
    by_cases heq : f = root
    · subst f
      exact ⟨.nil, by simpa using hf⟩
    obtain ⟨h, hadj, hlt⟩ := exists_closer H root hconnected heq
    have hh : h ∉ deepRegion H root far depth := by
      intro hmem
      have hhd := dist_gt_of_mem H root far hmem
      exact hf (mem_of_adj H root far hmem hadj.symm (by omega))
    obtain ⟨w, hw⟩ := ih (H.dist root h) (by omega) h rfl hh
    refine ⟨w.cons hadj, ?_⟩
    intro v hv
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hf
    · exact hw v hv

/-- The deep component is connected on its original face carrier. -/
theorem deepRegion_connected (depth : ℕ) (hfar : depth < H.dist root far) :
    (H.induce (deepRegion H root far depth)).Connected := by
  classical
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨far, far_mem H root far hfar⟩, ?_⟩
  intro f
  obtain ⟨w, hw⟩ := f.property
  have hs : ∀ v ∈ w.support, v ∈ deepRegion H root far depth := by
    intro v hv
    exact ⟨w.takeUntil v hv, fun x hx => hw x (w.support_takeUntil_subset_support hv hx)⟩
  exact ⟨w.induce _ hs⟩

/-- The complement is also connected, without a planarity hypothesis. -/
theorem deepRegion_compl_connected (hconnected : H.Connected) (depth : ℕ) :
    (H.induce (deepRegion H root far depth)ᶜ).Connected := by
  have hroot : root ∉ deepRegion H root far depth := by
    intro h
    have hd := dist_gt_of_mem H root far h
    simp at hd
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨root, hroot⟩, ?_⟩
  intro f
  obtain ⟨w, hw⟩ := exists_outside_walk H root far hconnected depth f.property
  exact ⟨(w.induce _ hw).reverse⟩

/-- Faces incident at a vertex meet both a region and its complement. -/
def Mixed (incident : V → Set F) (region : Set F) (v : V) : Prop :=
  (∃ f, f ∈ incident v ∧ f ∈ region) ∧ ∃ h, h ∈ incident v ∧ h ∉ region

/-- A complete frontier vertex has a face at exactly the depth, and no
incident face closer to the root. No minimum operation or choice is needed. -/
theorem mixed_distance (incident : V → Set F)
    (hclique : ∀ v f h, f ∈ incident v → h ∈ incident v → f = h ∨ H.Adj f h)
    {depth : ℕ} {v : V} (hv : Mixed incident (deepRegion H root far depth) v) :
    (∃ f ∈ incident v, H.dist root f = depth) ∧
      ∀ f ∈ incident v, depth ≤ H.dist root f := by
  obtain ⟨⟨f, hfv, hf⟩, ⟨h, hhv, hh⟩⟩ := hv
  have hadj : H.Adj f h := by
    rcases hclique v f h hfv hhv with rfl | hadj
    · exact (hh hf).elim
    · exact hadj
  obtain ⟨hfd, hhd⟩ := cut_distance H root far hf hh hadj
  refine ⟨⟨h, hhv, hhd⟩, ?_⟩
  intro x hx
  rcases hclique v f x hfv hx with rfl | hfx
  · omega
  · have hdiff := hfx.diff_dist_adj (u := root)
    omega

/-- Different depth frontiers are vertex-disjoint, derived from the actual
deep components rather than supplied as a contour-family hypothesis. -/
theorem mixed_disjoint (incident : V → Set F)
    (hclique : ∀ v f h, f ∈ incident v → h ∈ incident v → f = h ∨ H.Adj f h)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint {v | Mixed incident (deepRegion H root far i) v}
      {v | Mixed incident (deepRegion H root far j) v} := by
  apply Set.disjoint_left.mpr
  intro v hi hj
  obtain ⟨⟨f, hf, hfi⟩, hminI⟩ := mixed_distance H root far incident hclique hi
  obtain ⟨⟨h, hh, hhj⟩, hminJ⟩ := mixed_distance H root far incident hclique hj
  have hji := hminJ f hf
  have hij' := hminI h hh
  exact hij (by omega)

end Mettapedia.GraphTheory.FourColor.FaceDistanceFrontiers
