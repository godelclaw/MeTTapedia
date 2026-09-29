import Mettapedia.GraphTheory.FourColor.GoertzelV24PrimalCycleFacialBond
import Mettapedia.GraphTheory.FourColor.GoertzelV24BridgelessFaceTwoSided
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFaces
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.List.ChainOfFn

/-!
# Simple lobes of alternating walks

An alternating orbit can intersect itself. A shortest returning segment still
supplies an actual simple cycle: every internal transition is an original
alternating step, while the closing transition is left unrestricted. In a
bridgeless spherical cubic graph this cycle constructs two connected facial shores.
The theorem supplies geometry; it does not assert that the closing transition
has the usual tube contract or that either resulting patch is reducible.
-/

namespace Mettapedia.GraphTheory.FourColor.AlternatingWalkLobes

open _root_.SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24TwoEdgeCutMinimality PhysicalForkCodeFaces

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

private theorem exists_shortest_return {V : Type*} [Finite V] (f : ℕ → V) :
    ∃ a n : ℕ, 0 < n ∧ f (a + n) = f a ∧
      Function.Injective (fun i : Fin n => f (a + i.val)) := by
  have hex : ∃ n : ℕ, 0 < n ∧ ∃ a, f (a + n) = f a := by
    obtain ⟨i, j, hne, he⟩ := Finite.exists_ne_map_eq_of_infinite f
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨j - i, by omega, i, by simpa [Nat.add_sub_of_le (by omega : i ≤ j)] using he.symm⟩
    · exact ⟨i - j, by omega, j, by simpa [Nat.add_sub_of_le (by omega : j ≤ i)] using he⟩
  let n := Nat.find hex
  obtain ⟨hn, a, ha⟩ := Nat.find_spec hex
  refine ⟨a, n, hn, ha, ?_⟩
  intro i j hij
  apply Fin.ext
  by_contra hne
  have forbidden (r s : Fin n) (hlt : r.val < s.val)
      (he : f (a + r.val) = f (a + s.val)) : False := by
    have hc : 0 < s.val - r.val ∧ ∃ b, f (b + (s.val - r.val)) = f b := by
      refine ⟨by omega, a + r.val, ?_⟩
      have hsum : a + r.val + (s.val - r.val) = a + s.val := by omega
      simpa only [hsum] using he.symm
    have hmin := Nat.find_min' hex hc
    change n ≤ s.val - r.val at hmin
    have hs := s.isLt
    omega
  rcases lt_or_gt_of_ne hne with h | h
  · exact forbidden i j h hij
  · exact forbidden j i h hij.symm

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
/-- A nonbacktracking infinite dart walk in a finite simple graph contains
a simple cycle as one contiguous segment, with at most the ambient number
of vertices. The actual darts are retained, not merely its vertex set. -/
theorem exists_simple_segment (darts : ℕ → G.Dart)
    (adjacent : ∀ i, (darts i).snd = (darts (i + 1)).fst)
    (nonbacktracking : ∀ i, darts (i + 1) ≠ (darts i).symm) :
    ∃ (a n : ℕ) (root : V) (walk : G.Walk root root),
      3 ≤ n ∧ n ≤ Fintype.card V ∧ walk.IsCycle ∧
      walk.darts = List.ofFn (fun i : Fin n => darts (a + i.val)) := by
  obtain ⟨a, n, hn, hreturn, hinj⟩ := exists_shortest_return (fun i => (darts i).fst)
  have hlen : 3 ≤ n := by
    by_contra h
    have hcases : n = 1 ∨ n = 2 := by omega
    rcases hcases with rfl | rfl
    · exact (darts a).snd_ne_fst ((adjacent a).trans hreturn)
    · apply nonbacktracking a
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · exact (adjacent a).symm
      · change (darts (a + 1)).snd = (darts a).fst
        exact (adjacent (a + 1)).trans (by simpa only [Nat.add_assoc] using hreturn)
  have hcard : n ≤ Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj
  let ds := List.ofFn (fun i : Fin n => darts (a + i.val))
  have hds : ds ≠ [] := by
    intro h
    have hh : ds.length = n := by simp [ds]
    simp only [h, List.length_nil] at hh
    omega
  have hc : List.IsChain G.DartAdj ds := by
    rw [List.isChain_ofFn]
    intro i hi
    change (darts (a + i)).snd = (darts (a + (i + 1))).fst
    simpa only [Nat.add_assoc] using adjacent (a + i)
  have hl : G.DartAdj (ds.getLast hds) (ds.head hds) := by
    simp only [ds, List.getLast_ofFn, List.head_ofFn]
    change (darts (a + (n - 1))).snd = (darts (a + 0)).fst
    have hsum : a + (n - 1) + 1 = a + n := by omega
    have hh := adjacent (a + (n - 1))
    rw [hsum] at hh
    simpa only [Nat.add_zero] using hh.trans hreturn
  let w := (Walk.ofDarts ds hds hc).copy rfl hl
  have hw : w.darts = ds := by simp only [w, Walk.darts_copy, Walk.darts_ofDarts]
  have hnw : ¬ w.Nil := by
    intro h
    exact hds (hw.symm.trans (Walk.darts_eq_nil.mpr h))
  have hnodup : w.support.dropLast.Nodup := by
    rw [← w.map_fst_darts, hw, List.map_ofFn, List.nodup_ofFn]
    exact hinj
  have hcycle : w.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · apply Walk.IsPath.mk'
      rw [w.support_tail_of_not_nil hnw]
      exact w.tail_support_perm_dropLast_support.nodup_iff.mpr hnodup
    · have hh := w.length_darts
      rw [hw] at hh
      simp only [ds, List.length_ofFn] at hh
      omega
  exact ⟨a, n, _, w, hlen, hcard, hcycle, hw⟩

variable [DecidableRel G.Adj] (data : Data G)

/-- Cross an edge, choose the current left/right turn, then flip the phase. -/
def step (state : G.Dart × Bool) : G.Dart × Bool :=
  (if state.2 then data.vertexRotation (data.vertexRotation state.1.symm)
   else data.vertexRotation state.1.symm, !state.2)

def trajectory (start : G.Dart × Bool) (n : ℕ) : G.Dart × Bool :=
  (step data)^[n] start

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem trajectory_succ (start : G.Dart × Bool) (n : ℕ) :
    trajectory data start (n + 1) = step data (trajectory data start n) :=
  Function.iterate_succ_apply' _ _ _

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem trajectory_phase (start : G.Dart × Bool) (n : ℕ) :
    (trajectory data start (n + 1)).2 = !(trajectory data start n).2 := by
  rw [trajectory_succ]
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The extracted walk retains the full local operation at every internal
transition. Its closing transition is deliberately absent from this claim. -/
theorem internal_transition (start : G.Dart × Bool) {a n : ℕ} {root : V}
    (walk : G.Walk root root)
    (hd : walk.darts = List.ofFn (fun i : Fin n => (trajectory data start (a + i.val)).1))
    (i : ℕ) (hi : i + 1 < n) :
    walk.darts[i + 1]'(by rw [hd, List.length_ofFn]; exact hi) =
      (step data (walk.darts[i]'(by rw [hd, List.length_ofFn]; omega),
        (trajectory data start (a + i)).2)).1 := by
  simp only [hd, List.getElem_ofFn]
  simpa only [Nat.add_assoc] using
    congrArg Prod.fst (trajectory_succ data start (a + i))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem step_adjacent (state : G.Dart × Bool) :
    state.1.snd = (step data state).1.fst := by
  rcases state with ⟨d, phase⟩
  cases phase <;> simp [step, data.vertexRotation_fst]

theorem step_nonbacktracking (hC : Cubic3 data.toRotationSystem)
    (state : G.Dart × Bool) : (step data state).1 ≠ state.1.symm := by
  rcases state with ⟨d, phase⟩
  cases phase
  · exact hC.moves d.symm
  · intro he
    have h := congrArg data.vertexRotation he
    change data.vertexRotation (data.vertexRotation (data.vertexRotation d.symm)) =
      data.vertexRotation d.symm at h
    have hc := hC.cube d.symm
    exact hC.moves d.symm (h.symm.trans hc)

/-- Every starting dart and phase supplies an actual simple lobe. All its
internal transitions are the original alternating steps. Only the closing
transition may need a different local operation. -/
theorem exists_simple_lobe (hC : Cubic3 data.toRotationSystem)
    (start : G.Dart × Bool) :
    ∃ (a n : ℕ) (root : V) (walk : G.Walk root root),
      3 ≤ n ∧ n ≤ Fintype.card V ∧ walk.IsCycle ∧
      walk.darts = List.ofFn (fun i : Fin n => (trajectory data start (a + i.val)).1) := by
  apply exists_simple_segment (G := G) (fun i => (trajectory data start i).1)
  · intro i
    rw [trajectory_succ]
    exact step_adjacent data _
  · intro i
    rw [trajectory_succ]
    exact step_nonbacktracking data hC _

/-- The supplied lobe has exact facial separation with connected shores.
No simple full orbit, facial region or separator is assumed. -/
theorem exists_separating_lobe
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (start : G.Dart × Bool) :
    ∃ (a n : ℕ) (root : V) (walk : G.Walk root root)
      (faces : Finset (OrbitFace data.toRotationSystem)),
      3 ≤ n ∧ n ≤ Fintype.card V ∧ walk.IsCycle ∧
      walk.darts = List.ofFn (fun i : Fin n => (trajectory data start (a + i.val)).1) ∧
      (∀ d : G.Dart, d.edge ∈ walk.edges ↔
        ((dartOrbitFace data.toRotationSystem d ∈ faces ∧
          dartOrbitFace data.toRotationSystem d.symm ∉ faces) ∨
        (dartOrbitFace data.toRotationSystem d ∉ faces ∧
          dartOrbitFace data.toRotationSystem d.symm ∈ faces))) ∧
      ((orbitFaceDualGraph data).induce (faces : Set _)).Connected ∧
      ((orbitFaceDualGraph data).induce (faces : Set _)ᶜ).Connected := by
  obtain ⟨a, n, root, walk, hn, hc, hw, hd⟩ := exists_simple_lobe data
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) start
  have htwo := GoertzelV24BridgelessFaceTwoSided.BridgelessSphericalCubicMapData.orbitFacesTwoSided
    data.toRotationSystem ambient
  obtain ⟨faces, he, hf, hfc⟩ := exists_faceSet_bond_of_isCycle data ambient htwo walk hw
  exact ⟨a, n, root, walk, faces, hn, hc, hw, hd, he, hf, hfc⟩

end
end Mettapedia.GraphTheory.FourColor.AlternatingWalkLobes
