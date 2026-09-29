import Mettapedia.GraphTheory.FourColor.PlanarCycleBoundaryRecognition
import Mettapedia.GraphTheory.FourColor.TubeSlabEmbedding

/-!
# Cycle incidence from actual cubic-graph neighbours

A cyclic list of distinct vertices and one outside neighbour at each vertex
determine the entire induced shore in a cubic graph. The construction below
produces the incidence coordinates used by the uniform orientation theorem.
No rotation, colouring or tangle-isomorphism field is supplied by the input.
-/

namespace Mettapedia.GraphTheory.FourColor.CubicCycleIncidence

open SimpleGraph SimpleGraphDartRotation CycleBoundaryOrientation
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} {G : SimpleGraph V} {k : ℕ} [NeZero k]

/-- Only graph vertices and adjacencies are specified. Cubicity supplies
exhaustiveness; different spokes may meet the same exterior vertex. -/
structure Frame (G : SimpleGraph V) (k : ℕ) [NeZero k] where
  vertex : Fin k ↪ V
  adjacent : ∀ i, G.Adj (vertex i) (vertex (i + 1))
  spoke : Fin k → V
  spoke_adjacent : ∀ i, G.Adj (vertex i) (spoke i)
  spoke_outside : ∀ i j, spoke i ≠ vertex j

namespace Frame

variable (C : Frame G k)

theorem adjacent_prev (i : Fin k) : G.Adj (C.vertex i) (C.vertex (i - 1)) := by
  simpa using (C.adjacent (i - 1)).symm

theorem prev_ne_next (hk : 3 ≤ k) (i : Fin k) : i - 1 ≠ i + 1 := by
  have htwo : (2 : Fin k) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 2 < k)] at hv
  intro h
  have h11 : (1 : Fin k) + 1 = 2 := by
    apply Fin.ext
    simp [Fin.val_add,
      Nat.mod_eq_of_lt (by omega : 1 < k), Nat.mod_eq_of_lt (by omega : 2 < k)]
  have he : i + (0 : Fin k) = i + 2 := by
    simpa [add_assoc, h11] using (sub_eq_iff_eq_add.mp h)
  exact htwo (add_left_cancel he).symm

variable [DecidableEq V] [G.LocallyFinite]

theorem adjacent_iff (hk : 3 ≤ k) (hG : G.IsRegularOfDegree 3) (i : Fin k) (v : V) :
    G.Adj (C.vertex i) v ↔
      v = C.spoke i ∨ v = C.vertex (i - 1) ∨ v = C.vertex (i + 1) := by
  classical
  have hnp := C.vertex.injective.ne (prev_ne_next hk i)
  have hs : {C.spoke i, C.vertex (i - 1), C.vertex (i + 1)} ⊆
      G.neighborFinset (C.vertex i) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · simpa using C.spoke_adjacent i
    · simpa using C.adjacent_prev i
    · simpa using C.adjacent i
  have he : G.neighborFinset (C.vertex i) =
      {C.spoke i, C.vertex (i - 1), C.vertex (i + 1)} := by
    apply (Finset.eq_of_subset_of_card_le hs ?_).symm
    have hd := hG.degree_eq (C.vertex i)
    change (G.neighborFinset (C.vertex i)).card = 3 at hd
    simp [hd, C.spoke_outside, hnp]
  rw [← SimpleGraph.mem_neighborFinset, he]
  simp

/-- The three outgoing graph darts, before choosing any local rotation. -/
def star (i : Fin k) : Fin 3 → G.Dart
  | 0 => ⟨(C.vertex i, C.spoke i), C.spoke_adjacent i⟩
  | 1 => ⟨(C.vertex i, C.vertex (i - 1)), C.adjacent_prev i⟩
  | 2 => ⟨(C.vertex i, C.vertex (i + 1)), C.adjacent i⟩

omit [DecidableEq V] [G.LocallyFinite] in
@[simp] theorem star_fst (i : Fin k) (j : Fin 3) : (C.star i j).fst = C.vertex i := by
  fin_cases j <;> rfl

omit [DecidableEq V] [G.LocallyFinite] in
theorem star_injective (hk : 3 ≤ k) :
    Function.Injective (fun d : CycleBoundaryOrientation.Dart k => C.star d.1 d.2) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ he
  have hij : i = j := C.vertex.injective (by
    simpa only [star_fst] using congrArg (fun d : G.Dart => d.fst) he)
  subst j
  have hs := congrArg (fun d : G.Dart => d.snd) he
  have hnp := C.vertex.injective.ne (prev_ne_next hk i)
  have hsp := C.spoke_outside i (i - 1)
  have hsn := C.spoke_outside i (i + 1)
  fin_cases a <;> fin_cases b <;> simp_all [star]

theorem star_surjective_at (hk : 3 ≤ k) (hG : G.IsRegularOfDegree 3)
    (i : Fin k) (d : G.Dart) (hd : d.fst = C.vertex i) :
    ∃ j, C.star i j = d := by
  have ha : G.Adj (C.vertex i) d.snd := hd ▸ d.adj
  rcases (C.adjacent_iff hk hG i d.snd).mp ha with h | h | h
  · exact ⟨0, by apply SimpleGraph.Dart.ext; exact Prod.ext hd.symm h.symm⟩
  · exact ⟨1, by apply SimpleGraph.Dart.ext; exact Prod.ext hd.symm h.symm⟩
  · exact ⟨2, by apply SimpleGraph.Dart.ext; exact Prod.ext hd.symm h.symm⟩

variable [Fintype V] [DecidableRel G.Adj]

local instance cycleIncidenceEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance cycleIncidenceEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Delete everything outside the displayed cycle. -/
def deleted : Finset V := Finset.univ.filter fun v => ¬ ∃ i, v = C.vertex i

abbrev keep (v : V) : Prop := deletedRegionKeep C.deleted v

omit [G.LocallyFinite] [DecidableRel G.Adj] in
@[simp] theorem keep_iff (v : V) : C.keep v ↔ ∃ i, v = C.vertex i := by
  classical
  simp [keep, deleted, deletedRegionKeep]

omit [G.LocallyFinite] [DecidableRel G.Adj] in
theorem vertex_keep (i : Fin k) : C.keep (C.vertex i) := (C.keep_iff _).2 ⟨i, rfl⟩

omit [G.LocallyFinite] [DecidableRel G.Adj] in
theorem spoke_not_keep (i : Fin k) : ¬ C.keep (C.spoke i) := by
  rintro h
  obtain ⟨j, hj⟩ := (C.keep_iff _).1 h
  exact C.spoke_outside i j hj

def vertexEquiv : Fin k ≃ {v // C.keep v} :=
  Equiv.ofBijective (fun i => ⟨C.vertex i, C.vertex_keep i⟩) ⟨by
    intro i j h
    exact C.vertex.injective (congrArg Subtype.val h), by
    intro v
    obtain ⟨i, hi⟩ := (C.keep_iff _).1 v.2
    exact ⟨i, Subtype.ext hi.symm⟩⟩

omit [G.LocallyFinite] [DecidableRel G.Adj] in
/-- The displayed cycle itself supplies connectedness of the retained shore. -/
theorem connected : (G.induce {v | C.keep v}).Connected := by
  have hp : ∀ (n : ℕ) (hn : n < k), (G.induce {v | C.keep v}).Reachable
      (C.vertexEquiv 0) (C.vertexEquiv ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero => intro hn; exact .refl _
    | succ n ih =>
        intro hn
        have hprev : n < k := by omega
        have he : (⟨n, hprev⟩ : Fin k) + 1 = ⟨n + 1, hn⟩ := by
          apply Fin.ext
          simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < k), Nat.mod_eq_of_lt hn]
        have ha : (G.induce {v | C.keep v}).Adj
            (C.vertexEquiv ⟨n, hprev⟩) (C.vertexEquiv (⟨n, hprev⟩ + 1)) :=
          C.adjacent ⟨n, hprev⟩
        rw [he] at ha
        exact (ih hprev).trans ha.reachable
  refine { nonempty := ⟨C.vertexEquiv 0⟩, preconnected := ?_ }
  intro u v
  obtain ⟨i, rfl⟩ := C.vertexEquiv.surjective u
  obtain ⟨j, rfl⟩ := C.vertexEquiv.surjective v
  have hi : (G.induce {v | C.keep v}).Reachable (C.vertexEquiv 0) (C.vertexEquiv i) := by
    exact hp i.val i.isLt
  have hj : (G.induce {v | C.keep v}).Reachable (C.vertexEquiv 0) (C.vertexEquiv j) := by
    exact hp j.val j.isLt
  exact hi.symm.trans hj

variable (rotation : Data G)

def retained (d : CycleBoundaryOrientation.Dart k) :
    RetainedDart rotation.toRotationSystem C.keep :=
  ⟨C.star d.1 d.2, by
    change C.keep (C.star d.1 d.2).fst
    rw [C.star_fst]
    exact C.vertex_keep d.1⟩

def retainedEquiv (hk : 3 ≤ k) (hG : G.IsRegularOfDegree 3) :
    CycleBoundaryOrientation.Dart k ≃ RetainedDart rotation.toRotationSystem C.keep :=
  Equiv.ofBijective (C.retained rotation) ⟨by
    intro d e he
    exact C.star_injective hk (congrArg Subtype.val he), by
    intro d
    obtain ⟨i, hi⟩ := (C.keep_iff _).1 d.2
    obtain ⟨j, hj⟩ := C.star_surjective_at hk hG i d.1 hi
    exact ⟨(i, j), Subtype.ext hj⟩⟩

def boundaryDart (i : Fin k) : BoundaryDart rotation.toRotationSystem C.keep :=
  ⟨C.retained rotation (i, 0), C.spoke_not_keep i⟩

omit [G.LocallyFinite] [DecidableRel G.Adj] in
theorem star_boundary_iff (i : Fin k) (j : Fin 3) :
    (¬ C.keep (C.star i j).snd) ↔ j = 0 := by
  fin_cases j <;> simp [star, C.spoke_not_keep, C.vertex_keep]

def portEquiv (hk : 3 ≤ k) (hG : G.IsRegularOfDegree 3) :
    Fin k ≃ BoundaryDart rotation.toRotationSystem C.keep :=
  Equiv.ofBijective (C.boundaryDart rotation) ⟨by
    intro i j he
    have h : (i, (0 : Fin 3)) = (j, 0) := C.star_injective hk
      (show C.star i 0 = C.star j 0 from congrArg (fun d => d.val.val) he)
    exact congrArg Prod.fst h, by
    intro d
    obtain ⟨⟨i, j⟩, he⟩ := (C.retainedEquiv rotation hk hG).surjective d.1
    have hd : ¬ C.keep (C.star i j).snd := by
      change ¬ C.keep (rotation.toRotationSystem.vertOf
        (rotation.toRotationSystem.alpha (C.retained rotation (i, j)).1))
      change C.retained rotation (i, j) = d.1 at he
      rw [he]
      exact d.2
    have hj := (C.star_boundary_iff i j).1 hd
    subst j
    exact ⟨i, Subtype.ext he⟩⟩

def coordinate (hk : 3 ≤ k) (hG : G.IsRegularOfDegree 3) :
    CycleBoundaryOrientation.Dart k ≃
      InternalDart rotation.toRotationSystem C.keep ⊕ BoundaryDart rotation.toRotationSystem C.keep :=
  (C.retainedEquiv rotation hk hG).trans
    (retainedDartEquivInternalSumBoundary rotation.toRotationSystem C.keep)

def tangle := ofVertexSide rotation.toRotationSystem C.keep (C.retained rotation (0, 0))

theorem coordinate_boundary (hk : 3 ≤ k) (hG : G.IsRegularOfDegree 3) (i : Fin k) :
    C.coordinate rotation hk hG (i, 0) = .inr (C.portEquiv rotation hk hG i) :=
  TubeSlab.equiv_boundary _ _ (C.boundaryDart rotation i)

theorem coordinate_vert (hk : 3 ≤ k) (hG : G.IsRegularOfDegree 3)
    (d : CycleBoundaryOrientation.Dart k) :
    (C.tangle rotation).vertOf (C.coordinate rotation hk hG d) = C.vertexEquiv d.1 := by
  change openTangleVertOf
    (fun d : InternalDart rotation.toRotationSystem C.keep =>
      vertexSideVertex rotation.toRotationSystem C.keep d.1)
    (fun d : BoundaryDart rotation.toRotationSystem C.keep =>
      vertexSideVertex rotation.toRotationSystem C.keep d.1) _ = _
  rw [openTangleVertOf_vertexSide_partition_symm]
  simp only [coordinate, Equiv.trans_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  exact C.star_fst _ _

omit [G.LocallyFinite] in
theorem retained_flip (d : CycleBoundaryOrientation.Dart k) :
    C.retained rotation (CycleBoundaryOrientation.flip k d) =
      retainedCappedAlpha rotation.toRotationSystem C.keep (C.retained rotation d) := by
  rcases d with ⟨i, j⟩
  fin_cases j
  · rw [retainedCappedAlpha_apply_boundary _ _ _ (C.spoke_not_keep i)]
    rfl
  · apply Subtype.ext
    refine Eq.trans ?_ (retainedCappedAlpha_apply_internal rotation.toRotationSystem C.keep
      (C.retained rotation (i, 1)) (C.vertex_keep (i - 1))).symm
    change C.star (i - 1) 2 = (C.star i 1).symm
    apply SimpleGraph.Dart.ext
    simp [star, SimpleGraph.Dart.symm]
  · apply Subtype.ext
    refine Eq.trans ?_ (retainedCappedAlpha_apply_internal rotation.toRotationSystem C.keep
      (C.retained rotation (i, 2)) (C.vertex_keep (i + 1))).symm
    change C.star (i + 1) 1 = (C.star i 2).symm
    apply SimpleGraph.Dart.ext
    simp [star, SimpleGraph.Dart.symm]

theorem coordinate_alpha (hk : 3 ≤ k) (hG : G.IsRegularOfDegree 3)
    (d : CycleBoundaryOrientation.Dart k) :
    C.coordinate rotation hk hG (CycleBoundaryOrientation.flip k d) =
      Equiv.sumCongr (C.tangle rotation).interiorAlpha (Equiv.refl _)
        (C.coordinate rotation hk hG d) := by
  let e := retainedDartEquivInternalSumBoundary rotation.toRotationSystem C.keep
  have h (x : RetainedDart rotation.toRotationSystem C.keep) :
      e (retainedCappedAlpha rotation.toRotationSystem C.keep x) =
        Equiv.sumCongr (C.tangle rotation).interiorAlpha (Equiv.refl _) (e x) := by
    obtain ⟨y, rfl⟩ := e.symm.surjective x
    cases y with
    | inl a =>
        rw [e.apply_symm_apply]
        have ha := retainedCappedAlpha_apply_internal rotation.toRotationSystem C.keep a.1 a.2
        change e (retainedCappedAlpha rotation.toRotationSystem C.keep a.1) = .inl _
        rw [show retainedCappedAlpha rotation.toRotationSystem C.keep a.1 =
          (internalAlpha rotation.toRotationSystem C.keep a).1 from Subtype.ext ha]
        exact TubeSlab.equiv_internal _ _ (internalAlpha _ _ a)
    | inr a =>
        rw [e.apply_symm_apply]
        change e (retainedCappedAlpha rotation.toRotationSystem C.keep a.1) = .inr a
        rw [retainedCappedAlpha_apply_boundary _ _ _ a.2]
        exact TubeSlab.equiv_boundary _ _ a
  change e (C.retained rotation (CycleBoundaryOrientation.flip k d)) = _
  rw [C.retained_flip]
  exact h _

/-- Construct the complete incidence coordinates from the graph. In
particular, rotations are not part of this construction's hypotheses. -/
def incidence (hk : 3 ≤ k) (hG : G.IsRegularOfDegree 3) :
    CycleBoundaryOrientation.Incidence k (C.tangle rotation) where
  vertex := C.vertexEquiv
  port := C.portEquiv rotation hk hG
  darts := C.coordinate rotation hk hG
  boundary := C.coordinate_boundary rotation hk hG
  vert := C.coordinate_vert rotation hk hG
  alpha := C.coordinate_alpha rotation hk hG

open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24FaceDualConnectedness

/-- Source-facing recognition: graph adjacency plus spherical geometry gives
both the actual rotations and the exact port return, with one shared choice.
Only connectedness of the exterior is an additional connectivity hypothesis. -/
theorem uniform_geometry (hk : 3 ≤ k)
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    (hexterior : (G.induce {v | ¬ C.keep v}).Connected) :
    ∃ b : Bool,
      (∀ d : CycleBoundaryOrientation.Dart k,
        rotation.vertexRotation (C.star d.1 d.2) =
          C.star (turn k (fun _ => b) d).1 (turn k (fun _ => b) d).2) ∧
      ∀ i, retainedRegionBoundarySuccessor rotation.toRotationSystem C.keep
          (C.boundaryDart rotation i) =
        C.boundaryDart rotation (if b then i + 1 else i - 1) := by
  have hG : G.IsRegularOfDegree 3 := fun v =>
    (SimpleGraph.degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp hsphere.cubic) v)
  obtain ⟨b, hb, hp⟩ := PlanarCycleBoundaryRecognition.uniform_geometry_of_planarBond
    rotation C.deleted (C.retained rotation (0, 0)) (C.incidence rotation hk hG)
    hsphere htwo hconnected hrotation C.connected hexterior
  refine ⟨b, ?_, ?_⟩
  · intro d
    have h := hb d
    change (C.tangle rotation).rho (C.coordinate rotation hk hG d) =
      C.coordinate rotation hk hG (turn k (fun _ => b) d) at h
    have hh := congrArg (retainedDartEquivInternalSumBoundary rotation.toRotationSystem C.keep).symm h
    change (retainedDartEquivInternalSumBoundary rotation.toRotationSystem C.keep).symm
      ((ofVertexSide rotation.toRotationSystem C.keep (C.retained rotation (0, 0))).rho _) = _ at hh
    rw [ofVertexSide_rho_underlying] at hh
    simp only [coordinate, Equiv.trans_apply, Equiv.symm_apply_apply] at hh
    exact congrArg Subtype.val hh
  · intro i
    have h := hp i
    change OpenTanglePortReplacement.returnCode (C.tangle rotation)
      (C.boundaryDart rotation i) = C.boundaryDart rotation _ at h
    rw [tangle, OpenTangleVertexSideReturn.returnCode_eq] at h
    exact h

end Frame
end

end Mettapedia.GraphTheory.FourColor.CubicCycleIncidence
