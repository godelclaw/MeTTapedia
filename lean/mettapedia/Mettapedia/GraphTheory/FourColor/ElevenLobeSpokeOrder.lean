import Mettapedia.GraphTheory.FourColor.CycleSpokeConnectivity
import Mettapedia.GraphTheory.FourColor.GoertzelV24ComplementaryShoreBoundaryOrder

/-!
# Spoke order in an alternating eleven-lobe

Two disjoint graph cycles describe the local incidence. The five inner
spokes meet the odd positions of the outer eleven-cycle in an arbitrary
order. Alternating outer rotations determine its inner boundary walk,
including the longer gap at the closing seam. Spherical geometry then
forces the inner spoke order and orientation to agree with that walk.
-/

namespace Mettapedia.GraphTheory.FourColor.ElevenLobeSpokeOrder

open SimpleGraph SimpleGraphDartRotation CubicCycleIncidence CycleBoundaryOrientation
open GoertzelV24RotationCutDartDecomposition GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24FaceDualConnectedness

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Five inward attachments, separated by four one-vertex gaps and the
two-vertex gap across the closing seam. -/
def inward : Fin 5 ↪ Fin 11 where
  toFun i := ⟨2 * i.val + 1, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def reverseAt (i : Fin 11) : Bool := decide (i.val % 2 = 0)

/-- A map of a cyclic interface preserving a chosen direction is determined
by its phase and direction. This is independent of the interface length. -/
theorem eq_shift_or_reflection_of_step {k : ℕ} [NeZero k]
    (f : Fin k → Fin k) (b : Bool)
    (h : ∀ i, f (if b then i + 1 else i - 1) = f i + 1) :
    ∀ i, f i = if b then f 0 + i else f 0 - i := by
  have step (i : Fin k) : f (i + 1) = if b then f i + 1 else f i - 1 := by
    cases b
    · have hh := h (i + 1)
      simp only [Bool.false_eq_true, ite_false, add_sub_cancel_right] at hh ⊢
      exact eq_sub_iff_add_eq.mpr hh.symm
    · simpa using h i
  have all (n : ℕ) (hn : n < k) :
      f ⟨n, hn⟩ = if b then f 0 + ⟨n, hn⟩ else f 0 - ⟨n, hn⟩ := by
    induction n with
    | zero => simp
    | succ n ih =>
        have hprev : n < k := by omega
        have he : (⟨n, hprev⟩ : Fin k) + 1 = ⟨n + 1, hn⟩ := by
          apply Fin.ext
          simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < k), Nat.mod_eq_of_lt hn]
        rw [← he, step, ih hprev]
        cases b <;> simp <;> abel
  intro i
  exact all i.val i.isLt

variable {V : Type*} {G : SimpleGraph V}

/-- The matching is arbitrary incidence data, not a supplied cyclic order.
No inner rotation or colouring appears in the input. -/
structure Incidence (G : SimpleGraph V) where
  outer : Frame G 11
  inner : Frame G 5
  disjoint : ∀ i j, outer.vertex i ≠ inner.vertex j
  matching : Equiv.Perm (Fin 5)
  spoke : ∀ i, inner.spoke i = outer.vertex (inward (matching i))

namespace Incidence

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite]
  (L : Incidence G)

omit [DecidableRel G.Adj] [G.LocallyFinite] in
theorem outer_not_inner (i : Fin 11) : ¬ L.inner.keep (L.outer.vertex i) := by
  rintro h
  obtain ⟨j, hj⟩ := (L.inner.keep_iff _).mp h
  exact L.disjoint i j hj

omit [DecidableRel G.Adj] in
theorem exterior_connected (hcubic : G.IsRegularOfDegree 3) (hconnected : G.Connected) :
    (G.induce {v | ¬ L.inner.keep v}).Connected := by
  apply CycleSpokeConnectivity.exterior_connected_of_spokes_in_connected_side
    L.inner (by decide) hcubic hconnected {v | L.outer.keep v} L.outer.connected
  · intro v hv
    obtain ⟨i, rfl⟩ := (L.outer.keep_iff v).mp hv
    exact L.outer_not_inner i
  · intro i
    rw [L.spoke]
    exact L.outer.vertex_keep _

omit [Fintype V] [DecidableRel G.Adj] in
theorem outer_spoke (hcubic : G.IsRegularOfDegree 3) (j : Fin 5) :
    L.outer.spoke (inward j) = L.inner.vertex (L.matching.symm j) := by
  have ha := (L.inner.spoke_adjacent (L.matching.symm j)).symm
  rw [L.spoke, L.matching.apply_symm_apply] at ha
  rcases (L.outer.adjacent_iff (by decide) hcubic (inward j) _).mp ha with he | he | he
  · exact he.symm
  · exact (L.disjoint _ _ he.symm).elim
  · exact (L.disjoint _ _ he.symm).elim

local instance lobeOrderEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance lobeOrderEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G)

def outerDart (d : CycleBoundaryOrientation.Dart 11) :
    RetainedDart rotation.toRotationSystem (fun v => ¬ L.inner.keep v) :=
  ⟨L.outer.star d.1 d.2, by
    change ¬ L.inner.keep (L.outer.star d.1 d.2).fst
    rw [L.outer.star_fst]
    exact L.outer_not_inner d.1⟩

def port (hcubic : G.IsRegularOfDegree 3) (j : Fin 5) :
    BoundaryDart rotation.toRotationSystem (fun v => ¬ L.inner.keep v) :=
  ⟨L.outerDart rotation (inward j, 0), by
    change ¬ ¬ L.inner.keep (L.outer.spoke (inward j))
    rw [L.outer_spoke hcubic]
    exact not_not_intro (L.inner.vertex_keep _)⟩

theorem port_injective (hcubic : G.IsRegularOfDegree 3) :
    Function.Injective (L.port rotation hcubic) := by
  intro i j he
  have hh := congrArg (fun d => d.val.val.fst) he
  change L.outer.vertex (inward i) = L.outer.vertex (inward j) at hh
  exact inward.injective (L.outer.vertex.injective hh)

theorem complement_port (hcubic : G.IsRegularOfDegree 3) (i : Fin 5) :
    complementBoundaryAlphaEquiv rotation.toRotationSystem L.inner.deleted
        (L.inner.boundaryDart rotation i) = L.port rotation hcubic (L.matching i) := by
  apply Subtype.ext
  apply Subtype.ext
  apply SimpleGraph.Dart.ext
  change (L.inner.spoke i, L.inner.vertex i) =
    (L.outer.vertex (inward (L.matching i)), L.outer.spoke (inward (L.matching i)))
  simp [L.spoke, L.outer_spoke hcubic]

variable (hcubic : G.IsRegularOfDegree 3)
  (houterRotation : ∀ d : CycleBoundaryOrientation.Dart 11,
    rotation.vertexRotation (L.outer.star d.1 d.2) =
      L.outer.star (turn 11 reverseAt d).1 (turn 11 reverseAt d).2)

include hcubic houterRotation

theorem face_port (j : Fin 5) :
    retainedCappedFacePerm rotation.toRotationSystem (fun v => ¬ L.inner.keep v)
      (L.outerDart rotation (inward j, 0)) = L.outerDart rotation (inward j, 1) := by
  rw [retainedCappedFacePerm, Equiv.Perm.mul_apply,
    retainedCappedAlpha_apply_boundary _ _ _ (L.port rotation hcubic j).2]
  apply Subtype.ext
  change rotation.vertexRotation (L.outer.star (inward j) 0) = L.outer.star (inward j) 1
  rw [houterRotation (inward j, 0)]
  have ho : reverseAt (inward j) = false := by
    fin_cases j <;> decide
  simp [turn, ho]

omit hcubic [G.LocallyFinite] in
theorem face_prev (i : Fin 11) :
    retainedCappedFacePerm rotation.toRotationSystem (fun v => ¬ L.inner.keep v)
      (L.outerDart rotation (i, 1)) =
        L.outerDart rotation (i - 1, if reverseAt (i - 1) then 1 else 0) := by
  have he : retainedCappedAlpha rotation.toRotationSystem (fun v => ¬ L.inner.keep v)
      (L.outerDart rotation (i, 1)) = L.outerDart rotation (i - 1, 2) := by
    apply Subtype.ext
    refine (retainedCappedAlpha_apply_internal rotation.toRotationSystem _ _
      (L.outer_not_inner (i - 1))).trans ?_
    change (L.outer.star i 1).symm = L.outer.star (i - 1) 2
    apply SimpleGraph.Dart.ext
    simp [Frame.star, SimpleGraph.Dart.symm]
  rw [retainedCappedFacePerm, Equiv.Perm.mul_apply, he]
  apply Subtype.ext
  change rotation.vertexRotation (L.outer.star (i - 1) 2) =
    L.outer.star (i - 1) (if reverseAt (i - 1) then 1 else 0)
  rw [houterRotation (i - 1, 2)]
  cases h : reverseAt (i - 1) <;> simp [turn, h]

/-- The closing gap is included: four face steps there, three elsewhere.
Every intermediate dart remains strictly inside the complementary shore. -/
theorem boundary_return (j : Fin 5) :
    retainedRegionBoundarySuccessor rotation.toRotationSystem (fun v => ¬ L.inner.keep v)
      (L.port rotation hcubic j) = L.port rotation hcubic (j - 1) := by
  apply PermutationFirstReturnRestriction.nextHit_eq_of_returnArc
  refine (show PermutationFirstReturnRestriction.ReturnArc
    (retainedCappedFacePerm rotation.toRotationSystem (fun v => ¬ L.inner.keep v))
    (fun d => ¬ (¬ L.inner.keep (rotation.toRotationSystem.vertOf
      (rotation.toRotationSystem.alpha d.1))))
    (L.port rotation hcubic j).1 (L.port rotation hcubic (j - 1)).1
    (if j = 0 then 4 else 3) from ?_)
  constructor
  · split <;> omega
  constructor
  · change _ = L.outerDart rotation (inward (j - 1), 0)
    dsimp only [port]
    have hstart := L.face_port rotation hcubic houterRotation j
    fin_cases j <;>
      norm_num at hstart ⊢ <;>
      simp only [pow_succ', pow_zero, Equiv.Perm.one_apply, Equiv.Perm.mul_apply] <;>
      rw [hstart] <;>
      norm_num [
        L.face_prev rotation houterRotation, inward, reverseAt, Fin.sub_def, Fin.neg_def]
  · intro n hn hnlen
    let hit : RetainedDart rotation.toRotationSystem (fun v => ¬ L.inner.keep v) → Prop :=
      fun d => ¬ ¬ L.inner.keep d.1.snd
    change ¬ hit ((retainedCappedFacePerm rotation.toRotationSystem
      (fun v => ¬ L.inner.keep v) ^ n) (L.outerDart rotation (inward j, 0)))
    have hstart := L.face_port rotation hcubic houterRotation j
    fin_cases j <;>
      norm_num at hnlen hstart <;>
      interval_cases n <;>
      simp only [pow_succ', pow_zero, Equiv.Perm.one_apply, Equiv.Perm.mul_apply] <;>
      erw [hstart] <;>
      norm_num [L.face_prev rotation houterRotation, inward, reverseAt,
        Fin.sub_def, Fin.neg_def] <;>
      simp [hit, outerDart, Frame.star, L.disjoint]

omit hcubic in
/-- The same orientation controls the inner vertex turns and the matching
of its spokes to the outer lobe. No independent choices can disagree. -/
theorem inner_geometry
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem) :
    ∃ b : Bool,
      (∀ d : CycleBoundaryOrientation.Dart 5,
        rotation.vertexRotation (L.inner.star d.1 d.2) =
          L.inner.star (turn 5 (fun _ => b) d).1 (turn 5 (fun _ => b) d).2) ∧
      ∀ i, L.matching (if b then i + 1 else i - 1) = L.matching i + 1 := by
  have hcubic : G.IsRegularOfDegree 3 := fun v =>
    (SimpleGraph.degree_instance_independent v _ _).trans
      ((rotation.toRotationSystem_isCubic_iff.mp hsphere.cubic) v)
  have hext := L.exterior_connected hcubic hconnected
  obtain ⟨b, hb, hr⟩ := L.inner.uniform_geometry rotation (by decide)
    hsphere htwo hconnected hrotation hext
  refine ⟨b, hb, ?_⟩
  intro i
  have hopposite := boundarySuccessors_opposite_of_planarBond rotation L.inner.deleted
    hsphere htwo hconnected hrotation L.inner.connected hext (L.inner.boundaryDart rotation i)
  change retainedRegionBoundarySuccessor rotation.toRotationSystem (fun v => ¬ L.inner.keep v)
    (complementBoundaryAlphaEquiv rotation.toRotationSystem L.inner.deleted
      (retainedRegionBoundarySuccessor rotation.toRotationSystem L.inner.keep
        (L.inner.boundaryDart rotation i))) = _ at hopposite
  rw [hr, L.complement_port rotation hcubic, L.complement_port rotation hcubic,
    L.boundary_return rotation hcubic houterRotation] at hopposite
  exact sub_eq_iff_eq_add.mp (L.port_injective rotation hcubic hopposite)

omit hcubic in
/-- The arbitrary input matching is a shift or a reflected shift, and its
direction is exactly the direction of every actual inner vertex rotation. -/
theorem inner_geometry_affine
    (hsphere : OrbitSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem) :
    ∃ b : Bool,
      (∀ d : CycleBoundaryOrientation.Dart 5,
        rotation.vertexRotation (L.inner.star d.1 d.2) =
          L.inner.star (turn 5 (fun _ => b) d).1 (turn 5 (fun _ => b) d).2) ∧
      ∀ i, L.matching i = if b then L.matching 0 + i else L.matching 0 - i := by
  obtain ⟨b, hb, hm⟩ := L.inner_geometry rotation houterRotation hsphere htwo hconnected hrotation
  exact ⟨b, hb, eq_shift_or_reflection_of_step L.matching b hm⟩

end Incidence
end
end Mettapedia.GraphTheory.FourColor.ElevenLobeSpokeOrder
