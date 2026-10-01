import MettapediaFourColor.ExceptionalCore

/-!
# Facial orientation of the D1774 core

The prescribed core turns come from the pinned D1774 cyclic neighbour rows.
Fifteen are already turns of the first source exceptional occurrence. The
remaining three belong to the newly closed triangle. Triangular face closure
transports one of its turns to the other two, preserving actual ambient darts.
-/

namespace FourColor.ExceptionalCoreOrientation

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalPattern ExceptionalOverlap ExceptionalCore

set_option maxRecDepth 32768

variable {V : Type*} {G : SimpleGraph V} (rotation : Data G)

/-- A directed corner of an actual face, expressed at its first vertex. -/
def Corner (a b c : V) : Prop :=
  ∃ (hab : G.Adj a b) (hac : G.Adj a c),
    rotation.vertexRotation ⟨(a, b), hab⟩ = ⟨(a, c), hac⟩

theorem Corner.rotate [G.LocallyFinite] (tri : Triangular rotation)
    {a b c : V} (h : Corner rotation a b c) : Corner rotation b c a := by
  obtain ⟨hab, hac, step⟩ := h
  let ab : G.Dart := ⟨(a, b), hab⟩
  let ac : G.Dart := ⟨(a, c), hac⟩
  change rotation.vertexRotation ab = ac at step
  have hbc : G.Adj b c := by
    have h := consecutive_adjacent rotation tri ab
    rw [step] at h
    exact h
  let bc : G.Dart := ⟨(b, c), hbc⟩
  have hc : rotation.vertexRotation ac.symm = bc.symm := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact rotation.vertexRotation_fst ac.symm
    · have he := congrArg (fun e : G.Dart => e.fst) (tri ab.symm)
      simp only [SimpleGraph.Dart.symm_symm] at he
      rw [step, rotation.vertexRotation_fst] at he
      exact he
  have hb := tri ab.symm
  simp only [SimpleGraph.Dart.symm_symm] at hb
  rw [step, hc, SimpleGraph.Dart.symm_symm] at hb
  exact ⟨hbc, hab.symm, hb⟩

/-- A consecutive pair in the full source star; ring vertices are not
silently removed before testing consecutiveness. -/
def CoreTurn (i j k : Fin 8) : Prop :=
  core.Adj i j ∧ core.Adj i k ∧
    (j.val + 12, k.val + 12) ∈
      (input.neighbors (i.natAdd 11)).zip ((input.neighbors (i.natAdd 11)).rotate 1)

instance (i j k : Fin 8) : Decidable (CoreTurn i j k) := by
  unfold CoreTurn
  infer_instance

theorem old_turns : ∀ i j k : Fin 7,
    CoreTurn i.castSucc j.castSucc k.castSucc →
      ExceptionalPattern.Turn (oldLabel i) (oldLabel j) (oldLabel k) := by
  decide +kernel

theorem turn_partition : ∀ i j k : Fin 8, CoreTurn i j k →
    ((i, j, k) ∈ ([(0, 7, 5), (5, 0, 7), (7, 5, 0)] : List (Fin 8 × Fin 8 × Fin 8))) ∨
      (i.val < 7 ∧ j.val < 7 ∧ k.val < 7) := by
  decide +kernel

variable {rotation} [G.LocallyFinite] (x : Occurrence rotation)

theorem closing_corner : Corner rotation (coreVertex x 0) (coreVertex x 7)
    (coreVertex x 5) := by
  change Corner rotation (x.vertex 14) (closingDart x).snd (x.vertex 15)
  have hab : G.Adj (x.vertex 14) (closingDart x).snd := by
    simpa only [closing_fst] using (closingDart x).adj
  refine ⟨hab, x.edge 14 15 (by decide +kernel), ?_⟩
  have hd : (⟨(x.vertex 14, (closingDart x).snd), hab⟩ : G.Dart) = closingDart x := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext (closing_fst x).symm rfl
  rw [hd]
  exact rotation.vertexRotation.apply_symm_apply _

/-- All prescribed inner corners are preserved, including the three new
corners forced by triangular closure. -/
theorem preserves_turns (tri : Triangular rotation) (i j k : Fin 8)
    (h : CoreTurn i j k) :
    Corner rotation (coreVertex x i) (coreVertex x j) (coreVertex x k) := by
  rcases turn_partition i j k h with hn | ⟨hi, hj, hk⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hn
    rcases hn with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact closing_corner x
    · exact Corner.rotate rotation tri (Corner.rotate rotation tri (closing_corner x))
    · exact Corner.rotate rotation tri (closing_corner x)
  · let a : Fin 7 := ⟨i.val, hi⟩
    let b : Fin 7 := ⟨j.val, hj⟩
    let c : Fin 7 := ⟨k.val, hk⟩
    have ei : i = a.castSucc := by apply Fin.ext; rfl
    have ej : j = b.castSucc := by apply Fin.ext; rfl
    have ek : k = c.castSucc := by apply Fin.ext; rfl
    rw [ei, ej, ek] at h ⊢
    rw [vertex_old, vertex_old, vertex_old]
    have hab := (old_edges a b).mp h.1
    have hac := (old_edges a c).mp h.2.1
    exact ⟨x.edge _ _ hab, x.edge _ _ hac,
      x.turn _ _ _ hab hac (old_turns a b c h)⟩

/-- The retained joint witness supplies orientation as well as its already
proved core adjacency and degree observations. -/
theorem joint_preserves_turns (r : JointReading rotation) (tri : Triangular rotation)
    (i j k : Fin 8) (h : CoreTurn i j k) :
    Corner rotation (r.core.map i) (r.core.map j) (r.core.map k) := by
  rw [r.realizes, r.realizes, r.realizes]
  exact preserves_turns r.first tri i j k h

end FourColor.ExceptionalCoreOrientation
