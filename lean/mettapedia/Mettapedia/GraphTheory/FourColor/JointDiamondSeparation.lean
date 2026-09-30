import Mettapedia.GraphTheory.FourColor.PartialCubicDartBoundary

/-!
# Joint separation of the hexagon/hexagon diamond

The diagram has fourteen vertices, seventeen internal edges and eight
unpaired slots. Joint dart transport and girth separate every vertex pair
except two pairs at the opposite pentagonal ends. Identifying those ends
would consume four ports and leave a cyclic shore behind a four-edge cut.
-/

namespace Mettapedia.GraphTheory.FourColor.JointDiamond

open PartialCubicDartSeparation

abbrev Vertex := Fin 14
abbrev Slot := Vertex × Fin 3

def flat (d : Slot) : Fin 42 := ⟨3 * d.1.val + d.2.val, by omega⟩
def unflat (i : Fin 42) : Slot := (⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩)

def flipCodes : String := "D@XAM@J@OGb@EhIS@aPV@TgC\\@dY_@]eRKj[`iWNfc"

def flip (d : Slot) : Option Slot :=
  let n := (flipCodes.toUTF8[flat d |>.val]?.getD 64).toNat
  if n = 64 then none else some (unflat ⟨(n - 65) % 42, Nat.mod_lt _ (by decide)⟩)

def rotate (d : Slot) : Slot := (d.1, d.2 + 1)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def diagram : Diagram Vertex where
  rotate := rotate
  flip := flip
  flip_reverse := by decide

def exceptional (u v : Vertex) : Prop :=
  (u = 2 ∧ v = 6) ∨ (u = 6 ∧ v = 2) ∨
  (u = 3 ∧ v = 5) ∨ (u = 5 ∧ v = 3)

instance (u v : Vertex) : Decidable (exceptional u v) :=
  inferInstanceAs (Decidable ((u = 2 ∧ v = 6) ∨ (u = 6 ∧ v = 2) ∨
    (u = 3 ∧ v = 5) ∨ (u = 5 ∧ v = 3)))

def terminal (a b : Slot) : Bool := diagram.apart a b ||
  decide ((a.1 = 0 ∧ b.1 = 9) ∨ (a.1 = 9 ∧ b.1 = 0) ∨
    (a.1 = 1 ∧ b.1 = 8) ∨ (a.1 = 8 ∧ b.1 = 1))

theorem separates_nonexceptional : ∀ u v : Vertex, u ≠ v → ¬ exceptional u v →
    ∀ s : Fin 3, diagram.separatesWith terminal 6 (u, 0) (v, s) = true := by decide

theorem separates_nonzero_phase : ∀ s : Fin 3, s ≠ 0 →
    diagram.separatesWith terminal 6 (2, 0) (6, s) = true := by decide

variable {V : Type*} {G : SimpleGraph V} (F : Realization diagram G)

theorem terminal_sound (ht : Realization.TriangleFree (G := G))
    (hf : Realization.FourCycleFree (G := G)) (a b : Slot)
    (h : terminal a b = true) : F.dart a ≠ F.dart b := by
  have h09 : F.vertex 0 ≠ F.vertex 9 :=
    F.ne_of_path_four hf (b := 7) (c := 12) (d := 10) (by decide) (by decide)
      (diagram.pathCheck_sound (by decide)) (diagram.pathCheck_sound (by decide))
      (diagram.pathCheck_sound (by decide)) (diagram.pathCheck_sound (by decide))
  have h18 : F.vertex 1 ≠ F.vertex 8 :=
    F.ne_of_path_four hf (b := 4) (c := 13) (d := 11) (by decide) (by decide)
      (diagram.pathCheck_sound (by decide)) (diagram.pathCheck_sound (by decide))
      (diagram.pathCheck_sound (by decide)) (diagram.pathCheck_sound (by decide))
  simp only [terminal, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact F.apart_sound ht h
  · intro he
    have hv : F.vertex a.1 = F.vertex b.1 := by
      simpa only [F.fst] using congrArg (fun d : G.Dart => d.fst) he
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb] at hv; exact h09 hv
    · rw [ha, hb] at hv; exact h09 hv.symm
    · rw [ha, hb] at hv; exact h18 hv
    · rw [ha, hb] at hv; exact h18 hv.symm

theorem ne_nonexceptional (ht : Realization.TriangleFree (G := G))
    (hf : Realization.FourCycleFree (G := G)) {u v : Vertex}
    (hne : u ≠ v) (hex : ¬ exceptional u v) : F.vertex u ≠ F.vertex v := by
  intro he
  obtain ⟨s, hs⟩ := F.slots_surjective v (F.dart (u, 0)) ((F.fst _).trans he)
  exact F.separatesWith_sound terminal (terminal_sound F ht hf)
    (separates_nonexceptional u v hne hex s) hs.symm

/-- Equality at the exceptional pair fixes the phase; arbitrary independent
slot choices would miss this constraint. -/
theorem exceptional_dart_eq (ht : Realization.TriangleFree (G := G))
    (hf : Realization.FourCycleFree (G := G)) (he : F.vertex 2 = F.vertex 6) :
    F.dart (2, 0) = F.dart (6, 0) := by
  obtain ⟨s, hs⟩ := F.slots_surjective 6 (F.dart (2, 0)) ((F.fst _).trans he)
  have hz : s = 0 := by
    by_contra hn
    exact F.separatesWith_sound terminal (terminal_sound F ht hf)
      (separates_nonzero_phase s hn) hs.symm
  subst s
  exact hs.symm

end Mettapedia.GraphTheory.FourColor.JointDiamond
