import Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation
import Mettapedia.GraphTheory.FourColor.PentagonalCoronaImmersion

/-!
# The mixed pentagon/hexagon diamond

The central pentagon and consecutive neighbours of lengths five, six, five
determine thirteen vertex positions and seven unpaired slots. One four-edge
path supplies the extra terminal separation needed by joint dart transport.
No condition on the other two neighbouring face lengths is used.
-/

namespace Mettapedia.GraphTheory.FourColor.MixedDiamond

open PartialCubicDartSeparation

abbrev Vertex := Fin 13
abbrev Slot := Vertex × Fin 3

def flat (d : Slot) : Fin 39 := ⟨3 * d.1.val + d.2.val, by omega⟩
def unflat (i : Fin 39) : Slot := (⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩)

def flipCodes : String := "`@E@CH]FK@IN@LQZOT@RWfU@^PeaGYdA\\g@_[Vb"

def flip (d : Slot) : Option Slot :=
  let n := (flipCodes.toUTF8[flat d |>.val]?.getD 64).toNat
  if n = 64 then none else some (unflat ⟨(n - 65) % 39, Nat.mod_lt _ (by decide)⟩)

def rotate (d : Slot) : Slot :=
  (d.1, if d.1.val < 8 ∧ (d.1.val + 7) % 11 % 2 = 0 then d.2 - 1 else d.2 + 1)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def diagram : Diagram Vertex where
  rotate := rotate
  flip := flip
  flip_reverse := by decide

def embed (v : Vertex) : PentagonalCoronaSeparation.Vertex :=
  if h : v.val < 8 then .inl ⟨(v.val + 7) % 11, Nat.mod_lt _ (by decide)⟩
  else .inr ⟨v.val - 8, by omega⟩

def embedSlot (d : Slot) : PentagonalCoronaSeparation.Slot := (embed d.1, d.2)

theorem embed_injective : Function.Injective embed := by decide

theorem embed_rotate (d : Slot) :
    embedSlot (rotate d) = PentagonalCoronaSeparation.rotate (embedSlot d) := by
  revert d
  decide

/-- The extra endpoint test has a separate geometric proof. -/
def terminal (a b : Slot) : Bool := diagram.apart a b ||
  decide ((a.1 = 0 ∧ b.1 = 7) ∨ (a.1 = 7 ∧ b.1 = 0))

/-- All 468 ordered vertex/phase cases use the same joint operation law. -/
theorem separates_all : ∀ u v : Vertex, u ≠ v → ∀ s : Fin 3,
    diagram.separatesWith terminal 6 (u, 0) (v, s) = true := by decide

variable {V : Type*} {G : SimpleGraph V} (F : Realization diagram G)

theorem first_last_ne (hf : Realization.FourCycleFree (G := G)) :
    F.vertex 0 ≠ F.vertex 7 :=
  F.ne_of_path_four hf (b := 10) (c := 11) (d := 12) (by decide) (by decide)
    (diagram.pathCheck_sound (by decide)) (diagram.pathCheck_sound (by decide))
    (diagram.pathCheck_sound (by decide)) (diagram.pathCheck_sound (by decide))

theorem terminal_sound (ht : Realization.TriangleFree (G := G))
    (hf : Realization.FourCycleFree (G := G)) (a b : Slot)
    (h : terminal a b = true) : F.dart a ≠ F.dart b := by
  simp only [terminal, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact F.apart_sound ht h
  · intro he
    have hv : F.vertex a.1 = F.vertex b.1 := by
      simpa only [F.fst] using congrArg (fun d : G.Dart => d.fst) he
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb] at hv
      exact first_last_ne F hf hv
    · rw [ha, hb] at hv
      exact first_last_ne F hf hv.symm

/-- Exact geometric interpretation of the finite joint separation check. -/
theorem vertex_injective (ht : Realization.TriangleFree (G := G))
    (hf : Realization.FourCycleFree (G := G)) : Function.Injective F.vertex := by
  intro u v he
  by_contra hn
  obtain ⟨s, hs⟩ := F.slots_surjective v (F.dart (u, 0)) ((F.fst _).trans he)
  exact F.separatesWith_sound terminal (terminal_sound F ht hf)
    (separates_all u v hn s) hs.symm

end Mettapedia.GraphTheory.FourColor.MixedDiamond
