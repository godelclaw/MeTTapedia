import Mettapedia.GraphTheory.FourColor.JointDiamondSeparation
import Mettapedia.GraphTheory.FourColor.PartialCubicDartCutBound

/-!
# Fourteen distinct vertices in the joint diamond

The possible pentagonal-end identification preserves the slot phase and
consumes four of the eight candidate ports. Twelve vertices remain distinct,
so the resulting four-edge cut contradicts cyclic five-edge connectivity.
This establishes injectivity without assuming that the four-face picture
is already an embedded open piece.
-/

namespace Mettapedia.GraphTheory.FourColor.JointDiamond

open _root_.SimpleGraph PartialCubicDartSeparation
open GoertzelV24CubicSmallBoundaryCycle GoertzelV24MinimalTriangleFree

noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (F : Realization diagram G)

abbrev Twelve := {v : Vertex // v ≠ 5 ∧ v ≠ 6}

def twelveEquiv : Fin 12 ≃ Twelve where
  toFun i := ⟨⟨if i.val < 5 then i.val else i.val + 2, by split <;> omega⟩, by
    constructor <;> intro he <;> have hh := congrArg Fin.val he <;> dsimp at hh
    all_goals split at hh <;> omega⟩
  invFun v := ⟨if v.1.val < 5 then v.1.val else v.1.val - 2, by
    have h5 : v.1.val ≠ 5 := fun he => v.2.1 (Fin.ext he)
    have h6 : v.1.val ≠ 6 := fun he => v.2.2 (Fin.ext he)
    split <;> omega⟩
  left_inv i := by apply Fin.ext; dsimp; split <;> (try split) <;> omega
  right_inv v := by
    apply Subtype.ext; apply Fin.ext
    have h5 : v.1.val ≠ 5 := fun he => v.2.1 (Fin.ext he)
    have h6 : v.1.val ≠ 6 := fun he => v.2.2 (Fin.ext he)
    dsimp; split <;> (try split) <;> omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem twelve_injective (ht : Realization.TriangleFree (G := G))
    (hf : Realization.FourCycleFree (G := G)) :
    Function.Injective (fun v : Twelve => F.vertex v.1) := by
  intro u v he
  apply Subtype.ext
  by_contra hn
  have hex : ¬ exceptional u.1 v.1 := by
    have hall : ∀ a b : Vertex, a ≠ 5 → a ≠ 6 → b ≠ 5 → b ≠ 6 →
        ¬ exceptional a b := by decide
    exact hall u.1 v.1 u.2.1 u.2.2 v.2.1 v.2.2
  exact ne_nonexceptional F ht hf hn hex he

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem twelve_le_image (ht : Realization.TriangleFree (G := G))
    (hf : Realization.FourCycleFree (G := G)) :
    12 ≤ Fintype.card {v // F.imageSide v} := by
  classical
  have hi : Function.Injective (fun v : Twelve =>
      (⟨F.vertex v.1, ⟨v.1, rfl⟩⟩ : {v // F.imageSide v})) := by
    intro u v he
    exact twelve_injective F ht hf (congrArg Subtype.val he)
  have hh := Fintype.card_le_of_injective _ hi
  have hn : Fintype.card Twelve = 12 := (Fintype.card_congr twelveEquiv).symm
  rwa [hn] at hh

def remaining (p : Realization.Unpaired (P := diagram)) : Prop :=
  p.1 = (0, 1) ∨ p.1 = (1, 2) ∨ p.1 = (8, 1) ∨ p.1 = (9, 2)

instance (p : Realization.Unpaired (P := diagram)) : Decidable (remaining p) :=
  inferInstanceAs (Decidable (p.1 = (0, 1) ∨ p.1 = (1, 2) ∨ p.1 = (8, 1) ∨ p.1 = (9, 2)))

def remainingSlot : Fin 4 → Slot
  | 0 => (0, 1)
  | 1 => (1, 2)
  | 2 => (8, 1)
  | 3 => (9, 2)

def remainingEquiv : Fin 4 ≃ {p // remaining p} :=
  Equiv.ofBijective (fun i => ⟨⟨remainingSlot i, by revert i; decide⟩, by
    fin_cases i <;> simp [remaining, remainingSlot]⟩) ⟨by
      intro a b he
      have hh := congrArg (fun p : {p // remaining p} => p.1.1) he
      have hi : Function.Injective remainingSlot := by decide
      exact hi hh, by
      rintro ⟨p, hp⟩
      rcases hp with hp | hp | hp | hp
      · exact ⟨0, Subtype.ext (Subtype.ext hp.symm)⟩
      · exact ⟨1, Subtype.ext (Subtype.ext hp.symm)⟩
      · exact ⟨2, Subtype.ext (Subtype.ext hp.symm)⟩
      · exact ⟨3, Subtype.ext (Subtype.ext hp.symm)⟩⟩

theorem remaining_card [Fintype {p // remaining p}] :
    Fintype.card {p // remaining p} = 4 := (Fintype.card_congr remainingEquiv).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem rotate_eq_of_eq {u v : Vertex} {s t : Fin 3}
    (he : F.dart (u, s) = F.dart (v, t)) :
    F.dart (u, s + 1) = F.dart (v, t + 1) :=
  (F.rotate_eq _).trans ((congrArg F.rotation he).trans (F.rotate_eq _).symm)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exceptional_internal (he : F.dart (2, 0) = F.dart (6, 0))
    (p : Realization.Unpaired (P := diagram)) (hp : ¬ remaining p) :
    F.imageSide (F.dart p.1).snd := by
  have h35 : F.dart (3, 0) = F.dart (5, 0) :=
    (F.flip_eq (2, 0) (3, 0) (by decide)).symm.trans
      ((congrArg SimpleGraph.Dart.symm he).trans (F.flip_eq (6, 0) (5, 0) (by decide)))
  have h21 := rotate_eq_of_eq F he
  have h22 := rotate_eq_of_eq F h21
  have h31 := rotate_eq_of_eq F h35
  have h32 := rotate_eq_of_eq F h31
  simp only [Fin.reduceAdd] at h21 h22 h31 h32
  have hc : p.1 = (2, 1) ∨ p.1 = (3, 2) ∨ p.1 = (5, 1) ∨ p.1 = (6, 2) := by
    have hall : ∀ d : Slot, flip d = none →
        ¬ (d = (0, 1) ∨ d = (1, 2) ∨ d = (8, 1) ∨ d = (9, 2)) →
        d = (2, 1) ∨ d = (3, 2) ∨ d = (5, 1) ∨ d = (6, 2) := by decide
    exact hall p.1 p.2 hp
  rcases hc with hp | hp | hp | hp
  · rw [hp, h21, F.snd_of_flip (d := (6, 1)) (e := (7, 0)) (by decide)]
    exact ⟨7, rfl⟩
  · rw [hp, h32, F.snd_of_flip (d := (5, 2)) (e := (10, 2)) (by decide)]
    exact ⟨10, rfl⟩
  · rw [hp, ← h31, F.snd_of_flip (d := (3, 1)) (e := (11, 0)) (by decide)]
    exact ⟨11, rfl⟩
  · rw [hp, ← h22, F.snd_of_flip (d := (2, 2)) (e := (4, 2)) (by decide)]
    exact ⟨4, rfl⟩

theorem exceptional_ne (ht : Realization.TriangleFree (G := G))
    (hf : Realization.FourCycleFree (G := G)) (hcubic : G.IsRegularOfDegree 3)
    (hcyclic : CyclicallyFiveEdgeConnected G) (hsize : 17 ≤ Fintype.card V) :
    F.vertex 2 ≠ F.vertex 6 := by
  classical
  intro he
  have hports := F.crossing_card_le_of_internal remaining
    (exceptional_internal F (exceptional_dart_eq F ht hf he))
  rw [remaining_card] at hports
  have hlo := twelve_le_image F ht hf
  have hhi := F.card_imageSide_le
  have hpartition := Fintype.card_subtype_compl F.imageSide
  have hfourteen : Fintype.card Vertex = 14 := rfl
  rw [hfourteen] at hhi
  have hcycle := CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two
    hcubic F.imageSide (Fintype.card_pos_iff.mp (by omega)) (by omega)
  have hfive := CyclicFiveBoundary.five_le_crossing_card hcubic hcyclic F.imageSide
    hcycle (by omega)
  omega

/-- Both exceptional pairs are separated by transporting the same dart
equality; the cut argument supplies the extra terminal fact. -/
def fullTerminal (a b : Slot) : Bool := terminal a b ||
  decide ((a.1 = 2 ∧ b.1 = 6) ∨ (a.1 = 6 ∧ b.1 = 2))

theorem separates_all : ∀ u v : Vertex, u ≠ v → ∀ s : Fin 3,
    diagram.separatesWith fullTerminal 6 (u, 0) (v, s) = true := by decide

theorem vertex_injective (ht : Realization.TriangleFree (G := G))
    (hf : Realization.FourCycleFree (G := G)) (hcubic : G.IsRegularOfDegree 3)
    (hcyclic : CyclicallyFiveEdgeConnected G) (hsize : 17 ≤ Fintype.card V) :
    Function.Injective F.vertex := by
  have hterminal (a b : Slot) (h : fullTerminal a b = true) : F.dart a ≠ F.dart b := by
    simp only [fullTerminal, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact terminal_sound F ht hf a b h
    · intro he
      have hv : F.vertex a.1 = F.vertex b.1 := by
        simpa only [F.fst] using congrArg (fun d : G.Dart => d.fst) he
      have hh := exceptional_ne F ht hf hcubic hcyclic hsize
      rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [ha, hb] at hv; exact hh hv
      · rw [ha, hb] at hv; exact hh hv.symm
  intro u v he
  by_contra hn
  obtain ⟨s, hs⟩ := F.slots_surjective v (F.dart (u, 0)) ((F.fst _).trans he)
  exact F.separatesWith_sound fullTerminal hterminal (separates_all u v hn s) hs.symm

end
end Mettapedia.GraphTheory.FourColor.JointDiamond
