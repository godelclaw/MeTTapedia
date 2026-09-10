import Mettapedia.GraphTheory.FourColor.ColorAlgebra
import Mathlib.Data.Fin.VecNotation

/-!
# A fixed-exterior obstruction to disk-local joint exchange

This explicit dodecahedral edge presentation has two separated adjacent-pair
deletions. Both admit proper three-colourings with the same frozen exterior,
but no full colouring extends that exterior. Agreement on the common core
would glue to such a full colouring, so no boundary-fixed joint exchange can
reach agreement. A full colouring exists after changing one exterior edge.

Colours are `Fin 3`; none denotes the zero Klein colour. The combinatorial
disk geometry is separately checked by `v24_disk_exchange_gate.py`. This file
certifies the colouring obstruction, not a geometric realization theorem.
It does not assert positivity at a boundary-unrestricted absolute minimum.
-/

namespace Mettapedia.GraphTheory.FourColor.DiskExchangeBoundaryControl

abbrev Vertex := Fin 20
abbrev Edge := Fin 30
abbrev Coloring := Edge → Fin 3

def taitColor : Fin 3 → Color := ![red, blue, purple]

theorem color_encoding : Function.Injective taitColor ∧ ∀ i, taitColor i ≠ 0 := by
  decide +kernel

def ends : Edge → Vertex × Vertex := ![
  (0,1), (0,2), (0,5), (1,4), (1,6), (2,3), (2,8), (3,4), (3,10), (4,12),
  (5,7), (5,9), (6,7), (6,13), (7,16), (8,9), (8,11), (9,15), (10,11), (10,14),
  (11,17), (12,13), (12,14), (13,18), (14,19), (15,16), (15,17), (16,18), (17,19), (18,19)]

def star : Vertex → Fin 3 → Edge := ![
  ![0,1,2], ![0,3,4], ![1,5,6], ![5,7,8], ![3,7,9],
  ![2,10,11], ![4,12,13], ![10,12,14], ![6,15,16], ![11,15,17],
  ![8,18,19], ![16,18,20], ![9,21,22], ![13,21,23], ![19,22,24],
  ![17,25,26], ![14,25,27], ![20,26,28], ![23,27,29], ![24,28,29]]

/-- The stars enumerate exactly the incident edges, without repetitions. -/
theorem presentation_valid :
    Function.Injective ends ∧ (∀ e, (ends e).1 ≠ (ends e).2) ∧
    (∀ v, Function.Injective (star v)) ∧
    (∀ v e, (∃ i, star v i = e) ↔ (ends e).1 = v ∨ (ends e).2 = v) := by
  decide +kernel

def source : Finset Vertex := {0, 1}
def target : Finset Vertex := {17, 19}

def retained (deleted : Finset Vertex) (e : Edge) : Prop :=
  (ends e).1 ∉ deleted ∧ (ends e).2 ∉ deleted

instance (deleted : Finset Vertex) (e : Edge) : Decidable (retained deleted e) :=
  inferInstanceAs (Decidable (_ ∧ _))

def ProperOn (deleted : Finset Vertex) (c : Coloring) : Prop :=
  ∀ v i j, i ≠ j → retained deleted (star v i) → retained deleted (star v j) →
    c (star v i) ≠ c (star v j)

def frozen : Fin 9 → Edge := ![10, 11, 12, 13, 14, 17, 23, 25, 27]
def outsideColor : Fin 9 → Fin 3 := ![2, 0, 1, 0, 0, 2, 1, 1, 2]
def Fixed (c : Coloring) : Prop := ∀ i, c (frozen i) = outsideColor i

def left : Coloring := ![
  0,0,0,0,0,0,2,1,2,0,2,0,1,0,0,1,0,2,1,0,2,2,1,1,2,1,0,2,1,0]
def right : Coloring := ![
  0,2,1,1,2,1,0,2,0,0,2,0,1,0,0,1,2,2,1,2,0,2,1,1,0,1,0,2,0,0]

theorem deletion_witnesses :
    ProperOn source left ∧ ProperOn target right ∧ Fixed left ∧ Fixed right := by
  unfold ProperOn Fixed
  decide +kernel

private theorem force_zero : ∀ x : Fin 3, x ≠ 1 → x ≠ 2 → x = 0 := by decide
private theorem force_one : ∀ x : Fin 3, x ≠ 0 → x ≠ 2 → x = 1 := by decide
private theorem force_two : ∀ x : Fin 3, x ≠ 0 → x ≠ 1 → x = 2 := by decide

/-- The full star constraints contradict the frozen exterior. -/
theorem no_full_extension (c : Coloring) (hp : ProperOn ∅ c) (hf : Fixed c) : False := by
  have h (v : Vertex) :
      c (star v 0) ≠ c (star v 1) ∧ c (star v 0) ≠ c (star v 2) ∧
      c (star v 1) ≠ c (star v 2) := by
    exact ⟨hp v 0 1 (by decide) (by simp [retained]) (by simp [retained]),
      hp v 0 2 (by decide) (by simp [retained]) (by simp [retained]),
      hp v 1 2 (by decide) (by simp [retained]) (by simp [retained])⟩
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  have h8 := h 8; have h9 := h 9; have h10 := h 10; have h11 := h 11
  have h12 := h 12; have h13 := h 13; have h14 := h 14; have h15 := h 15
  have h16 := h 16; have h17 := h 17; have h18 := h 18; have h19 := h 19
  have f0 := hf 0; have f1 := hf 1; have f2 := hf 2; have f3 := hf 3
  have f4 := hf 4; have f5 := hf 5; have f6 := hf 6; have f7 := hf 7; have f8 := hf 8
  change c 0 ≠ c 1 ∧ c 0 ≠ c 2 ∧ c 1 ≠ c 2 at h0
  change c 0 ≠ c 3 ∧ c 0 ≠ c 4 ∧ c 3 ≠ c 4 at h1
  change c 1 ≠ c 5 ∧ c 1 ≠ c 6 ∧ c 5 ≠ c 6 at h2
  change c 5 ≠ c 7 ∧ c 5 ≠ c 8 ∧ c 7 ≠ c 8 at h3
  change c 3 ≠ c 7 ∧ c 3 ≠ c 9 ∧ c 7 ≠ c 9 at h4
  change c 2 ≠ c 10 ∧ c 2 ≠ c 11 ∧ c 10 ≠ c 11 at h5
  change c 4 ≠ c 12 ∧ c 4 ≠ c 13 ∧ c 12 ≠ c 13 at h6
  change c 10 ≠ c 12 ∧ c 10 ≠ c 14 ∧ c 12 ≠ c 14 at h7
  change c 6 ≠ c 15 ∧ c 6 ≠ c 16 ∧ c 15 ≠ c 16 at h8
  change c 11 ≠ c 15 ∧ c 11 ≠ c 17 ∧ c 15 ≠ c 17 at h9
  change c 8 ≠ c 18 ∧ c 8 ≠ c 19 ∧ c 18 ≠ c 19 at h10
  change c 16 ≠ c 18 ∧ c 16 ≠ c 20 ∧ c 18 ≠ c 20 at h11
  change c 9 ≠ c 21 ∧ c 9 ≠ c 22 ∧ c 21 ≠ c 22 at h12
  change c 13 ≠ c 21 ∧ c 13 ≠ c 23 ∧ c 21 ≠ c 23 at h13
  change c 19 ≠ c 22 ∧ c 19 ≠ c 24 ∧ c 22 ≠ c 24 at h14
  change c 17 ≠ c 25 ∧ c 17 ≠ c 26 ∧ c 25 ≠ c 26 at h15
  change c 14 ≠ c 25 ∧ c 14 ≠ c 27 ∧ c 25 ≠ c 27 at h16
  change c 20 ≠ c 26 ∧ c 20 ≠ c 28 ∧ c 26 ≠ c 28 at h17
  change c 23 ≠ c 27 ∧ c 23 ≠ c 29 ∧ c 27 ≠ c 29 at h18
  change c 24 ≠ c 28 ∧ c 24 ≠ c 29 ∧ c 28 ≠ c 29 at h19
  change c 10 = 2 at f0
  change c 11 = 0 at f1
  change c 12 = 1 at f2
  change c 13 = 0 at f3
  change c 14 = 0 at f4
  change c 17 = 2 at f5
  change c 23 = 1 at f6
  change c 25 = 1 at f7
  change c 27 = 2 at f8
  -- Propagate the forced third colour from the exterior to vertex 17.
  have e2 : c 2 = 1 := force_one _ (by simpa only [f1] using h5.2.1)
    (by simpa only [f0] using h5.1)
  have e4 : c 4 = 2 := force_two _ (by simpa only [f3] using h6.2.1)
    (by simpa only [f2] using h6.1)
  have e15 : c 15 = 1 := force_one _ (by simpa only [f1] using h9.1.symm)
    (by simpa only [f5] using h9.2.2)
  have e21 : c 21 = 2 := force_two _ (by simpa only [f3] using h13.1.symm)
    (by simpa only [f6] using h13.2.2)
  have e26 : c 26 = 0 := force_zero _ (by simpa only [f7] using h15.2.2.symm)
    (by simpa only [f5] using h15.2.1.symm)
  have e0 : c 0 = 0 := force_zero _ (by simpa only [e2] using h0.2.1)
    (by simpa only [e4] using h1.2.1)
  have e1 : c 1 = 2 := force_two _ (by simpa only [e0] using h0.1.symm)
    (by simpa only [e2] using h0.2.2)
  have e3 : c 3 = 1 := force_one _ (by simpa only [e0] using h1.1.symm)
    (by simpa only [e4] using h1.2.2)
  have e6 : c 6 = 0 := force_zero _ (by simpa only [e15] using h8.1)
    (by simpa only [e1] using h2.2.1.symm)
  have e5 : c 5 = 1 := force_one _ (by simpa only [e6] using h2.2.2)
    (by simpa only [e1] using h2.1.symm)
  have e16 : c 16 = 2 := force_two _ (by simpa only [e6] using h8.2.1.symm)
    (by simpa only [e15] using h8.2.2.symm)
  have e9 : c 9 = 0 := force_zero _ (by simpa only [e3] using h4.2.1.symm)
    (by simpa only [e21] using h12.1)
  have e7 : c 7 = 2 := force_two _ (by simpa only [e9] using h4.2.2)
    (by simpa only [e5] using h3.1.symm)
  have e8 : c 8 = 0 := force_zero _ (by simpa only [e5] using h3.2.1.symm)
    (by simpa only [e7] using h3.2.2.symm)
  have e18 : c 18 = 1 := force_one _ (by simpa only [e8] using h10.1.symm)
    (by simpa only [e16] using h11.1.symm)
  have e20 : c 20 = 0 := force_zero _ (by simpa only [e18] using h11.2.2.symm)
    (by simpa only [e16] using h11.2.1.symm)
  exact h17.1 (e20.trans e26.symm)

def CommonAgreement (c d : Coloring) : Prop :=
  ∀ e, retained source e → retained target e → c e = d e

/-- Every star is wholly present in at least one deletion. -/
theorem stars_covered : ∀ v,
    (∀ i, retained source (star v i)) ∨ (∀ i, retained target (star v i)) := by
  decide +kernel

def glue (c d : Coloring) : Coloring := fun e => if retained source e then c e else d e

theorem glue_proper {c d : Coloring} (hc : ProperOn source c) (hd : ProperOn target d)
    (ha : CommonAgreement c d) : ProperOn ∅ (glue c d) := by
  intro v i j hij _ _
  rcases stars_covered v with hl | hr
  · simpa only [glue, if_pos (hl i), if_pos (hl j)] using hc v i j hij (hl i) (hl j)
  · have eq (k : Fin 3) : glue c d (star v k) = d (star v k) := by
      by_cases hs : retained source (star v k)
      · simpa only [glue, if_pos hs] using ha _ hs (hr k)
      · simp only [glue, if_neg hs]
    rw [eq, eq]
    exact hd v i j hij (hr i) (hr j)

theorem frozen_retained : ∀ i, retained source (frozen i) ∧ retained target (frozen i) := by
  decide +kernel

theorem no_fixed_agreement {c d : Coloring} (hc : ProperOn source c)
    (hd : ProperOn target d) (hf : Fixed c) : ¬ CommonAgreement c d := by
  intro ha
  apply no_full_extension (glue c d) (glue_proper hc hd ha)
  intro i
  simpa only [glue, if_pos (frozen_retained i).1] using hf i

def disagreement (c d : Coloring) : Finset Edge :=
  Finset.univ.filter fun e => retained source e ∧ retained target e ∧ c e ≠ d e

theorem disagreement_pos {c d : Coloring} (hc : ProperOn source c)
    (hd : ProperOn target d) (hf : Fixed c) : 0 < (disagreement c d).card := by
  by_contra h
  have hempty := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos h)
  apply no_fixed_agreement hc hd hf
  intro e hs ht
  by_contra hne
  have hm : e ∈ disagreement c d := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, ht, hne⟩
  rw [hempty] at hm
  exact Finset.notMem_empty e hm

/-- A genuinely positive minimum over all boundary-fixed recolourings of
both deletion graphs. No Kempe-orbit restriction is imposed. -/
theorem exists_frozen_positive_minimum : ∃ c d : Coloring,
    ProperOn source c ∧ ProperOn target d ∧ Fixed c ∧ Fixed d ∧
    0 < (disagreement c d).card ∧
    ∀ c' d' : Coloring, ProperOn source c' → ProperOn target d' → Fixed c' → Fixed d' →
      (disagreement c d).card ≤ (disagreement c' d').card := by
  classical
  let P (n : Nat) := ∃ c d : Coloring,
    ProperOn source c ∧ ProperOn target d ∧ Fixed c ∧ Fixed d ∧
    (disagreement c d).card = n
  have hp : ∃ n, P n := ⟨_, left, right, deletion_witnesses.1,
    deletion_witnesses.2.1, deletion_witnesses.2.2.1, deletion_witnesses.2.2.2, rfl⟩
  obtain ⟨c, d, hc, hd, fc, fd, hm⟩ := Nat.find_spec hp
  refine ⟨c, d, hc, hd, fc, fd, disagreement_pos hc hd fc, ?_⟩
  intro c' d' hc' hd' fc' fd'
  rw [hm]
  exact Nat.find_min' hp ⟨c', d', hc', hd', fc', fd', rfl⟩

/-- The rule "positive disagreement always has a strictly improving
boundary-fixed joint exchange" is false on this explicit presentation. -/
theorem no_universal_fixed_exchange : ¬ (∀ c d : Coloring,
    ProperOn source c → ProperOn target d → Fixed c → Fixed d →
    0 < (disagreement c d).card → ∃ c' d' : Coloring,
      ProperOn source c' ∧ ProperOn target d' ∧ Fixed c' ∧ Fixed d' ∧
      (disagreement c' d').card < (disagreement c d).card) := by
  intro improve
  obtain ⟨c, d, hc, hd, fc, fd, hpos, hmin⟩ := exists_frozen_positive_minimum
  obtain ⟨c', d', hc', hd', fc', fd', hlt⟩ := improve c d hc hd fc fd hpos
  exact (Nat.not_lt_of_ge (hmin c' d' hc' hd' fc' fd')) hlt

def escape : Coloring := ![
  1,2,0,0,2,0,1,2,1,1,2,1,1,0,0,0,2,2,0,2,1,2,0,1,1,1,0,2,2,0]

/-- The same graph is colourable: exactly one frozen edge changes. -/
theorem escape_changes_one : ProperOn ∅ escape ∧
    (∀ i, escape (frozen i) ≠ outsideColor i ↔ i = 1) := by
  unfold ProperOn
  decide +kernel

end Mettapedia.GraphTheory.FourColor.DiskExchangeBoundaryControl
