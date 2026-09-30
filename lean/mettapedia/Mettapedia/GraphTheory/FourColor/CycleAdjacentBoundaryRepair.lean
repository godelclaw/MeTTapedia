import Mettapedia.GraphTheory.FourColor.CycleSeamTransfer

/-!
# Repair a constant cycle boundary at two adjacent ports

Renaming the two internal colours fixes the constant boundary and aligns the
shared edge with the intended new boundary colour. Replacing that edge by the
old boundary colour changes precisely its two adjacent ports. The resulting
word is nonconstant and has a genuine cycle-colouring witness.
-/

namespace Mettapedia.GraphTheory.FourColor.CycleAdjacentBoundaryRepair

open GoertzelV24OpenTangleComposition

variable {k : ℕ} [NeZero k]

def word (i : Fin k) (old new : Color) (j : Fin k) : Color :=
  if j = i ∨ j = i + 1 then new else old

private theorem offset_ne (i : Fin k) (r : ℕ)
    (hr : 0 < r) (hrk : r < k) : i + Fin.ofNat k r ≠ i := by
  intro h
  have he : Fin.ofNat k r = 0 := add_left_cancel (h.trans (add_zero i).symm)
  have hv := congrArg Fin.val he
  have hr0 : r = 0 := by
    simpa only [Fin.val_ofNat, Fin.val_zero, Nat.mod_eq_of_lt hrk] using hv
  omega

private theorem avoid_constant {a : Fin k → Color} (ha : CycleCap.Valid k a)
    {c : Color} (hc : CycleCap.spokes k a = fun _ => c) (j : Fin k) : a j ≠ c := by
  have hsum : a j + a (j+1) = c := congrFun hc j
  rw [← hsum]
  exact (add_ne_left_of_ne_zero (ha.1 (j+1))).symm

/-- Align the shared cycle edge by a colour permutation which fixes the
boundary colour and zero. -/
private theorem align {a : Fin k → Color} (ha : CycleCap.Valid k a)
    {c d : Color} (hc : CycleCap.spokes k a = fun _ => c)
    (hc0 : c ≠ 0) (hd0 : d ≠ 0) (hdc : d ≠ c) (i : Fin k) :
    ∃ b : Fin k → Color, CycleCap.Valid k b ∧
      CycleCap.spokes k b = (fun _ => c) ∧ b (i+1) = d ∧ ∀ j, b j ≠ c := by
  let p : Color ≃ Color := Equiv.swap (a (i+1)) d
  have hp0 : p 0 = 0 := Equiv.swap_apply_of_ne_of_ne
    (Ne.symm (ha.1 (i+1))) (Ne.symm hd0)
  have hpc : p c = c := Equiv.swap_apply_of_ne_of_ne
    (Ne.symm (avoid_constant ha hc (i+1))) (Ne.symm hdc)
  let b := p ∘ a
  have hb0 (j) : b j ≠ 0 := by
    intro h
    exact ha.1 j (p.injective (h.trans hp0.symm))
  have hbc (j) : b j ≠ c := by
    intro h
    exact avoid_constant ha hc j (p.injective (h.trans hpc.symm))
  have hbn (j) : b j ≠ b (j+1) := p.injective.ne (ha.2 j)
  refine ⟨b, ⟨hb0,hbn⟩, ?_, ?_, hbc⟩
  · funext j
    exact (ZigzagRing.third_eq_add (hb0 j) (hb0 (j+1)) hc0
      (hbn j) (hbc j) (hbc (j+1))).symm
  · exact Equiv.swap_apply_left _ _

/-- A two-port change has actual interior witnesses; it does not merely
preserve the zero-sum boundary equation. -/
theorem accepts_adjacent (hk : 3 ≤ k) {c d : Color}
    (hc0 : c ≠ 0) (hd0 : d ≠ 0) (hdc : d ≠ c)
    (h : (CycleCap.cap k (by omega)).AcceptsBoundaryWords Empty.elim (fun _ => c))
    (i : Fin k) :
    (CycleCap.cap k (by omega)).AcceptsBoundaryWords Empty.elim (word i c d) := by
  classical
  obtain ⟨seam,hc⟩ := (CycleSeamTransfer.accepts_iff_marked (by omega) _).mp h
  obtain ⟨a,ha,hs,_⟩ := (CycleSeamTransfer.marked_iff _ _ _).mp hc
  obtain ⟨b,hb,hbs,hbi,hbc⟩ := align ha hs hc0 hd0 hdc i
  let changed := Function.update b (i+1) c
  have hi : i+1 ≠ i := offset_ne i 1 (by omega) (by omega)
  have hnext : i+1+1 ≠ i+1 := offset_ne (i+1) 1 (by omega) (by omega)
  have hspokes : CycleCap.spokes k changed = word i c d := by
    funext j
    have hj : j+1 = i+1 ↔ j=i := add_right_cancel_iff
    have hs : b j + b (j+1) = c := congrFun hbs j
    by_cases he : j=i
    · subst j
      simp only [CycleCap.spokes, changed, Function.update_self,
        Function.update_of_ne hi.symm, word, true_or, ↓reduceIte]
      rw [hbi] at hs
      calc
        b i + c = b i + (b i + d) := congrArg _ hs.symm
        _ = d := by rw [← add_assoc, color_add_self, zero_add]
    · by_cases he' : j=i+1
      · subst j
        simp only [CycleCap.spokes, changed, Function.update_self,
          Function.update_of_ne hnext, word, or_true, ↓reduceIte]
        rw [hbi] at hs
        calc
          c + b (i+1+1) = (d+b (i+1+1))+b (i+1+1) :=
            congrArg (fun z : Color => z + b (i+1+1)) hs.symm
          _ = d := by rw [add_assoc, color_add_self, add_zero]
      · have hn : j+1 ≠ i+1 := fun h => he (hj.mp h)
        simp only [CycleCap.spokes, changed, Function.update_of_ne he',
          Function.update_of_ne hn, word, he, he', false_or, ↓reduceIte]
        exact hs
  have hvalid : CycleCap.Valid k changed := by
    refine ⟨?_, ?_⟩
    · intro j
      by_cases hj : j=i+1
      · simpa only [changed, Function.update_apply, hj, ↓reduceIte] using hc0
      · simpa only [changed, Function.update_of_ne hj] using hb.1 j
    · intro j
      by_cases hj : j=i+1
      · subst j
        simpa only [changed, Function.update_self, Function.update_of_ne hnext] using (hbc (i+1+1)).symm
      · by_cases hn : j+1=i+1
        · have he : j=i := add_right_cancel hn
          subst j
          simpa only [changed, Function.update_self, Function.update_of_ne hi.symm] using hbc i
        · simpa only [changed, Function.update_of_ne hj, Function.update_of_ne hn] using hb.2 j
  simpa only [hspokes] using CycleCap.accepts_spokes k (by omega) hvalid

theorem word_nonconstant (hk : 3 ≤ k) (i : Fin k) {c d : Color} (hdc : d ≠ c) :
    ¬ ∃ a, ∀ j, word i c d j = a := by
  rintro ⟨a,ha⟩
  have hi : word i c d i = d := by simp [word]
  have hfar : word i c d (i+2) = c := by
    have h₁ : i+2 ≠ i := offset_ne i 2 (by omega) (by omega)
    have h₂ : i+2 ≠ i+1 := by
      have hh : i+1+1 ≠ i+1 := offset_ne (i+1) 1 (by omega) (by omega)
      have htwo : (1 : Fin k)+1 = 2 := by
        apply Fin.ext
        simp [Fin.val_add,
          Nat.mod_eq_of_lt (show 1 < k by omega),
          Nat.mod_eq_of_lt (show 2 < k by omega)]
      simpa only [add_assoc, htwo] using hh
    simp [word, h₁, h₂]
  exact hdc (hi.symm.trans ((ha i).trans ((ha (i+2)).symm.trans hfar)))

end Mettapedia.GraphTheory.FourColor.CycleAdjacentBoundaryRepair
