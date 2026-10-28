import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Truncating tool output

A coding agent cannot show the model every byte a tool prints. One design cuts
the middle out of a long output, keeping its first `h` and last `t` elements
around a marker; another keeps the whole output in a file beside the session
and shows a cut view with a hint to search the file.

Proved, for a middle cut:

* it fits its budget whenever the marker is bounded (`middleCut_length_le`),
  and it keeps the output's head and tail exactly (`middleCut_head`,
  `middleCut_tail`);
* it loses information: two outputs that differ only in the middle look the
  same (`middleCut_not_injective`). Keeping the whole output in a file loses
  nothing, and its view is the same cut (`spill_injective`, `spill_view`);
* with a marker that does not depend on what was omitted, cutting again with
  nested budgets is the same as cutting once with the smaller ones
  (`middleCut_compose`), and cutting again with the same budget changes
  nothing (`middleCut_idem`);
* with a marker that states how much was omitted and is shorter than what it
  replaces, cutting again with a smaller budget states less than was really
  omitted (`recut_underreports`). An output is therefore cut once, at the
  budget it is shown at, and never cut again.

Elements stand for characters, bytes or tokens alike.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.CodingAgent.Truncation

universe u

variable {α : Type u}

/-- The last `t` elements. -/
def lastN (t : ℕ) (s : List α) : List α := s.drop (s.length - t)

theorem length_lastN (t : ℕ) (s : List α) (h : t ≤ s.length) : (lastN t s).length = t := by
  simp [lastN]
  omega

theorem lastN_append_of_le (l r : List α) (t : ℕ) (hr : t ≤ r.length) :
    lastN t (l ++ r) = lastN t r := by
  unfold lastN
  have hsplit : (l ++ r).length - t = l.length + (r.length - t) := by
    simp only [List.length_append]
    omega
  rw [hsplit, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    Nat.add_sub_cancel_left]

theorem lastN_lastN (s : List α) (t t' : ℕ) (ht : t' ≤ t) (hs : t ≤ s.length) :
    lastN t' (lastN t s) = lastN t' s := by
  have hlen : (lastN t s).length = t := length_lastN t s hs
  unfold lastN at hlen ⊢
  rw [hlen, List.drop_drop]
  congr 1
  omega

/-- A middle cut: an output of at most `h + t` elements is kept whole;
otherwise its first `h` and last `t` elements are kept, with the marker for
the `s.length - h - t` omitted elements between them. -/
def middleCut (marker : ℕ → List α) (h t : ℕ) (s : List α) : List α :=
  if s.length ≤ h + t then s else s.take h ++ marker (s.length - h - t) ++ lastN t s

/-- How many elements a cut with this budget omits. -/
def omitted (h t : ℕ) (s : List α) : ℕ := s.length - h - t

/-! ## Budget, head and tail -/

theorem middleCut_length_le (marker : ℕ → List α) (M h t : ℕ) (hm : ∀ k, (marker k).length ≤ M)
    (s : List α) : (middleCut marker h t s).length ≤ h + t + M := by
  unfold middleCut
  split
  · omega
  · rename_i hlong
    have := hm (s.length - h - t)
    simp [lastN]
    omega

theorem middleCut_head (marker : ℕ → List α) (h t : ℕ) (s : List α) :
    (middleCut marker h t s).take h = s.take h := by
  unfold middleCut
  split
  · rfl
  · rename_i hlong
    rw [List.append_assoc, List.take_append_of_le_length (by simp; omega)]
    simp

theorem middleCut_tail (marker : ℕ → List α) (h t : ℕ) (s : List α) :
    lastN t (middleCut marker h t s) = lastN t s := by
  unfold middleCut
  split
  · rfl
  · rename_i hlong
    have ht : (lastN t s).length = t := length_lastN t s (by omega)
    rw [lastN_append_of_le _ _ t (by omega), lastN_lastN s t t le_rfl (by omega)]

/-! ## Lossy against lossless -/

/-- Two outputs that differ only in the middle are cut to the same view. -/
theorem middleCut_not_injective (marker : ℕ → List Bool) :
    middleCut marker 1 1 [true, true, true] = middleCut marker 1 1 [true, false, true] := by
  simp [middleCut, lastN]

/-- Keeping the whole output beside its view. -/
def spill (marker : ℕ → List α) (h t : ℕ) (s : List α) : List α × List α :=
  (middleCut marker h t s, s)

theorem spill_injective (marker : ℕ → List α) (h t : ℕ) :
    Function.Injective (spill marker h t) := by
  intro a b hab
  exact congrArg Prod.snd hab

theorem spill_view (marker : ℕ → List α) (h t : ℕ) (s : List α) :
    (spill marker h t s).1 = middleCut marker h t s := rfl

/-! ## Cutting again -/

/-- With a marker that does not depend on the omitted count, cutting with
nested budgets equals one cut with the smaller budget. -/
theorem middleCut_compose (m : List α) (h t h' t' : ℕ) (hh : h' ≤ h) (ht : t' ≤ t)
    (s : List α) :
    middleCut (fun _ => m) h' t' (middleCut (fun _ => m) h t s) =
      middleCut (fun _ => m) h' t' s := by
  by_cases hlong : s.length ≤ h + t
  · simp [middleCut, hlong]
  · have hlt : (lastN t s).length = t := length_lastN t s (by omega)
    have hcut : middleCut (fun _ => m) h t s = s.take h ++ m ++ lastN t s := by
      simp [middleCut, hlong]
    rw [hcut]
    have hlen : (s.take h ++ m ++ lastN t s).length = h + m.length + t := by
      simp [hlt]
      omega
    by_cases hfit : (s.take h ++ m ++ lastN t s).length ≤ h' + t'
    · -- Only possible with h' = h, t' = t and an empty marker: nothing changes.
      have hh' : h' = h := by omega
      have ht' : t' = t := by omega
      subst hh' ht'
      unfold middleCut
      rw [if_pos hfit, if_neg hlong]
    · have hlong' : ¬ s.length ≤ h' + t' := by omega
      simp only [middleCut, hfit, hlong', if_false]
      have hhead : (s.take h ++ m ++ lastN t s).take h' = s.take h' := by
        rw [List.append_assoc, List.take_append_of_le_length (by simp; omega)]
        simp [List.take_take, Nat.min_eq_left hh]
      have htail : lastN t' (s.take h ++ m ++ lastN t s) = lastN t' s := by
        rw [lastN_append_of_le _ _ t' (by omega), lastN_lastN s t t' ht (by omega)]
      rw [hhead, htail]

/-- Cutting again with the same budget changes nothing, for any marker no
longer than the budget's slack. -/
theorem middleCut_idem (m : List α) (h t : ℕ) (s : List α) :
    middleCut (fun _ => m) h t (middleCut (fun _ => m) h t s) = middleCut (fun _ => m) h t s :=
  middleCut_compose m h t h t le_rfl le_rfl s

/-- **Cutting again under-reports.** If the marker is shorter than what it
replaces, a second cut with a budget no larger than the first states fewer
omitted elements than the original output lost to that budget. -/
theorem recut_underreports (marker : ℕ → List α) (h t h' t' : ℕ) (hh : h' + t' ≤ h + t)
    (s : List α) (hlong : h + t < s.length)
    (hshort : ∀ k, 0 < k → (marker k).length < k) :
    omitted h' t' (middleCut marker h t s) < omitted h' t' s := by
  have hlt : (lastN t s).length = t := length_lastN t s (by omega)
  have hm := hshort (s.length - h - t) (by omega)
  unfold omitted middleCut
  rw [if_neg (by omega)]
  simp [hlt]
  omega

end Mettapedia.CognitiveArchitecture.Agent.CodingAgent.Truncation
