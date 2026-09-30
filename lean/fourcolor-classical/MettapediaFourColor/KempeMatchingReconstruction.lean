import MettapediaFourColor.KempeMatchingChromogram
import Mathlib.Data.List.Forall2

/-!
# Reconstructing component selections from chromogram answers

Every answer to the translated chromogram at any boundary width is a simultaneous switch
of whole components of the original matching. No new matching is chosen for
the answer. This is the reconstruction direction needed to transport a
physical exterior support into the reference repair semantics.
-/

namespace FourColor.KempeMatchingChromogram

open Color

variable {n : ℕ}

theorem word_of_colours (mate : (Fin n) → (Fin n)) (c : (Fin n) → Color)
    (hzero : ∀ i, c i ≠ 0) (hfixed : ∀ i, mate i = i ↔ c i = .c1) :
    word mate (fun i => decide (c i = .c3)) = c := by
  funext i
  have hz := hzero i
  have hf := hfixed i
  cases hc : c i <;> simp_all [word]

/-- A common noncrossing matching supplies a chromogram and reconstructs
every one of its answers by switching a union of that same matching's chords. -/
theorem reconstruct (mate : (Fin n) → (Fin n)) (c : (Fin n) → Color)
    (hinv : ∀ i, mate (mate i) = i) (hplanar : Noncrossing mate)
    (hzero : ∀ i, c i ≠ 0) (hfixed : ∀ i, mate i = i ↔ c i = .c1) :
    matchg [] (List.ofFn c) (gram mate c) ∧
      ∀ et', matchg [] et' (gram mate c) →
        ∃ selected : Finset (Fin n),
          (∀ i, i ∈ selected ↔ mate i ∈ selected) ∧
          List.ofFn (fun i => if i ∈ selected then EdgePerm.e132 (c i) else c i) = et' := by
  have hw := word_of_colours mate c hzero hfixed
  have hm : matchg [] (List.ofFn c) (gram mate c) := by
    simpa only [hw] using
      (translation mate hinv hplanar (fun i => decide (c i = .c3))).1
  refine ⟨hm, ?_⟩
  intro et' hm'
  have hlen : et'.length = n := by
    simpa [gram] using (matchg_length et' [] (gram mate c) hm').symm
  let c' : (Fin n) → Color := fun i => et'[i.val]'(by omega)
  have hc' : List.ofFn c' = et' := by
    apply List.ext_getElem
    · simpa using hlen.symm
    · intro i hi hi'
      simp only [List.getElem_ofFn]
      rfl
  let bits : (Fin n) → Bool := fun i => decide (c i ≠ c' i)
  have hd : difference (List.ofFn c) et' = List.ofFn bits := by
    rw [← hc']
    apply List.ext_getElem
    · simp [difference]
    · intro i hi hi'
      simp [difference, bits]
  have hp : paired [] (List.ofFn bits) (layout mate) := by
    simpa only [List.zipWith_nil_left, hd, shape_gram] using
      difference_paired (gram mate c) (List.ofFn c) et' [] [] hm hm'
  have hb := (translation mate hinv hplanar bits).2 hp
  let selected : Finset (Fin n) := Finset.univ.filter fun i => bits i
  refine ⟨selected, ?_, ?_⟩
  · intro i
    simpa [selected] using congrArg (· = true) (hb i)
  · rw [← hc']
    apply congrArg List.ofFn
    funext i
    have hr := matches_related (gram mate c) (List.ofFn c) (List.ofFn c') [] []
      hm (by simpa only [hc'] using hm')
    have hi : c' i = c i ∨ c' i = EdgePerm.e132 (c i) := by
      simpa only [List.get_eq_getElem, List.getElem_ofFn] using
        hr.get (i := i.val) (by simpa only [List.length_ofFn] using i.isLt)
          (by simpa only [List.length_ofFn] using i.isLt)
    by_cases he : c i = c' i
    · simp [selected, bits, he]
    · have hs : i ∈ selected := by simp [selected, bits, he]
      rw [ite_eq_left hs]
      exact (hi.resolve_left (Ne.symm he)).symm

end FourColor.KempeMatchingChromogram
