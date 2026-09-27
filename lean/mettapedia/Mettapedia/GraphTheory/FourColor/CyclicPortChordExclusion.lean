import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Short faces exclude chords between regularly spaced ports

Suppose consecutive ports are joined by three face steps, starting on the
opposite side of the first port. A chord between two ports then forces a
second chord with a shorter cyclic gap whenever its face has length five
or six. Descent ends at a fixed edge reversal or a three-step face.
-/

namespace Mettapedia.GraphTheory.FourColor.CyclicPortChordExclusion

open Fin.NatCast

variable {D : Type*} {k : ℕ} [NeZero k]

/-- Actual face arcs, with two intermediate darts between consecutive
ports. The first intermediate darts are disjoint from all ports. -/
structure Arcs (face mate : Equiv.Perm D) (k : ℕ) [NeZero k] where
  port : Fin k → D
  first : Fin k → D
  second : Fin k → D
  start : ∀ i, face (mate (port i)) = first i
  middle : ∀ i, face (first i) = second i
  finish : ∀ i, face (second i) = port (i + 1)
  disjoint : ∀ i j, port i ≠ first j

namespace Arcs

variable {face mate : Equiv.Perm D} (A : Arcs face mate k)

theorem three_steps (i : Fin k) : (face ^ 3) (mate (A.port i)) = A.port (i + 1) := by
  simp only [pow_succ, pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    A.start, A.middle, A.finish]

theorem two_steps (i : Fin k) : (face ^ 2) (A.first i) = A.port (i + 1) := by
  simp only [pow_succ, pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    A.middle, A.finish]

/-- A pentagonal face cannot contain a chord of this port family. -/
theorem not_five_of_chord {i j : Fin k} (hc : mate (A.port i) = A.port j)
    (hfive : (face ^ 5) (A.port j) = A.port j) : False := by
  have hthree : (face ^ 3) (A.port j) = A.port (i + 1) := by
    rw [← hc, A.three_steps]
  have htwo : (face ^ 2) (A.port (i + 1)) = A.port j := by
    rw [← hthree, ← Equiv.Perm.mul_apply, ← pow_add]
    exact hfive
  have hother : (face ^ 2) (A.first (j - 1)) = A.port j := by
    simpa only [sub_add_cancel] using A.two_steps (j - 1)
  exact A.disjoint _ _ ((face ^ 2).injective (htwo.trans hother.symm))

/-- The next chord is forced by the same actual hexagonal face. -/
theorem shorter_chord (hinv : Function.Involutive mate)
    {i j : Fin k} (hc : mate (A.port i) = A.port j)
    (hsix : (face ^ 6) (A.port j) = A.port j) :
    mate (A.port (i + 1)) = A.port (j - 1) := by
  have hthree : (face ^ 3) (A.port j) = A.port (i + 1) := by
    rw [← hc, A.three_steps]
  have hreturn : (face ^ 3) (A.port (i + 1)) = A.port j := by
    rw [← hthree, ← Equiv.Perm.mul_apply, ← pow_add]
    exact hsix
  have hother : (face ^ 3) (mate (A.port (j - 1))) = A.port j := by
    simpa only [sub_add_cancel] using A.three_steps (j - 1)
  have he := (face ^ 3).injective (hreturn.trans hother.symm)
  exact (congrArg mate he).trans (hinv _)

/-- Uniform chord exclusion by descent on an oriented cyclic gap.
Only face periods at the ports are used. -/
theorem no_chord (hinv : Function.Involutive mate)
    (hfree : ∀ d, mate d ≠ d)
    (hshort : ∀ i, (face ^ 5) (A.port i) = A.port i ∨
      (face ^ 6) (A.port i) = A.port i)
    (hthree : ∀ i, (face ^ 3) (A.port i) ≠ A.port i)
    (i j : Fin k) : mate (A.port i) ≠ A.port j := by
  have descend : ∀ n : ℕ, ∀ i : Fin k,
      mate (A.port i) ≠ A.port (i + (↑n : Fin k)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hc
      rcases n with _ | _ | n
      · exact hfree _ (by simpa using hc)
      · have hh := A.three_steps i
        rw [hc] at hh
        exact hthree _ (by simpa using hh)
      · have hsix : (face ^ 6) (A.port (i + (↑(n + 2) : Fin k))) =
            A.port (i + (↑(n + 2) : Fin k)) := by
          rcases hshort (i + (↑(n + 2) : Fin k)) with h5 | h6
          · exact (A.not_five_of_chord hc h5).elim
          · exact h6
        have next := A.shorter_chord hinv hc hsix
        apply ih n (by omega) (i + 1)
        have htwo : (2 : Fin k) - 1 = 1 := by
          rw [← one_add_one_eq_two, add_sub_cancel_right]
        convert next using 1
        simp [Nat.cast_add, add_sub_assoc, add_comm, add_left_comm, htwo]
  have hh := descend (j - i).val i
  simpa only [Fin.cast_val_eq_self, add_sub_cancel] using hh

end Arcs
end Mettapedia.GraphTheory.FourColor.CyclicPortChordExclusion
