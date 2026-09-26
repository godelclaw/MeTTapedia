import Mettapedia.GraphTheory.FourColor.OddCycleCapConstruction
import Mettapedia.GraphTheory.FourColor.ZigzagRingComposite

/-!
# Full boundary support of sufficiently long odd-capped tubes

The cap supplies one representative of each odd colour-count class. Actual
zigzag rings rearrange that representative into any desired boundary word.
The conclusion is an edge colouring of the literal serial composite.
-/

namespace Mettapedia.GraphTheory.FourColor.CycleCap

open ZigzagRing GoertzelV24CorridorPumping

variable (k : Nat) [NeZero k] (hk : 2 ≤ k)

/-- The literal cap followed by the specified number of zigzag rings. -/
noncomputable def cappedTube : Nat → HiddenTangle Empty (Fin k)
  | 0 => ⟨Fin k, Dart k, cap k hk⟩
  | n + 1 => HiddenTangle.appendRing k (cappedTube n)

/-- A path in the ring relation extends a colouring of the physical tube. -/
theorem cappedTube_accepts_of_transfer {n : Nat} {x y : Fin k → Color}
    (h : ExactRelationalTransfer (Step k) n x y) :
    ∀ m, (cappedTube k hk m).Accepts Empty.elim x →
      (cappedTube k hk (m + n)).Accepts Empty.elim y := by
  induction h with
  | zero => intro m hm; simpa using hm
  | @succ n x z y hstep htail ih =>
      intro m hm
      have hz : (cappedTube k hk (m + 1)).Accepts Empty.elim z :=
        (HiddenTangle.appendRing_accepts_iff k _ _ _).mpr ⟨x, hm, hstep⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (m + 1) hz

/-- For each circumference, all sufficiently long capped tubes realize every
nonzero boundary word with odd colour counts. The threshold is uniform over
the words and over their count classes. -/
theorem cappedTube_eventually_full (hk3 : 3 ≤ k) :
    ∃ R, ∀ n, R ≤ n → ∀ w : Fin k → Color,
      (∀ i, w i ≠ 0) → OddCounts k w →
      (cappedTube k hk n).Accepts Empty.elim w := by
  obtain ⟨R, hR⟩ := tube_ergodicity k hk3
  refine ⟨R, ?_⟩
  intro n hn w hnz hodd
  obtain ⟨x, hx, hcounts⟩ := cap_meets_odd_count_class k hk w hnz hodd
  obtain ⟨p, hp⟩ := exists_perm_of_counts k w x (fun c => (hcounts c).symm)
  have hfull : Full k x := by
    rw [hp]
    exact (full_of_oddCounts k w hnz hodd).comp_perm k p
  have hpath := hR x w hfull hcounts n hn
  simpa using cappedTube_accepts_of_transfer k hk hpath 0 hx

/-- Every parity-admissible boundary colouring extends across a sufficiently
long tube capped by an odd cycle. This is a colouring of the actual composite. -/
theorem odd_cappedTube_eventually_full (hk3 : 3 ≤ k) (hodd : Odd k) :
    ∃ R, ∀ n, R ≤ n → ∀ w : Fin k → Color,
      (∀ i, w i ≠ 0) → (∑ i, w i) = 0 →
      (cappedTube k hk n).Accepts Empty.elim w := by
  obtain ⟨R, hR⟩ := cappedTube_eventually_full k hk hk3
  exact ⟨R, fun n hn w hnz hsum =>
    hR n hn w hnz (oddCounts_of_sum_eq_zero k hodd w hnz hsum)⟩

end Mettapedia.GraphTheory.FourColor.CycleCap
