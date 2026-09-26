import Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonTubeSupportInclusion
import Mettapedia.GraphTheory.FourColor.ZigzagRingErgodicity

/-!
# Eventual full support of pentagon-capped zigzag tubes

The pentagon cap meets every admissible colour-count class. Uniform tube
ergodicity therefore fills every admissible five-port word after sufficiently
many rings. This is a consequence of the arbitrary-circumference theorem,
without another finite transfer-matrix computation.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelV24PentagonTubeSupportInclusion

open ZigzagRing GoertzelV24CorridorPumping

private theorem full_of_admissible (w : CAP5BoundaryWord)
    (hnz : CAP5BoundaryWordIsNonzero w) (hodd : CAP5BoundaryWordHasOddColorCounts w) :
    Full 5 w := by
  refine ⟨hnz, ?_⟩
  have hocc : ∀ c, Odd (cap5BoundaryColorCount w c) → ∃ i, w i = c := by
    intro c hc
    have hpos : 0 < cap5BoundaryColorCount w c := by
      obtain ⟨n, hn⟩ := hc
      omega
    rw [cap5BoundaryColorCount, Finset.card_pos] at hpos
    obtain ⟨i, hi⟩ := hpos
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  intro c hc
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl
  · exact hocc red hodd.1
  · exact hocc blue hodd.2.1
  · exact hocc purple hodd.2.2

private theorem full_of_cap {w : CAP5BoundaryWord} (hw : w ∈ capSupport) : Full 5 w :=
  full_of_admissible w (cap5BoundaryWordIsNonzero_of_extendsAcrossCycle hw)
    (cap5BoundaryWordHasOddColorCounts_of_extendsAcrossCycle hw)

private theorem count_rotateN (w : CAP5BoundaryWord) (c : Color) (n : Nat) :
    colourCount 5 (cap5RotateBoundaryWordN n w) c = colourCount 5 w c := by
  have hshift : ∀ w : CAP5BoundaryWord, cap5RotateBoundaryWord w = shift 5 w := by
    intro w
    funext i
    fin_cases i <;> rfl
  induction n with
  | zero => rfl
  | succ n ih =>
      change colourCount 5 (cap5RotateBoundaryWord (cap5RotateBoundaryWordN n w)) c = _
      rw [hshift, colourCount_shift, ih]

private theorem canonical_counts (a b c d : Color) :
    colourCount 5 (cap5BoundaryWord311Of a b c) d =
      colourCount 5 (cap5BoundaryWord2111Of a b c) d := by
  revert a b c d
  decide +kernel

/-- Every parity-admissible five-port word has the same colour multiplicities
as a word realized by the pentagon cap. -/
theorem cap_meets_admissible_count_class (w : CAP5BoundaryWord)
    (hnz : CAP5BoundaryWordIsNonzero w) (hodd : CAP5BoundaryWordHasOddColorCounts w) :
    ∃ x ∈ capSupport, ∀ c, colourCount 5 x c = colourCount 5 w c := by
  rcases cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd hnz hodd
    with hgood | hbad
  · exact ⟨w, cap5_extendsAcrossCycle_of_coloredBlock311 hgood, fun _ => rfl⟩
  · obtain ⟨a, b, c, htriple, n, rfl⟩ := hbad
    refine ⟨cap5BoundaryWord311Of a b c, cap5BoundaryWord311Of_extendsAcrossCycle htriple, ?_⟩
    intro d
    rw [count_rotateN]
    exact canonical_counts a b c d

/-- Actual ring paths carry existing tube colourings forward. -/
theorem mem_tubeSupport_add_of_transfer {n : Nat} {x y : CAP5BoundaryWord}
    (h : ExactRelationalTransfer (Step 5) n x y) :
    ∀ m, x ∈ tubeSupport m → y ∈ tubeSupport (m + n) := by
  induction h with
  | zero => intro m hm; simpa using hm
  | @succ n x z y hstep htail ih =>
      intro m hm
      have hz : z ∈ tubeSupport (m + 1) := ⟨x, hm, hstep⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (m + 1) hz

/-- All admissible five-port words are realized by every sufficiently long
pentagon-capped tube. The threshold is independent of the boundary word. -/
theorem pentagon_tube_eventually_full :
    ∃ R, ∀ n, R ≤ n → ∀ w : CAP5BoundaryWord,
      CAP5BoundaryWordIsNonzero w → CAP5BoundaryWordHasOddColorCounts w →
      w ∈ tubeSupport n := by
  obtain ⟨R, hR⟩ := tube_ergodicity 5 (by omega)
  refine ⟨R, ?_⟩
  intro n hn w hnz hodd
  obtain ⟨x, hx, hcounts⟩ := cap_meets_admissible_count_class w hnz hodd
  have hpath := hR x w (full_of_cap hx) hcounts n hn
  simpa using mem_tubeSupport_add_of_transfer hpath 0 hx

end GoertzelV24PentagonTubeSupportInclusion
end Mettapedia.GraphTheory.FourColor
