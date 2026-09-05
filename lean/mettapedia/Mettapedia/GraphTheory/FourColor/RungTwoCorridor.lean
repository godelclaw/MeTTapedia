import Mettapedia.GraphTheory.FourColor.RungTwoTable

/-!
# No long thin annulus of thickness 2 in a least counterexample

The kernel check of `RungTwoTable` becomes the abstract stabilisation
hypothesis of `GeneralTubeChain` through the correspondence between word sets
and bitmasks (`hstab`), and the general tube theorem yields: a coherent chain
of `n` thickness-2 rungs in a graph-backed least counterexample, with good
connected innermost side and connected outermost complement, has
`n ≤ 14408` (`le_of_rungTube`).  This is the corridor case of the long-face
node for annuli of thickness 2: deleting rungs shortens the two bounding faces.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab
namespace RungTwo

open TubeRingOrbit
open ZigzagRing

/-- the words of a bitmask -/
def wordSet (S : Nat) : Set (Port → Color) :=
  {w | ∃ X, X < 81 ∧ S.testBit X = true ∧ w = wordOf 4 X}

theorem wordSet_singleton {X : Nat} (hX : X < 81) : wordSet (1 <<< X) = {wordOf 4 X} := by
  ext w
  simp only [wordSet, Set.mem_setOf_eq, Set.mem_singleton_iff, Nat.one_shiftLeft,
    Nat.testBit_two_pow]
  constructor
  · rintro ⟨X', -, h, rfl⟩
    rw [decide_eq_true_iff] at h
    rw [h]
  · rintro rfl
    exact ⟨X, hX, by simp, rfl⟩

theorem rungTableLit_eq : rungTableLit = (List.range 81).map fun X => rungMask X 243 :=
  rungTable_correct.symm

/-- accepted out-words are nonzero, and so are accepted in-words -/
theorem ne_zero_of_accepts {x y : Port → Color} (h : rung.AcceptsBoundaryWords x y) :
    (∀ i, x i ≠ 0) ∧ ∀ i, y i ≠ 0 := by
  obtain ⟨c, hV⟩ := (accepts_iff x y).mp h
  exact ⟨hV.x_ne_zero, hV.y_ne_zero⟩

/-- one rung on word sets is one mask step -/
theorem relImage_wordSet (S : Nat) :
    relImage rung (wordSet S) = wordSet (stepSet S rungTableLit 0) := by
  ext w'
  simp only [relImage, wordSet, Set.mem_setOf_eq]
  rw [rungTableLit_eq]
  constructor
  · rintro ⟨w, ⟨X, hX, hS, rfl⟩, hacc⟩
    have hy := (ne_zero_of_accepts hacc).2
    refine ⟨encW 4 w', encW_lt 4 w', ?_, (wordOf_encW 4 w' hy).symm⟩
    rw [testBit_stepSet]
    refine ⟨X, hX, by simpa using hS, ?_⟩
    rw [← accepts_iff_testBit X _ (encW_lt 4 w'), wordOf_encW 4 w' hy]
    exact hacc
  · rintro ⟨Y, hY, hb, rfl⟩
    rw [testBit_stepSet] at hb
    obtain ⟨X, hX, hS, hbit⟩ := hb
    exact ⟨wordOf 4 X, ⟨X, hX, by simpa using hS, rfl⟩, (accepts_iff_testBit X Y hY).mpr hbit⟩

theorem relImage_iterate_wordSet (S : Nat) :
    ∀ n, (relImage rung)^[n] (wordSet S) = wordSet (iterSet rungTableLit n S)
  | 0 => rfl
  | n + 1 => by
    simp only [iterSet]
    rw [Function.iterate_succ_apply, relImage_wordSet, relImage_iterate_wordSet _ n]

theorem relImage_iUnion {ι : Type} (W : ι → Set (Port → Color)) :
    relImage rung (⋃ i, W i) = ⋃ i, relImage rung (W i) := by
  ext w'
  simp only [relImage, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨w, ⟨i, hi⟩, h⟩; exact ⟨i, w, hi, h⟩
  · rintro ⟨i, w, hi, h⟩; exact ⟨w, ⟨i, hi⟩, h⟩

theorem relImage_iterate_iUnion {ι : Type} (W : ι → Set (Port → Color)) :
    ∀ n, (relImage rung)^[n] (⋃ i, W i) = ⋃ i, (relImage rung)^[n] (W i)
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply, relImage_iUnion]
    exact relImage_iterate_iUnion (fun i => relImage rung (W i)) n

/-- a word with a zero colour has no image -/
theorem relImage_singleton_zero {w : Port → Color} (hw : ¬ ∀ i, w i ≠ 0) :
    relImage rung {w} = ∅ := by
  ext w'
  simp only [relImage, Set.mem_singleton_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_exists, not_and]
  rintro _ rfl h
  exact hw (ne_zero_of_accepts h).1

theorem relImage_empty : relImage rung ∅ = ∅ := by
  ext; simp [relImage]

theorem relImage_iterate_empty : ∀ n, (relImage rung)^[n] ∅ = ∅
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply, relImage_empty, relImage_iterate_empty n]

/-- the kernel check, read on singletons -/
theorem iterSet_ten_eq_nine {X : Nat} (hX : X < 81) :
    iterSet rungTableLit 10 (1 <<< X) = iterSet rungTableLit 9 (1 <<< X) := by
  have h := stabilizes9_true
  unfold stabilizes9 at h
  rw [List.all_eq_true] at h
  have := h X (List.mem_range.mpr hX)
  rwa [beq_iff_eq] at this

/-- **the abstract stabilisation hypothesis at index 9** -/
theorem hstab (W : Set (Port → Color)) :
    (relImage rung)^[9 + 1] W = (relImage rung)^[9] W := by
  have hW : W = ⋃ w : W, ({(w : Port → Color)} : Set (Port → Color)) := by ext; simp
  rw [hW, relImage_iterate_iUnion, relImage_iterate_iUnion]
  congr 1
  funext w
  by_cases hw : ∀ i, (w : Port → Color) i ≠ 0
  · have hs : ({(w : Port → Color)} : Set (Port → Color)) = wordSet (1 <<< encW 4 w) := by
      rw [wordSet_singleton (encW_lt 4 w), wordOf_encW 4 w hw]
    rw [hs, relImage_iterate_wordSet, relImage_iterate_wordSet, iterSet_ten_eq_nine (encW_lt 4 w)]
  · simp only [Function.iterate_succ_apply, Function.iterate_zero_apply,
      relImage_singleton_zero hw, relImage_empty]

/-! ## The corridor theorem for thickness-2 annuli -/

open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24ConnectedEdgeShoreMajority

variable {V : Type} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
variable {rotation : SimpleGraphDartRotation.Data G}

/-- **No long thin annulus of thickness 2 in a least counterexample.** -/
theorem le_of_rungTube (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {inner : V → Prop} {n : Nat}
    (t : TubeOf rotation.toRotationSystem rung inner n) (hc : t.Coherent)
    (hgood : GoodSide (G := G) inner) (hconn : EdgeShoreConnected G (sideShore inner))
    (hcconn : EdgeShoreConnected G (ZigzagSlab.compShore (t.side n))) :
    n ≤ 14408 := by
  have := TubeOf.le_of_tubeOf shape minimal hstab (by norm_num) t hc hgood hconn hcconn
  norm_num [Nat.factorial] at this
  omega

end RungTwo
end TubeSlab
end Mettapedia.GraphTheory.FourColor
