import MettapediaFourColor.KempeIndexedCertificate
import MettapediaFourColor.KempeAnchorProjection

/-! # Checking supplied whole-chord witnesses

Each balanced unsigned exterior skeleton receives a mask and an answer.
The checker validates that the mask selects complete chords, produces exactly
the answer trace, and descends in rank. No search for a successful mask occurs
in the kernel. The original signed exterior is retained by `recolor_matches`.
-/

namespace FourColor.KempeMaskCertificate

open KempeChordMasks KempeProfileCertificate

def enumeratedEntries (n : ℕ) : List (List Bool × ℕ) :=
  ((KempeAnchorProjection.words n).filter (KempeChordMasks.balanced 0)).zipIdx

private def shortCodes : ℕ → List ℕ
  | 0 => [0]
  | 2 => [1]
  | 4 => [5, 3]
  | 6 => [21, 13, 19, 11, 7]
  | 8 => [85, 53, 77, 45, 29, 83, 51, 75, 43, 27, 71, 39, 23, 15]
  | 10 => [341, 213, 309, 181, 117, 333, 205, 301, 173, 109, 285, 157, 93, 61,
      339, 211, 307, 179, 115, 331, 203, 299, 171, 107, 283, 155, 91, 59,
      327, 199, 295, 167, 103, 279, 151, 87, 55, 271, 143, 79, 47, 31]
  | _ => []

private def shortEntries (n : ℕ) : List (List Bool × ℕ) :=
  ((shortCodes n).map fun code => (List.range n).map code.testBit).zipIdx

set_option maxRecDepth 32768 in
-- Check the shared small unsigned enumeration once, before its many consumers.
private theorem shortEntries_eq : ∀ n : Fin 11, shortEntries n = enumeratedEntries n := by
  decide +kernel

/-- A checked small enumeration; larger boundaries retain the general definition. -/
def entries (n : ℕ) : List (List Bool × ℕ) :=
  if n < 11 then shortEntries n else enumeratedEntries n

theorem entries_eq (n : ℕ) : entries n = enumeratedEntries n := by
  unfold entries
  split
  · exact shortEntries_eq ⟨n, by assumption⟩
  · rfl

theorem entries_complete (ds : List Bool) (hb : KempeChordMasks.balanced 0 ds = true) :
    ∃ j, (ds, j) ∈ entries ds.length := by
  have hs : ds ∈ (KempeAnchorProjection.words ds.length).filter (KempeChordMasks.balanced 0) :=
    List.mem_filter.mpr ⟨KempeAnchorProjection.mem_words ds, hb⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hs
  rw [entries_eq]
  exact ⟨j, List.mk_mem_zipIdx_iff_getElem?.mpr hj⟩

variable {I : Type*}

def answers (word : I → List Color) (next : I → ℕ → I × EdgePerm) (i : I) :
    List (I × EdgePerm) :=
  (entries (active (word i)).length).map fun p => next i p.2

def check (word : I → List Color) (rank : I → ℕ)
    (next : I → ℕ → I × EdgePerm) (mask : I → ℕ → List Bool) (i : I) : Bool :=
  (entries (active (word i)).length).all fun (ds, j) =>
    paired [] (mask i j) ds &&
      decide (answerWord word (next i j) = recolor (mask i j) (word i)) &&
      decide (rank (next i j).1 < rank i)

theorem check_sound (word : I → List Color) (rank : I → ℕ)
    (next : I → ℕ → I × EdgePerm) (mask : I → ℕ → List Bool) (i : I)
    (h : check word rank next mask i = true) :
    (∀ gram, matchg [] (word i) gram →
      ∃ a ∈ answers word next i, matchg [] (answerWord word a) gram) ∧
    ∀ a ∈ answers word next i, rank a.1 < rank i := by
  have each := List.all_eq_true.mp h
  constructor
  · intro gram hm
    obtain ⟨hb, hl⟩ := matched_skeleton gram (word i) [] hm
    obtain ⟨j, hj⟩ := entries_complete (skeleton gram) hb
    rw [hl] at hj
    have he := each _ hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at he
    refine ⟨next i j, List.mem_map.mpr ⟨(skeleton gram, j), hj, rfl⟩, ?_⟩
    rw [he.1.2]
    exact recolor_matches gram (word i) (mask i j) [] [] hm he.1.1
  · intro a ha
    obtain ⟨⟨ds, j⟩, hj, rfl⟩ := List.mem_map.mp ha
    have he := each _ hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at he
    exact he.2

end FourColor.KempeMaskCertificate
