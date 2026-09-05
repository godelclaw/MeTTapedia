import Mettapedia.GraphTheory.FourColor.RungTwoRelation
import Mettapedia.GraphTheory.FourColor.ZigzagRingComposite

/-!
# The thickness-2 rung: kernel table, stabilisation at index 9, and the bridge

Words on the four ports are base-3 numerals below `81`; `rungMask X` folds over
the `243` edge colourings and sets bit `Y` when the six vertex constraints hold
and `Y` is the forced out-word.  The kernel re-derives the literal table and
checks that `10` rungs give the same word set as `9` from every singleton.
The bridge `accepts_iff_testBit` identifies the mask with the closed form of
`RungTwoRelation`, and `hstab` turns the kernel check into the abstract
stabilisation hypothesis of `GeneralTubeChain`.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab
namespace RungTwo

open TubeRingOrbit
open ZigzagRing

/-! ## The computable mask -/

/-- the third digit -/
def third (p q : Nat) : Nat := 3 - p - q

/-- the six vertex constraints on in-digits `x` and edge digits `c` -/
def ok (X C : Nat) : Bool :=
  (digit X 0 != digit C 0) && (digit C 0 != digit C 1) && (digit C 0 != digit X 1) &&
  (digit C 1 != digit X 1) && (digit C 1 != digit C 2) && (digit C 2 != digit C 3) &&
  (digit C 2 != digit X 2) && (digit C 3 != digit X 2) && (digit C 3 != digit C 4) &&
  (digit C 4 != digit X 3)

/-- the forced out-word -/
def outOf (X C : Nat) : Nat :=
  third (digit X 0) (digit C 0) + third (digit C 1) (digit C 2) * 3 +
    third (digit C 3) (digit C 4) * 9 + third (digit C 4) (digit X 3) * 27

def rungMask (X : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => let acc := rungMask X n; if ok X n then acc ||| (1 <<< outOf X n) else acc

def rungTable : List Nat := (List.range 81).map fun X => rungMask X 243

def rungTableLit : List Nat := [
  72057594306363392, 134217728, 18014398509481984, 2305843011361177600, 1224979099718516736,
  36028797018963968, 4611686022722355200, 536870912, 1152921505949024256, 9447615269638246498304,
  4723519404442971537408, 144115188075855872, 75557863727013835046912, 37779508324259220946944,
  288230376151711744, 151115727454027670093824, 18894077617771886149632, 47225970672392860598272,
  18889465931774933598208, 8589934592, 4722366482939438432256, 604462909816110680375296,
  321120920839813093916672, 9444732965878876864512, 1208925819632221360750592, 34359738368,
  302231454908072520056832, 9481626453886709530626, 4722366482869645213697, 9223372036854775808,
  76738455346631734722576, 38406121161463286464520, 18446744073709551616,
  153476910693263469445152, 18889465931478580854788, 47813960639055157788682,
  1475739525896764130304, 590295810358705652224, 73786976294838206464, 8192,
  295147905179352829952, 147573952589676412928, 16384, 2361183241434822608896,
  1180591620717411308544, 755578637259143234193568, 302231454903657293676608,
  37778931862957161710088, 65536, 151115727451828646873120, 75557863725914323420176, 131072,
  1208925819614629174706432, 604462909807314587385984, 70643622084612, 35184372088832,
  68719476737, 571746046443648, 286147901128772, 137438953474, 1143492092887296, 140737488355328,
  356241767399488, 10995116802208, 4398046773312, 549755813896, 4194304, 2199025352736,
  1099511627792, 8388608, 17592187093248, 8796095643776, 5629499535261696, 2251799813685248,
  281474976972800, 33554432, 1125899924668416, 562949953945600, 67108864, 9007199254740992,
  4503599644147712]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rungTable_correct : rungTable = rungTableLit := by decide +kernel

/-- the kernel check: from every singleton, 10 rungs give the same word set as 9 -/
def stabilizes9 : Bool :=
  (List.range 81).all fun w => iterSet rungTableLit 10 (1 <<< w) == iterSet rungTableLit 9 (1 <<< w)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stabilizes9_true : stabilizes9 = true := by decide +kernel

/-! ## Bits of the mask -/

theorem testBit_rungMask (X Y : Nat) :
    ∀ n, (rungMask X n).testBit Y = true ↔ ∃ C, C < n ∧ ok X C = true ∧ outOf X C = Y
  | 0 => by simp [rungMask]
  | n + 1 => by
    have ih := testBit_rungMask X Y n
    simp only [rungMask]
    by_cases h : ok X n = true
    · rw [if_pos h, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨C, hC, hok, hout⟩ | hd)
        · exact ⟨C, by omega, hok, hout⟩
        · exact ⟨n, by omega, h, decide_eq_true_iff.mp hd⟩
      · rintro ⟨C, hC, hok, hout⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hC with hC | rfl
        · exact Or.inl ⟨C, hC, hok, hout⟩
        · exact Or.inr (decide_eq_true hout)
    · rw [if_neg h, ih]
      constructor
      · rintro ⟨C, hC, hok, hout⟩; exact ⟨C, by omega, hok, hout⟩
      · rintro ⟨C, hC, hok, hout⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hC with hC | rfl
        · exact ⟨C, hC, hok, hout⟩
        · exact absurd hok h

/-! ## The bridge to the closed form -/

theorem distinct3_col {p q r : Nat} (hp : p < 3) (hq : q < 3) (hr : r < 3) :
    Distinct3 (col p) (col q) (col r) ↔ p ≠ q ∧ p ≠ r ∧ q ≠ r := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun h => h1 (h ▸ rfl), fun h => h2 (h ▸ rfl), fun h => h3 (h ▸ rfl)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun h => h1 (col_inj hp hq h), fun h => h2 (col_inj hp hr h),
      fun h => h3 (col_inj hq hr h)⟩

theorem third_lt {p q : Nat} (hp : p < 3) (hq : q < 3) (hpq : p ≠ q) : third p q < 3 := by
  unfold third; omega

theorem col_third' {p q : Nat} (hp : p < 3) (hq : q < 3) (hpq : p ≠ q) :
    col (third p q) = col p + col q := col_third hp hq hpq

/-- the out-digits as a function -/
def outDigits (X C : Nat) : Nat → Nat
  | 0 => third (digit X 0) (digit C 0)
  | 1 => third (digit C 1) (digit C 2)
  | 2 => third (digit C 3) (digit C 4)
  | 3 => third (digit C 4) (digit X 3)
  | _ => 0

theorem outOf_eq_encB (X C : Nat) : outOf X C = encB 3 (outDigits X C) 4 := by
  simp [outOf, encB, outDigits]

/-- the constraints, unpacked -/
theorem ok_iff (X C : Nat) : ok X C = true ↔
    digit X 0 ≠ digit C 0 ∧ digit C 0 ≠ digit C 1 ∧ digit C 0 ≠ digit X 1 ∧
    digit C 1 ≠ digit X 1 ∧ digit C 1 ≠ digit C 2 ∧ digit C 2 ≠ digit C 3 ∧
    digit C 2 ≠ digit X 2 ∧ digit C 3 ≠ digit X 2 ∧ digit C 3 ≠ digit C 4 ∧
    digit C 4 ≠ digit X 3 := by
  simp only [ok, Bool.and_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩

theorem outDigits_lt (X C : Nat) (hok : ok X C = true) : ∀ i, i < 4 → outDigits X C i < 3 := by
  obtain ⟨h1, -, -, -, h5, -, -, -, h9, h10⟩ := (ok_iff X C).mp hok
  intro i hi
  match i, hi with
  | 0, _ => exact third_lt (digit_lt _ _) (digit_lt _ _) h1
  | 1, _ => exact third_lt (digit_lt _ _) (digit_lt _ _) h5
  | 2, _ => exact third_lt (digit_lt _ _) (digit_lt _ _) h9
  | 3, _ => exact third_lt (digit_lt _ _) (digit_lt _ _) h10

theorem digit_outOf (X C : Nat) (hok : ok X C = true) (i : Nat) (hi : i < 4) :
    digit (outOf X C) i = outDigits X C i := by
  rw [outOf_eq_encB, digit_eq_digB]
  exact digB_encB (by norm_num) 4 (outDigits_lt X C hok) i hi

theorem outOf_lt (X C : Nat) (hok : ok X C = true) : outOf X C < 81 := by
  rw [outOf_eq_encB]
  exact encB_lt (by norm_num) 4 (outDigits_lt X C hok)

/-- the edge digits of a valid colouring -/
def encC (c : Fin 5 → Color) : Nat := encB 3 (fun j => if h : j < 5 then idx (c ⟨j, h⟩) else 0) 5

theorem digit_encC (c : Fin 5 → Color) (j : Fin 5) : digit (encC c) j = idx (c j) := by
  simp only [encC, digit_eq_digB]
  rw [digB_encB (by norm_num) 5 (fun i _ => by split_ifs; exact idx_lt _) j j.isLt]
  simp [j.isLt]

theorem digit_encC' (c : Fin 5 → Color) (j : Nat) (hj : j < 5) :
    digit (encC c) j = idx (c ⟨j, hj⟩) := by
  simp only [encC, digit_eq_digB]
  rw [digB_encB (by norm_num) 5 (fun i _ => by split_ifs; exact idx_lt _) j hj]
  simp [hj]

theorem encC_lt (c : Fin 5 → Color) : encC c < 243 :=
  encB_lt (by norm_num) 5 (fun i _ => by split_ifs; exact idx_lt _)

/-- three distinct nonzero colours: the third is the digit `third` -/
theorem digit_of_distinct3 {p q r : Nat} (hp : p < 3) (hq : q < 3) (hr : r < 3)
    (h : Distinct3 (col p) (col q) (col r)) : r = third p q := by
  obtain ⟨h1, h2, h3⟩ := h
  have hpq : p ≠ q := fun e => h1 (e ▸ rfl)
  have := third_eq_add (col_ne_zero p) (col_ne_zero q) (col_ne_zero r) h1 h2 h3
  rw [← col_third' hp hq hpq] at this
  exact col_inj hr (third_lt hp hq hpq) this

theorem distinct3_third {p q : Nat} (hp : p < 3) (hq : q < 3) (hpq : p ≠ q) :
    Distinct3 (col p) (col q) (col (third p q)) := by
  rw [col_third' hp hq hpq]
  have hne : col p ≠ col q := fun h => hpq (col_inj hp hq h)
  exact ⟨hne, (add_ne_left_of_ne_zero (col_ne_zero q)).symm,
    (add_ne_right_of_ne_zero (col_ne_zero p)).symm⟩

/-- **the mask is the closed form** -/
theorem accepts_iff_testBit (X Y : Nat) (hY : Y < 81) :
    rung.AcceptsBoundaryWords (wordOf 4 X) (wordOf 4 Y) ↔ (rungMask X 243).testBit Y = true := by
  rw [accepts_iff, testBit_rungMask]
  constructor
  · rintro ⟨c, hV⟩
    have hc : ∀ j, col (idx (c j)) = c j := fun j => col_idx (hV.c_ne_zero j)
    have v0 : Distinct3 (col (digit X 0)) (col (idx (c 0))) (col (digit Y 0)) := by
      simpa [wordOf, hc] using hV.v0
    have v1 : Distinct3 (col (idx (c 0))) (col (idx (c 1))) (col (digit X 1)) := by
      simpa [wordOf, hc] using hV.v1
    have v2 : Distinct3 (col (idx (c 1))) (col (idx (c 2))) (col (digit Y 1)) := by
      simpa [wordOf, hc] using hV.v2
    have v3 : Distinct3 (col (idx (c 2))) (col (idx (c 3))) (col (digit X 2)) := by
      simpa [wordOf, hc] using hV.v3
    have v4 : Distinct3 (col (idx (c 3))) (col (idx (c 4))) (col (digit Y 2)) := by
      simpa [wordOf, hc] using hV.v4
    have v5 : Distinct3 (col (idx (c 4))) (col (digit X 3)) (col (digit Y 3)) := by
      simpa [wordOf, hc] using hV.v5
    have d0 := (distinct3_col (digit_lt X 0) (idx_lt _) (digit_lt Y 0)).mp v0
    have d1 := (distinct3_col (idx_lt _) (idx_lt _) (digit_lt X 1)).mp v1
    have d2 := (distinct3_col (idx_lt _) (idx_lt _) (digit_lt Y 1)).mp v2
    have d3 := (distinct3_col (idx_lt _) (idx_lt _) (digit_lt X 2)).mp v3
    have d4 := (distinct3_col (idx_lt _) (idx_lt _) (digit_lt Y 2)).mp v4
    have d5 := (distinct3_col (idx_lt _) (digit_lt X 3) (digit_lt Y 3)).mp v5
    have hok : ok X (encC c) = true := by
      rw [ok_iff, digit_encC' c 0 (by norm_num), digit_encC' c 1 (by norm_num),
        digit_encC' c 2 (by norm_num), digit_encC' c 3 (by norm_num), digit_encC' c 4 (by norm_num)]
      exact ⟨d0.1, d1.1, d1.2.1, d1.2.2, d2.1, d3.1, d3.2.1, d3.2.2, d4.1, d5.1⟩
    refine ⟨encC c, encC_lt c, hok, ?_⟩
    rw [outOf_eq_encB, ← encB_digB_of_lt (β := 3) (n := 4) hY]
    apply encB_congr
    intro i hi
    rw [← digit_eq_digB]
    match i, hi with
    | 0, _ =>
      show third (digit X 0) (digit (encC c) 0) = digit Y 0
      rw [digit_encC' c 0 (by norm_num)]
      exact (digit_of_distinct3 (digit_lt X 0) (idx_lt _) (digit_lt Y 0) v0).symm
    | 1, _ =>
      show third (digit (encC c) 1) (digit (encC c) 2) = digit Y 1
      rw [digit_encC' c 1 (by norm_num), digit_encC' c 2 (by norm_num)]
      exact (digit_of_distinct3 (idx_lt _) (idx_lt _) (digit_lt Y 1) v2).symm
    | 2, _ =>
      show third (digit (encC c) 3) (digit (encC c) 4) = digit Y 2
      rw [digit_encC' c 3 (by norm_num), digit_encC' c 4 (by norm_num)]
      exact (digit_of_distinct3 (idx_lt _) (idx_lt _) (digit_lt Y 2) v4).symm
    | 3, _ =>
      show third (digit (encC c) 4) (digit X 3) = digit Y 3
      rw [digit_encC' c 4 (by norm_num)]
      exact (digit_of_distinct3 (idx_lt _) (digit_lt X 3) (digit_lt Y 3) v5).symm
  · rintro ⟨C, hC, hok, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := (ok_iff X C).mp hok
    refine ⟨fun j => col (digit C j), ⟨fun i => wordOf_ne_zero 4 X i, fun i => wordOf_ne_zero 4 _ i,
      fun j => col_ne_zero _, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · show Distinct3 (col (digit X 0)) (col (digit C 0)) (col (digit (outOf X C) 0))
      rw [digit_outOf X C hok 0 (by norm_num)]
      exact distinct3_third (digit_lt _ _) (digit_lt _ _) h1
    · show Distinct3 (col (digit C 0)) (col (digit C 1)) (col (digit X 1))
      exact (distinct3_col (digit_lt _ _) (digit_lt _ _) (digit_lt _ _)).mpr ⟨h2, h3, h4⟩
    · show Distinct3 (col (digit C 1)) (col (digit C 2)) (col (digit (outOf X C) 1))
      rw [digit_outOf X C hok 1 (by norm_num)]
      exact distinct3_third (digit_lt _ _) (digit_lt _ _) h5
    · show Distinct3 (col (digit C 2)) (col (digit C 3)) (col (digit X 2))
      exact (distinct3_col (digit_lt _ _) (digit_lt _ _) (digit_lt _ _)).mpr ⟨h6, h7, h8⟩
    · show Distinct3 (col (digit C 3)) (col (digit C 4)) (col (digit (outOf X C) 2))
      rw [digit_outOf X C hok 2 (by norm_num)]
      exact distinct3_third (digit_lt _ _) (digit_lt _ _) h9
    · show Distinct3 (col (digit C 4)) (col (digit X 3)) (col (digit (outOf X C) 3))
      rw [digit_outOf X C hok 3 (by norm_num)]
      exact distinct3_third (digit_lt _ _) (digit_lt _ _) h10

end RungTwo
end TubeSlab
end Mettapedia.GraphTheory.FourColor
