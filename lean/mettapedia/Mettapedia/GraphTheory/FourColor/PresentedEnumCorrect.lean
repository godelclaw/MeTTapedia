import Mettapedia.GraphTheory.FourColor.PresentedEnumRun

/-!
# Correctness of the enumerator, part three: the mask is the closed form

`enumMask_testBit_iff`: bit `Y` of `enumMask X` is set iff some nonzero interior
colouring makes the tangle accept the colour words of `X` and `Y`
(`Pres.ValidColoring`, hence `Pres.accepts_iff`).  With this, a valid
presentation's relation table is a kernel computation and its stabilisation a
kernel check, for every shape at once.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab
namespace Presented

open PA ZigzagRing TubeRingOrbit

/-! ## Bits of the fold -/

theorem testBit_foldl_or {α : Type} (f : α → Nat) (Y : Nat) :
    ∀ (L : List α) (a : Nat),
      (L.foldl (fun acc σ => acc ||| (1 <<< f σ)) a).testBit Y = true ↔
        a.testBit Y = true ∨ ∃ σ ∈ L, f σ = Y
  | [], a => by simp
  | σ :: L, a => by
    simp only [List.foldl_cons, List.mem_cons, exists_eq_or_imp]
    rw [testBit_foldl_or f Y L, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
      Bool.or_eq_true, decide_eq_true_iff]
    tauto

namespace Pres

variable {V N k : Nat} [NeZero k] (P : Pres V N k)

/-- every edge and out-port slot occurs at some vertex -/
theorem slotsOf_all (hP : P.Valid) (s : Slot N k) (hs : ∀ i, s ≠ Slot.inp i) :
    P.SlotsOf (List.finRange V) s := by
  obtain ⟨hend, -, -, hout, -⟩ := hP
  rcases s with e | i | i
  · refine ⟨(P.endPos e false).1, List.mem_finRange _, ?_⟩
    have := hend e false
    simp only [slotAt] at this
    simp only [SlotOf]
    rcases hs3 : (P.endPos e false).2 with ⟨n, hn⟩
    rw [hs3] at this
    match n, hn, this with
    | 0, _, h => exact Or.inl h.symm
    | 1, _, h => exact Or.inr (Or.inl h.symm)
    | 2, _, h => exact Or.inr (Or.inr h.symm)
  · exact absurd rfl (hs i)
  · refine ⟨(P.outPos i).1, List.mem_finRange _, ?_⟩
    have := hout i
    simp only [slotAt] at this
    simp only [SlotOf]
    rcases hs3 : (P.outPos i).2 with ⟨n, hn⟩
    rw [hs3] at this
    match n, hn, this with
    | 0, _, h => exact Or.inl h.symm
    | 1, _, h => exact Or.inr (Or.inl h.symm)
    | 2, _, h => exact Or.inr (Or.inr h.symm)

theorem look_empty (x : Fin k → Fin 3) (s : Slot N k) :
    ((PA.empty : PA N k).look x s).isSome ↔ ∃ i, s = Slot.inp i := by
  cases s <;> simp [PA.empty, look]

/-- membership in the final list: every slot assigned, every vertex proper -/
theorem mem_final_iff (hP : P.Valid) (x : Fin k → Fin 3) (σ : PA N k) :
    σ ∈ P.runVertices x (List.finRange V) [PA.empty] ↔
      (∀ s, (σ.look x s).isSome) ∧ ∀ v, properAt x σ (P.tri v 0) (P.tri v 1) (P.tri v 2) = true := by
  rw [mem_runVertices_iff]
  constructor
  · rintro ⟨σ₀, hσ₀, -, hdom, hp⟩
    simp only [List.mem_singleton] at hσ₀
    subst hσ₀
    refine ⟨fun s => ?_, fun v => hp v (List.mem_finRange v)⟩
    rw [hdom, look_empty]
    by_cases hs : ∃ i, s = Slot.inp i
    · exact Or.inl hs
    · right
      exact P.slotsOf_all hP s (fun i h => hs ⟨i, h⟩)
  · rintro ⟨hall, hp⟩
    refine ⟨PA.empty, List.mem_singleton_self _, ?_, fun s => ?_, fun v _ => hp v⟩
    · intro s hs
      rw [look_empty] at hs
      obtain ⟨i, rfl⟩ := hs
      rfl
    · constructor
      · intro _
        rw [look_empty]
        by_cases hs : ∃ i, s = Slot.inp i
        · exact Or.inl hs
        · exact Or.inr (P.slotsOf_all hP s (fun i h => hs ⟨i, h⟩))
      · intro _; exact hall s

/-! ## Digits and colours -/

/-- the digit a complete assignment gives a slot -/
noncomputable def digitOf (x : Fin k → Fin 3) (σ : PA N k) (s : Slot N k) : Fin 3 :=
  (σ.look x s).getD 0

theorem look_eq_some_digitOf (x : Fin k → Fin 3) (σ : PA N k) (s : Slot N k)
    (h : (σ.look x s).isSome) : σ.look x s = some (digitOf x σ s) := by
  unfold digitOf
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
  rw [hd]; rfl

/-- the colouring read off a complete assignment -/
noncomputable def colOf (x : Fin k → Fin 3) (σ : PA N k) (e : Fin N) : Color :=
  col (digitOf x σ (Slot.edge e))

noncomputable def outWordOf (x : Fin k → Fin 3) (σ : PA N k) (i : Fin k) : Color :=
  col (digitOf x σ (Slot.out i))

theorem inWord_val (X : Nat) (i : Fin k) : ((inWord X i : Fin 3) : Nat) = digit X i := rfl

/-- the colour at a position is the colour of the assigned digit -/
theorem colAt_eq_digitOf (X : Nat) (σ : PA N k) (hall : ∀ s, (σ.look (inWord X) s).isSome)
    (p : Pos V) :
    P.colAt (colOf (inWord X) σ) (wordOf k X) (outWordOf (inWord X) σ) p =
      col (digitOf (inWord X) σ (P.slotAt p)) := by
  unfold colAt
  cases h : P.slotAt p with
  | edge e => rfl
  | inp i =>
    simp only [wordOf]
    unfold digitOf
    simp [look, inWord_val]
  | out i => rfl

theorem properAt_iff_digits (x : Fin k → Fin 3) (σ : PA N k)
    (hall : ∀ s, (σ.look x s).isSome) (s0 s1 s2 : Slot N k) :
    properAt x σ s0 s1 s2 = true ↔
      digitOf x σ s0 ≠ digitOf x σ s1 ∧ digitOf x σ s0 ≠ digitOf x σ s2 ∧
        digitOf x σ s1 ≠ digitOf x σ s2 := by
  rw [properAt_iff]
  constructor
  · rintro ⟨a, b, c, h0, h1, h2, hab, hac, hbc⟩
    simp only [digitOf, h0, h1, h2, Option.getD_some]
    exact ⟨hab, hac, hbc⟩
  · rintro ⟨hab, hac, hbc⟩
    exact ⟨_, _, _, look_eq_some_digitOf x σ s0 (hall s0), look_eq_some_digitOf x σ s1 (hall s1),
      look_eq_some_digitOf x σ s2 (hall s2), hab, hac, hbc⟩

theorem col_fin_inj {a b : Fin 3} (h : col (a : Nat) = col (b : Nat)) : a = b :=
  Fin.ext (col_inj a.isLt b.isLt h)

theorem outNumeral_digit (σ : PA N k) (i : Fin k) :
    digit (outNumeral σ) i = ((σ.o i).getD 0).val := by
  unfold outNumeral
  rw [digit_eq_digB, digB_encB (by norm_num) k (fun j _ => by
    unfold outDigit; split_ifs <;> first | exact Fin.isLt _ | omega) i i.isLt]
  simp [outDigit, i.isLt]

theorem outNumeral_lt (σ : PA N k) : outNumeral σ < 3 ^ k :=
  encB_lt (by norm_num) k (fun j _ => by unfold outDigit; split_ifs <;> first | exact Fin.isLt _ | omega)

/-! ## The theorem -/

/-- **the enumerator is the closed form** -/
theorem enumMask_testBit_iff (hP : P.Valid) (X Y : Nat) (hY : Y < 3 ^ k) :
    (P.enumMask X).testBit Y = true ↔
      ∃ c, P.ValidColoring c (wordOf k X) (wordOf k Y) := by
  unfold enumMask
  rw [testBit_foldl_or]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨σ, hσ, hout⟩
    rw [mem_final_iff P hP] at hσ
    obtain ⟨hall, hp⟩ := hσ
    -- the out word of `σ` is the word of `Y`
    have hy : wordOf k Y = outWordOf (inWord X) σ := by
      funext i
      simp only [wordOf, outWordOf, digitOf, look, ← hout, outNumeral_digit]
    rw [hy]
    refine ⟨colOf (inWord X) σ, ⟨fun e => col_ne_zero _, fun i => wordOf_ne_zero k X i,
      fun i => col_ne_zero _, ?_⟩⟩
    intro v s s' hss'
    rw [colAt_eq_digitOf P X σ hall, colAt_eq_digitOf P X σ hall]
    have hpv := (properAt_iff_digits (inWord X) σ hall _ _ _).mp (hp v)
    intro heq
    have := col_fin_inj heq
    simp only [slotAt] at this
    fin_cases s <;> fin_cases s' <;> simp at hss' <;>
      first
      | exact hpv.1 this | exact hpv.1 this.symm
      | exact hpv.2.1 this | exact hpv.2.1 this.symm
      | exact hpv.2.2 this | exact hpv.2.2 this.symm
  · rintro ⟨c, hV⟩
    -- the assignment of the colouring
    let σ : PA N k := ⟨fun e => some ⟨idx (c e), idx_lt _⟩, fun i => some ⟨digit Y i, digit_lt _ _⟩⟩
    have hall : ∀ s, (σ.look (inWord X) s).isSome := by
      rintro (e | i | i) <;> simp [σ, look]
    have hdig : ∀ p : Pos V, col (digitOf (inWord X) σ (P.slotAt p)) =
        P.colAt c (wordOf k X) (wordOf k Y) p := by
      intro p
      unfold colAt digitOf
      cases P.slotAt p with
      | edge e => simp [σ, look, col_idx (hV.c_ne_zero e)]
      | inp i => simp [σ, look, wordOf, inWord_val]
      | out i => simp [σ, look, wordOf]
    refine ⟨σ, ?_, ?_⟩
    · rw [mem_final_iff P hP]
      refine ⟨hall, fun v => ?_⟩
      rw [properAt_iff_digits (inWord X) σ hall]
      have hd : ∀ s s' : Fin 3, s ≠ s' → digitOf (inWord X) σ (P.tri v s) ≠ digitOf (inWord X) σ (P.tri v s') := by
        intro s s' hss' heq
        apply hV.distinct v s s' hss'
        rw [← hdig (v, s), ← hdig (v, s')]
        simp only [slotAt]
        rw [heq]
      exact ⟨hd 0 1 (by decide), hd 0 2 (by decide), hd 1 2 (by decide)⟩
    · -- the out numeral is `Y`
      rw [← encB_digB_of_lt (β := 3) (n := k) hY]
      unfold outNumeral
      apply encB_congr
      intro i hi
      simp [outDigit, hi, σ, digit_eq_digB]

end Pres
end Presented
end TubeSlab
end Mettapedia.GraphTheory.FourColor
