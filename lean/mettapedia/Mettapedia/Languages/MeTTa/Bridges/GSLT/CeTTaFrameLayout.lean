import Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameLayoutCode
import Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback

/-!
# CeTTa's frame identities as a declared layout

CeTTa packs a frame identity, a handle and a generation, into 32 bits with
four classes chosen by a prefix: `0` (20-bit handle, 11-bit generation),
`10` (24, 6), `110` (26, 3) and `1110` (26, 2). The prefix `1111` is reserved;
CeTTa's decoder still reads it, as a handle past the limit.

`frameIdentity` declares that layout once. The kernel decides that it is
well formed, so the generic laws of `LayoutCodes` apply: a written identity
reads back, every valid identity has exactly one word, and distinct words read
as distinct pairs. The theorems below show that the declared layout is the
codec `CeTTaFrameWriteback.NativeFrames` restates by hand: the same total
reading (`unpackHandle`, `unpackGeneration`), the same checked reading
(`decode?`), the same words (`encoding`). The hand codec's round trip follows
from the generic one (`decode_encode_of_layout`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameLayout

open Mettapedia.GSLT.LanguageDef.LayoutAlgebra (Slot pack)
open Mettapedia.GSLT.LanguageDef.LayoutCodes
open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Token)

open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameLayoutCode (frameClass reservedClass frameIdentity)

/-! The layout's constants are CeTTa's. -/

@[simp] theorem code_classOneFirst : CeTTaFrameLayoutCode.classOneFirst = classOneFirst := rfl
@[simp] theorem code_classTwoFirst : CeTTaFrameLayoutCode.classTwoFirst = classTwoFirst := rfl
@[simp] theorem code_classThreeFirst : CeTTaFrameLayoutCode.classThreeFirst = classThreeFirst := rfl
@[simp] theorem code_handleLimit : CeTTaFrameLayoutCode.handleLimit = handleLimit := rfl

theorem frameIdentity_facts : frameIdentity.Facts :=
  Code.facts_of_wellFormed CeTTaFrameLayoutCode.frameIdentity_wellFormed

/-! ## The total reading is CeTTa's -/

theorem frameIdentity_parts {w : Nat} (hw : w < 2 ^ 32) :
    frameIdentity.parts w = [unpackHandle w, unpackGeneration w] := by
  unfold Code.parts
  by_cases first : w < 2 ^ 31
  · have h0 : w / 2 ^ 31 = 0 := by omega
    simp only [frameIdentity, code_classOneFirst, code_classTwoFirst, code_classThreeFirst, Mettapedia.GSLT.LanguageDef.LayoutCodes.Trie.locate, h0, if_true, frameClass, readPlaces, Mettapedia.GSLT.LanguageDef.LayoutAlgebra.get,
      List.map, unpackHandle, unpackGeneration, first]
    simp only [Nat.reduceSub, Nat.reduceAdd, Nat.pow_zero, Nat.div_one, Nat.add_zero, List.cons.injEq,
      and_true]
    omega
  · have h0 : ¬ w / 2 ^ 31 = 0 := by omega
    by_cases second : w < 3 * 2 ^ 30
    · have h1 : w % 2 ^ 31 / 2 ^ 30 = 0 := by omega
      simp only [frameIdentity, code_classOneFirst, code_classTwoFirst, code_classThreeFirst, Mettapedia.GSLT.LanguageDef.LayoutCodes.Trie.locate, h0, h1, if_true, if_false, frameClass, readPlaces,
        List.map, unpackHandle, unpackGeneration, first, second]
      simp only [Nat.reduceSub, Nat.reduceAdd, Nat.pow_zero, Nat.div_one, Nat.add_zero,
        List.cons.injEq, and_true, classOneFirst, Mettapedia.GSLT.LanguageDef.LayoutAlgebra.get]
      omega
    · have h1 : ¬ w % 2 ^ 31 / 2 ^ 30 = 0 := by omega
      by_cases third : w < 7 * 2 ^ 29
      · have h2 : w % 2 ^ 31 % 2 ^ 30 / 2 ^ 29 = 0 := by omega
        simp only [frameIdentity, code_classOneFirst, code_classTwoFirst, code_classThreeFirst, Mettapedia.GSLT.LanguageDef.LayoutCodes.Trie.locate, h0, h1, h2, if_true, if_false, frameClass,
          readPlaces, Mettapedia.GSLT.LanguageDef.LayoutAlgebra.get, List.map, unpackHandle, unpackGeneration, first, second, third]
        simp only [Nat.reduceSub, Nat.reduceAdd, Nat.pow_zero, Nat.div_one, Nat.add_zero,
          List.cons.injEq, and_true, classTwoFirst]
        omega
      · have h2 : ¬ w % 2 ^ 31 % 2 ^ 30 / 2 ^ 29 = 0 := by omega
        by_cases fourth : w < 15 * 2 ^ 28
        · have h3 : w % 2 ^ 31 % 2 ^ 30 % 2 ^ 29 / 2 ^ 28 = 0 := by omega
          simp only [frameIdentity, code_classOneFirst, code_classTwoFirst, code_classThreeFirst, Mettapedia.GSLT.LanguageDef.LayoutCodes.Trie.locate, h0, h1, h2, h3, if_true, if_false, frameClass,
            readPlaces, Mettapedia.GSLT.LanguageDef.LayoutAlgebra.get, List.map, unpackHandle, unpackGeneration, first, second, third, fourth]
          simp only [Nat.reduceSub, Nat.reduceAdd, Nat.pow_zero, Nat.div_one, Nat.add_zero,
            List.cons.injEq, and_true, classThreeFirst]
          omega
        · have h3 : ¬ w % 2 ^ 31 % 2 ^ 30 % 2 ^ 29 / 2 ^ 28 = 0 := by omega
          simp only [frameIdentity, code_classOneFirst, code_classTwoFirst, code_classThreeFirst, code_handleLimit, Mettapedia.GSLT.LanguageDef.LayoutCodes.Trie.locate, h0, h1, h2, h3, if_false, reservedClass,
            readPlaces, Mettapedia.GSLT.LanguageDef.LayoutAlgebra.get, List.map, unpackHandle, unpackGeneration, first, second, third, fourth]
          simp only [Nat.reduceSub, Nat.reduceAdd, Nat.pow_zero, Nat.div_one, Nat.add_zero,
            List.cons.injEq, and_true, handleLimit]
          omega

/-! ## The checked reading is CeTTa's -/

private theorem admits_class {hb f lo gb mx h g : Nat} :
    (frameClass hb f lo gb mx).admits [h, g] =
      (decide (lo ≤ h ∧ h ≤ f + 2 ^ hb - 1) && decide (1 ≤ g ∧ g ≤ mx)) := by
  simp [frameClass, Case.admits, within]

theorem frameIdentity_admits {w : Nat} (hw : w < 2 ^ 32) :
    (frameIdentity.trie.locate 32 w).1.admits [unpackHandle w, unpackGeneration w] =
      decide (Representable ⟨unpackHandle w, unpackGeneration w⟩) := by
  unfold Representable
  by_cases first : w < 2 ^ 31
  · have h0 : w / 2 ^ 31 = 0 := by omega
    simp only [frameIdentity, code_classOneFirst, code_classTwoFirst, code_classThreeFirst, Mettapedia.GSLT.LanguageDef.LayoutCodes.Trie.locate, h0, if_true, frameClass, Case.admits, within,
      unpackHandle, unpackGeneration, first, generationMax]
    simp only [classOneFirst, handleLimit, Bool.not_false, Bool.true_and, Bool.and_true]
    have : w % 2 ^ 20 < 2 ^ 20 := Nat.mod_lt _ (by decide)
    simp only [show w % 2 ^ 20 < 2 ^ 20 from this, if_true]
    simp only [← Bool.decide_and, decide_eq_decide]; omega
  · have h0 : ¬ w / 2 ^ 31 = 0 := by omega
    by_cases second : w < 3 * 2 ^ 30
    · have h1 : w % 2 ^ 31 / 2 ^ 30 = 0 := by omega
      have n0 : ¬ classOneFirst + w % 2 ^ 24 < classOneFirst := by omega
      have n1 : classOneFirst + w % 2 ^ 24 < classTwoFirst := by
        unfold classOneFirst classTwoFirst; omega
      simp only [frameIdentity, code_classOneFirst, code_classTwoFirst, code_classThreeFirst, Mettapedia.GSLT.LanguageDef.LayoutCodes.Trie.locate, h0, h1, if_true, if_false, admits_class,
        unpackHandle, unpackGeneration, first, second, generationMax, n0, n1]
      simp only [← Bool.decide_and, decide_eq_decide]
      unfold classOneFirst handleLimit
      omega
    · have h1 : ¬ w % 2 ^ 31 / 2 ^ 30 = 0 := by omega
      by_cases third : w < 7 * 2 ^ 29
      · have h2 : w % 2 ^ 31 % 2 ^ 30 / 2 ^ 29 = 0 := by omega
        have n0 : ¬ classTwoFirst + w % 2 ^ 26 < classOneFirst := by
          unfold classOneFirst classTwoFirst; omega
        have n1 : ¬ classTwoFirst + w % 2 ^ 26 < classTwoFirst := by omega
        have n2 : classTwoFirst + w % 2 ^ 26 < classThreeFirst := by
          unfold classTwoFirst classThreeFirst; omega
        simp only [frameIdentity, code_classOneFirst, code_classTwoFirst, code_classThreeFirst, Mettapedia.GSLT.LanguageDef.LayoutCodes.Trie.locate, h0, h1, h2, if_true, if_false, admits_class,
          unpackHandle, unpackGeneration, first, second, third, generationMax, n0, n1, n2]
        simp only [← Bool.decide_and, decide_eq_decide]
        unfold classTwoFirst handleLimit
        omega
      · have h2 : ¬ w % 2 ^ 31 % 2 ^ 30 / 2 ^ 29 = 0 := by omega
        by_cases fourth : w < 15 * 2 ^ 28
        · have h3 : w % 2 ^ 31 % 2 ^ 30 % 2 ^ 29 / 2 ^ 28 = 0 := by omega
          have n0 : ¬ classThreeFirst + w % 2 ^ 26 < classOneFirst := by
            unfold classOneFirst classThreeFirst; omega
          have n1 : ¬ classThreeFirst + w % 2 ^ 26 < classTwoFirst := by
            unfold classTwoFirst classThreeFirst; omega
          have n2 : ¬ classThreeFirst + w % 2 ^ 26 < classThreeFirst := by omega
          simp only [frameIdentity, code_classOneFirst, code_classTwoFirst, code_classThreeFirst, Mettapedia.GSLT.LanguageDef.LayoutCodes.Trie.locate, h0, h1, h2, h3, if_true, if_false, admits_class,
            unpackHandle, unpackGeneration, first, second, third, fourth, generationMax, n0, n1, n2]
          simp only [← Bool.decide_and, decide_eq_decide]
          unfold classThreeFirst handleLimit
          omega
        · have h3 : ¬ w % 2 ^ 31 % 2 ^ 30 % 2 ^ 29 / 2 ^ 28 = 0 := by omega
          simp only [frameIdentity, code_classOneFirst, code_classTwoFirst, code_classThreeFirst, code_handleLimit, Mettapedia.GSLT.LanguageDef.LayoutCodes.Trie.locate, h0, h1, h2, h3, if_false, reservedClass,
            Case.admits, unpackHandle, first, second, third, fourth]
          simp only [Bool.not_true, Bool.false_and, false_eq_decide_iff, not_and]
          intro _ h
          omega

theorem frameIdentity_decode {w : Nat} (hw : w < 2 ^ 32) :
    frameIdentity.decode w =
      (decode? (BitVec.ofNat 64 w)).map fun t => [t.handle, t.generation] := by
  have hw64 : (BitVec.ofNat 64 w).toNat = w := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  unfold Code.decode decode?
  simp only [packedHandle, packedGeneration, hw64]
  rw [frameIdentity_parts hw]
  have hadm := frameIdentity_admits hw
  simp only [frameIdentity] at hadm ⊢
  simp only [hadm]
  by_cases hr : Representable ⟨unpackHandle w, unpackGeneration w⟩
  · have hw' : w < 4294967296 := hw
    simp [hr, hw']
  · simp [hr]

/-! ## The words are CeTTa's -/

private theorem pack_two {a b n m : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ m) :
    pack [⟨0, n⟩, ⟨n, m⟩] [a, b] 0 = 2 ^ n * b + a := by
  simp only [Mettapedia.GSLT.LanguageDef.LayoutAlgebra.pack, Mettapedia.GSLT.LanguageDef.LayoutAlgebra.set, Nat.zero_add, Nat.pow_zero, Nat.zero_div, Nat.mul_zero, Nat.zero_mod,
    Nat.one_mul, Nat.add_zero, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega)))]
  simp

theorem frameIdentity_leaves : frameIdentity.trie.leaves =
    [(frameClass 20 0 1 11 2046, 0, 1), (frameClass 24 classOneFirst classOneFirst 6 62, 2, 2),
      (frameClass 26 classTwoFirst classTwoFirst 3 6, 6, 3), (frameClass 26 classThreeFirst classThreeFirst 2 2, 14, 4),
      (reservedClass, 15, 4)] := rfl

private theorem value_class {hb f lo gb mx h g : Nat} (hl : h - f < 2 ^ hb) (hg : g < 2 ^ gb) :
    pack (Mettapedia.GSLT.LanguageDef.LayoutCodes.slotsOf (frameClass hb f lo gb mx).places)
      (Mettapedia.GSLT.LanguageDef.LayoutCodes.storePlaces (frameClass hb f lo gb mx).places [h, g]) 0 =
        2 ^ hb * g + (h - f) := by
  simp only [frameClass, Mettapedia.GSLT.LanguageDef.LayoutCodes.slotsOf, List.map,
    Mettapedia.GSLT.LanguageDef.LayoutCodes.storePlaces, Nat.sub_zero]
  exact pack_two hl hg

/-- The declared layout writes each valid identity as CeTTa's word. -/
theorem frameIdentity_encode {token : Token} (valid : Representable token) :
    frameIdentity.encode [token.handle, token.generation] = some (encoding token) := by
  obtain ⟨h, g⟩ := token
  unfold Representable at valid
  obtain ⟨hpos, hlim, gpos, gmax⟩ := valid
  simp only at hpos hlim gpos gmax
  unfold Code.encode Code.choose
  rw [frameIdentity_leaves]
  unfold handleLimit at hlim
  have r4 : reservedClass.admits [h, g] = false := rfl
  by_cases c0 : h < classOneFirst
  · have hg : g ≤ 2046 := by simpa [generationMax, c0] using gmax
    have a0 : (frameClass 20 0 1 11 2046).admits [h, g] = true := by
      rw [admits_class]; unfold classOneFirst at c0; simp; omega
    simp only [List.find?_cons, a0, Option.map_some, Option.some.injEq]
    rw [value_class (by unfold classOneFirst at c0; omega) (by omega)]
    simp only [encoding, c0, if_true, frameIdentity]
    unfold classOneFirst at c0
    omega
  · have a0 : (frameClass 20 0 1 11 2046).admits [h, g] = false := by
      rw [admits_class]; unfold classOneFirst at c0; simp; omega
    by_cases c1 : h < classTwoFirst
    · have hg : g ≤ 62 := by simpa [generationMax, c0, c1] using gmax
      have a1 : (frameClass 24 classOneFirst classOneFirst 6 62).admits [h, g] = true := by
        rw [admits_class]; unfold classOneFirst at c0 ⊢; unfold classTwoFirst at c1; simp; omega
      simp only [List.find?_cons, a0, a1, Option.map_some, Option.some.injEq]
      rw [value_class (by unfold classOneFirst classTwoFirst at *; omega) (by omega)]
      simp only [encoding, c0, c1, if_true, if_false, frameIdentity]
      unfold classOneFirst classTwoFirst at *
      omega
    · have a1 : (frameClass 24 classOneFirst classOneFirst 6 62).admits [h, g] = false := by
        rw [admits_class]; unfold classOneFirst at c0 ⊢; unfold classTwoFirst at c1; simp; omega
      by_cases c2 : h < classThreeFirst
      · have hg : g ≤ 6 := by simpa [generationMax, c0, c1, c2] using gmax
        have a2 : (frameClass 26 classTwoFirst classTwoFirst 3 6).admits [h, g] = true := by
          rw [admits_class]; unfold classTwoFirst at c1 ⊢; unfold classThreeFirst at c2; simp; omega
        simp only [List.find?_cons, a0, a1, a2, Option.map_some, Option.some.injEq]
        rw [value_class (by unfold classTwoFirst classThreeFirst at *; omega) (by omega)]
        simp only [encoding, c0, c1, c2, if_true, if_false, frameIdentity]
        unfold classOneFirst classTwoFirst classThreeFirst at *
        omega
      · have hg : g ≤ 2 := by simpa [generationMax, c0, c1, c2] using gmax
        have a2 : (frameClass 26 classTwoFirst classTwoFirst 3 6).admits [h, g] = false := by
          rw [admits_class]; unfold classTwoFirst at c1 ⊢; unfold classThreeFirst at c2; simp; omega
        have a3 : (frameClass 26 classThreeFirst classThreeFirst 2 2).admits [h, g] = true := by
          rw [admits_class]; unfold classThreeFirst at c2 ⊢; simp; omega
        simp only [List.find?_cons, a0, a1, a2, a3, Option.map_some, Option.some.injEq]
        rw [value_class (by unfold classThreeFirst at *; omega) (by omega)]
        simp only [encoding, c0, c1, c2, if_false, frameIdentity]
        unfold classOneFirst classTwoFirst classThreeFirst at *
        omega

/-- CeTTa's hand codec's round trip, derived from the layout: the layout writes
the token as CeTTa's word, its generic law reads that word back, and the
layout's checked reading is CeTTa's. -/
theorem decode_encode_of_layout {token : Token} (valid : Representable token) :
    decode? (encode token) = some token := by
  have hr := Code.decode_encode frameIdentity_facts (frameIdentity_encode valid)
  have hlt : encoding token < 2 ^ 32 := by
    unfold Code.decode at hr
    split at hr
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1
    · simp at hr
  rw [frameIdentity_decode hlt] at hr
  unfold encode
  cases hd : decode? (BitVec.ofNat 64 (encoding token)) with
  | none => rw [hd] at hr; simp at hr
  | some t =>
      rw [hd] at hr
      simp only [Option.map_some, Option.some.injEq, List.cons.injEq, and_true] at hr
      cases t; cases token
      simp_all

/-- Distinct 32-bit words are distinct frame readings, valid or not: CeTTa's
total decoder never confuses two identities. -/
theorem unpack_injective {w w' : Nat} (hw : w < 2 ^ 32) (hw' : w' < 2 ^ 32)
    (h : unpackHandle w = unpackHandle w' ∧ unpackGeneration w = unpackGeneration w') : w = w' := by
  apply Code.parts_injective frameIdentity_facts hw hw'
  rw [frameIdentity_parts hw, frameIdentity_parts hw', h.1, h.2]

/-! ## Examples -/

example : frameIdentity.encode [5, 3] = some (3 * 2 ^ 20 + 5) := by decide
/-- Generation zero is never issued. -/
example : frameIdentity.encode [5, 0] = none := by decide
/-- The first handle of class one. -/
example : frameIdentity.encode [classOneFirst, 1] = some (2 ^ 31 + 2 ^ 24) := by decide
/-- The reserved prefix reads as a handle past the limit and never decodes. -/
example : frameIdentity.decode (15 * 2 ^ 28) = none := by decide
example : frameIdentity.parts (15 * 2 ^ 28) = [handleLimit, 0] := by decide

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameLayout
