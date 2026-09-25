import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PackedFiniteDataCodec
import Lean.Elab.Tactic.Basic

/-!
# Kernel bridge from flat hexadecimal payloads to explicit tables

Several generated tables are stored as newline-delimited lowercase hexadecimal
text in string literals and decoded by `decodeHexadecimalNatArray`. Reducing
such a decode in the kernel first rebuilds the literal's UTF-8 bytes through
`List.toByteArray`, whose repeated `Array.push` makes the cost quadratic in the
payload size; payloads of a few kilobytes already exceed practical memory.

This module proves, once and for all tables, that decoding the rendering of a
table returns the table (`decodeHexadecimalNatArray_render`). A single payload
is then connected to an explicit table by the kernel alone: the tactic
`hex_payload_bridge` checks `payload = (String.ofList (hexRender table)).toUTF8`
by `Eq.refl`, which the kernel decides by comparing the literal's characters
with the rendering, in time linear in the payload. The data definitions are not
changed; the explicit tables only give later kernel replays a cheap route to
the same values.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16HexPayloadBridge

open HypercubicDimension16PackedFiniteDataCodec

/-! ## `ByteArray.foldl` as a list fold -/

theorem byteArray_foldlM_loop_id {β : Type} (f : β → UInt8 → β) (as : ByteArray)
    (h : as.size ≤ as.size) :
    ∀ (i j : Nat) (b : β), j + i = as.size →
      ByteArray.foldlM.loop (m := Id) (fun b a => pure (f b a)) as as.size h i j b =
        (as.data.toList.drop j).foldl f b := by
  have hlen : as.data.toList.length = as.size := Array.length_toList
  intro i
  induction i with
  | zero =>
    intro j b hj
    simp only [Nat.add_zero] at hj
    subst hj
    unfold ByteArray.foldlM.loop
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    rw [List.drop_eq_nil_of_le (by omega)]
    try rfl
  | succ i ih =>
    intro j b hj
    have hlt : j < as.size := by omega
    unfold ByteArray.foldlM.loop
    simp only [hlt, ↓reduceDIte]
    show ByteArray.foldlM.loop (m := Id) (fun b a => pure (f b a)) as as.size h i (j + 1)
        (f b as[j]) = _
    rw [ih (j + 1) _ (by omega)]
    have hj' : j < as.data.toList.length := by omega
    rw [List.drop_eq_getElem_cons hj']
    simp [ByteArray.getElem_eq_getElem_data]

theorem byteArray_foldl_eq_foldl_toList {β : Type} (f : β → UInt8 → β) (init : β)
    (as : ByteArray) : as.foldl f init = as.data.toList.foldl f init := by
  unfold ByteArray.foldl ByteArray.foldlM
  simp only [Nat.le_refl, ↓reduceDIte, Nat.sub_zero]
  exact byteArray_foldlM_loop_id f as (Nat.le_refl _) as.size 0 init (by omega)

/-! ## The hexadecimal decoder over a byte list -/

/-- One step of `decodeHexadecimalNatArray`. -/
@[reducible] def hexFoldStep (state : Array Nat × Nat × Bool) (byte : UInt8) :
    Array Nat × Nat × Bool :=
  if byte.toNat = 10 then
    if state.2.2 then (state.1.push state.2.1, 0, false) else state
  else
    (state.1, 16 * state.2.1 + hexadecimalDigit byte, true)

/-- `decodeHexadecimalNatArray` over the payload's byte list. -/
@[reducible] def hexListDecode (bytes : List UInt8) : Array Nat :=
  let state := bytes.foldl hexFoldStep (#[], 0, false)
  if state.2.2 then state.1.push state.2.1 else state.1

theorem decodeHexadecimalNatArray_eq_hexListDecode (payload : ByteArray) :
    decodeHexadecimalNatArray payload = hexListDecode payload.data.toList := by
  unfold decodeHexadecimalNatArray hexListDecode
  rw [byteArray_foldl_eq_foldl_toList]

theorem toUTF8_ofList_data_toList (cs : List Char) :
    (String.ofList cs).toUTF8.data.toList = cs.flatMap String.utf8EncodeChar := by
  simp [String.ofList, List.utf8Encode]

/-! ## Rendering a table and decoding it back -/

/-- Lowercase hexadecimal numerals, one per line, without a trailing newline:
the layout of the generated payloads. -/
@[reducible] def hexRender (table : List Nat) : List Char :=
  List.intercalate ['\n'] (table.map (Nat.toDigits 16))

/-- A hexadecimal digit character is one byte, not a newline, decoding to its value. -/
theorem hexDigit_byte (d : Nat) (hd : d < 16) :
    String.utf8EncodeChar (Nat.digitChar d) = [UInt8.ofNat (Nat.digitChar d).toNat] ∧
      (UInt8.ofNat (Nat.digitChar d).toNat).toNat ≠ 10 ∧
      hexadecimalDigit (UInt8.ofNat (Nat.digitChar d).toNat) = d := by
  have : ∀ e : Fin 16,
      String.utf8EncodeChar (Nat.digitChar e.val) = [UInt8.ofNat (Nat.digitChar e.val).toNat] ∧
        (UInt8.ofNat (Nat.digitChar e.val).toNat).toNat ≠ 10 ∧
        hexadecimalDigit (UInt8.ofNat (Nat.digitChar e.val).toNat) = e.val := by decide
  exact this ⟨d, hd⟩

theorem hexFoldStep_digit (arr : Array Nat) (acc d : Nat) (hd : d < 16) :
    (String.utf8EncodeChar (Nat.digitChar d)).foldl hexFoldStep (arr, acc, true) =
      (arr, 16 * acc + d, true) ∧
    (String.utf8EncodeChar (Nat.digitChar d)).foldl hexFoldStep (arr, acc, false) =
      (arr, 16 * acc + d, true) := by
  obtain ⟨hb, hb10, hbd⟩ := hexDigit_byte d hd
  rw [hb]
  simp only [List.foldl_cons, List.foldl_nil, hexFoldStep, hb10, ↓reduceIte, hbd]
  exact ⟨trivial, trivial⟩

/-- The bytes of `toDigits 16 n`, folded from a fresh accumulator, give `n`. -/
theorem fold_toDigits (n : Nat) (arr : Array Nat) :
    ((Nat.toDigits 16 n).flatMap String.utf8EncodeChar).foldl hexFoldStep (arr, 0, false) =
      (arr, n, true) := by
  induction n using Nat.strongRecOn generalizing arr with
  | ind n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · rename_i hn
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, (hexFoldStep_digit arr 0 n hn).2]
      simp
    · rename_i hn
      have hdiv : n / 16 < n := Nat.div_lt_self (by omega) (by decide)
      rw [List.flatMap_append, List.foldl_append, ih (n / 16) hdiv arr, List.flatMap_cons,
        List.flatMap_nil, List.append_nil,
        (hexFoldStep_digit arr (n / 16) (n % 16) (Nat.mod_lt _ (by decide))).1]
      congr 2
      omega

/-- The newline byte closes the current numeral. -/
theorem hexFoldStep_newline (arr : Array Nat) (acc : Nat) :
    (String.utf8EncodeChar '\n').foldl hexFoldStep (arr, acc, true) = (arr.push acc, 0, false) := by
  have h : String.utf8EncodeChar '\n' = [10] := by decide
  rw [h]
  rfl

theorem fold_render_cons (rest : List Nat) : ∀ (n : Nat) (arr : Array Nat),
    ((List.intercalate ['\n'] ((n :: rest).map (Nat.toDigits 16))).flatMap
        String.utf8EncodeChar).foldl hexFoldStep (arr, 0, false) =
      (arr ++ (n :: rest).dropLast.toArray, (n :: rest).getLast (by simp), true) := by
  induction rest with
  | nil =>
    intro n arr
    simp only [List.map_cons, List.map_nil, List.intercalate_singleton, fold_toDigits]
    simp
  | cons m rest ih =>
    intro n arr
    rw [List.map_cons, List.map_cons, List.intercalate_cons_cons, List.flatMap_append,
      List.flatMap_append, List.foldl_append, List.foldl_append, fold_toDigits,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, hexFoldStep_newline,
      ← List.map_cons, ih m (arr.push n)]
    simp [List.dropLast_cons_cons]

theorem hexListDecode_render (table : List Nat) :
    hexListDecode ((hexRender table).flatMap String.utf8EncodeChar) = table.toArray := by
  cases table with
  | nil => rfl
  | cons n rest =>
    simp only [hexListDecode, hexRender]
    rw [fold_render_cons rest n #[]]
    simp only [↓reduceIte]
    simp only [Array.empty_append, List.push_toArray]
    rw [List.dropLast_concat_getLast]

/-- Decoding the rendering of any table returns the table. -/
theorem decodeHexadecimalNatArray_render (table : List Nat) :
    decodeHexadecimalNatArray (String.ofList (hexRender table)).toUTF8 = table.toArray := by
  rw [decodeHexadecimalNatArray_eq_hexListDecode, toUTF8_ofList_data_toList,
    hexListDecode_render]

theorem decode_eq_of_payload_eq (p : ByteArray) (table : List Nat)
    (h : p = (String.ofList (hexRender table)).toUTF8) :
    decodeHexadecimalNatArray p = table.toArray := by
  subst h
  exact decodeHexadecimalNatArray_render table

/-! ## Connecting one payload to its table -/

open Lean Elab Tactic Meta in
/-- Closes `decodeHexadecimalNatArray p = List.toArray t` by
`decode_eq_of_payload_eq`, where `p = (String.ofList (hexRender t)).toUTF8` is
added as an auxiliary theorem proved by `Eq.refl` and so checked by the kernel
alone, as `decide +kernel` does for its `Eq.refl true`. The proof term is built
explicitly, so the elaborator never unfolds the decoder. A literal `match` left
by `unfold` on the left is reduced by one matcher step first. -/
elab "hex_payload_bridge" : tactic => liftMetaTactic fun g => do
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := ty.eq? | throwError "hex_payload_bridge: goal is not an equality"
  let lhs ← match ← Meta.reduceMatcher? lhs with
    | Meta.ReduceMatcherResult.reduced e => pure e.headBeta
    | _ => pure lhs
  let_expr Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PackedFiniteDataCodec.decodeHexadecimalNatArray p := lhs
    | throwError m!"hex_payload_bridge: left side is not `decodeHexadecimalNatArray p`: {lhs}"
  let_expr List.toArray _ t := rhs
    | throwError m!"hex_payload_bridge: right side is not `List.toArray t`: {rhs}"
  let rendered := mkApp (mkConst ``String.toUTF8)
    (mkApp (mkConst ``String.ofList) (mkApp (mkConst ``hexRender) t))
  let eqTy := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``ByteArray) p rendered
  let aux ← mkAuxLemma [] eqTy (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``ByteArray) p)
  g.assign (mkApp3 (mkConst ``decode_eq_of_payload_eq) p t (mkConst aux))
  return []

end HypercubicDimension16HexPayloadBridge
end YangMills
end QuantumTheory
end Mettapedia
