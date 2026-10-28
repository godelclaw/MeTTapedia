import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.NormNum

/-! A fixed authored radix algebra and exact 24-bit scalar-data codec.
Words are representation data; Unicode and lexical-class formation remain
separate checks. No primitive carrier or source spelling normalization is used. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

#module_file "../../../../../../metta/gslt/module/Radix16.module"
#module_roundtrip Radix16

namespace Radix16Codec

def language? : Option LanguageDef := Radix16.language.toOption

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def language : LanguageDef := language?.get (by decide +kernel)

theorem language_exact : language? = some language := (Option.some_get _).symm

def nibble (value : Fin 16) : Pattern := .apply ("R16Nibble" ++ toString value.val) []

def readNibble? : Pattern → Option (Fin 16)
  | .apply "R16Nibble0" [] => some ⟨0, by decide⟩
  | .apply "R16Nibble1" [] => some ⟨1, by decide⟩
  | .apply "R16Nibble2" [] => some ⟨2, by decide⟩
  | .apply "R16Nibble3" [] => some ⟨3, by decide⟩
  | .apply "R16Nibble4" [] => some ⟨4, by decide⟩
  | .apply "R16Nibble5" [] => some ⟨5, by decide⟩
  | .apply "R16Nibble6" [] => some ⟨6, by decide⟩
  | .apply "R16Nibble7" [] => some ⟨7, by decide⟩
  | .apply "R16Nibble8" [] => some ⟨8, by decide⟩
  | .apply "R16Nibble9" [] => some ⟨9, by decide⟩
  | .apply "R16Nibble10" [] => some ⟨10, by decide⟩
  | .apply "R16Nibble11" [] => some ⟨11, by decide⟩
  | .apply "R16Nibble12" [] => some ⟨12, by decide⟩
  | .apply "R16Nibble13" [] => some ⟨13, by decide⟩
  | .apply "R16Nibble14" [] => some ⟨14, by decide⟩
  | .apply "R16Nibble15" [] => some ⟨15, by decide⟩
  | _ => none

theorem readNibble?_nibble (value : Fin 16) : readNibble? (nibble value) = some value := by
  fin_cases value <;> rfl

def word (n5 n4 n3 n2 n1 n0 : Fin 16) : Pattern :=
  .apply "R16Pack24" [nibble n5, nibble n4, nibble n3, nibble n2, nibble n1, nibble n0]

def decode? : Pattern → Option Nat
  | .apply "R16Pack24" [n5, n4, n3, n2, n1, n0] => do
      let a5 ← readNibble? n5
      let a4 ← readNibble? n4
      let a3 ← readNibble? n3
      let a2 ← readNibble? n2
      let a1 ← readNibble? n1
      let a0 ← readNibble? n0
      pure (((((a5.val * 16 + a4.val) * 16 + a3.val) * 16 + a2.val) * 16 + a1.val) * 16 + a0.val)
  | _ => none

def digit (value place : Nat) : Fin 16 := ⟨value / 16 ^ place % 16, Nat.mod_lt _ (by decide)⟩

def encode (value : Fin (16 ^ 6)) : Pattern :=
  word (digit value.val 5) (digit value.val 4) (digit value.val 3)
    (digit value.val 2) (digit value.val 1) (digit value.val 0)

theorem decode?_word (n5 n4 n3 n2 n1 n0 : Fin 16) :
    decode? (word n5 n4 n3 n2 n1 n0) =
      some (((((n5.val * 16 + n4.val) * 16 + n3.val) * 16 + n2.val) * 16 + n1.val) * 16 + n0.val) := by
  simp [word, decode?, readNibble?_nibble]

theorem decode?_encode (value : Fin (16 ^ 6)) :
    decode? (encode value) = some value.val := by
  rw [encode, decode?_word]
  apply congrArg some
  simp only [digit]
  norm_num
  have bounded := value.isLt
  norm_num at bounded
  omega

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode? same
  apply Fin.ext
  simpa only [decode?_encode, Option.some.injEq] using decoded

theorem nibble_typed (value : Fin 16) :
    HasType language FreeTypeContext.empty [] (nibble value) (.base "R16Nibble") := by
  apply checkHasType_sound
  fin_cases value <;> decide +kernel

theorem word_typed (n5 n4 n3 n2 n1 n0 : Fin 16) :
    HasType language FreeTypeContext.empty [] (word n5 n4 n3 n2 n1 n0) (.base "R16Word24") := by
  apply HasType.constructor (rule := language.terms[16])
  · decide +kernel
  · have length : language.terms[16].bareParams.length = 6 := by decide +kernel
    rintro ⟨parameterName, collectionKind, elementType, same⟩
    have lengths := congrArg List.length same
    rw [length] at lengths
    norm_num at lengths
  · exact .cons trivial rfl (nibble_typed n5)
      (.cons trivial rfl (nibble_typed n4)
      (.cons trivial rfl (nibble_typed n3)
      (.cons trivial rfl (nibble_typed n2)
      (.cons trivial rfl (nibble_typed n1)
      (.cons trivial rfl (nibble_typed n0) .nil)))))

theorem encode_typed (value : Fin (16 ^ 6)) :
    HasType language FreeTypeContext.empty [] (encode value) (.base "R16Word24") :=
  word_typed _ _ _ _ _ _

def wordSort : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort language :=
  ⟨"R16Word24", by decide +kernel⟩

theorem encode_closed (value : Fin (16 ^ 6)) :
    ClosedTermWellSorted language wordSort (encode value) :=
  ⟨encode_typed value, by rfl, by rfl, by rfl, (encode_typed value).isWellScopedAt⟩

def closedWord (value : Fin (16 ^ 6)) : ClosedTerm language wordSort :=
  ⟨encode value, encode_closed value⟩

theorem ast_carriers : ∀ (declaration : TypeDecl), List.Mem declaration language.types →
    declaration.carrier = .ast := by decide +kernel

theorem unicode_controls :
    decode? (encode 955) = some 955 ∧ decode? (encode 128512) = some 128512 ∧
      decode? (encode 1114111) = some 1114111 ∧
      encode 955 ≠ encode 128512 := by decide +kernel

theorem malformed_words_refused :
    decode? (.apply "R16Pack24" []) = none ∧
      readNibble? (.apply "R16Nibble16" []) = none ∧
      readNibble? (.apply "R16Nibble0" [.apply "extra" []]) = none := by decide

#print axioms language_exact
#print axioms decode?_encode
#print axioms encode_typed
#print axioms encode_closed
#print axioms unicode_controls

end Radix16Codec
end Mettapedia.GSLT.LanguageDef.ModuleFormat
