import Mettapedia.Computability.BinaryWordAddition
import Mettapedia.Computability.FramedWordMapping
import Mettapedia.Computability.WordHomomorphismMachine
import Mettapedia.OSLF.Syntax.BindingWireBinary

/-!
# Executed addition of original graph-address words

An original binary natural-codec field stores an atom marker, arbitrary binary
digits and a terminator. This machine reads two such fields, projects their
actual digits, runs the physical carry machine, and writes the original
natural codec for their sum. Addresses remain unbounded stack data.

The execution theorem covers the original codec images. Admission of arbitrary
malformed address packets belongs to the surrounding graph decoder. This
stage supplies addition for block relocation; it does not relocate a graph.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.GraphAddressAddition
open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
abbrev Alphabet := Binary.Alphabet
open BinaryStackArithmetic (naturalBits)

def natWord (n : Nat) : List Alphabet := encodeWith Codec.nat n
def bits (n : Nat) : List (Option Bool) := (naturalBits n).map some
def fields (left right : Nat) : Fin 2 → List Alphabet := ![natWord left,natWord right]
def inputWire (left right : Nat) := Indexed.argumentWire (fields left right)
def bitImage (symbol : Alphabet) : List (Option Bool) :=
  if symbol.val = 0 then [some false] else if symbol.val = 1 then [some true] else []

theorem flatMap_singleton_image {A B : Type} (f : A → B) (xs : List A) :
    xs.flatMap (fun x => [f x]) = xs.map f := by
  induction xs <;> simp_all

theorem natWord_bits (n : Nat) : (natWord n).flatMap bitImage = bits n := by
  have marker : bitImage 3 = [] := rfl
  have terminator : bitImage 2 = [] := rfl
  simp only [natWord,Binary.encodeWith,Codec.nat,encodeData_atom,natural,List.flatMap_cons,
    List.flatMap_append,List.flatMap_map,List.flatMap_nil,marker,terminator,List.nil_append,List.append_nil]
  rw [bits,naturalBits,List.map_map]
  rw [← flatMap_singleton_image]
  apply List.flatMap_congr
  intro digit member
  have bound := Nat.digits_lt_base (by decide : 1<2) member
  have alternatives : digit=0 ∨ digit=1 := by omega
  rcases alternatives with rfl | rfl <;> rfl

theorem bits_length (n : Nat) : (bits n).length ≤ (natWord n).length := by
  simp only [bits,naturalBits,natWord,Binary.encodeWith,Codec.nat,encodeData_atom,natural,
    List.length_map,List.length_cons,List.length_append,List.length_nil]
  omega

attribute [local implicit_reducible] WordHomomorphismMachine.machine
  FramedWordMapping.machine Indexed.machine StackMachineComposition.machine WordTemplateMachine.machine
def bitMachine := WordHomomorphismMachine.machine bitImage
attribute [local implicit_reducible] bitMachine
local instance : Fintype (bitMachine.Γ bitMachine.k₁) := inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (bitMachine.Γ bitMachine.k₀) := inferInstanceAs (Inhabited Alphabet)
local instance : Inhabited (bitMachine.Γ bitMachine.k₁) := inferInstanceAs (Inhabited (Option Bool))
def mappedMachine := FramedWordMapping.machine bitMachine
def mappedWire (left right : Nat) := Indexed.frame [bits left,bits right]
def sumTemplate : Indexed.Template (Option Bool) 2 := [.inr 0,.inl none,.inr 1]
local instance : Fintype (mappedMachine.Γ mappedMachine.k₁) := inferInstanceAs (Fintype (Option (Option Bool)))
local instance : Inhabited (mappedMachine.Γ mappedMachine.k₁) := inferInstanceAs (Inhabited (Option (Option Bool)))
def preparedMachine := StackMachineComposition.machine mappedMachine (Indexed.machine sumTemplate)
  (Equiv.refl (Option (Option Bool)))
attribute [local implicit_reducible] mappedMachine preparedMachine
local instance : Fintype (preparedMachine.Γ preparedMachine.k₁) := inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (preparedMachine.Γ preparedMachine.k₁) := inferInstanceAs (Inhabited (Option Bool))
local instance : Fintype (BinaryWordAddition.machine.Γ BinaryWordAddition.machine.k₁) := inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (BinaryWordAddition.machine.Γ BinaryWordAddition.machine.k₁) := inferInstanceAs (Inhabited (Option Bool))
def addedMachine := StackMachineComposition.machine preparedMachine BinaryWordAddition.machine
  (Equiv.refl (Option Bool))
attribute [local implicit_reducible] addedMachine
local instance : Fintype (addedMachine.Γ addedMachine.k₁) := inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (addedMachine.Γ addedMachine.k₁) := inferInstanceAs (Inhabited (Option Bool))

def digitImage : Option Bool → List Alphabet
  | none => [4]
  | some bit => [if bit then 1 else 0]
def digitWord (n : Nat) := (naturalBits n).map (fun bit => if bit then (1:Alphabet) else 0)
theorem digit_natural (n : Nat) : digitWord n ++ [2] = natural n := by
  simp only [digitWord,naturalBits,natural,List.map_map]
  congr 1
  apply List.map_congr_left
  intro digit member
  have bound := Nat.digits_lt_base (by decide : 1<2) member
  have alternatives : digit=0 ∨ digit=1 := by omega
  rcases alternatives with rfl | rfl <;> rfl
theorem digit_projection (n : Nat) : (bits n).flatMap digitImage = digitWord n := by
  simp only [bits,digitWord,List.flatMap_map,digitImage]
  exact flatMap_singleton_image _ _
def digitMachine := WordHomomorphismMachine.machine digitImage
def digitOutputs (n : Nat) : TM2OutputsInTime digitMachine (bits n) (some (digitWord n))
    (2*(bits n).length+2*(digitWord n).length+2) := by
  have ran := WordHomomorphismMachine.outputs digitImage (bits n)
  rw [digit_projection] at ran
  exact ran
def projectedMachine := StackMachineComposition.machine addedMachine digitMachine (Equiv.refl (Option Bool))
attribute [local implicit_reducible] digitMachine projectedMachine
local instance : Fintype (projectedMachine.Γ projectedMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (projectedMachine.Γ projectedMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
def finalTemplate : WordTemplateMachine.Template Alphabet := [some 3,none,some 2]
def machine := StackMachineComposition.machine projectedMachine (WordTemplateMachine.machine finalTemplate) (Equiv.refl Alphabet)

def mappedClock (left right : Nat) := 8*(inputWire left right).length+14
def preparedClock (left right : Nat) := mappedClock left right + 2*(mappedWire left right).length+2 +
  16*((mappedWire left right).length+1)
def addedClock (left right : Nat) := preparedClock left right +
  7*(BinaryWordAddition.encodedInput (left,right)).length+10
def projectedClock (left right : Nat) := addedClock left right + 6*(bits (left+right)).length+4
def clock (left right : Nat) := projectedClock left right + 2*(digitWord (left+right)).length+2 +
  16*((digitWord (left+right)).length+1)

def bitOutputs (n : Nat) : TM2OutputsInTime bitMachine (natWord n) (some (bits n)) (4*(natWord n).length+2) := by
  have ran := WordHomomorphismMachine.outputs bitImage (natWord n)
  rw [natWord_bits] at ran
  exact WordEqualityMachine.within ran (by have bound := bits_length n; omega)

noncomputable def mappedOutputs (left right : Nat) :
    TM2OutputsInTime mappedMachine (inputWire left right) (some (mappedWire left right)) (mappedClock left right) := by
  have ran := FramedWordMapping.outputs bitMachine natWord bits (fun n => 4*(natWord n).length+2) bitOutputs [left,right]
  have inputSame : Indexed.frame ([left,right].map natWord) = inputWire left right := by
    simp [inputWire,fields,Indexed.argumentWire,Indexed.frame,List.finRange_succ]
  have outSame : Indexed.frame ([left,right].map bits) = mappedWire left right := rfl
  rw [inputSame,outSame] at ran
  apply WordEqualityMachine.within ran
  have first := bits_length left
  have second := bits_length right
  simp only [FramedWordMapping.totalClock,FramedWordMapping.vectorClock,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    mappedWire,Indexed.frame,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,List.length_map,
    List.length_cons,List.length_nil,mappedClock,inputWire,fields,Indexed.argumentWire,List.finRange_succ,
    List.finRange_zero,Matrix.cons_val_zero,Matrix.cons_val_succ] at *
  omega

noncomputable def preparedOutputs (left right : Nat) : TM2OutputsInTime preparedMachine (inputWire left right)
    (some (BinaryWordAddition.encodedInput (left,right))) (preparedClock left right) := by
  let words : Fin 2 → List (Option Bool) := ![bits left,bits right]
  have ran := Indexed.outputs sumTemplate words
  have inputSame : Indexed.argumentWire words = mappedWire left right := by
    simp [words,Indexed.argumentWire,mappedWire,List.finRange_succ,Indexed.frame]
  have outSame : Indexed.instantiate sumTemplate words = BinaryWordAddition.encodedInput (left,right) := by
    simp [words,sumTemplate,Indexed.instantiate,BinaryWordAddition.encodedInput,BinaryWordAddition.packet,bits]
  rw [inputSame,outSame] at ran
  have joined := StackMachineComposition.outputs mappedMachine (Indexed.machine sumTemplate) (Equiv.refl (Option (Option Bool)))
    (inputWire left right) (mappedWire left right) (BinaryWordAddition.encodedInput (left,right)) _ _ (mappedOutputs left right) (by
      change TM2OutputsInTime (Indexed.machine sumTemplate) ((mappedWire left right).map id) _ _
      simpa only [List.map_id] using ran)
  simpa [preparedMachine,preparedClock,sumTemplate] using joined

noncomputable def addedOutputs (left right : Nat) : TM2OutputsInTime addedMachine (inputWire left right)
    (some (bits (left+right))) (addedClock left right) := by
  have joined := StackMachineComposition.outputs preparedMachine BinaryWordAddition.machine (Equiv.refl (Option Bool))
    (inputWire left right) (BinaryWordAddition.encodedInput (left,right)) (bits (left+right)) _ _ (preparedOutputs left right) (by
      change TM2OutputsInTime BinaryWordAddition.machine ((BinaryWordAddition.encodedInput (left,right)).map id) _ _
      simpa only [List.map_id,bits] using BinaryWordAddition.naturalOutputs left right)
  convert joined using 1
  · rfl
  · simp only [addedClock]; omega

noncomputable def projectedOutputs (left right : Nat) : TM2OutputsInTime projectedMachine (inputWire left right)
    (some (digitWord (left+right))) (projectedClock left right) := by
  have ran := digitOutputs (left+right)
  have joined := StackMachineComposition.outputs addedMachine digitMachine (Equiv.refl (Option Bool))
    (inputWire left right) (bits (left+right)) (digitWord (left+right)) _ _ (addedOutputs left right) (by
      change TM2OutputsInTime digitMachine ((bits (left+right)).map id) _ _
      simpa only [List.map_id] using ran)
  apply WordEqualityMachine.within joined
  simp only [projectedClock,digitWord,bits,List.length_map]
  omega

noncomputable def outputs (left right : Nat) : TM2OutputsInTime machine (inputWire left right)
    (some (natWord (left+right))) (clock left right) := by
  have ran := WordTemplateMachine.outputs finalTemplate (digitWord (left+right))
  have outputSame : WordTemplateMachine.instantiate finalTemplate (digitWord (left+right)) = natWord (left+right) := by
    simp only [finalTemplate,instantiate_literal,instantiate_hole,instantiate_nil,natWord,
      Binary.encodeWith,Codec.nat,encodeData_atom]
    rw [digit_natural]
  rw [outputSame] at ran
  have joined := StackMachineComposition.outputs projectedMachine (WordTemplateMachine.machine finalTemplate) (Equiv.refl Alphabet)
    (inputWire left right) (digitWord (left+right)) (natWord (left+right)) _ _ (projectedOutputs left right) (by
      change TM2OutputsInTime (WordTemplateMachine.machine finalTemplate) ((digitWord (left+right)).map id) _ _
      simpa only [List.map_id] using ran)
  simpa [machine,clock,finalTemplate] using joined

theorem input_length (left right : Nat) : (inputWire left right).length =
    (natWord left).length + (natWord right).length + 2 := by
  simp [inputWire,fields,Indexed.argumentWire,Indexed.frame,List.finRange_succ,Nat.add_assoc]

theorem clock_linear (left right : Nat) : clock left right ≤ 57*(inputWire left right).length+64 := by
  have inputSize := input_length left right
  have first := bits_length left
  have second := bits_length right
  have mappedSize : (mappedWire left right).length ≤ (inputWire left right).length := by
    simp only [mappedWire,Indexed.frame,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,
      List.length_map,List.length_cons,List.length_nil]
    omega
  have addedSize : (BinaryWordAddition.encodedInput (left,right)).length ≤ (inputWire left right).length := by
    simp only [BinaryWordAddition.encodedInput,BinaryWordAddition.packet,List.length_append,List.length_map,List.length_cons]
    simp only [bits,List.length_map] at first second
    omega
  have carry := BinaryWordAddition.naturalBits_add_length left right
  have sumSize : (bits (left+right)).length ≤ (inputWire left right).length := by
    simp only [bits,List.length_map] at first second ⊢
    omega
  have digitSize : (digitWord (left+right)).length = (bits (left+right)).length := by
    simp [digitWord,bits]
  unfold clock projectedClock addedClock preparedClock mappedClock
  rw [digitSize]
  omega

noncomputable def linearOutputs (left right : Nat) : TM2OutputsInTime machine (inputWire left right)
    (some (natWord (left+right))) (57*(inputWire left right).length+64) :=
  WordEqualityMachine.within (outputs left right) (clock_linear left right)

theorem run_readout (left right : Nat) {word : List Alphabet}
    (finished : TM2Outputs machine (inputWire left right) (some word)) : word = natWord (left+right) :=
  StackMachineComposition.outputs_unique finished (outputs left right).toEvalsTo

theorem run_decodes (left right : Nat) {word : List Alphabet}
    (finished : TM2Outputs machine (inputWire left right) (some word)) :
    decodeWith Codec.nat word = some (left+right) := by
  rw [run_readout left right finished]
  exact decodeWith_encodeWith Codec.nat (left+right)

theorem wrong_address_impossible (left right proposed : Nat) {word : List Alphabet}
    (finished : TM2Outputs machine (inputWire left right) (some word))
    (different : proposed ≠ left+right) : decodeWith Codec.nat word ≠ some proposed := by
  rw [run_decodes left right finished]
  intro same
  exact different (Option.some.inj same).symm

noncomputable def realization : TM2ComputableInPolyTime
    (fun input : Nat × Nat => inputWire input.1 input.2) natWord (fun input => input.1+input.2) where
  tm := machine
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := Polynomial.C 57 * Polynomial.X + Polynomial.C 64
  outputsFun input := by
    change TM2OutputsInTime machine ((inputWire input.1 input.2).map id)
      (some ((natWord (input.1+input.2)).map id)) _
    simp only [List.map_id,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    exact linearOutputs input.1 input.2

namespace Controls
theorem zero_word : natWord 0 = [3,2] := rfl
theorem carry_word : natWord ((2^128-1)+1) = natWord (2^128) := by
  congr 1
theorem carry_changes_length : (natWord (2^128)).length > (natWord (2^128-1)).length := by
  decide +kernel
theorem incorrect_one_refused : decodeWith Codec.nat (natWord (7+58)) ≠ some 64 := by
  rw [natWord,decodeWith_encodeWith]
  decide
theorem trailing_address_refused : decodeWith Codec.nat (natWord (7+58) ++ [0]) = none := by
  exact decodeWith_trailing_refused Codec.nat _ [0] (by decide)
end Controls

end Mettapedia.Languages.HOLLight.GraphAddressAddition
