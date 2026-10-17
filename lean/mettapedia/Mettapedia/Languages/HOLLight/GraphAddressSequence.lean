import Mettapedia.Languages.HOLLight.GraphAddressAddition
import Mettapedia.Languages.HOLLight.GraphExpansion
import Mettapedia.Computability.FramedWordDecoding

/-!
# Physical sequences of relocated graph addresses

A fixed list of local block offsets is compiled into word templates. The
current graph base is runtime data in its original natural codec. Each
template copies those actual bytes, supplies its local offset, and feeds the
existing physical addition machine. The output retains every ordered address
field, including repeated offsets. The descriptor length is charged.

This stage computes the internal address vector. Selection of external roots,
rewriting block parent fields and chronological cache updates are separate
driver operations.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.GraphAddressSequence
open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
abbrev Alphabet := Binary.Alphabet
abbrev Cell := Option (Option Alphabet)
open GraphAddressAddition (natWord)
attribute [local implicit_reducible] WordHomomorphismMachine.machine WordTemplateMachine.machine
  StackMachineComposition.machine FramedWordMapping.machine

def liftImage (symbol : Alphabet) : List Cell := [some (some symbol)]
def lifted (base : Nat) : List Cell := (natWord base).map (some ∘ some)
def jobTemplate (offset : Nat) : WordTemplateMachine.Template Cell :=
  [none,some (some none)] ++ (natWord offset).map (fun symbol => some (some (some symbol))) ++
    [some (some none),some none]
def plan (offsets : List Nat) := offsets.flatMap jobTemplate
def preparedWire (offsets : List Nat) (base : Nat) :=
  Indexed.frame (offsets.map (GraphAddressAddition.inputWire base))
def resultWire (offsets : List Nat) (base : Nat) :=
  Indexed.frame (offsets.map (fun offset => natWord (base+offset)))

theorem job_instantiates (offset base : Nat) :
    WordTemplateMachine.instantiate (jobTemplate offset) (lifted base) =
      (GraphAddressAddition.inputWire base offset).map some ++ [none] := by
  simp [jobTemplate,lifted,WordTemplateMachine.instantiate,GraphAddressAddition.inputWire,
    GraphAddressAddition.fields,Indexed.argumentWire,Indexed.frame,List.finRange_succ,
    List.map_map,List.append_assoc]
  simp only [List.flatMap_map]
  exact GraphAddressAddition.flatMap_singleton_image _ _

theorem plan_instantiates (offsets : List Nat) (base : Nat) :
    WordTemplateMachine.instantiate (plan offsets) (lifted base) = preparedWire offsets base := by
  induction offsets with
  | nil => simp [plan,preparedWire,Indexed.frame]
  | cons offset rest ih =>
    simp only [plan,List.flatMap_cons,instantiate_append,job_instantiates]
    change _ ++ WordTemplateMachine.instantiate (plan rest) (lifted base) = _
    rw [ih]
    simp [preparedWire,Indexed.frame]

def liftMachine := WordHomomorphismMachine.machine liftImage
attribute [local implicit_reducible] liftMachine
def liftedOutputs (base : Nat) : TM2OutputsInTime liftMachine (natWord base) (some (lifted base))
    (4*(natWord base).length+2) := by
  have ran := WordHomomorphismMachine.outputs liftImage (natWord base)
  have same : (natWord base).flatMap liftImage = lifted base := by
    simp only [lifted]
    exact GraphAddressAddition.flatMap_singleton_image _ _
  rw [same] at ran
  convert ran using 1
  · rfl
  · simp only [lifted,List.length_map]; omega

local instance : Fintype (liftMachine.Γ liftMachine.k₁) := inferInstanceAs (Fintype Cell)
local instance : Inhabited (liftMachine.Γ liftMachine.k₁) := inferInstanceAs (Inhabited Cell)
def preparedMachine (offsets : List Nat) := StackMachineComposition.machine liftMachine
  (WordTemplateMachine.machine (plan offsets)) (Equiv.refl Cell)
attribute [local implicit_reducible] preparedMachine
local instance (offsets : List Nat) : Fintype ((preparedMachine offsets).Γ (preparedMachine offsets).k₁) := inferInstanceAs (Fintype Cell)
local instance (offsets : List Nat) : Inhabited ((preparedMachine offsets).Γ (preparedMachine offsets).k₁) := inferInstanceAs (Inhabited Cell)
local instance : Fintype (GraphAddressAddition.machine.Γ GraphAddressAddition.machine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (GraphAddressAddition.machine.Γ GraphAddressAddition.machine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (GraphAddressAddition.machine.Γ GraphAddressAddition.machine.k₁) := inferInstanceAs (Inhabited Alphabet)
def mappedMachine := FramedWordMapping.machine GraphAddressAddition.machine
def machine (offsets : List Nat) := StackMachineComposition.machine (preparedMachine offsets) mappedMachine (Equiv.refl Cell)

def preparedClock (offsets : List Nat) (base : Nat) := 6*(natWord base).length+4 +
  4*((plan offsets).length+1)*((natWord base).length+1)
def mappedClock (offsets : List Nat) (base : Nat) := 68*(preparedWire offsets base).length+2
def clock (offsets : List Nat) (base : Nat) := preparedClock offsets base +
  2*(preparedWire offsets base).length+2 + mappedClock offsets base

noncomputable def preparedOutputs (offsets : List Nat) (base : Nat) :
    TM2OutputsInTime (preparedMachine offsets) (natWord base) (some (preparedWire offsets base)) (preparedClock offsets base) := by
  have ran := WordTemplateMachine.outputs (plan offsets) (lifted base)
  rw [plan_instantiates] at ran
  have joined := StackMachineComposition.outputs liftMachine (WordTemplateMachine.machine (plan offsets)) (Equiv.refl Cell)
    (natWord base) (lifted base) (preparedWire offsets base) _ _ (liftedOutputs base) (by
      change TM2OutputsInTime (WordTemplateMachine.machine (plan offsets)) ((lifted base).map id) _ _
      simpa only [List.map_id] using ran)
  convert joined using 1
  · rfl
  · simp only [preparedClock,lifted,List.length_map]; omega

theorem nat_word_length (value : Nat) : (natWord value).length =
    (BinaryStackArithmetic.naturalBits value).length+2 := by
  simp [natWord,GraphAddressAddition.natWord,Binary.encodeWith,Codec.nat,encodeData_atom,natural,
    BinaryStackArithmetic.naturalBits,Nat.add_assoc]

theorem sum_word_length (base offset : Nat) : (natWord (base+offset)).length ≤
    (GraphAddressAddition.inputWire base offset).length := by
  have carry := BinaryWordAddition.naturalBits_add_length base offset
  rw [GraphAddressAddition.input_length,nat_word_length,nat_word_length,nat_word_length]
  omega

theorem mapped_clock_bound (offsets : List Nat) (base : Nat) :
    FramedWordMapping.totalClock GraphAddressAddition.machine (GraphAddressAddition.inputWire base)
      (fun offset => natWord (base+offset))
      (fun offset => 57*(GraphAddressAddition.inputWire base offset).length+64) offsets ≤ mappedClock offsets base := by
  induction offsets with
  | nil => simp [FramedWordMapping.totalClock,FramedWordMapping.vectorClock,mappedClock,preparedWire,Indexed.frame]
  | cons offset rest ih =>
    have length := sum_word_length base offset
    simp only [FramedWordMapping.totalClock,FramedWordMapping.vectorClock,mappedClock,preparedWire,Indexed.frame,
      List.map_cons,List.flatMap_cons,List.length_append,List.length_map,List.length_cons,List.length_nil,
      List.sum_cons] at ih ⊢
    omega

noncomputable def mappedOutputs (offsets : List Nat) (base : Nat) :
    TM2OutputsInTime mappedMachine (preparedWire offsets base) (some (resultWire offsets base)) (mappedClock offsets base) := by
  have ran := FramedWordMapping.outputs GraphAddressAddition.machine (GraphAddressAddition.inputWire base)
    (fun offset => natWord (base+offset))
    (fun offset => 57*(GraphAddressAddition.inputWire base offset).length+64)
    (GraphAddressAddition.linearOutputs base) offsets
  exact WordEqualityMachine.within ran (mapped_clock_bound offsets base)

noncomputable def outputs (offsets : List Nat) (base : Nat) : TM2OutputsInTime (machine offsets) (natWord base)
    (some (resultWire offsets base)) (clock offsets base) := by
  have joined := StackMachineComposition.outputs (preparedMachine offsets) mappedMachine (Equiv.refl Cell)
    (natWord base) (preparedWire offsets base) (resultWire offsets base) _ _ (preparedOutputs offsets base) (by
      change TM2OutputsInTime mappedMachine ((preparedWire offsets base).map id) _ _
      simpa only [List.map_id] using mappedOutputs offsets base)
  exact joined

theorem job_length (offset : Nat) : (jobTemplate offset).length = (natWord offset).length+4 := by
  simp [jobTemplate,Nat.add_assoc]
theorem plan_length (offsets : List Nat) : (plan offsets).length =
    (offsets.map (fun offset => (natWord offset).length+4)).sum := by
  simp [plan,List.length_flatMap,job_length]
theorem prepared_length (offsets : List Nat) (base : Nat) : (preparedWire offsets base).length ≤
    (plan offsets).length*((natWord base).length+1) := by
  induction offsets with
  | nil => simp [plan,preparedWire,Indexed.frame]
  | cons offset rest ih =>
    have layout := GraphAddressAddition.input_length base offset
    simp only [plan,List.flatMap_cons,List.length_append,job_length,preparedWire,Indexed.frame,
      List.map_cons,List.flatMap_cons,List.length_append,List.length_map,List.length_cons,List.length_nil] at ih ⊢
    nlinarith

def coefficient (offsets : List Nat) := 80*((plan offsets).length+1)
theorem clock_linear (offsets : List Nat) (base : Nat) : clock offsets base ≤
    coefficient offsets*((natWord base).length+1) := by
  have size := prepared_length offsets base
  unfold clock preparedClock mappedClock coefficient
  nlinarith
noncomputable def linearOutputs (offsets : List Nat) (base : Nat) : TM2OutputsInTime (machine offsets) (natWord base)
    (some (resultWire offsets base)) (coefficient offsets*((natWord base).length+1)) :=
  WordEqualityMachine.within (outputs offsets base) (clock_linear offsets base)

theorem run_readout (offsets : List Nat) (base : Nat) {word : List (Option Alphabet)}
    (finished : TM2Outputs (machine offsets) (natWord base) (some word)) : word = resultWire offsets base :=
  StackMachineComposition.outputs_unique finished (outputs offsets base).toEvalsTo

noncomputable def realization (offsets : List Nat) : TM2ComputableInPolyTime natWord (resultWire offsets) id where
  tm := machine offsets
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl (Option Alphabet)
  time := Polynomial.C (coefficient offsets)*(Polynomial.X+Polynomial.C 1)
  outputsFun base := by
    change TM2OutputsInTime (machine offsets) ((natWord base).map id) (some ((resultWire offsets base).map id)) _
    simp only [List.map_id,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X]
    exact linearOutputs offsets base

def readAddresses : List (List Alphabet) → Option (List Nat)
  | [] => some []
  | word :: words => do
    let first ← decodeWith Codec.nat word
    let rest ← readAddresses words
    pure (first :: rest)
def readOutput (word : List (Option Alphabet)) : Option (List Nat) :=
  (Indexed.decodeFrames word).bind readAddresses

theorem readAddresses_exact (values : List Nat) : readAddresses (values.map natWord) = some values := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [readAddresses,natWord,GraphAddressAddition.natWord,decodeWith_encodeWith,ih]
theorem result_readout (offsets : List Nat) (base : Nat) : readOutput (resultWire offsets base) =
    some (offsets.map (base+·)) := by
  simp only [readOutput,resultWire,Indexed.decodeFrames_frame,Option.bind_some]
  simpa only [List.map_map,Function.comp_def] using readAddresses_exact (offsets.map (base+·))

theorem run_decodes (offsets : List Nat) (base : Nat) {word : List (Option Alphabet)}
    (finished : TM2Outputs (machine offsets) (natWord base) (some word)) :
    readOutput word = some (offsets.map (base+·)) := by
  rw [run_readout offsets base finished,result_readout]

/-- An actually executed original addition supplies the exact address used
by the original graph relocation for an internal parent. -/
theorem internal_parent_address (roots : List Nat) (base index : Nat) {word : List Alphabet}
    (internal : roots.length ≤ index)
    (finished : TM2Outputs GraphAddressAddition.machine
      (GraphAddressAddition.inputWire base (index-roots.length)) (some word)) :
    decodeWith Codec.nat word = some (GraphExpansion.address roots base index) := by
  rw [GraphAddressAddition.run_decodes base (index-roots.length) finished]
  simp [GraphExpansion.address,show ¬index<roots.length by omega]

namespace Controls
theorem ordered_addresses : readOutput (resultWire [0,1,57] 7) = some [7,8,64] := by
  rw [result_readout]; rfl
theorem repeated_offsets : readOutput (resultWire [2,2,0] 7) = some [9,9,7] := by
  rw [result_readout]; rfl
theorem empty_plan : readOutput (resultWire [] 7) = some [] := by
  rw [result_readout]; rfl
theorem wrong_address_vector : readOutput (resultWire [0,1,57] 7) ≠ some [7,8,65] := by
  rw [result_readout]; decide
theorem unterminated_address_refused : readOutput [some 3] = none := rfl
theorem trailing_address_refused : readOutput (Indexed.frame [[3,2,0]]) = none := by
  decide +kernel
end Controls

end Mettapedia.Languages.HOLLight.GraphAddressSequence
