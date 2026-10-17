import Mettapedia.Computability.AuthoredListFraming
import Mettapedia.Computability.FramedWordMapping
import Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming
import Mettapedia.Languages.HOLLight.ClaimCheckingMachine

/-!
# Physical union of original authored axiom provenance

A fixed sorted basis contains the original authored axiom sequents. Incoming
axiom sets are read through their original binary codec, framed without arity
specialization, validated by complete dictionary words and united once in that
same codec order. This is a fixed-basis descriptor, whose literal bytes and
finite-register representation remain explicit; no enumerated-control-table
or specification-uniform bound is asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.AuthoredAxiomUnion
open Turing Polynomial StateTransition
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open FiniteWordClassifier

abbrev Basis := Finset Sequent
def ordered (basis : Basis) : List Sequent := basis.sort (encodedLe sequentCodec)
abbrev Index (basis : Basis) := Fin (ordered basis).length
def dictionary (basis : Basis) (index : Index basis) : Data := sequentCodec.put ((ordered basis).get index)
def words (basis : Basis) (index : Index basis) : List Alphabet := encodeData (dictionary basis index)

theorem dictionary_known (basis : Basis) (values : Finset Sequent) (within : values ⊆ basis)
    (value : Sequent) (member : value ∈ values.sort (encodedLe sequentCodec)) :
    ∃ index, dictionary basis index = sequentCodec.put value := by
  have included : value ∈ ordered basis := (Finset.mem_sort _).mpr (within ((Finset.mem_sort _).mp member))
  rcases List.mem_iff_get.mp included with ⟨index,same⟩
  exact ⟨index,congrArg sequentCodec.put same⟩

theorem words_injective (basis : Basis) : Function.Injective (words basis) := by
  intro first second same
  have actual := Codec.put_injective sequentCodec (encodeData_injective same)
  exact (List.nodup_iff_injective_get.mp (Finset.sort_nodup basis (encodedLe sequentCodec))) actual

theorem dictionary_framed (basis : Basis) (values : Finset Sequent) (within : values ⊆ basis) :
    ((values.sort (encodedLe sequentCodec)).map (encodeWith sequentCodec)).all
      (fun word => (classify (words basis) word).isSome) = true := by
  apply List.all_eq_true.mpr
  intro word member
  rcases List.mem_map.mp member with ⟨value,member,same⟩
  rcases dictionary_known basis values within value member with ⟨index,actual⟩
  have wordSame : words basis index = encodeWith sequentCodec value := congrArg encodeData actual
  subst word
  rw [← wordSame,Union.classify_self (words basis) (words_injective basis)]
  rfl

/-- The union machine's ordered emission is the filtered authored word vector. -/
theorem emitWire_filter {n : Nat} (table : Fin n → List Alphabet) (seen : Fin n → Bool) (cursor : Nat) :
    Union.emitWire table seen cursor = Indexed.frame
      (((List.finRange n).drop cursor).filter seen |>.map table) := by
  by_cases inside : cursor < n
  · have position : cursor < (List.finRange n).length := by simpa using inside
    have point : (List.finRange n).get ⟨cursor,position⟩ = ⟨cursor,inside⟩ := by apply Fin.ext; simp
    rw [List.get_eq_getElem] at point
    rw [List.drop_eq_getElem_cons position,point]
    rw [Union.emitWire]
    simp only [dif_pos inside,List.filter_cons]
    cases selected : seen ⟨cursor,inside⟩ with
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte,List.nil_append]
      exact emitWire_filter table seen (cursor+1)
    | true =>
      simp only [↓reduceIte,List.map_cons,Indexed.frame,List.flatMap_cons]
      rw [emitWire_filter table seen (cursor+1)]
      rfl
  · rw [Union.emitWire]
    simp only [dif_neg inside]
    have empty : (List.finRange n).drop cursor = [] := List.drop_eq_nil_iff.mpr (by simpa using Nat.le_of_not_gt inside)
    rw [empty]
    rfl
termination_by n-cursor

/-- Filtering a sorted basis reconstructs the original finite-set codec order. -/
theorem sorted_subset (basis values : Basis) (within : values ⊆ basis) :
    (ordered basis).filter (fun value => decide (value ∈ values)) = values.sort (encodedLe sequentCodec) := by
  let picked := (ordered basis).filter (fun value => decide (value ∈ values))
  have support : picked.toFinset = values := by
    ext value
    simp only [picked,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,ordered,Finset.mem_sort]
    exact and_iff_right_of_imp (fun member => within member)
  have nodup := (Finset.sort_nodup basis (encodedLe sequentCodec)).filter (fun value => decide (value ∈ values))
  have order := (Finset.pairwise_sort basis (encodedLe sequentCodec)).filter (fun value => decide (value ∈ values))
  have same := (List.toFinset_sort (encodedLe sequentCodec) nodup).mpr order
  change picked.toFinset.sort (encodedLe sequentCodec) = picked at same
  rw [support] at same
  exact same.symm

/-- A successful dictionary union has exactly the original sorted union bytes. -/
theorem union_result (basis left right : Basis) (leftWithin : left ⊆ basis) (rightWithin : right ⊆ basis) :
    Union.result (words basis) (0 : Alphabet) 1
      (Indexed.frame ((left.sort (encodedLe sequentCodec) ++ right.sort (encodedLe sequentCodec)).map (encodeWith sequentCodec))) =
    some 1 :: Indexed.frame (((left ∪ right).sort (encodedLe sequentCodec)).map (encodeWith sequentCodec)) := by
  let values := (left.sort (encodedLe sequentCodec) ++ right.sort (encodedLe sequentCodec)).map (encodeWith sequentCodec)
  have known : values.all (fun word => (classify (words basis) word).isSome) = true := by
    simp only [values,List.map_append,List.all_append,dictionary_framed basis left leftWithin,
      dictionary_framed basis right rightWithin,Bool.and_true]
  have seen : (Union.foldWords (words basis) values (Union.initial (words basis))).seen =
      fun index => decide ((ordered basis).get index ∈ left ∪ right) := by
    funext index
    apply Bool.eq_iff_iff.mpr
    have detected := Union.seen_frame_iff (words basis) (words_injective basis) values index
    rw [Union.walk_frame _ _ _ rfl] at detected
    rw [detected]
    simp only [values,words,dictionary,encodeWith,List.map_append,List.mem_append,List.mem_map,
      encodeData_injective.eq_iff,Codec.put_injective sequentCodec |>.eq_iff,Finset.mem_sort,Finset.mem_union,decide_eq_true_eq]
    aesop
  have collected := Union.result_frame (words basis) (0 : Alphabet) 1 values
  change Union.result _ _ _ _ = _
  rw [show Union.frame values = Indexed.frame values from rfl] at collected
  rw [collected,known]
  simp only [ite_true]
  rw [seen,emitWire_filter]
  simp only [List.drop_zero]
  have orderedResult : ((List.finRange (ordered basis).length).filter
      (fun index => decide ((ordered basis).get index ∈ left ∪ right))).map (words basis) =
      ((left ∪ right).sort (encodedLe sequentCodec)).map (encodeWith sequentCodec) := by
    have mapped : ((List.finRange (ordered basis).length).filter
        (fun index => decide ((ordered basis).get index ∈ left ∪ right))).map (words basis) =
        ((ordered basis).filter (fun value => decide (value ∈ left ∪ right))).map (encodeWith sequentCodec) := by
      unfold words dictionary
      have aligned : (List.finRange (ordered basis).length).map (ordered basis).get = ordered basis := by
        rw [← List.ofFn_eq_map]
        exact List.ofFn_get _
      conv_rhs => rw [← aligned]
      simp only [List.filter_map,List.map_map]
      rfl
    rw [mapped,sorted_subset basis (left∪right) (Finset.union_subset leftWithin rightWithin)]
  rw [orderedResult]


def framed (values : Basis) : List (Option Alphabet) :=
  Indexed.frame ((values.sort (encodedLe sequentCodec)).map (encodeWith sequentCodec))
def source (values : Basis) : List Alphabet := encodeWith (finsetCodec sequentCodec) values

/-- Unknown original axiom words remain an unknown frame for downstream union refusal. -/
def rawIdentity : FinTM2 := WordHomomorphismMachine.machine (fun cell : Option Alphabet => [cell])
local instance : Fintype (rawIdentity.Γ rawIdentity.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (rawIdentity.Γ rawIdentity.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def accept (cell : Option Alphabet) : Bool := decide (cell = some 1)
def strippedFramer := StackMachineComposition.Dispatch.machine rawIdentity accept [some 0,none]
local instance : Fintype (strippedFramer.Γ strippedFramer.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (strippedFramer.Γ strippedFramer.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance (basis : Basis) : Fintype ((AuthoredListFraming.machine (dictionary basis)).Γ
    (AuthoredListFraming.machine (dictionary basis)).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (basis : Basis) : Inhabited ((AuthoredListFraming.machine (dictionary basis)).Γ
    (AuthoredListFraming.machine (dictionary basis)).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def scanner (basis : Basis) : FinTM2 := StackMachineComposition.machine
  (AuthoredListFraming.machine (dictionary basis)) strippedFramer (Equiv.refl (Option Alphabet))
local instance (basis : Basis) : Fintype ((scanner basis).Γ (scanner basis).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (basis : Basis) : Inhabited ((scanner basis).Γ (scanner basis).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance (basis : Basis) : Inhabited ((scanner basis).Γ (scanner basis).k₀) := inferInstanceAs (Inhabited Alphabet)

def scannerClock (values : Basis) : Nat := 10*(source values).length+10

noncomputable def scannerOutputs (basis values : Basis) (within : values ⊆ basis) :
    TM2OutputsInTime (scanner basis) (source values) (some (framed values)) (scannerClock values) := by
  have parsed := AuthoredListFraming.codecOutputs sequentCodec (dictionary basis)
    (values.sort (encodedLe sequentCodec)) (dictionary_known basis values within)
  change TM2OutputsInTime (AuthoredListFraming.machine (dictionary basis)) (source values)
    (some (some 1::framed values)) (3*(source values).length+2) at parsed
  have identity := WordHomomorphismMachine.outputs (fun cell : Option Alphabet => [cell]) (framed values)
  simp only [List.flatMap_singleton'] at identity
  have stripped := StackMachineComposition.Dispatch.outputs_success rawIdentity accept [some 0,none]
    (some 1) (framed values) (framed values) (4*(framed values).length+2) (by decide) (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine (fun cell : Option Alphabet => [cell])) _ _ _
      convert identity using 1
      omega)
  have joined := StackMachineComposition.outputs (AuthoredListFraming.machine (dictionary basis)) strippedFramer
    (Equiv.refl (Option Alphabet)) (source values) (some 1::framed values) (framed values) _ _ parsed (by
      change TM2OutputsInTime strippedFramer ((some 1::framed values).map id) _ _
      simpa only [List.map_id,strippedFramer] using stripped)
  have size := CertificateArgumentFraming.framedArguments_length sequentCodec (values.sort (encodedLe sequentCodec))
  change (framed values).length+2 = (source values).length at size
  apply WordEqualityMachine.within joined
  simp only [List.length_cons,scannerClock]
  omega

/-- Outside mapper boundaries are removed; inside axiom occurrence delimiters remain. -/
def flatten : Option (Option Alphabet) → List (Option Alphabet)
  | none => []
  | some cell => [cell]

theorem flatten_frame (values : List (List (Option Alphabet))) :
    (Indexed.frame values).flatMap flatten = values.flatten := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    have single : (value.map some).flatMap flatten = value := by
      induction value with
      | nil => rfl
      | cons cell value inner => simpa [flatten] using congrArg (List.cons cell) inner
    change ((value.map some ++ [none]) ++ Indexed.frame values).flatMap flatten = value++values.flatten
    rw [List.flatMap_append,List.flatMap_append,single,ih]
    simp [flatten]


local instance (basis : Basis) : Fintype ((FramedWordMapping.machine (scanner basis)).Γ
    (FramedWordMapping.machine (scanner basis)).k₁) := inferInstanceAs (Fintype (Option (Option Alphabet)))
local instance (basis : Basis) : Inhabited ((FramedWordMapping.machine (scanner basis)).Γ
    (FramedWordMapping.machine (scanner basis)).k₁) := inferInstanceAs (Inhabited (Option (Option Alphabet)))
def preparedMachine (basis : Basis) : FinTM2 := StackMachineComposition.machine
  (FramedWordMapping.machine (scanner basis)) (WordHomomorphismMachine.machine flatten)
    (Equiv.refl (Option (Option Alphabet)))

abbrev Supported (basis : Basis) := { values : Basis // values ⊆ basis }
def pairClock (basis left right : Basis) (leftWithin : left ⊆ basis) (rightWithin : right ⊆ basis) : Nat :=
  let values : List (Supported basis) := [⟨left,leftWithin⟩,⟨right,rightWithin⟩]
  let vector := Indexed.frame [framed left,framed right]
  FramedWordMapping.totalClock (scanner basis) (fun value : Supported basis => source value.1)
    (fun value => framed value.1) (fun value => scannerClock value.1) values +
    4*vector.length+2*(framed left++framed right).length+4

noncomputable def preparedOutputs (basis left right : Basis) (leftWithin : left ⊆ basis) (rightWithin : right ⊆ basis) :
    TM2OutputsInTime (preparedMachine basis) (Indexed.frame [source left,source right])
      (some (framed left++framed right)) (pairClock basis left right leftWithin rightWithin) := by
  let values : List (Supported basis) := [⟨left,leftWithin⟩,⟨right,rightWithin⟩]
  have mapped := FramedWordMapping.outputs (scanner basis) (fun value : Supported basis => source value.1)
    (fun value => framed value.1) (fun value => scannerClock value.1)
    (fun value => scannerOutputs basis value.1 value.2) values
  change TM2OutputsInTime (FramedWordMapping.machine (scanner basis)) (Indexed.frame [source left,source right])
    (some (Indexed.frame [framed left,framed right])) _ at mapped
  have flattened := WordHomomorphismMachine.outputs flatten (Indexed.frame [framed left,framed right])
  rw [flatten_frame] at flattened
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil] at flattened
  have joined := StackMachineComposition.outputs (FramedWordMapping.machine (scanner basis))
    (WordHomomorphismMachine.machine flatten) (Equiv.refl (Option (Option Alphabet)))
    (Indexed.frame [source left,source right]) (Indexed.frame [framed left,framed right])
    (framed left++framed right) _ _ mapped (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine flatten) ((Indexed.frame [framed left,framed right]).map id) _ _
      simpa only [List.map_id] using flattened)
  apply WordEqualityMachine.within joined
  dsimp only [pairClock,values]
  omega


local instance (basis : Basis) : Fintype ((Union.machine (words basis) (0 : Alphabet) 1).Γ
    (Union.machine (words basis) (0 : Alphabet) 1).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (basis : Basis) : Inhabited ((Union.machine (words basis) (0 : Alphabet) 1).Γ
    (Union.machine (words basis) (0 : Alphabet) 1).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def assembler := StackMachineComposition.Dispatch.machine CertificateArgumentFraming.ListAssembly.machine accept [(0 : Alphabet)]
local instance : Fintype (assembler.Γ assembler.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (assembler.Γ assembler.k₁) := inferInstanceAs (Inhabited Alphabet)
def core (basis : Basis) : FinTM2 := StackMachineComposition.machine
  (Union.machine (words basis) (0 : Alphabet) 1) assembler (Equiv.refl (Option Alphabet))
attribute [local implicit_reducible] rawIdentity strippedFramer scanner preparedMachine assembler core
local instance (basis : Basis) : Fintype ((core basis).Γ (core basis).k₁) := inferInstanceAs (Fintype Alphabet)
local instance (basis : Basis) : Inhabited ((core basis).Γ (core basis).k₁) := inferInstanceAs (Inhabited Alphabet)

def coreClock (basis left right : Basis) : Nat :=
  (framed left++framed right).length +
    2*((ordered basis).length*(Union.basisBytes (words basis)+2)) +
    5*(framed (left∪right)).length+20

noncomputable def coreOutputs (basis left right : Basis) (leftWithin : left ⊆ basis) (rightWithin : right ⊆ basis) :
    TM2OutputsInTime (core basis) (framed left++framed right)
      (some ((1 : Alphabet)::source (left∪right))) (coreClock basis left right) := by
  have united := Union.outputs (words basis) (0 : Alphabet) 1 (framed left++framed right)
  have computed := union_result basis left right leftWithin rightWithin
  have framing : framed left++framed right = Indexed.frame
      ((left.sort (encodedLe sequentCodec)++right.sort (encodedLe sequentCodec)).map (encodeWith sequentCodec)) := by
    simp only [List.map_append,Indexed.frame,List.flatMap_append,framed]
  rw [← framing] at computed
  change Union.result _ _ _ _ = some 1::framed (left∪right) at computed
  rw [computed] at united
  have assembled := CertificateArgumentFraming.ListAssembly.outputs
    (((left∪right).sort (encodedLe sequentCodec)).map (encodeWith sequentCodec))
  rw [CertificateArgumentFraming.ListAssembly.wire_codec] at assembled
  change TM2OutputsInTime CertificateArgumentFraming.ListAssembly.machine (framed (left∪right))
    (some ((1 : Alphabet)::source (left∪right))) (3*(framed (left∪right)).length+4) at assembled
  have dispatched := StackMachineComposition.Dispatch.outputs_success CertificateArgumentFraming.ListAssembly.machine
    accept [(0 : Alphabet)] (some 1) (framed (left∪right)) ((1 : Alphabet)::source (left∪right)) _ (by decide) assembled
  have joined := StackMachineComposition.outputs (Union.machine (words basis) (0 : Alphabet) 1)
    assembler (Equiv.refl (Option Alphabet)) (framed left++framed right)
    (some 1::framed (left∪right)) ((1 : Alphabet)::source (left∪right)) _ _ united (by
      change TM2OutputsInTime assembler ((some 1::framed (left∪right)).map id) _ _
      simpa only [List.map_id,assembler] using dispatched)
  apply WordEqualityMachine.within joined
  simp only [coreClock,List.length_cons]
  omega

local instance (basis : Basis) : Fintype ((preparedMachine basis).Γ (preparedMachine basis).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (basis : Basis) : Inhabited ((preparedMachine basis).Γ (preparedMachine basis).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
def machine (basis : Basis) : FinTM2 := StackMachineComposition.machine (preparedMachine basis)
  (core basis) (Equiv.refl (Option Alphabet))

attribute [local implicit_reducible] machine
def clock (basis left right : Basis) (leftWithin : left ⊆ basis) (rightWithin : right ⊆ basis) : Nat :=
  pairClock basis left right leftWithin rightWithin + 2*(framed left++framed right).length+2 + coreClock basis left right

/-- Actual original incoming axiom bytes produce the original union codec and a success status. -/
noncomputable def outputs (basis left right : Basis) (leftWithin : left ⊆ basis) (rightWithin : right ⊆ basis) :
    TM2OutputsInTime (machine basis) (Indexed.frame [source left,source right])
      (some ((1 : Alphabet)::source (left∪right))) (clock basis left right leftWithin rightWithin) := by
  have joined := StackMachineComposition.outputs (preparedMachine basis) (core basis) (Equiv.refl (Option Alphabet))
    (Indexed.frame [source left,source right]) (framed left++framed right) ((1 : Alphabet)::source (left∪right)) _ _
    (preparedOutputs basis left right leftWithin rightWithin) (by
      change TM2OutputsInTime (core basis) ((framed left++framed right).map id) _ _
      simpa only [List.map_id] using coreOutputs basis left right leftWithin rightWithin)
  exact joined

/-- Literal authored bytes are retained once in dictionary order. -/
def basisBytes (basis : Basis) : Nat := Union.basisBytes (words basis)

end Mettapedia.Languages.HOLLight.AuthoredAxiomUnion
