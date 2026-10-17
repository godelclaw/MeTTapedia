import Mettapedia.Languages.HOLLight.SourceQuantifierEmission
import Mettapedia.Languages.HOLLight.ScopedRuleSpecialization
import Mettapedia.Computability.FramedWordMapping

/-!
# Coherent original raw and named operands through physical field execution

Each complete canonical source field is physically projected to its raw term,
framed, and fed to the original naming machine while that same raw word is
retained. The vector caller preserves order and duplicate occurrences. Only
its outer separators are removed, leaving one original raw/named pair per
source operand. No independently supplied named word drives execution.

This stage consumes canonical fields produced by the original source renderer.
Source admission and final fixed-row specialization are separate compositions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.SourceOperandPairing
open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open ArgumentRenderingMachine PrimitiveTransport
attribute [local implicit_reducible] StackMachineComposition.machine WordHomomorphismMachine.machine WordTemplateMachine.machine

/-- Independently generated original source operands cannot alter binder names. -/
theorem applicative_empty {term : DBTerm} {source : SourceTerm}
    (shape : ArgumentNamingMachine.Applicative term source) : freeNames term=[] := by
  induction shape with
  | const => rfl
  | app first second left right => simp only [freeNames,left,right,List.nil_append]

theorem rendered_empty (pattern : Pattern) : freeNames (renderedArgument pattern).term=[] :=
  applicative_empty (ArgumentNamingMachine.rendered_shape pattern)
theorem rendered_named (pattern : Pattern) (binders : List SourceVar) :
    named? (renderedArgument pattern).term binders = some (checkedSource (renderedArgument pattern)).source :=
  ArgumentNamingMachine.named_exact (ArgumentNamingMachine.rendered_shape pattern) binders

abbrev raw (value : CanonicalTerm) : List Alphabet := encodeWith dbTermCodec value.term
abbrev namedWord (pattern : Pattern) : List Alphabet :=
  encodeWith sourceTermCodec (checkedSource (renderedArgument pattern)).source

def frameTemplate : WordTemplateMachine.Template (Option Alphabet) := [none,some none]
def liftMachine : FinTM2 := WordHomomorphismMachine.machine (fun symbol : Alphabet => [some symbol])
local instance : Fintype (liftMachine.Γ liftMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (liftMachine.Γ liftMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def frameMachine : FinTM2 := StackMachineComposition.machine liftMachine
  (WordTemplateMachine.machine frameTemplate) (Equiv.refl (Option Alphabet))
attribute [local implicit_reducible] liftMachine frameMachine

noncomputable def frameOutputs (word : List Alphabet) :
    TM2OutputsInTime frameMachine word (some (word.map some++[none])) (18*word.length+16) := by
  unfold frameMachine liftMachine
  have lifted := WordHomomorphismMachine.outputs (fun symbol : Alphabet => [some symbol]) word
  simp only [← List.map_eq_flatMap] at lifted
  have framed := WordTemplateMachine.outputs frameTemplate (word.map some)
  simp only [frameTemplate,WordTemplateMachine.instantiate_hole,WordTemplateMachine.instantiate_literal,
    WordTemplateMachine.instantiate_nil] at framed
  have joined := StackMachineComposition.outputs liftMachine (WordTemplateMachine.machine frameTemplate)
    (Equiv.refl (Option Alphabet)) word (word.map some) (word.map some++[none]) _ _ lifted (by
      change TM2OutputsInTime (WordTemplateMachine.machine frameTemplate) ((word.map some).map id) _ _
      simpa only [List.map_id,frameTemplate] using framed)
  apply WordEqualityMachine.within joined
  simp only [List.length_map,List.length_cons,List.length_nil]
  omega

local instance : Fintype (SourceQuantifierEmission.rawMachine.Γ SourceQuantifierEmission.rawMachine.k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (SourceQuantifierEmission.rawMachine.Γ SourceQuantifierEmission.rawMachine.k₁) :=
  inferInstanceAs (Inhabited Alphabet)
def rawFrameMachine : FinTM2 := StackMachineComposition.machine SourceQuantifierEmission.rawMachine frameMachine
  (Equiv.refl Alphabet)
def rawFrame (value : CanonicalTerm) : List (Option Alphabet) := (raw value).map some++[none]

noncomputable def rawFrameOutputs (value : CanonicalTerm) :
    TM2OutputsInTime rawFrameMachine (encodeWith canonicalCodec value) (some (rawFrame value))
      (40*((encodeWith canonicalCodec value).length+1)) := by
  have joined := StackMachineComposition.outputs SourceQuantifierEmission.rawMachine frameMachine
    (Equiv.refl Alphabet) (encodeWith canonicalCodec value) (raw value) (rawFrame value) _ _
    (SourceQuantifierEmission.rawOutputs value) (by
      change TM2OutputsInTime frameMachine ((raw value).map id) _ _
      simpa only [List.map_id,rawFrame] using frameOutputs (raw value))
  apply WordEqualityMachine.within joined
  have lengthBound := SourceQuantifierEmission.term_length_le value
  change (raw value).length ≤ (encodeWith canonicalCodec value).length at lengthBound
  omega

def selector : Indexed.Template Alphabet 1 := [.inr 0]
local instance : Fintype ((Indexed.machine selector).Γ (Indexed.machine selector).k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine selector).Γ (Indexed.machine selector).k₁) := inferInstanceAs (Inhabited Alphabet)
def selectedNamingMachine : FinTM2 := StackMachineComposition.machine (Indexed.machine selector)
  ArgumentNamingMachine.machine (Equiv.refl Alphabet)
local instance : Fintype (selectedNamingMachine.Γ selectedNamingMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (selectedNamingMachine.Γ selectedNamingMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (selectedNamingMachine.Γ selectedNamingMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
def namedPairMachine : FinTM2 := RetainedWordExecution.WithOutput.Framed.machine selectedNamingMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
def pairFields (pattern : Pattern) : Fin 2 → List Alphabet := ![raw (renderedArgument pattern),namedWord pattern]
def pairWire (pattern : Pattern) : List (Option Alphabet) := Indexed.argumentWire (pairFields pattern)

theorem rawFrame_eq (value : CanonicalTerm) :
    rawFrame value=Indexed.argumentWire (![raw value] : Fin 1 → List Alphabet) := by
  simp [rawFrame,Indexed.argumentWire,Indexed.frame,List.finRange_succ]
theorem pair_exact (pattern : Pattern) :
    RetainedWordExecution.WithOutput.Framed.outputWord selectedNamingMachine
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (rawFrame (renderedArgument pattern)) (namedWord pattern) =
        pairWire pattern := by
  change (rawFrame (renderedArgument pattern)).map id ++ (namedWord pattern).map some ++ [none] = _
  rw [List.map_id]
  simp [rawFrame,pairWire,pairFields,Indexed.argumentWire,Indexed.frame,List.finRange_succ,List.append_assoc]

noncomputable def selectedNamingOutputs (pattern : Pattern) :
    TM2OutputsInTime selectedNamingMachine (rawFrame (renderedArgument pattern)) (some (namedWord pattern))
      (24*((raw (renderedArgument pattern)).length+2)) := by
  have selected := Indexed.outputs selector (![raw (renderedArgument pattern)] : Fin 1 → List Alphabet)
  simp only [selector,Indexed.instantiate_hole,Indexed.instantiate_nil,List.append_nil] at selected
  rw [← rawFrame_eq] at selected
  have joined := StackMachineComposition.outputs (Indexed.machine selector) ArgumentNamingMachine.machine
    (Equiv.refl Alphabet) (rawFrame (renderedArgument pattern)) (raw (renderedArgument pattern)) (namedWord pattern)
    _ _ selected (by
      change TM2OutputsInTime ArgumentNamingMachine.machine ((raw (renderedArgument pattern)).map id) _ _
      simpa only [List.map_id] using ArgumentNamingMachine.argumentOutputs pattern)
  apply WordEqualityMachine.within joined
  simp only [rawFrame,List.length_append,List.length_map,List.length_cons,List.length_nil]
  dsimp only [raw]
  omega

noncomputable def namedPairOutputs (pattern : Pattern) :
    TM2OutputsInTime namedPairMachine (rawFrame (renderedArgument pattern)) (some (pairWire pattern))
      (100*((raw (renderedArgument pattern)).length+2)) := by
  have paired := RetainedWordExecution.WithOutput.Framed.outputs selectedNamingMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (rawFrame (renderedArgument pattern)) (namedWord pattern)
    _ (selectedNamingOutputs pattern)
  rw [pair_exact] at paired
  apply WordEqualityMachine.within paired
  have lengthSame := ArgumentNamingMachine.wire_length (ArgumentNamingMachine.rendered_shape pattern)
  change (namedWord pattern).length=(raw (renderedArgument pattern)).length at lengthSame
  simp only [rawFrame,List.length_append,List.length_map,List.length_cons,List.length_nil]
  dsimp only [raw] at lengthSame ⊢
  omega

local instance : Fintype (rawFrameMachine.Γ rawFrameMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (rawFrameMachine.Γ rawFrameMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def machine : FinTM2 := StackMachineComposition.machine rawFrameMachine namedPairMachine (Equiv.refl (Option Alphabet))

noncomputable def outputs (pattern : Pattern) :
    TM2OutputsInTime machine (encodeWith canonicalCodec (renderedArgument pattern)) (some (pairWire pattern))
      (300*((encodeWith canonicalCodec (renderedArgument pattern)).length+1)) := by
  have joined := StackMachineComposition.outputs rawFrameMachine namedPairMachine (Equiv.refl (Option Alphabet))
    (encodeWith canonicalCodec (renderedArgument pattern)) (rawFrame (renderedArgument pattern)) (pairWire pattern)
    _ _ (rawFrameOutputs (renderedArgument pattern)) (by
      change TM2OutputsInTime namedPairMachine ((rawFrame (renderedArgument pattern)).map id) _ _
      simpa only [List.map_id] using namedPairOutputs pattern)
  apply WordEqualityMachine.within joined
  have lengthBound := SourceQuantifierEmission.term_length_le (renderedArgument pattern)
  change (raw (renderedArgument pattern)).length ≤ (encodeWith canonicalCodec (renderedArgument pattern)).length at lengthBound
  simp only [rawFrame,List.length_append,List.length_map,List.length_cons,List.length_nil]
  dsimp only [raw] at lengthBound ⊢
  omega


/-- Every canonical source field produces exactly two coherent physical fields. -/
theorem pair_length (pattern : Pattern) :
    (pairWire pattern).length=2*(raw (renderedArgument pattern)).length+2 := by
  have namedLength := ArgumentNamingMachine.wire_length (ArgumentNamingMachine.rendered_shape pattern)
  change (namedWord pattern).length=(raw (renderedArgument pattern)).length at namedLength
  have layout : pairWire pattern=(raw (renderedArgument pattern)).map some++[none]++(namedWord pattern).map some++[none] := by
    simp [pairWire,pairFields,Indexed.argumentWire,Indexed.frame,List.finRange_succ,List.append_assoc]
  rw [layout]
  simp only [List.length_append,List.length_map,List.length_cons,List.length_nil,namedLength]
  omega

local instance : Fintype (machine.Γ machine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (machine.Γ machine.k₀) := inferInstanceAs (Inhabited Alphabet)
local instance : Inhabited (machine.Γ machine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def nestedMachine : FinTM2 := FramedWordMapping.machine machine

def canonicalWire (pattern : Pattern) : List Alphabet := encodeWith canonicalCodec (renderedArgument pattern)
def vectorInput (patterns : List Pattern) : List (Option Alphabet) := Indexed.frame (patterns.map canonicalWire)
def nestedWire (patterns : List Pattern) : List (Option (Option Alphabet)) := Indexed.frame (patterns.map pairWire)

theorem summed_clock (patterns : List Pattern) :
    (patterns.map (fun pattern => 300*((canonicalWire pattern).length+1)+
      2*(canonicalWire pattern).length+2*(pairWire pattern).length+4)).sum ≤ 400*(vectorInput patterns).length := by
  induction patterns with
  | nil => simp [vectorInput,Indexed.frame]
  | cons pattern rest ih =>
      have rawLength := SourceQuantifierEmission.term_length_le (renderedArgument pattern)
      change (raw (renderedArgument pattern)).length ≤ (canonicalWire pattern).length at rawLength
      rw [List.map_cons,List.sum_cons,pair_length]
      simp only [vectorInput,List.map_cons,Indexed.frame,List.flatMap_cons,List.length_append,List.length_map,List.length_cons,List.length_nil] at ih ⊢
      omega

noncomputable def nestedOutputs (patterns : List Pattern) :
    TM2OutputsInTime nestedMachine (vectorInput patterns) (some (nestedWire patterns))
      (400*((vectorInput patterns).length+1)) := by
  have mapped := FramedWordMapping.outputs machine canonicalWire pairWire
    (fun pattern => 300*((canonicalWire pattern).length+1)) outputs patterns
  apply WordEqualityMachine.within mapped
  rw [FramedWordMapping.totalClock_eq]
  have summed := summed_clock patterns
  omega

theorem nested_length (patterns : List Pattern) : (nestedWire patterns).length ≤ 3*(vectorInput patterns).length := by
  induction patterns with
  | nil => simp [nestedWire,vectorInput,Indexed.frame]
  | cons pattern rest ih =>
      have rawLength := SourceQuantifierEmission.term_length_le (renderedArgument pattern)
      change (raw (renderedArgument pattern)).length ≤ (canonicalWire pattern).length at rawLength
      simp only [nestedWire,vectorInput,List.map_cons,Indexed.frame,List.flatMap_cons,List.length_append,List.length_map,List.length_cons,List.length_nil,
        pair_length] at ih ⊢
      omega

/-- Only the outer caller separators disappear; every inner raw/named separator survives. -/
def flattenCell : Option (Option Alphabet) → List (Option Alphabet)
  | none => []
  | some symbol => [symbol]

theorem flatten_frame (words : List (List (Option Alphabet))) :
    (Indexed.frame words).flatMap flattenCell=words.flatten := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
      have inner : (word.map some).flatMap flattenCell=word := by
        induction word with
        | nil => rfl
        | cons symbol tail ih => simp only [List.map_cons,List.flatMap_cons,flattenCell,List.singleton_append,ih]
      change (word.map some++[none]++Indexed.frame rest).flatMap flattenCell=word++rest.flatten
      simp only [List.flatMap_append,List.flatMap_cons,flattenCell,List.flatMap_nil,List.append_nil,inner,ih]

def vectorWire (patterns : List Pattern) : List (Option Alphabet) := patterns.flatMap pairWire

theorem flattened (patterns : List Pattern) : (nestedWire patterns).flatMap flattenCell=vectorWire patterns := by
  rw [nestedWire,flatten_frame]
  rfl

theorem flatten_length_le (word : List (Option (Option Alphabet))) : (word.flatMap flattenCell).length≤word.length := by
  induction word with
  | nil => rfl
  | cons symbol rest ih => cases symbol <;> simp only [List.flatMap_cons,flattenCell,List.nil_append,List.singleton_append,List.length_cons] <;> omega

local instance : Fintype (nestedMachine.Γ nestedMachine.k₁) := inferInstanceAs (Fintype (Option (Option Alphabet)))
local instance : Inhabited (nestedMachine.Γ nestedMachine.k₁) := inferInstanceAs (Inhabited (Option (Option Alphabet)))
def vectorMachine : FinTM2 := StackMachineComposition.machine nestedMachine
  (WordHomomorphismMachine.machine flattenCell) (Equiv.refl (Option (Option Alphabet)))

noncomputable def vectorOutputs (patterns : List Pattern) :
    TM2OutputsInTime vectorMachine (vectorInput patterns) (some (vectorWire patterns))
      (1000*((vectorInput patterns).length+1)) := by
  have flattenedRun := WordHomomorphismMachine.outputs flattenCell (nestedWire patterns)
  rw [flattened] at flattenedRun
  have joined := StackMachineComposition.outputs nestedMachine (WordHomomorphismMachine.machine flattenCell)
    (Equiv.refl (Option (Option Alphabet))) (vectorInput patterns) (nestedWire patterns) (vectorWire patterns)
    _ _ (nestedOutputs patterns) (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine flattenCell) ((nestedWire patterns).map id) _ _
      simpa only [List.map_id] using flattenedRun)
  apply WordEqualityMachine.within joined
  have outerLength := nested_length patterns
  have flatLength := flatten_length_le (nestedWire patterns)
  rw [flattened] at flatLength
  omega

end Mettapedia.Languages.HOLLight.SourceOperandPairing
