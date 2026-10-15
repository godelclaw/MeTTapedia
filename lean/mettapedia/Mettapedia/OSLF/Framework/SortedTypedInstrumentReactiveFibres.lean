import Mettapedia.OSLF.Framework.SortedTypedInstrumentArgumentFibres
import Mettapedia.OSLF.Framework.SortedCommutativeReactiveFibreFinite

/-!
# Administrative primitive reactum fibres are finite

Equality of complete sorted administrative redex readings recovers the
actual instrument and whole body. Every possible output is then in the
independently bounded complete argument range. In particular proper-Cut
ask is finitely branching without being deterministic. Authored occurrence
origins remain part of receipts and are not required to be finite or inhabited.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.ReactiveFibres

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.OSLF.SortedCommutative.ReactiveFiniteness
open Mettapedia.GSLT.InterfaceModalLogic
open ArgumentFibres

universe u v w

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {Origins : Type w}

abbrev SortedValue := Σ sort : Srt source Parallel,
  ValueClass (source := source) (Parallel := Parallel) sort

def valueArrow (reading : SortedValue (source := source) (Parallel := Parallel)) :
    Σ object : ContextCategory source Parallel, (.origin : ContextCategory source Parallel) ⟶ object :=
  ⟨.interface reading.1, .value reading.2⟩

theorem valueArrow_injective :
    Function.Injective (valueArrow (source := source) (Parallel := Parallel)) := by
  rintro ⟨firstSort, first⟩ ⟨secondSort, second⟩ same
  obtain ⟨sorts, values⟩ := Sigma.mk.inj_iff.mp same
  have sameSort : firstSort = secondSort := RawObject.interface.inj sorts
  subst secondSort
  have sameValue : first = second := RawArrow.value.inj (eq_of_heq values)
  subst second
  rfl

def redexReading (supplied : Occurrence source Parallel Origins) :
    SortedValue (source := source) (Parallel := Parallel) :=
  ⟨result supplied.instrument, classOf (cut supplied.instrument (probe supplied.instrument) supplied.body)⟩

def outputReading (supplied : Occurrence source Parallel Origins) :
    SortedValue (source := source) (Parallel := Parallel) :=
  ⟨result supplied.instrument, classOf supplied.output⟩

private theorem constructorInventory_heq {first second : Srt source Parallel}
    (before : ValueClass (source := source) (Parallel := Parallel) first)
    (after : ValueClass (source := source) (Parallel := Parallel) second)
    (sortRead : first = second) (valueRead : HEq before after) :
    constructorInventory before = constructorInventory after := by
  subst second
  exact congrArg constructorInventory (eq_of_heq valueRead)

theorem cut_redex_readout (first second : Probe source Parallel)
    (before : Value (source := source) (Parallel := Parallel) (receiver first))
    (after : Value (source := source) (Parallel := Parallel) (receiver second))
    (same : (⟨result first, classOf (cut first (probe first) before)⟩ :
        SortedValue (source := source) (Parallel := Parallel)) =
      ⟨result second, classOf (cut second (probe second) after)⟩) :
    first = second ∧ HEq (classOf before) (classOf after) := by
  obtain ⟨sorts, readings⟩ := Sigma.mk.inj_iff.mp same
  have constructors := constructorInventory_heq _ _ sorts readings
  rw [constructorInventory_probeCut, constructorInventory_probeCut] at constructors
  have instruments : first = second := Constructor.cut.inj (Multiset.singleton_inj.mp constructors)
  subst second
  have completeRead : classOf (cut first (probe first) before) = classOf (cut first (probe first) after) :=
    eq_of_heq readings
  have bodyRead := (node_class_eq_iff (signature := signature source Parallel)
    (Parallel := NativeParallel) (Constructor.cut first) _ _).mp completeRead 1
  change classOf before = classOf after at bodyRead
  exact ⟨rfl, heq_of_eq bodyRead⟩

theorem occurrence_redex_readout (first second : Occurrence source Parallel Origins)
    (same : redexReading first = redexReading second) :
    first.instrument = second.instrument ∧ HEq (classOf first.body) (classOf second.body) :=
  cut_redex_readout first.instrument second.instrument first.body second.body same

def sortedOutputsAtBody (instrument : Probe source Parallel)
    (body : ValueClass (source := source) (Parallel := Parallel) (receiver instrument)) :
    Set (SortedValue (source := source) (Parallel := Parallel)) :=
  (Sigma.mk (result instrument)) ''
    {output | ∃ arguments : Arguments (probeHead instrument),
      classOf (bodyAt instrument arguments) = body ∧ classOf (outputAt instrument arguments) = output}

theorem sortedOutputsAtBody_finite (instrument : Probe source Parallel)
    (body : ValueClass (source := source) (Parallel := Parallel) (receiver instrument)) :
    (sortedOutputsAtBody instrument body).Finite :=
  (outputs_finite_at_body instrument body).image (Sigma.mk (result instrument))

theorem occurrence_output_mem (instrument : Probe source Parallel)
    (body : ValueClass (source := source) (Parallel := Parallel) (receiver instrument))
    (supplied : Occurrence source Parallel Origins)
    (instrumentRead : supplied.instrument = instrument) (bodyRead : HEq (classOf supplied.body) body) :
    outputReading supplied ∈ sortedOutputsAtBody instrument body := by
  cases supplied with
  | ask origin head arguments =>
    change Probe.ask head = instrument at instrumentRead
    subst instrument
    exact ⟨classOf (bundle head arguments), ⟨arguments, eq_of_heq bodyRead, rfl⟩, rfl⟩
  | get origin head arguments position =>
    change Probe.get head position = instrument at instrumentRead
    subst instrument
    exact ⟨classOf (arguments position), ⟨arguments, eq_of_heq bodyRead, rfl⟩, rfl⟩
  | build origin head arguments =>
    change Probe.build head = instrument at instrumentRead
    subst instrument
    exact ⟨classOf (sourceNode head arguments), ⟨arguments, eq_of_heq bodyRead, rfl⟩, rfl⟩

theorem same_redex_outputs_finite (reference : Occurrence source Parallel Origins) :
    Set.Finite {output : SortedValue (source := source) (Parallel := Parallel) |
      ∃ supplied : Occurrence source Parallel Origins,
        redexReading supplied = redexReading reference ∧ outputReading supplied = output} := by
  apply (sortedOutputsAtBody_finite reference.instrument (classOf reference.body)).subset
  rintro output ⟨supplied, same, rfl⟩
  obtain ⟨instrumentRead, bodyRead⟩ := occurrence_redex_readout supplied reference same
  exact occurrence_output_mem reference.instrument (classOf reference.body) supplied instrumentRead bodyRead

theorem rule_complete_readout (supplied : Occurrence source Parallel Origins)
    {sort : Srt source Parallel}
    (redex reactum : ValueClass (source := source) (Parallel := Parallel) sort)
    (same : supplied.rule = {codomain := .interface sort, redex := .value redex, reactum := .value reactum}) :
    redexReading supplied = ⟨sort, redex⟩ ∧ outputReading supplied = ⟨sort, reactum⟩ := by
  constructor
  · apply valueArrow_injective
    exact congrArg (fun rule => (⟨rule.codomain, rule.redex⟩ :
      Σ object : ContextCategory source Parallel, (.origin : ContextCategory source Parallel) ⟶ object)) same
  · apply valueArrow_injective
    exact congrArg (fun rule => (⟨rule.codomain, rule.reactum⟩ :
      Σ object : ContextCategory source Parallel, (.origin : ContextCategory source Parallel) ⟶ object)) same

theorem administrative_finiteReactumFibres :
    FiniteReactumFibres (rules source Parallel Origins) := by
  classical
  intro sort redex
  by_cases inhabited : ∃ reactum : ValueClass (source := source) (Parallel := Parallel) sort,
      rules source Parallel Origins
        {codomain := .interface sort, redex := .value redex, reactum := .value reactum}
  · obtain ⟨reactum, reference, referenceRule⟩ := inhabited
    have referenceRead := (rule_complete_readout reference redex reactum referenceRule).1
    let _ := (same_redex_outputs_finite reference).fintype
    apply Finite.of_injective (fun output =>
      (⟨(⟨sort, output.val⟩ : SortedValue (source := source) (Parallel := Parallel)), by
        obtain ⟨supplied, suppliedRule⟩ := output.property
        obtain ⟨redexRead, outputRead⟩ := rule_complete_readout supplied redex output.val suppliedRule
        exact ⟨supplied, redexRead.trans referenceRead.symm, outputRead⟩⟩ :
        {output : SortedValue (source := source) (Parallel := Parallel) |
          ∃ supplied : Occurrence source Parallel Origins,
            redexReading supplied = redexReading reference ∧ outputReading supplied = output}))
    intro first second same
    apply Subtype.ext
    exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val same)).2
  · exact Set.finite_empty.subset (fun output admitted => (inhabited ⟨output, admitted⟩).elim)

theorem administrative_imageFinite : ImageFinite (rules source Parallel Origins) :=
  imageFinite administrative_finiteReactumFibres

end Mettapedia.OSLF.Framework.SortedTypedInstruments.ReactiveFibres
