import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.StableSource
import Mettapedia.OSLF.NativeTypes.SortProfiles.Slots

open Mettapedia.OSLF.Framework

/-!
# Derived modal slots and shared structural operation profiles

Every modal coordinate is indexed by an actual authored occurrence. Structural
formers read the same argument/result profile used to form the language's
equations. They do not have a second, unrelated copy of those coordinates.
The finite center decides common formation and uniform preservation of the
typed equation-formation relation. It does not identify a local profile with
an arbitrary operation truth table.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Derived

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler

abbrev ModalSlot (language : LanguageDef) :=
  Σ index : Fin (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language).length,
    Fin (Mettapedia.OSLF.NativeTypes.SortProfiles.Slots.modalFamily language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language)[index]).slotCount

abbrev ModalProfile (language : LanguageDef) := ModalSlot language → HSort

abbrev CubeVertex (language : LanguageDef) :=
  ModalProfile language × Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature language)

structure Assignment where
  family : Mettapedia.OSLF.NativeTypes.SortProfiles.Slots.Family
  inputs : List HSort
  output : HSort
  deriving DecidableEq, Repr

def modalAssignment (language : LanguageDef) (profile : ModalProfile language)
    (index : Fin (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language).length) : Assignment :=
  let family := Mettapedia.OSLF.NativeTypes.SortProfiles.Slots.modalFamily language (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language)[index]
  {family := family,
    inputs := List.ofFn fun input : Fin family.inputs.length =>
      profile ⟨index, ⟨input.val, Nat.lt_trans input.isLt (Nat.lt_succ_self _)⟩⟩,
    output := profile ⟨index, ⟨family.inputs.length, Nat.lt_succ_self _⟩⟩}

theorem constructor_key_present (language : LanguageDef) (declaration : GrammarRule)
    (declared : declaration ∈ language.terms) :
    Key.constructor declaration.label declaration.params.length ∈ operationKeys language := by
  apply List.mem_toFinset.mpr
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨declaration, declared, rfl⟩

def constructorOperation (language : LanguageDef) (declaration : GrammarRule)
    (declared : declaration ∈ language.terms) : (signature language).Operation :=
  ⟨.constructor declaration.label declaration.params.length,
    constructor_key_present language declaration declared⟩

def structuralAssignment (language : LanguageDef)
    (profile : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature language))
    (declaration : GrammarRule) (declared : declaration ∈ language.terms) (index : Nat) : Assignment :=
  let operation := constructorOperation language declaration declared
  {family := Mettapedia.OSLF.NativeTypes.SortProfiles.Slots.structuralFamily (declaration, index),
    inputs := List.ofFn fun input : Fin declaration.params.length =>
      Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.input profile operation input,
    output := Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.output profile operation}

def assignments (language : LanguageDef) (vertex : CubeVertex language) : List Assignment :=
  (List.ofFn fun index => modalAssignment language vertex.1 index) ++
    language.terms.attach.zipIdx.map fun entry =>
      structuralAssignment language vertex.2 entry.1.val entry.1.property entry.2

theorem modal_inputs_exact (language : LanguageDef) (profile : ModalProfile language)
    (index : Fin (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language).length) :
    (modalAssignment language profile index).inputs.length =
      (modalAssignment language profile index).family.inputs.length := by
  simp [modalAssignment]

theorem structural_inputs_exact (language : LanguageDef)
    (profile : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature language))
    (declaration : GrammarRule) (declared : declaration ∈ language.terms) (index : Nat) :
    (structuralAssignment language profile declaration declared index).inputs.length =
      declaration.params.length := by
  simp [structuralAssignment]

theorem structural_reads_equation_profile (language : LanguageDef)
    (profile : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature language))
    (declaration : GrammarRule) (declared : declaration ∈ language.terms) (index : Nat) :
    (structuralAssignment language profile declaration declared index).output =
      Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.output profile (constructorOperation language declaration declared) ∧
    ∀ input : Fin declaration.params.length,
      (structuralAssignment language profile declaration declared index).inputs[input.val]'(by
        rw [structural_inputs_exact]; exact input.isLt) =
        Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.input profile (constructorOperation language declaration declared) input := by
  constructor
  · rfl
  · intro input
    simp [structuralAssignment]

def center (language : LanguageDef) : Finset (CubeVertex language) :=
  Finset.univ.filter fun vertex => Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableLanguage? language vertex.2 = some true

theorem mem_center_iff (language : LanguageDef) (vertex : CubeVertex language) :
    vertex ∈ center language ↔
      (equations language).diagnostics = [] ∧
      ∀ equation index, (equation, index) ∈ language.equations.zipIdx →
        Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.SourceEquationStable language (equationLaw equation index) vertex.2 := by
  simp only [center, Finset.mem_filter, Finset.mem_univ, true_and,
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.original_stable_equation_check_exact]

theorem no_equations_whole_cube (language : LanguageDef) (empty : language.equations = []) :
    center language = Finset.univ := by
  have every := Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.no_authored_equations_stable_whole_cube language empty
  apply Finset.ext
  intro vertex
  simp only [center, Finset.mem_filter, Finset.mem_univ, true_and]
  have member : vertex.2 ∈ Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.stableLanguageCenter language := by rw [every]; exact Finset.mem_univ _
  exact ⟨fun _ => trivial, fun _ => (Finset.mem_filter.mp member).2⟩

end Mettapedia.OSLF.NativeTypes.SortProfiles.Derived
