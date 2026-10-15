import Mettapedia.OSLF.Syntax.RhoFiniteQuotedParallel

/-!
# Constructed lists of actual quoted parallel decompositions

Canonical component lists and their sublists give an explicit search order.
The resulting value pairs agree with the independently constructed complete
finite catalogue. A chosen entry carries its actual quotation equation.
Repeated equal cuts can occur in the list; their positions are not identified
with runtime occurrence provenance.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoQuotedParallelLists

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding RhoFiniteQuotationOrigins RhoIntrinsicCanonicalBag
open RhoFiniteParallelSplits RhoFiniteQuotedParallel RhoIntrinsicReadback MeTTaIL.Syntax

local instance processClassDecision (context : Ctx sig) : DecidableEq (Process context) :=
  equationClassDecision context Srt.pr

def originList {context : Ctx sig} (name : Name context) : List (Origin name) :=
  ⟨drop name, quote_drop name⟩ ::
    match readout : bodyOrigin context (encodeEquationClass name) with
    | none => []
    | some process => [⟨process, bodyOrigin_sound readout⟩]

theorem originList_complete {context : Ctx sig} (name : Name context) (origin : Origin name) :
    ∃ entry ∈ originList name, entry.val = origin.val := by
  rcases quotation_fibre_complete name origin.val origin.property with direct | exposed
  · exact ⟨⟨drop name, quote_drop name⟩, List.mem_cons_self, direct.symm⟩
  · refine ⟨⟨origin.val, bodyOrigin_sound exposed⟩, ?_, rfl⟩
    unfold originList
    split
    · next absent => rw [absent] at exposed; cases exposed
    · next process readout =>
      have same : process = origin.val := Option.some.inj (readout.symm.trans exposed)
      subst process
      exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)

theorem sublist_is_cut {context : Ctx sig} (process : Process context) (elements : List Pattern)
    (member : elements ∈ (contents process).sublists) :
    (elements : Multiset Pattern) ≤ components process := by
  apply Multiset.mem_powerset.mp
  change (elements : Multiset Pattern) ∈ (contents process : Multiset Pattern).powerset
  rw [Multiset.powerset_coe, Multiset.mem_coe]
  exact List.mem_map.mpr ⟨elements, member, rfl⟩

def cutList {context : Ctx sig} (process : Process context) :
    List {parts : Multiset Pattern // parts ≤ components process} :=
  (contents process).sublists.attach.map fun elements =>
    ⟨elements.val, sublist_is_cut process elements.val elements.property⟩

theorem cutList_complete {context : Ctx sig} (process : Process context) (parts : Multiset Pattern)
    (included : parts ≤ components process) :
    ∃ cut ∈ cutList process, cut.val = parts := by
  have member := Multiset.mem_powerset.mpr included
  change parts ∈ (contents process : Multiset Pattern).powerset at member
  rw [Multiset.powerset_coe, Multiset.mem_coe] at member
  obtain ⟨elements, listed, same⟩ := List.mem_map.mp member
  let cut : {parts : Multiset Pattern // parts ≤ components process} :=
    ⟨elements, sublist_is_cut process elements listed⟩
  refine ⟨cut, ?_, same⟩
  exact List.mem_map.mpr ⟨⟨elements, listed⟩, List.mem_attach _ _, rfl⟩

def candidateList {context : Ctx sig} (process : Process context) :
    List (Process context × Process context) :=
  (cutList process).map fun cut => makeSplit process cut.val cut.property

theorem candidateList_length {context : Ctx sig} (process : Process context) :
    (candidateList process).length = 2 ^ (components process).card := by
  simp only [candidateList, cutList, List.length_map, List.length_attach, List.length_sublists]
  rfl

theorem candidateList_sound {context : Ctx sig} (process first second : Process context)
    (member : (first, second) ∈ candidateList process) : join first second = process := by
  obtain ⟨cut, _, same⟩ := List.mem_map.mp member
  have actual := makeSplit_sound process cut.val cut.property
  rw [same] at actual
  exact actual

theorem candidateList_complete {context : Ctx sig} (process first second : Process context)
    (readout : join first second = process) : (first, second) ∈ candidateList process := by
  have inventory : components first + components second = components process := by
    rw [← readout, join_components]
  have included : components first ≤ components process := by
    rw [← inventory]
    exact Multiset.le_add_right _ _
  obtain ⟨cut, listed, cutReadout⟩ := cutList_complete process (components first) included
  apply List.mem_map.mpr
  refine ⟨cut, listed, ?_⟩
  apply Prod.ext
  · apply components_injective context
    change components (factor process cut.val cut.property) = components first
    rw [factor_components, cutReadout]
  · apply components_injective context
    change components (factor process (components process - cut.val) _) = components second
    rw [factor_components, cutReadout, ← inventory, add_comm]
    exact Multiset.add_sub_cancel_right

abbrev Decomposition {context : Ctx sig} (name : Name context) :=
  {pair : Process context × Process context // quote (join pair.1 pair.2) = name}

def decompositionList {context : Ctx sig} (name : Name context) : List (Decomposition name) :=
  (originList name).flatMap fun origin =>
    (candidateList origin.val).attach.map fun pair =>
      ⟨pair.val, (congrArg quote (candidateList_sound origin.val pair.val.1 pair.val.2 pair.property)).trans
        origin.property⟩

theorem decompositionList_complete {context : Ctx sig} (name : Name context)
    (first second : Process context) (readout : quote (join first second) = name) :
    ∃ entry ∈ decompositionList name, entry.val = (first, second) := by
  obtain ⟨origin, originListed, originReadout⟩ :=
    originList_complete name ⟨join first second, readout⟩
  have pairListed := candidateList_complete origin.val first second originReadout.symm
  let entry : Decomposition name :=
    ⟨(first, second), (congrArg quote (candidateList_sound origin.val first second pairListed)).trans
      origin.property⟩
  refine ⟨entry, List.mem_flatMap.mpr ⟨origin, originListed, ?_⟩, rfl⟩
  exact List.mem_map.mpr ⟨⟨(first, second), pairListed⟩, List.mem_attach _ _, rfl⟩

theorem decompositionList_values_agree {context : Ctx sig} (name : Name context) :
    ((decompositionList name).map Subtype.val).toFinset = decompositions name := by
  apply Finset.ext
  intro pair
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨entry, _, same⟩
    exact (quoted_parallel_iff name pair.1 pair.2).mp (same ▸ entry.property)
  · intro member
    exact decompositionList_complete name pair.1 pair.2 ((quoted_parallel_iff _ _ _).mpr member)

end Mettapedia.OSLF.Binding.RhoQuotedParallelLists
