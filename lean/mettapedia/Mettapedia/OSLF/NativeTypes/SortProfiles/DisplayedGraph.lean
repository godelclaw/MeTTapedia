import Mettapedia.OSLF.NativeTypes.SortProfiles.Derived
import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference

open Mettapedia.OSLF.Framework

/-!
# Finite consistency of displayed modal profiles

The revised Hypercube presentation separates ordinary equations from finite
matching of displayed type occurrences.  This construction has the complete
index/rely/target interface of each authored site.  Its generated type
metavariables are fresh labels, not program metavariable names.  Bare
`LanguageDef` equations contain program syntax only and hence supply no typed
occurrence matching.  Their conversion semantics remains a separate layer.

Explicit matching can be supplied as finite pairs of these typed occurrences;
the checker inserts a pair only when its carriers agree.  The computed checker
is compared to independent reflexive/symmetric/transitive graph consistency.
Structural operation slots are retained independently and are not merged by
ordinary program equations.  This is not the older universal fixed-output
formation diagnostic and does not establish that stronger claim.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Generation.Occurrences Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler Mettapedia.OSLF.NativeTypes.SortProfiles.Derived RedexPosition

def indexNames (site : Site) : List String :=
  ((contextNames site.context).filter fun name => (fvarNames site.focus).contains name).eraseDups

theorem index_names_exact (site : Site) (name : String) :
    name ∈ indexNames site ↔ name ∈ contextNames site.context ∧ name ∈ fvarNames site.focus := by
  simp [indexNames, List.mem_filter]

inductive LocalSlot where
  | index (name : String)
  | rely (name : String)
  | target
  deriving DecidableEq, Repr

def interface (site : Site) : List LocalSlot :=
  (indexNames site).map LocalSlot.index ++ site.relyNames.map LocalSlot.rely ++ [.target]

theorem interface_length (site : Site) :
    (interface site).length = (indexNames site).length + site.relyNames.length + 1 := by
  simp [interface, Nat.add_assoc]

abbrev Slot (language : LanguageDef) :=
  Σ site : Fin (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language).length,
    Fin (interface (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language)[site]).length

abbrev ModalVertex (language : LanguageDef) := Slot language → HSort

abbrev Vertex (language : LanguageDef) :=
  ModalVertex language × Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature language)

def slots (language : LanguageDef) : List (Slot language) :=
  (List.ofFn fun site : Fin (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language).length => site).flatMap fun site =>
    List.ofFn fun position : Fin (interface (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language)[site]).length =>
      (⟨site, position⟩ : Slot language)

theorem slots_complete (language : LanguageDef) (slot : Slot language) : slot ∈ slots language := by
  apply List.mem_flatMap.mpr
  exact ⟨slot.1, List.mem_ofFn.mpr ⟨slot.1, rfl⟩, List.mem_ofFn.mpr ⟨slot.2, rfl⟩⟩

def slotLabel (language : LanguageDef) (slot : Slot language) : LocalSlot :=
  (interface (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language)[slot.1])[slot.2]

/-- Omitted binding metadata is earned from the actual authored grammar. -/
def effectiveRule (language : LanguageDef) (site : Site) : RewriteRule :=
  match compile? language site.rule with
  | some binding => binding.elaborate site.rule
  | none => site.rule

def carrier? (language : LanguageDef) (slot : Slot language) : Option TypeExpr :=
  let site := (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language)[slot.1]
  let rule := effectiveRule language site
  match slotLabel language slot with
  | .index name | .rely name => rule.typeContext.lookup name
  | .target => Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar.headType?
      language rule.typeContext [] rule.right

inductive Role where
  | declaration
  | inputPremise
  | suppliedArgument
  | continuation
  | targetPremise
  deriving DecidableEq, Repr

/-- The label is the fresh generated type-code metavariable, not the authored
program variable. Its site and role class are part of its identity. -/
structure TypeMeta (language : LanguageDef) where
  site : Fin (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language).length
  label : LocalSlot
  deriving DecidableEq, Repr

structure TypeOccurrence (language : LanguageDef) where
  slot : Slot language
  role : Role
  codeName : TypeMeta language
  deriving DecidableEq

def ordinaryMeta (language : LanguageDef) (slot : Slot language) : TypeMeta language :=
  ⟨slot.1, slotLabel language slot⟩

def variableLabel? (site : Site) (name : String) : Option LocalSlot :=
  if name ∈ indexNames site then some (.index name)
  else if name ∈ site.relyNames then some (.rely name)
  else none

/-- A displayed variable target reads the generated type metavariable of its
index/rely declaration. External ambient declarations have no profile slot. -/
def targetMeta (language : LanguageDef) (slot : Slot language) : TypeMeta language :=
  let site := (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language)[slot.1]
  match slotLabel language slot, site.rule.right with
  | .target, .fvar name =>
      match variableLabel? site name with
      | some label => ⟨slot.1, label⟩
      | none => ordinaryMeta language slot
  | _, _ => ordinaryMeta language slot

/-- Finite displayed occurrences in the formation, introduction and
elimination rule templates. Type-code labels are generated once and reused. -/
def slotOccurrences (language : LanguageDef) (slot : Slot language) :
    List (TypeOccurrence language) :=
  match slotLabel language slot with
  | .index _ | .rely _ =>
      [.mk slot .declaration (ordinaryMeta language slot),
       .mk slot .inputPremise (ordinaryMeta language slot),
       .mk slot .suppliedArgument (ordinaryMeta language slot)]
  | .target =>
      [.mk slot .continuation (ordinaryMeta language slot),
       .mk slot .targetPremise (targetMeta language slot)]

def occurrences (language : LanguageDef) : List (TypeOccurrence language) :=
  (slots language).flatMap (slotOccurrences language)

def sameCarrier (language : LanguageDef) (first second : Slot language) : Bool :=
  match carrier? language first, carrier? language second with
  | some firstType, some secondType => decide (firstType = secondType)
  | _, _ => false

def matchable (language : LanguageDef) (first second : TypeOccurrence language) : Bool :=
  decide (first.codeName = second.codeName) && sameCarrier language first.slot second.slot

/-- Independently specified shared-type-metavariable constraint. -/
def SharedType (language : LanguageDef) (first second : Slot language) : Prop :=
  ∃ left ∈ occurrences language, ∃ right ∈ occurrences language,
    left.slot = first ∧ right.slot = second ∧ left.codeName = right.codeName ∧
      ∃ carrier, carrier? language first = some carrier ∧
        carrier? language second = some carrier

def intrinsicEdges (language : LanguageDef) : List (Slot language × Slot language) :=
  (occurrences language).flatMap fun first =>
    ((occurrences language).filter fun second => matchable language first second).map
      fun second => (first.slot, second.slot)

theorem sameCarrier_exact (language : LanguageDef) (first second : Slot language) :
    sameCarrier language first second = true ↔
      ∃ carrier, carrier? language first = some carrier ∧ carrier? language second = some carrier := by
  cases firstType : carrier? language first <;> cases secondType : carrier? language second <;>
    simp [sameCarrier, firstType, secondType]
  exact ⟨fun equal => equal.symm, fun equal => equal.symm⟩

theorem intrinsic_edge_exact (language : LanguageDef) (first second : Slot language) :
    (first, second) ∈ intrinsicEdges language ↔ SharedType language first second := by
  simp only [intrinsicEdges, List.mem_flatMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨left, leftPresent, right, ⟨rightPresent, matched⟩, pairEq⟩
    have firstEq := congrArg Prod.fst pairEq
    have secondEq := congrArg Prod.snd pairEq
    change left.slot = first at firstEq
    change right.slot = second at secondEq
    have parts := Bool.and_eq_true_iff.mp (show (decide (left.codeName = right.codeName) &&
      sameCarrier language left.slot right.slot) = true from matched)
    exact ⟨left, leftPresent, right, rightPresent, firstEq, secondEq,
      of_decide_eq_true parts.1, by simpa only [firstEq, secondEq] using
        (sameCarrier_exact language left.slot right.slot).mp parts.2⟩
  · rintro ⟨left, leftPresent, right, rightPresent, firstEq, secondEq, metaEq, carrier, firstType, secondType⟩
    refine ⟨left, leftPresent, right, ⟨rightPresent, ?_⟩, ?_⟩
    · apply Bool.and_eq_true_iff.mpr
      refine ⟨decide_eq_true metaEq, ?_⟩
      exact (sameCarrier_exact language left.slot right.slot).mpr
        ⟨carrier, firstEq.symm ▸ firstType, secondEq.symm ▸ secondType⟩
    · exact Prod.ext firstEq secondEq

/-- Explicit equation matching is data between actual generated typed
occurrences. Carrier checking is earned independently of the supplied pair. -/
structure EquationMatching (language : LanguageDef) where
  equation : Fin language.equations.length
  first : TypeOccurrence language
  firstPresent : first ∈ occurrences language
  second : TypeOccurrence language
  secondPresent : second ∈ occurrences language

def equationEdges (language : LanguageDef) (matching : List (EquationMatching language)) :
    List (Slot language × Slot language) :=
  matching.filterMap fun pair =>
    if sameCarrier language pair.first.slot pair.second.slot then
      some (pair.first.slot, pair.second.slot) else none

def EquationMatch (language : LanguageDef) (matching : List (EquationMatching language))
    (first second : Slot language) : Prop :=
  ∃ pair ∈ matching, pair.first.slot = first ∧ pair.second.slot = second ∧
    ∃ carrier, carrier? language first = some carrier ∧ carrier? language second = some carrier

theorem equation_edge_exact (language : LanguageDef) (matching : List (EquationMatching language))
    (first second : Slot language) :
    (first, second) ∈ equationEdges language matching ↔ EquationMatch language matching first second := by
  simp only [equationEdges, List.mem_filterMap]
  constructor
  · rintro ⟨pair, present, selected⟩
    split at selected
    · rename_i matched
      have equal := Option.some.inj selected
      have firstEq := congrArg Prod.fst equal
      have secondEq := congrArg Prod.snd equal
      change pair.first.slot = first at firstEq
      change pair.second.slot = second at secondEq
      exact ⟨pair, present, firstEq, secondEq, by simpa only [firstEq, secondEq] using
        (sameCarrier_exact language pair.first.slot pair.second.slot).mp matched⟩
    · contradiction
  · rintro ⟨pair, present, firstEq, secondEq, carrier, firstType, secondType⟩
    refine ⟨pair, present, ?_⟩
    have matchingCarriers := (sameCarrier_exact language pair.first.slot pair.second.slot).mpr
      ⟨carrier, firstEq.symm ▸ firstType, secondEq.symm ▸ secondType⟩
    simp only [matchingCarriers, ↓reduceIte]
    exact congrArg some (Prod.ext firstEq secondEq)

def edges (language : LanguageDef) (matching : List (EquationMatching language)) :
    List (Slot language × Slot language) :=
  intrinsicEdges language ++ equationEdges language matching

def Constraint (language : LanguageDef) (matching : List (EquationMatching language))
    (first second : Slot language) : Prop :=
  SharedType language first second ∨ EquationMatch language matching first second

def Connected (language : LanguageDef) (matching : List (EquationMatching language)) :
    Slot language → Slot language → Prop :=
  Relation.EqvGen (Constraint language matching)

def Consistent (language : LanguageDef) (matching : List (EquationMatching language))
    (vertex : Vertex language) : Prop :=
  ∀ first second, Connected language matching first second → vertex.1 first = vertex.1 second

def check (language : LanguageDef) (matching : List (EquationMatching language))
    (vertex : Vertex language) : Bool :=
  (edges language matching).all fun pair => decide (vertex.1 pair.1 = vertex.1 pair.2)

theorem edge_exact (language : LanguageDef) (matching : List (EquationMatching language))
    (first second : Slot language) :
    (first, second) ∈ edges language matching ↔ Constraint language matching first second := by
  simp only [edges, List.mem_append, intrinsic_edge_exact, equation_edge_exact, Constraint]

theorem check_exact (language : LanguageDef) (matching : List (EquationMatching language))
    (vertex : Vertex language) : check language matching vertex = true ↔ Consistent language matching vertex := by
  rw [check, List.all_eq_true]
  constructor
  · intro checked first second connected
    induction connected with
    | rel first second constraint =>
        exact of_decide_eq_true (checked (first, second) ((edge_exact _ _ _ _).mpr constraint))
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ firstIH secondIH => exact firstIH.trans secondIH
  · intro consistent pair present
    exact decide_eq_true (consistent pair.1 pair.2
      (.rel _ _ ((edge_exact _ _ _ _).mp present)))

def allStar (language : LanguageDef) : Vertex language := (fun _ => .star, fun _ => .star)

theorem allStar_consistent (language : LanguageDef) (matching : List (EquationMatching language)) :
    Consistent language matching (allStar language) := fun _ _ _ => rfl

theorem allStar_checked (language : LanguageDef) (matching : List (EquationMatching language)) :
    check language matching (allStar language) = true :=
  (check_exact _ _ _).mpr (allStar_consistent _ _)

def center (language : LanguageDef) (matching : List (EquationMatching language)) :
    Finset (Vertex language) := Finset.univ.filter fun vertex => check language matching vertex = true

theorem center_exact (language : LanguageDef) (matching : List (EquationMatching language))
    (vertex : Vertex language) : vertex ∈ center language matching ↔ Consistent language matching vertex := by
  simp only [center, Finset.mem_filter, Finset.mem_univ, true_and, check_exact]

theorem no_matching_keeps_intrinsic_graph (language : LanguageDef) :
    edges language [] = intrinsicEdges language := by simp [edges, equationEdges]

theorem no_equations_no_matching (language : LanguageDef) (empty : language.equations = [])
    (matching : List (EquationMatching language)) : matching = [] := by
  cases matching with
  | nil => rfl
  | cons pair tail =>
      have impossible := pair.equation.isLt
      simp [empty] at impossible

inductive DisplayedName (language : LanguageDef) where
  | programMeta (name : String)
  | nativeMeta (codeName : TypeMeta language)
  deriving DecidableEq

/-- The actual equation context and both complete free-name traversals remain
program names. They are not relabeled as generated type-code metavariables. -/
def bareEquationNames (language : LanguageDef) (index : Fin language.equations.length) :
    List (DisplayedName language) :=
  let equation := language.equations[index]
  ((equation.typeContext.map Prod.fst) ++ fvarNames equation.left ++ fvarNames equation.right).map
    DisplayedName.programMeta

theorem bare_equation_has_no_generated_type_meta (language : LanguageDef)
    (index : Fin language.equations.length) (codeName : TypeMeta language) :
    DisplayedName.nativeMeta codeName ∉ bareEquationNames language index := by
  intro present
  obtain ⟨name, _, impossible⟩ := List.mem_map.mp present
  cases impossible

/-- The unannotated authored language has no explicit typed occurrence pairs;
this is the bare-presentation policy, not omission of its program equations. -/
def bareMatching (language : LanguageDef) : List (EquationMatching language) := []

def bareCheck (language : LanguageDef) (vertex : Vertex language) : Bool :=
  check language (bareMatching language) vertex

theorem bare_check_exact (language : LanguageDef) (vertex : Vertex language) :
    bareCheck language vertex = true ↔ Consistent language [] vertex := check_exact _ _ _

def carriersKnown (language : LanguageDef) : Bool :=
  (slots language).all fun slot => (carrier? language slot).isSome

def admit? (language : LanguageDef) (matching : List (EquationMatching language))
    (vertex : Vertex language) : Option Bool :=
  if carriersKnown language then some (check language matching vertex) else none

theorem admission_exact (language : LanguageDef) (matching : List (EquationMatching language))
    (vertex : Vertex language) :
    admit? language matching vertex = some true ↔
      carriersKnown language = true ∧ Consistent language matching vertex := by
  by_cases known : carriersKnown language = true <;> simp [admit?, known, check_exact]

def legacySlot (language : LanguageDef) (slot : ModalSlot language) : Slot language :=
  let site := (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language)[slot.1]
  ⟨slot.1, ⟨(indexNames site).length + slot.2.val, by
    have below : slot.2.val < site.relyNames.length + 1 := by
      simpa only [Mettapedia.OSLF.NativeTypes.SortProfiles.Slots.modal_slot_count] using slot.2.isLt
    rw [interface_length]
    dsimp only [site] at *
    omega⟩⟩

def project (language : LanguageDef) (vertex : Vertex language) : CubeVertex language :=
  (fun slot => vertex.1 (legacySlot language slot), vertex.2)

/-- Legacy rely and target coordinates are copied exactly; missing index
coordinates receive the separately declared constant sort. -/
def extend (language : LanguageDef) (legacy : CubeVertex language) (indexSort : HSort) : Vertex language :=
  (fun slot =>
    let site := (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate language)[slot.1]
    if before : slot.2.val < (indexNames site).length then indexSort
    else legacy.1 ⟨slot.1, ⟨slot.2.val - (indexNames site).length, by
      have below : slot.2.val < (indexNames site).length + site.relyNames.length + 1 := by
        simpa only [interface_length] using slot.2.isLt
      rw [Mettapedia.OSLF.NativeTypes.SortProfiles.Slots.modal_slot_count]
      dsimp only [site] at *
      omega⟩⟩, legacy.2)

theorem project_extend (language : LanguageDef) (legacy : CubeVertex language) (indexSort : HSort) :
    project language (extend language legacy indexSort) = legacy := by
  apply Prod.ext
  · funext slot
    simp only [project, extend, legacySlot]
    split
    · omega
    · apply congrArg legacy.1
      apply Sigma.ext
      · rfl
      · simp
  · rfl

theorem extend_allStar (language : LanguageDef) :
    extend language (fun _ => .star, fun _ => .star) .star = allStar language := by
  apply Prod.ext
  · funext slot
    simp [extend, allStar]
  · rfl

#print axioms check_exact
#print axioms admission_exact
#print axioms project_extend

end Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph
