import Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
import Mettapedia.Languages.MeTTa.HE.Spec.Type
import Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory

/-!
# Executable-independent evaluator steps

This module formalizes non-recursive constraint and branch-selection
judgments for `unify`, ordered switching, and equation-rule selection,
including their negative cases. Every judgment is fuel-free and uses the
independent matching and logical constraint conjunction. Exact primitive execution in
`Spec.Eval` additionally requires the selected binding-frame materialization;
a constraint-only step does not determine the emitted syntax.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Match.Merge Spec.Bindings.ScopeObservation

/-! ## Primitive unify -/

/-- One surviving match-and-merge candidate for primitive `unify`. -/
def UnifyCandidateRel
    (target pattern : Atom) (incoming output : Bindings) : Prop :=
  ∃ matched,
    MatchRel equalityGroundedSemantic target pattern matched ∧
      LogicalMergeRel matched incoming output

/-- Constraint-only observation of successful `unify` selection. The atom is
equal to the template in every model of the merged bindings. Exact primitive
execution additionally fixes its actual selected-frame readout. -/
def UnifySuccessRel
    (target pattern thenBranch : Atom) (incoming : Bindings)
    (emitted : Atom) (output : Bindings) : Prop :=
    UnifyCandidateRel target pattern incoming output ∧
    ∀ valuation : String → Metta.Atom,
      LeaTTaBridge.HEBindingSatisfied valuation output →
        LeaTTaBridge.HEAtomEquationSatisfied valuation emitted thenBranch

/-- No structurally matched binding has a logically satisfiable conjunction. -/
def UnifyNoMatchRel
    (target pattern : Atom) (incoming : Bindings) : Prop :=
  ∀ output, ¬UnifyCandidateRel target pattern incoming output

/-- The constraint-level projection of primitive `unify`. This relation does
not determine the literal readout of a successful template. -/
inductive UnifyStep
    (target pattern thenBranch elseBranch : Atom) (incoming : Bindings) :
    Atom → Bindings → Prop where
  | success {emitted : Atom} {output : Bindings} :
      UnifySuccessRel target pattern thenBranch incoming emitted output →
      UnifyStep target pattern thenBranch elseBranch incoming
        emitted output
  | noMatch :
      UnifyNoMatchRel target pattern incoming →
      UnifyStep target pattern thenBranch elseBranch incoming
        elseBranch incoming

/-! ## Ordered switch -/

/-- Raw outcome of scanning a `switch-minimal` branch list. -/
inductive SwitchRawOutcome where
  | selected (atom : Atom) (bindings : Bindings)
  | noMatch
  deriving Repr

/-- Left-to-right branch scan.  Malformed branches and well-formed branches
without a surviving unify candidate fall through; the first viable branch
wins. -/
inductive SwitchRawRel (scrutinee : Atom) (incoming : Bindings) :
    List Atom → SwitchRawOutcome → Prop where
  | nil : SwitchRawRel scrutinee incoming [] .noMatch
  | malformed {branch : Atom} {branches : List Atom}
      {outcome : SwitchRawOutcome} :
      (∀ pattern template,
        branch ≠ .expression [pattern, template]) →
      SwitchRawRel scrutinee incoming branches outcome →
      SwitchRawRel scrutinee incoming (branch :: branches) outcome
  | hit {pattern template emitted : Atom} {branches : List Atom}
      {output : Bindings} :
      UnifySuccessRel scrutinee pattern template incoming emitted output →
      SwitchRawRel scrutinee incoming
        (.expression [pattern, template] :: branches)
        (.selected emitted output)
  | miss {pattern template : Atom} {branches : List Atom}
      {outcome : SwitchRawOutcome} :
      UnifyNoMatchRel scrutinee pattern incoming →
      SwitchRawRel scrutinee incoming branches outcome →
      SwitchRawRel scrutinee incoming
        (.expression [pattern, template] :: branches) outcome

/-- Final `switch-minimal` step.  No match and a selected `NotReducible`
sentinel both become `Empty`; every other first-hit result is preserved. -/
inductive SwitchStep (scrutinee : Atom) (branches : List Atom)
    (incoming : Bindings) : Atom → Bindings → Prop where
  | noMatch :
      SwitchRawRel scrutinee incoming branches .noMatch →
      SwitchStep scrutinee branches incoming Atom.empty incoming
  | notReducible {output : Bindings} :
      SwitchRawRel scrutinee incoming branches
        (.selected Atom.notReducible output) →
      SwitchStep scrutinee branches incoming Atom.empty output
  | selected {atom : Atom} {output : Bindings} :
      SwitchRawRel scrutinee incoming branches (.selected atom output) →
      atom ≠ Atom.notReducible →
      SwitchStep scrutinee branches incoming atom output

/-! ## Capture-avoiding equation selection -/

/- Structural variable renaming on atoms. -/
mutual
  inductive AlphaRenameAtomRel (rename : String → String) : Atom → Atom → Prop where
    | symbol (name : String) :
        AlphaRenameAtomRel rename (.symbol name) (.symbol name)
    | variable (name : String) :
        AlphaRenameAtomRel rename (.var name) (.var (rename name))
    | grounded (value : GroundedValue) :
        AlphaRenameAtomRel rename (.grounded value) (.grounded value)
    | expression {source target : List Atom} :
        AlphaRenameAtomsRel rename source target →
        AlphaRenameAtomRel rename (.expression source) (.expression target)

  inductive AlphaRenameAtomsRel (rename : String → String) :
      List Atom → List Atom → Prop where
    | nil : AlphaRenameAtomsRel rename [] []
    | cons {sourceHead targetHead : Atom} {sourceTail targetTail : List Atom} :
        AlphaRenameAtomRel rename sourceHead targetHead →
        AlphaRenameAtomsRel rename sourceTail targetTail →
        AlphaRenameAtomsRel rename
          (sourceHead :: sourceTail) (targetHead :: targetTail)
end

/-- A variable name visible to the current query configuration. -/
def QueryVisibleName
    (live : List Atom) (query : Atom) (incoming : Bindings)
    (name : String) : Prop :=
  AtomOccurs query name ∨
    (∃ atom ∈ live, AtomOccurs atom name) ∨
    (∃ value, (name, value) ∈ incoming.assignments) ∨
    (∃ key value,
      (key, value) ∈ incoming.assignments ∧ AtomOccurs value name) ∨
    ∃ left right,
      (left, right) ∈ incoming.equalities ∧
        (name = left ∨ name = right)

/-- A simultaneous injective alpha-variant of both sides of an equation.  All
renamed rule variables avoid names visible in the query and incoming binding
state. -/
def AlphaVariantRel
    (live : List Atom) (query : Atom) (incoming : Bindings)
    (rawLhs rawRhs freshLhs freshRhs : Atom) : Prop :=
  ∃ rename : String → String,
    Function.Injective rename ∧
      AlphaRenameAtomRel rename rawLhs freshLhs ∧
      AlphaRenameAtomRel rename rawRhs freshRhs ∧
      ∀ name,
        (AtomOccurs rawLhs name ∨ AtomOccurs rawRhs name) →
          ¬QueryVisibleName live query incoming (rename name)

/-- Freshening and matching of one fixed raw equation. Storage membership is
separate so an occurrence can retain the exact physical row. -/
def EquationRuleInstanceRel
    (live : List Atom) (query : Atom) (incoming : Bindings)
    (rawLhs rawRhs freshPattern freshRhs : Atom) (matched : Bindings) : Prop :=
  AlphaVariantRel live query incoming rawLhs rawRhs freshPattern freshRhs ∧
    MatchRel equalityGroundedSemantic query freshPattern matched

/-- One hygienically selected equation rule whose fresh left-hand side
matches the query. -/
def EquationRuleMatchRel
    (space : Space) (live : List Atom) (query : Atom) (incoming : Bindings)
    (freshPattern freshRhs : Atom) (matched : Bindings) : Prop :=
  ∃ rawLhs rawRhs,
    .expression [.symbol "=", rawLhs, rawRhs] ∈ space.atoms ∧
      EquationRuleInstanceRel live query incoming rawLhs rawRhs freshPattern freshRhs matched

/-- The selected match and caller constraints form one satisfiable logical
conjunction with exact support. RHS observation describes this query item before
invocation or recursive evaluation; it does not select a concrete representative. -/
def EquationQueryResultRel (incoming matched : Bindings) (freshRhs emitted : Atom)
    (output : Bindings) : Prop :=
  LogicalMergeRel matched incoming output ∧
    ∀ valuation : String → Metta.Atom,
      LeaTTaBridge.HEBindingSatisfied valuation output →
        LeaTTaBridge.HEAtomEquationSatisfied valuation emitted freshRhs

/-- One selected equation rule survives the ambient merge and emits an atom
observationally equal to the fresh RHS. -/
def EquationQueryCandidateRel
    (space : Space) (live : List Atom) (query : Atom) (incoming : Bindings)
    (emitted : Atom) (output : Bindings) : Prop :=
  ∃ freshPattern freshRhs matched,
    EquationRuleMatchRel space live query incoming freshPattern freshRhs matched ∧
      EquationQueryResultRel incoming matched freshRhs emitted output

/-- One physical stored equation occurrence, with its own freshening, match,
merge and emitted work item. The row's raw RHS and the observed fresh RHS share
one witness; an unrelated successful equation cannot justify this occurrence. -/
structure EquationQueryOccurrenceRel
    (space : Space) (live : List Atom) (query : Atom) (incoming : Bindings)
    (position : Nat) (rawLhs rawRhs freshPattern freshRhs : Atom)
    (matched : Bindings) (emitted : Atom) (output : Bindings) : Prop where
  stored : space.atoms[position]? = some (.expression [.symbol "=", rawLhs, rawRhs])
  selected : EquationRuleInstanceRel live query incoming rawLhs rawRhs freshPattern freshRhs matched
  result : EquationQueryResultRel incoming matched freshRhs emitted output

namespace EquationQueryOccurrenceRel

/-- Forgetting physical occurrence evidence recovers the existing query
judgment without changing any matching or merging rule. -/
theorem candidate {space : Space} {live : List Atom} {query : Atom} {incoming : Bindings}
    {position : Nat} {rawLhs rawRhs freshPattern freshRhs : Atom}
    {matched : Bindings} {emitted : Atom} {output : Bindings}
    (occurrence : EquationQueryOccurrenceRel space live query incoming position
      rawLhs rawRhs freshPattern freshRhs matched emitted output) :
    EquationQueryCandidateRel space live query incoming emitted output :=
  ⟨freshPattern, freshRhs, matched,
    ⟨rawLhs, rawRhs, List.mem_of_getElem? occurrence.stored, occurrence.selected⟩,
    occurrence.result⟩

/-- A physical position fixes both raw sides, including when several equal
rules occupy different positions. -/
theorem raw_rule_unique {space : Space} {live : List Atom} {query : Atom} {incoming : Bindings}
    {position : Nat} {lhs rhs otherLhs otherRhs freshPattern freshRhs otherPattern otherFreshRhs : Atom}
    {matched otherMatched output otherOutput : Bindings} {emitted otherEmitted : Atom}
    (first : EquationQueryOccurrenceRel space live query incoming position
      lhs rhs freshPattern freshRhs matched emitted output)
    (second : EquationQueryOccurrenceRel space live query incoming position
      otherLhs otherRhs otherPattern otherFreshRhs otherMatched otherEmitted otherOutput) :
    lhs = otherLhs ∧ rhs = otherRhs := by
  have same := Option.some.inj (first.stored.symm.trans second.stored)
  simpa only [Atom.expression.injEq, List.cons.injEq, and_true, true_and] using same

end EquationQueryOccurrenceRel

/-- The old existential judgment is exactly the erasure of physical source
occurrence evidence. This does not assert completeness of any executable query. -/
theorem equationQueryCandidateRel_iff_occurrence
    (space : Space) (live : List Atom) (query : Atom) (incoming : Bindings)
    (emitted : Atom) (output : Bindings) :
    EquationQueryCandidateRel space live query incoming emitted output ↔
      ∃ position rawLhs rawRhs freshPattern freshRhs matched,
        EquationQueryOccurrenceRel space live query incoming position
          rawLhs rawRhs freshPattern freshRhs matched emitted output := by
  constructor
  · rintro ⟨freshPattern, freshRhs, matched, ⟨rawLhs, rawRhs, stored, selected⟩, result⟩
    obtain ⟨position, atPosition⟩ := List.mem_iff_getElem?.mp stored
    exact ⟨position, rawLhs, rawRhs, freshPattern, freshRhs, matched,
      ⟨atPosition, selected, result⟩⟩
  · rintro ⟨position, rawLhs, rawRhs, freshPattern, freshRhs, matched, occurrence⟩
    exact occurrence.candidate

/-- No selected equation rule matches the query.  This is the spec
counterpart of the unchanged-query result, without an executable empty-list
test. -/
def EquationQueryNoMatchRel
    (space : Space) (live : List Atom) (query : Atom)
    (incoming : Bindings) : Prop :=
  ∀ freshPattern freshRhs matched,
    ¬EquationRuleMatchRel space live query incoming
      freshPattern freshRhs matched

/-- At least one equation rule matches, but every match is eliminated by the
ambient merge or semantic filters. Raw invocation reports `NotReducible`
when the final candidate collection is empty; ordinary return restores the
invocation, just as when no rule matched. -/
def EquationQueryAllFilteredRel
    (space : Space) (live : List Atom) (query : Atom)
    (incoming : Bindings) : Prop :=
  (∃ freshPattern freshRhs matched,
    EquationRuleMatchRel space live query incoming
      freshPattern freshRhs matched) ∧
    ∀ emitted output,
      ¬EquationQueryCandidateRel
        space live query incoming emitted output

/-! ## Boundary examples -/

private theorem mergeEmptyEmpty :
    LogicalMergeRel Bindings.empty Bindings.empty Bindings.empty := by
  refine ⟨BindingSourceAgreement.refl _, fun name => .var name, ?_⟩
  simp [Spec.Type.RuntimeRefinement.TypeBindingSatisfied, Bindings.empty]

private theorem equalSymbolUnifySuccess (branch : Atom) :
    UnifySuccessRel
      (.symbol "a") (.symbol "a") branch
      Bindings.empty branch Bindings.empty := by
  refine ⟨⟨Bindings.empty,
    MatchRel.symSym "a" semanticLoopFree_empty,
    mergeEmptyEmpty⟩, ?_⟩
  intro valuation _
  rfl

/-- Positive unify: equal symbols select the then branch. -/
example : UnifyStep
    (.symbol "a") (.symbol "a") (.symbol "then") (.symbol "else")
    Bindings.empty (.symbol "then") Bindings.empty :=
  .success (equalSymbolUnifySuccess (.symbol "then"))

private theorem distinctSymbolUnifyNoMatch :
    UnifyNoMatchRel
      (.symbol "a") (.symbol "b") Bindings.empty := by
  intro output hcandidate
  obtain ⟨matched, hmatch, _⟩ := hcandidate
  exact symbol_mismatch_not_match (by decide) matched hmatch

/-- Negative unify: distinct symbols select the else branch. -/
example : UnifyStep
    (.symbol "a") (.symbol "b") (.symbol "then") (.symbol "else")
    Bindings.empty (.symbol "else") Bindings.empty :=
  .noMatch distinctSymbolUnifyNoMatch

/-- Positive ordered switch: a failed first branch falls through to the first
successful branch. -/
example : SwitchStep (.symbol "a")
    [.expression [.symbol "b", .symbol "wrong"],
      .expression [.symbol "a", .symbol "right"]]
    Bindings.empty (.symbol "right") Bindings.empty := by
  apply SwitchStep.selected
  · exact SwitchRawRel.miss distinctSymbolUnifyNoMatch
      (SwitchRawRel.hit (by
        simpa only using equalSymbolUnifySuccess (.symbol "right")))
  · decide

/-- Negative ordered switch: an empty branch list yields `Empty`. -/
example : SwitchStep (.symbol "a") [] Bindings.empty
    Atom.empty Bindings.empty :=
  .noMatch SwitchRawRel.nil

private def oneRuleSpace : Space :=
  Space.ofList [
    .expression [.symbol "=", .symbol "a", .symbol "result"]]

private theorem closedSymbolsAlphaVariant :
    AlphaVariantRel [] (.symbol "a") Bindings.empty
      (.symbol "a") (.symbol "result")
      (.symbol "a") (.symbol "result") := by
  refine ⟨id, Function.injective_id,
    AlphaRenameAtomRel.symbol "a", AlphaRenameAtomRel.symbol "result", ?_⟩
  intro name hocc
  rcases hocc with hocc | hocc <;> cases hocc

/-- Positive equation selection: a closed rule in the space supplies a spec
query candidate without any executable query operation. -/
example : EquationQueryCandidateRel oneRuleSpace []
    (.symbol "a") Bindings.empty (.symbol "result") Bindings.empty := by
  refine ⟨.symbol "a", .symbol "result", Bindings.empty, ?_,
    mergeEmptyEmpty, ?_⟩
  · refine ⟨.symbol "a", .symbol "result", ?_, closedSymbolsAlphaVariant,
      MatchRel.symSym "a" semanticLoopFree_empty⟩
    simp [oneRuleSpace, Space.ofList]
  · intro valuation _
    rfl

/-- Negative equation selection: an empty space has no matching rule. -/
example : EquationQueryNoMatchRel Space.empty []
    (.symbol "a") Bindings.empty := by
  intro freshPattern freshRhs matched hmatch
  obtain ⟨rawLhs, rawRhs, hmem, _⟩ := hmatch
  simp [Space.empty] at hmem

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps

namespace Mettapedia.Languages.MeTTa.HE.EquationFreshening
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval.Steps Spec.Type.RuntimeRefinement

mutual

/-- Whole-atom renaming realizes the independent structural judgment. -/
theorem rename_alpha (rename : String → String) (atom : Atom) :
    AlphaRenameAtomRel rename atom (renameTypeVars rename atom) := by
  cases atom with
  | symbol name => simpa [renameTypeVars] using AlphaRenameAtomRel.symbol (rename := rename) name
  | var name => simpa [renameTypeVars] using AlphaRenameAtomRel.variable (rename := rename) name
  | grounded value => simpa [renameTypeVars] using AlphaRenameAtomRel.grounded (rename := rename) value
  | expression atoms =>
    simpa [renameTypeVars] using AlphaRenameAtomRel.expression (rename_list_alpha rename atoms)
termination_by 2 * sizeOf atom

theorem rename_list_alpha (rename : String → String) (atoms : List Atom) :
    AlphaRenameAtomsRel rename atoms (atoms.map (renameTypeVars rename)) := by
  cases atoms with
  | nil => exact .nil
  | cons head tail => exact .cons (rename_alpha rename head) (rename_list_alpha rename tail)
termination_by 2 * sizeOf atoms + 1
decreasing_by
  all_goals simp_wf
  all_goals omega

end

mutual

/-- The independent structural renaming fixes one exact renamed atom. -/
theorem alphaRename_eq {rename : String → String} {source target : Atom}
    (renamed : AlphaRenameAtomRel rename source target) :
    target = renameTypeVars rename source := by
  cases renamed with
  | symbol => simp [renameTypeVars]
  | «variable» => simp [renameTypeVars]
  | grounded => simp [renameTypeVars]
  | expression children =>
      simpa only [renameTypeVars] using congrArg Atom.expression (alphaRenameAtoms_eq children)

/-- List companion of the exact structural renaming law. -/
theorem alphaRenameAtoms_eq {rename : String → String} {source target : List Atom}
    (renamed : AlphaRenameAtomsRel rename source target) :
    target = source.map (renameTypeVars rename) := by
  cases renamed with
  | nil => rfl
  | cons first rest => exact congrArg₂ List.cons (alphaRename_eq first) (alphaRenameAtoms_eq rest)

end

end Mettapedia.Languages.MeTTa.HE.EquationFreshening

/-! ## Simultaneous variable renaming

The same permutation acts on the complete query, live syntax, binding record
and stored equation table. Rule positions and repeated rows are retained.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.ScopeObservation Spec.Bindings.ScopeObservation

@[simp] theorem renameTypeVars_perm_inverse_reverse (p : Equiv.Perm String) (atom : Atom) :
    renameTypeVars p (renameTypeVars p.symm atom) = atom :=
  renameTypeVars_perm_inverse p.symm atom

@[simp] theorem atoms_inverse (permutation : Equiv.Perm String) (atoms : List Atom) :
    (atoms.map (renameTypeVars permutation)).map (renameTypeVars permutation.symm) = atoms := by
  simp only [List.map_map, Function.comp_def, renameTypeVars_perm_inverse]
  exact List.map_id atoms

def space (permutation : Equiv.Perm String) (source : Space) : Space :=
  ⟨source.atoms.map (renameTypeVars permutation)⟩

@[simp] theorem space_inverse (permutation : Equiv.Perm String) (source : Space) :
    space permutation.symm (space permutation source) = source := by
  cases source
  simp only [space, atoms_inverse]

@[simp] theorem space_inverse_reverse (permutation : Equiv.Perm String) (source : Space) :
    space permutation (space permutation.symm source) = source := space_inverse permutation.symm source

@[simp] theorem atom_symbol (permutation : Equiv.Perm String) (name : String) :
    renameTypeVars permutation (.symbol name) = .symbol name := by simp [renameTypeVars]
@[simp] theorem atom_var (permutation : Equiv.Perm String) (name : String) :
    renameTypeVars permutation (.var name) = .var (permutation name) := by simp [renameTypeVars]
@[simp] theorem atom_grounded (permutation : Equiv.Perm String) (value : GroundedValue) :
    renameTypeVars permutation (.grounded value) = .grounded value := by simp [renameTypeVars]
@[simp] theorem atom_expr (permutation : Equiv.Perm String) (atoms : List Atom) :
    renameTypeVars permutation (.expression atoms) =
      .expression (atoms.map (renameTypeVars permutation)) := by simp [renameTypeVars]

@[simp] theorem atom_eq_symbol (permutation : Equiv.Perm String) (atom : Atom) (name : String) :
    renameTypeVars permutation atom = .symbol name ↔ atom = .symbol name := by
  exact (renameTypeVars_perm_injective permutation).eq_iff' (by simp)

@[simp] theorem atom_eq_grounded (permutation : Equiv.Perm String) (atom : Atom) (value : GroundedValue) :
    renameTypeVars permutation atom = .grounded value ↔ atom = .grounded value := by
  exact (renameTypeVars_perm_injective permutation).eq_iff' (by simp)

@[simp] theorem atom_empty (permutation : Equiv.Perm String) :
    renameTypeVars permutation Atom.empty = Atom.empty := by simp [Atom.empty]
@[simp] theorem atom_notReducible (permutation : Equiv.Perm String) :
    renameTypeVars permutation Atom.notReducible = Atom.notReducible := by simp [Atom.notReducible]

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.ScopeObservation
open Spec.Bindings.ScopeObservation Spec.Match.Merge Spec.Eval.Steps
open LeaTTaBridge

/-- Reindex the complete binding theory, including all repeated rows. -/
theorem binding_satisfied (rename : String → String) (bindings : Bindings)
    (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation (renameBindings rename bindings) ↔
      HEBindingSatisfied (valuation ∘ rename) bindings := by
  constructor
  · intro satisfied
    constructor
    · intro name value member
      have renamed := satisfied.1 (rename name) (renameTypeVars rename value)
        (List.mem_map.mpr ⟨(name,value),member,rfl⟩)
      simpa only [EquationFreshening.applyClassSolution_renameTypeVars,Function.comp_apply] using renamed
    · intro left right member
      exact satisfied.2 (rename left) (rename right) (List.mem_map.mpr ⟨(left,right),member,rfl⟩)
  · intro satisfied
    constructor
    · intro name value member
      change (name,value) ∈ bindings.assignments.map
        (fun row=>(rename row.1,renameTypeVars rename row.2)) at member
      obtain ⟨⟨key,stored⟩,original,same⟩ := List.mem_map.mp member
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl,rfl⟩ := same
      simpa only [EquationFreshening.applyClassSolution_renameTypeVars,Function.comp_apply] using
        satisfied.1 key stored original
    · intro left right member
      change (left,right) ∈ bindings.equalities.map (fun edge=>(rename edge.1,rename edge.2)) at member
      obtain ⟨⟨first,second⟩,original,same⟩ := List.mem_map.mp member
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl,rfl⟩ := same
      exact satisfied.2 first second original

theorem atom_equation (rename : String → String) (left right : Atom)
    (valuation : String → Metta.Atom) :
    HEAtomEquationSatisfied valuation (renameTypeVars rename left) (renameTypeVars rename right) ↔
      HEAtomEquationSatisfied (valuation ∘ rename) left right := by
  simp only [HEAtomEquationSatisfied,EquationFreshening.applyClassSolution_renameTypeVars]

theorem binding_model (permutation : Equiv.Perm String) {bindings : Bindings}
    (model : ∃ valuation,HEBindingSatisfied valuation bindings) :
    ∃ valuation,HEBindingSatisfied valuation (renameBindings permutation bindings) := by
  obtain ⟨valuation,satisfied⟩ := model
  refine ⟨valuation ∘ permutation.symm,(binding_satisfied _ _ _).mpr ?_⟩
  simpa [Function.comp_def] using satisfied

private theorem query_visible_forward (p : Equiv.Perm String) {live : List Atom} {query : Atom}
    {bindings : Bindings} {name : String} (visible : QueryVisibleName live query bindings name) :
    QueryVisibleName (live.map (renameTypeVars p)) (renameTypeVars p query)
      (renameBindings p bindings) (p name) := by
  rcases visible with occurs | ⟨atom,member,occurs⟩ | ⟨value,member⟩ |
    ⟨key,value,member,occurs⟩ | ⟨left,right,member,equal⟩
  · exact Or.inl (occurs.rename p)
  · exact Or.inr (Or.inl ⟨renameTypeVars p atom,List.mem_map.mpr ⟨atom,member,rfl⟩,occurs.rename p⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨renameTypeVars p value,List.mem_map.mpr ⟨(name,value),member,rfl⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p key,renameTypeVars p value,
      List.mem_map.mpr ⟨(key,value),member,rfl⟩,occurs.rename p⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p left,p right,List.mem_map.mpr ⟨(left,right),member,rfl⟩,
      equal.imp (congrArg p) (congrArg p)⟩)))

theorem query_visible (p : Equiv.Perm String) (live : List Atom) (query : Atom)
    (bindings : Bindings) (name : String) :
    QueryVisibleName (live.map (renameTypeVars p)) (renameTypeVars p query)
      (renameBindings p bindings) (p name) ↔ QueryVisibleName live query bindings name := by
  constructor
  · intro visible
    simpa only [atoms_inverse,renameTypeVars_perm_inverse,renameBindings_perm_inverse,Equiv.symm_apply_apply]
      using query_visible_forward p.symm visible
  · exact query_visible_forward p

theorem conjugate_atom (permutation : Equiv.Perm String) (rename : String → String) (atom : Atom) :
    renameTypeVars (fun name=>permutation (rename (permutation.symm name)))
      (renameTypeVars permutation atom) = renameTypeVars permutation (renameTypeVars rename atom) := by
  rw [renameTypeVars_comp,renameTypeVars_comp]
  congr 1
  funext name
  simp

/-- A whole configuration action conjugates the private freshening function;
it preserves the independent capture-avoidance boundary. -/
theorem alpha_variant (permutation : Equiv.Perm String)
    {live : List Atom} {query rawLhs rawRhs freshLhs freshRhs : Atom} {incoming : Bindings}
    (variant : AlphaVariantRel live query incoming rawLhs rawRhs freshLhs freshRhs) :
    AlphaVariantRel (live.map (renameTypeVars permutation)) (renameTypeVars permutation query)
      (renameBindings permutation incoming) (renameTypeVars permutation rawLhs)
      (renameTypeVars permutation rawRhs) (renameTypeVars permutation freshLhs)
      (renameTypeVars permutation freshRhs) := by
  obtain ⟨rename,injective,left,right,fresh⟩ := variant
  refine ⟨fun name=>permutation (rename (permutation.symm name)),?_,?_,?_,?_⟩
  · exact permutation.injective.comp (injective.comp permutation.symm.injective)
  · rw [EquationFreshening.alphaRename_eq left,←conjugate_atom]
    exact EquationFreshening.rename_alpha _ _
  · rw [EquationFreshening.alphaRename_eq right,←conjugate_atom]
    exact EquationFreshening.rename_alpha _ _
  · intro name occurs visible
    have sourceOccurs : AtomOccurs rawLhs (permutation.symm name) ∨
        AtomOccurs rawRhs (permutation.symm name) := by
      rcases occurs with leftOccurs | rightOccurs
      · exact Or.inl ((AtomOccurs.rename_iff permutation rawLhs (permutation.symm name)).mp (by simpa using leftOccurs))
      · exact Or.inr ((AtomOccurs.rename_iff permutation rawRhs (permutation.symm name)).mp (by simpa using rightOccurs))
    exact fresh _ sourceOccurs ((query_visible permutation live query incoming _).mp visible)

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Match.Merge Spec.Eval.Steps
open LeaTTaBridge

theorem match_rename (p : Equiv.Perm String) {left right : Atom} {output : Bindings}
    (derived : MatchRel equalityGroundedSemantic left right output) :
    MatchRel equalityGroundedSemantic (renameTypeVars p left) (renameTypeVars p right)
      (renameBindings p output) := by
  simpa only [Parameters.rename_equalityGroundedSemantic] using derived.rename p

theorem merge_rename (p : Equiv.Perm String) {left right output : Bindings}
    (derived : MergeRel equalityGroundedSemantic left right output) :
    MergeRel equalityGroundedSemantic (renameBindings p left) (renameBindings p right)
      (renameBindings p output) := by
  simpa only [Parameters.rename_equalityGroundedSemantic] using derived.rename p

theorem unify_candidate (p : Equiv.Perm String) {target pattern : Atom} {incoming output : Bindings}
    (candidate : UnifyCandidateRel target pattern incoming output) :
    UnifyCandidateRel (renameTypeVars p target) (renameTypeVars p pattern)
      (renameBindings p incoming) (renameBindings p output) := by
  obtain ⟨matched,matchedRule,merged⟩ := candidate
  exact ⟨renameBindings p matched,match_rename p matchedRule,merged.rename p⟩

theorem unify_success (p : Equiv.Perm String) {target pattern thenBranch emitted : Atom}
    {incoming output : Bindings} (derived : UnifySuccessRel target pattern thenBranch incoming emitted output) :
    UnifySuccessRel (renameTypeVars p target) (renameTypeVars p pattern) (renameTypeVars p thenBranch)
      (renameBindings p incoming) (renameTypeVars p emitted) (renameBindings p output) := by
  refine ⟨unify_candidate p derived.1,?_⟩
  intro valuation satisfied
  exact (atom_equation _ _ _ _).mpr (derived.2 _ ((binding_satisfied _ _ _).mp satisfied))

theorem unify_no_match (p : Equiv.Perm String) {target pattern : Atom} {incoming : Bindings}
    (missing : UnifyNoMatchRel target pattern incoming) :
    UnifyNoMatchRel (renameTypeVars p target) (renameTypeVars p pattern) (renameBindings p incoming) := by
  intro output candidate
  apply missing (renameBindings p.symm output)
  simpa only [renameTypeVars_perm_inverse,renameBindings_perm_inverse] using unify_candidate p.symm candidate

theorem unify_step (p : Equiv.Perm String) {target pattern thenBranch elseBranch emitted : Atom}
    {incoming output : Bindings} (derived : UnifyStep target pattern thenBranch elseBranch incoming emitted output) :
    UnifyStep (renameTypeVars p target) (renameTypeVars p pattern) (renameTypeVars p thenBranch)
      (renameTypeVars p elseBranch) (renameBindings p incoming) (renameTypeVars p emitted) (renameBindings p output) := by
  cases derived with
  | success success => exact .success (unify_success p success)
  | noMatch missing => exact .noMatch (unify_no_match p missing)

def switch_outcome (p : Equiv.Perm String) : SwitchRawOutcome → SwitchRawOutcome
  | .selected atom bindings=>.selected (renameTypeVars p atom) (renameBindings p bindings)
  | .noMatch=>.noMatch

theorem switch_raw (p : Equiv.Perm String) {scrutinee : Atom} {incoming : Bindings}
    {branches : List Atom} {outcome : SwitchRawOutcome} (derived : SwitchRawRel scrutinee incoming branches outcome) :
    SwitchRawRel (renameTypeVars p scrutinee) (renameBindings p incoming)
      (branches.map (renameTypeVars p)) (switch_outcome p outcome) := by
  induction derived with
  | nil => exact .nil
  | @malformed branch branches outcome malformed rest ih =>
    apply SwitchRawRel.malformed _ ih
    intro pattern template same
    apply malformed (renameTypeVars p.symm pattern) (renameTypeVars p.symm template)
    simpa using congrArg (renameTypeVars p.symm) same
  | hit hit => simpa [switch_outcome] using SwitchRawRel.hit (unify_success p hit)
  | miss missing rest ih => simpa using SwitchRawRel.miss (unify_no_match p missing) ih

theorem switch_step (p : Equiv.Perm String) {scrutinee emitted : Atom} {branches : List Atom}
    {incoming output : Bindings} (derived : SwitchStep scrutinee branches incoming emitted output) :
    SwitchStep (renameTypeVars p scrutinee) (branches.map (renameTypeVars p))
      (renameBindings p incoming) (renameTypeVars p emitted) (renameBindings p output) := by
  cases derived with
  | noMatch scan => simpa only [atom_empty] using SwitchStep.noMatch (switch_raw p scan)
  | notReducible scan =>
    simpa only [atom_empty] using SwitchStep.notReducible
      (by simpa [switch_outcome] using switch_raw p scan)
  | selected scan nonNR =>
    exact .selected (switch_raw p scan) (by simpa [Atom.notReducible] using nonNR)

theorem rule_instance (p : Equiv.Perm String) {live : List Atom}
    {query lhs rhs freshPattern freshRhs : Atom} {incoming matched : Bindings}
    (selected : EquationRuleInstanceRel live query incoming lhs rhs freshPattern freshRhs matched) :
    EquationRuleInstanceRel (live.map (renameTypeVars p)) (renameTypeVars p query) (renameBindings p incoming)
      (renameTypeVars p lhs) (renameTypeVars p rhs) (renameTypeVars p freshPattern) (renameTypeVars p freshRhs)
      (renameBindings p matched) := ⟨alpha_variant p selected.1,match_rename p selected.2⟩

theorem rule_match (p : Equiv.Perm String) {context : Space} {live : List Atom}
    {query freshPattern freshRhs : Atom} {incoming matched : Bindings}
    (selected : EquationRuleMatchRel context live query incoming freshPattern freshRhs matched) :
    EquationRuleMatchRel (space p context) (live.map (renameTypeVars p)) (renameTypeVars p query)
      (renameBindings p incoming) (renameTypeVars p freshPattern) (renameTypeVars p freshRhs)
      (renameBindings p matched) := by
  obtain ⟨lhs,rhs,stored,instantiated⟩ := selected
  refine ⟨renameTypeVars p lhs,renameTypeVars p rhs,?_,rule_instance p instantiated⟩
  exact List.mem_map.mpr ⟨.expression [.symbol "=",lhs,rhs],stored,by simp⟩

theorem query_result (p : Equiv.Perm String) {incoming matched output : Bindings} {freshRhs emitted : Atom}
    (selected : EquationQueryResultRel incoming matched freshRhs emitted output) :
    EquationQueryResultRel (renameBindings p incoming) (renameBindings p matched)
      (renameTypeVars p freshRhs) (renameTypeVars p emitted) (renameBindings p output) := by
  refine ⟨selected.1.rename p,?_⟩
  intro valuation satisfied
  exact (atom_equation _ _ _ _).mpr (selected.2 _ ((binding_satisfied _ _ _).mp satisfied))

theorem query_candidate (p : Equiv.Perm String) {context : Space} {live : List Atom} {query emitted : Atom}
    {incoming output : Bindings} (selected : EquationQueryCandidateRel context live query incoming emitted output) :
    EquationQueryCandidateRel (space p context) (live.map (renameTypeVars p)) (renameTypeVars p query)
      (renameBindings p incoming) (renameTypeVars p emitted) (renameBindings p output) := by
  obtain ⟨pattern,rhs,matched,selected,observed⟩ := selected
  exact ⟨renameTypeVars p pattern,renameTypeVars p rhs,renameBindings p matched,
    rule_match p selected,query_result p observed⟩

/-- The very same stored row position survives the simultaneous action.
Equal-valued equations in different positions remain different occurrences. -/
theorem query_occurrence (p : Equiv.Perm String) {context : Space} {live : List Atom}
    {query lhs rhs freshPattern freshRhs emitted : Atom} {incoming matched output : Bindings} {position : Nat}
    (selected : EquationQueryOccurrenceRel context live query incoming position lhs rhs freshPattern freshRhs
      matched emitted output) :
    EquationQueryOccurrenceRel (space p context) (live.map (renameTypeVars p)) (renameTypeVars p query)
      (renameBindings p incoming) position (renameTypeVars p lhs) (renameTypeVars p rhs)
      (renameTypeVars p freshPattern) (renameTypeVars p freshRhs) (renameBindings p matched)
      (renameTypeVars p emitted) (renameBindings p output) := by
  refine ⟨?_,rule_instance p selected.selected,query_result p selected.result⟩
  simp [space,List.getElem?_map,selected.stored]

theorem query_no_match (p : Equiv.Perm String) {context : Space} {live : List Atom} {query : Atom}
    {incoming : Bindings} (missing : EquationQueryNoMatchRel context live query incoming) :
    EquationQueryNoMatchRel (space p context) (live.map (renameTypeVars p)) (renameTypeVars p query)
      (renameBindings p incoming) := by
  intro pattern rhs matched selected
  apply missing (renameTypeVars p.symm pattern) (renameTypeVars p.symm rhs) (renameBindings p.symm matched)
  simpa only [space_inverse,atoms_inverse,renameTypeVars_perm_inverse,renameBindings_perm_inverse] using rule_match p.symm selected

theorem query_filtered (p : Equiv.Perm String) {context : Space} {live : List Atom} {query : Atom}
    {incoming : Bindings} (filtered : EquationQueryAllFilteredRel context live query incoming) :
    EquationQueryAllFilteredRel (space p context) (live.map (renameTypeVars p)) (renameTypeVars p query)
      (renameBindings p incoming) := by
  obtain ⟨⟨pattern,rhs,matched,selected⟩,refused⟩ := filtered
  refine ⟨⟨renameTypeVars p pattern,renameTypeVars p rhs,renameBindings p matched,rule_match p selected⟩,?_⟩
  intro emitted output candidate
  apply refused (renameTypeVars p.symm emitted) (renameBindings p.symm output)
  simpa only [space_inverse,atoms_inverse,renameTypeVars_perm_inverse,renameBindings_perm_inverse] using query_candidate p.symm candidate

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming


namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation Spec.Match.Merge

/-- Representation changes preserve logical success without imposing a shape
condition on the caller's assignment rows. -/
theorem unifyCandidate_congr_incoming {target pattern : Atom} {incoming other output : Bindings}
    (agreement : BindingSourceAgreement incoming other) :
    UnifyCandidateRel target pattern incoming output ↔ UnifyCandidateRel target pattern other output := by
  constructor
  · rintro ⟨matched, matching, logical⟩
    exact ⟨matched, matching,
      (LogicalMergeRel.congr_inputs (BindingSourceAgreement.refl matched) agreement).mp logical⟩
  · rintro ⟨matched, matching, logical⟩
    exact ⟨matched, matching,
      (LogicalMergeRel.congr_inputs (BindingSourceAgreement.refl matched) agreement).mpr logical⟩

theorem unifyNoMatch_congr_incoming {target pattern : Atom} {incoming other : Bindings}
    (agreement : BindingSourceAgreement incoming other) :
    UnifyNoMatchRel target pattern incoming ↔ UnifyNoMatchRel target pattern other := by
  constructor
  · intro missing output candidate
    exact missing output ((unifyCandidate_congr_incoming agreement).mpr candidate)
  · intro missing output candidate
    exact missing output ((unifyCandidate_congr_incoming agreement).mp candidate)

/-- Existence of a successful output is precisely a match with a common finite
model. This constructs the output constraints and does not assume a saved run. -/
theorem unifyCandidate_exists_iff_common_model (target pattern : Atom) (incoming : Bindings) :
    (∃ output, UnifyCandidateRel target pattern incoming output) ↔
      ∃ matched, MatchRel equalityGroundedSemantic target pattern matched ∧
        ∃ valuation : String → Atom,
          TypeBindingSatisfied valuation matched ∧ TypeBindingSatisfied valuation incoming := by
  constructor
  · rintro ⟨output, matched, matching, logical⟩
    exact ⟨matched, matching, logical.common_model⟩
  · rintro ⟨matched, matching, common⟩
    exact ⟨_, matched, matching, LogicalMergeRel.append_of_common_model common⟩

theorem unifyNoMatch_iff_no_common_model (target pattern : Atom) (incoming : Bindings) :
    UnifyNoMatchRel target pattern incoming ↔
      ∀ matched, MatchRel equalityGroundedSemantic target pattern matched →
        ¬∃ valuation : String → Atom,
          TypeBindingSatisfied valuation matched ∧ TypeBindingSatisfied valuation incoming := by
  constructor
  · intro missing matched matching common
    obtain ⟨output, candidate⟩ := (unifyCandidate_exists_iff_common_model target pattern incoming).mpr
      ⟨matched, matching, common⟩
    exact missing output candidate
  · intro noCommon output candidate
    obtain ⟨matched, matching, logical⟩ := candidate
    exact noCommon matched matching logical.common_model

theorem equationQueryResult_congr_inputs {incoming other matched otherMatched output : Bindings}
    {freshRhs emitted : Atom} (caller : BindingSourceAgreement incoming other)
    (matching : BindingSourceAgreement matched otherMatched) :
    EquationQueryResultRel incoming matched freshRhs emitted output ↔
      EquationQueryResultRel other otherMatched freshRhs emitted output := by
  exact and_congr (LogicalMergeRel.congr_inputs matching caller) Iff.rfl

/-- The negative query judgment retains its quantification over every actual
freshened match. Finite incompatibility, rather than a concrete row layout,
excludes its possible outputs. -/
theorem equationQueryAllFiltered_iff_no_common_model
    (space : Space) (live : List Atom) (query : Atom) (incoming : Bindings) :
    EquationQueryAllFilteredRel space live query incoming ↔
      (∃ freshPattern freshRhs matched,
        EquationRuleMatchRel space live query incoming freshPattern freshRhs matched) ∧
      ∀ freshPattern freshRhs matched,
        EquationRuleMatchRel space live query incoming freshPattern freshRhs matched →
          ¬∃ valuation : String → Atom,
            TypeBindingSatisfied valuation matched ∧ TypeBindingSatisfied valuation incoming := by
  constructor
  · rintro ⟨existsMatch, filtered⟩
    refine ⟨existsMatch, ?_⟩
    intro pattern rhs matched matching common
    apply filtered rhs _
    exact ⟨pattern, rhs, matched, matching,
      LogicalMergeRel.append_of_common_model common, fun _ _ => rfl⟩
  · rintro ⟨existsMatch, incompatible⟩
    refine ⟨existsMatch, ?_⟩
    rintro emitted output ⟨pattern, rhs, matched, matching, logical, _observed⟩
    exact incompatible pattern rhs matched matching logical.common_model

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps


namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.LogicalMergeControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Match.Merge

def aliases : Bindings := ⟨[("u", .var "w"), ("w", .var "v")], []⟩
def matched : Bindings := Bindings.empty.addEquality "u" "v"
def conjoined : Bindings := ⟨aliases.assignments, matched.equalities⟩

theorem aliases_model : TypeBindingSatisfied (fun _ => .symbol "One") aliases := by
  constructor
  · intro name value stored
    have alternatives : (name = "u" ∧ value = .var "w") ∨
        (name = "w" ∧ value = .var "v") := by simpa [aliases] using stored
    rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [applyTypeValuation]
  · intro left right stored
    simp [aliases] at stored

theorem logical_alias_conjunction : LogicalMergeRel matched aliases conjoined := by
  exact LogicalMergeRel.append_of_common_model
    ⟨fun _ => .symbol "One", by simp [TypeBindingSatisfied, matched, Bindings.empty, Bindings.addEquality],
      aliases_model⟩

theorem redundant_alias_accepted : UnifyCandidateRel (.var "u") (.var "v") aliases conjoined :=
  ⟨matched, .varVar _ _ (semanticLoopFree_of_assignments_nil rfl), logical_alias_conjunction⟩

theorem redundant_alias_cannot_be_refused : ¬UnifyNoMatchRel (.var "u") (.var "v") aliases :=
  fun refused => refused conjoined redundant_alias_accepted

theorem representative_cycle_does_not_make_constraints_inconsistent :
    conjoined.hasLoop = true ∧ LogicalMergeRel matched aliases conjoined :=
  ⟨by decide +kernel, logical_alias_conjunction⟩

theorem conflicting_ground_assignment_refused :
    UnifyNoMatchRel (.var "x") (.symbol "A") (⟨[("x", .symbol "B")], []⟩ : Bindings) := by
  rintro output ⟨candidate, matching, logical⟩
  cases matching with
  | varNonVar _ _ =>
    obtain ⟨valuation, first, second⟩ := logical.common_model
    have a := first.1 "x" (.symbol "A") (by
      simp [Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup])
    have b := second.1 "x" (.symbol "B") (by simp)
    have impossible := a.symm.trans b
    simp [applyTypeValuation] at impossible

theorem structural_occurs_refused :
    UnifyNoMatchRel (.var "x") (.expression [.symbol "F", .var "x"]) Bindings.empty := by
  rintro output ⟨candidate, matching, _logical⟩
  cases matching with
  | varNonVar _ free =>
    apply (semanticLoopFree_single_assignment_iff.mp free)
    exact .expression (by simp) (.var _)

theorem tautological_support_cannot_disappear :
    ¬LogicalMergeRel (⟨[], [("ghost", "ghost")]⟩ : Bindings) Bindings.empty Bindings.empty := by
  intro merged
  have names := merged.support "ghost"
  simp [specBindingVars, Bindings.empty] at names

def duplicated : Space := Space.ofList
  [.expression [.symbol "=", .symbol "A", .symbol "Result"],
   .expression [.symbol "=", .symbol "A", .symbol "Result"]]

private theorem duplicated_at (position : Nat)
    (stored : duplicated.atoms[position]? = some (.expression [.symbol "=", .symbol "A", .symbol "Result"])) :
    EquationQueryOccurrenceRel duplicated [] (.symbol "A") aliases position
      (.symbol "A") (.symbol "Result") (.symbol "A") (.symbol "Result")
      Bindings.empty (.symbol "Result") aliases := by
  refine ⟨stored, ⟨?_, .symSym _ semanticLoopFree_empty⟩, ?_, ?_⟩
  · refine ⟨id, Function.injective_id, .symbol _, .symbol _, ?_⟩
    intro name occurs
    rcases occurs with occurs | occurs <;> cases occurs
  · exact ⟨BindingSourceAgreement.refl _, _, aliases_model⟩
  · intro valuation _model
    rfl

theorem both_physical_occurrences_retained :
    EquationQueryOccurrenceRel duplicated [] (.symbol "A") aliases 0
      (.symbol "A") (.symbol "Result") (.symbol "A") (.symbol "Result")
      Bindings.empty (.symbol "Result") aliases ∧
    EquationQueryOccurrenceRel duplicated [] (.symbol "A") aliases 1
      (.symbol "A") (.symbol "Result") (.symbol "A") (.symbol "Result")
      Bindings.empty (.symbol "Result") aliases :=
  ⟨duplicated_at 0 (by rfl), duplicated_at 1 (by rfl)⟩

theorem absent_physical_position_refused :
    ¬EquationQueryOccurrenceRel duplicated [] (.symbol "A") aliases 2
      (.symbol "A") (.symbol "Result") (.symbol "A") (.symbol "Result")
      Bindings.empty (.symbol "Result") aliases := by
  intro occurrence
  have impossible := occurrence.stored
  simp [duplicated, Space.ofList] at impossible

theorem duplicate_query_not_all_filtered :
    ¬EquationQueryAllFilteredRel duplicated [] (.symbol "A") aliases := by
  intro filtered
  exact filtered.2 _ _ both_physical_occurrences_retained.1.candidate

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.LogicalMergeControls
