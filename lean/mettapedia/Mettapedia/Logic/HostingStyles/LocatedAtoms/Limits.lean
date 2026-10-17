import Mettapedia.Logic.HostingStyles.LocatedAtoms.Compare

/-!
# Located atoms: what the reading decides, and what it does not reach

* **The normal form decides the class of the run of an atom**
  (`related_runAtom_iff`): a term is equal to the run of the atom of a term,
  in the space of a list of rules, exactly when its normal form is the atom
  pushed in that space.
* **One step is one transition** (`locatedTermsMap_steps`): a reduction of a
  number of steps is a reduction of that number of transitions between the
  runs.
* **The evaluator does not take its rules from the space of the run premise**
  (`locatedEvaluator_not_rulesFromSpace`): it takes them from the space in
  which the subject is located, and where that space stores no atom it
  answers nothing (`locatedAnswers_of_stores_nothing`).
* **With its contexts as they are the candidate receives no map from a
  theory on the terms with free variables below a width**
  (`located_isEmpty_contextMap_scoped`): a context of the source may leave a
  hole unused, for any number of holes, and a context of the candidate uses
  each of its holes once.  The readings in which the holes of atoms are free
  are needed.
* **A rule whose right side binds is not hosted** by this reading
  (`located_bindingRule_not_preserved`): the evaluator answers nothing for
  an equation whose right side is an abstraction.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.LocatedAtoms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti
  (Theory RuleTable rewritingTheory TermContext patternVars usesOnly constantFunctionRule
    normal_of_normalTest)
open Mettapedia.GSLT.Dedukti.Language (metaName)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)
open Mettapedia.Logic.HostingStyles.AmbientSpace (pureCover)

variable {base : BasePremiseEvaluator}

/-! ## The normal form decides the class of a run -/

/-- **A term is equal to the run of the atom of a term exactly when its
normal form is the atom pushed in the space.** -/
theorem related_runAtom_iff {rules : List Dedukti.RewriteRule} {depth : Nat} {term : LF.Term}
    {other : Contexts.Term located (atomInterface depth)} :
    (termSetoid base located (atomInterface depth)).r other (runAtom rules depth term) ↔
      settle other.1 = push (ruleSpace rules) (atomAt depth term) := by
  constructor
  · intro related
    rw [settle_eq_of_related related]
    exact settle_run_atomAt rules term depth
  · intro normal
    exact (spelled_related (ruleSpaceTerm rules)
      (spells_of_settle (ruleSpace_plain rules) other.2 normal) other.2
      (locatedAtom depth term).2).1 rfl

/-! ## One step is one transition -/

/-- **One step of the theory is one transition of the candidate**: a
reduction of `count` steps is a reduction of `count` transitions between the
runs of the atoms. -/
theorem locatedTermsMap_steps (regions : Contexts.Interface → Prop) {theory : Theory}
    {table : RuleTable} (tabular : theory.Tabular table) (admitted : BoundFirstOrder table)
    {count : Nat} {first final : LF.Term}
    (steps : ((rewritingTheory theory).gslt ()).termsAlone.Steps (interface := PUnit.unit) count
      first final) :
    (locatedTheory.regionReading regions).Steps count (runAtom table.toList 0 first)
      (runAtom table.toList 0 final) :=
  (locatedTermsMap regions theory table.toList).steps_of_preserves
    (locatedTermsMap_hosting regions admitted.listed.1 admitted.listed.2
      (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined).preserves
    steps

/-! ## Where the evaluator takes its rules -/

/-- **Where the space in which the subject is located stores no atom, the
evaluator answers nothing.** -/
theorem locatedAnswers_of_stores_nothing {space subject : Pattern}
    (empty : ∀ inner plain, located? (settle (runPattern space subject)) = some (inner, plain) →
      storedAtoms inner = []) :
    locatedAnswers space subject = [] := by
  unfold locatedAnswers
  cases found : located? (settle (runPattern space subject)) with
  | none => rfl
  | some pair =>
      obtain ⟨inner, plain⟩ := pair
      simp [matchResults, empty inner plain found]

/-- **Negative**: the evaluator of located atoms does not take its rules from
the space of the run premise.  With the empty space there and a subject that
is located in the space of the rule `x ⟶ u`, it answers. -/
theorem locatedEvaluator_not_rulesFromSpace : ¬ RulesFromSpace locatedEvaluator := by
  intro fromSpace
  have spaceValue : applyBindings
      [("subject", runPattern (ruleSpace [takeAll]) unitAtom), ("space", emptySpace)]
      (.fvar "space") = emptySpace := by simp [applyBindings]
  have subjectValue : applyBindings
      [("subject", runPattern (ruleSpace [takeAll]) unitAtom), ("space", emptySpace)]
      (.fvar "subject") = runPattern (ruleSpace [takeAll]) unitAtom := by simp [applyBindings]
  have silent := fromSpace located
    [("subject", runPattern (ruleSpace [takeAll]) unitAtom), ("space", emptySpace)]
    (by rw [spaceValue]; decide)
  have normal : settle (runPattern emptySpace (runPattern (ruleSpace [takeAll]) unitAtom)) =
      push (ruleSpace [takeAll]) unitAtom := by
    rw [settle_runPattern, settle_runPattern, settle_ruleSpace, push_push]
    rfl
  have answered : runPattern (ruleSpace [takeAll]) (atomAt 0 (.con "u")) ∈
      locatedAnswers emptySpace (runPattern (ruleSpace [takeAll]) unitAtom) := by
    rw [locatedAnswers_of_settle normal (by decide)]
    refine List.mem_map.mpr ⟨_, ?_, rfl⟩
    refine (mem_matchResults_ruleSpace takeAll_admitted.1).mpr
      ⟨takeAll, List.mem_singleton.mpr rfl, [(metaName 0, unitAtom)], ?_, ?_⟩
    · show _ ∈ matchPattern (asRule (atomAt 0 (.var 0))) _
      rw [atomAt_freeVariable, asRule_variableAtom]
      simp [matchPattern]
    · show atomAt 0 (.con "u") = applyBindings _ (ruleSide (.con "u"))
      rw [ruleSide_con, applyBindings_symbolAtom]
      rfl
  have member : (("answer", runPattern (ruleSpace [takeAll]) (atomAt 0 (.con "u"))) ::
      [("subject", runPattern (ruleSpace [takeAll]) unitAtom), ("space", emptySpace)] :
        Bindings) ∈ locatedEvaluator located
          [("subject", runPattern (ruleSpace [takeAll]) unitAtom), ("space", emptySpace)]
          runPremise := by
    show _ ∈ (locatedAnswers
      (applyBindings [("subject", runPattern (ruleSpace [takeAll]) unitAtom),
        ("space", emptySpace)] (.fvar "space"))
      (applyBindings [("subject", runPattern (ruleSpace [takeAll]) unitAtom),
        ("space", emptySpace)] (.fvar "subject"))).map
        fun result => ("answer", result) ::
          [("subject", runPattern (ruleSpace [takeAll]) unitAtom), ("space", emptySpace)]
    rw [spaceValue, subjectValue]
    exact List.mem_map.mpr ⟨_, answered, rfl⟩
  rw [silent] at member
  cases member

/-! ## With the contexts of the candidate as they are -/

/-- **With its contexts as they are the candidate with located atoms receives
no map from a theory on the terms with free variables below a width**, under
any evaluator: the context of the source that is a sort, read with a hole for
every number, uses none of its holes, and its image would use each of them
once. -/
theorem located_isEmpty_contextMap_scoped (base : BasePremiseEvaluator) (width : Nat)
    (theory : Theory) :
    IsEmpty (ContextMap (scopedRewriting width theory)
      (contextTheory base locatedPresentation)) := by
  refine ⟨fun map => ?_⟩
  have image := map.context (holes := fun _ : ℕ => ()) (result := ())
    (⟨.srt .type, trivial⟩ : {context : TermContext ℕ // ScopedContext width context})
  obtain ⟨missing, absent⟩ := Infinite.exists_notMem_finset image.shape.holes.toFinset
  exact absent (List.mem_toFinset.mpr (image.linear.2 missing))

/-! ## A right side that binds -/

/-- **The run of the atom of `k c` has no transition in the space of the rule
`k x ⟶ λ y : Type. x`**: the evaluator answers nothing for an equation whose
right side binds, and `k c` has no beta step. -/
theorem located_bindingRule_normal (target : Contexts.Term located AtomsReduce.closedAtom) :
    ¬ TermStep locatedEvaluator located
      (runAtom [constantFunctionRule] 0 (.app (.con "k") (.con "c"))) target := by
  rintro ⟨redex, contractum, before, ⟨fuel, fired⟩, -⟩
  have normal : settle redex.1 =
      push (ruleSpace [constantFunctionRule]) (atomAt 0 (.app (.con "k") (.con "c"))) := by
    rw [← settle_eq_of_related before]
    exact settle_run_atomAt _ _ 0
  have spelled := spells_of_settle (ruleSpace_plain [constantFunctionRule]) redex.2 normal
  obtain ⟨next, -, sourceStep⟩ :=
    spelled_stepAt (ruleSpace_plain [constantFunctionRule]) (theory := Theory.empty)
      (fun found => by
        rw [matchResults_constantFunctionRule] at found
        cases found) fuel spelled fired
  exact normal_of_normalTest pureCover _ (by decide) _ sourceStep

/-- **A rule whose right side binds is not hosted by this reading**: the
theory contracts `k c`, and the run of the atom of `k c` has no transition in
the space of the rule. -/
theorem located_bindingRule_not_preserved :
    Dedukti.Step (Theory.ofTable {constantFunctionRule}) (.app (.con "k") (.con "c"))
        (.lam (.srt .type) (.con "c")) ∧
      ∀ target : Contexts.Term located AtomsReduce.closedAtom,
        ¬ TermStep locatedEvaluator located
          (runAtom [constantFunctionRule] 0 (.app (.con "k") (.con "c"))) target :=
  ⟨bindingRule_step, located_bindingRule_normal⟩

#print axioms related_runAtom_iff
#print axioms locatedTermsMap_steps
#print axioms locatedAnswers_of_stores_nothing
#print axioms locatedEvaluator_not_rulesFromSpace
#print axioms located_isEmpty_contextMap_scoped
#print axioms located_bindingRule_not_preserved

end Mettapedia.Logic.HostingStyles.LocatedAtoms
