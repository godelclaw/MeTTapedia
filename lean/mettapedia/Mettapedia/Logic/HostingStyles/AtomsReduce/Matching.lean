import Mettapedia.Logic.HostingStyles.AtomsReduce.Encoding

/-!
# Rules as equations in a space of the candidate, and what the matching evaluator answers

A rule of a table is stored in a space as the equation of the atoms of its two
sides (`equationOf`, `ruleSpace`).  The pattern variables of a rule are the
free variables of its sides, so they are stored as variable atoms, and the
matching evaluator reads a variable atom of a stored side as a pattern
variable (`ruleSide`).

For rules without binder whose right sides mention only variables of their
left sides, the answers of the space of a list of rules for the atom of a
term are exactly the atoms of the instances of the rules on that term, **at
every depth** (`mem_matchResults_ruleSpace_iff`): beneath `depth` binders the
assigned terms may mention the variables that those binders bind, which are
bound variables of the pattern and are carried by the bindings as they are.

**What stops a rule whose right side binds** is stated at the end:

* the evaluator admits an equation only when both sides are read as
  first-order patterns, and the reading of an abstraction is not one
  (`atomResults_bindingRight`): it answers nothing;
* the reading of a stored side does not go beneath a binder: a variable atom
  there stays a variable atom (`asRule_beneath_binder`);
* and where a rule is instantiated beneath a binder of its right side, the
  assigned terms have to be lifted, which the instantiation of the evaluator
  does not do (`applyBindings_captures`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AtomsReduce

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Dedukti
  (inst substitute inst_eq_substitute patternVars usesOnly constantFunctionRule)
open Mettapedia.GSLT.Dedukti.Language (metaName metaName_injective)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.Framework.PredFiniteSufficient (matchPattern_applyBindings_complete)
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

/-! ## A side of a rule, as the pattern that the evaluator matches -/

/-- **A side of a rule, as the evaluator reads it** in a space: the atom of
the side, its variable atoms read as pattern variables. -/
def ruleSide (term : LF.Term) : Pattern := asRule (atomAt 0 term)

theorem asRule_symbolAtom (code : Nat) : asRule (symbolAtom code) = symbolAtom code := by
  rw [symbolAtom, asRule_apply_of_ne (by decide)]
  simp [asRule_numeral]

@[simp] theorem ruleSide_var (index : Nat) : ruleSide (.var index) = .fvar (metaName index) := by
  rw [ruleSide, atomAt_freeVariable]
  exact asRule_variableAtom index

theorem ruleSide_srt (sort : LF.Srt) : ruleSide (.srt sort) = symbolAtom (sortCode sort) := by
  rw [ruleSide, atomAt_srt, asRule_symbolAtom]

theorem ruleSide_con (name : String) : ruleSide (.con name) = symbolAtom (nameCode name + 2) :=
  asRule_symbolAtom _

@[simp] theorem ruleSide_app (function argument : LF.Term) :
    ruleSide (.app function argument) = .apply "App" [ruleSide function, ruleSide argument] := by
  rw [ruleSide, atomAt, asRule_apply_of_ne (by decide)]
  rfl

theorem isMatchCorrectAux_symbolAtom (code : Nat) : isMatchCorrectAux (symbolAtom code) = true := by
  simp [symbolAtom, isMatchCorrectAux, isMatchCorrectListAux, isMatchCorrectAux_numeral]

/-- **A side without binder is read as a first-order pattern.** -/
theorem isMatchCorrectAux_ruleSide :
    ∀ {term : LF.Term}, Dedukti.binderFree term = true → isMatchCorrectAux (ruleSide term) = true := by
  intro term
  induction term with
  | var index => intro _; simp [isMatchCorrectAux]
  | con name => intro _; rw [ruleSide_con]; exact isMatchCorrectAux_symbolAtom _
  | srt sort => intro _; rw [ruleSide_srt]; exact isMatchCorrectAux_symbolAtom _
  | app function argument ihFunction ihArgument =>
      intro free
      simp only [Dedukti.binderFree, Bool.and_eq_true] at free
      simp [isMatchCorrectAux, isMatchCorrectListAux, ihFunction free.1, ihArgument free.2]
  | lam domain body _ _ => intro free; simp [Dedukti.binderFree] at free
  | pi domain body _ _ => intro free; simp [Dedukti.binderFree] at free

theorem applyBindings_symbolAtom (bindings : Bindings) (code : Nat) :
    applyBindings bindings (symbolAtom code) = symbolAtom code := by
  simp [symbolAtom, applyBindings, applyBindings_numeral]

/-- **An instance of a side is the atom of the instance of the term**, at
every depth, when the bindings give each variable of the term the atom of its
value at that depth. -/
theorem applyBindings_ruleSide (depth : Nat) (bindings : Bindings) (assignment : Nat → LF.Term) :
    ∀ {term : LF.Term}, Dedukti.binderFree term = true →
      (∀ index ∈ patternVars term,
        applyBindings bindings (.fvar (metaName index)) = atomAt depth (assignment index)) →
        applyBindings bindings (ruleSide term) = atomAt depth (substitute assignment term) := by
  intro term
  induction term with
  | var index =>
      intro _ values
      simpa [substitute] using values index (List.mem_singleton.mpr rfl)
  | con name =>
      intro _ _
      rw [ruleSide_con, applyBindings_symbolAtom]
      rfl
  | srt sort =>
      intro _ _
      rw [ruleSide_srt, applyBindings_symbolAtom]
      exact (atomAt_srt depth sort).symm
  | app function argument ihFunction ihArgument =>
      intro free values
      simp only [Dedukti.binderFree, Bool.and_eq_true] at free
      have left := ihFunction free.1 fun index member =>
        values index (List.mem_append_left _ member)
      have right := ihArgument free.2 fun index member =>
        values index (List.mem_append_right _ member)
      simp [substitute, atomAt, applyBindings, left, right]
  | lam domain body _ _ => intro free; simp [Dedukti.binderFree] at free
  | pi domain body _ _ => intro free; simp [Dedukti.binderFree] at free

/-- The assignment that bindings stand for at a depth: the term whose atom a
variable is bound to. -/
noncomputable def assignmentAt (depth : Nat) (bindings : Bindings) (index : Nat) : LF.Term :=
  open Classical in
  if known : ∃ term, applyBindings bindings (.fvar (metaName index)) = atomAt depth term then
    Classical.choose known
  else .srt .type

theorem assignmentAt_eq {depth : Nat} {bindings : Bindings} {index : Nat} {term : LF.Term}
    (bound : applyBindings bindings (.fvar (metaName index)) = atomAt depth term) :
    assignmentAt depth bindings index = term := by
  have known : ∃ other, applyBindings bindings (.fvar (metaName index)) = atomAt depth other :=
    ⟨term, bound⟩
  unfold assignmentAt
  rw [dif_pos known]
  exact atomAt_injective depth ((Classical.choose_spec known).symm.trans bound)

/-- **What an instance of a side is the atom of**: if an instance of a side
without binder is the atom of a term at a depth, the term is the instance of
the side under the assignment that the bindings stand for there, and each
variable of the side is bound to the atom of its value. -/
theorem substitute_of_applyBindings_ruleSide (depth : Nat) (bindings : Bindings) :
    ∀ {side : LF.Term}, Dedukti.binderFree side = true → ∀ {term : LF.Term},
      applyBindings bindings (ruleSide side) = atomAt depth term →
        term = substitute (assignmentAt depth bindings) side ∧
          ∀ index ∈ patternVars side,
            applyBindings bindings (.fvar (metaName index)) =
              atomAt depth (assignmentAt depth bindings index) := by
  intro side
  induction side with
  | var index =>
      intro _ term same
      rw [ruleSide_var] at same
      have value := assignmentAt_eq same
      refine ⟨by simp [substitute, value], fun other member => ?_⟩
      rw [List.mem_singleton.mp member, value]
      exact same
  | con name =>
      intro _ term same
      rw [ruleSide_con, applyBindings_symbolAtom] at same
      have image : atomAt depth (.con name) = atomAt depth term := same
      exact ⟨(atomAt_injective depth image).symm,
        fun other member => by simp [patternVars] at member⟩
  | srt sort =>
      intro _ term same
      rw [ruleSide_srt, applyBindings_symbolAtom, ← atomAt_srt depth sort] at same
      exact ⟨(atomAt_injective depth same).symm,
        fun other member => by simp [patternVars] at member⟩
  | app function argument ihFunction ihArgument =>
      intro free term same
      simp only [Dedukti.binderFree, Bool.and_eq_true] at free
      have unfolded : applyBindings bindings (ruleSide (.app function argument)) =
          .apply "App" [applyBindings bindings (ruleSide function),
            applyBindings bindings (ruleSide argument)] := by
        simp [applyBindings]
      rw [unfolded] at same
      obtain ⟨first, second, rfl, functionEq, argumentEq⟩ := atomAt_eq_app same.symm
      obtain ⟨functionSame, functionValues⟩ := ihFunction free.1 functionEq
      obtain ⟨argumentSame, argumentValues⟩ := ihArgument free.2 argumentEq
      refine ⟨by simp [substitute, ← functionSame, ← argumentSame], fun index member => ?_⟩
      rcases List.mem_append.mp member with inFunction | inArgument
      · exact functionValues index inFunction
      · exact argumentValues index inArgument
  | lam domain body _ _ => intro free; simp [Dedukti.binderFree] at free
  | pi domain body _ _ => intro free; simp [Dedukti.binderFree] at free

/-- The bindings that give each listed variable the atom of its value at a
depth. -/
def sideBindingsAt (depth : Nat) (indices : List Nat) (assignment : Nat → LF.Term) : Bindings :=
  indices.map fun index => (metaName index, atomAt depth (assignment index))

theorem applyBindings_sideBindingsAt (depth : Nat) (assignment : Nat → LF.Term) :
    ∀ {indices : List Nat} {index : Nat}, index ∈ indices →
      applyBindings (sideBindingsAt depth indices assignment) (.fvar (metaName index)) =
        atomAt depth (assignment index) := by
  intro indices
  induction indices with
  | nil => intro index member; cases member
  | cons head rest ih =>
      intro index member
      rw [sideBindingsAt, List.map_cons, applyBindings_fvar_cons]
      by_cases same : metaName head = metaName index
      · rw [if_pos same, metaName_injective same]
      · rw [if_neg same]
        exact ih ((List.mem_cons.mp member).resolve_left fun equal => same (by rw [equal]))

/-! ## The space of a list of rules -/

/-- **A rule, as an equation stored in a space.** -/
def equationOf (rule : Dedukti.RewriteRule) : Pattern :=
  .apply "=" [atomAt 0 rule.lhs, atomAt 0 rule.rhs]

/-- **The space of a list of rules**: their equations, in order. -/
def ruleSpace (rules : List Dedukti.RewriteRule) : Pattern :=
  spaceOfAtoms (rules.map equationOf)

theorem equationOf_injective : Function.Injective equationOf := by
  intro first second same
  simp only [equationOf, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
  cases first
  cases second
  simp only [Dedukti.RewriteRule.mk.injEq]
  exact ⟨atomAt_injective 0 same.1, atomAt_injective 0 same.2⟩

/-- **The space of a list of rules determines the list.** -/
theorem ruleSpace_injective : Function.Injective ruleSpace := by
  intro first second same
  have stored := congrArg storedAtoms same
  rw [ruleSpace, ruleSpace, storedAtoms_spaceOfAtoms, storedAtoms_spaceOfAtoms] at stored
  exact List.map_injective_iff.mpr equationOf_injective stored

theorem contract_ruleSpace (rules : List Dedukti.RewriteRule) :
    contract (ruleSpace rules) = ruleSpace rules := by
  rw [ruleSpace, contract_spaceOfAtoms, List.map_map]
  congr 1
  apply List.map_congr_left
  intro rule _
  show contract (equationOf rule) = equationOf rule
  rw [equationOf, contract_apply_of_ne (by decide)]
  simp [contract_atomAt]

theorem tokens_spaceOfAtoms {counted : String → Bool} (empty : counted "prime-space-empty" = false)
    (add : counted "prime-space-add" = false) :
    ∀ {atoms : List Pattern}, (∀ atom ∈ atoms, tokens counted atom = 0) →
      tokens counted (spaceOfAtoms atoms) = 0
  | [], _ => by simp [spaceOfAtoms, emptySpace, tokens, tokensList, empty]
  | atom :: atoms, zero => by
      have rest := tokens_spaceOfAtoms empty add fun other member =>
        zero other (List.mem_cons_of_mem _ member)
      simp [spaceOfAtoms, addAtom, tokens, tokensList, add, zero atom (List.mem_cons_self ..), rest]

/-- **The space of a list of rules has no constructor outside those of a
space, of an equation and of the atoms of terms.** -/
theorem tokens_ruleSpace {counted : String → Bool} (empty : counted "prime-space-empty" = false)
    (add : counted "prime-space-add" = false) (equation : counted "=" = false)
    (unit : counted "prime-unit" = false) (variable_ : counted "prime-variable" = false)
    (symbol : counted "prime-symbol" = false) (application : counted "App" = false)
    (abstraction : counted "Lam" = false) (product : counted "Pi" = false)
    (rules : List Dedukti.RewriteRule) : tokens counted (ruleSpace rules) = 0 := by
  refine tokens_spaceOfAtoms empty add fun atom member => ?_
  obtain ⟨rule, -, rfl⟩ := List.mem_map.mp member
  simp [equationOf, tokens, tokensList, equation,
    tokens_atomAt equation unit variable_ symbol application abstraction product]

/-- The space of a list of atoms of the candidate is a space of the
candidate. -/
theorem spaceOfAtoms_wellSorted_atoms {bound : List TypeExpr} :
    ∀ {atoms : List Pattern},
      (∀ atom ∈ atoms, OpenPatternWellSorted atomsReduce FreeTypeContext.empty bound
        (.base "Atom") atom) →
      OpenPatternWellSorted atomsReduce FreeTypeContext.empty bound (.base "Space")
        (spaceOfAtoms atoms)
  | [], _ => wellSorted_apply_zero (lang := atomsReduce) (label := "prime-space-empty") (by decide)
  | atom :: _, sorted =>
      wellSorted_apply_two (lang := atomsReduce) (label := "prime-space-add") (firstName := "atom")
        (secondName := "rest") (by decide) (sorted atom (List.mem_cons_self ..))
        (spaceOfAtoms_wellSorted_atoms fun other member =>
          sorted other (List.mem_cons_of_mem _ member))

/-- **The space of a list of rules is a closed space of the candidate.** -/
theorem ruleSpace_wellSorted (rules : List Dedukti.RewriteRule) :
    OpenPatternWellSorted atomsReduce FreeTypeContext.empty [] (.base "Space") (ruleSpace rules) :=
  spaceOfAtoms_wellSorted_atoms fun atom member => by
    obtain ⟨rule, -, rfl⟩ := List.mem_map.mp member
    exact wellSorted_apply_two (lang := atomsReduce) (label := "=") (firstName := "left")
      (secondName := "right") (by decide) (atomAt_wellSorted rule.lhs 0)
      (atomAt_wellSorted rule.rhs 0)

/-! ## The answers of the space of a list of rules -/

/-- The answers of the space of a list of first-order rules. -/
theorem mem_matchResults_ruleSpace {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules, Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    {subject answer : Pattern} :
    answer ∈ matchResults (ruleSpace rules) subject ↔
      ∃ rule ∈ rules, ∃ bindings ∈ matchPattern (ruleSide rule.lhs) subject,
        answer = applyBindings bindings (ruleSide rule.rhs) := by
  rw [ruleSpace, mem_matchResults_spaceOfAtoms]
  constructor
  · rintro ⟨atom, member, found⟩
    obtain ⟨rule, inRules, rfl⟩ := List.mem_map.mp member
    obtain ⟨left, right⟩ := firstOrder rule inRules
    rw [equationOf, atomResults_equation _ (isMatchCorrectAux_ruleSide left)
      (isMatchCorrectAux_ruleSide right)] at found
    obtain ⟨bindings, matched, rfl⟩ := List.mem_map.mp found
    exact ⟨rule, inRules, bindings, matched, rfl⟩
  · rintro ⟨rule, inRules, bindings, matched, rfl⟩
    obtain ⟨left, right⟩ := firstOrder rule inRules
    refine ⟨equationOf rule, List.mem_map.mpr ⟨rule, inRules, rfl⟩, ?_⟩
    rw [equationOf, atomResults_equation _ (isMatchCorrectAux_ruleSide left)
      (isMatchCorrectAux_ruleSide right)]
    exact List.mem_map.mpr ⟨bindings, matched, rfl⟩

/-- **An instance of a rule is an answer of the space of the rules**, at
every depth. -/
theorem atomAt_mem_matchResults {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules, Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {rule : Dedukti.RewriteRule} (member : rule ∈ rules) (depth : Nat)
    (assignment : Nat → LF.Term) :
    atomAt depth (inst assignment rule.rhs) ∈
      matchResults (ruleSpace rules) (atomAt depth (inst assignment rule.lhs)) := by
  obtain ⟨left, right⟩ := firstOrder rule member
  have leftExact := isMatchCorrectAux_ruleSide left
  have instance_ : applyBindings (sideBindingsAt depth (patternVars rule.lhs) assignment)
      (ruleSide rule.lhs) = atomAt depth (substitute assignment rule.lhs) :=
    applyBindings_ruleSide depth _ assignment left fun index inLeft =>
      applyBindings_sideBindingsAt depth assignment inLeft
  obtain ⟨found, matched, -⟩ := matchPattern_applyBindings_complete
    (bs := sideBindingsAt depth (patternVars rule.lhs) assignment) leftExact
  rw [instance_] at matched
  have rebuilt : applyBindings found (ruleSide rule.lhs) =
      atomAt depth (substitute assignment rule.lhs) := matchPattern_correct matched leftExact
  obtain ⟨sameLeft, values⟩ := substitute_of_applyBindings_ruleSide depth found left rebuilt
  have agree := eq_of_substitute_eq left sameLeft
  have answer : applyBindings found (ruleSide rule.rhs) =
      atomAt depth (substitute assignment rule.rhs) := by
    rw [applyBindings_ruleSide depth found (assignmentAt depth found) right fun index inRight =>
      values index (patternVars_of_usesOnly right (bound rule member) index inRight)]
    congr 1
    exact (substitute_congr right fun index inRight =>
      agree index (patternVars_of_usesOnly right (bound rule member) index inRight)).symm
  rw [inst_eq_substitute assignment left, inst_eq_substitute assignment right]
  exact (mem_matchResults_ruleSpace firstOrder).mpr ⟨rule, member, found, matched, answer.symm⟩

/-- **An answer of the space of the rules for the atom of a term is the atom
of an instance of a rule on that term**, at every depth. -/
theorem exists_instance_of_mem_matchResults {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules, Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true) {depth : Nat}
    {term : LF.Term} {answer : Pattern}
    (found : answer ∈ matchResults (ruleSpace rules) (atomAt depth term)) :
    ∃ rule ∈ rules, ∃ assignment : Nat → LF.Term,
      term = inst assignment rule.lhs ∧ answer = atomAt depth (inst assignment rule.rhs) := by
  obtain ⟨rule, member, bindings, matched, rfl⟩ :=
    (mem_matchResults_ruleSpace firstOrder).mp found
  obtain ⟨left, right⟩ := firstOrder rule member
  have rebuilt : applyBindings bindings (ruleSide rule.lhs) = atomAt depth term :=
    matchPattern_correct matched (isMatchCorrectAux_ruleSide left)
  obtain ⟨termEq, values⟩ := substitute_of_applyBindings_ruleSide depth bindings left rebuilt
  refine ⟨rule, member, assignmentAt depth bindings, ?_, ?_⟩
  · rw [inst_eq_substitute _ left]
    exact termEq
  · rw [inst_eq_substitute _ right]
    exact applyBindings_ruleSide depth bindings (assignmentAt depth bindings) right
      fun index inRight =>
        values index (patternVars_of_usesOnly right (bound rule member) index inRight)

/-- **The answers of the space of a list of first-order rules with bound
right sides, for the atom of a term at a depth, are the atoms of the
instances of the rules on the term.** -/
theorem mem_matchResults_ruleSpace_iff {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules, Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true) {depth : Nat}
    {term : LF.Term} {answer : Pattern} :
    answer ∈ matchResults (ruleSpace rules) (atomAt depth term) ↔
      ∃ rule ∈ rules, ∃ assignment : Nat → LF.Term,
        term = inst assignment rule.lhs ∧ answer = atomAt depth (inst assignment rule.rhs) :=
  ⟨exists_instance_of_mem_matchResults firstOrder bound, by
    rintro ⟨rule, member, assignment, rfl, rfl⟩
    exact atomAt_mem_matchResults firstOrder bound member depth assignment⟩

/-! ## What stops a rule whose right side binds -/

/-- **The evaluator answers nothing for an equation whose right side is an
abstraction**: the reading of an abstraction is no first-order pattern. -/
theorem atomResults_bindingRight (subject left domain body : Pattern) :
    atomResults subject (.apply "=" [left, .apply "Lam" [domain, .lambda none body]]) = [] := by
  have notExact : isMatchCorrectAux (asRule (.apply "Lam" [domain, .lambda none body])) = false := by
    rw [asRule_apply_of_ne (by decide)]
    simp [asRule, isMatchCorrectAux, isMatchCorrectListAux]
  simp [atomResults, MeTTaZero.viewEquation?, notExact]

/-- So the space of the rule `k x ⟶ λ y : Type. x` answers nothing, for any
subject. -/
theorem matchResults_constantFunctionRule (subject : Pattern) :
    matchResults (ruleSpace [constantFunctionRule]) subject = [] := by
  have stored : storedAtoms (ruleSpace [constantFunctionRule]) =
      [equationOf constantFunctionRule] := storedAtoms_spaceOfAtoms _
  rw [matchResults, stored]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact atomResults_bindingRight subject _ _ _

/-- **The reading of a stored side does not go beneath a binder**: a variable
atom there stays a variable atom, and is no pattern variable. -/
theorem asRule_beneath_binder (domain : Pattern) (index : Nat) :
    asRule (.apply "Lam" [domain, .lambda none (variableAtom (numeral index))]) =
      .apply "Lam" [asRule domain, .lambda none (variableAtom (numeral index))] := by
  rw [asRule_apply_of_ne (by decide)]
  simp [asRule]

/-- **Instantiation beneath a binder needs lifting.**  The instance of the
right side of `k x ⟶ λ y : Type. x` at the variable that an enclosing binder
binds refers to that binder from beneath the new one: its atom at depth one
has the bound variable `1` in its body.  Putting the atom of the assigned
term in the body unchanged gives the bound variable `0`, which the new
binder captures. -/
theorem applyBindings_captures :
    atomAt 1 (inst (fun _ => .var 0) constantFunctionRule.rhs) =
        .apply "Lam" [symbolAtom 0, .lambda none (.bvar 1)] ∧
      applyBindings [(metaName 0, atomAt 1 (.var 0))]
          (.apply "Lam" [symbolAtom 0, .lambda none (.fvar (metaName 0))]) =
        .apply "Lam" [symbolAtom 0, .lambda none (.bvar 0)] := by
  constructor
  · rfl
  · simp [applyBindings, symbolAtom, applyBindings_numeral, atomAt]

#print axioms isMatchCorrectAux_ruleSide
#print axioms applyBindings_ruleSide
#print axioms substitute_of_applyBindings_ruleSide
#print axioms ruleSpace_injective
#print axioms tokens_ruleSpace
#print axioms ruleSpace_wellSorted
#print axioms atomAt_mem_matchResults
#print axioms exists_instance_of_mem_matchResults
#print axioms mem_matchResults_ruleSpace_iff
#print axioms atomResults_bindingRight
#print axioms matchResults_constantFunctionRule
#print axioms asRule_beneath_binder
#print axioms applyBindings_captures

end Mettapedia.Logic.HostingStyles.AtomsReduce
