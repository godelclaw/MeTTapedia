import Mettapedia.Logic.HostingStyles.PrimeCandidate.SpaceExtension
import Mettapedia.GSLT.Dedukti.LanguageDefSteps
import Mathlib.Logic.Equiv.List

/-!
# The matching evaluator: rules as equations stored in a space

The evaluator that a MeTTa has answers an evaluation by matching the subject
against the equations stored in a space.  With a space that is a term
(`SpaceExtension`) this evaluator is a function of the term alone.

* `matchingEvaluator` answers the run premise.  It reads the space and the
  subject up to the static equivalence (through their contractions), reads
  each stored atom of the shape `(= left right)` as a rule (`asRule`: a
  variable atom is a pattern variable), matches the left side against the
  subject with the matcher of the framework (`matchPattern`), and answers
  with the instances of the right side (`matchResults`).  It answers no
  other premise.  It is a computable function and mentions no source.
* **It respects the static equivalence** (`matchingEvaluator_respectsStatics`).
* **With it the extended probe hosts, on terms, every theory of first-order
  rule instances** (`matchingCandidate_hostOf_firstOrderInstances`): for a
  finite table of rules without binder whose right sides mention only
  variables of their left sides (`FirstOrderTable`, `BoundTable`), the theory
  in which a term steps by an instance of a rule at its root
  (`instanceTheory`).  A term is read as the run of its atom in the space of
  the table (`runOf`); one step of the source is one step of the candidate.
  The table is in the term: one evaluator serves every table.
* The class leaves two things out, and both are needed for the theories given
  by a table (`rootStep_ofTable_iff`): beta, and steps beneath the root.
  `MatchingLimits` shows that the candidate hosts neither.
* At the empty space nothing runs (`emptySpace_run_normal`), and a table with
  a right side that mentions another variable is not hosted
  (`freeInstances_not_hostedBy_matching`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.PrimeCandidate

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti
  (Theory RuleTable RootStep inst substitute FirstOrderTable inst_eq_substitute patternVars usesOnly
    chooseLeft chooseRight choiceTable)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (freeRule)
open Mettapedia.GSLT.Dedukti.Language (metaName metaName_injective)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_applyBindings)
open Mettapedia.OSLF.Framework.PredFiniteSufficient (matchPattern_applyBindings_complete)
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef

/-! ## Reading a stored atom as a side of a rule -/

mutual
  /-- The number that a numeral stands for; zero for a pattern that is no
  numeral. -/
  def numeralValue : Pattern → Nat
    | .apply label arguments => if label = "=" then numeralValueList arguments else 0
    | _ => 0

  /-- The number of the two arguments of a numeral above zero. -/
  def numeralValueList : List Pattern → Nat
    | [_, rest] => numeralValue rest + 1
    | _ => 0
end

theorem numeralValue_numeral (count : Nat) : numeralValue (numeral count) = count := by
  induction count with
  | zero => simp [numeral, unitAtom, numeralValue]
  | succ count ih => simp [numeral, numeralValue, numeralValueList, ih]

/-- The number of the index of a variable atom, from its arguments. -/
def indexOf : List Pattern → Nat
  | [index] => numeralValue index
  | _ => 0

mutual
  /-- **A stored atom, read as a side of a rule**: each variable atom becomes
  the pattern variable of its index, and nothing else changes. -/
  def asRule : Pattern → Pattern
    | .apply label arguments =>
        if label = "prime-variable" then .fvar (metaName (indexOf arguments))
        else .apply label (asRuleList arguments)
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .lambda binder body => .lambda binder body
    | .multiLambda arity binders body => .multiLambda arity binders body
    | .subst body replacement => .subst body replacement
    | .collection kind elements rest => .collection kind elements rest

  /-- Reading along a list. -/
  def asRuleList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => asRule pattern :: asRuleList patterns
end

@[simp] theorem asRuleList_eq_map :
    ∀ patterns : List Pattern, asRuleList patterns = patterns.map asRule
  | [] => rfl
  | pattern :: patterns => by
      simp only [asRuleList, List.map_cons, asRuleList_eq_map patterns]

theorem asRule_apply_of_ne {label : String} (other : label ≠ "prime-variable")
    (arguments : List Pattern) :
    asRule (.apply label arguments) = .apply label (arguments.map asRule) := by
  rw [asRule, if_neg other, asRuleList_eq_map]

/-- **Positive**: a variable atom is read as a pattern variable. -/
theorem asRule_variableAtom (index : Nat) :
    asRule (variableAtom (numeral index)) = .fvar (metaName index) := by
  simp [variableAtom, asRule, indexOf, numeralValue_numeral]

/-- **Negative**: a numeral has no variable atom, and is read as itself. -/
theorem asRule_numeral (count : Nat) : asRule (numeral count) = numeral count := by
  induction count with
  | zero => simp [numeral, unitAtom, asRule]
  | succ count ih =>
      rw [numeral, asRule_apply_of_ne (by decide)]
      simp only [List.map_cons, List.map_nil, ih]
      rfl

/-! ## The evaluator -/

/-- **The answers of one stored atom for a subject**: if the atom is an
equation whose two sides, read as sides of a rule, are first-order, the
instances of its right side under the matches of its left side. -/
def atomResults (subject atom : Pattern) : List Pattern :=
  match MeTTaZero.viewEquation? atom with
  | some (left, right) =>
      if isMatchCorrectAux (asRule left) && isMatchCorrectAux (asRule right) then
        (matchPattern (asRule left) subject).map fun bindings =>
          applyBindings bindings (asRule right)
      else []
  | none => []

/-- **The answers of a space for a subject**: those of its stored atoms. -/
def matchResults (space subject : Pattern) : List Pattern :=
  (storedAtoms space).flatMap (atomResults subject)

/-- **The matching evaluator.**  It answers the run premise with the answers
of the space for the subject, both read up to the static equivalence, and it
answers no other premise. -/
def matchingEvaluator : BasePremiseEvaluator := fun _ bindings premise =>
  match premise with
  | .relationQuery "PrimeStep" [space, subject, .fvar answer] =>
      (matchResults (contract (applyBindings bindings space))
        (contract (applyBindings bindings subject))).map fun result => (answer, result) :: bindings
  | _ => []

/-- **The extended probe under the matching evaluator.** -/
abbrev matchingCandidate : ContextTheory.{0} := contextTheory matchingEvaluator spacePresentation

/-- **Negative**: the empty space answers nothing. -/
theorem matchResults_emptySpace (subject : Pattern) : matchResults emptySpace subject = [] := by
  simp [matchResults]

theorem mem_matchResults_spaceOfAtoms {atoms : List Pattern} {subject answer : Pattern} :
    answer ∈ matchResults (spaceOfAtoms atoms) subject ↔
      ∃ atom ∈ atoms, answer ∈ atomResults subject atom := by
  simp [matchResults, storedAtoms_spaceOfAtoms]

/-- The answers of an equation whose sides are first-order. -/
theorem atomResults_equation {left right : Pattern} (subject : Pattern)
    (leftExact : isMatchCorrectAux (asRule left) = true)
    (rightExact : isMatchCorrectAux (asRule right) = true) :
    atomResults subject (.apply "=" [left, right]) =
      (matchPattern (asRule left) subject).map fun bindings =>
        applyBindings bindings (asRule right) := by
  simp [atomResults, MeTTaZero.viewEquation?, leftExact, rightExact]

/-- **The matching evaluator respects the static equivalence**, in every
language whose static equivalence is that of quotation and dropping and whose
premises are those of the probe with the run constructor or congruences. -/
theorem matchingEvaluator_respectsStatics_of_premises {lang : LanguageDef}
    (only : QuoteDropOnly lang)
    (premises : ∀ premise ∈ presentedPremises lang,
      premise ∈ presentedPremises probeWithRun ∨
        ∃ source target, premise = .congruence source target) :
    RespectsStatics matchingEvaluator lang := by
  intro premise member first second related result answered
  have contractions : BindingsRelated (fun left right => contract left = contract right) first
      second := related.mono fun _ _ equivalent => (only.equiv equivalent).1
  rcases premises premise member with listed | ⟨source, target, rfl⟩
  swap
  · simp [matchingEvaluator] at answered
  rw [presentedPremises_probeWithRun] at listed
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl
  · simp [matchingEvaluator] at answered
  · simp [matchingEvaluator] at answered
  · simp [matchingEvaluator] at answered
  · have answers : result ∈ (matchResults (contract (applyBindings first (.fvar "space")))
        (contract (applyBindings first (.fvar "subject")))).map
          fun answer => ("answer", answer) :: first := answered
    obtain ⟨answer, found, rfl⟩ := List.mem_map.mp answers
    rw [contract_applyBindings_congr contractions (.fvar "space") rfl,
      contract_applyBindings_congr contractions (.fvar "subject") rfl] at found
    refine ⟨("answer", answer) :: second, ?_, .cons ⟨rfl, .refl _⟩ related⟩
    show _ ∈ (matchResults (contract (applyBindings second (.fvar "space")))
      (contract (applyBindings second (.fvar "subject")))).map
        fun answer => ("answer", answer) :: second
    exact List.mem_map.mpr ⟨answer, found, rfl⟩

/-- In particular in every language with the rewrites and the equation of the
probe with the run constructor. -/
theorem matchingEvaluator_respectsStatics {lang : LanguageDef} (only : QuoteDropOnly lang)
    (rules : lang.rewrites = probeWithRun.rewrites) : RespectsStatics matchingEvaluator lang :=
  matchingEvaluator_respectsStatics_of_premises only fun _ member =>
    .inl (presentedPremises_of_rules only rules ▸ member)

/-- A run reduces to the run of each answer of its space for its subject. -/
theorem matching_run_step {space subject answer : Pattern}
    (found : answer ∈ matchResults (contract space) (contract subject)) :
    Step matchingEvaluator probeWithSpace (runPattern space subject) (runPattern space answer) := by
  refine ⟨1, .rule (rule := runRewrite)
    (initialBindings := [("subject", subject), ("space", space)])
    (finalBindings := [("answer", answer), ("subject", subject), ("space", space)])
    (by rw [probeWithSpace_rewrites, probeWithRun_rewrites]; simp) ?_ ?_ ?_⟩
  · simp [matchPatternForRule_eq_syntactic, runRewrite, runPattern, matchPattern, matchArgs,
      mergeBindings]
  · refine .cons (.relationQuery ?_) (.nil _)
    show _ ∈ (matchResults
      (contract (applyBindings [("subject", subject), ("space", space)] (.fvar "space")))
      (contract (applyBindings [("subject", subject), ("space", space)] (.fvar "subject")))).map
        fun result => ("answer", result) :: [("subject", subject), ("space", space)]
    have spaceValue : applyBindings [("subject", subject), ("space", space)] (.fvar "space") =
        space := by simp [applyBindings]
    have subjectValue : applyBindings [("subject", subject), ("space", space)] (.fvar "subject") =
        subject := by simp [applyBindings]
    rw [spaceValue, subjectValue]
    exact List.mem_map.mpr ⟨answer, found, rfl⟩
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide)]
    simp [runRewrite, runPattern, applyBindings]

/-- **A step out of a pattern that contracts to a run** is such a step: the
redex is a run, and the contractum is the run of an answer of its space. -/
theorem matching_run_step_inv {redex contractum : Pattern}
    (runHead : head? (contract redex) = some "prime-run")
    (step : Step matchingEvaluator probeWithSpace redex contractum) :
    ∃ space subject answer, redex = runPattern space subject ∧
      answer ∈ matchResults (contract space) (contract subject) ∧
        contractum = runPattern space answer := by
  obtain ⟨space, subject, final, rfl, answered, rfl⟩ :=
    run_step_shape probeWithSpace_rewrites runHead step
  have answers : final ∈ (matchResults
      (contract (applyBindings [("subject", subject), ("space", space)] (.fvar "space")))
      (contract (applyBindings [("subject", subject), ("space", space)] (.fvar "subject")))).map
        fun result => ("answer", result) :: [("subject", subject), ("space", space)] := answered
  have spaceValue : applyBindings [("subject", subject), ("space", space)] (.fvar "space") =
      space := by simp [applyBindings]
  have subjectValue : applyBindings [("subject", subject), ("space", space)] (.fvar "subject") =
      subject := by simp [applyBindings]
  rw [spaceValue, subjectValue] at answers
  obtain ⟨answer, found, rfl⟩ := List.mem_map.mp answers
  exact ⟨space, subject, answer, rfl, found, by simp [runRewrite, runPattern, applyBindings]⟩

theorem contract_runPattern' (space subject : Pattern) :
    contract (runPattern space subject) = runPattern (contract space) (contract subject) := by
  rw [runPattern, contract_apply_of_ne (by decide)]
  rfl

/-- The run of an atom at the empty space, as a closed term. -/
def emptyRunTerm : Contexts.Term probeWithSpace closedProcess :=
  ⟨runPattern emptySpace unitAtom, checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **Negative**: at the empty space nothing runs. -/
theorem emptySpace_run_normal (next : Contexts.Term probeWithSpace closedProcess) :
    ¬ matchingCandidate.rewrites emptyRunTerm next := by
  rintro ⟨redex, contractum, before, fired, after⟩
  have same := probeWithSpace_quoteDropOnly.contract_eq before
  have shape : contract redex.1 = runPattern emptySpace unitAtom := by
    rw [← same]
    decide
  obtain ⟨space, subject, answer, redexShape, found, -⟩ :=
    matching_run_step_inv (by rw [shape]; rfl) fired
  rw [redexShape, contract_runPattern'] at shape
  simp only [runPattern, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
  rw [shape.1, matchResults_emptySpace] at found
  cases found

/-! ## λΠ terms as atoms, and tables as spaces -/

/-- A number for each name of a constant. -/
def nameCode (name : String) : Nat := Encodable.encode (name.toList.map Char.toNat)

theorem nameCode_injective : Function.Injective nameCode := by
  intro first second same
  have lists := Encodable.encode_injective same
  exact String.toList_injective
    (List.map_injective_iff.mpr (fun _ _ equal => Char.toNat_inj.mp equal) lists)

/-- **A λΠ term as an atom.**  A variable is a variable atom, a constant and
a sort are tagged numerals, and application, abstraction and product are
three binary constructors of atoms. -/
def atomOf : LF.Term → Pattern
  | .var index => variableAtom (numeral index)
  | .con name => .apply "prime-inert-dependency" [numeral (nameCode name)]
  | .srt .type => .apply "prime-request-dependency" [numeral 0]
  | .srt .kind => .apply "prime-request-dependency" [numeral 1]
  | .app function argument => .apply "=" [atomOf function, atomOf argument]
  | .lam domain body => .apply "prime-space-atom-dependency" [atomOf domain, atomOf body]
  | .pi domain body => .apply "prime-capability-dependency" [atomOf domain, atomOf body]

theorem atomOf_injective : Function.Injective atomOf := by
  intro first
  induction first with
  | var index =>
      intro second same
      cases second with
      | var other =>
          simp only [atomOf, variableAtom, Pattern.apply.injEq, List.cons.injEq, and_true,
            true_and] at same
          rw [numeral_injective same]
      | srt sort => cases sort <;> simp [atomOf, variableAtom] at same
      | _ => simp [atomOf, variableAtom] at same
  | con name =>
      intro second same
      cases second with
      | con other =>
          simp only [atomOf, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
          rw [nameCode_injective (numeral_injective same)]
      | srt sort => cases sort <;> simp [atomOf] at same
      | _ => simp [atomOf, variableAtom] at same
  | srt sort =>
      intro second same
      cases second with
      | srt other =>
          cases sort <;> cases other <;> first
            | rfl
            | (simp only [atomOf, Pattern.apply.injEq, List.cons.injEq, and_true,
                true_and] at same
               exact absurd (numeral_injective same) (by decide))
      | _ => cases sort <;> simp [atomOf, variableAtom] at same
  | app function argument ihFunction ihArgument =>
      intro second same
      cases second with
      | app otherFunction otherArgument =>
          simp only [atomOf, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
          rw [ihFunction same.1, ihArgument same.2]
      | srt sort => cases sort <;> simp [atomOf] at same
      | _ => simp [atomOf, variableAtom] at same
  | lam domain body ihDomain ihBody =>
      intro second same
      cases second with
      | lam otherDomain otherBody =>
          simp only [atomOf, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
          rw [ihDomain same.1, ihBody same.2]
      | srt sort => cases sort <;> simp [atomOf] at same
      | _ => simp [atomOf, variableAtom] at same
  | pi domain body ihDomain ihBody =>
      intro second same
      cases second with
      | pi otherDomain otherBody =>
          simp only [atomOf, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
          rw [ihDomain same.1, ihBody same.2]
      | srt sort => cases sort <;> simp [atomOf] at same
      | _ => simp [atomOf, variableAtom] at same

/-- The atom of a term has no quotation to contract. -/
theorem contract_atomOf (term : LF.Term) : contract (atomOf term) = atomOf term := by
  induction term with
  | var index =>
      rw [atomOf, variableAtom, contract_apply_of_ne (by decide)]
      simp [contract_numeral]
  | con name =>
      rw [atomOf, contract_apply_of_ne (by decide)]
      simp [contract_numeral]
  | srt sort =>
      cases sort <;> rw [atomOf, contract_apply_of_ne (by decide)] <;> simp [contract_numeral]
  | app function argument ihFunction ihArgument =>
      rw [atomOf, contract_apply_of_ne (by decide)]
      simp [ihFunction, ihArgument]
  | lam domain body ihDomain ihBody =>
      rw [atomOf, contract_apply_of_ne (by decide)]
      simp [ihDomain, ihBody]
  | pi domain body ihDomain ihBody =>
      rw [atomOf, contract_apply_of_ne (by decide)]
      simp [ihDomain, ihBody]

/-- **The atom of a term is a closed atom of the extension**, beneath any
binders. -/
theorem atomOf_wellSorted (bound : List TypeExpr) (term : LF.Term) :
    OpenPatternWellSorted probeWithSpace FreeTypeContext.empty bound (.base "Atom")
      (atomOf term) := by
  have numerals : ∀ count, OpenPatternWellSorted probeWithSpace FreeTypeContext.empty bound
      (.base "Atom") (numeral count) :=
    numeral_wellSorted_in (lang := probeWithSpace) (by decide) (by decide) bound
  induction term with
  | var index => exact variableAtom_wellSorted (numerals index)
  | con name =>
      exact wellSorted_apply_one (lang := probeWithSpace) (label := "prime-inert-dependency")
        (name := "key") (by decide) (numerals _)
  | srt sort =>
      cases sort <;>
        exact wellSorted_apply_one (lang := probeWithSpace) (label := "prime-request-dependency")
          (name := "key") (by decide) (numerals _)
  | app function argument ihFunction ihArgument =>
      exact wellSorted_apply_two (lang := probeWithSpace) (label := "=") (firstName := "left")
        (secondName := "right") (by decide) ihFunction ihArgument
  | lam domain body ihDomain ihBody =>
      exact wellSorted_apply_two (lang := probeWithSpace) (label := "prime-space-atom-dependency")
        (firstName := "key") (secondName := "atom") (by decide) ihDomain ihBody
  | pi domain body ihDomain ihBody =>
      exact wellSorted_apply_two (lang := probeWithSpace) (label := "prime-capability-dependency")
        (firstName := "key") (secondName := "result") (by decide) ihDomain ihBody

/-- **A side of a rule, as the pattern that the evaluator matches.** -/
def sideOf (term : LF.Term) : Pattern := asRule (atomOf term)

@[simp] theorem sideOf_var (index : Nat) : sideOf (.var index) = .fvar (metaName index) :=
  asRule_variableAtom index

theorem sideOf_con (name : String) : sideOf (.con name) = atomOf (.con name) := by
  rw [sideOf, atomOf, asRule_apply_of_ne (by decide)]
  simp [asRule_numeral]

theorem sideOf_srt (sort : LF.Srt) : sideOf (.srt sort) = atomOf (.srt sort) := by
  cases sort <;> rw [sideOf, atomOf, asRule_apply_of_ne (by decide)] <;> simp [asRule_numeral]

@[simp] theorem sideOf_app (function argument : LF.Term) :
    sideOf (.app function argument) = .apply "=" [sideOf function, sideOf argument] := by
  rw [sideOf, atomOf, asRule_apply_of_ne (by decide)]
  rfl

theorem isMatchCorrectAux_numeral (count : Nat) : isMatchCorrectAux (numeral count) = true := by
  induction count with
  | zero => decide
  | succ count ih => simp [numeral, unitAtom, isMatchCorrectAux, isMatchCorrectListAux, ih]

/-- **A side without binder is a first-order pattern.** -/
theorem isMatchCorrectAux_sideOf :
    ∀ {term : LF.Term}, Dedukti.binderFree term = true → isMatchCorrectAux (sideOf term) = true := by
  intro term
  induction term with
  | var index => intro _; simp [isMatchCorrectAux]
  | con name =>
      intro _
      rw [sideOf_con]
      simp [atomOf, isMatchCorrectAux, isMatchCorrectListAux, isMatchCorrectAux_numeral]
  | srt sort =>
      intro _
      rw [sideOf_srt]
      cases sort <;>
        simp [atomOf, isMatchCorrectAux, isMatchCorrectListAux, isMatchCorrectAux_numeral]
  | app function argument ihFunction ihArgument =>
      intro free
      simp only [Dedukti.binderFree, Bool.and_eq_true] at free
      simp [isMatchCorrectAux, isMatchCorrectListAux, ihFunction free.1, ihArgument free.2]
  | lam domain body _ _ => intro free; simp [Dedukti.binderFree] at free
  | pi domain body _ _ => intro free; simp [Dedukti.binderFree] at free

theorem applyBindings_numeral (bindings : Bindings) (count : Nat) :
    applyBindings bindings (numeral count) = numeral count := by
  induction count with
  | zero => simp [numeral, unitAtom, applyBindings]
  | succ count ih => simp [numeral, unitAtom, applyBindings, ih]

/-- **An instance of a side is the atom of the instance of the term**, when
the bindings give each variable of the term the atom of its value. -/
theorem applyBindings_sideOf (bindings : Bindings) (assignment : Nat → LF.Term) :
    ∀ {term : LF.Term}, Dedukti.binderFree term = true →
      (∀ index ∈ patternVars term,
        applyBindings bindings (.fvar (metaName index)) = atomOf (assignment index)) →
        applyBindings bindings (sideOf term) = atomOf (substitute assignment term) := by
  intro term
  induction term with
  | var index =>
      intro _ values
      simpa [substitute] using values index (List.mem_singleton.mpr rfl)
  | con name =>
      intro _ _
      rw [sideOf_con]
      simp [atomOf, substitute, applyBindings, applyBindings_numeral]
  | srt sort =>
      intro _ _
      rw [sideOf_srt]
      cases sort <;> simp [atomOf, substitute, applyBindings, applyBindings_numeral]
  | app function argument ihFunction ihArgument =>
      intro free values
      simp only [Dedukti.binderFree, Bool.and_eq_true] at free
      have left := ihFunction free.1 fun index member =>
        values index (List.mem_append_left _ member)
      have right := ihArgument free.2 fun index member =>
        values index (List.mem_append_right _ member)
      simp [substitute, atomOf, applyBindings, left, right]
  | lam domain body _ _ => intro free; simp [Dedukti.binderFree] at free
  | pi domain body _ _ => intro free; simp [Dedukti.binderFree] at free

/-- The assignment that bindings stand for: the term whose atom a variable is
bound to. -/
noncomputable def assignmentOf (bindings : Bindings) (index : Nat) : LF.Term :=
  open Classical in
  if known : ∃ term, applyBindings bindings (.fvar (metaName index)) = atomOf term then
    Classical.choose known
  else .srt .type

theorem atomOf_assignmentOf {bindings : Bindings} {index : Nat} {term : LF.Term}
    (bound : applyBindings bindings (.fvar (metaName index)) = atomOf term) :
    assignmentOf bindings index = term := by
  have known : ∃ other, applyBindings bindings (.fvar (metaName index)) = atomOf other :=
    ⟨term, bound⟩
  unfold assignmentOf
  rw [dif_pos known]
  exact atomOf_injective ((Classical.choose_spec known).symm.trans bound)

/-- **What an instance of a side is the atom of**: if an instance of a side
without binder is the atom of a term, the term is the instance of the side
under the assignment that the bindings stand for, and each variable of the
side is bound to the atom of its value. -/
theorem substitute_of_applyBindings_sideOf (bindings : Bindings) :
    ∀ {side : LF.Term}, Dedukti.binderFree side = true → ∀ {term : LF.Term},
      applyBindings bindings (sideOf side) = atomOf term →
        term = substitute (assignmentOf bindings) side ∧
          ∀ index ∈ patternVars side,
            applyBindings bindings (.fvar (metaName index)) =
              atomOf (assignmentOf bindings index) := by
  intro side
  induction side with
  | var index =>
      intro _ term same
      rw [sideOf_var] at same
      have value := atomOf_assignmentOf same
      refine ⟨by simp [substitute, value], fun other member => ?_⟩
      rw [List.mem_singleton.mp member, value]
      exact same
  | con name =>
      intro _ term same
      rw [sideOf_con] at same
      have fixed : applyBindings bindings (atomOf (.con name)) = atomOf (.con name) := by
        simp [atomOf, applyBindings, applyBindings_numeral]
      rw [fixed] at same
      exact ⟨(atomOf_injective same).symm, fun other member => by simp [patternVars] at member⟩
  | srt sort =>
      intro _ term same
      rw [sideOf_srt] at same
      have fixed : applyBindings bindings (atomOf (.srt sort)) = atomOf (.srt sort) := by
        cases sort <;> simp [atomOf, applyBindings, applyBindings_numeral]
      rw [fixed] at same
      exact ⟨(atomOf_injective same).symm, fun other member => by simp [patternVars] at member⟩
  | app function argument ihFunction ihArgument =>
      intro free term same
      simp only [Dedukti.binderFree, Bool.and_eq_true] at free
      have unfolded : applyBindings bindings (sideOf (.app function argument)) =
          .apply "=" [applyBindings bindings (sideOf function),
            applyBindings bindings (sideOf argument)] := by
        simp [applyBindings]
      rw [unfolded] at same
      cases term with
      | app termFunction termArgument =>
          simp only [atomOf, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
          obtain ⟨functionEq, functionValues⟩ := ihFunction free.1 same.1
          obtain ⟨argumentEq, argumentValues⟩ := ihArgument free.2 same.2
          refine ⟨by simp [substitute, ← functionEq, ← argumentEq], fun index member => ?_⟩
          rcases List.mem_append.mp member with inFunction | inArgument
          · exact functionValues index inFunction
          · exact argumentValues index inArgument
      | srt sort => cases sort <;> simp [atomOf] at same
      | _ => simp [atomOf, variableAtom] at same
  | lam domain body _ _ => intro free; simp [Dedukti.binderFree] at free
  | pi domain body _ _ => intro free; simp [Dedukti.binderFree] at free

/-- A right side that mentions only variables of the left side has its
variables among those of the left side. -/
theorem patternVars_of_usesOnly {allowed : List Nat} :
    ∀ {term : LF.Term}, Dedukti.binderFree term = true → usesOnly allowed 0 term = true →
      ∀ index ∈ patternVars term, index ∈ allowed := by
  intro term
  induction term with
  | var index =>
      intro _ uses other member
      rw [List.mem_singleton.mp member]
      simpa [usesOnly] using uses
  | con name => intro _ _ other member; simp [patternVars] at member
  | srt sort => intro _ _ other member; simp [patternVars] at member
  | app function argument ihFunction ihArgument =>
      intro free uses other member
      simp only [Dedukti.binderFree, Bool.and_eq_true] at free
      simp only [usesOnly, Bool.and_eq_true] at uses
      rcases List.mem_append.mp member with inFunction | inArgument
      · exact ihFunction free.1 uses.1 other inFunction
      · exact ihArgument free.2 uses.2 other inArgument
  | lam domain body _ _ => intro free; simp [Dedukti.binderFree] at free
  | pi domain body _ _ => intro free; simp [Dedukti.binderFree] at free

/-- Two assignments with one instance of a term without binder agree on its
variables. -/
theorem eq_of_substitute_eq {first second : Nat → LF.Term} :
    ∀ {term : LF.Term}, Dedukti.binderFree term = true →
      substitute first term = substitute second term →
        ∀ index ∈ patternVars term, first index = second index := by
  intro term
  induction term with
  | var index =>
      intro _ same other member
      rw [List.mem_singleton.mp member]
      simpa [substitute] using same
  | con name => intro _ _ other member; simp [patternVars] at member
  | srt sort => intro _ _ other member; simp [patternVars] at member
  | app function argument ihFunction ihArgument =>
      intro free same other member
      simp only [Dedukti.binderFree, Bool.and_eq_true] at free
      simp only [substitute, LF.Term.app.injEq] at same
      rcases List.mem_append.mp member with inFunction | inArgument
      · exact ihFunction free.1 same.1 other inFunction
      · exact ihArgument free.2 same.2 other inArgument
  | lam domain body _ _ => intro free; simp [Dedukti.binderFree] at free
  | pi domain body _ _ => intro free; simp [Dedukti.binderFree] at free

/-- An instance of a term without binder is determined by the values of its
variables. -/
theorem substitute_congr {first second : Nat → LF.Term} :
    ∀ {term : LF.Term}, Dedukti.binderFree term = true →
      (∀ index ∈ patternVars term, first index = second index) →
        substitute first term = substitute second term := by
  intro term
  induction term with
  | var index => intro _ agree; simpa [substitute] using agree index (List.mem_singleton.mpr rfl)
  | con name => intro _ _; rfl
  | srt sort => intro _ _; rfl
  | app function argument ihFunction ihArgument =>
      intro free agree
      simp only [Dedukti.binderFree, Bool.and_eq_true] at free
      simp only [substitute]
      rw [ihFunction free.1 fun index member => agree index (List.mem_append_left _ member),
        ihArgument free.2 fun index member => agree index (List.mem_append_right _ member)]
  | lam domain body _ _ => intro free; simp [Dedukti.binderFree] at free
  | pi domain body _ _ => intro free; simp [Dedukti.binderFree] at free

/-- The bindings that give each listed variable the atom of its value. -/
def sideBindings (indices : List Nat) (assignment : Nat → LF.Term) : Bindings :=
  indices.map fun index => (metaName index, atomOf (assignment index))

theorem applyBindings_sideBindings (assignment : Nat → LF.Term) :
    ∀ {indices : List Nat} {index : Nat}, index ∈ indices →
      applyBindings (sideBindings indices assignment) (.fvar (metaName index)) =
        atomOf (assignment index) := by
  intro indices
  induction indices with
  | nil => intro index member; cases member
  | cons head rest ih =>
      intro index member
      rw [sideBindings, List.map_cons, applyBindings_fvar_cons]
      by_cases same : metaName head = metaName index
      · rw [if_pos same, metaName_injective same]
      · rw [if_neg same]
        exact ih ((List.mem_cons.mp member).resolve_left fun equal => same (by rw [equal]))

/-! ## The theories of first-order rule instances -/

/-- **One instance of a rule of a table, at the root.** -/
def RuleInstance (table : RuleTable) (source target : LF.Term) : Prop :=
  ∃ rule ∈ table, ∃ assignment : Nat → LF.Term,
    source = inst assignment rule.lhs ∧ target = inst assignment rule.rhs

/-- **The theory of the instances of the rules of a table**: λΠ terms compared
by identity; a term steps by an instance of a rule at its root. -/
def instanceTheory (table : RuleTable) : GSLT.{0} where
  Term := LF.Term
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := RuleInstance table
  rewrites_resp_left := fun same step => ⟨_, same ▸ step, rfl⟩
  rewrites_resp_right := fun step same => same ▸ step

/-- **What the class leaves out of a theory given by a table**: a contraction
at the root is beta or an instance of a rule; a step of the theory is such a
contraction at any position. -/
theorem rootStep_ofTable_iff {table : RuleTable} {source target : LF.Term} :
    RootStep (Theory.ofTable table) source target ↔
      (∃ domain body argument, source = .app (.lam domain body) argument ∧
        target = LFTyping.subst0 argument body) ∨ RuleInstance table source target := by
  constructor
  · intro step
    cases step with
    | beta domain body argument => exact .inl ⟨domain, body, argument, rfl, rfl⟩
    | delta defined => cases defined
    | @rule rule assignment member => exact .inr ⟨rule, member, assignment, rfl, rfl⟩
  · rintro (⟨domain, body, argument, rfl, rfl⟩ | ⟨rule, member, assignment, rfl, rfl⟩)
    · exact .beta domain body argument
    · exact .rule assignment member

/-- **A table whose right sides mention only variables of their left
sides.** -/
def BoundTable (table : RuleTable) : Prop :=
  ∀ rule ∈ table, usesOnly (patternVars rule.lhs) 0 rule.rhs = true

/-- **Positive**: the two rules of choice. -/
theorem choiceTable_bound : BoundTable choiceTable := by
  intro rule member
  simp only [choiceTable, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl <;> decide

theorem choiceTable_firstOrder : FirstOrderTable choiceTable := by
  intro rule member
  simp only [choiceTable, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl <;> decide

/-- **Negative**: the table of the rule `c ⟶ x`. -/
theorem freeTable_not_bound : ¬ BoundTable {freeRule} := by
  intro bound
  have uses := bound freeRule (Finset.mem_singleton_self _)
  revert uses
  decide

/-- **The theories of first-order rule instances**: one for each finite table
of rules without binder whose right sides mention only variables of their
left sides. -/
def FirstOrderInstances (source : ContextTheory.{0}) : Prop :=
  ∃ table : RuleTable, FirstOrderTable table ∧ BoundTable table ∧
    source = (instanceTheory table).termsAlone

/-! ## The hosting map -/

/-- A rule, as a stored equation. -/
def equationAtom (rule : Dedukti.RewriteRule) : Pattern :=
  .apply "=" [atomOf rule.lhs, atomOf rule.rhs]

/-- The space of a list of rules. -/
def spaceOfRules (rules : List Dedukti.RewriteRule) : Pattern :=
  spaceOfAtoms (rules.map equationAtom)

/-- **A term, in the space of a list of rules**: the run of its atom. -/
def runOf (rules : List Dedukti.RewriteRule) (term : LF.Term) : Pattern :=
  runPattern (spaceOfRules rules) (atomOf term)

theorem contract_spaceOfAtoms :
    ∀ atoms : List Pattern, contract (spaceOfAtoms atoms) = spaceOfAtoms (atoms.map contract)
  | [] => by decide
  | atom :: atoms => by
      rw [spaceOfAtoms, addAtom, contract_apply_of_ne (by decide)]
      simp only [List.map_cons, List.map_nil, contract_spaceOfAtoms atoms]
      rfl

theorem contract_spaceOfRules (rules : List Dedukti.RewriteRule) :
    contract (spaceOfRules rules) = spaceOfRules rules := by
  rw [spaceOfRules, contract_spaceOfAtoms, List.map_map]
  congr 1
  apply List.map_congr_left
  intro rule _
  show contract (equationAtom rule) = equationAtom rule
  rw [equationAtom, contract_apply_of_ne (by decide)]
  simp [contract_atomOf]

theorem contract_runOf (rules : List Dedukti.RewriteRule) (term : LF.Term) :
    contract (runOf rules term) = runOf rules term := by
  rw [runOf, contract_runPattern', contract_spaceOfRules, contract_atomOf]

theorem runOf_wellSorted (rules : List Dedukti.RewriteRule) (term : LF.Term) :
    OpenPatternWellSorted probeWithSpace FreeTypeContext.empty [] (.base "Process")
      (runOf rules term) :=
  wellSorted_apply_two (lang := probeWithSpace) (label := "prime-run") (firstName := "space")
    (secondName := "subject") (by decide)
    (spaceOfAtoms_wellSorted fun atom member => by
      obtain ⟨rule, -, rfl⟩ := List.mem_map.mp member
      exact wellSorted_apply_two (lang := probeWithSpace) (label := "=") (firstName := "left")
        (secondName := "right") (by decide) (atomOf_wellSorted [] rule.lhs)
        (atomOf_wellSorted [] rule.rhs))
    (atomOf_wellSorted [] term)

/-- The run of a term, as a closed term of the extension. -/
def runTermOf (rules : List Dedukti.RewriteRule) (term : LF.Term) :
    Contexts.Term probeWithSpace closedProcess :=
  ⟨runOf rules term, runOf_wellSorted rules term⟩

/-- The answers of the space of a list of first-order rules. -/
theorem mem_matchResults_spaceOfRules {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    {subject answer : Pattern} :
    answer ∈ matchResults (spaceOfRules rules) subject ↔
      ∃ rule ∈ rules, ∃ bindings ∈ matchPattern (sideOf rule.lhs) subject,
        answer = applyBindings bindings (sideOf rule.rhs) := by
  rw [spaceOfRules, mem_matchResults_spaceOfAtoms]
  constructor
  · rintro ⟨atom, member, found⟩
    obtain ⟨rule, inRules, rfl⟩ := List.mem_map.mp member
    obtain ⟨left, right⟩ := firstOrder rule inRules
    rw [equationAtom, atomResults_equation _ (isMatchCorrectAux_sideOf left)
      (isMatchCorrectAux_sideOf right)] at found
    obtain ⟨bindings, matched, rfl⟩ := List.mem_map.mp found
    exact ⟨rule, inRules, bindings, matched, rfl⟩
  · rintro ⟨rule, inRules, bindings, matched, rfl⟩
    obtain ⟨left, right⟩ := firstOrder rule inRules
    refine ⟨equationAtom rule, List.mem_map.mpr ⟨rule, inRules, rfl⟩, ?_⟩
    rw [equationAtom, atomResults_equation _ (isMatchCorrectAux_sideOf left)
      (isMatchCorrectAux_sideOf right)]
    exact List.mem_map.mpr ⟨bindings, matched, rfl⟩

/-- **An instance of a rule is an answer of the space of the rules.** -/
theorem atomOf_mem_matchResults {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {rule : Dedukti.RewriteRule} (member : rule ∈ rules) (assignment : Nat → LF.Term) :
    atomOf (inst assignment rule.rhs) ∈
      matchResults (spaceOfRules rules) (atomOf (inst assignment rule.lhs)) := by
  obtain ⟨left, right⟩ := firstOrder rule member
  have leftExact := isMatchCorrectAux_sideOf left
  have instance_ : applyBindings (sideBindings (patternVars rule.lhs) assignment)
      (sideOf rule.lhs) = atomOf (substitute assignment rule.lhs) :=
    applyBindings_sideOf _ assignment left fun index inLeft =>
      applyBindings_sideBindings assignment inLeft
  obtain ⟨found, matched, -⟩ := matchPattern_applyBindings_complete
    (bs := sideBindings (patternVars rule.lhs) assignment) leftExact
  rw [instance_] at matched
  have rebuilt : applyBindings found (sideOf rule.lhs) = atomOf (substitute assignment rule.lhs) :=
    matchPattern_correct matched leftExact
  obtain ⟨sameLeft, values⟩ := substitute_of_applyBindings_sideOf found left rebuilt
  have agree := eq_of_substitute_eq left sameLeft
  have answer : applyBindings found (sideOf rule.rhs) = atomOf (substitute assignment rule.rhs) := by
    rw [applyBindings_sideOf found (assignmentOf found) right fun index inRight =>
      values index (patternVars_of_usesOnly right (bound rule member) index inRight)]
    congr 1
    exact (substitute_congr right fun index inRight =>
      agree index (patternVars_of_usesOnly right (bound rule member) index inRight)).symm
  rw [inst_eq_substitute assignment left, inst_eq_substitute assignment right]
  exact (mem_matchResults_spaceOfRules firstOrder).mpr ⟨rule, member, found, matched, answer.symm⟩

/-- **An answer of the space of the rules for the atom of a term is the atom
of an instance of a rule on that term.** -/
theorem exists_instance_of_mem_matchResults {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true)
    {term : LF.Term} {answer : Pattern}
    (found : answer ∈ matchResults (spaceOfRules rules) (atomOf term)) :
    ∃ rule ∈ rules, ∃ assignment : Nat → LF.Term,
      term = inst assignment rule.lhs ∧ answer = atomOf (inst assignment rule.rhs) := by
  obtain ⟨rule, member, bindings, matched, rfl⟩ :=
    (mem_matchResults_spaceOfRules firstOrder).mp found
  obtain ⟨left, right⟩ := firstOrder rule member
  have rebuilt : applyBindings bindings (sideOf rule.lhs) = atomOf term :=
    matchPattern_correct matched (isMatchCorrectAux_sideOf left)
  obtain ⟨termEq, values⟩ := substitute_of_applyBindings_sideOf bindings left rebuilt
  refine ⟨rule, member, assignmentOf bindings, ?_, ?_⟩
  · rw [inst_eq_substitute _ left]
    exact termEq
  · rw [inst_eq_substitute _ right]
    exact applyBindings_sideOf bindings (assignmentOf bindings) right fun index inRight =>
      values index (patternVars_of_usesOnly right (bound rule member) index inRight)

theorem runTermOf_resp (table : RuleTable) {first second : LF.Term}
    (related : (instanceTheory table).equations.r first second) :
    (termSetoid matchingEvaluator probeWithSpace closedProcess).r (runTermOf table.toList first)
      (runTermOf table.toList second) := by
  have same : first = second := related
  rw [same]

/-- **The theory of the instances of a table, in the extended probe**: a term
is read as the run of its atom in the space of the table. -/
noncomputable def matchingMap (table : RuleTable) :
    ContextMap (instanceTheory table).termsAlone matchingCandidate :=
  ContextMap.ofTerms (source := instanceTheory table) (target := matchingCandidate) closedProcess
    (fun term => runTermOf table.toList term) (fun related => runTermOf_resp table related)

/-- **Under the matching evaluator the extended probe hosts the instances of
every first-order table whose right sides are bound**: no two terms get one
image, a step of the source is a step of the image, and a step of the image
is the image of a step. -/
theorem matchingMap_hosting {table : RuleTable} (firstOrder : FirstOrderTable table)
    (bound : BoundTable table) : (matchingMap table).Hosting := by
  have listed : ∀ rule ∈ table.toList,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true :=
    fun rule member => firstOrder rule (Finset.mem_toList.mp member)
  have listedBound : ∀ rule ∈ table.toList, usesOnly (patternVars rule.lhs) 0 rule.rhs = true :=
    fun rule member => bound rule (Finset.mem_toList.mp member)
  refine (ContextMap.ofTerms_hosting_iff (source := instanceTheory table)
    (target := matchingCandidate) closedProcess (fun term => runTermOf table.toList term)
    (fun related => runTermOf_resp table related)).mpr ⟨?_, ?_, ?_⟩
  · intro (first : LF.Term) (second : LF.Term) related
    have same := probeWithSpace_quoteDropOnly.contract_eq related
    have unfolded : contract (runOf table.toList first) = contract (runOf table.toList second) :=
      same
    rw [contract_runOf, contract_runOf] at unfolded
    simp only [runOf, runPattern, Pattern.apply.injEq, List.cons.injEq, and_true,
      true_and] at unfolded
    exact atomOf_injective unfolded
  · rintro first next ⟨rule, member, assignment, rfl, rfl⟩
    refine ⟨runTermOf table.toList _, runTermOf table.toList _, Relation.EqvGen.refl _, ?_,
      Relation.EqvGen.refl _⟩
    refine matching_run_step ?_
    rw [contract_spaceOfRules, contract_atomOf]
    exact atomOf_mem_matchResults listed listedBound (Finset.mem_toList.mpr member) assignment
  · intro (first : LF.Term) next step
    obtain ⟨redex, contractum, before, fired, after⟩ := step
    have same := probeWithSpace_quoteDropOnly.contract_eq before
    have redexClass : contract redex.1 = runOf table.toList first := by
      have unfolded : contract (runOf table.toList first) = contract redex.1 := same
      rw [contract_runOf] at unfolded
      exact unfolded.symm
    obtain ⟨space, subject, answer, redexShape, found, contractumShape⟩ :=
      matching_run_step_inv (by rw [redexClass]; rfl) fired
    rw [redexShape, contract_runPattern'] at redexClass
    simp only [runOf, runPattern, Pattern.apply.injEq, List.cons.injEq, and_true,
      true_and] at redexClass
    rw [redexClass.1, redexClass.2] at found
    obtain ⟨rule, member, assignment, rfl, rfl⟩ :=
      exists_instance_of_mem_matchResults listed listedBound found
    refine ⟨inst assignment rule.rhs, ⟨rule, Finset.mem_toList.mp member, assignment, rfl, rfl⟩, ?_⟩
    refine (probeWithSpace_quoteDropOnly.termSetoid_iff probeWithSpace_quoteDropSorted).mpr ?_
    rw [← probeWithSpace_quoteDropOnly.contract_eq after]
    show contract contractum.1 = contract (runOf table.toList (inst assignment rule.rhs))
    rw [contractumShape, contract_runPattern', redexClass.1, contract_atomOf, contract_runOf]
    rfl

/-- **The extended probe under the matching evaluator hosts every theory of
first-order rule instances.** -/
theorem matchingCandidate_hostsEvery : HostsEvery matchingCandidate FirstOrderInstances := by
  rintro source ⟨table, firstOrder, bound, rfl⟩
  exact ⟨matchingMap table, matchingMap_hosting firstOrder bound⟩

/-- **The sentence for the matching evaluator**: the extended probe, with the
evaluator that matches against the equations stored in the space, is a host
of the theories of first-order rule instances, on terms. -/
theorem matchingCandidate_hostOf_firstOrderInstances :
    HostOf matchingCandidate FirstOrderInstances .terms .hosting :=
  HostOf.terms (hostOf_contexts_hosting_iff.mpr matchingCandidate_hostsEvery)

/-- **Positive**: the instances of the two rules of choice are hosted. -/
theorem choiceInstances_hostedBy_matching :
    HostedBy (instanceTheory choiceTable).termsAlone matchingCandidate :=
  matchingCandidate_hostsEvery _ ⟨choiceTable, choiceTable_firstOrder, choiceTable_bound, rfl⟩

/-- **Negative**: the instances of the rule `c ⟶ x`, whose right side
mentions a variable that its left side does not bind, are not hosted.  The
constant has infinitely many reducts, and the candidate is finitely
branching. -/
theorem freeInstances_not_hostedBy_matching :
    ¬ HostedBy (instanceTheory {freeRule}).termsAlone matchingCandidate := by
  intro hosted
  obtain ⟨reducts, covered⟩ := finitelyBranching_of_hostedBy
    (spacePresentation_finitelyBranching
      (matchingEvaluator_respectsStatics probeWithSpace_quoteDropOnly probeWithSpace_rewrites))
    hosted (LF.Term.con "c")
  have every : ∀ index : Nat, LF.Term.var index ∈ reducts := fun index => by
    obtain ⟨reduct, member, same⟩ := covered (.var index)
      ⟨freeRule, Finset.mem_singleton_self _, fun _ => .var index, by simp [freeRule],
        by simp [freeRule]⟩
    exact (show LF.Term.var index = reduct from same) ▸ member
  exact Set.infinite_range_of_injective (fun first second same => LF.Term.var.inj same)
    ((List.finite_toSet reducts).subset (by
      rintro _ ⟨index, rfl⟩
      exact every index))

#print axioms matchingEvaluator
#print axioms matchingEvaluator_respectsStatics_of_premises
#print axioms matchingEvaluator_respectsStatics
#print axioms matching_run_step
#print axioms matching_run_step_inv
#print axioms emptySpace_run_normal
#print axioms atomOf_injective
#print axioms atomOf_wellSorted
#print axioms applyBindings_sideOf
#print axioms substitute_of_applyBindings_sideOf
#print axioms rootStep_ofTable_iff
#print axioms atomOf_mem_matchResults
#print axioms exists_instance_of_mem_matchResults
#print axioms matchingMap_hosting
#print axioms matchingCandidate_hostsEvery
#print axioms matchingCandidate_hostOf_firstOrderInstances
#print axioms choiceInstances_hostedBy_matching
#print axioms freeInstances_not_hostedBy_matching

end Mettapedia.Logic.HostingStyles.PrimeCandidate
