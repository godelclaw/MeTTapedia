import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.AuthoredEvaluator

/-!
# What the matching evaluator computes, equation by equation

The matching evaluator is given by the matcher and the substitution of the
framework, applied to stored atoms read as sides of rules.  An equation
program has no such functions: it has equations on first-order data, taken in
order.  This module restates what the matching evaluator computes in that
form, as functions defined by cases on the stored atom, and proves each equal
to the existing definition.  The program of `MatchingProgram` computes these
functions, one equation for each case.

* `lookupValue`: the value that bindings give to a name.  It is the lookup of
  the framework (`applyBindings_fvar`), and merging two lists of bindings is a
  recursion on it (`mergeBindings_cons`).
* `firstOrder`: a stored atom reads as a first-order side
  (`firstOrder_eq`).
* `ruleMatch`: the match of a stored atom, read as a left side, against a
  subject; one match at most (`matchPattern_asRule`).
* `ruleInstance`: the instance of a stored atom, read as a right side
  (`applyBindings_asRule`).
* `atomResult`: the answer of one stored atom (`atomResults_eq`), and so the
  answers of a space (`matchResults_eq_filterMap`).
* `matchingAnswers`: the answers of the matching evaluator to a relation and
  a list of inputs, and the matching evaluator in terms of it
  (`matchingEvaluator_apply`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredEvaluators

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.Dedukti.Language (metaName)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Logic.HostingStyles.PrimeCandidate

/-! ## Bindings -/

/-- The value that bindings give to a name: that of the first entry with the
name. -/
def lookupValue : Bindings → String → Option Pattern
  | [], _ => none
  | binding :: rest, name => if binding.1 = name then some binding.2 else lookupValue rest name

theorem find?_eq_lookupValue (name : String) :
    ∀ bindings : Bindings, (bindings.find? (·.1 == name)).map (·.2) = lookupValue bindings name
  | [] => rfl
  | binding :: rest => by
      by_cases same : binding.1 = name
      · simp [lookupValue, same]
      · simp [lookupValue, same, find?_eq_lookupValue name rest]

/-- The value of a name, or the name itself as a variable. -/
def boundOr (bindings : Bindings) (name : String) : Pattern :=
  (lookupValue bindings name).getD (.fvar name)

/-- **Positive**: a bound name has its value. -/
theorem boundOr_bound (name : String) (value : Pattern) (rest : Bindings) :
    boundOr ((name, value) :: rest) name = value := by
  simp [boundOr, lookupValue]

/-- **Negative**: a name that is not bound is the variable. -/
theorem boundOr_nil (name : String) : boundOr [] name = .fvar name := rfl

/-- **The instance of a variable is its value, or the variable.** -/
theorem applyBindings_fvar (name : String) :
    ∀ bindings : Bindings, applyBindings bindings (.fvar name) = boundOr bindings name
  | [] => by simp [applyBindings, boundOr, lookupValue]
  | binding :: rest => by
      rw [applyBindings_fvar_cons, applyBindings_fvar name rest]
      by_cases same : binding.1 = name <;> simp [boundOr, lookupValue, same]

theorem mergeBindings_nil (bindings : Bindings) : mergeBindings bindings [] = some bindings := rfl

/-- **Merging, one entry at a time**: a new name is added in front; a name
that is bound must be bound to the same value. -/
theorem mergeBindings_cons (bindings : Bindings) (name : String) (value : Pattern)
    (rest : Bindings) :
    mergeBindings bindings ((name, value) :: rest) =
      match lookupValue bindings name with
      | none => mergeBindings ((name, value) :: bindings) rest
      | some existing => if existing = value then mergeBindings bindings rest else none := by
  have found := find?_eq_lookupValue name bindings
  unfold mergeBindings
  rw [List.foldlM_cons]
  cases entry : bindings.find? (·.1 == name) with
  | none =>
      rw [entry] at found
      simp only [Option.map_none] at found
      simp [entry, ← found]
  | some pair =>
      obtain ⟨key, existing⟩ := pair
      rw [entry] at found
      simp only [Option.map_some] at found
      rw [← found]
      by_cases same : existing = value
      · simp [entry, same]
      · simp [entry, same]

/-- **Positive**: a bound name. -/
theorem lookupValue_bound (name : String) (value : Pattern) (rest : Bindings) :
    lookupValue ((name, value) :: rest) name = some value := by
  simp [lookupValue]

/-- **Negative**: no bindings, no value. -/
theorem lookupValue_nil (name : String) : lookupValue [] name = none := rfl

/-! ## The names of pattern variables -/

/-- **The name of a pattern variable, as data**: as many cells of the
character `x` as its index and one more. -/
theorem encodeName_metaName (index : Nat) :
    encodeName (metaName index) = cells (List.replicate (index + 1) (encodeCharacter 'x')) :=
  encodeName_ofList_replicate (index + 1) 'x'

/-! ## Stored atoms that read as first-order sides -/

mutual
  /-- **A stored atom reads as a first-order side of a rule**: no binder, no
  substitution and no collection outside its variable atoms. -/
  def firstOrder : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply label arguments =>
        if label = "prime-variable" then true else firstOrderList arguments
    | .lambda _ _ => false
    | .multiLambda _ _ _ => false
    | .subst _ _ => false
    | .collection _ _ _ => false

  /-- All of a list read so. -/
  def firstOrderList : List Pattern → Bool
    | [] => true
    | pattern :: patterns => firstOrder pattern && firstOrderList patterns
end

mutual
  theorem firstOrder_eq : ∀ pattern : Pattern,
      firstOrder pattern = isMatchCorrectAux (asRule pattern)
    | .bvar _ => by simp [firstOrder, asRule, isMatchCorrectAux]
    | .fvar _ => by simp [firstOrder, asRule, isMatchCorrectAux]
    | .apply label arguments => by
        by_cases isVariable : label = "prime-variable"
        · simp [firstOrder, asRule, isVariable, isMatchCorrectAux]
        · rw [firstOrder, if_neg isVariable, asRule, if_neg isVariable, isMatchCorrectAux,
            firstOrderList_eq arguments]
    | .lambda _ _ => by simp [firstOrder, asRule, isMatchCorrectAux]
    | .multiLambda _ _ _ => by simp [firstOrder, asRule, isMatchCorrectAux]
    | .subst _ _ => by simp [firstOrder, asRule, isMatchCorrectAux]
    | .collection _ _ _ => by simp [firstOrder, asRule, isMatchCorrectAux]

  theorem firstOrderList_eq : ∀ patterns : List Pattern,
      firstOrderList patterns = isMatchCorrectListAux (asRuleList patterns)
    | [] => by simp [firstOrderList, asRuleList, isMatchCorrectListAux]
    | pattern :: patterns => by
        rw [firstOrderList, asRuleList, isMatchCorrectListAux, firstOrder_eq pattern,
          firstOrderList_eq patterns]
end

/-- **Positive**: a variable atom, whatever its index. -/
theorem firstOrder_variable (arguments : List Pattern) :
    firstOrder (.apply "prime-variable" arguments) = true := by
  simp [firstOrder]

/-- **Negative**: an abstraction. -/
theorem firstOrder_lambda (binder : Option String) (body : Pattern) :
    firstOrder (.lambda binder body) = false := rfl

/-! ## The match of a stored atom against a subject -/

mutual
  /-- **The match of a stored atom, read as a left side, against a subject.** -/
  def ruleMatch : Pattern → Pattern → Option Bindings
    | .bvar index, subject =>
        match subject with
        | .bvar other => if index = other then some [] else none
        | _ => none
    | .fvar name, subject => some [(name, subject)]
    | .apply label arguments, subject =>
        if label = "prime-variable" then some [(metaName (indexOf arguments), subject)]
        else
          match subject with
          | .apply other subjects =>
              if label = other then ruleMatchList arguments subjects else none
          | _ => none
    | .lambda _ _, _ => none
    | .multiLambda _ _ _, _ => none
    | .subst _ _, _ => none
    | .collection _ _ _, _ => none

  /-- The match of a list of stored atoms against a list of subjects. -/
  def ruleMatchList : List Pattern → List Pattern → Option Bindings
    | [], [] => some []
    | [], _ :: _ => none
    | _ :: _, [] => none
    | pattern :: patterns, subject :: subjects =>
        (ruleMatch pattern subject).bind fun head =>
          (ruleMatchList patterns subjects).bind fun tail => mergeBindings head tail
end

theorem ruleMatchList_eq_none :
    ∀ (patterns subjects : List Pattern), patterns.length ≠ subjects.length →
      ruleMatchList patterns subjects = none
  | [], [], apart => absurd rfl apart
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | pattern :: patterns, subject :: subjects, apart => by
      have later := ruleMatchList_eq_none patterns subjects (fun same => apart (by simp [same]))
      rw [ruleMatchList, later]
      cases ruleMatch pattern subject <;> rfl

theorem flatMap_filterMap_toList {α β γ : Type} (first : Option α) (second : Option β)
    (combine : α → β → Option γ) :
    (first.toList.flatMap fun head => second.toList.filterMap fun tail => combine head tail) =
      (first.bind fun head => second.bind fun tail => combine head tail).toList := by
  cases first with
  | none => rfl
  | some head =>
      cases second with
      | none => rfl
      | some tail => cases found : combine head tail <;> simp [found]

mutual
  /-- **The matcher of the framework, on a stored atom read as a first-order
  left side, finds the match of the atom and no other.** -/
  theorem matchPattern_asRule : ∀ (pattern subject : Pattern), firstOrder pattern = true →
      matchPattern (asRule pattern) subject = (ruleMatch pattern subject).toList
    | .bvar index, subject, _ => by
        cases subject with
        | bvar other =>
            rw [asRule, matchPattern, ruleMatch]
            by_cases same : index = other <;> simp [same]
        | _ => simp [asRule, matchPattern, ruleMatch]
    | .fvar name, subject, _ => by simp [asRule, matchPattern, ruleMatch]
    | .apply label arguments, subject, exact => by
        by_cases isVariable : label = "prime-variable"
        · simp [asRule, isVariable, matchPattern, ruleMatch]
        · rw [firstOrder, if_neg isVariable] at exact
          cases subject with
          | apply other subjects =>
              rw [asRule, if_neg isVariable, ruleMatch, if_neg isVariable, matchPattern,
                matchArgs_asRuleList arguments subjects exact]
              by_cases same : label = other
              · by_cases lengths : arguments.length = subjects.length
                · simp [same, lengths]
                · simp [same, lengths, ruleMatchList_eq_none arguments subjects lengths]
              · simp [same]
          | _ => simp [asRule, isVariable, ruleMatch, matchPattern]
    | .lambda _ _, _, exact => by simp [firstOrder] at exact
    | .multiLambda _ _ _, _, exact => by simp [firstOrder] at exact
    | .subst _ _, _, exact => by simp [firstOrder] at exact
    | .collection _ _ _, _, exact => by simp [firstOrder] at exact

  theorem matchArgs_asRuleList : ∀ (patterns subjects : List Pattern),
      firstOrderList patterns = true →
        matchArgs (asRuleList patterns) subjects = (ruleMatchList patterns subjects).toList
    | [], [], _ => by simp [asRuleList, matchArgs, ruleMatchList]
    | [], _ :: _, _ => by simp [asRuleList, matchArgs, ruleMatchList]
    | _ :: _, [], _ => by simp [asRuleList, matchArgs, ruleMatchList]
    | pattern :: patterns, subject :: subjects, exact => by
        simp only [firstOrderList, Bool.and_eq_true] at exact
        rw [asRuleList, matchArgs, matchPattern_asRule pattern subject exact.1,
          matchArgs_asRuleList patterns subjects exact.2, ruleMatchList]
        exact flatMap_filterMap_toList _ _ _
end

/-- **Positive**: a variable atom matches every subject. -/
theorem ruleMatch_variable (index subject : Pattern) :
    ruleMatch (variableAtom index) subject = some [(metaName (numeralValue index), subject)] := by
  simp [variableAtom, ruleMatch, indexOf]

/-- **Negative**: an abstraction matches nothing. -/
theorem ruleMatch_lambda (binder : Option String) (body subject : Pattern) :
    ruleMatch (.lambda binder body) subject = none := rfl

/-! ## The instance of a stored atom -/

mutual
  /-- **The instance of a stored atom, read as a right side, under
  bindings.** -/
  def ruleInstance (bindings : Bindings) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => boundOr bindings name
    | .apply label arguments =>
        if label = "prime-variable" then boundOr bindings (metaName (indexOf arguments))
        else .apply label (ruleInstanceList bindings arguments)
    | .lambda binder body => .lambda binder body
    | .multiLambda arity binders body => .multiLambda arity binders body
    | .subst body replacement => .subst body replacement
    | .collection kind elements rest => .collection kind elements rest

  /-- The instances of a list of stored atoms. -/
  def ruleInstanceList (bindings : Bindings) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => ruleInstance bindings pattern :: ruleInstanceList bindings patterns
end

mutual
  /-- **The substitution of the framework, on a stored atom read as a
  first-order right side, gives the instance of the atom.** -/
  theorem applyBindings_asRule (bindings : Bindings) : ∀ pattern : Pattern,
      firstOrder pattern = true →
        applyBindings bindings (asRule pattern) = ruleInstance bindings pattern
    | .bvar index, _ => by simp [asRule, applyBindings, ruleInstance]
    | .fvar name, _ => by rw [asRule, applyBindings_fvar, ruleInstance]
    | .apply label arguments, exact => by
        by_cases isVariable : label = "prime-variable"
        · rw [asRule, if_pos isVariable, applyBindings_fvar, ruleInstance, if_pos isVariable]
        · rw [firstOrder, if_neg isVariable] at exact
          rw [asRule, if_neg isVariable, ruleInstance, if_neg isVariable,
            ← map_applyBindings_asRuleList bindings arguments exact]
          simp [applyBindings]
    | .lambda _ _, exact => by simp [firstOrder] at exact
    | .multiLambda _ _ _, exact => by simp [firstOrder] at exact
    | .subst _ _, exact => by simp [firstOrder] at exact
    | .collection _ _ _, exact => by simp [firstOrder] at exact

  theorem map_applyBindings_asRuleList (bindings : Bindings) : ∀ patterns : List Pattern,
      firstOrderList patterns = true →
        (asRuleList patterns).map (applyBindings bindings) = ruleInstanceList bindings patterns
    | [], _ => rfl
    | pattern :: patterns, exact => by
        simp only [firstOrderList, Bool.and_eq_true] at exact
        rw [asRuleList, List.map_cons, applyBindings_asRule bindings pattern exact.1,
          map_applyBindings_asRuleList bindings patterns exact.2, ruleInstanceList]
end

/-- **Positive**: a variable atom is replaced by the value of its pattern
variable. -/
theorem ruleInstance_variable (index value : Pattern) :
    ruleInstance [(metaName (numeralValue index), value)] (variableAtom index) = value := by
  simp [variableAtom, ruleInstance, indexOf, boundOr, lookupValue]

/-- **Negative**: an abstraction is left as it is. -/
theorem ruleInstance_lambda (bindings : Bindings) (binder : Option String) (body : Pattern) :
    ruleInstance bindings (.lambda binder body) = .lambda binder body := rfl

/-! ## The answers of a stored atom, and of a space -/

/-- **The answer of one stored atom for a subject**: for an equation whose two
sides read as first-order sides, the instance of the right side under the
match of the left side. -/
def atomResult (subject atom : Pattern) : Option Pattern :=
  match atom with
  | .apply label arguments =>
      if label = "=" then
        match arguments with
        | [left, right] =>
            if (firstOrder left && firstOrder right) = true then
              (ruleMatch left subject).map fun bindings => ruleInstance bindings right
            else none
        | _ => none
      else none
  | _ => none

theorem viewEquation?_apply_of_ne {label : String} (other : label ≠ "=")
    (arguments : List Pattern) : MeTTaZero.viewEquation? (.apply label arguments) = none := by
  unfold MeTTaZero.viewEquation?
  split
  · rename_i same
    simp only [Pattern.apply.injEq] at same
    exact absurd same.1 other
  · rfl

/-- **A stored atom answers a subject once at most, with the answer above.** -/
theorem atomResults_eq (subject atom : Pattern) :
    atomResults subject atom = (atomResult subject atom).toList := by
  cases atom with
  | apply label arguments =>
      by_cases equation : label = "="
      · subst equation
        rcases arguments with _ | ⟨left, _ | ⟨right, _ | ⟨third, rest⟩⟩⟩
        · simp [atomResults, atomResult, MeTTaZero.viewEquation?]
        · simp [atomResults, atomResult, MeTTaZero.viewEquation?]
        · by_cases exact : (firstOrder left && firstOrder right) = true
          · have sides := exact
            simp only [Bool.and_eq_true] at sides
            have matcher : (isMatchCorrectAux (asRule left) && isMatchCorrectAux (asRule right)) =
                true := by rw [← firstOrder_eq, ← firstOrder_eq]; exact exact
            simp only [atomResults, MeTTaZero.viewEquation?, matcher, if_true, atomResult, exact,
              matchPattern_asRule left subject sides.1]
            cases ruleMatch left subject with
            | none => rfl
            | some bindings => simp [applyBindings_asRule bindings right sides.2]
          · have matcher : ¬ (isMatchCorrectAux (asRule left) && isMatchCorrectAux (asRule right)) =
                true := by rw [← firstOrder_eq, ← firstOrder_eq]; exact exact
            simp [atomResults, MeTTaZero.viewEquation?, matcher, atomResult, exact]
        · simp [atomResults, atomResult, MeTTaZero.viewEquation?]
      · simp [atomResults, atomResult, viewEquation?_apply_of_ne equation, equation]
  | _ => simp [atomResults, atomResult, MeTTaZero.viewEquation?]

theorem flatMap_toList_eq_filterMap {α β : Type} (answer : α → Option β) :
    ∀ items : List α, (items.flatMap fun item => (answer item).toList) = items.filterMap answer
  | [] => rfl
  | item :: items => by
      rw [List.flatMap_cons, flatMap_toList_eq_filterMap answer items, List.filterMap_cons]
      cases answer item <;> rfl

/-- **The answers of a space are the answers of its stored atoms.** -/
theorem matchResults_eq_filterMap (space subject : Pattern) :
    matchResults space subject = (storedAtoms space).filterMap (atomResult subject) := by
  rw [matchResults, ← flatMap_toList_eq_filterMap]
  congr 1
  funext atom
  exact atomResults_eq subject atom

/-- **Positive**: an equation between two variable atoms of one index sends
every subject to itself. -/
theorem atomResult_identity (index subject : Pattern) :
    atomResult subject (.apply "=" [variableAtom index, variableAtom index]) = some subject := by
  simp [atomResult, variableAtom, firstOrder, ruleMatch, ruleInstance, boundOr, lookupValue]

/-- **Negative**: an atom that is no equation answers nothing. -/
theorem atomResult_unit (subject : Pattern) : atomResult subject unitAtom = none := by
  simp [atomResult, unitAtom]

/-! ## The matching evaluator, by its answers -/

/-- **The answers of the matching evaluator** to a relation and a list of
inputs: for `PrimeStep` and two inputs, the answers of the first, as a space,
for the second, both read up to the static equivalence. -/
def matchingAnswers (relation : String) (inputs : List Pattern) : List Pattern :=
  if relation = "PrimeStep" then
    match inputs with
    | [space, subject] => matchResults (contract space) (contract subject)
    | _ => []
  else []

/-- **The matching evaluator answers the queries of `PrimeStep` on two inputs
by `matchingAnswers`, and nothing else.** -/
theorem matchingEvaluator_apply (lang : LanguageDef) (bindings : Bindings) (premise : Premise) :
    matchingEvaluator lang bindings premise =
      match premise with
      | .relationQuery relation arguments =>
        match queryShape arguments with
        | some (inputs, answer) =>
            (matchingAnswers relation (inputs.map (applyBindings bindings))).map fun result =>
              (answer, result) :: bindings
        | none => []
      | _ => [] := by
  unfold matchingEvaluator
  split
  · rfl
  · rename_i other
    cases premise with
    | relationQuery relation arguments =>
        show ([] : List Bindings) = match queryShape arguments with
          | some (inputs, answer) =>
              (matchingAnswers relation (inputs.map (applyBindings bindings))).map fun result =>
                (answer, result) :: bindings
          | none => []
        cases shape : queryShape arguments with
        | none => rfl
        | some found =>
            obtain ⟨inputs, answer⟩ := found
            have split := eq_append_of_queryShape shape
            have empty : matchingAnswers relation (inputs.map (applyBindings bindings)) = [] := by
              by_cases step : relation = "PrimeStep"
              · subst step
                rcases inputs with _ | ⟨space, _ | ⟨subject, _ | ⟨third, rest⟩⟩⟩
                · rfl
                · rfl
                · exact absurd (by rw [split]; rfl) (other space subject answer)
                · rfl
              · simp [matchingAnswers, step]
            simp [empty]
    | _ => rfl

/-- **Positive**: the run premise, under bindings of a space and a subject. -/
theorem matchingAnswers_run (space subject : Pattern) :
    matchingAnswers "PrimeStep" [space, subject] =
      matchResults (contract space) (contract subject) := rfl

/-- **Negative**: another relation has no answer. -/
theorem matchingAnswers_other (inputs : List Pattern) : matchingAnswers "ZeroQuery" inputs = [] := by
  simp [matchingAnswers]

#print axioms mergeBindings_cons
#print axioms applyBindings_fvar
#print axioms firstOrder_eq
#print axioms matchPattern_asRule
#print axioms applyBindings_asRule
#print axioms atomResults_eq
#print axioms matchResults_eq_filterMap
#print axioms matchingEvaluator_apply

end Mettapedia.Logic.HostingStyles.AuthoredEvaluators
