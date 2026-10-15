import Mettapedia.Languages.MM0.Translation.FirstOrderTheoryPresentations

/-!
# The first-order fragment of MM0 is the class of presentations

Two classes of formal systems are compared.

* A **presentation** is a language with finitely many sorts and first-order
  constructors, definitional equations, judgment sorts, and finitely many
  inference rules whose premises and conclusion are schemas over typed
  metavariables.
* A **first-order MM0 theory** is the table of an MM0 development none of
  whose declarations binds a variable: `Theory.FirstOrder`.

The translation sends a presentation to an MM0 theory. This module proves
that the two classes are the same class, seen from the two sides.

* `generated_firstOrder`: the theory generated from a presentation is
  admitted from the empty theory, is first-order, and carries the
  presentation's names.
* `theory_sourcePresentation` (previous module): every first-order theory
  with names is the generated theory of a presentation.
* `read_generated`: reading a generated theory back gives a presentation
  with the same generated tables, and `read_derives_iff` shows that it
  derives exactly what the original presentation derives.

With `Presentation.derivability_iff` this says what MM0 without binders
checks: derivability modulo definitions in a sorted first-order rule
presentation, and nothing else.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderFragment

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderConversion
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderConversion FirstOrderRules
open FirstOrderAdmission FirstOrderNaming FirstOrderTheoryPresentations

/-- The names a presentation gives to the declarations of its theory. -/
def presentationNames (source : Presentation) : Names :=
  { sorts := source.syntaxSignature.sorts
    terms := source.syntaxSignature.names
    rules := source.rules.map fun rule => rule.row.id }

/-- Every declaration of a generated theory is first-order. -/
theorem admissions_firstOrder (source : Presentation) :
    ∀ admission ∈ admissions source, admission.FirstOrder := by
  intro admission member
  simp only [admissions, List.mem_append, List.mem_map] at member
  rcases member with
    ((⟨row, -, rfl⟩ | ⟨row, inTerms, rfl⟩) | ⟨row, inDefinitions, rfl⟩) | ⟨row, inTheorems, rfl⟩
  · trivial
  · obtain ⟨rule, -, compiled⟩ := List.mem_compileIndexed_value _ _ 0 inTerms
    have declared : declaration? source.syntaxSignature.sorts rule = some row.2 := by
      split at compiled
      · exact compiled
      · cases compiled
    obtain ⟨parameters, -, dependencies⟩ := declaration?_fields declared
    exact ⟨parameters?_ordinary parameters, dependencies⟩
  · obtain ⟨sourceRow, rowMember, computed⟩ := List.mem_filterMap.mp inDefinitions
    obtain ⟨declaration, expression, compiledRow, same⟩ := definitionRow?_eq source rowMember
    rw [same] at computed
    cases computed
    exact ⟨(signature_dependencyFree source compiledRow.term).1, rfl⟩
  · obtain ⟨rule, -, compiled⟩ := List.mem_compileIndexed_value _ _ 0 inTheorems
    exact ((rule?_eq_some_iff _ _ _).mp compiled).contexts.ordinary

/-- The tables of a generated theory are first-order. -/
theorem chronological_firstOrder (source : Presentation) : (chronological source).FirstOrder :=
  (admitted source).firstOrder (admissions_firstOrder source) Theory.empty_firstOrder

/-- The names of a presentation fit its generated theory. -/
theorem chronological_fit (source : Presentation) :
    (presentationNames source).Fit (chronological source) where
  distinctSorts := source.syntaxSignature.distinctSorts
  distinctTerms := source.syntaxSignature.distinctConstructors
  distinctRules := source.distinctRules
  sorts := by
    intro index
    rw [chronological_sorts, Presentation.theory_sortSignature]
    show (source.syntaxSignature.sorts[index]?).map source.sortInfo ≠ none ↔
      index < source.syntaxSignature.sorts.length
    simp
  terms := by
    intro index
    rw [chronological_terms, Presentation.theory_termSignature]
    show source.syntaxSignature.termSignature index ≠ none ↔
      index < (constructorNames source.syntaxSignature.language).length
    cases lookup : source.syntaxSignature.language.terms[index]? with
    | none =>
        have beyond := List.getElem?_eq_none_iff.mp lookup
        have value : source.syntaxSignature.termSignature index = none := by
          show source.syntaxSignature.language.terms[index]?.bind
            (declaration? source.syntaxSignature.sorts) = none
          rw [lookup]
          rfl
        rw [value]
        simp [constructorNames, Nat.not_lt.mpr beyond]
    | some rule =>
        obtain ⟨declaration, compiled⟩ :=
          source.syntaxSignature.ordinaryConstructors rule (List.mem_of_getElem? lookup)
        have below := (List.getElem?_eq_some_iff.mp lookup).1
        have value : source.syntaxSignature.termSignature index = some declaration := by
          show source.syntaxSignature.language.terms[index]?.bind
            (declaration? source.syntaxSignature.sorts) = some declaration
          rw [lookup]
          exact compiled
        rw [value]
        simp [constructorNames, below]
  rules := by
    intro index
    rw [chronological_theorems, Presentation.theory_theoremSignature]
    show source.rules[index]?.bind (rule? source.syntaxSignature) ≠ none ↔
      index < (source.rules.map fun rule => rule.row.id).length
    cases lookup : source.rules[index]? with
    | none =>
        have beyond := List.getElem?_eq_none_iff.mp lookup
        simp [Nat.not_lt.mpr beyond]
    | some rule =>
        obtain ⟨declaration, compiled⟩ := source.rule_compiles (List.mem_of_getElem? lookup)
        have below := (List.getElem?_eq_some_iff.mp lookup).1
        simp [(rule?_eq_some_iff _ _ _).mpr compiled, below]

/-- **A generated theory is a first-order MM0 theory.** It is admitted from
the empty theory, none of its declarations binds a variable, and its
lookups are the generated tables. -/
theorem generated_firstOrder (source : Presentation) :
    ∃ theory : Theory,
      Theory.Runs {} (admissions source) theory ∧ theory.FirstOrder ∧
      (presentationNames source).Fit theory ∧
      theory.sortSignature = source.theory.sortSignature ∧
      theory.termSignature = source.theory.termSignature ∧
      theory.definitionSignature = source.theory.definitionSignature ∧
      theory.theoremSignature = source.theory.theoremSignature :=
  ⟨chronological source, admitted source, chronological_firstOrder source,
    chronological_fit source, chronological_sorts source, chronological_terms source,
    chronological_definitions source, chronological_theorems source⟩

/-- The presentation read back from the generated theory of a presentation. -/
def readBack (source : Presentation) : Presentation :=
  sourcePresentation (presentationNames source) (chronological source)
    (chronological_fit source) (chronological_firstOrder source)

/-- **Reading a generated theory back loses nothing MM0 sees.** The
presentation read from the generated theory generates the same term,
definition and assertion tables. -/
theorem read_generated (source : Presentation) :
    (readBack source).theory.termSignature = source.theory.termSignature ∧
      (readBack source).theory.definitionSignature = source.theory.definitionSignature ∧
      (readBack source).theory.theoremSignature = source.theory.theoremSignature :=
  ⟨(termSignature_eq _ _).trans (chronological_terms source),
    (definitionSignature_eq _ _).trans (chronological_definitions source),
    (theoremSignature_eq _ _).trans (chronological_theorems source)⟩

/-- **The presentation read back derives what the original derives.** The
two differ in the names of their metavariables and in nothing a derivation
depends on. -/
theorem read_derives_iff (source : Presentation) {base other : BasePremiseEvaluator}
    {bound : List TypeExpr} {context : Context} {hypotheses : List Pattern}
    {targetHypotheses : List Preterm} {pattern : Pattern} {expression : Preterm}
    (contexts : ContextEncodes source.syntaxSignature.sorts bound context)
    (localScope : List.Forall₂ (Encodes source.syntaxSignature.names) hypotheses
      targetHypotheses)
    (encoded : Encodes source.syntaxSignature.names pattern expression) :
    DerivesModulo base source.syntaxSignature.language source.rules bound hypotheses pattern ↔
      DerivesModulo other (readBack source).syntaxSignature.language (readBack source).rules
        bound hypotheses pattern := by
  have original := Presentation.derivability_iff (base := base) contexts localScope encoded
  have read := derives_iff (base := other) (chronological_fit source)
    (chronological_firstOrder source) (bound := bound) (context := context)
    (hypotheses := hypotheses) (targetHypotheses := targetHypotheses) (pattern := pattern)
    (expression := expression) contexts localScope encoded
  rw [chronological_terms, chronological_definitions, chronological_theorems] at read
  exact original.trans read.symm

/-! ## Outside the fragment -/

/-- A theory that declares a constructor with a bound formal is not
first-order. -/
theorem bound_formal_not_firstOrder {theory : Theory} {index sort result : Nat}
    {rest : Context} {dependencies : Finset Nat}
    (declared : theory.termSignature index = some ⟨.bound sort :: rest, result, dependencies⟩) :
    ¬ theory.FirstOrder := by
  intro firstOrder
  obtain ⟨other, impossible⟩ :=
    (firstOrder.terms (index, _) (mem_of_lookup declared)).arguments (.bound sort) (by simp)
  cases impossible

/-- A theory with a definition that uses a dummy variable is not
first-order. -/
theorem dummy_not_firstOrder {theory : Theory} {index : Nat} {body : Definition.Body}
    (declared : theory.definitionSignature index = some body) (dummies : body.dummies ≠ []) :
    ¬ theory.FirstOrder :=
  fun firstOrder => dummies (firstOrder.bodies (index, body) (mem_of_lookup declared)).1

end Mettapedia.Languages.MM0.Translation.FirstOrderFragment
