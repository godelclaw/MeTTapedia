import Mettapedia.Logic.HostingStyles.AtomsReduce.Encoding

/-!
# The static equivalence of the candidate, where no name is dropped

The static equivalence of the candidate is that of quotation and dropping:
two terms are equal exactly when they have one contraction
(`QuoteDropOnly.termSetoid_iff`).  In the probe a sort apart from quotation
has only terms that are their own contraction (`contract_of_hasType`); the
sort of atoms is not one, in the probe or here, since a dropping takes a
name.

In the candidate a name is taken by dropping and by nothing else
(`NamesOnlyDropped`, `atomsReduce_namesOnlyDropped`).  So a quotation occurs
in an atom or a space only beneath a dropping, and **a term of those sorts
whose contraction has no dropping is its own contraction**
(`contract_of_dropFree`).  Hence a term that the static equivalence
identifies with a term without quotation and dropping is that term
(`eq_of_related_of_dropFree`): on such terms the static equivalence is
identity, and a step up to the static equivalence is a step.

**Negative**: in the probe the evaluation of a name takes a name too
(`language_not_namesOnlyDropped`); and with a dropping the static equivalence
is not identity (`droppedQuotation_spellings`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AtomsReduce

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

/-! ## Names are taken by dropping alone -/

/-- The label of dropping, as a count. -/
def dropLabel (label : String) : Bool := label == "prime-drop"

/-- **Names are taken by dropping alone**, among the constructors of some
sorts: none of them is quotation, and each of them other than dropping takes
arguments of those sorts. -/
def NamesOnlyDropped (lang : LanguageDef) (sorts : List String) : Prop :=
  ∀ rule ∈ lang.terms, rule.category ∈ sorts →
    rule.label ≠ "prime-quote" ∧
      (rule.label ≠ "prime-drop" →
        ∀ parameter ∈ rule.params, ∀ expected ∈ parameterType? parameter,
          resultIn sorts expected = true)

/-- The sorts of the candidate other than the sort of names. -/
def unquotedSorts : List String := ["Atom", "Space"]

/-- **Positive**: the atoms and the spaces of the candidate. -/
theorem atomsReduce_namesOnlyDropped : NamesOnlyDropped atomsReduce unquotedSorts := by
  intro rule member category
  have listed : rule ∈
      [MeTTaZero.equationConstructor, unitConstructor, quoteConstructor, dropConstructor,
        emptySpaceConstructor, addAtomConstructor, variableConstructor, symbolConstructor,
        runAtomConstructor, applicationConstructor, abstractionConstructor, productConstructor] :=
    member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd category (by decide)
    | refine ⟨by decide, fun other => ?_⟩
      first
        | exact absurd rfl other
        | intro parameter inParams expected isType
          revert isType
          revert expected
          revert inParams
          revert parameter
          decide

/-- **Negative**: in the probe the evaluation of a name takes a name, and is
no dropping. -/
theorem language_not_namesOnlyDropped :
    ¬ NamesOnlyDropped language ["Atom", "Space", "Process"] := by
  intro only
  have taken := (only evaluateNameConstructor (by decide) (by decide)).2 (by decide)
    (.simple "name" (.base "CandidateName")) (by decide) (.base "CandidateName") rfl
  revert taken
  decide

/-! ## A term whose contraction drops no name is its own contraction -/

mutual
  /-- **A term of sorts in which names are taken by dropping alone, whose
  contraction has no dropping, is its own contraction.** -/
  theorem contract_of_dropFree {lang : LanguageDef} {sorts : List String}
      (only : NamesOnlyDropped lang sorts) (sorted : QuoteDropSorted lang) {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType lang free bound pattern type)
      (inSorts : resultIn sorts type = true) (object : isObjectPattern pattern = true)
      (dropFree : tokens dropLabel (contract pattern) = 0) : contract pattern = pattern := by
    cases typed with
    | bvar _ => rw [contract]
    | fvar _ => rw [contract]
    | @constructor _ rule arguments member _ argumentsTyped =>
        have category : rule.category ∈ sorts := by simpa [resultIn] using inSorts
        obtain ⟨other, parameters⟩ := only rule member category
        rw [contract_apply_of_ne other] at dropFree ⊢
        rw [tokens] at dropFree
        have notDrop : rule.label ≠ "prime-drop" := by
          intro isDrop
          simp [dropLabel, isDrop] at dropFree
        rw [contractList_of_dropFree_arguments only sorted argumentsTyped (parameters notDrop)
          (by simpa [isObjectPattern] using object) (by omega)]
    | lambda bodyTyped =>
        rw [contract] at dropFree ⊢
        rw [contract_of_dropFree only sorted bodyTyped (by simpa [resultIn] using inSorts)
          (by simpa [isObjectPattern] using object) (by simpa [tokens] using dropFree)]
    | multiLambda bodyTyped =>
        rw [contract] at dropFree ⊢
        rw [contract_of_dropFree only sorted bodyTyped (by simpa [resultIn] using inSorts)
          (by simpa [isObjectPattern] using object) (by simpa [tokens] using dropFree)]
    | subst _ _ => simp [isObjectPattern] at object
    | collection elementsTyped =>
        simp only [isObjectPattern, Bool.and_eq_true] at object
        rw [contract, contractList_eq_map] at dropFree ⊢
        rw [contractList_of_dropFree_elements only sorted elementsTyped
          (by simpa [resultIn] using inSorts) object.2 (by simpa [tokens] using dropFree)]
    | @collectionConstructor _ rule parameterName kind elements rest elementType member shape
        elementsTyped =>
        have category : rule.category ∈ sorts := by simpa [resultIn] using inSorts
        simp only [isObjectPattern, Bool.and_eq_true] at object
        rw [contract, contractList_eq_map] at dropFree ⊢
        by_cases isDrop : rule.label = "prime-drop"
        · have params := sorted.drop rule member isDrop
          rw [params] at shape
          simp at shape
        · have element := (only rule member category).2 isDrop (.simple parameterName
            (.collection kind elementType)) (by rw [shape]; exact List.mem_singleton.mpr rfl)
            (.collection kind elementType) rfl
          rw [contractList_of_dropFree_elements only sorted elementsTyped
            (by simpa [resultIn] using element) object.2 (by simpa [tokens] using dropFree)]

  theorem contractList_of_dropFree_arguments {lang : LanguageDef} {sorts : List String}
      (only : NamesOnlyDropped lang sorts) (sorted : QuoteDropSorted lang) {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes lang free bound arguments parameters)
      (inSorts : ∀ parameter ∈ parameters, ∀ expected ∈ parameterType? parameter,
        resultIn sorts expected = true)
      (object : isObjectPatternList arguments = true)
      (dropFree : tokensList dropLabel (arguments.map contract) = 0) :
      arguments.map contract = arguments := by
    cases typed with
    | nil => rfl
    | cons _ expectedType argumentTyped argumentsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        rw [List.map_cons, tokensList] at dropFree
        rw [List.map_cons,
          contract_of_dropFree only sorted argumentTyped
            (inSorts _ (List.mem_cons_self ..) _ expectedType) object.1 (by omega),
          contractList_of_dropFree_arguments only sorted argumentsTyped
            (fun parameter member => inSorts parameter (List.mem_cons_of_mem _ member)) object.2
            (by omega)]

  theorem contractList_of_dropFree_elements {lang : LanguageDef} {sorts : List String}
      (only : NamesOnlyDropped lang sorts) (sorted : QuoteDropSorted lang) {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr}
      (typed : ElementsHaveType lang free bound elements elementType)
      (inSorts : resultIn sorts elementType = true)
      (object : isObjectPatternList elements = true)
      (dropFree : tokensList dropLabel (elements.map contract) = 0) :
      elements.map contract = elements := by
    cases typed with
    | nil => rfl
    | cons elementTyped elementsTyped =>
        simp only [isObjectPatternList, Bool.and_eq_true] at object
        rw [List.map_cons, tokensList] at dropFree
        rw [List.map_cons, contract_of_dropFree only sorted elementTyped inSorts object.1 (by omega),
          contractList_of_dropFree_elements only sorted elementsTyped inSorts object.2 (by omega)]
end

/-- **A term of the candidate, at a type of atoms or spaces, that the static
equivalence identifies with a pattern without quotation and dropping is that
pattern.** -/
theorem eq_of_contract_eq_of_dropFree {interface : Contexts.Interface}
    (term : Contexts.Term atomsReduce interface)
    (inSorts : resultIn unquotedSorts interface.type = true) {image : Pattern}
    (dropFree : tokens dropLabel image = 0) (same : contract term.1 = image) : term.1 = image := by
  rw [← same]
  exact (contract_of_dropFree atomsReduce_namesOnlyDropped atomsReduce_quoteDropSorted term.2.1
    inSorts term.2.2.2.1
    (by rw [same]; exact dropFree)).symm

/-- The same, from the static equivalence. -/
theorem eq_of_related_of_dropFree {base : BasePremiseEvaluator} {interface : Contexts.Interface}
    {term image : Contexts.Term atomsReduce interface}
    (inSorts : resultIn unquotedSorts interface.type = true)
    (fixed : contract image.1 = image.1) (dropFree : tokens dropLabel image.1 = 0)
    (related : (termSetoid base atomsReduce interface).r image term) : term = image :=
  Subtype.ext (eq_of_contract_eq_of_dropFree term inSorts dropFree
    ((atomsReduce_quoteDropOnly.contract_eq related).symm.trans fixed))

/-! ## With a dropping the static equivalence is not identity -/

/-- The dropping of the quotation of the unit atom, as a closed atom. -/
def droppedUnit : Contexts.Term atomsReduce closedAtom :=
  ⟨dropped (quoted unitAtom), checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The same atom, written with one more quotation of a dropping. -/
def droppedUnitRespelled : Contexts.Term atomsReduce closedAtom :=
  ⟨dropped (quoted (dropped (quoted unitAtom))),
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **Negative**: a dropped quotation has two spellings, equal and
different. -/
theorem droppedQuotation_spellings (base : BasePremiseEvaluator) :
    (termSetoid base atomsReduce closedAtom).r droppedUnit droppedUnitRespelled ∧
      droppedUnit ≠ droppedUnitRespelled :=
  ⟨(atomsReduce_quoteDropOnly.termSetoid_iff atomsReduce_quoteDropSorted).mpr (by decide),
    fun same => absurd (congrArg Subtype.val same) (by decide)⟩

#print axioms atomsReduce_namesOnlyDropped
#print axioms language_not_namesOnlyDropped
#print axioms contract_of_dropFree
#print axioms eq_of_contract_eq_of_dropFree
#print axioms eq_of_related_of_dropFree
#print axioms droppedQuotation_spellings

end Mettapedia.Logic.HostingStyles.AtomsReduce
