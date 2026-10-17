import Mettapedia.Logic.HostingStyles.PrimeCandidate.ProbeDynamics
import Mettapedia.Logic.HostingStyles.TermsAloneHosting

/-!
# Where data that does not reduce lives in the candidate presentation

In the probe only the sort `Process` reduces.  So its atoms are inert, and so
are its names, where the principle "atoms reduce and data does not" would put
data.  This module exhibits both as inert data indexed by the natural
numbers:

* `probeAtoms`: the numeral atoms, nested equations over the unit atom;
* `probeNames`: their quotations, at the sort of names.

Neither family exhausts its sort: the dropping of a quoted unit atom is an
atom that is no numeral (`droppedAtom_not_numeral`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

open Mettapedia.Logic.HostingStyles

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef

/-! ## Numerals -/

/-- **The atom that stands for a number**: as many equations, nested on the
right over the unit atom. -/
def numeral : Nat → Pattern
  | 0 => unitAtom
  | count + 1 => .apply "=" [unitAtom, numeral count]

theorem numeral_injective : Function.Injective numeral := by
  intro first
  induction first with
  | zero =>
      intro second same
      cases second with
      | zero => rfl
      | succ second => simp [numeral, unitAtom] at same
  | succ first ih =>
      intro second same
      cases second with
      | zero => simp [numeral, unitAtom] at same
      | succ second =>
          simp only [numeral, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
          rw [ih same]

/-- A numeral has no quotation to contract. -/
theorem contract_numeral (count : Nat) : contract (numeral count) = numeral count := by
  induction count with
  | zero => decide
  | succ count ih =>
      rw [numeral, contract_apply_of_ne (by decide)]
      simp only [List.map_cons, List.map_nil, ih]
      rfl

/-- The quotation of a numeral is not contracted either. -/
theorem contract_quoted_numeral (count : Nat) :
    contract (quoted (numeral count)) = quoted (numeral count) := by
  have inner := contract_numeral count
  cases count with
  | zero => decide
  | succ count =>
      rw [numeral] at inner ⊢
      simp only [quoted, contract, contractList] at inner ⊢
      rw [inner]
      simp [contractRoot]

/-- **Every numeral is an atom**, beneath any binders, of every language that
declares the equation constructor and the unit atom. -/
theorem numeral_wellSorted_in {lang : LanguageDef}
    (equation : MeTTaZero.equationConstructor ∈ lang.terms) (unit : unitConstructor ∈ lang.terms)
    (bound : List TypeExpr) (count : Nat) :
    OpenPatternWellSorted lang FreeTypeContext.empty bound (.base "Atom") (numeral count) := by
  have unitSorted : OpenPatternWellSorted lang FreeTypeContext.empty bound (.base "Atom")
      unitAtom :=
    ⟨.constructor (rule := unitConstructor) unit
        (fun bare => by
          have checked := (usesBareCollection?_eq_true_iff _).mpr bare
          revert checked
          decide) .nil,
      by decide, by decide, by
        show unitAtom.isWellScopedAt bound.length = true
        simp [unitAtom, Pattern.isWellScopedAt, Pattern.isWellScopedListAt]⟩
  induction count with
  | zero => exact unitSorted
  | succ count ih =>
      obtain ⟨typed, canonical, object, scopeSafe⟩ := ih
      obtain ⟨unitTyped, unitCanonical, unitObject, unitScopeSafe⟩ := unitSorted
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact .constructor (rule := MeTTaZero.equationConstructor) equation
          (fun bare => by
            have checked := (usesBareCollection?_eq_true_iff _).mpr bare
            revert checked
            decide)
          (.cons trivial rfl unitTyped (.cons trivial rfl typed .nil))
      · simpa [numeral, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList] using ⟨unitCanonical, canonical⟩
      · simpa [numeral, isObjectPattern, isObjectPatternList] using ⟨unitObject, object⟩
      · have here : (numeral count).isWellScopedAt bound.length = true := scopeSafe
        have there : unitAtom.isWellScopedAt bound.length = true := unitScopeSafe
        show (numeral (count + 1)).isWellScopedAt bound.length = true
        simp [numeral, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, here, there]

/-- Every numeral is a closed atom of the probe. -/
theorem numeral_wellSorted (count : Nat) :
    OpenPatternWellSorted language FreeTypeContext.empty [] (.base "Atom") (numeral count) :=
  numeral_wellSorted_in (by decide) (by decide) [] count

/-- **The quotation of a numeral is a closed name of the probe.** -/
theorem quoted_numeral_wellSorted (count : Nat) :
    OpenPatternWellSorted language FreeTypeContext.empty [] (.base "CandidateName")
      (quoted (numeral count)) := by
  obtain ⟨typed, canonical, object, scopeSafe⟩ := numeral_wellSorted count
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact .constructor (rule := quoteConstructor) (by decide)
      (fun bare => by
        have checked := (usesBareCollection?_eq_true_iff _).mpr bare
        revert checked
        decide)
      (.cons trivial rfl typed .nil)
  · simpa [quoted, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
      using canonical
  · simpa [quoted, isObjectPattern, isObjectPatternList] using object
  · have here : (numeral count).isWellScopedAt 0 = true := scopeSafe
    show (quoted (numeral count)).isWellScopedAt 0 = true
    simp [quoted, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, here]

/-- The interface of the closed atoms. -/
def closedAtom : Contexts.Interface := ⟨.base "Atom", []⟩

/-- The interface of the closed names. -/
def closedName : Contexts.Interface := ⟨.base "CandidateName", []⟩

/-! ## Inert data -/

/-- **The numeral atoms are inert data of the probe**, for every evaluator of
its premises: atoms do not reduce there. -/
def probeAtoms (base : BasePremiseEvaluator) :
    (contextTheory base queryFirstCandidatePresentation).InertData Nat where
  interface := closedAtom
  datum := fun count => ⟨numeral count, numeral_wellSorted count⟩
  normal := fun _ next step =>
    probe_static_of_ne_process base (interface := closedAtom) (by decide) _ next step
  apart := fun first second related => by
    have same := language_quoteDropOnly.contract_eq related
    rw [contract_numeral, contract_numeral] at same
    exact numeral_injective same

/-- **The quoted numerals are inert data of the probe**, at the sort of
names. -/
def probeNames (base : BasePremiseEvaluator) :
    (contextTheory base queryFirstCandidatePresentation).InertData Nat where
  interface := closedName
  datum := fun count => ⟨quoted (numeral count), quoted_numeral_wellSorted count⟩
  normal := fun _ next step =>
    probe_static_of_ne_process base (interface := closedName) (by decide) _ next step
  apart := fun first second related => by
    have same := language_quoteDropOnly.contract_eq related
    rw [contract_quoted_numeral, contract_quoted_numeral] at same
    simp only [quoted, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
    exact numeral_injective same

/-! ## The numerals do not exhaust the atoms -/

/-- The dropping of the quoted unit atom, a closed atom. -/
def droppedAtom : Contexts.Term language closedAtom :=
  ⟨dropped (quoted unitAtom), checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **Negative**: an atom of the probe that is no numeral, up to the static
equivalence. -/
theorem droppedAtom_not_numeral (base : BasePremiseEvaluator) (count : Nat) :
    ¬ (termSetoid base language closedAtom).r droppedAtom
      ⟨numeral count, numeral_wellSorted count⟩ := by
  intro related
  have same := language_quoteDropOnly.contract_eq related
  rw [contract_numeral] at same
  cases count with
  | zero => revert same; decide
  | succ count =>
      have heads : head? (contract droppedAtom.1) = head? (numeral (count + 1)) :=
        congrArg head? same
      have left : head? (contract droppedAtom.1) = some "prime-drop" := by decide
      have right : head? (numeral (count + 1)) = some "=" := rfl
      rw [left, right] at heads
      exact absurd heads (by decide)

#print axioms numeral_injective
#print axioms numeral_wellSorted_in
#print axioms numeral_wellSorted
#print axioms probeAtoms
#print axioms probeNames
#print axioms droppedAtom_not_numeral

end Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
