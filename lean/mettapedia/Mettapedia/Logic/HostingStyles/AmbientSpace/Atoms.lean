import Mettapedia.Logic.HostingStyles.AmbientSpace.Language
import Mettapedia.Logic.HostingStyles.AtomsReduce.Summary

/-!
# The atoms of λΠ terms and the spaces of rules, in every candidate that declares their constructors

The reading of a λΠ term as an atom (`atomAt`) and of a list of rules as a
space (`ruleSpace`) uses nine constructors: the equation constructor, the
unit atom, the two constructors of a space, the variable atom, the symbol,
application, abstraction and product.  A language that declares them as the
candidate does (`CarriesAtoms`) has those atoms and those spaces as terms
(`atomAt_wellSorted_of`, `ruleSpace_wellSorted_of`).  The statements about
`atomsReduce` of the module `AtomsReduce.Encoding` are the instance at that
language; they are stated again here because the ambient presentation and
the presentation with located atoms are other languages.

For the ambient presentation the module then gives

* the atom of a term and the space of a list of rules as terms (`atomTerm`,
  `listSpace`, `tableSpace`);
* **the atom of a term is the only term of its class** of the static
  equivalence (`eq_atomTerm_of_related`): names are taken by dropping alone
  (`ambient_namesOnlyDropped`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientSpace

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (RuleTable)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

/-! ## Languages that declare the constructors of atoms and spaces -/

/-- The nine constructors that the atoms of λΠ terms and the spaces of rules
are built from, as the candidate declares them. -/
def atomConstructors : List GrammarRule :=
  [MeTTaZero.equationConstructor, unitConstructor, emptySpaceConstructor, addAtomConstructor,
    variableConstructor, symbolConstructor, applicationConstructor, abstractionConstructor,
    productConstructor]

/-- **A language carries the atoms of λΠ terms and the spaces of rules**: it
declares their nine constructors as the candidate does. -/
def CarriesAtoms (lang : LanguageDef) : Prop := ∀ rule ∈ atomConstructors, rule ∈ lang.terms

/-- **Positive**: the ambient presentation. -/
theorem ambient_carriesAtoms : CarriesAtoms ambient := by
  unfold CarriesAtoms
  decide

/-- **Positive**: the candidate with a run. -/
theorem atomsReduce_carriesAtoms : CarriesAtoms atomsReduce := by
  unfold CarriesAtoms
  decide

/-- **Negative**: the probe with a space that is a term has no application. -/
theorem probeWithSpace_not_carriesAtoms : ¬ CarriesAtoms probeWithSpace := by
  unfold CarriesAtoms
  decide

variable {lang : LanguageDef}

/-- A numeral is an atom, beneath any binders. -/
theorem numeral_wellSorted_of (carries : CarriesAtoms lang) (bound : List TypeExpr) (count : Nat) :
    OpenPatternWellSorted lang FreeTypeContext.empty bound (.base "Atom") (numeral count) :=
  numeral_wellSorted_in (carries _ (by decide)) (carries _ (by decide)) bound count

/-- A symbol is an atom, beneath any binders. -/
theorem symbolAtom_wellSorted_of (carries : CarriesAtoms lang) (bound : List TypeExpr)
    (code : Nat) :
    OpenPatternWellSorted lang FreeTypeContext.empty bound (.base "Atom") (symbolAtom code) :=
  wellSorted_apply_one (lang := lang) (label := "prime-symbol") (name := "index")
    (carries symbolConstructor (by decide)) (numeral_wellSorted_of carries bound code)

/-- **Every λΠ term is an atom** of a language that carries atoms, at the
stage of the binders it is beneath. -/
theorem atomAt_wellSorted_of (carries : CarriesAtoms lang) (term : LF.Term) :
    ∀ depth : Nat, OpenPatternWellSorted lang FreeTypeContext.empty
      (List.replicate depth (.base "Atom")) (.base "Atom") (atomAt depth term) := by
  induction term with
  | var index =>
      intro depth
      by_cases below : index < depth
      · rw [atomAt_var_of_lt below]
        refine ⟨.bvar (by simp [below]), by simp [Pattern.hasCanonicalBinderMetadata],
          by simp [isObjectPattern], ?_⟩
        show (Pattern.bvar index).isWellScopedAt (List.replicate depth (TypeExpr.base "Atom")).length =
          true
        simp [Pattern.isWellScopedAt, below]
      · rw [atomAt_var_of_le (Nat.le_of_not_lt below)]
        exact wellSorted_apply_one (lang := lang) (label := "prime-variable")
          (name := "index") (carries variableConstructor (by decide))
          (numeral_wellSorted_of carries _ _)
  | srt sort =>
      intro depth
      rw [atomAt_srt]
      exact symbolAtom_wellSorted_of carries _ _
  | con name => intro depth; exact symbolAtom_wellSorted_of carries _ _
  | app function argument ihFunction ihArgument =>
      intro depth
      exact wellSorted_apply_two (lang := lang) (label := "App") (firstName := "f")
        (secondName := "a") (carries applicationConstructor (by decide)) (ihFunction depth)
        (ihArgument depth)
  | lam domain body ihDomain ihBody =>
      intro depth
      have bodySorted := ihBody (depth + 1)
      rw [List.replicate_succ] at bodySorted
      exact wellSorted_apply_binder (lang := lang) (label := "Lam") (name := "a")
        (binder := "x") (bodyName := "body") (carries abstractionConstructor (by decide))
        (ihDomain depth) bodySorted
  | pi domain body ihDomain ihBody =>
      intro depth
      have bodySorted := ihBody (depth + 1)
      rw [List.replicate_succ] at bodySorted
      exact wellSorted_apply_binder (lang := lang) (label := "Pi") (name := "a")
        (binder := "x") (bodyName := "body") (carries productConstructor (by decide))
        (ihDomain depth) bodySorted

/-- The space of a list of atoms is a space, beneath any binders. -/
theorem spaceOfAtoms_wellSorted_of (carries : CarriesAtoms lang) {bound : List TypeExpr} :
    ∀ {atoms : List Pattern},
      (∀ atom ∈ atoms, OpenPatternWellSorted lang FreeTypeContext.empty bound (.base "Atom") atom) →
      OpenPatternWellSorted lang FreeTypeContext.empty bound (.base "Space") (spaceOfAtoms atoms)
  | [], _ =>
      wellSorted_apply_zero (lang := lang) (label := "prime-space-empty")
        (carries emptySpaceConstructor (by decide))
  | atom :: _, sorted =>
      wellSorted_apply_two (lang := lang) (label := "prime-space-add") (firstName := "atom")
        (secondName := "rest") (carries addAtomConstructor (by decide))
        (sorted atom (List.mem_cons_self ..))
        (spaceOfAtoms_wellSorted_of carries fun other member =>
          sorted other (List.mem_cons_of_mem _ member))

/-- The equation of a rule is an atom. -/
theorem equationOf_wellSorted_of (carries : CarriesAtoms lang) (rule : Dedukti.RewriteRule) :
    OpenPatternWellSorted lang FreeTypeContext.empty [] (.base "Atom") (equationOf rule) :=
  wellSorted_apply_two (lang := lang) (label := "=") (firstName := "left")
    (secondName := "right") (carries MeTTaZero.equationConstructor (by decide))
    (atomAt_wellSorted_of carries rule.lhs 0) (atomAt_wellSorted_of carries rule.rhs 0)

/-- **The space of a list of rules is a closed space** of a language that
carries atoms. -/
theorem ruleSpace_wellSorted_of (carries : CarriesAtoms lang) (rules : List Dedukti.RewriteRule) :
    OpenPatternWellSorted lang FreeTypeContext.empty [] (.base "Space") (ruleSpace rules) :=
  spaceOfAtoms_wellSorted_of carries fun atom member => by
    obtain ⟨rule, -, rfl⟩ := List.mem_map.mp member
    exact equationOf_wellSorted_of carries rule

/-! ## The atoms and the spaces of the ambient presentation -/

/-- **The atom of a term**, as a term of the ambient presentation at the
stage of `depth` binders. -/
def atomTerm (depth : Nat) (term : LF.Term) : Contexts.Term ambient (atomInterface depth) :=
  ⟨atomAt depth term, atomAt_wellSorted_of ambient_carriesAtoms term depth⟩

@[simp] theorem atomTerm_val (depth : Nat) (term : LF.Term) :
    (atomTerm depth term).1 = atomAt depth term :=
  rfl

theorem atomTerm_injective (depth : Nat) : Function.Injective (atomTerm depth) :=
  fun _ _ same => atomAt_injective depth (congrArg Subtype.val same)

/-- **The space of a list of rules**, as a space of the candidate. -/
def listSpace (rules : List Dedukti.RewriteRule) : SpaceTerm :=
  ⟨ruleSpace rules, ruleSpace_wellSorted_of ambient_carriesAtoms rules⟩

@[simp] theorem listSpace_val (rules : List Dedukti.RewriteRule) :
    (listSpace rules).1 = ruleSpace rules :=
  rfl

/-- **The space of a table.**  A table is a finite set; its space stores its
rules in one order. -/
noncomputable def tableSpace (table : RuleTable) : SpaceTerm := listSpace table.toList

/-- The space of no rule is the empty space. -/
theorem listSpace_nil : listSpace [] = emptySpaceTerm := rfl

/-- The space of a list of rules determines the list. -/
theorem listSpace_injective : Function.Injective listSpace :=
  fun _ _ same => ruleSpace_injective (congrArg Subtype.val same)

/-! ## Names are taken by dropping alone -/

/-- **In the ambient presentation a name is taken by dropping and by nothing
else**, among the constructors of atoms and of spaces. -/
theorem ambient_namesOnlyDropped : NamesOnlyDropped ambient unquotedSorts := by
  intro rule member category
  have listed : rule ∈
      [MeTTaZero.equationConstructor, unitConstructor, quoteConstructor, dropConstructor,
        emptySpaceConstructor, addAtomConstructor, variableConstructor, symbolConstructor,
        applicationConstructor, abstractionConstructor, productConstructor] :=
    member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

/-- **A term of the ambient presentation, at a type of atoms or spaces, that
the static equivalence identifies with a pattern without quotation and
dropping is that pattern.** -/
theorem eq_of_related_of_dropFree {base : BasePremiseEvaluator} {interface : Contexts.Interface}
    {term image : Contexts.Term ambient interface}
    (inSorts : resultIn unquotedSorts interface.type = true)
    (fixed : contract image.1 = image.1) (dropFree : tokens dropLabel image.1 = 0)
    (related : (termSetoid base ambient interface).r image term) : term = image := by
  apply Subtype.ext
  have same : contract term.1 = image.1 :=
    (ambient_quoteDropOnly.contract_eq related).symm.trans fixed
  rw [← same]
  exact (contract_of_dropFree ambient_namesOnlyDropped ambient_quoteDropSorted term.2.1 inSorts
    term.2.2.2.1 (by rw [same]; exact dropFree)).symm

/-- **The atom of a term is the only term of its class.** -/
theorem eq_atomTerm_of_related {base : BasePremiseEvaluator} {depth : Nat} {term : LF.Term}
    {other : Contexts.Term ambient (atomInterface depth)}
    (related : (termSetoid base ambient (atomInterface depth)).r (atomTerm depth term) other) :
    other = atomTerm depth term :=
  eq_of_related_of_dropFree (show resultIn unquotedSorts (.base "Atom") = true by decide)
    (contract_atomAt term depth) (tokens_drop_atomAt term depth) related

/-- **Negative**: with a dropping the static equivalence of the ambient
presentation is not identity.  A dropped quotation has two spellings. -/
theorem ambient_droppedQuotation_spellings (base : BasePremiseEvaluator) :
    ∃ first second : Contexts.Term ambient AtomsReduce.closedAtom,
      (termSetoid base ambient AtomsReduce.closedAtom).r first second ∧ first ≠ second :=
  ⟨⟨dropped (quoted unitAtom), checkOpenPatternWellSorted_sound (by decide +kernel)⟩,
    ⟨dropped (quoted (dropped (quoted unitAtom))),
      checkOpenPatternWellSorted_sound (by decide +kernel)⟩,
    (ambient_quoteDropOnly.termSetoid_iff ambient_quoteDropSorted).mpr (by decide),
    fun same => absurd (congrArg Subtype.val same) (by decide)⟩

#print axioms ambient_carriesAtoms
#print axioms probeWithSpace_not_carriesAtoms
#print axioms atomAt_wellSorted_of
#print axioms ruleSpace_wellSorted_of
#print axioms ambient_namesOnlyDropped
#print axioms eq_of_related_of_dropFree
#print axioms eq_atomTerm_of_related
#print axioms ambient_droppedQuotation_spellings

end Mettapedia.Logic.HostingStyles.AmbientSpace
