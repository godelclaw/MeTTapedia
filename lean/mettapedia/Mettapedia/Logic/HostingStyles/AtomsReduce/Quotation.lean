import Mettapedia.Logic.HostingStyles.AtomsReduce.Statics
import Mettapedia.Logic.HostingStyles.AtomsReduce.Rules
import Mettapedia.Logic.HostingStyles.ContextReadings.PresentedReadings

/-!
# Quotation in the candidate: sealed against reduction, released by dropping

The candidate keeps the equation of the probe,
`prime-quote (prime-drop name) = name`, and adds one rewrite about
quotation: the dropping of a quotation steps to the quoted atom
(`releaseRule`).

* **A quotation is sealed against reduction.**  Every rewrite of the
  candidate is headed by a constructor of atoms (`atomsReduce_headedIn_atom`),
  so no name and no space has a transition (`name_static`, `space_static`):
  the quotation of an atom that reduces does not reduce
  (`quotedRedex_static`).  And no congruence goes beneath a dropping: the only
  step of a dropped quotation, as it is written, is its release
  (`dropped_step_inv`).
* **Dropping releases** (`droppedQuotation_release`).

## What became of the critical pair

In the probe one term has two transitions whose results are apart
(`probe_demand_branches`): the equation gives one name two spellings,
`prime-quote a` and `prime-quote (prime-drop (prime-quote a))`, and the
rewrite of reflected demand reads the atom beneath the quotation.  That
rewrite is not in the candidate (`reflectedDemand_absent`).  The release
reads the atom beneath a quotation too, so **the pair remains, in a form that
joins**:

* every dropped quotation has a transition to its atom and a transition to
  itself (`droppedQuotation_release`, `droppedQuotation_self`);
* for the unit atom the two results are apart (`release_branches`), these are
  the only two (`droppedUnit_reducts`), and the second reaches the first in
  one step: the pair joins (`release_joins`);
* the transition to itself is a cyclic reduction under every evaluator of
  the premises (`release_not_rank`): the release with the equation costs
  termination at every dropped quotation.

## Substitution enters a quotation

Beta is the binder-eliminating instantiation of patterns, which goes beneath
every constructor.  So a quotation is not sealed against substitution: an
abstraction whose body drops a quotation that mentions the bound variable
reduces, by beta and then by release, to the quoted atom with the argument in
place of the variable (`substitution_enters_quotation`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AtomsReduce

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti.Language (betaRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar instantiateBVarAt liftBVars)
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.ContextReadings (rewritesHeadedIn termStep_ofSorts ofSorts)

variable {base : BasePremiseEvaluator}

/-! ## Sealed against reduction -/

/-- **Every rewrite of the candidate is headed by a constructor of atoms.** -/
theorem atomsReduce_headedIn_atom : rewritesHeadedIn atomsReduce ["Atom"] = true := by decide

/-- **Negative**: not every rewrite is headed by a constructor of names. -/
theorem atomsReduce_not_headedIn_name : rewritesHeadedIn atomsReduce ["CandidateName"] = false := by
  decide

/-- **A term that reduces is an atom.** -/
theorem atom_of_termStep {interface : Contexts.Interface}
    {source target : Contexts.Term atomsReduce interface}
    (step : TermStep base atomsReduce source target) : interface.type = .base "Atom" := by
  obtain ⟨sort, listed, type⟩ := termStep_ofSorts atomsReduce_headedIn_atom step
  rw [List.mem_singleton.mp listed] at type
  exact type

/-- **No name has a transition.** -/
theorem name_static {stage : List TypeExpr}
    (term next : Contexts.Term atomsReduce ⟨.base "CandidateName", stage⟩) :
    ¬ TermStep base atomsReduce term next :=
  fun step => absurd (TypeExpr.base.inj (atom_of_termStep step)) (by decide)

/-- **No space has a transition.** -/
theorem space_static {stage : List TypeExpr}
    (term next : Contexts.Term atomsReduce ⟨.base "Space", stage⟩) :
    ¬ TermStep base atomsReduce term next :=
  fun step => absurd (TypeExpr.base.inj (atom_of_termStep step)) (by decide)

theorem quoted_wellSorted {bound : List TypeExpr} {atom : Pattern}
    (sorted : OpenPatternWellSorted atomsReduce FreeTypeContext.empty bound (.base "Atom") atom) :
    OpenPatternWellSorted atomsReduce FreeTypeContext.empty bound (.base "CandidateName")
      (quoted atom) :=
  wellSorted_apply_one (lang := atomsReduce) (label := "prime-quote") (name := "term")
    (by decide) sorted

theorem dropped_wellSorted {bound : List TypeExpr} {name : Pattern}
    (sorted : OpenPatternWellSorted atomsReduce FreeTypeContext.empty bound (.base "CandidateName")
      name) :
    OpenPatternWellSorted atomsReduce FreeTypeContext.empty bound (.base "Atom") (dropped name) :=
  wellSorted_apply_one (lang := atomsReduce) (label := "prime-drop") (name := "name")
    (by decide) sorted

/-- The quotation of an atom, as a name. -/
def quoteTerm {stage : List TypeExpr} (atom : Contexts.Term atomsReduce ⟨.base "Atom", stage⟩) :
    Contexts.Term atomsReduce ⟨.base "CandidateName", stage⟩ :=
  ⟨quoted atom.1, quoted_wellSorted atom.2⟩

/-- The dropping of the quotation of an atom, as an atom. -/
def dropQuoteTerm {stage : List TypeExpr}
    (atom : Contexts.Term atomsReduce ⟨.base "Atom", stage⟩) :
    Contexts.Term atomsReduce ⟨.base "Atom", stage⟩ :=
  ⟨dropped (quoted atom.1), dropped_wellSorted (quoted_wellSorted atom.2)⟩

/-- An application of another constructor matches no dropping. -/
theorem dropped_not_matched {label : String} (other : label ≠ "prime-drop")
    {parameters : List Pattern} {name : Pattern} {bindings : Bindings} :
    bindings ∉ matchPattern (.apply label parameters) (dropped name) := by
  intro matched
  obtain ⟨arguments, shape, -⟩ := eq_apply_of_matched matched
  simp only [dropped, Pattern.apply.injEq] at shape
  exact other shape.1.symm

/-- **No congruence goes beneath a dropping**: the only step of a dropping,
as it is written, is the release of a quotation. -/
theorem dropped_step_inv {name target : Pattern}
    (step : Step base atomsReduce (dropped name) target) :
    name = quoted target := by
  obtain ⟨fuel, bounded⟩ := step
  cases fuel with
  | zero => cases bounded
  | succ fuel =>
      obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ :=
        exists_rule_of_stepAt bounded
      rw [atomsReduce_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      · exact absurd matched (dropped_not_matched (label := "App") (by decide))
      · exact absurd matched (dropped_not_matched (label := "App") (by decide))
      · exact absurd matched (dropped_not_matched (label := "App") (by decide))
      · exact absurd matched (dropped_not_matched (label := "Pi") (by decide))
      · exact absurd matched (dropped_not_matched (label := "Pi") (by decide))
      · exact absurd matched (dropped_not_matched (label := "Lam") (by decide))
      · exact absurd matched (dropped_not_matched (label := "Lam") (by decide))
      · obtain ⟨atom, shape, applied⟩ := release_inv matched premises
        simp only [dropped, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
        rw [applied, shape]
      · exact absurd matched (dropped_not_matched (label := "prime-run") (by decide))
      · exact absurd matched (dropped_not_matched (label := "prime-run") (by decide))
      · exact absurd matched (dropped_not_matched (label := "prime-run") (by decide))
      · exact absurd matched (dropped_not_matched (label := "prime-run") (by decide))
      · exact absurd matched (dropped_not_matched (label := "prime-run") (by decide))
      · exact absurd matched (dropped_not_matched (label := "prime-run") (by decide))
      · exact absurd matched (dropped_not_matched (label := "prime-run") (by decide))
      · exact absurd matched (dropped_not_matched (label := "prime-run") (by decide))

/-! ## Dropping releases, and every dropped quotation steps to itself -/

/-- **Dropping a quotation releases the quoted atom**, under every evaluator. -/
theorem droppedQuotation_release {stage : List TypeExpr}
    (atom : Contexts.Term atomsReduce ⟨.base "Atom", stage⟩) :
    TermStep base atomsReduce (dropQuoteTerm atom) atom :=
  ⟨dropQuoteTerm atom, atom, Relation.EqvGen.refl _,
    ⟨1, step_release (by simp [atomsReduce_rewrites]) atom.1⟩, Relation.EqvGen.refl _⟩

/-- The contraction of a dropping is the dropping of the contraction. -/
theorem contract_dropped (pattern : Pattern) :
    contract (dropped pattern) = dropped (contract pattern) := by
  rw [dropped, contract_apply_of_ne (by decide)]
  rfl

/-- The contraction of a quotation: the contraction at the root of the
quotation of the contraction. -/
theorem contract_quoted (pattern : Pattern) :
    contract (quoted pattern) = contractRoot "prime-quote" [contract pattern] := by
  rw [quoted, contract, contractList_eq_map]
  rfl

/-- A dropped quotation and the dropped quotation of it have one
contraction. -/
theorem contract_dropQuote_dropQuote (atom : Pattern) :
    contract (dropped (quoted (dropped (quoted atom)))) = contract (dropped (quoted atom)) := by
  rw [contract_dropped, contract_quoted_dropped, contract_dropped]

/-- **Every dropped quotation has a transition to itself**, under every
evaluator: the equation writes it as the dropped quotation of itself, which
the release steps back to it. -/
theorem droppedQuotation_self {stage : List TypeExpr}
    (atom : Contexts.Term atomsReduce ⟨.base "Atom", stage⟩) :
    TermStep base atomsReduce (dropQuoteTerm atom) (dropQuoteTerm atom) :=
  ⟨dropQuoteTerm (dropQuoteTerm atom), dropQuoteTerm atom,
    (atomsReduce_quoteDropOnly.termSetoid_iff atomsReduce_quoteDropSorted).mpr
      (contract_dropQuote_dropQuote atom.1).symm,
    ⟨1, step_release (by simp [atomsReduce_rewrites]) (dropped (quoted atom.1))⟩,
    Relation.EqvGen.refl _⟩

/-! ## The pair, at the unit atom -/

/-- The unit atom, as a closed atom of the candidate. -/
def unitTerm : Contexts.Term atomsReduce closedAtom :=
  ⟨unitAtom, checkOpenPatternWellSorted_sound (by decide +kernel)⟩

theorem dropQuoteTerm_unit : dropQuoteTerm unitTerm = droppedUnit := rfl

/-- **The quotation of an atom that reduces does not reduce**: the dropped
quotation of the unit atom has a transition, and its quotation has none. -/
theorem quotedRedex_static (base : BasePremiseEvaluator)
    (next : Contexts.Term atomsReduce ⟨.base "CandidateName", []⟩) :
    TermStep base atomsReduce droppedUnit unitTerm ∧
      ¬ TermStep base atomsReduce (quoteTerm droppedUnit) next :=
  ⟨droppedQuotation_release unitTerm, name_static _ _⟩

/-- **The critical pair remains**: the dropped quotation of the unit atom has
a transition to the unit atom and a transition to itself, and the two results
are apart, under every evaluator of the premises. -/
theorem release_branches (base : BasePremiseEvaluator) :
    TermStep base atomsReduce droppedUnit unitTerm ∧
      TermStep base atomsReduce droppedUnit droppedUnit ∧
        ¬ (termSetoid base atomsReduce closedAtom).r unitTerm droppedUnit :=
  ⟨droppedQuotation_release unitTerm, droppedQuotation_self unitTerm, fun related =>
    absurd (atomsReduce_quoteDropOnly.contract_eq related) (by decide)⟩

/-- **The pair joins**: the second result has a transition to the first. -/
theorem release_joins (base : BasePremiseEvaluator) :
    ∃ common : Contexts.Term atomsReduce closedAtom,
      Relation.ReflTransGen (TermStep base atomsReduce) unitTerm common ∧
        Relation.ReflTransGen (TermStep base atomsReduce) droppedUnit common :=
  ⟨unitTerm, .refl, .single (droppedQuotation_release unitTerm)⟩

/-- **These are its only two transitions**, up to the static equivalence. -/
theorem droppedUnit_reducts {target : Contexts.Term atomsReduce closedAtom}
    (step : TermStep base atomsReduce droppedUnit target) :
    (termSetoid base atomsReduce closedAtom).r target unitTerm ∨
      (termSetoid base atomsReduce closedAtom).r target droppedUnit := by
  obtain ⟨redex, contractum, before, fired, after⟩ := step
  have same : contract (dropped (quoted unitAtom)) = contract redex.1 :=
    atomsReduce_quoteDropOnly.contract_eq before
  have class_ : contract (dropped (quoted unitAtom)) = dropped (quoted unitAtom) := by decide
  rw [class_] at same
  obtain ⟨rule, member, _, initial, final, matched, premises, applied⟩ := exists_rule_of_step fired
  have headed : ∃ name, redex.1 = dropped name := by
    rw [atomsReduce_rewrites] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    have other : ∀ {label : String} {parameters : List Pattern}, label ≠ "prime-quote" →
        label ≠ "prime-drop" → initial ∈ matchPattern (.apply label parameters) redex.1 → False := by
      intro label parameters notQuote notDrop found
      have head := head?_contract (head?_of_matched found) notQuote
      rw [← same] at head
      exact notDrop (Option.some.inj head).symm
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact (other (label := "App") (by decide) (by decide) matched).elim
    · exact (other (label := "App") (by decide) (by decide) matched).elim
    · exact (other (label := "App") (by decide) (by decide) matched).elim
    · exact (other (label := "Pi") (by decide) (by decide) matched).elim
    · exact (other (label := "Pi") (by decide) (by decide) matched).elim
    · exact (other (label := "Lam") (by decide) (by decide) matched).elim
    · exact (other (label := "Lam") (by decide) (by decide) matched).elim
    · obtain ⟨atom, shape, -⟩ := mem_matchPattern_releaseLeft matched
      exact ⟨quoted atom, shape⟩
    · exact (other (label := "prime-run") (by decide) (by decide) matched).elim
    · exact (other (label := "prime-run") (by decide) (by decide) matched).elim
    · exact (other (label := "prime-run") (by decide) (by decide) matched).elim
    · exact (other (label := "prime-run") (by decide) (by decide) matched).elim
    · exact (other (label := "prime-run") (by decide) (by decide) matched).elim
    · exact (other (label := "prime-run") (by decide) (by decide) matched).elim
    · exact (other (label := "prime-run") (by decide) (by decide) matched).elim
    · exact (other (label := "prime-run") (by decide) (by decide) matched).elim
  obtain ⟨name, redexShape⟩ := headed
  rw [redexShape] at fired same
  have released := dropped_step_inv fired
  rw [released, contract_dropped] at same
  have names : quoted unitAtom = contract (quoted contractum.1) := by
    simpa [dropped] using same
  have root : contractRoot "prime-quote" [contract contractum.1] = quoted unitAtom := by
    rw [names, contract_quoted]
  have targetClass : contract target.1 = contract contractum.1 :=
    (atomsReduce_quoteDropOnly.contract_eq after).symm
  rcases contractRoot_quote_cases (contract contractum.1) with ⟨inner, isDrop, value⟩ | plain
  · refine .inr ((atomsReduce_quoteDropOnly.termSetoid_iff atomsReduce_quoteDropSorted).mpr ?_)
    rw [targetClass, isDrop, ← value, root]
    exact class_.symm
  · refine .inl ((atomsReduce_quoteDropOnly.termSetoid_iff atomsReduce_quoteDropSorted).mpr ?_)
    rw [plain] at root
    simp only [quoted, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at root
    rw [targetClass, root]
    decide

/-- **The transition of a dropped quotation to itself is a cyclic reduction
under every evaluator of the premises**: with the equation and the release
the candidate has no rank, whatever answers its run premise. -/
theorem release_not_rank (base : BasePremiseEvaluator) :
    IsEmpty (contextTheory base atomsReducePresentation).Rank :=
  ⟨fun ranked => ranked.not_cycle
    (.single (droppedQuotation_self (base := base) unitTerm))⟩

/-- **The rewrite of reflected demand, the second half of the pair of the
probe, is not in the candidate**; the release is. -/
theorem reflectedDemand_absent :
    reflectedDemandRewrite.name ∉ atomsReduce.rewrites.map (·.name) ∧
      releaseRule ∈ atomsReduce.rewrites := by
  constructor
  · decide
  · simp [atomsReduce_rewrites]

/-! ## Substitution enters a quotation -/

/-- `(λ x. * @ (f x)) payload`, with `f` and the payload two symbols and the
domain a third: an abstraction whose body drops a quotation that mentions the
bound variable, applied. -/
def quotingRedex : Contexts.Term atomsReduce closedAtom :=
  ⟨.apply "App" [.apply "Lam" [symbolAtom 0,
      .lambda none (dropped (quoted (.apply "App" [symbolAtom 1, .bvar 0])))], symbolAtom 2],
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- `* @ (f payload)`. -/
def quotingContractum : Contexts.Term atomsReduce closedAtom :=
  ⟨dropped (quoted (.apply "App" [symbolAtom 1, symbolAtom 2])),
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- `(f payload)`. -/
def quotingResult : Contexts.Term atomsReduce closedAtom :=
  ⟨.apply "App" [symbolAtom 1, symbolAtom 2], checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **Beta substitutes beneath a quotation**, and the release then yields the
quoted atom with the argument in place of the bound variable: a quotation is
sealed against reduction and not against substitution. -/
theorem substitution_enters_quotation (base : BasePremiseEvaluator) :
    TermStep base atomsReduce quotingRedex quotingContractum ∧
      TermStep base atomsReduce quotingContractum quotingResult := by
  refine ⟨⟨quotingRedex, quotingContractum, Relation.EqvGen.refl _, ⟨1, ?_⟩,
    Relation.EqvGen.refl _⟩, droppedQuotation_release quotingResult⟩
  have step := step_beta (base := base) (lang := atomsReduce) (by simp [atomsReduce_rewrites])
    (symbolAtom 0) (dropped (quoted (.apply "App" [symbolAtom 1, .bvar 0]))) (symbolAtom 2) none
  have instantiated : instantiateBVar (symbolAtom 2)
      (dropped (quoted (.apply "App" [symbolAtom 1, .bvar 0]))) =
      dropped (quoted (.apply "App" [symbolAtom 1, symbolAtom 2])) := by
    simp [instantiateBVar, instantiateBVarAt, dropped, quoted, symbolAtom,
      instantiateBVarAt_numeral, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
  rw [instantiated] at step
  exact step

#print axioms atomsReduce_headedIn_atom
#print axioms name_static
#print axioms space_static
#print axioms quotedRedex_static
#print axioms dropped_step_inv
#print axioms droppedQuotation_release
#print axioms droppedQuotation_self
#print axioms release_branches
#print axioms release_joins
#print axioms droppedUnit_reducts
#print axioms release_not_rank
#print axioms reflectedDemand_absent
#print axioms substitution_enters_quotation

end Mettapedia.Logic.HostingStyles.AtomsReduce
