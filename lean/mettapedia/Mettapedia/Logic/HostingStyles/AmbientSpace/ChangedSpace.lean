import Mettapedia.Logic.HostingStyles.AmbientSpace.Hosting

/-!
# A changed space: adding an atom to the space

The space is the index of the family, so changing the space is moving from
one member to another.  This module compares the member at a space with the
member at that space with one more stored atom (`addedSpace`).

* The larger space answers what the smaller answers, and what the added atom
  answers (`matchResults_addAtom`).
* **Every step of the member at the smaller space is a step of the member at
  the larger one**, between the same terms, at every interface
  (`addedSpace_steps`).  The terms and the static equivalence are those of the
  one presentation; only the evaluator moved.
* So the identity on terms and on contexts is a map of theories from the
  member at the smaller space to the member at the larger one that is
  faithful and preserves transitions (`enlargeMap`, `enlargeMap_faithful`,
  `enlargeMap_preserves`).
* **The converse fails** (`addedSpace_converse_fails`): with the first rule of
  choice added to the empty space, the atom of `choose heads tails` has a
  transition that it does not have at the empty space.  So that map does not
  reflect transitions, and is not hosting (`enlargeMap_not_hosting`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientSpace

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory chooseLeft patternVars usesOnly)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce

/-! ## A space with one more atom -/

/-- **A space with one more stored atom.** -/
def addedSpace (atom : Contexts.Term ambient AtomsReduce.closedAtom) (space : SpaceTerm) :
    SpaceTerm :=
  ⟨addAtom atom.1 space.1,
    wellSorted_apply_two (lang := ambient) (label := "prime-space-add") (firstName := "atom")
      (secondName := "rest") (by decide) atom.2 space.2⟩

/-- The equation of a rule, as a closed atom of the presentation. -/
def equationTerm (rule : Dedukti.RewriteRule) : Contexts.Term ambient AtomsReduce.closedAtom :=
  ⟨equationOf rule, equationOf_wellSorted_of ambient_carriesAtoms rule⟩

/-- **Positive**: the space of a list of rules with one more rule is the
space of the list with the equation of that rule added. -/
theorem listSpace_cons (rule : Dedukti.RewriteRule) (rules : List Dedukti.RewriteRule) :
    listSpace (rule :: rules) = addedSpace (equationTerm rule) (listSpace rules) :=
  rfl

/-- **Negative**: the empty space is no space with an atom added. -/
theorem emptySpaceTerm_ne_addedSpace (atom : Contexts.Term ambient AtomsReduce.closedAtom)
    (space : SpaceTerm) : emptySpaceTerm ≠ addedSpace atom space := by
  intro same
  have patterns : emptySpace = addAtom atom.1 space.1 := congrArg Subtype.val same
  simp [emptySpace, addAtom] at patterns

theorem contract_addAtom (atom space : Pattern) :
    contract (addAtom atom space) = addAtom (contract atom) (contract space) := by
  rw [addAtom, contract_apply_of_ne (by decide)]
  rfl

/-- **The answers of a space with one more atom**: those of the atom, then
those of the space. -/
theorem matchResults_addAtom (atom space subject : Pattern) :
    matchResults (addAtom atom space) subject =
      atomResults subject atom ++ matchResults space subject := by
  simp [matchResults]

/-- The larger space answers what the smaller answers. -/
theorem matchResults_subset_addAtom (atom space subject : Pattern) {answer : Pattern}
    (found : answer ∈ matchResults (contract space) subject) :
    answer ∈ matchResults (contract (addAtom atom space)) subject := by
  rw [contract_addAtom, matchResults_addAtom]
  exact List.mem_append_right _ found

/-! ## Every step at the smaller space is a step at the larger -/

/-- An evaluator at a space that answers at least what another answers gives
at least its answers to every premise. -/
theorem ambientEvaluator_mono {small large : Pattern}
    (included : ∀ (subject answer : Pattern), answer ∈ matchResults (contract small) subject →
      answer ∈ matchResults (contract large) subject)
    (lang : LanguageDef) (bindings : Bindings) (premise : Premise) :
    ∀ result ∈ ambientEvaluator small lang bindings premise,
      result ∈ ambientEvaluator large lang bindings premise := by
  unfold ambientEvaluator
  split
  · intro result member
    obtain ⟨answer, found, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨answer, included _ _ found, rfl⟩
  · intro result member
    cases member

/-- A raw step at the smaller space is a raw step at the larger. -/
theorem stepAt_addAtom (atom space : Pattern) {fuel : Nat} {source target : Pattern}
    (step : StepAt (ambientEvaluator space) ambient fuel source target) :
    StepAt (ambientEvaluator (addAtom atom space)) ambient fuel source target :=
  StepAt.transport (fun _ member => member)
    (fun _ _ premise _ bindings result answered =>
      ambientEvaluator_mono (fun subject _ found => matchResults_subset_addAtom atom space subject found)
        ambient bindings premise result answered) step

/-- The static equivalence of the presentation is the same under every
evaluator: it is that of quotation and dropping. -/
theorem termSetoid_base_irrelevant {first second : BasePremiseEvaluator}
    {interface : Contexts.Interface} {left right : Contexts.Term ambient interface}
    (related : (termSetoid first ambient interface).r left right) :
    (termSetoid second ambient interface).r left right :=
  (ambient_quoteDropOnly.termSetoid_iff ambient_quoteDropSorted).mpr
    (ambient_quoteDropOnly.contract_eq related)

/-- **Every step of the member at a space is a step of the member at that
space with one more atom**, between the same terms and at every interface. -/
theorem addedSpace_steps (atom : Contexts.Term ambient AtomsReduce.closedAtom) (space : SpaceTerm)
    {interface : Contexts.Interface} {term next : Contexts.Term ambient interface}
    (step : (ambientTheory space).rewrites term next) :
    (ambientTheory (addedSpace atom space)).rewrites term next := by
  obtain ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩ := step
  exact ⟨redex, contractum, termSetoid_base_irrelevant before,
    ⟨fuel, stepAt_addAtom atom.1 space.1 fired⟩, termSetoid_base_irrelevant after⟩

/-! ## The converse fails -/

/-- The first rule of choice alone is first-order with a bound right side. -/
theorem chooseLeft_admitted :
    (∀ rule ∈ [chooseLeft],
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true) ∧
      ∀ rule ∈ [chooseLeft], usesOnly (patternVars rule.lhs) 0 rule.rhs = true := by
  decide

/-- `choose heads tails ⟶ heads`, in the theory of the first rule of choice. -/
theorem chooseLeft_step :
    Dedukti.Step (Theory.ofTable {chooseLeft}) coin (.con "heads") := by
  have root := Dedukti.RootStep.rule (theory := Theory.ofTable {chooseLeft}) (rule := chooseLeft)
    (fun index => if index = 0 then .con "tails" else .con "heads") (Finset.mem_singleton_self _)
  simpa [chooseLeft, Dedukti.choose, coin, Dedukti.inst, Dedukti.instantiate, Dedukti.lift_zero]
    using Dedukti.Step.root root

/-- **The converse fails**: with the first rule of choice added to the empty
space, the atom of `choose heads tails` has a transition to the atom of
`heads`; at the empty space it has no transition. -/
theorem addedSpace_converse_fails :
    (ambientTheory (addedSpace (equationTerm chooseLeft) emptySpaceTerm)).rewrites
        (atomTerm 0 coin) (atomTerm 0 (.con "heads")) ∧
      ∀ target : Contexts.Term ambient AtomsReduce.closedAtom,
        ¬ (ambientTheory emptySpaceTerm).rewrites (atomTerm 0 coin) target := by
  refine ⟨?_, emptyMember_choice_normal⟩
  exact (termStep_atomTerm_iff (rules := [chooseLeft]) chooseLeft_admitted.1 chooseLeft_admitted.2
    (theory := Theory.ofTable {chooseLeft})
    (fun rule => by
      show rule ∈ ({chooseLeft} : Finset Dedukti.RewriteRule) ↔ rule ∈ [chooseLeft]
      simp)
    (fun _ => rfl) (depth := 0)).mpr ⟨_, chooseLeft_step, rfl⟩

/-! ## As a map of theories -/

/-- **From the member at a space to the member at that space with one more
atom**: the identity on interfaces, on terms and on contexts. -/
def enlargeMap (atom : Contexts.Term ambient AtomsReduce.closedAtom) (space : SpaceTerm) :
    ContextMap (ambientTheory space) (ambientTheory (addedSpace atom space)) where
  interface := fun interface => interface
  term := fun term => term
  context := fun context => context
  term_resp := fun related => termSetoid_base_irrelevant related
  equivariant := fun _ _ => Relation.EqvGen.refl _

/-- It identifies no two terms. -/
theorem enlargeMap_faithful (atom : Contexts.Term ambient AtomsReduce.closedAtom)
    (space : SpaceTerm) : (enlargeMap atom space).Faithful :=
  (enlargeMap atom space).faithful_of_reflectsEquations fun related =>
    termSetoid_base_irrelevant related

/-- **It preserves transitions**: adding an atom to the space removes no
step. -/
theorem enlargeMap_preserves (atom : Contexts.Term ambient AtomsReduce.closedAtom)
    (space : SpaceTerm) : (enlargeMap atom space).PreservesTransitions :=
  (enlargeMap atom space).preservesTransitions_of_rewrites fun step =>
    addedSpace_steps atom space step

/-- **It is not hosting**: the larger space has steps that the smaller has
not.  Witness: the first rule of choice added to the empty space. -/
theorem enlargeMap_not_hosting :
    ¬ (enlargeMap (equationTerm chooseLeft) emptySpaceTerm).Hosting := by
  intro hosting
  obtain ⟨next, step, -⟩ :=
    (enlargeMap (equationTerm chooseLeft) emptySpaceTerm).reflectsRewrites_of_transitions
      hosting.reflects (interface := AtomsReduce.closedAtom) (term := atomTerm 0 coin)
      addedSpace_converse_fails.1
  exact addedSpace_converse_fails.2 next step

#print axioms matchResults_addAtom
#print axioms ambientEvaluator_mono
#print axioms stepAt_addAtom
#print axioms termSetoid_base_irrelevant
#print axioms addedSpace_steps
#print axioms addedSpace_converse_fails
#print axioms enlargeMap_faithful
#print axioms enlargeMap_preserves
#print axioms enlargeMap_not_hosting

end Mettapedia.Logic.HostingStyles.AmbientSpace
