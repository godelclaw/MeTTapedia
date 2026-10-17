import Mettapedia.Logic.HostingStyles.LocatedAtoms.TwoSpaces
import Mettapedia.Logic.HostingStyles.AmbientSpace.BesideRun
import Mettapedia.GSLT.Contexts.TermFamilies

/-!
# The two forms compared: from the members summed over their spaces into located atoms

In the ambient form the space is the index of a family of evaluators; in the
located form it is in the term.  The comparison places an atom of the member
at a space in a run in that space (`locatedOf`).  On the closed atoms of all
members at once this is a map of theories out of the sum of the members read
on their terms (`compareMap`), into the located presentation under any
evaluator.

* **It identifies no two atoms of a member** (`compareMap_reflectsEquations`),
  under every evaluator.
* **On the atoms of terms it is the hosting of located atoms**
  (`locatedOf_atomTerm`): the reading of a term as the run of its atom is the
  reading of the term as its atom, followed by the comparison.
* **On the image of a table it preserves and reflects transitions**, under
  the evaluator of located atoms (`compare_step_iff`): at the space of a list
  of first-order rules with bound right sides, the transitions of the image
  of the atom of a term are the images of the transitions of the atom.
* **Under the matching evaluator it is not hosting**
  (`compareMap_matching_not_hosting`): the image of the atom of
  `choose heads tails` at the empty space has a transition, by a rule of
  another space, and the atom has none at the empty space.

What the located form has that the ambient form lacks:

* **a term whose parts are in two spaces** (`mixedCoins_in_no_member`): the
  application of a run in one space to a run in another is the image of no
  atom of any member; the sum has no context between two spaces
  (`ambientSum_isEmpty_context_of_ne`), and here each part steps by the rules
  of its own space (`pair_termStep_inv`);
* **one candidate for all tables**: the sum is a family, the located
  presentation is one presentation under one evaluator.

What it costs:

* **no linear size** (`located_no_linearSize`), under every evaluator: the
  equation of an application writes the space twice;
* the static equivalence is no longer decided by contraction: the run of a
  term has many spellings (`run_not_alone`), and the evaluator has to read
  through the normal form (`matchingEvaluator_not_respectsStatics`);
* the two equations with a binder are sound for closed spaces only
  (`binder_captures`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.LocatedAtoms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory inst patternVars usesOnly withChoice chooseLeft chooseRight)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList binaryContext)
open Mettapedia.Logic.HostingStyles.AmbientSpace
  (ambient SpaceTerm ambientTheory ambientEvaluator atomTerm listSpace emptySpaceTerm coin
    ambient_terms_subset tokens_run_ambient tokens_contract ambient_quoteDropOnly
    ambient_quoteDropSorted termStep_atomTerm_iff emptyMember_choice_normal wellSorted_of_terms_subset)

variable {base : BasePremiseEvaluator}

/-! ## An atom of a member, located in the space of the member -/

/-- A term of the ambient presentation, as a term of the candidate with
located atoms: its constructors are constructors of that candidate. -/
def inLocated {interface : Contexts.Interface} (term : Contexts.Term ambient interface) :
    Contexts.Term located interface :=
  ⟨term.1, wellSorted_of_terms_subset (large := located)
    (show ∀ rule ∈ ambient.terms, rule ∈ located.terms from ambient_terms_subset) term.2⟩

/-- **An atom of the member at a space, located in that space.** -/
def locatedOf (space : SpaceTerm) (atom : Contexts.Term ambient AtomsReduce.closedAtom) :
    Contexts.Term located AtomsReduce.closedAtom :=
  runTerm (stage := []) (inLocated space) (inLocated atom)

@[simp] theorem locatedOf_val (space : SpaceTerm)
    (atom : Contexts.Term ambient AtomsReduce.closedAtom) :
    (locatedOf space atom).1 = runPattern space.1 atom.1 :=
  rfl

/-- **On the atom of a term, at the space of a list of rules, it is the run
of the atom**: the reading of a term by located atoms is its reading by the
member, followed by the comparison. -/
theorem locatedOf_atomTerm (rules : List Dedukti.RewriteRule) (term : LF.Term) :
    locatedOf (listSpace rules) (atomTerm 0 term) = runAtom rules 0 term :=
  Subtype.ext rfl

/-- One generator of the static equivalence of the ambient presentation is
one generator of that of the candidate with located atoms, in one of the two
directions. -/
theorem contextStep_ambient_located {first second : BasePremiseEvaluator} {left right : Pattern}
    (step : EquationContextStep first ambient left right) :
    EquationContextStep second located left right ∨
      EquationContextStep second located right left := by
  cases step with
  | inContext context generator =>
      rcases ambient_quoteDropOnly.generator generator with rfl | rfl
      · exact .inl (.inContext context (Or.inl (quotedDropped_instance _)))
      · exact .inr (.inContext context (Or.inl (quotedDropped_instance _)))

/-- Terms that the ambient presentation identifies are identified by the
candidate with located atoms. -/
theorem inLocated_related {first second : BasePremiseEvaluator} {interface : Contexts.Interface}
    {left right : Contexts.Term ambient interface}
    (related : (termSetoid first ambient interface).r left right) :
    (termSetoid second located interface).r (inLocated left) (inLocated right) := by
  induction related with
  | rel left right step =>
      rcases contextStep_ambient_located (second := second) step with forward | backward
      · exact .rel _ _ forward
      · exact .symm _ _ (.rel _ _ backward)
  | refl term => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ firstStep secondStep => exact .trans _ _ _ firstStep secondStep

/-! ## The comparison, as a map of theories -/

/-- The members of the family, each on its closed atoms. -/
abbrev memberAtoms : SpaceTerm → GSLT.{0} :=
  fun space => (ambientTheory space).gslt AtomsReduce.closedAtom

/-- **The comparison**: from the members summed over their spaces, read on
their closed atoms, into the candidate with located atoms under an evaluator.
An atom of the member at a space is placed in a run in that space. -/
def compareMap (base : BasePremiseEvaluator) :
    ContextMap (familyTermsAlone memberAtoms) (contextTheory base locatedPresentation) :=
  ContextMap.ofFamilyTerms (family := memberAtoms)
    (target := contextTheory base locatedPresentation) (fun _ => AtomsReduce.closedAtom)
    (fun {space} atom => locatedOf space atom)
    (fun {space} _ _ related =>
      runTerm_related (stage := []) (inLocated space) (inLocated_related related))

/-- The normal form of an atom of the ambient presentation is its
contraction, and has no run. -/
theorem settle_ambient {interface : Contexts.Interface} (term : Contexts.Term ambient interface) :
    settle term.1 = contract term.1 ∧ tokens runLabel (settle term.1) = 0 := by
  have same := settle_eq_contract term.1 (tokens_run_ambient term) term.2.2.1
  exact ⟨same, by
    rw [same, tokens_contract (by decide) (by decide)]
    exact tokens_run_ambient term⟩

/-- **The comparison identifies no two atoms of a member**, under every
evaluator. -/
theorem compareMap_reflectsEquations (base : BasePremiseEvaluator) :
    (compareMap base).ReflectsEquations := by
  intro space first second related
  have same : settle (runPattern (space : SpaceTerm).1
        (first : Contexts.Term ambient AtomsReduce.closedAtom).1) =
      settle (runPattern (space : SpaceTerm).1
        (second : Contexts.Term ambient AtomsReduce.closedAtom).1) :=
    settle_eq_of_related related
  rw [settle_runPattern, settle_runPattern] at same
  have plain := congrArg unlocate same
  rw [unlocate_push _ _ (settle_ambient (interface := AtomsReduce.closedAtom) first).2,
    unlocate_push _ _ (settle_ambient (interface := AtomsReduce.closedAtom) second).2,
    (settle_ambient (interface := AtomsReduce.closedAtom) first).1,
    (settle_ambient (interface := AtomsReduce.closedAtom) second).1] at plain
  exact (ambient_quoteDropOnly.termSetoid_iff ambient_quoteDropSorted).mpr plain

/-! ## On the image of a table -/

/-- A list of rules as the table of a theory with no definition. -/
theorem ofTable_rules (rules : List Dedukti.RewriteRule) (rule : Dedukti.RewriteRule) :
    (Theory.ofTable rules.toFinset).rule rule ↔ rule ∈ rules :=
  List.mem_toFinset

/-- **On the image of a table the comparison preserves and reflects
transitions**, under the evaluator of located atoms: at the space of a list
of first-order rules with bound right sides, the transitions of the image of
the atom of a term are the images of the transitions of the atom. -/
theorem compare_step_iff {rules : List Dedukti.RewriteRule}
    (firstOrder : ∀ rule ∈ rules,
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true)
    (bound : ∀ rule ∈ rules, usesOnly (patternVars rule.lhs) 0 rule.rhs = true) {term : LF.Term}
    {target : Contexts.Term located AtomsReduce.closedAtom} :
    TermStep locatedEvaluator located (locatedOf (listSpace rules) (atomTerm 0 term)) target ↔
      ∃ next : Contexts.Term ambient AtomsReduce.closedAtom,
        (ambientTheory (listSpace rules)).rewrites (atomTerm 0 term) next ∧
          (termSetoid locatedEvaluator located AtomsReduce.closedAtom).r target
            (locatedOf (listSpace rules) next) := by
  rw [locatedOf_atomTerm]
  constructor
  · intro step
    obtain ⟨nextTerm, sourceStep, related⟩ :=
      (runAtom_termStep_iff (depth := 0) firstOrder bound (ofTable_rules rules)
        (fun _ => rfl)).mp step
    exact ⟨atomTerm 0 nextTerm,
      (termStep_atomTerm_iff firstOrder bound (ofTable_rules rules) (fun _ => rfl)
        (depth := 0)).mpr ⟨nextTerm, sourceStep, rfl⟩,
      by rw [locatedOf_atomTerm]; exact related⟩
  · rintro ⟨next, step, related⟩
    obtain ⟨nextTerm, sourceStep, rfl⟩ :=
      (termStep_atomTerm_iff firstOrder bound (ofTable_rules rules) (fun _ => rfl)
        (depth := 0)).mp step
    rw [locatedOf_atomTerm] at related
    exact (runAtom_termStep_iff (depth := 0) firstOrder bound (ofTable_rules rules)
      (fun _ => rfl)).mpr ⟨nextTerm, sourceStep, related⟩

/-! ## Under the matching evaluator -/

/-- **Under the matching evaluator the comparison is not hosting**: the image
of the atom of `choose heads tails` at the empty space has a transition, and
the atom has none at the empty space. -/
theorem compareMap_matching_not_hosting : ¬ (compareMap matchingEvaluator).Hosting := by
  intro hosting
  have step : (contextTheory matchingEvaluator locatedPresentation).rewrites
      ((compareMap matchingEvaluator).term (origin := listSpace []) (atomTerm 0 coin))
      (runAtom [takeAll] 0 (.con "u")) := by
    show TermStep matchingEvaluator located (locatedOf (listSpace []) (atomTerm 0 coin)) _
    rw [locatedOf_atomTerm]
    exact matching_foreign_step
  obtain ⟨next, sourceStep, -⟩ :=
    (compareMap matchingEvaluator).reflectsRewrites_of_transitions hosting.reflects step
  exact emptyMember_choice_normal next sourceStep

/-! ## What the located form has: a term in two spaces -/

/-- **A term whose parts are in two spaces is the image of no atom of any
member.** -/
theorem mixedCoins_in_no_member (base : BasePremiseEvaluator) (space : SpaceTerm)
    (atom : Contexts.Term ambient AtomsReduce.closedAtom) :
    ¬ (termSetoid base located AtomsReduce.closedAtom).r (locatedOf space atom) mixedCoins := by
  intro related
  have same := settle_eq_of_related related
  rw [locatedOf_val, settle_runPattern] at same
  have pair : settle mixedCoins.1 =
      .apply "App" [push (ruleSpace [chooseLeft, chooseRight]) (atomAt 0 coin),
        push (ruleSpace []) (atomAt 0 coin)] := settle_pair _ _ 0 coin coin
  rw [pair] at same
  have clean := tokens_atomAt (counted := runLabel) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) coin 0
  have recognized := located?_push (settle_ambient atom).2 (settle space.1)
  rw [same, located?_app_apart (fun wrong => absurd (ruleSpace_injective wrong) (by decide))
    clean clean] at recognized
  cases recognized

/-! ## What it costs: no linear size -/

/-- The run of an atom in a space, as a context of two holes. -/
def runContext (base : BasePremiseEvaluator) :
    (contextTheory base locatedPresentation).Context
      (fun index : Bool =>
        (⟨.base (bif index then "Atom" else "Space"), []⟩ : Contexts.Interface))
      AtomsReduce.closedAtom :=
  binaryContext locatedPresentation (fun index => bif index then "Atom" else "Space")
    (rule := runAtomConstructor) (firstName := "space") (secondName := "subject")
    (by decide) rfl rfl []

/-- The application of an atom to an atom, as a context of two holes. -/
def appContext (base : BasePremiseEvaluator) :
    (contextTheory base locatedPresentation).Context
      (fun _ : Bool => (⟨.base "Atom", []⟩ : Contexts.Interface)) AtomsReduce.closedAtom :=
  binaryContext locatedPresentation (fun _ => "Atom") (rule := applicationConstructor)
    (firstName := "f") (secondName := "a") (by decide) rfl rfl []

/-- The empty space, as a closed space of the candidate. -/
def emptyLocatedSpace : Contexts.Term located closedSpace := ruleSpaceTerm []

/-- The unit atom, as a closed atom of the candidate. -/
def unitLocatedAtom : Contexts.Term located AtomsReduce.closedAtom :=
  ⟨unitAtom, checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- A space and an atom, as what fills the two holes of a run. -/
def runFilling (space : Contexts.Term located closedSpace)
    (subject : Contexts.Term located AtomsReduce.closedAtom) : (index : Bool) →
      Contexts.Term located
        (⟨.base (bif index then "Atom" else "Space"), []⟩ : Contexts.Interface)
  | false => space
  | true => subject

/-- **The candidate with located atoms has no linear size**, under any
evaluator.  The run of an application writes its space once and the
application of the two runs writes it twice; the two are one term. -/
theorem located_no_linearSize (base : BasePremiseEvaluator) :
    IsEmpty (contextTheory base locatedPresentation).LinearSize := by
  refine ⟨fun sized => ?_⟩
  obtain ⟨runWeight, runAdds⟩ := sized.additive (runContext base)
  obtain ⟨appWeight, appAdds⟩ := sized.additive (appContext base)
  have inside : sized.size ((contextTheory base locatedPresentation).fill (appContext base)
      fun _ => unitLocatedAtom) =
      appWeight + (sized.size unitLocatedAtom + sized.size unitLocatedAtom) := by
    have adds := appAdds fun _ => unitLocatedAtom
    rw [Fintype.sum_bool] at adds
    exact adds
  have outside : sized.size ((contextTheory base locatedPresentation).fill (runContext base)
      (runFilling emptyLocatedSpace ((contextTheory base locatedPresentation).fill
        (appContext base) fun _ => unitLocatedAtom))) =
      runWeight + (sized.size ((contextTheory base locatedPresentation).fill (appContext base)
        fun _ => unitLocatedAtom) + sized.size emptyLocatedSpace) := by
    have adds := runAdds (runFilling emptyLocatedSpace
      ((contextTheory base locatedPresentation).fill (appContext base) fun _ => unitLocatedAtom))
    rw [Fintype.sum_bool] at adds
    exact adds
  have part : sized.size ((contextTheory base locatedPresentation).fill (runContext base)
      (runFilling emptyLocatedSpace unitLocatedAtom)) =
      runWeight + (sized.size unitLocatedAtom + sized.size emptyLocatedSpace) := by
    have adds := runAdds (runFilling emptyLocatedSpace unitLocatedAtom)
    rw [Fintype.sum_bool] at adds
    exact adds
  have twice : sized.size ((contextTheory base locatedPresentation).fill (appContext base)
      fun _ => (contextTheory base locatedPresentation).fill (runContext base)
        (runFilling emptyLocatedSpace unitLocatedAtom)) =
      appWeight + (sized.size ((contextTheory base locatedPresentation).fill (runContext base)
          (runFilling emptyLocatedSpace unitLocatedAtom)) +
        sized.size ((contextTheory base locatedPresentation).fill (runContext base)
          (runFilling emptyLocatedSpace unitLocatedAtom))) := by
    have adds := appAdds fun _ => (contextTheory base locatedPresentation).fill (runContext base)
      (runFilling emptyLocatedSpace unitLocatedAtom)
    rw [Fintype.sum_bool] at adds
    exact adds
  have same : (termSetoid base located AtomsReduce.closedAtom).r
      ((contextTheory base locatedPresentation).fill (runContext base)
        (runFilling emptyLocatedSpace ((contextTheory base locatedPresentation).fill
          (appContext base) fun _ => unitLocatedAtom)))
      ((contextTheory base locatedPresentation).fill (appContext base) fun _ =>
        (contextTheory base locatedPresentation).fill (runContext base)
          (runFilling emptyLocatedSpace unitLocatedAtom)) :=
    related_of_instance (runApplication_instance emptyLocatedSpace.1 unitAtom unitAtom)
  have equal := sized.respects same
  have positive := sized.positive emptyLocatedSpace
  omega

#print axioms inLocated_related
#print axioms compareMap_reflectsEquations
#print axioms locatedOf_atomTerm
#print axioms compare_step_iff
#print axioms compareMap_matching_not_hosting
#print axioms mixedCoins_in_no_member
#print axioms located_no_linearSize

end Mettapedia.Logic.HostingStyles.LocatedAtoms
