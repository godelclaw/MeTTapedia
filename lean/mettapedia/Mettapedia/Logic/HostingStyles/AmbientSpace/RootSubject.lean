import Mettapedia.Logic.HostingStyles.AmbientSpace.Hosting

/-!
# The root step of the ambient presentation types no subject

The rewrite of the root step of the ambient presentation is
`AmbientStep(subject, answer) ⊢ subject ~> answer`.  Its left side is a
variable: it matches a pattern of every sort, and the type that the rule
declares for `subject` is not read when the rule fires.  In the candidate in
which atoms reduce the left side of the root step is a run, which is an atom,
and neither a name nor a space has a transition (`name_static`,
`space_static`).

* At the space of the rule `x ⟶ x` every pattern is an answer for itself
  (`identity_answers`).
* **Positive witness** (`ambient_space_steps`): at that space the empty
  space, a term of sort `Space`, has a transition to itself.  So in the
  ambient presentation as it is written a space may have a transition.

The theories that a member hosts are read on atoms of λΠ terms, at the
interfaces of atoms; this defect is at the interfaces of the other sorts.  A
presentation that excludes it would give the root step a left side that only
an atom matches, which the constructors of this presentation do not provide
without a constructor that marks the subject.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientSpace

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory patternVars usesOnly)
open Mettapedia.GSLT.Dedukti.Language (metaName)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce

/-- The rule `x ⟶ x`. -/
def identityRule : Dedukti.RewriteRule := ⟨.var 0, .var 0⟩

/-- It is first-order, and its right side mentions only the variable of its
left side. -/
theorem identityRule_admitted :
    (∀ rule ∈ [identityRule],
      Dedukti.binderFree rule.lhs = true ∧ Dedukti.binderFree rule.rhs = true) ∧
      ∀ rule ∈ [identityRule], usesOnly (patternVars rule.lhs) 0 rule.rhs = true := by
  decide

/-- **At the space of the rule `x ⟶ x` every pattern is an answer for
itself.** -/
theorem identity_answers (subject : Pattern) :
    subject ∈ matchResults (ruleSpace [identityRule]) subject := by
  refine (mem_matchResults_ruleSpace identityRule_admitted.1).mpr
    ⟨identityRule, List.mem_singleton.mpr rfl, [(metaName 0, subject)], ?_, ?_⟩
  · show _ ∈ matchPattern (asRule (atomAt 0 (.var 0))) subject
    rw [atomAt_freeVariable, asRule_variableAtom]
    simp [matchPattern]
  · show subject = applyBindings _ (asRule (atomAt 0 (.var 0)))
    rw [atomAt_freeVariable, asRule_variableAtom]
    simp [applyBindings]

/-- **Negative**: the empty space answers nothing, for any subject. -/
theorem emptySpace_answers_nothing (subject : Pattern) :
    matchResults (ruleSpace []) subject = [] :=
  matchResults_emptySpace subject

/-- **A space has a transition**: at the space of the rule `x ⟶ x` the empty
space, a term of sort `Space`, steps to itself.  The root step types no
subject. -/
theorem ambient_space_steps :
    (ambientTheory (listSpace [identityRule])).rewrites (interface := closedSpace) emptySpaceTerm
      emptySpaceTerm := by
  refine ⟨emptySpaceTerm, emptySpaceTerm, .refl _,
    ⟨1, step_root (lang := ambient) (by simp [ambient_rewrites]) ?_⟩, .refl _⟩
  show emptySpace ∈ matchResults (contract (ruleSpace [identityRule])) (contract emptySpace)
  have fixed : contract emptySpace = emptySpace := by decide
  rw [contract_ruleSpace, fixed]
  exact identity_answers emptySpace

#print axioms identity_answers
#print axioms ambient_space_steps

end Mettapedia.Logic.HostingStyles.AmbientSpace
