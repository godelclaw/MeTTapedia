import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalParts
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Parts at the front door

A language with canonical forms and a listing of the parts of its collections decides splits at the front door: the
verdict of a closed parts region is exact (`decideParts_sound`), so it is a certified decider (`partsDecider`), which
`askWith` consults before the generic search. An equation-free language has one for free (`equationFreeDecider`), its
splits being the cuts of its collections. Certified deciders never disagree (`Decider.agree`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern)

variable {relEnv : RelationEnv} {language : LanguageDef} {fuel : ℕ} {canon : Pattern → Pattern}
  {domain : Pattern → Bool} {presentations : Pattern → List Pattern}

/-- **The parts decider**: for a behavioural formula with parts, the verdict of the parts region grown from the term,
when it closes. -/
def partsDecider (canonical : Canonical relEnv language canon domain)
    (coherent : Coherent relEnv language fuel canon domain presentations)
    (listing : PartsListing relEnv language canon domain) (rounds : ℕ) : Decider relEnv language where
  decide formula term :=
    if formula.behaviouralParts then
      decideParts relEnv language fuel canon domain presentations listing formula term rounds
    else none
  exact := by
    intro formula term answer decided
    by_cases fragment : formula.behaviouralParts = true
    · rw [if_pos fragment] at decided
      exact (decideParts_sound canonical coherent fragment decided).symm
    · rw [if_neg fragment] at decided
      cases decided

/-- **An equation-free language decides splits at the front door**, with the identity as canonical forms and the cuts
of its collections. -/
def equationFreeDecider (free : language.isEquationFree = true) (fuel rounds : ℕ) : Decider relEnv language :=
  partsDecider (fuel := fuel) (presentations := List.singleton) (identity_canonical free) (identity_coherent free)
    (identityParts free) rounds


/-- **Certified deciders never disagree**: where two answer, they give the same verdict. -/
theorem Decider.agree (first second : Decider relEnv language) {formula : Formula 0} {term : Pattern}
    {firstAnswer secondAnswer : Bool} (firstDecided : first.decide formula term = some firstAnswer)
    (secondDecided : second.decide formula term = some secondAnswer) : firstAnswer = secondAnswer := by
  have same := (first.exact firstDecided).symm.trans (second.exact secondDecided)
  cases firstAnswer <;> cases secondAnswer <;> simp_all

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
