import Mathlib.Tactic
import Mettapedia.GraphTheory.FourColor.GoertzelV24CurvatureScope

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DependencyLedger

/-- The mathematical quantifier pattern of the v24 Short Strand Conjecture:
some universal reach bound works for every relevant locked configuration. -/
def ShortStrandConjecture
    (Configuration : Type*)
    (isLockedNormalFormDeepDesert : Configuration → Prop)
    (singletonStrandReach : Configuration → Nat) : Prop :=
  ∃ rho : Nat, ∀ c : Configuration,
    isLockedNormalFormDeepDesert c → singletonStrandReach c <= rho

/-- A numerical datum reported by an external search. It is not a
kernel-checked graph construction. -/
structure ShortStrandExternalEvidenceDatum where
  goldbergP : Nat
  goldbergQ : Nat
  strandEdgeCount : Nat
  singletonStrandReach : Nat
  previouslyProposedBound : Nat
  unlockSwitchCount : Nat
  measuredUnlockRadius : Nat
  deriving DecidableEq, Repr

/-- The GP(8,0) hairpin datum reported in the same-week addendum to
"Deserts, Pivots, and the Necklace". -/
def gp80HairpinEvidence : ShortStrandExternalEvidenceDatum where
  goldbergP := 8
  goldbergQ := 0
  strandEdgeCount := 688
  singletonStrandReach := 40
  previouslyProposedBound := 4
  unlockSwitchCount := 15
  measuredUnlockRadius := 8

/-- The reported reach-40 strand refutes the previously proposed empirical
bound `rho = 4`. -/
theorem gp80HairpinEvidence_not_within_proposedBound :
    ¬ gp80HairpinEvidence.singletonStrandReach <=
      gp80HairpinEvidence.previouslyProposedBound := by
  decide

/-- Vocabulary for the final Trail Completability statement. -/
structure TrailCompletabilityVocabulary where
  Trail : Type*
  colorable : Trail → Prop
  completableByBetweenRegionMoves : Trail → Prop

/-- The v24 route's final theorem statement: every colorable trail is
completable using between-region moves. -/
def TrailCompletability (v : TrailCompletabilityVocabulary) : Prop :=
  ∀ trail : v.Trail, v.colorable trail →
    v.completableByBetweenRegionMoves trail

end GoertzelV24DependencyLedger

end Mettapedia.GraphTheory.FourColor
