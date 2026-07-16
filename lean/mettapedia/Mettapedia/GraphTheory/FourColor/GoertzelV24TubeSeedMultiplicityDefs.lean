import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeSeed

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer

/-- A completely computed one-ring routing test. The proposed terminal
assignment is data; every remaining clause is evaluated from the source
colors, the five split choices, and reachability in the twenty-edge ring
graph. -/
def IsFullyRoutedTubeRingChoice
    (source : TubeFrontierState) (choice : TubeRingChoice)
    (terminal : Fin 4 -> Fin 5) : Prop :=
  source.Valid ∧
  choice.Valid source ∧
  Function.Injective terminal ∧
  (∀ position, IsTracked (newColor source choice position) ↔
    ∃ index, terminal index = position) ∧
  (∀ left right,
    trackedRingReachable source choice
      (.old (source.terminal left)) (.old (source.terminal right)) = true ↔
      left = right) ∧
  ∀ index position,
    trackedRingReachable source choice
      (.old (source.terminal index)) (.new position) = true ↔
      terminal index = position
  deriving Decidable

def tubeFrontierPositions : List (Fin 5) := [0, 1, 2, 3, 4]

/-- The first output position reachable from a named input terminal. The
default is used only when no output is reachable; the fully-routed predicate
below then fails its exact reachability clauses. -/
def computedRoutedTerminal
    (source : TubeFrontierState) (choice : TubeRingChoice)
    (index : Fin 4) : Fin 5 :=
  ((tubeFrontierPositions.find? fun position =>
    trackedRingReachable source choice
      (.old (source.terminal index)) (.new position))).getD 0

/-- A five-bit ring choice is fully routed when its computed two-color
support carries all four named input germs to four distinct output edges. -/
def TubeRingChoice.FullyRouted
    (source : TubeFrontierState) (choice : TubeRingChoice) : Prop :=
  IsFullyRoutedTubeRingChoice source choice
    (computedRoutedTerminal source choice)
  deriving Decidable

theorem isFullyRoutedTubeRingChoice_of_successor
    {source target : TubeFrontierState} {choice : TubeRingChoice}
    (hsuccessor : IsTubeRingSuccessor source target choice) :
    IsFullyRoutedTubeRingChoice source choice target.terminal := by
  refine ⟨hsuccessor.1, hsuccessor.2.1, hsuccessor.2.2.1.1, ?_,
    hsuccessor.2.2.2.2.1, hsuccessor.2.2.2.2.2⟩
  intro position
  rw [← hsuccessor.2.2.2.1 position]
  exact hsuccessor.2.2.1.2 position

set_option maxHeartbeats 2000000 in
theorem computedRoutedTerminal_eq_of_successor
    {source target : TubeFrontierState} {choice : TubeRingChoice}
    (hsuccessor : IsTubeRingSuccessor source target choice) :
    computedRoutedTerminal source choice = target.terminal := by
  funext index
  let candidates : List (Fin 5) := tubeFrontierPositions
  let reaches : Fin 5 -> Bool := fun position =>
    trackedRingReachable source choice
      (.old (source.terminal index)) (.new position)
  have htarget : reaches (target.terminal index) = true :=
    (hsuccessor.2.2.2.2.2 index (target.terminal index)).2 rfl
  have hmem : target.terminal index ∈ candidates := by
    simp only [candidates, tubeFrontierPositions, List.mem_cons,
      List.not_mem_nil, or_false]
    omega
  have hnotNone : List.find? reaches candidates ≠ none := by
    intro hnone
    have hall := (List.find?_eq_none.mp hnone)
      (target.terminal index) hmem
    exact hall htarget
  cases hfind : List.find? reaches candidates with
  | none => exact False.elim (hnotNone hfind)
  | some found =>
      have hfound : reaches found = true := List.find?_some hfind
      have heq : target.terminal index = found :=
        (hsuccessor.2.2.2.2.2 index found).1 hfound
      simp only [computedRoutedTerminal, candidates, reaches] at hfind ⊢
      rw [hfind]
      exact heq.symm

def tubeRingChoiceOfBits
    (b0 b1 b2 b3 b4 : Bool) : TubeRingChoice := ![b0, b1, b2, b3, b4]

def phaseAFirstFullyRoutedChoice : Fin 10 -> TubeRingChoice := ![
  tubeRingChoiceOfBits false true true true false,
  tubeRingChoiceOfBits false true true true false,
  tubeRingChoiceOfBits false true false true false,
  tubeRingChoiceOfBits false true true true true,
  tubeRingChoiceOfBits false true true true false,
  tubeRingChoiceOfBits false false true true false,
  tubeRingChoiceOfBits false true true false false,
  tubeRingChoiceOfBits false true true true false,
  tubeRingChoiceOfBits false false false false true,
  tubeRingChoiceOfBits false false false false true
]

def phaseASecondFullyRoutedChoice : Fin 10 -> TubeRingChoice := ![
  tubeRingChoiceOfBits true false false false false,
  tubeRingChoiceOfBits true false false true true,
  tubeRingChoiceOfBits true false true false true,
  tubeRingChoiceOfBits true false false false false,
  tubeRingChoiceOfBits true false true false true,
  tubeRingChoiceOfBits true true false false true,
  tubeRingChoiceOfBits true false false true true,
  tubeRingChoiceOfBits true true false false true,
  tubeRingChoiceOfBits false true true true false,
  tubeRingChoiceOfBits true true true true false
]

def phaseBFirstFullyRoutedChoice : Fin 10 -> TubeRingChoice := ![
  tubeRingChoiceOfBits false true true false false,
  tubeRingChoiceOfBits false true true true true,
  tubeRingChoiceOfBits false true false true false,
  tubeRingChoiceOfBits false true true false false,
  tubeRingChoiceOfBits false false true true false,
  tubeRingChoiceOfBits false false true true false,
  tubeRingChoiceOfBits false true true true true,
  tubeRingChoiceOfBits false true false true false,
  tubeRingChoiceOfBits false false false false true,
  tubeRingChoiceOfBits true false false false true
]

def phaseBSecondFullyRoutedChoice : Fin 10 -> TubeRingChoice := ![
  tubeRingChoiceOfBits true false false false true,
  tubeRingChoiceOfBits true false false false false,
  tubeRingChoiceOfBits true false false false true,
  tubeRingChoiceOfBits true false false true true,
  tubeRingChoiceOfBits true true false false true,
  tubeRingChoiceOfBits true false false false true,
  tubeRingChoiceOfBits true false false false true,
  tubeRingChoiceOfBits true false true false true,
  tubeRingChoiceOfBits true true true true false,
  tubeRingChoiceOfBits true true true true false
]

def firstFullyRoutedChoice : RecurrentTubeProfile -> TubeRingChoice
  | (false, index) => phaseAFirstFullyRoutedChoice index
  | (true, index) => phaseBFirstFullyRoutedChoice index

def secondFullyRoutedChoice : RecurrentTubeProfile -> TubeRingChoice
  | (false, index) => phaseASecondFullyRoutedChoice index
  | (true, index) => phaseBSecondFullyRoutedChoice index

def phaseAFirstFullyRoutedTarget : Fin 10 -> Fin 10 :=
  ![0, 2, 4, 3, 5, 8, 7, 9, 8, 9]

def phaseASecondFullyRoutedTarget : Fin 10 -> Fin 10 :=
  ![1, 3, 2, 6, 7, 5, 0, 4, 6, 1]

def phaseBFirstFullyRoutedTarget : Fin 10 -> Fin 10 :=
  ![2, 1, 5, 4, 8, 9, 6, 7, 9, 8]

def phaseBSecondFullyRoutedTarget : Fin 10 -> Fin 10 :=
  ![1, 3, 4, 6, 5, 7, 0, 2, 0, 3]

def firstFullyRoutedTarget : RecurrentTubeProfile -> RecurrentTubeProfile
  | (false, index) => (true, phaseAFirstFullyRoutedTarget index)
  | (true, index) => (false, phaseBFirstFullyRoutedTarget index)

def secondFullyRoutedTarget : RecurrentTubeProfile -> RecurrentTubeProfile
  | (false, index) => (true, phaseASecondFullyRoutedTarget index)
  | (true, index) => (false, phaseBSecondFullyRoutedTarget index)

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer
