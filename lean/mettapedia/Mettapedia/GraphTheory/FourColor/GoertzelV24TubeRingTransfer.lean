import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorPumping
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24WindingClassification

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TubeRingTransfer

open GoertzelV24CorridorPumping
open GoertzelV24EarlyFalsifiers
open GoertzelV24WindingClassification

/-- A normalized five-edge frontier state for the `(5,0)` tube. `terminal`
records which tracked frontier edge is connected to each of the four fixed
seed terminals. -/
structure TubeFrontierState where
  color : Fin 5 → StrandColor
  terminal : Fin 4 → Fin 5
  deriving DecidableEq, Fintype

def IsTracked (color : StrandColor) : Prop := color ≠ .c
  deriving Decidable

def TubeFrontierState.Valid (state : TubeFrontierState) : Prop :=
  Function.Injective state.terminal ∧
  ∀ position, IsTracked (state.color position) ↔
    ∃ terminal, state.terminal terminal = position
  deriving Decidable

/-- The twenty edges in one normalized tube ring: five old frontier edges,
ten edges between the split and merge layers, and five new frontier edges. -/
inductive TubeRingEdge where
  | old : Fin 5 → TubeRingEdge
  | middle : Fin 10 → TubeRingEdge
  | new : Fin 5 → TubeRingEdge
  deriving DecidableEq, Fintype

/-- Split-layer endpoint of each middle edge. -/
def middleFirst : Fin 10 → Fin 5 :=
  ![0, 1, 0, 4, 1, 2, 2, 3, 3, 4]

/-- Which of the two edges at its split vertex a middle edge occupies. -/
def middleSlot : Fin 10 → Bool :=
  ![false, false, true, false, true, false, true, false, true, true]

/-- Merge-layer endpoint of each middle edge. -/
def middleSecond : Fin 10 → Fin 5 :=
  ![0, 0, 1, 1, 2, 2, 3, 3, 4, 4]

def secondLeft : Fin 5 → Fin 10 := ![0, 2, 4, 6, 8]

def secondRight : Fin 5 → Fin 10 := ![1, 3, 5, 7, 9]

/-- New-frontier position incident with each merge vertex. -/
def secondNew : Fin 5 → Fin 5 := ![0, 4, 1, 2, 3]

/-- Merge vertex incident with each new-frontier position. -/
def newSecond : Fin 5 → Fin 5 := ![0, 2, 3, 4, 1]

def firstComplement : StrandColor → StrandColor
  | .a => .b
  | .b => .a
  | .c => .a

def secondComplement : StrandColor → StrandColor
  | .a => .c
  | .b => .c
  | .c => .b

/-- The third color. Equal inputs are assigned `.a`; local validity excludes
that branch wherever this operation is used by a ring coloring. -/
def thirdColor : StrandColor → StrandColor → StrandColor
  | .a, .b | .b, .a => .c
  | .a, .c | .c, .a => .b
  | .b, .c | .c, .b => .a
  | _, _ => .a

/-- A choice swaps the two complementary colors at each split vertex. -/
abbrev TubeRingChoice := Fin 5 → Bool

def middleColor (source : TubeFrontierState) (choice : TubeRingChoice)
    (edge : Fin 10) : StrandColor :=
  let oldColor := source.color (middleFirst edge)
  if choice (middleFirst edge) = middleSlot edge then
    firstComplement oldColor
  else
    secondComplement oldColor

def newColor (source : TubeFrontierState) (choice : TubeRingChoice)
    (position : Fin 5) : StrandColor :=
  let vertex := newSecond position
  thirdColor
    (middleColor source choice (secondLeft vertex))
    (middleColor source choice (secondRight vertex))

def TubeRingChoice.Valid
    (source : TubeFrontierState) (choice : TubeRingChoice) : Prop :=
  ∀ vertex,
    middleColor source choice (secondLeft vertex) ≠
      middleColor source choice (secondRight vertex)
  deriving Decidable

def ringColor (source : TubeFrontierState) (choice : TubeRingChoice) :
    TubeRingEdge → StrandColor
  | .old position => source.color position
  | .middle edge => middleColor source choice edge
  | .new position => newColor source choice position

def firstIncident : TubeRingEdge → Fin 5 → Bool
  | .old position, vertex => position == vertex
  | .middle edge, vertex => middleFirst edge == vertex
  | .new _, _ => false

def secondIncident : TubeRingEdge → Fin 5 → Bool
  | .old _, _ => false
  | .middle edge, vertex => middleSecond edge == vertex
  | .new position, vertex => newSecond position == vertex

def ShareRingVertex (left right : TubeRingEdge) : Prop :=
  (∃ vertex, firstIncident left vertex = true ∧ firstIncident right vertex = true) ∨
  ∃ vertex, secondIncident left vertex = true ∧ secondIncident right vertex = true
  deriving Decidable

theorem shareRingVertex_symm : Std.Symm ShareRingVertex := ⟨by
    intro left right hshare
    rcases hshare with ⟨vertex, hleft, hright⟩ | ⟨vertex, hleft, hright⟩
    · exact Or.inl ⟨vertex, hright, hleft⟩
    · exact Or.inr ⟨vertex, hright, hleft⟩⟩

/-- The local two-color component graph through one normalized tube ring. -/
def trackedRingGraph (source : TubeFrontierState) (choice : TubeRingChoice) :
    SimpleGraph TubeRingEdge where
  Adj left right :=
    left ≠ right ∧
    IsTracked (ringColor source choice left) ∧
    IsTracked (ringColor source choice right) ∧
    ShareRingVertex left right
  symm := ⟨by
    rintro left right ⟨hne, hleft, hright, hshare⟩
    exact ⟨hne.symm, hright, hleft, shareRingVertex_symm.symm left right hshare⟩⟩
  loopless := ⟨by
    intro edge hedge
    exact hedge.1 rfl⟩

instance trackedRingGraph_decidableAdj
    (source : TubeFrontierState) (choice : TubeRingChoice) :
    DecidableRel (trackedRingGraph source choice).Adj := by
  intro left right
  change Decidable
    (left ≠ right ∧
      IsTracked (ringColor source choice left) ∧
      IsTracked (ringColor source choice right) ∧
      ShareRingVertex left right)
  infer_instance

def trackedRingAdj (source : TubeFrontierState) (choice : TubeRingChoice)
    (left right : TubeRingEdge) : Bool :=
  decide ((trackedRingGraph source choice).Adj left right)

/-- Executable bounded breadth-first reachability on the twenty-edge local
ring graph. -/
def trackedRingReachable (source : TubeFrontierState) (choice : TubeRingChoice)
    (start finish : TubeRingEdge) : Bool :=
  decide (finish ∈ finsetReachWithin (trackedRingAdj source choice) start
    (Fintype.card TubeRingEdge))

theorem trackedRingReachable_eq_true_iff_reachable
    (source : TubeFrontierState) (choice : TubeRingChoice)
    (start finish : TubeRingEdge) :
    trackedRingReachable source choice start finish = true ↔
      (trackedRingGraph source choice).Reachable start finish := by
  simp only [trackedRingReachable, decide_eq_true_eq]
  apply mem_finsetReachWithin_card_iff_reachable
  intro left right
  simp [trackedRingAdj]

/-- A target is a genuine one-ring successor when a proper local Tait
extension realizes exactly its new colors and exactly its four terminal-to-
frontier tracked components. -/
def IsTubeRingSuccessor
    (source target : TubeFrontierState) (choice : TubeRingChoice) : Prop :=
  source.Valid ∧
  choice.Valid source ∧
  target.Valid ∧
  (∀ position, target.color position = newColor source choice position) ∧
  (∀ left right,
    trackedRingReachable source choice
      (.old (source.terminal left)) (.old (source.terminal right)) = true ↔
      left = right) ∧
  ∀ terminal position,
    trackedRingReachable source choice
      (.old (source.terminal terminal)) (.new position) = true ↔
      target.terminal terminal = position
  deriving Decidable

/-- Existential one-ring transfer after forgetting the local split choices. -/
def TubeRingStep (source target : TubeFrontierState) : Prop :=
  ∃ choice : TubeRingChoice, IsTubeRingSuccessor source target choice
  deriving Decidable

/-- Three colors are pairwise distinct. This is local Tait properness at a
cubic vertex. -/
def PairwiseDistinct3 (first second third : StrandColor) : Prop :=
  first ≠ second ∧ first ≠ third ∧ second ≠ third
  deriving Decidable

/-- The middle edge in the left slot at each split vertex. -/
def firstLeft : Fin 5 → Fin 10 := ![0, 1, 5, 7, 3]

/-- The middle edge in the right slot at each split vertex. -/
def firstRight : Fin 5 → Fin 10 := ![2, 4, 6, 8, 9]

theorem middleFirst_firstLeft (vertex : Fin 5) :
    middleFirst (firstLeft vertex) = vertex := by fin_cases vertex <;> decide

theorem middleFirst_firstRight (vertex : Fin 5) :
    middleFirst (firstRight vertex) = vertex := by fin_cases vertex <;> decide

theorem middleSlot_firstLeft (vertex : Fin 5) :
    middleSlot (firstLeft vertex) = false := by fin_cases vertex <;> decide

theorem middleSlot_firstRight (vertex : Fin 5) :
    middleSlot (firstRight vertex) = true := by fin_cases vertex <;> decide

/-- Properness of the three incident colors at all ten internal vertices of
one ring. -/
def TubeRingChoice.LocallyTait
    (source : TubeFrontierState) (choice : TubeRingChoice) : Prop :=
  (∀ vertex,
    PairwiseDistinct3
      (source.color vertex)
      (middleColor source choice (firstLeft vertex))
      (middleColor source choice (firstRight vertex))) ∧
  ∀ vertex,
    PairwiseDistinct3
      (middleColor source choice (secondLeft vertex))
      (middleColor source choice (secondRight vertex))
      (newColor source choice (secondNew vertex))

theorem complement_pairwiseDistinct (color : StrandColor) :
    PairwiseDistinct3 color (firstComplement color) (secondComplement color) := by
  cases color <;> decide

theorem complement_pairwiseDistinct_swap (color : StrandColor) :
    PairwiseDistinct3 color (secondComplement color) (firstComplement color) := by
  cases color <;> decide

theorem split_pairwiseDistinct (color : StrandColor) (choice : Bool) :
    PairwiseDistinct3 color
      (if choice = false then firstComplement color else secondComplement color)
      (if choice = true then firstComplement color else secondComplement color) := by
  cases choice
  · simpa using complement_pairwiseDistinct color
  · simpa using complement_pairwiseDistinct_swap color

theorem thirdColor_pairwiseDistinct {left right : StrandColor}
    (hne : left ≠ right) :
    PairwiseDistinct3 left right (thirdColor left right) := by
  cases left <;> cases right <;> simp_all [PairwiseDistinct3, thirdColor]

/-- Merge validity plus the explicit complementary split construction proves
proper Tait coloring at every internal vertex of the ring. -/
theorem TubeRingChoice.locallyTait_of_valid
    (source : TubeFrontierState) (choice : TubeRingChoice)
    (hvalid : choice.Valid source) : choice.LocallyTait source := by
  constructor
  · intro vertex
    simpa [middleColor, middleFirst_firstLeft, middleFirst_firstRight,
      middleSlot_firstLeft, middleSlot_firstRight] using
      split_pairwiseDistinct (source.color vertex) (choice vertex)
  · intro vertex
    have hne := hvalid vertex
    have hproper := thirdColor_pairwiseDistinct hne
    fin_cases vertex <;>
      simpa [newColor, newSecond, secondNew] using hproper

theorem IsTubeRingSuccessor.locallyTait
    {source target : TubeFrontierState} {choice : TubeRingChoice}
    (hsuccessor : IsTubeRingSuccessor source target choice) :
    choice.LocallyTait source :=
  choice.locallyTait_of_valid source hsuccessor.2.1

/-- One coloring of a whole glued tube corridor. Frontier levels are stored
once, so adjacent ring certificates agree on every shared edge by
construction. -/
structure TubeCorridorTaitColoring (rings : Nat)
    (start finish : TubeFrontierState) where
  frontierState : Fin (rings + 1) → TubeFrontierState
  ringChoice : Fin rings → TubeRingChoice
  first_state : frontierState 0 = start
  last_state : frontierState (Fin.last rings) = finish
  successor : ∀ ring,
    IsTubeRingSuccessor
      (frontierState ring.castSucc)
      (frontierState ring.succ)
      (ringChoice ring)

/-- An exact path of genuine ring transfers assembles into one corridor
coloring with shared frontier colors and tracked terminal identities. -/
theorem exactTransfer_exists_taitColoring
    {rings : Nat} {start finish : TubeFrontierState}
    (transfer : ExactRelationalTransfer TubeRingStep rings start finish) :
    Nonempty (TubeCorridorTaitColoring rings start finish) := by
  induction transfer with
  | zero profile =>
      exact ⟨{
        frontierState := fun _ => profile
        ringChoice := Fin.elim0
        first_state := rfl
        last_state := rfl
        successor := fun ring => Fin.elim0 ring
      }⟩
  | @succ length start next finish hstep _tail ih =>
      obtain ⟨choice, hchoice⟩ := hstep
      obtain ⟨tailColoring⟩ := ih
      exact ⟨{
        frontierState := Fin.cases start tailColoring.frontierState
        ringChoice := Fin.cases choice tailColoring.ringChoice
        first_state := rfl
        last_state := by
          change tailColoring.frontierState (Fin.last length) = finish
          exact tailColoring.last_state
        successor := by
          intro ring
          refine Fin.cases ?_ (fun index => ?_) ring
          · change IsTubeRingSuccessor start
              (tailColoring.frontierState 0) choice
            rw [tailColoring.first_state]
            exact hchoice
          · change IsTubeRingSuccessor
              (tailColoring.frontierState index.castSucc)
              (tailColoring.frontierState index.succ)
              (tailColoring.ringChoice index)
            exact tailColoring.successor index
      }⟩

/-- Shared frontier edges and internal middle edges of a glued tube corridor. -/
abbrev TubeCorridorEdge (rings : Nat) :=
  (Fin (rings + 1) × Fin 5) ⊕ (Fin rings × Fin 10)

def TubeCorridorTaitColoring.edgeColor
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish) :
    TubeCorridorEdge rings → StrandColor
  | .inl (level, position) => (coloring.frontierState level).color position
  | .inr (ring, edge) =>
      middleColor (coloring.frontierState ring.castSucc)
        (coloring.ringChoice ring) edge

/-- Properness of the assembled edge-coloring at all internal cubic vertices
of all rings. -/
def TubeCorridorTaitColoring.LocallyTait
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish) : Prop :=
  ∀ ring,
    (∀ vertex,
      PairwiseDistinct3
        (coloring.edgeColor (.inl (ring.castSucc, vertex)))
        (coloring.edgeColor (.inr (ring, firstLeft vertex)))
        (coloring.edgeColor (.inr (ring, firstRight vertex)))) ∧
    ∀ vertex,
      PairwiseDistinct3
        (coloring.edgeColor (.inr (ring, secondLeft vertex)))
        (coloring.edgeColor (.inr (ring, secondRight vertex)))
        (coloring.edgeColor (.inl (ring.succ, secondNew vertex)))

/-- Every assembled corridor certificate is a proper Tait coloring at every
internal cubic vertex, including vertices adjacent to shared frontiers. -/
theorem TubeCorridorTaitColoring.locallyTait
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish) :
    coloring.LocallyTait := by
  intro ring
  have hsuccessor := coloring.successor ring
  have hlocal := hsuccessor.locallyTait
  constructor
  · intro vertex
    exact hlocal.1 vertex
  · intro vertex
    have hcolor := hsuccessor.2.2.2.1 (secondNew vertex)
    change PairwiseDistinct3
      (middleColor (coloring.frontierState ring.castSucc)
        (coloring.ringChoice ring) (secondLeft vertex))
      (middleColor (coloring.frontierState ring.castSucc)
        (coloring.ringChoice ring) (secondRight vertex))
      ((coloring.frontierState ring.succ).color (secondNew vertex))
    rw [hcolor]
    exact hlocal.2 vertex

/-- Exact relational composition therefore produces an assembled coloring
whose local Tait properness is part of the conclusion. -/
theorem exactTransfer_exists_locallyTaitColoring
    {rings : Nat} {start finish : TubeFrontierState}
    (transfer : ExactRelationalTransfer TubeRingStep rings start finish) :
    ∃ coloring : TubeCorridorTaitColoring rings start finish,
      coloring.LocallyTait := by
  obtain ⟨coloring⟩ := exactTransfer_exists_taitColoring transfer
  exact ⟨coloring, coloring.locallyTait⟩

/-- The first of the two alternating ten-state recurrent frontier sets. -/
def recurrentPhaseAState : Fin 10 → TubeFrontierState := ![
  ⟨![.a, .a, .a, .b, .c], ![2, 1, 0, 3]⟩,
  ⟨![.a, .a, .b, .c, .a], ![1, 0, 4, 2]⟩,
  ⟨![.a, .a, .c, .a, .b], ![3, 1, 0, 4]⟩,
  ⟨![.a, .b, .a, .a, .c], ![0, 3, 2, 1]⟩,
  ⟨![.a, .b, .c, .a, .a], ![0, 4, 3, 1]⟩,
  ⟨![.a, .c, .a, .b, .a], ![2, 0, 4, 3]⟩,
  ⟨![.b, .a, .a, .c, .a], ![4, 2, 1, 0]⟩,
  ⟨![.b, .c, .a, .a, .a], ![4, 3, 2, 0]⟩,
  ⟨![.c, .a, .a, .a, .b], ![3, 2, 1, 4]⟩,
  ⟨![.c, .a, .b, .a, .a], ![1, 4, 3, 2]⟩
]

/-- The second of the two alternating ten-state recurrent frontier sets. -/
def recurrentPhaseBState : Fin 10 → TubeFrontierState := ![
  ⟨![.a, .a, .a, .c, .b], ![2, 1, 0, 4]⟩,
  ⟨![.a, .a, .b, .a, .c], ![1, 0, 3, 2]⟩,
  ⟨![.a, .a, .c, .b, .a], ![1, 0, 4, 3]⟩,
  ⟨![.a, .b, .a, .c, .a], ![0, 4, 2, 1]⟩,
  ⟨![.a, .c, .a, .a, .b], ![3, 2, 0, 4]⟩,
  ⟨![.a, .c, .b, .a, .a], ![0, 4, 3, 2]⟩,
  ⟨![.b, .a, .a, .a, .c], ![3, 2, 1, 0]⟩,
  ⟨![.b, .a, .c, .a, .a], ![4, 3, 1, 0]⟩,
  ⟨![.c, .a, .a, .b, .a], ![2, 1, 4, 3]⟩,
  ⟨![.c, .b, .a, .a, .a], ![4, 3, 2, 1]⟩
]

/-- One explicitly selected genuine successor from each phase-A state. -/
def phaseAToBIndex : Fin 10 → Fin 10 := ![0, 2, 2, 3, 5, 5, 0, 4, 6, 1]

/-- One explicitly selected genuine successor from each phase-B state. -/
def phaseBToAIndex : Fin 10 → Fin 10 := ![1, 1, 4, 4, 5, 7, 0, 2, 0, 3]

/-- A recurrent profile remembers which normalized frontier phase is active
and its index in that phase's ten-state set. -/
abbrev RecurrentTubeProfile := Bool × Fin 10

def recurrentProfileState : RecurrentTubeProfile → TubeFrontierState
  | (false, index) => recurrentPhaseAState index
  | (true, index) => recurrentPhaseBState index

def selectedRecurrentSuccessor : RecurrentTubeProfile → RecurrentTubeProfile
  | (false, index) => (true, phaseAToBIndex index)
  | (true, index) => (false, phaseBToAIndex index)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
/-- Independent kernel evaluation of the normalized local ring graph verifies
the selected successor from every state in both recurrent phases. -/
theorem selectedRecurrentSuccessor_isTubeRingStep :
    ∀ profile : RecurrentTubeProfile,
      TubeRingStep (recurrentProfileState profile)
        (recurrentProfileState (selectedRecurrentSuccessor profile)) := by
  decide

/-- The actual normalized local-ring relation on the alternating recurrent
frontier profiles. -/
def RecurrentTubeRingStep
    (source target : RecurrentTubeProfile) : Prop :=
  TubeRingStep (recurrentProfileState source) (recurrentProfileState target)

theorem recurrentTubeRingStep_isSerial :
    LiveTransferIsSerial (fun _ : RecurrentTubeProfile => True)
      RecurrentTubeRingStep := by
  intro profile _hprofile
  exact ⟨selectedRecurrentSuccessor profile, True.intro,
    selectedRecurrentSuccessor_isTubeRingStep profile⟩

/-- The normalized recurrent `(5,0)` tube transfer has exact corridor paths
in a positive-period congruence class. This is obtained from genuine local
Tait extensions and tracked-component migration, not a self-loop premise. -/
theorem recurrentTube_periodicCorridorPumpingWithCongruence :
    PeriodicCorridorPumpingWithCongruence
      (fun _ : RecurrentTubeProfile => True)
      (ExactRelationalTransfer RecurrentTubeRingStep) :=
  finiteSerialTransfer_periodicCorridorPumpingWithCongruence
    (fun _ : RecurrentTubeProfile => True)
    RecurrentTubeRingStep recurrentTubeRingStep_isSerial

/-- The good cap word `(a,a,a,b,c)` with the four tracked terminals in cap
boundary order. -/
def goodTubeCapState : TubeFrontierState :=
  ⟨![.a, .a, .a, .b, .c], ![0, 1, 2, 3]⟩

theorem goodTubeCapState_valid : goodTubeCapState.Valid := by decide

/-- Reflection from cap boundary order to the normalized ring coordinates. -/
def goodTubeCapReflection : Fin 5 ≃ Fin 5 where
  toFun := ![0, 4, 3, 2, 1]
  invFun := ![0, 4, 3, 2, 1]
  left_inv := by intro position; fin_cases position <;> rfl
  right_inv := by intro position; fin_cases position <;> rfl

/-- Reindex a frontier state without changing its colors or terminal
identities. -/
def TubeFrontierState.reindex
    (state : TubeFrontierState) (coordinates : Fin 5 ≃ Fin 5) :
    TubeFrontierState where
  color position := state.color (coordinates.symm position)
  terminal index := coordinates (state.terminal index)

/-- The canonical good seed after rotating the cap frontier into the
normalized ring coordinates. -/
def normalizedTubeSeed : TubeFrontierState := recurrentPhaseBState 5

/-- The declared recurrent seed is exactly the reflected good cap word, with
all four original terminal identities preserved. -/
theorem goodTubeCapState_reindex_eq_normalizedTubeSeed :
    goodTubeCapState.reindex goodTubeCapReflection = normalizedTubeSeed := by
  unfold TubeFrontierState.reindex goodTubeCapState goodTubeCapReflection
    normalizedTubeSeed recurrentPhaseBState
  congr 1
  · funext position
    fin_cases position <;> rfl
  · funext terminal
    fin_cases terminal <;> rfl

/-- Four genuine normalized ring extensions return the canonical seed state.
This is the concrete period detected by the alternating recurrent subsystem. -/
theorem normalizedTubeSeed_fourRingReturn :
    ExactRelationalTransfer TubeRingStep 4
      normalizedTubeSeed normalizedTubeSeed := by
  have h0 : TubeRingStep normalizedTubeSeed (recurrentPhaseAState 7) := by
    simpa [normalizedTubeSeed, recurrentProfileState, selectedRecurrentSuccessor,
      phaseBToAIndex] using
      selectedRecurrentSuccessor_isTubeRingStep (true, (5 : Fin 10))
  have h1 : TubeRingStep (recurrentPhaseAState 7) (recurrentPhaseBState 4) := by
    simpa [recurrentProfileState, selectedRecurrentSuccessor, phaseAToBIndex] using
      selectedRecurrentSuccessor_isTubeRingStep (false, (7 : Fin 10))
  have h2 : TubeRingStep (recurrentPhaseBState 4) (recurrentPhaseAState 5) := by
    simpa [recurrentProfileState, selectedRecurrentSuccessor, phaseBToAIndex] using
      selectedRecurrentSuccessor_isTubeRingStep (true, (4 : Fin 10))
  have h3 : TubeRingStep (recurrentPhaseAState 5) normalizedTubeSeed := by
    simpa [normalizedTubeSeed, recurrentProfileState, selectedRecurrentSuccessor,
      phaseAToBIndex] using
      selectedRecurrentSuccessor_isTubeRingStep (false, (5 : Fin 10))
  exact .succ h0 (.succ h1 (.succ h2 (.succ h3 (.zero normalizedTubeSeed))))

/-- The canonical normalized seed returns after every whole multiple of four
rings. -/
theorem normalizedTubeSeed_periodicPadding (repetitions : Nat) :
    ExactRelationalTransfer TubeRingStep (repetitions * 4)
      normalizedTubeSeed normalizedTubeSeed :=
  normalizedTubeSeed_fourRingReturn.repeat repetitions

/-- The four-ring return is one proper edge-coloring of the whole glued tube,
not merely four unrelated local witnesses. -/
theorem normalizedTubeSeed_fourRingTaitColoring :
    ∃ coloring : TubeCorridorTaitColoring 4
        normalizedTubeSeed normalizedTubeSeed,
      coloring.LocallyTait :=
  exactTransfer_exists_locallyTaitColoring normalizedTubeSeed_fourRingReturn

/-- Every multiple of four rings admits a proper glued tube coloring that
starts and ends at the reflected good cap state. -/
theorem normalizedTubeSeed_periodicTaitColoring (repetitions : Nat) :
    ∃ coloring : TubeCorridorTaitColoring (repetitions * 4)
        normalizedTubeSeed normalizedTubeSeed,
      coloring.LocallyTait :=
  exactTransfer_exists_locallyTaitColoring
    (normalizedTubeSeed_periodicPadding repetitions)

/-- Concrete corrected L2 statement for the normalized `(5,0)` tube seed:
the exact return lengths contain the congruence class `0 mod 4`. -/
theorem normalizedTubeSeed_periodicCorridorPumpingWithCongruence :
    PeriodicCorridorPumpingWithCongruence
      (fun state : TubeFrontierState => state = normalizedTubeSeed)
      (ExactRelationalTransfer TubeRingStep) := by
  intro start hstart
  subst start
  exact ⟨normalizedTubeSeed, 0, 4, by decide,
    ExactRelationalTransfer.zero normalizedTubeSeed,
    normalizedTubeSeed_fourRingReturn, by
      intro length hlength
      obtain ⟨repetitions, rfl⟩ := hlength
      simpa using normalizedTubeSeed_periodicPadding repetitions⟩

end GoertzelV24TubeRingTransfer

end Mettapedia.GraphTheory.FourColor
