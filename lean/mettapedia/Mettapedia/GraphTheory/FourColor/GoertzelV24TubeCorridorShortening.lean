import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeEventualSupportPeriodicity
import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeCorridorLineGraph

/-!
# What the two-ring support return says about literal tube colourings

The normalized transfer is presented by actual choices of colours on the
twenty edges of each ring.  This file identifies exact transfer existence
with existence of a coherent colouring of the whole open corridor, then
transports the nine-to-eleven return to arbitrary endpoint tests.

The conclusion concerns the canonical open corridor and its full frontier
certificate.  It does not assert that an arbitrary planar map has such a
subcorridor or that removing two rings is a valid ambient map surgery.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeCorridorShortening

open GoertzelV24TubeRingTransfer
open GoertzelV24TubeEventualSupportPeriodicity
open GoertzelV24CorridorPumping
open GoertzelV24WindingClassification

/-- The literal line graph of one tube ring: vertices are its twenty edges,
and adjacency is incidence at an internal split or merge vertex. -/
def ringLineGraph : SimpleGraph TubeRingEdge where
  Adj left right := left ≠ right ∧ ShareRingVertex left right
  symm := ⟨by
    rintro left right ⟨hne, hshare⟩
    exact ⟨hne.symm, shareRingVertex_symm.symm left right hshare⟩⟩
  loopless := ⟨by
    intro edge hedge
    exact hedge.1 rfl⟩

/-- Every locally Tait-valid choice gives a proper colouring of the actual
one-ring incidence graph, whether or not its tracked strands survive. -/
def ringLineColouring (source : TubeFrontierState) (choice : TubeRingChoice)
    (hlocal : choice.LocallyTait source) : ringLineGraph.Coloring StrandColor :=
  SimpleGraph.Coloring.mk (ringColor source choice) (by
    intro left right hadj
    exact TubeRingChoice.ringColor_ne_of_share source choice hlocal
      hadj.1 hadj.2)

/-- This graph is exactly the single-ring part of the canonical corridor
line graph, not a separately invented adjacency test. -/
theorem ringLineGraph_adj_iff_corridor (left right : TubeRingEdge) :
    ringLineGraph.Adj left right ↔
      (tubeCorridorLineGraph 1).Adj
        (embedRingEdge (0 : Fin 1) left)
        (embedRingEdge (0 : Fin 1) right) := by
  constructor
  · rintro ⟨hne, hshare⟩
    exact ⟨0, left, right, hne, hshare, rfl, rfl⟩
  · rintro ⟨ring, localLeft, localRight, hne, hshare, hleft, hright⟩
    have hring : ring = (0 : Fin 1) := Subsingleton.elim _ _
    subst ring
    have hl : localLeft = left := embedRingEdge_injective 0 hleft
    have hr : localRight = right := embedRingEdge_injective 0 hright
    subst localLeft
    subst localRight
    exact ⟨hne, hshare⟩

/-- A locally proper five-bit choice at the normalized seed that is *not*
fully routed.  Its existence is a precise obstruction to reflecting all
proper graph colourings into the twenty-state recurrent transfer. -/
def escapingChoice : TubeRingChoice :=
  tubeRingChoiceOfBits true false true false true

theorem escapingChoice_locallyTait :
    escapingChoice.LocallyTait
      (recurrentProfileState (true, (5 : Fin 10))) := by
  constructor <;> intro vertex <;> fin_cases vertex <;> decide +kernel

theorem escapingChoice_not_fullyRouted :
    ¬ escapingChoice.FullyRouted
      (recurrentProfileState (true, (5 : Fin 10))) := by
  decide +kernel

/-- The failure is not an abstract predicate mismatch: the choice joins
two different incoming named strands (numbers two and three). -/
theorem escapingChoice_joins_old_terminals :
    trackedRingReachable
      (recurrentProfileState (true, (5 : Fin 10))) escapingChoice
      (.old ((recurrentProfileState (true, (5 : Fin 10))).terminal 2))
      (.old ((recurrentProfileState (true, (5 : Fin 10))).terminal 3)) = true := by
  decide +kernel

/-- This proper one-ring graph colouring is not a state transition in the
normalized physical transfer: no target frontier supplies the missing
four-strand routing certificate. -/
theorem escapingChoice_no_successor :
    ¬ ∃ target : TubeFrontierState,
      IsTubeRingSuccessor
        (recurrentProfileState (true, (5 : Fin 10)))
        target escapingChoice := by
  rintro ⟨target, hsuccessor⟩
  have h := (hsuccessor.2.2.2.2.1 (2 : Fin 4) (3 : Fin 4)).1
    escapingChoice_joins_old_terminals
  exact (by decide : (2 : Fin 4) ≠ 3) h

/-- An actual proper one-ring graph colouring which the fully-routed
transfer does not admit. The theorem `escapingChoice_no_successor` gives the
negative half; this definition gives the positive, graph-level half. -/
def escapingChoice_properGraphColouring : ringLineGraph.Coloring StrandColor :=
  ringLineColouring _ escapingChoice escapingChoice_locallyTait

/-- A coherent corridor colouring determines an exact path of physical
one-ring successors.  Combined with `exactTransfer_exists_taitColoring`,
this closes the semantic round trip for the canonical open corridor. -/
theorem TubeCorridorTaitColoring.toExactTransfer
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish) :
    ExactRelationalTransfer TubeRingStep rings start finish := by
  induction rings generalizing start with
  | zero =>
      have hstart := coloring.first_state
      have hfinish := coloring.last_state
      have heq : start = finish := by
        calc
          start = coloring.frontierState 0 := hstart.symm
          _ = coloring.frontierState (Fin.last 0) := rfl
          _ = finish := hfinish
      subst finish
      exact .zero start
  | succ rings ih =>
      let next := coloring.frontierState 1
      have hstep : TubeRingStep start next := by
        refine ⟨coloring.ringChoice 0, ?_⟩
        simpa [next, coloring.first_state] using coloring.successor 0
      let tail : TubeCorridorTaitColoring rings next finish := {
        frontierState := fun level => coloring.frontierState level.succ
        ringChoice := fun ring => coloring.ringChoice ring.succ
        first_state := rfl
        last_state := by simpa using coloring.last_state
        successor := by
          intro ring
          simpa using coloring.successor ring.succ
      }
      exact .succ hstep (ih tail)

/-- Reachability is exactly existence of a proper coherent colouring of
the canonical open tube graph, with its complete frontier certificate. -/
theorem transfer_iff_corridor_colouring
    (rings : Nat) (start finish : TubeFrontierState) :
    ExactRelationalTransfer TubeRingStep rings start finish ↔
      Nonempty (TubeCorridorTaitColoring rings start finish) := by
  constructor
  · exact exactTransfer_exists_taitColoring
  · rintro ⟨coloring⟩
    exact TubeCorridorTaitColoring.toExactTransfer coloring

/-- Inserting or deleting two rings after the first nine preserves every
endpoint-dependent existence test on coherent, locally proper corridor
colourings. -/
theorem corridorCapAcceptance_period_two_after_nine
    (extra : Nat) (source : RecurrentTubeProfile)
    (accepts : TubeFrontierState → Prop) :
    (∃ target : TubeFrontierState,
        Nonempty (TubeCorridorTaitColoring (9 + extra + 2)
          (recurrentProfileState source) target) ∧ accepts target) ↔
      (∃ target : TubeFrontierState,
        Nonempty (TubeCorridorTaitColoring (9 + extra)
          (recurrentProfileState source) target) ∧ accepts target) := by
  simpa only [← transfer_iff_corridor_colouring] using
    rawCapAcceptance_period_two_after_nine extra source accepts

/-- In particular, if a cap rejects every colouring of the eleven-ring
canonical corridor, it also rejects every colouring of the nine-ring one. -/
theorem no_shorter_cap_colouring_of_no_longer_cap_colouring
    (source : RecurrentTubeProfile)
    (accepts : TubeFrontierState → Prop)
    (h : ¬ ∃ target : TubeFrontierState,
      Nonempty (TubeCorridorTaitColoring 11
        (recurrentProfileState source) target) ∧ accepts target) :
    ¬ ∃ target : TubeFrontierState,
      Nonempty (TubeCorridorTaitColoring 9
        (recurrentProfileState source) target) ∧ accepts target := by
  intro hshort
  exact h ((corridorCapAcceptance_period_two_after_nine 0 source accepts).2
    (by simpa using hshort))

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeCorridorShortening
