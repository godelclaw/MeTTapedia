import Mettapedia.Combinatorics.Reconfiguration.Composition
import Mettapedia.GraphTheory.FourColor.GoertzelLemma814

/-!
# Step lifting fails for two gadgets in series

Two canonical three-cell gadgets are glued in series along the interface
`X.B4..X.B7 = Y.B0..Y.B3`.  A colouring of the composite is a pair of gadget
colourings agreeing on the interface; the projection keeps the upstream one.

`GoertzelLemma814.lemma818_pointwise_lift_preparation_obstruction` takes the
upstream state `6` with downstream state `176`, and the input-avoiding
`{r,b}`-switch seeded at `B5`, whose interface footprint is `{B5,B7}`.  It
shows that no downstream colouring with the same interface colours pairs the
corresponding downstream stubs, so the preparation step of the manuscript's
proof of Lemma 8.18 cannot be carried out.

This file checks the stronger fact behind it: the switch carries the upstream
state `6` to state `4`, and state `4` agrees on the interface with no
downstream gadget colouring at all.  So no composite colouring lies over the
target of this move, and step lifting for every upstream move
(`Reconfiguration.LiftsSteps`) fails for the composite, whatever the composite
moves are.  A lifting hypothesis can only be asked of moves whose target
extends, which is the form `Reconfiguration.ImageStep` takes.

None of this touches the composite statement: LKR_in of the two-gadget
composite holds (`GoertzelLemma818LengthTwoTTRealAudit.ttChainLKRInAudit_ok`).
-/

namespace Mettapedia.Combinatorics.Reconfiguration

namespace TauTauLifting

open Mettapedia.GraphTheory.FourColor
open GoertzelLemma814

/-- Colourings of two gadgets in series: two listed gadget colourings agreeing
on the glued interface. -/
def SeriesState : Type :=
  { p : TauState × TauState //
    p.1 ∈ allTauStates ∧ p.2 ∈ allTauStates ∧ tauInterfaceColorAgrees p.1 p.2 = true }

/-- Restriction to the upstream gadget. -/
def upstream (s : SeriesState) : TauState :=
  s.1.1

/-- One input-avoiding Kempe switch of the upstream gadget, in the list model
certified by Lemma 8.14's audit. -/
def upstreamStep (s t : TauState) : Prop :=
  singleKempeStep s t = true

/-- The obstruction's composite colouring exists. -/
theorem obstruction_source :
    stateAt 6 ∈ allTauStates ∧ stateAt 176 ∈ allTauStates ∧
      tauInterfaceColorAgrees (stateAt 6) (stateAt 176) = true := by
  decide

/-- The obstruction's switch — `{r,b}` on the component seeded at `B5` — carries
upstream state `6` to state `4`, and it is an input-avoiding Kempe switch. -/
theorem obstruction_switch :
    agreesWithSwitch (stateAt 6) (stateAt 4)
        (tauComponent (stateAt 6) LColor.r LColor.b TauEdge.B5) LColor.r LColor.b = true ∧
      componentAvoidsInputs (tauComponent (stateAt 6) LColor.r LColor.b TauEdge.B5) = true ∧
      upstreamStep (stateAt 6) (stateAt 4) := by
  refine ⟨by decide, by decide, ?_⟩
  change singleKempeStep (stateAt 6) (stateAt 4) = true
  decide

/-- Upstream state `4` extends across the interface to no downstream gadget
colouring. -/
theorem obstruction_target_has_no_extension :
    allTauStates.all (fun y => !tauInterfaceColorAgrees (stateAt 4) y) = true := by
  decide

/-- **Step lifting fails for two gadgets in series**, for any choice of
composite moves. -/
theorem not_liftsSteps (seriesStep : SeriesState → SeriesState → Prop) :
    ¬ LiftsSteps seriesStep upstreamStep upstream := by
  intro hlift
  let x : SeriesState := ⟨(stateAt 6, stateAt 176), obstruction_source⟩
  obtain ⟨y, hy, -⟩ := hlift x (stateAt 4) obstruction_switch.2.2
  have hno := List.all_eq_true.mp obstruction_target_has_no_extension y.1.2 y.2.2.1
  have hagree := y.2.2.2
  change upstream y = stateAt 4 at hy
  simp only [upstream] at hy
  rw [hy] at hagree
  rw [hagree] at hno
  exact Bool.false_ne_true hno

/-- The move is not an image move, so the restricted lifting hypothesis of
`Reconfiguration.fibresConnected_of_parts` asks nothing of it. -/
theorem obstruction_switch_not_imageStep :
    ¬ ImageStep upstreamStep upstream (stateAt 6) (stateAt 4) := by
  rintro ⟨-, y, hy⟩
  have hno := List.all_eq_true.mp obstruction_target_has_no_extension y.1.2 y.2.2.1
  have hagree := y.2.2.2
  change y.1.1 = stateAt 4 at hy
  rw [hy] at hagree
  rw [hagree] at hno
  exact Bool.false_ne_true hno

end TauTauLifting

end Mettapedia.Combinatorics.Reconfiguration
