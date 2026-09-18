import Mettapedia.Combinatorics.Reconfiguration.Composition
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818Fibration
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareLadder
import Mettapedia.GraphTheory.FourColor.GoertzelV24RouteSquareTransport

/-!
# The earlier presentations are instances

Three earlier modules state pieces of the reconfiguration layer for their own
use:

* `GoertzelLemma818Fibration` defines its own reachability `Reach` (an inductive
  copy of `Relation.ReflTransGen`), `Connected`, and a `Fibration` structure with
  fields `fiberReach` and `liftStep`;
* `GoertzelV24SquareLadder` defines `SidePathLifting` with fields `surjective`,
  `connectedFibres` and `liftsEdges`;
* `GoertzelV24RouteSquareTransport` proves the two-sided completability skeleton
  `wcStar_of_both_sides` and the one-sided `side_reaches_targetUp`.

Here each is identified with the general notion: `Reach` is `ReflTransGen`, the
first `Fibration` is `Reconfiguration.Fibration`, and `SidePathLifting` is
`Reconfiguration.Fibration` together with surjectivity of the projection.  The
fields match one for one; surjectivity is the only extra datum, and it is used
only to lift a target, never a path.

Each headline theorem is then re-derived from the general layer under its own
exact statement, and the two proofs are equated.  Since proofs of a
proposition are equal, the equation `@old = @new` type-checks exactly when the
two statements agree, so a change to either statement breaks this file.
-/

namespace Mettapedia.Combinatorics.Reconfiguration

open Relation
open Mettapedia.GraphTheory.FourColor

namespace Instances

universe u v w

/-! ## `GoertzelLemma818Fibration` -/

section Lemma818

variable {α : Type u} {step : α → α → Prop}

/-- The inductive `Reach` of `GoertzelLemma818Fibration` is `ReflTransGen`. -/
theorem reach_iff_reflTransGen {x y : α} :
    GoertzelLemma818Fibration.Reach step x y ↔ ReflTransGen step x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail hstep
  · intro h
    induction h with
    | refl => exact GoertzelLemma818Fibration.Reach.refl _
    | tail _ hstep ih => exact GoertzelLemma818Fibration.Reach.tail ih hstep

theorem connected_iff :
    GoertzelLemma818Fibration.Connected step ↔ Connected step :=
  forall₂_congr fun _ _ => reach_iff_reflTransGen

variable {Total : Type u} {Base : Type v}
  {totalStep : Total → Total → Prop} {baseStep : Base → Base → Prop}
  {proj : Total → Base}

/-- The `Fibration` of `GoertzelLemma818Fibration` is `Reconfiguration.Fibration`. -/
theorem lemma818Fibration_iff :
    GoertzelLemma818Fibration.Fibration totalStep baseStep proj ↔
      Fibration totalStep baseStep proj := by
  constructor
  · intro h
    exact
      { fibresConnected := fun x y hxy =>
          reach_iff_reflTransGen.1 (h.fiberReach x y hxy)
        liftsSteps := fun x b hb =>
          (h.liftStep x b hb).imp fun _ hy =>
            ⟨hy.1, reach_iff_reflTransGen.1 hy.2⟩ }
  · intro h
    exact
      { fiberReach := fun x y hxy =>
          reach_iff_reflTransGen.2 (h.fibresConnected x y hxy)
        liftStep := fun x b hb =>
          (h.liftsSteps x b hb).imp fun _ hy =>
            ⟨hy.1, reach_iff_reflTransGen.2 hy.2⟩ }

/-- `exists_reachable_over_base`, from `LiftsSteps.lift`. -/
theorem exists_reachable_over_base
    (h : GoertzelLemma818Fibration.Fibration totalStep baseStep proj)
    {x : Total} {b : Base}
    (hbase : GoertzelLemma818Fibration.Reach baseStep (proj x) b) :
    ∃ y : Total, proj y = b ∧ GoertzelLemma818Fibration.Reach totalStep x y :=
  ((lemma818Fibration_iff.1 h).liftsSteps.lift
      (reach_iff_reflTransGen.1 hbase)).imp fun _ hy =>
    ⟨hy.1, reach_iff_reflTransGen.2 hy.2⟩

/-- `totalReach_of_baseReach`, from `Fibration.reach`. -/
theorem totalReach_of_baseReach
    (h : GoertzelLemma818Fibration.Fibration totalStep baseStep proj)
    {x y : Total}
    (hbase : GoertzelLemma818Fibration.Reach baseStep (proj x) (proj y)) :
    GoertzelLemma818Fibration.Reach totalStep x y :=
  reach_iff_reflTransGen.2
    ((lemma818Fibration_iff.1 h).reach (reach_iff_reflTransGen.1 hbase))

/-- `totalConnected_of_baseConnected`, from `Fibration.connected`. -/
theorem totalConnected_of_baseConnected
    (h : GoertzelLemma818Fibration.Fibration totalStep baseStep proj)
    (hbase : GoertzelLemma818Fibration.Connected baseStep) :
    GoertzelLemma818Fibration.Connected totalStep :=
  connected_iff.2 ((lemma818Fibration_iff.1 h).connected (connected_iff.1 hbase))

theorem exists_reachable_over_base_eq :
    @GoertzelLemma818Fibration.Fibration.exists_reachable_over_base =
      @exists_reachable_over_base :=
  rfl

theorem totalReach_of_baseReach_eq :
    @GoertzelLemma818Fibration.Fibration.totalReach_of_baseReach =
      @totalReach_of_baseReach :=
  rfl

theorem totalConnected_of_baseConnected_eq :
    @GoertzelLemma818Fibration.Fibration.totalConnected_of_baseConnected =
      @totalConnected_of_baseConnected :=
  rfl

end Lemma818

/-! ## `GoertzelV24SquareLadder.SidePathLifting` -/

section SquareLadder

variable {Upper : Type u} {Lower : Type v}
  {upperStep : Upper → Upper → Prop} {lowerStep : Lower → Lower → Prop}
  {project : Upper → Lower}

/-- `SidePathLifting` is a fibration with a surjective projection. -/
theorem sidePathLifting_iff :
    GoertzelV24SquareLadder.SidePathLifting upperStep lowerStep project ↔
      Fibration upperStep lowerStep project ∧ Function.Surjective project :=
  ⟨fun h => ⟨⟨h.connectedFibres, h.liftsEdges⟩, h.surjective⟩,
    fun h => ⟨h.2, h.1.fibresConnected, h.1.liftsSteps⟩⟩

theorem fibration_of_sidePathLifting
    (h : GoertzelV24SquareLadder.SidePathLifting upperStep lowerStep project) :
    Fibration upperStep lowerStep project :=
  (sidePathLifting_iff.1 h).1

/-- `lift_path`, from `LiftsSteps.lift`. -/
theorem lift_path
    (hlift : GoertzelV24SquareLadder.SidePathLifting upperStep lowerStep project)
    {a b : Lower} (hpath : ReflTransGen lowerStep a b) :
    ∀ x : Upper, project x = a →
      ∃ y : Upper, project y = b ∧ ReflTransGen upperStep x y := by
  rintro x rfl
  exact (fibration_of_sidePathLifting hlift).liftsSteps.lift hpath

/-- `reflTransGen_of_sidePathLifting`, from `Fibration.connected`. -/
theorem reflTransGen_of_sidePathLifting
    (hlift : GoertzelV24SquareLadder.SidePathLifting upperStep lowerStep project)
    (hlower : ∀ a b : Lower, ReflTransGen lowerStep a b)
    (x y : Upper) : ReflTransGen upperStep x y :=
  (fibration_of_sidePathLifting hlift).connected hlower x y

theorem lift_path_eq :
    @GoertzelV24SquareLadder.lift_path = @lift_path :=
  rfl

theorem reflTransGen_of_sidePathLifting_eq :
    @GoertzelV24SquareLadder.reflTransGen_of_sidePathLifting =
      @reflTransGen_of_sidePathLifting :=
  rfl

variable {targetUp : Set Upper} {targetDown : Set Lower}

/-- `targetUp_nonempty_of_capped`, from `nonempty_of_surjective`. -/
theorem targetUp_nonempty_of_capped
    (hlift : GoertzelV24SquareLadder.SidePathLifting upperStep lowerStep project)
    (hword : ∀ y : Upper, project y ∈ targetDown → y ∈ targetUp)
    (hcapped : ∃ b : Lower, b ∈ targetDown) :
    ∃ y : Upper, y ∈ targetUp :=
  nonempty_of_surjective (sidePathLifting_iff.1 hlift).2 hword hcapped

/-- `side_reaches_targetUp`, from `LiftsSteps.completable_of_weaklyCompletable`.
Only step lifting is used; connected fibres and surjectivity are not. -/
theorem side_reaches_targetUp
    (hlift : GoertzelV24SquareLadder.SidePathLifting upperStep lowerStep project)
    (hword : ∀ y : Upper, project y ∈ targetDown → y ∈ targetUp)
    (hcapped : ∃ b : Lower, b ∈ targetDown)
    (hdown : (∃ b : Lower, b ∈ targetDown) →
      ∀ a : Lower, ∃ b ∈ targetDown, ReflTransGen lowerStep a b)
    (x : Upper) :
    ∃ y ∈ targetUp, ReflTransGen upperStep x y :=
  (fibration_of_sidePathLifting hlift).liftsSteps.completable_of_weaklyCompletable
    hword hcapped hdown x

theorem targetUp_nonempty_of_capped_eq :
    @GoertzelV24RouteSquareTransport.targetUp_nonempty_of_capped =
      @targetUp_nonempty_of_capped :=
  rfl

theorem side_reaches_targetUp_eq :
    @GoertzelV24RouteSquareTransport.side_reaches_targetUp =
      @side_reaches_targetUp :=
  rfl

end SquareLadder

/-! ## `GoertzelV24RouteSquareTransport.wcStar_of_both_sides` -/

section TwoSides

variable {State : Type u} {Left : Type v} {Right : Type w}

/-- `wcStar_of_both_sides`, from `completable_of_two_sides`.  Its conclusion is
`Completable step target`, and its side hypotheses are completability of each
side towards the preimage of the target. -/
theorem wcStar_of_both_sides (step : State → State → Prop) (target : Set State)
    (includeLeft : Left → State) (includeRight : Right → State)
    (leftStep : Left → Left → Prop) (rightStep : Right → Right → Prop)
    (hleftStep : ∀ a b : Left, leftStep a b → step (includeLeft a) (includeLeft b))
    (hrightStep : ∀ a b : Right,
      rightStep a b → step (includeRight a) (includeRight b))
    (hcover : ∀ x : State, (∃ a : Left, includeLeft a = x) ∨
      (∃ a : Right, includeRight a = x))
    (hleft : ∀ a : Left, ∃ b : Left, includeLeft b ∈ target ∧
      ReflTransGen leftStep a b)
    (hright : ∀ a : Right, ∃ b : Right, includeRight b ∈ target ∧
      ReflTransGen rightStep a b) :
    ∀ x : State, ∃ w ∈ target, ReflTransGen step x w :=
  completable_of_two_sides includeLeft includeRight hleftStep hrightStep hcover
    hleft hright

theorem wcStar_of_both_sides_eq :
    @GoertzelV24RouteSquareTransport.wcStar_of_both_sides =
      @wcStar_of_both_sides :=
  rfl

end TwoSides

end Instances

end Mettapedia.Combinatorics.Reconfiguration
