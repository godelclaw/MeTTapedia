import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareLadder
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareWCStarRegression

/-!
# Route-specific square transport from cap nonemptiness

Generic square transport for an arbitrary target is false.  The route's own
target is not arbitrary: a target word is exactly the restriction of a
colouring after the fixed completion cap is restored, and that extra fact is
what closes the square rung.

The argument, with the two premises the source names:

* **Capped colourability.**  Each capped reduction is Tait-colourable, being
  four vertices smaller than a closed instance whose minimality is available.
  Restricting such a colouring to the reduction leaves a colouring whose
  boundary word extends across the cap — by the colouring just removed — so
  the reduction's target set is nonempty on *both* sides.
* **Downstairs WC\*.**  The tangle induction supplies `WC*` for each
  reduction against the same target, in its loaded form: given that some
  colouring of the reduction has a target word, every colouring reaches one.

Given those, one colouring of the ambient tangle lands in some side, projects
to the reduction, reaches a target downstairs, and the path lifts.  Projection
changes only the square and preserves every ordered boundary edge, so a lift
of a target is a target.  The proviso is met because surjectivity lifts a
downstairs target to an upstairs one.

The whole path stays inside the side it started in.  No cross-side migration
and no all-equal overlap is used anywhere, which is exactly why the generic
counterexample does not touch this: there one side has an empty target set, so
its capped-colourability premise fails, and the vacuous truth of `WC*` on that
side cannot manufacture a target.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RouteSquareTransport

open GoertzelV24SquareLadder

section OneSide

variable {Upper Lower : Type*} {upperStep : Upper → Upper → Prop}
  {lowerStep : Lower → Lower → Prop} {project : Upper → Lower}
  {targetUp : Set Upper} {targetDown : Set Lower}

/-- **The proviso.**  Capped colourability gives the reduction a target state,
and surjectivity of the projection lifts it, so the ambient target is nonempty
too. -/
theorem targetUp_nonempty_of_capped
    (hlift : SidePathLifting upperStep lowerStep project)
    (hword : ∀ y : Upper, project y ∈ targetDown → y ∈ targetUp)
    (hcapped : ∃ b : Lower, b ∈ targetDown) :
    ∃ y : Upper, y ∈ targetUp := by
  obtain ⟨b, hb⟩ := hcapped
  obtain ⟨y, hy⟩ := hlift.surjective b
  exact ⟨y, hword y (hy ▸ hb)⟩

/-- **One side reaches the target without leaving itself.**  Project, use
downstairs `WC*` to reach a target of the reduction, and lift the path.  The
lifted endpoint projects to a target, hence is one. -/
theorem side_reaches_targetUp
    (hlift : SidePathLifting upperStep lowerStep project)
    (hword : ∀ y : Upper, project y ∈ targetDown → y ∈ targetUp)
    (hcapped : ∃ b : Lower, b ∈ targetDown)
    (hdown : (∃ b : Lower, b ∈ targetDown) →
      ∀ a : Lower, ∃ b ∈ targetDown, Relation.ReflTransGen lowerStep a b)
    (x : Upper) :
    ∃ y ∈ targetUp, Relation.ReflTransGen upperStep x y := by
  obtain ⟨b, hb, hpath⟩ := hdown hcapped (project x)
  obtain ⟨y, hy, hxy⟩ := lift_path hlift hpath x rfl
  exact ⟨y, hword y (hy ▸ hb), hxy⟩

end OneSide

/-! ## Assembling the two sides -/

section TwoSides

variable {State Left Right : Type*} (step : State → State → Prop)
  (target : Set State) (includeLeft : Left → State) (includeRight : Right → State)
  (leftStep : Left → Left → Prop) (rightStep : Right → Right → Prop)

/-- **Route-specific square transport.**  With every ambient colouring lying in
one of the two lifted sides, and each side reaching a target inside itself, the
ambient tangle satisfies `WC*`.  The witnessing path is the image of a path
that never left its starting side. -/
theorem wcStar_of_both_sides
    (hleftStep : ∀ a b : Left, leftStep a b → step (includeLeft a) (includeLeft b))
    (hrightStep : ∀ a b : Right,
      rightStep a b → step (includeRight a) (includeRight b))
    (hcover : ∀ x : State, (∃ a : Left, includeLeft a = x) ∨
      (∃ a : Right, includeRight a = x))
    (hleft : ∀ a : Left, ∃ b : Left, includeLeft b ∈ target ∧
      Relation.ReflTransGen leftStep a b)
    (hright : ∀ a : Right, ∃ b : Right, includeRight b ∈ target ∧
      Relation.ReflTransGen rightStep a b) :
    ∀ x : State, ∃ w ∈ target, Relation.ReflTransGen step x w := by
  intro x
  rcases hcover x with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · obtain ⟨b, hb, hpath⟩ := hleft a
    exact ⟨includeLeft b, hb,
      Relation.ReflTransGen.lift includeLeft (fun {u v} h => hleftStep u v h) hpath⟩
  · obtain ⟨b, hb, hpath⟩ := hright a
    exact ⟨includeRight b, hb,
      Relation.ReflTransGen.lift includeRight (fun {u v} h => hrightStep u v h) hpath⟩

end TwoSides

/-! ## Why the generic counterexample is harmless

In the refuting specimen the first reduction has no target colouring at all.
Its capped-colourability premise therefore fails, and the vacuous truth of
`WC*` on that side cannot manufacture a target.  Target nonemptiness in the
route comes from the smaller capped instance, never from an all-equal square
state. -/

/-- The generic counterexample's first reduction carries no target state, so
the capped-colourability premise of the route theorem fails on it. -/
theorem genericCounterexample_capped_premise_fails :
    GoertzelV24SquareWCStarRegression.reductionZeroTargetCountsByClass.sum = 0 := by
  decide

/-- Its second reduction does carry targets, so the failure is one-sided: the
specimen is exactly the sharpness case where one side's target set is
empty. -/
theorem genericCounterexample_other_side_bears_target :
    0 < GoertzelV24SquareWCStarRegression.reductionOneTargetCountsByClass.sum := by
  decide

end GoertzelV24RouteSquareTransport

end Mettapedia.GraphTheory.FourColor
