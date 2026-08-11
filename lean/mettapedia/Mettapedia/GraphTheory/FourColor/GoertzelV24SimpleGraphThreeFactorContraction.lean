import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphSupResidual
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareGraphComposition

/-!
# Finite-interface contraction for three graph factors

Reachability in a union of three graphs can be computed on a selected
interface whenever every genuine switch between two factors occurs at a
selected vertex.  This is the three-factor analogue of
`reachable_sup_iff_subtype_componentClosure` and is tailored to a corridor
step split into an old prefix, a new Cell, and an explicit residual seam.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SimpleGraphThreeFactorContraction

open SimpleGraph

/-- One whole-component move through any of three graph factors, restricted
to a selected finite interface. -/
def SelectedThreeFactorComponentStep {N : Type*}
    (first second third : SimpleGraph N) (Selected : N → Prop)
    (left right : Subtype Selected) : Prop :=
  first.Reachable left right ∨
    second.Reachable left right ∨
    third.Reachable left right

/-- If every nontrivial switch between any two factors occurs in `Selected`,
then reachability in their union is exactly the closure of their component
relations on the selected subtype. -/
theorem reachable_sup_sup_iff_subtype_threeFactorComponentClosure
    {N : Type*} (first second third : SimpleGraph N)
    (Selected : N → Prop) (start finish : N)
    (hstart : Selected start) (hfinish : Selected finish)
    (hswitchFirstSecond : ∀ {x middle y}, x ≠ middle → middle ≠ y →
      first.Reachable x middle → second.Reachable middle y →
        Selected middle)
    (hswitchFirstThird : ∀ {x middle y}, x ≠ middle → middle ≠ y →
      first.Reachable x middle → third.Reachable middle y →
        Selected middle)
    (hswitchSecondThird : ∀ {x middle y}, x ≠ middle → middle ≠ y →
      second.Reachable x middle → third.Reachable middle y →
        Selected middle) :
    ((first ⊔ second) ⊔ third).Reachable start finish ↔
      Relation.ReflTransGen
        (SelectedThreeFactorComponentStep first second third Selected)
        ⟨start, hstart⟩ ⟨finish, hfinish⟩ := by
  have hswitchFirstSecondThird : ∀ {x middle y},
      x ≠ middle → middle ≠ y →
        (first ⊔ second).Reachable x middle →
        third.Reachable middle y → Selected middle := by
    intro x middle y hx hy hfirstSecond hthird
    have hmiddleSupport : middle ∈ (first ⊔ second).support :=
      SimpleGraph.mem_support_of_reachable hx.symm hfirstSecond.symm
    rcases (SimpleGraph.mem_support (first ⊔ second)).1 hmiddleSupport with
      ⟨neighbor, hmiddleNeighbor⟩
    rcases (SimpleGraph.sup_adj first second middle neighbor).1
        hmiddleNeighbor with hfirst | hsecond
    · exact hswitchFirstThird hfirst.ne.symm hy
        hfirst.symm.reachable hthird
    · exact hswitchSecondThird hsecond.ne.symm hy
        hsecond.symm.reachable hthird
  rw [reachable_sup_iff_subtype_componentClosure
    (first ⊔ second) third Selected start finish hstart hfinish
      hswitchFirstSecondThird]
  constructor
  · intro hclosure
    exact Relation.ReflTransGen.trans_induction_on
      (motive := fun {left right} _ =>
        Relation.ReflTransGen
          (SelectedThreeFactorComponentStep first second third Selected)
          left right)
      hclosure
      (fun _ => Relation.ReflTransGen.refl)
      (fun {left right} hstep => by
        rcases hstep with hfirstSecond | hthird
        · have hfirstSecondClosure :=
            (reachable_sup_iff_subtype_componentClosure
              first second Selected left.1 right.1 left.2 right.2
                hswitchFirstSecond).1
              hfirstSecond
          exact hfirstSecondClosure.mono (by
            intro left right hfactor
            exact hfactor.elim Or.inl (fun h => Or.inr (Or.inl h)))
        · exact Relation.ReflTransGen.single (Or.inr (Or.inr hthird)))
      (fun _ _ hleft hright => hleft.trans hright)
  · intro hclosure
    exact Relation.ReflTransGen.trans_induction_on
      (motive := fun {left right} _ =>
        Relation.ReflTransGen
          (fun x y : Subtype Selected =>
            (first ⊔ second).Reachable x y ∨ third.Reachable x y)
          left right)
      hclosure
      (fun _ => Relation.ReflTransGen.refl)
      (fun hstep => by
        rcases hstep with hfirst | hsecond | hthird
        · exact Relation.ReflTransGen.single
            (Or.inl (hfirst.mono le_sup_left))
        · exact Relation.ReflTransGen.single
            (Or.inl (hsecond.mono le_sup_right))
        · exact Relation.ReflTransGen.single (Or.inr hthird))
      (fun _ _ hleft hright => hleft.trans hright)

end GoertzelV24SimpleGraphThreeFactorContraction

end Mettapedia.GraphTheory.FourColor
