import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphThreeFactorContraction

/-!
# Selected anchors for components of a three-factor union

Finite-interface contraction computes reachability between selected switch
vertices.  A factor-fragment decoder also needs the converse coverage fact:
when a selected start reaches a vertex supported by the first factor, the
terminal first-factor component contains a selected switch vertex.

The proof follows the union path backwards.  As long as it uses first-factor
edges it stays in the terminal first component.  A first step belonging to the
second or third factor would make the junction a genuine factor switch, hence
selected by hypothesis.  This generic lemma is the anchor-existence input for
the literal facial rebase; it contains no Four-Color-specific geometry.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SimpleGraphThreeFactorSelectedAnchor

open GoertzelV24SimpleGraphThreeFactorContraction
open SimpleGraph

/-- A selected-to-terminal path in a three-factor union meets the terminal
component of the first factor at a selected anchor. -/
theorem exists_selected_firstFactor_anchor
    {N : Type*} (first second third : SimpleGraph N)
    (Selected : N → Prop) (start finish : N)
    (hstart : Selected start)
    (hfinishSupport : finish ∈ first.support)
    (hswitchFirstSecond : ∀ {x middle y}, x ≠ middle → middle ≠ y →
      first.Reachable x middle → second.Reachable middle y →
        Selected middle)
    (hswitchFirstThird : ∀ {x middle y}, x ≠ middle → middle ≠ y →
      first.Reachable x middle → third.Reachable middle y →
        Selected middle)
    (hreachable : ((first ⊔ second) ⊔ third).Reachable start finish) :
    ∃ anchor, Selected anchor ∧ first.Reachable anchor finish := by
  by_contra hnone
  push Not at hnone
  have hpath :=
    (SimpleGraph.reachable_iff_reflTransGen start finish).1 hreachable
  have hfirstReachable : first.Reachable start finish :=
    Relation.ReflTransGen.head_induction_on
      (motive := fun left _ => first.Reachable left finish)
      hpath (SimpleGraph.Reachable.refl finish) (by
        intro left middle hstep _ htail
        rcases (SimpleGraph.sup_adj (first ⊔ second) third left middle).1
            hstep with hfirstSecond | hthird
        · rcases (SimpleGraph.sup_adj first second left middle).1
              hfirstSecond with hfirst | hsecond
          · exact hfirst.reachable.trans htail
          · have hmiddleFirstSupport : middle ∈ first.support := by
              by_cases hmiddle : middle = finish
              · simpa [hmiddle] using hfinishSupport
              · exact SimpleGraph.mem_support_of_reachable hmiddle htail
            rcases (SimpleGraph.mem_support first).1 hmiddleFirstSupport with
              ⟨neighbor, hmiddleNeighbor⟩
            have hselected : Selected middle :=
              hswitchFirstSecond hmiddleNeighbor.ne.symm hsecond.ne.symm
                hmiddleNeighbor.symm.reachable hsecond.symm.reachable
            exact False.elim ((hnone middle hselected) htail)
        · have hmiddleFirstSupport : middle ∈ first.support := by
            by_cases hmiddle : middle = finish
            · simpa [hmiddle] using hfinishSupport
            · exact SimpleGraph.mem_support_of_reachable hmiddle htail
          rcases (SimpleGraph.mem_support first).1 hmiddleFirstSupport with
            ⟨neighbor, hmiddleNeighbor⟩
          have hselected : Selected middle :=
            hswitchFirstThird hmiddleNeighbor.ne.symm hthird.ne.symm
              hmiddleNeighbor.symm.reachable hthird.symm.reachable
          exact False.elim ((hnone middle hselected) htail))
  exact (hnone start hstart) hfirstReachable

/-- Membership-sensitive form of `exists_selected_firstFactor_anchor`.  The
first factor may contain an isolated terminal which is absent from graph
support; an explicit `FirstPresent` predicate records that vertex membership.
This is the form needed for singleton regional face fragments. -/
theorem exists_selected_firstFactor_anchor_of_present
    {N : Type*} (first second third : SimpleGraph N)
    (FirstPresent Selected : N → Prop) (start finish : N)
    (hstart : Selected start)
    (hfinishPresent : FirstPresent finish)
    (hfirstReachablePresent : ∀ {left right}, FirstPresent right →
      first.Reachable left right → FirstPresent left)
    (hswitchFirstSecond : ∀ {middle right}, FirstPresent middle →
      middle ≠ right → second.Reachable middle right → Selected middle)
    (hswitchFirstThird : ∀ {middle right}, FirstPresent middle →
      middle ≠ right → third.Reachable middle right → Selected middle)
    (hreachable : ((first ⊔ second) ⊔ third).Reachable start finish) :
    ∃ anchor, Selected anchor ∧ first.Reachable anchor finish := by
  by_contra hnone
  push Not at hnone
  have hpath :=
    (SimpleGraph.reachable_iff_reflTransGen start finish).1 hreachable
  have hfirstReachable : first.Reachable start finish :=
    Relation.ReflTransGen.head_induction_on
      (motive := fun left _ => first.Reachable left finish)
      hpath (SimpleGraph.Reachable.refl finish) (by
        intro left middle hstep _ htail
        rcases (SimpleGraph.sup_adj (first ⊔ second) third left middle).1
            hstep with hfirstSecond | hthird
        · rcases (SimpleGraph.sup_adj first second left middle).1
              hfirstSecond with hfirst | hsecond
          · exact hfirst.reachable.trans htail
          · have hmiddlePresent :=
              hfirstReachablePresent hfinishPresent htail
            have hselected : Selected middle :=
              hswitchFirstSecond hmiddlePresent hsecond.ne.symm
                hsecond.symm.reachable
            exact False.elim ((hnone middle hselected) htail)
        · have hmiddlePresent :=
            hfirstReachablePresent hfinishPresent htail
          have hselected : Selected middle :=
            hswitchFirstThird hmiddlePresent hthird.ne.symm
              hthird.symm.reachable
          exact False.elim ((hnone middle hselected) htail))
  exact (hnone start hstart) hfirstReachable

end GoertzelV24SimpleGraphThreeFactorSelectedAnchor

end Mettapedia.GraphTheory.FourColor
