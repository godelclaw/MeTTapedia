import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The exact residual of two graph factors

When two subgraphs do not cover every edge of a larger graph, the omitted
edges form a third, canonical factor.  This tiny construction keeps that
factor explicit instead of hiding it behind a false two-factor coverage
premise.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SimpleGraphSupResidual

open SimpleGraph

/-- Edges of `whole` that belong to neither displayed factor. -/
def supResidual {N : Type*}
    (whole left right : SimpleGraph N) : SimpleGraph N where
  Adj x y := whole.Adj x y ∧ ¬ left.Adj x y ∧ ¬ right.Adj x y
  symm := ⟨by
    rintro x y ⟨hwhole, hleft, hright⟩
    exact ⟨hwhole.symm, fun h => hleft h.symm, fun h => hright h.symm⟩⟩
  loopless := ⟨by
    intro x hloop
    exact hloop.1.ne rfl⟩

@[simp]
theorem supResidual_adj {N : Type*}
    (whole left right : SimpleGraph N) (x y : N) :
    (supResidual whole left right).Adj x y ↔
      whole.Adj x y ∧ ¬ left.Adj x y ∧ ¬ right.Adj x y :=
  Iff.rfl

/-- Two subgraphs together with their residual recover the whole graph
exactly. -/
theorem sup_sup_supResidual_eq {N : Type*}
    (whole left right : SimpleGraph N)
    (hleft : left ≤ whole) (hright : right ≤ whole) :
    (left ⊔ right) ⊔ supResidual whole left right = whole := by
  ext x y
  change
    ((left.Adj x y ∨ right.Adj x y) ∨
        (whole.Adj x y ∧ ¬ left.Adj x y ∧ ¬ right.Adj x y)) ↔
      whole.Adj x y
  constructor
  · rintro ((hleftAdj | hrightAdj) | hresidual)
    · exact hleft hleftAdj
    · exact hright hrightAdj
    · exact hresidual.1
  · intro hwhole
    by_cases hleftAdj : left.Adj x y
    · exact Or.inl (Or.inl hleftAdj)
    by_cases hrightAdj : right.Adj x y
    · exact Or.inl (Or.inr hrightAdj)
    · exact Or.inr ⟨hwhole, hleftAdj, hrightAdj⟩

/-- The residual is empty exactly when the two displayed factors cover the
whole graph. -/
theorem supResidual_eq_bot_iff {N : Type*}
    (whole left right : SimpleGraph N) :
    supResidual whole left right = ⊥ ↔ whole ≤ left ⊔ right := by
  constructor
  · intro hempty x y hwhole
    by_contra hnot
    have hleft : ¬ left.Adj x y := by
      intro h
      exact hnot (Or.inl h)
    have hright : ¬ right.Adj x y := by
      intro h
      exact hnot (Or.inr h)
    have hresidual : (supResidual whole left right).Adj x y :=
      ⟨hwhole, hleft, hright⟩
    rw [hempty] at hresidual
    exact hresidual
  · intro hcovered
    ext x y
    constructor
    · rintro ⟨hwhole, hleft, hright⟩
      rcases hcovered hwhole with hleftAdj | hrightAdj
      · exact (hleft hleftAdj).elim
      · exact (hright hrightAdj).elim
    · intro hbot
      exact hbot.elim

/-- One component-level move through either of two displayed factors, or one
literal edge of their explicit seam factor.  This is the relational update
visible to a finite connectivity profile: the factors contribute connected
components, while the seam contributes the newly exposed turns. -/
def ThreeFactorComponentStep {N : Type*}
    (left right seam : SimpleGraph N) (x y : N) : Prop :=
  left.Reachable x y ∨ right.Reachable x y ∨ seam.Adj x y

/-- Reachability in a three-factor graph is exactly the reflexive-transitive
closure of whole-component moves in the first two factors and literal seam
moves in the third.  No determinism or interface-coverage premise is needed. -/
theorem reachable_sup_sup_iff_threeFactorComponentClosure {N : Type*}
    (left right seam : SimpleGraph N) (x y : N) :
    ((left ⊔ right) ⊔ seam).Reachable x y ↔
      Relation.ReflTransGen (ThreeFactorComponentStep left right seam) x y := by
  have hleft : left ≤ (left ⊔ right) ⊔ seam :=
    le_trans le_sup_left le_sup_left
  have hright : right ≤ (left ⊔ right) ⊔ seam :=
    le_trans le_sup_right le_sup_left
  have hseam : seam ≤ (left ⊔ right) ⊔ seam := le_sup_right
  constructor
  · intro hreachable
    have hpath :=
      (SimpleGraph.reachable_iff_reflTransGen x y).mp hreachable
    exact hpath.mono (by
      intro u v huv
      rcases (SimpleGraph.sup_adj (left ⊔ right) seam u v).mp huv with
        hfactor | hseamAdj
      · rcases (SimpleGraph.sup_adj left right u v).mp hfactor with
          hleftAdj | hrightAdj
        · exact Or.inl hleftAdj.reachable
        · exact Or.inr (Or.inl hrightAdj.reachable)
      · exact Or.inr (Or.inr hseamAdj))
  · intro hclosure
    exact Relation.ReflTransGen.trans_induction_on
      (motive := fun {u v} _ => ((left ⊔ right) ⊔ seam).Reachable u v)
      hclosure
      (fun _ => SimpleGraph.Reachable.rfl)
      (fun hstep => by
        rcases hstep with hleftReach | hrightReach | hseamAdj
        · exact hleftReach.mono hleft
        · exact hrightReach.mono hright
        · exact hseamAdj.reachable.mono hseam)
      (fun _ _ hfirst hsecond => hfirst.trans hsecond)

end GoertzelV24SimpleGraphSupResidual

end Mettapedia.GraphTheory.FourColor
