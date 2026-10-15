import Mettapedia.GSLT.Causality.DoCalculus.Derivation
import Mettapedia.GSLT.Causality.DoCalculus.IdentifyDeriv

/-!
# One attempt: a do-free `identify` answer as a `Deriv`

The open goal is that every `.doFree` answer of `identify` is the end of a
`Deriv` whose `gDenote` agrees under the positivity that derivation collects.
This file is the one attempt. It closes the `A → B` instance and does not
close the quantifier.

On that graph `identify` returns `exchangeResult`, and `Deriv.rule2` at the
fragment's own sets asks for a checker profile whose outcome overlaps the
conditioning. That profile is false (`gap_parents_accept_rule2_refuses`).
The outcome is already inside the conditioning, so the two unions do not
mention it. Rule 2 read at an empty outcome has the same ends, and that
profile's checker accepts. `gap_identify_doFree_is_deriv` is that instance.

The quantifier over fuel, an enumeration, and the five arguments of
`identify` does not follow. A `parentsIn` success is not the checker premise
of `Deriv.rule2` on those sets, and the front-door, back-door, napkin, and
recursive answers are not this exchange. The attempt stops at this instance.
The unproved goal, with `graph` acyclic and the scalar type of `gDenote`
fixed as in `Derivation`, is:

```
∀ (fuel : Nat) (enum : List V) (L outcome intervention conditioning : Finset V)
  {expr : MassExpr V},
  identify graph fuel enum L outcome intervention conditioning = .doFree expr →
  ∃ step : Deriv graph
    (.cond intervention (intervention ∪ outcome ∪ conditioning)
      (intervention ∪ conditioning)) expr,
  ∀ cpt anchor, Positive graph hAcyclic step cpt anchor →
    gDenote graph hAcyclic cpt anchor
      (.cond intervention (intervention ∪ outcome ∪ conditioning)
        (intervention ∪ conditioning)) =
    gDenote graph hAcyclic cpt anchor expr
```
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation

/-- Rank along the single arrow `A → B`. -/
def gapRank : GapV → Nat
  | .a => 0
  | .b => 1

lemma gap_edge_increases {u v : GapV} (h : gapGraph.edges u v) :
    gapRank u < gapRank v := by
  cases u <;> cases v <;> simp [gapGraph, gapRank] at h ⊢

lemma gap_reachable_rank {u v : GapV} (h : gapGraph.Reachable u v) :
    gapRank u ≤ gapRank v := by
  induction h with
  | refl => exact le_rfl
  | step hedge _ ih => exact le_trans (Nat.le_of_lt (gap_edge_increases hedge)) ih

/-- `A → B` has no directed cycle. -/
lemma gapAcyclic : gapGraph.IsAcyclic := by
  intro v ⟨src, hedge, hreach⟩
  exact (lt_irrefl _) <|
    lt_of_lt_of_le (gap_edge_increases hedge) (gap_reachable_rank hreach)

/-- Rule 2 at an empty outcome: `{B}` against `{A}` in the mutilated graph. -/
theorem gap_empty_outcome_rule2_accepts :
    FiniteDSeparation.check (gout gapGraph (∅ : Finset GapV) gapB)
      (rule2Profile (∅ : Finset GapV) gapB gapA) = true := by
  decide

/-- The query `identify` answers on `A → B`. -/
def gapQuery : MassExpr GapV :=
  .cond gapB (gapB ∪ gapA ∪ gapA) (gapB ∪ gapA)

/-- Rule 2's source at an empty outer intervention and an empty outcome. -/
def gapRule2Source : MassExpr GapV :=
  .cond ((∅ : Finset GapV) ∪ gapB)
    ((∅ : Finset GapV) ∪ (∅ : Finset GapV) ∪ gapB ∪ gapA)
    ((∅ : Finset GapV) ∪ gapB ∪ gapA)

/-- Rule 2's target at those same sets. -/
def gapRule2Target : MassExpr GapV :=
  .cond (∅ : Finset GapV)
    ((∅ : Finset GapV) ∪ (∅ : Finset GapV) ∪ gapB ∪ gapA)
    ((∅ : Finset GapV) ∪ gapB ∪ gapA)

theorem gapQuery_eq_rule2Source : gapQuery = gapRule2Source := by
  decide

theorem gapResult_eq_rule2Target :
    exchangeResult gapA gapB gapA = gapRule2Target := by
  decide

/-- The empty-outcome exchange, whose checker premise holds. -/
def gapExchangeStep : Deriv gapGraph gapRule2Source gapRule2Target :=
  .rule2 (∅ : Finset GapV) (∅ : Finset GapV) gapB gapA gap_empty_outcome_rule2_accepts

/-- The query and the do-free exchange are the ends of that step. -/
def gapDoFreeDeriv :
    Deriv gapGraph gapQuery (exchangeResult gapA gapB gapA) :=
  .rewriteEq gapQuery_eq_rule2Source.symm gapResult_eq_rule2Target.symm gapExchangeStep

section Denote

variable {β : Type} [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
  [MeasurableSingletonClass β] [StandardBorelSpace β] [StandardBorelSpace (GapV → β)]

/-- On `A → B`, `identify` returns the do-free exchange, and that answer is
the end of a `Deriv`. Positivity of the step makes the two `gDenote`s agree. -/
theorem gap_identify_doFree_is_deriv :
    identify gapGraph 1 [GapV.a, GapV.b] (∅ : Finset GapV) gapA gapB gapA =
      .doFree (exchangeResult gapA gapB gapA) ∧
    ∃ step : Deriv gapGraph gapQuery (exchangeResult gapA gapB gapA),
      ∀ (cpt : (network (β := β) gapGraph gapAcyclic).DiscreteCPT) (anchor : GapV → β),
        Positive gapGraph gapAcyclic step cpt anchor →
          gDenote gapGraph gapAcyclic cpt anchor gapQuery =
            gDenote gapGraph gapAcyclic cpt anchor (exchangeResult gapA gapB gapA) := by
  refine ⟨gap_identify_exchanges, gapDoFreeDeriv, ?_⟩
  intro cpt anchor hpos
  exact deriv_gDenote gapGraph gapAcyclic gapDoFreeDeriv cpt anchor hpos

end Denote

end Mettapedia.GSLT.Causality.DoCalculus
