import Mettapedia.GSLT.Causality.DoCalculus.BackDoorAny
import Mettapedia.GSLT.Causality.DoCalculus.Identification

/-!
# Where a do-free `identify` answer is not a checker step

`identify` returns `exchangeResult` when `parentsIn` holds, and `deleteResult`
when `deleteOK` holds. Those two Booleans are the parent condition and the
no-outside-child condition. `Deriv.rule2` and `Deriv.rule3` ask for the
d-separation checker instead. On `A → B`, with outcome `A`, intervention `B`,
and conditioning `A`, both Booleans hold and both checkers refuse. The
do-free answer is the target of that `rule2` shape, and absorbing `{B}` lands
on the `rule3` shape; both checker premises are false.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation

/-- Two vertices, with one arrow. -/
inductive GapV
  | a
  | b
  deriving DecidableEq

instance : Fintype GapV where
  elems := {GapV.a, GapV.b}
  complete := by intro vertex; cases vertex <;> simp

/-- `A → B`. -/
def gapGraph : DirectedGraph GapV where
  edges source target := source = GapV.a ∧ target = GapV.b

instance : DecidableRel gapGraph.edges := fun _ _ => by
  unfold gapGraph
  infer_instance

/-- The parent, and the conditioning vertex. -/
def gapA : Finset GapV := {GapV.a}

/-- The child, and the intervention. -/
def gapB : Finset GapV := {GapV.b}

/-- `parentsIn` holds because `A`, the only parent of `B`, is conditioned on.
Rule 2's checker refuses: the outcome `{A}` is not disjoint from that
conditioning set. -/
theorem gap_parents_accept_rule2_refuses :
    parentsIn gapGraph gapB (∅ : Finset GapV) gapA = true ∧
      FiniteDSeparation.check (gout gapGraph (∅ : Finset GapV) gapB)
        (rule2Profile gapA gapB ((∅ : Finset GapV) ∪ gapA)) = false := by
  decide

/-- `deleteOK` holds because `B` has no child and misses both `{A}` sets.
Rule 3's checker refuses for the same overlap of outcome and conditioning. -/
theorem gap_delete_accepts_rule3_refuses :
    deleteOK gapGraph gapA gapB gapA = true ∧
      FiniteDSeparation.check
        (rule3Graph gapGraph (∅ : Finset GapV) gapB gapA)
        (rule3Profile gapA gapB ((∅ : Finset GapV) ∪ gapA)) = false := by
  decide

/-- At fuel 1, `identify` takes the parent branch and returns the do-free
exchange. -/
theorem gap_identify_exchanges :
    identify gapGraph 1 [GapV.a, GapV.b] (∅ : Finset GapV) gapA gapB gapA =
      .doFree (exchangeResult gapA gapB gapA) :=
  identify_fuel_exchange gapGraph 0 [GapV.a, GapV.b] (∅ : Finset GapV)
    gapA gapB gapA gap_parents_accept_rule2_refuses.1

/-- That do-free answer and the query are the two ends of `Deriv.rule2`
with an empty outer intervention. The checker premise of that constructor
is false. -/
theorem gap_exchange_matches_rule2_ends :
    FiniteDSeparation.check (gout gapGraph (∅ : Finset GapV) gapB)
        (rule2Profile gapA gapB ((∅ : Finset GapV) ∪ gapA)) = false ∧
      exchangeResult gapA gapB gapA =
        (MassExpr.cond (∅ : Finset GapV)
          ((∅ : Finset GapV) ∪ gapA ∪ gapB ∪ gapA)
          ((∅ : Finset GapV) ∪ gapB ∪ gapA)) ∧
      (MassExpr.cond gapB (gapB ∪ gapA ∪ gapA) (gapB ∪ gapA) : MassExpr GapV) =
        MassExpr.cond ((∅ : Finset GapV) ∪ gapB)
          ((∅ : Finset GapV) ∪ gapA ∪ gapB ∪ gapA)
          ((∅ : Finset GapV) ∪ gapB ∪ gapA) := by
  refine ⟨gap_parents_accept_rule2_refuses.2, ?_, ?_⟩
  · simp only [exchangeResult]
    refine condSetEq rfl ?_ ?_
    · ext vertex
      cases vertex <;> simp [gapA, gapB]
    · ext vertex
      cases vertex <;> simp [gapA, gapB]
  · refine condSetEq ?_ ?_ ?_
    · ext vertex
      cases vertex <;> simp [gapB]
    · ext vertex
      cases vertex <;> simp [gapA, gapB]
    · ext vertex
      cases vertex <;> simp [gapA, gapB]

/-- Absorbing the intervention `{B}` out of both sides of the query lands on
the source of `Deriv.rule3`. That constructor's checker premise is false. -/
theorem gap_absorb_lands_on_false_rule3 :
    gapB ⊆ gapB ∧
      (MassExpr.cond gapB gapA gapA : MassExpr GapV) =
        MassExpr.cond ((∅ : Finset GapV) ∪ gapB)
          ((∅ : Finset GapV) ∪ gapA ∪ gapA)
          ((∅ : Finset GapV) ∪ gapA) ∧
      FiniteDSeparation.check
        (rule3Graph gapGraph (∅ : Finset GapV) gapB gapA)
        (rule3Profile gapA gapB ((∅ : Finset GapV) ∪ gapA)) = false := by
  refine ⟨fun _ hmember => hmember, ?_, gap_delete_accepts_rule3_refuses.2⟩
  refine condSetEq ?_ ?_ ?_
  · ext vertex
    cases vertex <;> simp [gapB]
  · ext vertex
    cases vertex <;> simp [gapA]
  · ext vertex
    cases vertex <;> simp [gapA]

end Mettapedia.GSLT.Causality.DoCalculus
