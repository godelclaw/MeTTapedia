import Mettapedia.GSLT.Causality.DoCalculus.CheckerRules
import Mettapedia.GSLT.Causality.DoCalculus.IdentifyDeriv

/-!
# The parent test is rule 2 under a wider checker

On `A → B`, `parentsIn` makes `idFragment` return the do-free exchange while
rule 2's d-separation checker, read at the fragment's own outcome, is false.
`exchangeReady` accepts that parent test or the checker. Its soundness is
`exchange_ready_sound`: the parent disjunct is `id_exchange_sound`, and the
checker disjunct is `rule2_of_check`. This is not an eighth authored rule.

The same ends are a `Deriv` when rule 2 is read at an empty outcome, because
the outcome is already in the conditioning. That instance is
`gap_identify_doFree_is_deriv`. It does not prove the quantifier over every
`.doFree` answer of `identify`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation

variable {V : Type} [Fintype V] [DecidableEq V]
variable (graph : DirectedGraph V) [DecidableRel graph.edges]

/-- Rule 2's exchange, accepted by the parent test or by the d-separation checker. -/
def exchangeReady (outcome bound conditioning : Finset V) : Bool :=
  parentsIn graph bound (∅ : Finset V) conditioning ||
    FiniteDSeparation.check (gout graph (∅ : Finset V) bound)
      (rule2Profile outcome bound ((∅ : Finset V) ∪ conditioning))

omit [Fintype V] [DecidableEq V] graph [DecidableRel graph.edges] in
/-- On `A → B` the parent test fires, the narrow checker does not, and
`idFragment` returns the do-free exchange. -/
theorem gap_parent_test_is_rule2_under_exchangeReady :
    exchangeReady gapGraph gapA gapB gapA = true ∧
      FiniteDSeparation.check (gout gapGraph (∅ : Finset GapV) gapB)
        (rule2Profile gapA gapB ((∅ : Finset GapV) ∪ gapA)) = false ∧
      idFragment gapGraph gapA gapB gapA =
        .doFree (exchangeResult gapA gapB gapA) := by
  refine ⟨?_, gap_parents_accept_rule2_refuses.2, ?_⟩
  · simp [exchangeReady, gap_parents_accept_rule2_refuses.1]
  · simp [idFragment, gap_parents_accept_rule2_refuses.1]

variable (hAcyclic : graph.IsAcyclic)
variable {β : Type} [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
  [MeasurableSingletonClass β] [StandardBorelSpace β]

theorem exchange_ready_sound
    (outcome bound conditioning : Finset V)
    (hready : exchangeReady graph outcome bound conditioning = true)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β)
    (hpos : truncSlice graph hAcyclic cpt (doFinset (∅ : Finset V) anchor)
      (bound ∪ conditioning) anchor ≠ 0) :
    gDenote graph hAcyclic cpt anchor (exchangeSource outcome bound conditioning) =
      gDenote graph hAcyclic cpt anchor
        (exchangeResult outcome bound conditioning) := by
  by_cases hparents : parentsIn graph bound (∅ : Finset V) conditioning = true
  · exact (id_exchange_sound graph hAcyclic outcome bound conditioning
      hparents cpt anchor hpos).2
  · have hcheck :
        FiniteDSeparation.check (gout graph (∅ : Finset V) bound)
          (rule2Profile outcome bound ((∅ : Finset V) ∪ conditioning)) = true := by
      simpa [exchangeReady, hparents, Bool.or_false] using hready
    have hposRule :
        truncSlice graph hAcyclic cpt (doFinset (∅ : Finset V) anchor)
          ((∅ : Finset V) ∪ bound ∪ conditioning) anchor ≠ 0 := by
      simpa [Finset.empty_union] using hpos
    have hratio :=
      rule2_of_check (β := β) graph hAcyclic cpt
        (X := (∅ : Finset V)) (Y := outcome) (Z := bound) (W := conditioning)
        anchor anchor anchor (fun _ _ => rfl) hcheck hposRule
    have hmerge : mergeAssign (∅ : Finset V) anchor anchor = anchor := by
      funext vertex
      unfold mergeAssign
      split_ifs <;> rfl
    simpa [exchangeSource, exchangeResult, gDenote, hmerge, Finset.empty_union] using hratio

end Mettapedia.GSLT.Causality.DoCalculus
