import Mettapedia.GSLT.Causality.DoCalculus.Identification

/-!
# Singleton c-components, with a descendant beside the treatment

Edges `Z → X`, `Z → Y`, `W → X`, `W → Y`, `X → Y`, and `X → D`. The latent
set is empty, so every observed c-component is a singleton. `{Z}` leaves the
`W` fork open, `{W}` leaves the `Z` fork open, and `D` is a child of `X`, so
the covariate set `{Z, W, D}` fails the back-door checker. At fuel 2,
`identify` therefore returns the parental product `parentSum`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation

inductive TruncV
  | z
  | w
  | d
  | x
  | y
  deriving DecidableEq

instance : Fintype TruncV where
  elems := {TruncV.z, TruncV.w, TruncV.d, TruncV.x, TruncV.y}
  complete := by intro vertex; cases vertex <;> simp

/-- `Z → X`, `Z → Y`, `W → X`, `W → Y`, `X → Y`, and `X → D`. -/
def truncGraph : DirectedGraph TruncV where
  edges source target :=
    (source = TruncV.z ∧ target = TruncV.x) ∨
    (source = TruncV.z ∧ target = TruncV.y) ∨
    (source = TruncV.w ∧ target = TruncV.x) ∨
    (source = TruncV.w ∧ target = TruncV.y) ∨
    (source = TruncV.x ∧ target = TruncV.y) ∨
    (source = TruncV.x ∧ target = TruncV.d)

instance : DecidableRel truncGraph.edges := fun _ _ => by
  unfold truncGraph
  infer_instance

def truncX : Finset TruncV := {TruncV.x}
def truncY : Finset TruncV := {TruncV.y}
def truncCov : Finset TruncV := {TruncV.z, TruncV.w, TruncV.d}
def truncEnum : List TruncV := [TruncV.z, TruncV.w, TruncV.d, TruncV.x, TruncV.y]

theorem trunc_parents_fail :
    parentsIn truncGraph truncX (∅ : Finset TruncV) (∅ : Finset TruncV) = false := by
  decide

theorem trunc_delete_fail :
    deleteOK truncGraph truncY truncX (∅ : Finset TruncV) = false := by
  decide

theorem trunc_no_front_mediator :
    findVertex truncEnum (fun v =>
      outsideQuery (∅ : Finset TruncV) truncY truncX v &&
        frontDoorReady truncGraph truncX {v} truncY) = none := by
  decide

theorem trunc_no_napkin :
    findNapkin truncGraph truncEnum (∅ : Finset TruncV) truncY truncX = none := by
  decide

theorem trunc_no_singleton_backdoor :
    findVertex truncEnum (fun v =>
      outsideQuery (∅ : Finset TruncV) truncY truncX v &&
        backDoorReady truncGraph truncX {v} truncY) = none := by
  decide

/-- `X` reaches `Y`. -/
theorem trunc_misses_forward :
    missesForward truncGraph truncX (truncY ∪ (∅ : Finset TruncV)) = false := by
  decide

theorem trunc_no_bow :
    bowPair truncGraph truncEnum (∅ : Finset TruncV) truncY truncX = none := by
  decide

theorem trunc_covariates :
    covariateSet (∅ : Finset TruncV) truncY truncX (∅ : Finset TruncV) = truncCov := by
  unfold covariateSet
  ext vertex
  cases vertex <;> simp [truncX, truncY, truncCov]

/-- `D` is a child of `X`, so `{Z, W, D}` fails rule 3 of the back door. -/
theorem trunc_full_backdoor_fails :
    backDoorReady truncGraph truncX truncCov truncY = false := by
  decide

theorem trunc_outcome_hedge :
    componentHedge truncGraph truncEnum (∅ : Finset TruncV) truncY truncX = none := by
  decide

theorem trunc_observed_hedge :
    componentHedge truncGraph truncEnum (∅ : Finset TruncV)
      (Finset.univ \ (∅ : Finset TruncV)) truncX = none := by
  decide

theorem trunc_singletons :
    allSingletonComponents truncGraph (∅ : Finset TruncV) = true := by
  decide

/-- Fuel 2 reaches `unresolved`, and every observed c-component is a singleton,
so the answer is the do-free parental product. -/
theorem trunc_identify_is_parent_sum :
    identify truncGraph 2 truncEnum (∅ : Finset TruncV) truncY truncX (∅ : Finset TruncV) =
      .doFree (parentSum truncGraph truncEnum (∅ : Finset TruncV) truncY truncX) ∧
    doFree (parentSum truncGraph truncEnum (∅ : Finset TruncV) truncY truncX) = true := by
  refine ⟨?_, ?_⟩
  · unfold identify
    have hparents :
        ¬ parentsIn truncGraph truncX (∅ : Finset TruncV) (∅ : Finset TruncV) = true := by
      simp [trunc_parents_fail]
    have hdelete :
        ¬ deleteOK truncGraph truncY truncX (∅ : Finset TruncV) = true := by
      simp [trunc_delete_fail]
    split
    · rename_i hzero
      cases hzero
    · rw [if_neg hparents, if_neg hdelete, if_pos (rfl : (∅ : Finset TruncV) = ∅)]
      rw [trunc_no_front_mediator, trunc_no_napkin, trunc_no_singleton_backdoor]
      have hmiss :
          ¬ missesForward truncGraph truncX (truncY ∪ (∅ : Finset TruncV)) = true := by
        rw [trunc_misses_forward]
        decide
      rw [if_neg hmiss, trunc_no_bow]
      unfold identifyRest
      rw [if_neg hmiss, if_pos (rfl : (∅ : Finset TruncV) = ∅)]
      have hready :
          ¬ backDoorReady truncGraph truncX
              (covariateSet (∅ : Finset TruncV) truncY truncX (∅ : Finset TruncV))
              truncY = true := by
        rw [trunc_covariates, trunc_full_backdoor_fails]
        decide
      rw [if_neg hready]
      unfold unresolved
      rw [trunc_outcome_hedge, trunc_observed_hedge, if_pos trunc_singletons]
  · decide

end Mettapedia.GSLT.Causality.DoCalculus
