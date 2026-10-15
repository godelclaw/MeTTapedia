import Mettapedia.GSLT.Causality.DoCalculus.Identification

/-!
# Two observed forks into one treatment

`Z → X`, `Z → Y`, `W → X`, `W → Y`, and `X → Y`, with no latent vertex.
Neither `{Z}` nor `{W}` blocks both forks. The identified form of `P(Y | do(X))`
is the back-door sum `Σ_{z,w} P(Y | X, z, w) P(z, w)`, which is `backDoorShape`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation

inductive AdjustV
  | x
  | y
  | z
  | w
  deriving DecidableEq

instance : Fintype AdjustV where
  elems := {AdjustV.x, AdjustV.y, AdjustV.z, AdjustV.w}
  complete := by intro vertex; cases vertex <;> simp

/-- `Z → X ← W`, both also pointing at `Y`, and `X → Y`. -/
def adjustGraph : DirectedGraph AdjustV where
  edges source target :=
    (source = AdjustV.z ∧ target = AdjustV.x) ∨
    (source = AdjustV.z ∧ target = AdjustV.y) ∨
    (source = AdjustV.w ∧ target = AdjustV.x) ∨
    (source = AdjustV.w ∧ target = AdjustV.y) ∨
    (source = AdjustV.x ∧ target = AdjustV.y)

instance : DecidableRel adjustGraph.edges := fun _ _ => by
  unfold adjustGraph
  infer_instance

def adjustX : Finset AdjustV := {AdjustV.x}
def adjustY : Finset AdjustV := {AdjustV.y}
def adjustCov : Finset AdjustV := {AdjustV.z, AdjustV.w}
def adjustEnum : List AdjustV := [AdjustV.x, AdjustV.z, AdjustV.w, AdjustV.y]

theorem adjust_parents_fail :
    parentsIn adjustGraph adjustX (∅ : Finset AdjustV) (∅ : Finset AdjustV) = false := by
  decide

theorem adjust_delete_fail :
    deleteOK adjustGraph adjustY adjustX (∅ : Finset AdjustV) = false := by
  decide

theorem adjust_no_front_mediator :
    findVertex adjustEnum (fun v =>
      outsideQuery (∅ : Finset AdjustV) adjustY adjustX v &&
        frontDoorReady adjustGraph adjustX {v} adjustY) = none := by
  decide

theorem adjust_no_napkin :
    findNapkin adjustGraph adjustEnum (∅ : Finset AdjustV) adjustY adjustX = none := by
  decide

theorem adjust_no_singleton_backdoor :
    findVertex adjustEnum (fun v =>
      outsideQuery (∅ : Finset AdjustV) adjustY adjustX v &&
        backDoorReady adjustGraph adjustX {v} adjustY) = none := by
  decide

theorem adjust_no_bow :
    bowPair adjustGraph adjustEnum (∅ : Finset AdjustV) adjustY adjustX = none := by
  decide

theorem adjust_misses_forward :
    missesForward adjustGraph adjustX (adjustY ∪ (∅ : Finset AdjustV)) = false := by
  decide

theorem adjust_backdoor_ready :
    backDoorReady adjustGraph adjustX adjustCov adjustY = true := by
  decide

theorem adjust_covariates :
    covariateSet (∅ : Finset AdjustV) adjustY adjustX (∅ : Finset AdjustV) = adjustCov := by
  unfold covariateSet
  ext vertex
  cases vertex <;> simp [adjustX, adjustY, adjustCov]

/-- `P(Y | do(X))` is the sum over both forks, not the conditional `P(Y | X, Z, W)`. -/
theorem adjust_identify_sums :
    identify adjustGraph 4 adjustEnum (∅ : Finset AdjustV) adjustY adjustX (∅ : Finset AdjustV) =
      .doFree (backDoorShape adjustX adjustY adjustCov) ∧
    backDoorShape adjustX adjustY adjustCov ≠
      exchangeResult adjustY (adjustX ∪ adjustCov) (∅ : Finset AdjustV) := by
  refine ⟨?_, ?_⟩
  · unfold identify
    have hparents : ¬ parentsIn adjustGraph adjustX (∅ : Finset AdjustV) (∅ : Finset AdjustV) = true := by
      simp [adjust_parents_fail]
    have hdelete : ¬ deleteOK adjustGraph adjustY adjustX (∅ : Finset AdjustV) = true := by
      simp [adjust_delete_fail]
    split
    · rename_i hzero
      cases hzero
    · rw [if_neg hparents, if_neg hdelete, if_pos (rfl : (∅ : Finset AdjustV) = ∅)]
      rw [adjust_no_front_mediator, adjust_no_napkin, adjust_no_singleton_backdoor]
      have hmiss :
          ¬ missesForward adjustGraph adjustX (adjustY ∪ (∅ : Finset AdjustV)) = true := by
        rw [adjust_misses_forward]
        decide
      rw [if_neg hmiss, adjust_no_bow]
      unfold identifyRest
      rw [if_neg hmiss, if_pos (rfl : (∅ : Finset AdjustV) = ∅)]
      have hready :
          backDoorReady adjustGraph adjustX
            (covariateSet (∅ : Finset AdjustV) adjustY adjustX (∅ : Finset AdjustV))
            adjustY = true := by
        rw [adjust_covariates]
        exact adjust_backdoor_ready
      rw [if_pos hready, adjust_covariates]
  · intro h
    cases h

end Mettapedia.GSLT.Causality.DoCalculus
