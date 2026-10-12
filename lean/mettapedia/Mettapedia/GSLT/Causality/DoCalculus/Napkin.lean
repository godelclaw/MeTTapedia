import Mettapedia.GSLT.Causality.DoCalculus.CheckerRules
import Mettapedia.GSLT.Causality.DoCalculus.Derivation
import Mettapedia.GSLT.Causality.DoCalculus.Identification
import Mettapedia.GSLT.Causality.DoCalculus.RegimeGraph
import Mettapedia.GSLT.Causality.DoCalculus.Soundness

/-!
# The napkin

`NapkinV` is the latent confounder `U` together with observed `W, Z, X, Y`.
The edges are `U → W → Z → X → Y` and `U → X`. `idFragment` refuses
`P(y | do(x))`. The checker premises below are Cinelli's three graphical
steps: insert `do(z)` by rule 3, exchange `do(x)` for `x` by rule 2, and
adjust the effect of `Z` by the back door at `W`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open DirectedGraph
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation

inductive NapkinV
  | u
  | w
  | z
  | x
  | y
  deriving DecidableEq

instance : Fintype NapkinV where
  elems := {NapkinV.u, NapkinV.w, NapkinV.z, NapkinV.x, NapkinV.y}
  complete := by intro v; cases v <;> simp

/-- `U → W → Z → X → Y` and `U → X`. -/
def napkinGraph : DirectedGraph NapkinV where
  edges a b :=
    (a = .u ∧ b = .w) ∨ (a = .w ∧ b = .z) ∨ (a = .z ∧ b = .x) ∨
      (a = .x ∧ b = .y) ∨ (a = .u ∧ b = .x)

instance : DecidableRel napkinGraph.edges := fun a b => by
  unfold napkinGraph
  infer_instance

def napkinRank : NapkinV → ℕ
  | .u => 0
  | .w => 1
  | .z => 2
  | .x => 3
  | .y => 4

lemma napkin_edge_increases {a b : NapkinV} (h : napkinGraph.edges a b) :
    napkinRank a < napkinRank b := by
  cases a <;> cases b <;> simp [napkinGraph, napkinRank] at h ⊢

lemma napkin_reachable_rank {a b : NapkinV} (h : napkinGraph.Reachable a b) :
    napkinRank a ≤ napkinRank b := by
  induction h with
  | refl => exact le_rfl
  | step hedge _ ih => exact le_trans (Nat.le_of_lt (napkin_edge_increases hedge)) ih

lemma napkinAcyclic : napkinGraph.IsAcyclic := by
  intro v ⟨src, hedge, hreach⟩
  exact (lt_irrefl _) <|
    lt_of_lt_of_le (napkin_edge_increases hedge) (napkin_reachable_rank hreach)

def napkinW : Finset NapkinV := {NapkinV.w}
def napkinZ : Finset NapkinV := {NapkinV.z}
def napkinX : Finset NapkinV := {NapkinV.x}
def napkinY : Finset NapkinV := {NapkinV.y}

theorem napkin_five_vertices : Fintype.card NapkinV = 5 := by
  decide

theorem napkin_instrument_edge : napkinGraph.edges NapkinV.w NapkinV.z := by
  decide

theorem napkin_fragment_refuses :
    idFragment napkinGraph napkinY napkinX (∅ : Finset NapkinV) = .refuse := by
  decide

/-- Rule 3 inserts `do(z)` beside `do(x)`: `(Y ⊥ Z | X)` after the arrows
into `X` and into `Z` are deleted. -/
theorem napkin_insert_z_checked :
    FiniteDSeparation.check
      (rule3Graph napkinGraph napkinX napkinZ (∅ : Finset NapkinV))
      (rule3Profile napkinY napkinZ (napkinX ∪ ∅)) = true := by
  decide

/-- Rule 2 exchanges `do(x)` for `x` while `do(z)` stays. -/
theorem napkin_exchange_x_checked :
    FiniteDSeparation.check (gout napkinGraph napkinZ napkinX)
      (rule2Profile napkinY napkinX (napkinZ ∪ ∅)) = true := by
  decide

/-- Back-door adjustment of `Z` on `X` through `W`. -/
theorem napkin_backdoor_x_checked :
    FiniteDSeparation.check (gout napkinGraph (∅ : Finset NapkinV) napkinZ)
      (rule2Profile napkinX napkinZ (∅ ∪ napkinW)) = true := by
  decide

/-- Back-door adjustment of `Z` on the joint `{X, Y}` through `W`. -/
theorem napkin_backdoor_joint_checked :
    FiniteDSeparation.check (gout napkinGraph (∅ : Finset NapkinV) napkinZ)
      (rule2Profile (napkinX ∪ napkinY) napkinZ (∅ ∪ napkinW)) = true := by
  decide

/-- Rule 3 deletes `do(z)` from `P(w)`. -/
theorem napkin_delete_z_from_w_checked :
    FiniteDSeparation.check
      (rule3Graph napkinGraph (∅ : Finset NapkinV) napkinZ (∅ : Finset NapkinV))
      (rule3Profile napkinW napkinZ (∅ ∪ ∅)) = true := by
  decide

lemma napkin_cond_eq {i n d i' n' d' : Finset NapkinV}
    (hi : i = i') (hn : n = n') (hd : d = d') :
    (MassExpr.cond i n d : MassExpr NapkinV) = .cond i' n' d' := by
  cases hi
  cases hn
  cases hd
  rfl

/-- `P(y | do(x))`. -/
def napkinQuery : MassExpr NapkinV :=
  .cond napkinX (napkinY ∪ napkinX) napkinX

def napkinInsertSource : MassExpr NapkinV :=
  .cond napkinX (napkinX ∪ napkinY ∪ (∅ : Finset NapkinV)) (napkinX ∪ ∅)

theorem napkinQuery_eq_insertSource : napkinQuery = napkinInsertSource := by
  unfold napkinQuery napkinInsertSource
  refine napkin_cond_eq rfl ?_ ?_
  · ext vertex; cases vertex <;> simp [napkinX, napkinY]
  · ext vertex; cases vertex <;> simp [napkinX]

/-- `P(y | do(x), do(z))`. -/
def napkinInserted : MassExpr NapkinV :=
  .cond (napkinX ∪ napkinZ) (napkinX ∪ napkinY ∪ (∅ : Finset NapkinV)) (napkinX ∪ ∅)

def insertDoZ : Deriv napkinGraph napkinInsertSource napkinInserted :=
  .rule3Rev napkinX napkinY napkinZ ∅ napkin_insert_z_checked

def napkinFromQuery : Deriv napkinGraph napkinQuery napkinInserted :=
  .rewriteEq napkinQuery_eq_insertSource.symm rfl insertDoZ

/-- `P(y | do(x), do(z))` written as the source of the rule-2 exchange. -/
def napkinExchangeSource : MassExpr NapkinV :=
  .cond (napkinZ ∪ napkinX)
    (napkinZ ∪ napkinY ∪ napkinX ∪ (∅ : Finset NapkinV))
    (napkinZ ∪ napkinX ∪ ∅)

/-- `P(y | do(x), do(z))` with `Z` written into both slices. -/
def napkinSlicesZ : MassExpr NapkinV :=
  .cond (napkinX ∪ napkinZ)
    ((napkinX ∪ napkinY ∪ (∅ : Finset NapkinV)) ∪ napkinZ)
    ((napkinX ∪ (∅ : Finset NapkinV)) ∪ napkinZ)

def putZInSlices : Deriv napkinGraph napkinInserted napkinSlicesZ :=
  .absorbRev (napkinX ∪ napkinZ) (napkinX ∪ napkinY ∪ ∅) (napkinX ∪ ∅) napkinZ
    Finset.subset_union_right

theorem napkinSlicesZ_eq_exchangeSource : napkinSlicesZ = napkinExchangeSource := by
  unfold napkinSlicesZ napkinExchangeSource
  refine napkin_cond_eq ?_ ?_ ?_
  · ext vertex; cases vertex <;> simp [napkinX, napkinZ]
  · ext vertex; cases vertex <;> simp [napkinX, napkinY, napkinZ]
  · ext vertex; cases vertex <;> simp [napkinX, napkinZ]

/-- `P(y | x, do(z))`. -/
def napkinSeenX : MassExpr NapkinV :=
  .cond napkinZ (napkinZ ∪ napkinY ∪ napkinX ∪ (∅ : Finset NapkinV))
    (napkinZ ∪ napkinX ∪ ∅)

def exchangeDoX : Deriv napkinGraph napkinExchangeSource napkinSeenX :=
  .rule2 napkinZ napkinY napkinX ∅ napkin_exchange_x_checked

/-- From `P(y | do(x))` to `P(y | x, do(z))`. -/
def napkinToSeenX : Deriv napkinGraph napkinQuery napkinSeenX :=
  .trans napkinFromQuery
    (.trans putZInSlices
      (.rewriteEq napkinSlicesZ_eq_exchangeSource.symm rfl exchangeDoX))

/-! ## The quotient and the two back doors at `W` -/

lemma napkinW_disjoint_napkinZ : Disjoint napkinW napkinZ := by
  rw [Finset.disjoint_left]
  intro vertex hw hz
  simp only [napkinW, napkinZ, Finset.mem_singleton] at hw hz
  subst hw
  cases hz

lemma napkinW_disjoint_napkinX : Disjoint napkinW napkinX := by
  rw [Finset.disjoint_left]
  intro vertex hw hx
  simp only [napkinW, napkinX, Finset.mem_singleton] at hw hx
  subst hw
  cases hx

lemma napkinW_disjoint_napkinY : Disjoint napkinW napkinY := by
  rw [Finset.disjoint_left]
  intro vertex hw hy
  simp only [napkinW, napkinY, Finset.mem_singleton] at hw hy
  subst hw
  cases hy

lemma napkinW_disjoint_joint : Disjoint napkinW (napkinX ∪ napkinY) := by
  rw [Finset.disjoint_left]
  intro vertex hw hunion
  simp only [napkinW, napkinX, napkinY, Finset.mem_singleton, Finset.mem_union] at hw hunion
  subst hw
  cases hunion with
  | inl hx => cases hx
  | inr hy => cases hy

/-- `P(out | do(z))`, the source of one back-door adjustment. -/
def napkinMarginalSource (out : Finset NapkinV) : MassExpr NapkinV :=
  .cond napkinZ (napkinZ ∪ out ∪ (∅ : Finset NapkinV)) (napkinZ ∪ ∅)

def napkinOpen (out : Finset NapkinV) (hout : Disjoint napkinW out) :
    Deriv napkinGraph (napkinMarginalSource out)
      (.sum napkinW
        (.cond napkinZ
          (napkinZ ∪ out ∪ napkinW ∪ (∅ : Finset NapkinV))
          (napkinZ ∪ ∅))) :=
  .marginalIntro napkinZ out napkinW ∅ napkinW_disjoint_napkinZ hout
    (Finset.disjoint_empty_right _)

def napkinProduct (out : Finset NapkinV) : MassExpr NapkinV :=
  .mul
    (.cond napkinZ
      (napkinZ ∪ out ∪ napkinW ∪ (∅ : Finset NapkinV))
      (napkinZ ∪ napkinW ∪ ∅))
    (.cond napkinZ (napkinZ ∪ napkinW ∪ (∅ : Finset NapkinV)) (napkinZ ∪ ∅))

def napkinChain (out : Finset NapkinV) :
    Deriv napkinGraph
      (.cond napkinZ
        (napkinZ ∪ out ∪ napkinW ∪ (∅ : Finset NapkinV))
        (napkinZ ∪ ∅))
      (napkinProduct out) :=
  .chain napkinZ out napkinW ∅

def napkinLeftNow (out : Finset NapkinV) : MassExpr NapkinV :=
  .cond napkinZ
    (napkinZ ∪ out ∪ napkinW ∪ (∅ : Finset NapkinV))
    (napkinZ ∪ napkinW ∪ ∅)

def napkinLeftRule2 (out : Finset NapkinV) : MassExpr NapkinV :=
  .cond ((∅ : Finset NapkinV) ∪ napkinZ)
    ((∅ : Finset NapkinV) ∪ out ∪ napkinZ ∪ napkinW)
    ((∅ : Finset NapkinV) ∪ napkinZ ∪ napkinW)

theorem napkinLeft_eq (out : Finset NapkinV) :
    napkinLeftNow out = napkinLeftRule2 out := by
  unfold napkinLeftNow napkinLeftRule2
  refine napkin_cond_eq ?_ ?_ ?_
  · ext vertex; cases vertex <;> simp [napkinZ]
  · ext vertex; cases vertex <;> simp [napkinZ, napkinW]
  · ext vertex; cases vertex <;> simp [napkinZ, napkinW]

/-- `P(out | z, w)`, do-free. -/
def napkinLeftObs (out : Finset NapkinV) : MassExpr NapkinV :=
  .cond (∅ : Finset NapkinV)
    ((∅ : Finset NapkinV) ∪ out ∪ napkinZ ∪ napkinW)
    ((∅ : Finset NapkinV) ∪ napkinZ ∪ napkinW)

def exchangeNapkinLeft (out : Finset NapkinV)
    (hcheck : FiniteDSeparation.check (gout napkinGraph (∅ : Finset NapkinV) napkinZ)
      (rule2Profile out napkinZ ((∅ : Finset NapkinV) ∪ napkinW)) = true) :
    Deriv napkinGraph (napkinLeftRule2 out) (napkinLeftObs out) :=
  .rule2 ∅ out napkinZ napkinW hcheck

def leftToNapkinObs (out : Finset NapkinV)
    (hcheck : FiniteDSeparation.check (gout napkinGraph (∅ : Finset NapkinV) napkinZ)
      (rule2Profile out napkinZ ((∅ : Finset NapkinV) ∪ napkinW)) = true) :
    Deriv napkinGraph (napkinLeftNow out) (napkinLeftObs out) :=
  .rewriteEq (napkinLeft_eq out).symm rfl (exchangeNapkinLeft out hcheck)

def napkinRightNow : MassExpr NapkinV :=
  .cond napkinZ (napkinZ ∪ napkinW ∪ (∅ : Finset NapkinV)) (napkinZ ∪ ∅)

def napkinAbsorbSource : MassExpr NapkinV :=
  .cond napkinZ (napkinW ∪ napkinZ) ((∅ : Finset NapkinV) ∪ napkinZ)

theorem napkinRight_eq_absorb : napkinRightNow = napkinAbsorbSource := by
  unfold napkinRightNow napkinAbsorbSource
  refine napkin_cond_eq rfl ?_ ?_
  · ext vertex; cases vertex <;> simp [napkinZ, napkinW]
  · ext vertex; cases vertex <;> simp [napkinZ]

def absorbNapkinZ : Deriv napkinGraph napkinAbsorbSource (.cond napkinZ napkinW ∅) :=
  .absorb napkinZ napkinW ∅ napkinZ (fun _ hmember => hmember)

def napkinRule3Source : MassExpr NapkinV :=
  .cond ((∅ : Finset NapkinV) ∪ napkinZ)
    ((∅ : Finset NapkinV) ∪ napkinW ∪ ∅)
    ((∅ : Finset NapkinV) ∪ ∅)

theorem napkinAbsorbed_eq_rule3 :
    (.cond napkinZ napkinW (∅ : Finset NapkinV)) = napkinRule3Source := by
  unfold napkinRule3Source
  refine napkin_cond_eq ?_ ?_ ?_
  · ext vertex; cases vertex <;> simp [napkinZ]
  · ext vertex; cases vertex <;> simp [napkinW]
  · ext vertex; cases vertex <;> simp

/-- `P(w)`, do-free. -/
def napkinWObs : MassExpr NapkinV :=
  .cond (∅ : Finset NapkinV)
    ((∅ : Finset NapkinV) ∪ napkinW ∪ ∅)
    ((∅ : Finset NapkinV) ∪ ∅)

def deleteNapkinZ : Deriv napkinGraph napkinRule3Source napkinWObs :=
  .rule3 ∅ napkinW napkinZ ∅ napkin_delete_z_from_w_checked

def rightToNapkinObs : Deriv napkinGraph napkinRightNow napkinWObs :=
  .trans
    (.rewriteEq napkinRight_eq_absorb.symm rfl absorbNapkinZ)
    (.rewriteEq napkinAbsorbed_eq_rule3.symm rfl deleteNapkinZ)

def napkinAdjustedBody (out : Finset NapkinV) : MassExpr NapkinV :=
  .mul (napkinLeftObs out) napkinWObs

def adjustNapkinProduct (out : Finset NapkinV)
    (hcheck : FiniteDSeparation.check (gout napkinGraph (∅ : Finset NapkinV) napkinZ)
      (rule2Profile out napkinZ ((∅ : Finset NapkinV) ∪ napkinW)) = true) :
    Deriv napkinGraph (napkinProduct out) (napkinAdjustedBody out) :=
  .trans (.mulLeft (leftToNapkinObs out hcheck)) (.mulRight rightToNapkinObs)

/-- `Σ_w P(out | z, w) P(w)`. -/
def napkinAdjusted (out : Finset NapkinV) : MassExpr NapkinV :=
  .sum napkinW (napkinAdjustedBody out)

def adjustNapkin (out : Finset NapkinV) (hout : Disjoint napkinW out)
    (hcheck : FiniteDSeparation.check (gout napkinGraph (∅ : Finset NapkinV) napkinZ)
      (rule2Profile out napkinZ ((∅ : Finset NapkinV) ∪ napkinW)) = true) :
    Deriv napkinGraph (napkinMarginalSource out) (napkinAdjusted out) :=
  .trans (napkinOpen out hout)
    (.trans (.sumBody (napkinChain out)) (.sumBody (adjustNapkinProduct out hcheck)))

/-- `P(y, x | do(z))`, the numerator produced by the chain-rule quotient. -/
def napkinJointDiv : MassExpr NapkinV :=
  .cond napkinZ (napkinZ ∪ napkinY ∪ napkinX ∪ (∅ : Finset NapkinV)) (napkinZ ∪ ∅)

theorem napkinJointDiv_eq_marginal :
    napkinJointDiv = napkinMarginalSource (napkinX ∪ napkinY) := by
  unfold napkinJointDiv napkinMarginalSource
  refine napkin_cond_eq rfl ?_ rfl
  ext vertex; cases vertex <;> simp [napkinZ, napkinY, napkinX]

def adjustNapkinJoint :
    Deriv napkinGraph napkinJointDiv (napkinAdjusted (napkinX ∪ napkinY)) :=
  .rewriteEq napkinJointDiv_eq_marginal.symm rfl
    (adjustNapkin (napkinX ∪ napkinY) napkinW_disjoint_joint napkin_backdoor_joint_checked)

def adjustNapkinX : Deriv napkinGraph (napkinMarginalSource napkinX) (napkinAdjusted napkinX) :=
  adjustNapkin napkinX napkinW_disjoint_napkinX napkin_backdoor_x_checked

/-- `P(y, x | do(z)) / P(x | do(z))`. -/
def napkinQuotient : MassExpr NapkinV :=
  .div napkinJointDiv (napkinMarginalSource napkinX)

/-- `Σ_w P(y, x | z, w) P(w) / Σ_w P(x | z, w) P(w)`. -/
def napkinExpr : MassExpr NapkinV :=
  .div (napkinAdjusted (napkinX ∪ napkinY)) (napkinAdjusted napkinX)

def napkinFromSeenX : Deriv napkinGraph napkinSeenX napkinExpr :=
  .trans (.divCond napkinZ napkinY napkinX ∅)
    (.trans (.divNum adjustNapkinJoint) (.divDen adjustNapkinX))

/-- From `P(y | do(x))` to the do-free napkin adjustment. -/
def napkinDeriv : Deriv napkinGraph napkinQuery napkinExpr :=
  .trans napkinToSeenX napkinFromSeenX

theorem napkinExpr_doFree : doFree napkinExpr = true := by
  unfold napkinExpr napkinAdjusted napkinAdjustedBody napkinLeftObs napkinWObs doFree
  decide

def napkinEnum : List NapkinV :=
  [NapkinV.u, NapkinV.w, NapkinV.z, NapkinV.x, NapkinV.y]

theorem napkin_parents_fail :
    parentsIn napkinGraph napkinX (∅ : Finset NapkinV) (∅ : Finset NapkinV) = false := by
  decide

theorem napkin_delete_query_fail :
    deleteOK napkinGraph napkinY napkinX (∅ : Finset NapkinV) = false := by
  decide

theorem napkin_no_front_mediator :
    findVertex napkinEnum (fun v =>
      outsideQuery {NapkinV.u} napkinY napkinX v &&
        frontDoorReady napkinGraph napkinX {v} napkinY) = none := by
  decide

/-- The singleton back-door checker accepts some observed vertex. The napkin
branch of `identify` is tried before that search. -/
theorem napkin_back_door_hits :
    (findVertex napkinEnum fun v =>
      outsideQuery {NapkinV.u} napkinY napkinX v &&
        backDoorReady napkinGraph napkinX {v} napkinY).isSome = true := by
  decide

theorem napkin_find_zw :
    findNapkin napkinGraph napkinEnum {NapkinV.u} napkinY napkinX =
      some (NapkinV.z, NapkinV.w) := by
  decide

theorem napkin_shape_eq :
    napkinShape napkinX {NapkinV.z} {NapkinV.w} napkinY = napkinExpr := by
  unfold napkinShape napkinExpr napkinAdjusted napkinAdjustedBody napkinLeftObs napkinWObs
    napkinZ napkinW
  rfl

/-- `idFragment` refuses `P(y | do(x))`, and ID returns the do-free napkin adjustment. -/
theorem napkin_id_separates :
    idFragment napkinGraph napkinY napkinX (∅ : Finset NapkinV) = .refuse ∧
      identify napkinGraph 2 napkinEnum {NapkinV.u} napkinY napkinX (∅ : Finset NapkinV) =
        .doFree napkinExpr ∧
      doFree napkinExpr = true := by
  refine ⟨napkin_fragment_refuses, ?_, napkinExpr_doFree⟩
  unfold identify
  have hparents :
      ¬ parentsIn napkinGraph napkinX (∅ : Finset NapkinV) (∅ : Finset NapkinV) = true := by
    simp [napkin_parents_fail]
  have hdelete :
      ¬ deleteOK napkinGraph napkinY napkinX (∅ : Finset NapkinV) = true := by
    simp [napkin_delete_query_fail]
  split
  · rename_i hzero
    cases hzero
  · rw [if_neg hparents, if_neg hdelete, if_pos (rfl : (∅ : Finset NapkinV) = ∅)]
    rw [napkin_no_front_mediator, napkin_find_zw]
    dsimp
    rw [napkin_shape_eq]

section Denote

variable {β : Type}
variable [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
variable [MeasurableSingletonClass β] [StandardBorelSpace β]
variable [StandardBorelSpace (NapkinV → β)]

theorem napkin_ends_agree
    (cpt : (network (β := β) napkinGraph napkinAcyclic).DiscreteCPT)
    (anchor : NapkinV → β)
    (hpos : Positive napkinGraph napkinAcyclic napkinDeriv cpt anchor) :
    doFree napkinExpr = true ∧
      gDenote napkinGraph napkinAcyclic cpt anchor napkinQuery =
        gDenote napkinGraph napkinAcyclic cpt anchor napkinExpr :=
  ⟨napkinExpr_doFree,
    deriv_gDenote napkinGraph napkinAcyclic napkinDeriv cpt anchor hpos⟩

end Denote

end Mettapedia.GSLT.Causality.DoCalculus
