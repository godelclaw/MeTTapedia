import Mettapedia.GSLT.Causality.DoCalculus.Distinctions
import Mettapedia.GSLT.Causality.DoCalculus.ExchangeDelete
import Mettapedia.GSLT.Core.NonFactorization

/-!
# The observed margin of a latent set

`observedMargin L` sums a joint over the coordinates in the latent set `L`.
A query is identified from that margin when it `Factors` through the margin.
`identified_iff_constant_on_fibers` equates that claim with fibre-constancy
only for a surjective margin. The empty margin below is fibre-constant and
does not `Factors`.

On the bow, `L = {U}`. The two bow tables share that margin and disagree on
`bowQuery`. The point mass at one full configuration `Factors` through the
joint and does not `Factors` through the margin.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.GSLT.Core.NonFactorization
open scoped ENNReal

variable {V β : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype β] [DecidableEq β]

/-- The joint with the coordinates in `L` summed out. -/
noncomputable def observedMargin (L : Finset V) (joint : (V → β) → ℝ≥0∞)
    (observed : {v // v ∉ L} → β) : ℝ≥0∞ :=
  ∑ latent : {v // v ∈ L} → β, joint (glue L latent observed)

/-- Identified from a margin: one query value on each fibre of that margin. -/
def IdentifiedFrom {Model Shadow Query : Type}
    (margin : Model → Shadow) (query : Model → Query) : Prop :=
  ConstantOnFibers margin query

/-- On a surjective margin, identification is `Factors`, by
`identified_iff_constant_on_fibers`. -/
theorem identifiedFrom_iff_factors
    {Model Shadow Query : Type}
    {margin : Model → Shadow}
    (onto : Function.Surjective margin)
    (query : Model → Query) :
    IdentifiedFrom margin query ↔ Factors margin query :=
  (identified_iff_constant_on_fibers onto query).symm

/-- Fibre-constancy is not `Factors` when the margin misses a shadow.
The empty carrier has no fibres, and there is no map from `Unit` into `Empty`. -/
theorem constancy_not_factors_when_margin_misses :
    IdentifiedFrom (fun _ : Empty => ()) (fun e : Empty => e) ∧
      ¬ Factors (fun _ : Empty => ()) (fun e : Empty => e) := by
  refine ⟨?_, ?_⟩
  · intro a
    exact Empty.elim a
  · intro ⟨recover, _⟩
    exact Empty.elim (recover ())

theorem missed_margin_not_surjective :
    ¬ Function.Surjective (fun _ : Empty => ()) := by
  intro onto
  exact Empty.elim (onto ()).choose

/-! ## The bow query misses the margin of `U` -/

/-- Margin of a bow table after summing out the confounder. -/
noncomputable def bowMarginFun
    (cpt : (network (β := Bool) bowGraph bowAcyclic).DiscreteCPT) :
    ({v // v ∉ ({Bow.u} : Finset Bow)} → Bool) → ℝ≥0∞ :=
  fun observed => observedMargin {Bow.u} (fun assignment => cpt.jointWeight assignment) observed

theorem bow_margins_agree :
    bowMarginFun bowCPT1 = bowMarginFun bowCPT2 := by
  funext observed
  unfold bowMarginFun observedMargin
  refine Finset.sum_congr rfl fun latent _ => ?_
  exact bow_joint_agree (glue {Bow.u} latent observed)

/-- The bow effect is two models, one margin of `U`, and two values. -/
theorem bow_query_two_models_one_margin :
    bowMarginFun bowCPT1 = bowMarginFun bowCPT2 ∧
      bowQuery bowCPT1 ≠ bowQuery bowCPT2 :=
  ⟨bow_margins_agree, bow_effect_not_identified.2⟩

/-- The bow effect does not `Factors` through the margin of `U`. -/
theorem bow_query_not_factors_observed_margin :
    ¬ Factors bowMarginFun bowQuery := by
  exact (⟨bowCPT1, bowCPT2, bow_margins_agree, bow_effect_not_identified.2⟩ :
    NonTrivialFiber bowMarginFun bowQuery).not_factors

/-! ## Factoring through the joint is strictly weaker -/

/-- A point mass on one bow configuration. -/
noncomputable def pointMass (focus : Bow → Bool) : (Bow → Bool) → ℝ≥0∞ :=
  fun assignment => if assignment = focus then 1 else 0

/-- The mass at `(U, X, Y) = (true, true, true)`. -/
noncomputable def pointQuery (joint : (Bow → Bool) → ℝ≥0∞) : ℝ≥0∞ :=
  joint (bowOf true true true)

/-- The full joint, as the identity shadow on mass assignments. -/
def fullJoint : ((Bow → Bool) → ℝ≥0∞) → (Bow → Bool) → ℝ≥0∞ := id

/-- The margin that sums out `U`. -/
noncomputable def marginOfU (joint : (Bow → Bool) → ℝ≥0∞) :
    ({v // v ∉ ({Bow.u} : Finset Bow)} → Bool) → ℝ≥0∞ :=
  fun observed => observedMargin {Bow.u} joint observed

lemma latentU_subsingleton :
    Subsingleton {v // v ∈ ({Bow.u} : Finset Bow)} := by
  refine ⟨?_⟩
  intro a b
  cases a with
  | mk va ha =>
    cases b with
    | mk vb hb =>
      have hva : va = Bow.u := by simpa using ha
      have hvb : vb = Bow.u := by simpa using hb
      cases hva
      cases hvb
      rfl

lemma sum_latentU (g : ({v // v ∈ ({Bow.u} : Finset Bow)} → Bool) → ℝ≥0∞) :
    ∑ latent, g latent = g (fun _ => false) + g (fun _ => true) := by
  let encode : Bool → {v // v ∈ ({Bow.u} : Finset Bow)} → Bool := fun bit _ => bit
  let decode : ({v // v ∈ ({Bow.u} : Finset Bow)} → Bool) → Bool :=
    fun latent => latent ⟨Bow.u, by simp⟩
  let e : Bool ≃ ({v // v ∈ ({Bow.u} : Finset Bow)} → Bool) :=
    { toFun := encode
      invFun := decode
      left_inv := fun bit => rfl
      right_inv := by
        intro latent
        funext vertex
        have hvertex : vertex = ⟨Bow.u, by simp⟩ :=
          @Subsingleton.elim _ latentU_subsingleton _ _
        rw [hvertex] }
  have hsum : ∑ latent, g latent = g (encode false) + g (encode true) := by
    have huniv : (Finset.univ : Finset Bool) = {false, true} := by
      ext bit
      cases bit <;> simp
    rw [← e.sum_comp g, huniv, Finset.sum_pair (by decide)]
    rfl
  simpa [encode] using hsum

lemma glue_bow_u (bit : Bool) (observed : {v // v ∉ ({Bow.u} : Finset Bow)} → Bool) :
    glue {Bow.u} (fun _ => bit) observed =
      bowOf bit (observed ⟨Bow.x, by simp⟩) (observed ⟨Bow.y, by simp⟩) := by
  funext vertex
  cases vertex with
  | u => simp [glue, bowOf, Finset.mem_singleton]
  | x => simp [glue, bowOf, show Bow.x ∉ ({Bow.u} : Finset Bow) by simp]
  | y =>
      simp [glue, bowOf, show Bow.y ∉ ({Bow.u} : Finset Bow) by simp]

lemma bowOf_eq_iff (leftU leftX leftY rightU rightX rightY : Bool) :
    bowOf leftU leftX leftY = bowOf rightU rightX rightY ↔
      leftU = rightU ∧ leftX = rightX ∧ leftY = rightY := by
  constructor
  · intro hagree
    refine ⟨congrFun hagree Bow.u, congrFun hagree Bow.x, congrFun hagree Bow.y⟩
  · intro hagree
    rcases hagree with ⟨hu, hx, hy⟩
    simp [hu, hx, hy]

lemma margin_pointMass (focusBit focusX focusY : Bool)
    (observed : {v // v ∉ ({Bow.u} : Finset Bow)} → Bool) :
    marginOfU (pointMass (bowOf focusBit focusX focusY)) observed =
      if observed ⟨Bow.x, by simp⟩ = focusX ∧ observed ⟨Bow.y, by simp⟩ = focusY then
        1 else 0 := by
  unfold marginOfU observedMargin pointMass
  rw [sum_latentU]
  simp only [glue_bow_u]
  set seenX := observed ⟨Bow.x, by simp⟩
  set seenY := observed ⟨Bow.y, by simp⟩
  by_cases hseen : seenX = focusX ∧ seenY = focusY
  · rcases hseen with ⟨hx, hy⟩
    cases focusBit <;> simp [hx, hy, bowOf_eq_iff]
  · have hleft :
        bowOf false seenX seenY ≠ bowOf focusBit focusX focusY := by
      intro hagree
      exact hseen ⟨(bowOf_eq_iff _ _ _ _ _ _).1 hagree |>.2.1,
        (bowOf_eq_iff _ _ _ _ _ _).1 hagree |>.2.2⟩
    have hright :
        bowOf true seenX seenY ≠ bowOf focusBit focusX focusY := by
      intro hagree
      exact hseen ⟨(bowOf_eq_iff _ _ _ _ _ _).1 hagree |>.2.1,
        (bowOf_eq_iff _ _ _ _ _ _).1 hagree |>.2.2⟩
    simp [hseen, hleft, hright]

/-- The point mass `Factors` through the full joint. -/
theorem pointQuery_factors_full_joint :
    Factors fullJoint pointQuery :=
  ⟨pointQuery, fun _ => rfl⟩

/-- The same point mass does not `Factors` through the margin of `U`. -/
theorem pointQuery_not_factors_margin :
    ¬ Factors marginOfU pointQuery := by
  have same :
      marginOfU (pointMass (bowOf true true true)) =
        marginOfU (pointMass (bowOf false true true)) := by
    funext observed
    rw [margin_pointMass, margin_pointMass]
  have different :
      pointQuery (pointMass (bowOf true true true)) ≠
        pointQuery (pointMass (bowOf false true true)) := by
    have hne : bowOf true true true ≠ bowOf false true true := by
      intro hagree
      exact Bool.false_ne_true
        ((bowOf_eq_iff true true true false true true).1 hagree).1.symm
    simp only [pointQuery, pointMass, if_neg hne, if_true]
    exact one_ne_zero
  exact (⟨pointMass (bowOf true true true), pointMass (bowOf false true true),
    same, different⟩ : NonTrivialFiber marginOfU pointQuery).not_factors

/-- Factoring through the margin implies factoring through the full joint.
The point mass factors through the joint and misses the margin. -/
theorem joint_factoring_strictly_weaker :
    (∀ query : ((Bow → Bool) → ℝ≥0∞) → ℝ≥0∞,
      Factors marginOfU query → Factors fullJoint query) ∧
      Factors fullJoint pointQuery ∧ ¬ Factors marginOfU pointQuery := by
  refine ⟨?_, pointQuery_factors_full_joint, pointQuery_not_factors_margin⟩
  intro query factors
  exact Factors.of_coarsening (shadow := marginOfU) (fine := fullJoint)
    (coarsen := marginOfU) (fun _ => rfl) factors

end Mettapedia.GSLT.Causality.DoCalculus
