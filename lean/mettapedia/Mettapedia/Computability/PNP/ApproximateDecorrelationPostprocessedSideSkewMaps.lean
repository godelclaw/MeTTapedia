import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideCollisions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# PNP approximate decorrelation: postprocessed-side layer

This module contains the skew-map counterexamples separating pointwise collisions from equivalence-preserving maps.
-/

namespace Mettapedia.Computability.PNP

/-- A three-coin retained-side postprocessing audit instance.  Both source
sides observe the same two values, but with multiplicities `2,1` versus `1,2`.
This is the minimal finite pattern showing that pointwise support overlap is
strictly weaker than the preserving coin-equivalence obligation. -/
def postprocessedSidePointwiseCollisionSkewRecoding (b : Bool) (c : Fin 3) :
    Bool :=
  if b = true then decide (c.val < 2) else decide (c.val = 0)

/-- In the skew three-coin audit instance, every true-side observed value has a
false-side witness and every false-side observed value has a true-side witness.
Thus pointwise collisions/support overlap alone can hold. -/
theorem postprocessedSidePointwiseCollisionSkew_pointwise_true_false_collisions :
    (∀ cTrue : Fin 3,
        ∃ cFalse : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse) ∧
      (∀ cFalse : Fin 3,
        ∃ cTrue : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
            postprocessedSidePointwiseCollisionSkewRecoding false cFalse) := by
  constructor
  · intro cTrue
    fin_cases cTrue
    · exact ⟨0, by simp [postprocessedSidePointwiseCollisionSkewRecoding]⟩
    · exact ⟨0, by simp [postprocessedSidePointwiseCollisionSkewRecoding]⟩
    · exact ⟨1, by simp [postprocessedSidePointwiseCollisionSkewRecoding]⟩
  · intro cFalse
    fin_cases cFalse
    · exact ⟨0, by simp [postprocessedSidePointwiseCollisionSkewRecoding]⟩
    · exact ⟨2, by simp [postprocessedSidePointwiseCollisionSkewRecoding]⟩
    · exact ⟨2, by simp [postprocessedSidePointwiseCollisionSkewRecoding]⟩

/-- In the skew three-coin audit instance, no bijective coin matching can
preserve the postprocessed observation.  Two true-side coins with observed
value `true` would both have to map to the unique false-side coin with that
same observed value. -/
theorem postprocessedSidePointwiseCollisionSkew_no_coinEquiv_preserving :
    ¬ ∃ e : Fin 3 ≃ Fin 3,
      ∀ c : Fin 3,
        postprocessedSidePointwiseCollisionSkewRecoding true c =
          postprocessedSidePointwiseCollisionSkewRecoding false (e c) := by
  rintro ⟨e, hpres⟩
  have hfalse_true_eq_zero :
      ∀ c : Fin 3,
        postprocessedSidePointwiseCollisionSkewRecoding false c = true →
          c = 0 := by
    intro c hc
    fin_cases c <;>
      simp [postprocessedSidePointwiseCollisionSkewRecoding] at hc ⊢
  have he0 : e 0 = 0 := by
    apply hfalse_true_eq_zero
    simpa [postprocessedSidePointwiseCollisionSkewRecoding] using
      (hpres 0).symm
  have he1 : e 1 = 0 := by
    apply hfalse_true_eq_zero
    simpa [postprocessedSidePointwiseCollisionSkewRecoding] using
      (hpres 1).symm
  have h01 : (0 : Fin 3) = 1 := by
    apply e.injective
    rw [he0, he1]
  norm_num at h01

/-- Pointwise true/false support overlap does not imply the postprocessed-side
coin-matching obligation.  This blocks the repair route that tries to replace
the preserving coin equivalence with mere two-sided support collisions. -/
theorem postprocessedSide_pointwise_collisions_do_not_imply_coinEquiv_preserving :
    ∃ r : Bool → Fin 3 → Bool,
    ∃ side : Fin 3 → Unit,
    ∃ post : Bool × Unit → Bool,
      ((∀ cTrue : Fin 3,
          ∃ cFalse : Fin 3,
            post (r true cTrue, side cTrue) =
              post (r false cFalse, side cFalse)) ∧
        (∀ cFalse : Fin 3,
          ∃ cTrue : Fin 3,
            post (r true cTrue, side cTrue) =
              post (r false cFalse, side cFalse))) ∧
        ¬ ∃ e : Fin 3 ≃ Fin 3,
          ∀ c : Fin 3,
            post (r true c, side c) = post (r false (e c), side (e c)) := by
  refine
    ⟨postprocessedSidePointwiseCollisionSkewRecoding,
      (fun _c => ()), (fun x : Bool × Unit => x.1), ?_⟩
  exact
    ⟨postprocessedSidePointwiseCollisionSkew_pointwise_true_false_collisions,
      postprocessedSidePointwiseCollisionSkew_no_coinEquiv_preserving⟩

/-- A one-sided true-to-false coin map preserving postprocessed observations
promotes to the required preserving coin equivalence as soon as it is
injective.  Thus the missing datum in a witness-choice repair is not the
choice function itself, but its finite injectivity/bijectivity. -/
theorem exists_postprocessedSide_coinEquiv_preserving_of_injective_coinMap_preserving
    {Coin α Side β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (f : Coin → Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c)))
    (hinj : Function.Injective f) :
    ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  classical
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  let e : Coin ≃ Coin := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e, ?_⟩
  intro c
  change post (r true c, side c) = post (r false (f c), side (f c))
  exact hpres c

/-- Contrapositive form of the one-sided-map audit: whenever no preserving
postprocessed-side coin equivalence exists, every one-sided preserving
true-to-false coin map must collapse two coin choices. -/
theorem not_injective_postprocessedSide_coinMap_preserving_of_no_coinEquiv
    {Coin α Side β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (f : Coin → Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c)))
    (hno :
      ¬ ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c))) :
    ¬ Function.Injective f := by
  intro hinj
  exact hno
    (exists_postprocessedSide_coinEquiv_preserving_of_injective_coinMap_preserving
      r side post f hpres hinj)

/-- An injective one-sided witness map is not a weaker repair target: for a
finite coin type it is equivalent to the full preserving postprocessed-side
coin equivalence.  The forward direction promotes injectivity to bijectivity;
the reverse direction forgets the equivalence to its underlying function. -/
theorem exists_injective_postprocessedSide_coinMap_preserving_iff_exists_coinEquiv_preserving
    {Coin α Side β : Type*} [Fintype Coin]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ f : Coin → Coin,
      (∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c))) ∧
        Function.Injective f) ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c)) := by
  constructor
  · rintro ⟨f, hpres, hinj⟩
    exact
      exists_postprocessedSide_coinEquiv_preserving_of_injective_coinMap_preserving
        r side post f hpres hinj
  · rintro ⟨e, hpres⟩
    refine ⟨fun c => e c, ?_, e.injective⟩
    exact hpres

/-- A concrete one-sided witness map for the skew three-coin instance.  It
sends both true-side coins with observed value `true` to the unique false-side
coin with observed value `true`, and sends the remaining true-side coin to a
false-side coin with observed value `false`. -/
def postprocessedSidePointwiseCollisionSkewTrueToFalseMap (c : Fin 3) : Fin 3 :=
  if postprocessedSidePointwiseCollisionSkewRecoding true c = true then 0 else 1

/-- The concrete skew witness map preserves the postprocessed observation. -/
theorem postprocessedSidePointwiseCollisionSkew_trueToFalseMap_preserving :
    ∀ c : Fin 3,
      postprocessedSidePointwiseCollisionSkewRecoding true c =
        postprocessedSidePointwiseCollisionSkewRecoding false
          (postprocessedSidePointwiseCollisionSkewTrueToFalseMap c) := by
  intro c
  fin_cases c <;>
    simp [postprocessedSidePointwiseCollisionSkewRecoding,
      postprocessedSidePointwiseCollisionSkewTrueToFalseMap]

/-- The concrete skew witness map is necessarily non-injective: it collapses
the two true-side coins whose postprocessed observation is `true`. -/
theorem postprocessedSidePointwiseCollisionSkew_trueToFalseMap_not_injective :
    ¬ Function.Injective postprocessedSidePointwiseCollisionSkewTrueToFalseMap := by
  intro hinj
  have hsame :
      postprocessedSidePointwiseCollisionSkewTrueToFalseMap (0 : Fin 3) =
        postprocessedSidePointwiseCollisionSkewTrueToFalseMap 1 := by
    simp [postprocessedSidePointwiseCollisionSkewRecoding,
      postprocessedSidePointwiseCollisionSkewTrueToFalseMap]
  have h01 : (0 : Fin 3) = 1 := hinj hsame
  norm_num at h01

/-- In the skew three-coin instance, every one-sided true-to-false map that
preserves the postprocessed observation is non-injective.  This blocks the
repair route that tries to choose a false-side witness for each true-side coin
without proving the choice is an injective/bijective matching. -/
theorem postprocessedSidePointwiseCollisionSkew_any_preserving_coinMap_not_injective
    (f : Fin 3 → Fin 3)
    (hpres :
      ∀ c : Fin 3,
        postprocessedSidePointwiseCollisionSkewRecoding true c =
          postprocessedSidePointwiseCollisionSkewRecoding false (f c)) :
    ¬ Function.Injective f := by
  have hpres' :
      ∀ c : Fin 3,
        (fun x : Bool × Unit => x.1)
            (postprocessedSidePointwiseCollisionSkewRecoding true c, ()) =
          (fun x : Bool × Unit => x.1)
            (postprocessedSidePointwiseCollisionSkewRecoding false (f c), ()) := by
    intro c
    exact hpres c
  have hno :
      ¬ ∃ e : Fin 3 ≃ Fin 3,
        ∀ c : Fin 3,
          (fun x : Bool × Unit => x.1)
              (postprocessedSidePointwiseCollisionSkewRecoding true c, ()) =
            (fun x : Bool × Unit => x.1)
              (postprocessedSidePointwiseCollisionSkewRecoding false (e c), ()) := by
    simpa using postprocessedSidePointwiseCollisionSkew_no_coinEquiv_preserving
  exact
    not_injective_postprocessedSide_coinMap_preserving_of_no_coinEquiv
      postprocessedSidePointwiseCollisionSkewRecoding (fun _c => ())
      (fun x : Bool × Unit => x.1) f hpres' hno

/-- A one-sided witness-choice repair is still strictly weaker than the
postprocessed-side preserving coin equivalence: the skew instance has
one-sided preserving maps, but every such map is non-injective and hence cannot
be promoted to a bijective matching. -/
theorem postprocessedSide_oneSided_coinMap_preserving_does_not_imply_coinEquiv_preserving :
    ∃ r : Bool → Fin 3 → Bool,
    ∃ side : Fin 3 → Unit,
    ∃ post : Bool × Unit → Bool,
      (∃ f : Fin 3 → Fin 3,
        ∀ c : Fin 3,
          post (r true c, side c) = post (r false (f c), side (f c))) ∧
        (∀ f : Fin 3 → Fin 3,
          (∀ c : Fin 3,
            post (r true c, side c) = post (r false (f c), side (f c))) →
            ¬ Function.Injective f) ∧
          ¬ ∃ e : Fin 3 ≃ Fin 3,
            ∀ c : Fin 3,
              post (r true c, side c) = post (r false (e c), side (e c)) := by
  refine
    ⟨postprocessedSidePointwiseCollisionSkewRecoding,
      (fun _c => ()), (fun x : Bool × Unit => x.1), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact
      ⟨postprocessedSidePointwiseCollisionSkewTrueToFalseMap,
        postprocessedSidePointwiseCollisionSkew_trueToFalseMap_preserving⟩
  · intro f hpres
    exact postprocessedSidePointwiseCollisionSkew_any_preserving_coinMap_not_injective f hpres
  · exact postprocessedSidePointwiseCollisionSkew_no_coinEquiv_preserving

end Mettapedia.Computability.PNP
