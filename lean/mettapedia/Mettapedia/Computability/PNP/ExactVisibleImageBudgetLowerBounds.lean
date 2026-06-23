import Mettapedia.Computability.PNP.ExactVisibleImageBudgetFiniteCovers

/-!
# Predictor-image lower bounds

Finite predictor-image covers, representative-index covers, and quotient-code
presentations all inherit the same lower bounds from injectively realized
probe families or from surjectivity onto a finite Boolean classifier space.
-/

namespace Mettapedia.Computability.PNP

universe u v w

namespace IndexedPredictorFamily

variable {Index : Type u} {Input : Type v}

/-- If an indexed family realizes an injectively indexed finite probe family of
Boolean classifiers, then any finite predictor-image cover must contain at
least that many classifiers. -/
theorem finitePredictorCover_card_le_of_injective_realization
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N := by
  classical
  rcases hcover with ⟨S, hmem, hcard⟩
  let toCover : Probe → {f : Input → Bool // f ∈ S} :=
    fun p =>
      ⟨target p, by
        rcases hreal p with ⟨i, hi⟩
        rw [← hi]
        exact hmem i⟩
  have htoCover : Function.Injective toCover := by
    intro p q hpq
    apply hinj
    exact congrArg Subtype.val hpq
  have hle :
      Fintype.card Probe ≤ Fintype.card {f : Input → Bool // f ∈ S} :=
    Fintype.card_le_of_injective toCover htoCover
  have hcoverCard : Fintype.card {f : Input → Bool // f ∈ S} = S.card := by
    simp
  have hsubtypeCard : Fintype.card {f : Input → Bool // f ∈ S} ≤ N := by
    simpa [hcoverCard] using hcard
  exact le_trans hle hsubtypeCard

/-- Negative form of the finite injective-realization lower bound for
predictor-image covers. -/
theorem not_finitePredictorCover_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorCover N := by
  intro hcover
  exact Nat.not_le_of_lt hN
    (finitePredictorCover_card_le_of_injective_realization
      target hinj hreal hcover)

/-- A representative-index cover must contain at least every injectively
realized finite probe family. -/
theorem finiteIndexRepresentativeCover_card_le_of_injective_realization
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N :=
  finitePredictorCover_card_le_of_injective_realization target hinj hreal
    (finitePredictorCover_of_finiteIndexRepresentativeCover hrep)

/-- Negative representative-index form of the finite injective-realization
lower bound. -/
theorem not_finiteIndexRepresentativeCover_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  intro hrep
  exact Nat.not_le_of_lt hN
    (finiteIndexRepresentativeCover_card_le_of_injective_realization
      target hinj hreal hrep)

/-- A finite quotient-code presentation must contain at least every injectively
realized finite probe family. -/
theorem finitePredictorQuotient_card_le_of_injective_realization
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N :=
  finitePredictorCover_card_le_of_injective_realization target hinj hreal
    (finitePredictorCover_of_finitePredictorQuotient hquot)

/-- Negative quotient-code form of the finite injective-realization lower
bound. -/
theorem not_finitePredictorQuotient_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (target : Probe → Input → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorQuotient N := by
  intro hquot
  exact Nat.not_le_of_lt hN
    (finitePredictorQuotient_card_le_of_injective_realization
      target hinj hreal hquot)

/-- If an indexed family already realizes every Boolean classifier on a finite
input type, then any finite predictor-image cover must contain at least the
full Boolean classifier space. -/
theorem finitePredictorCover_card_le_of_surjective_predict
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card Input ≤ N := by
  classical
  rcases hcover with ⟨S, hmem, hcard⟩
  have hsub : (Finset.univ : Finset (Input → Bool)) ⊆ S := by
    intro f _
    rcases hsurj f with ⟨i, hi⟩
    rw [← hi]
    exact hmem i
  have hclassifierCard : Fintype.card (Input → Bool) ≤ S.card := by
    simpa using Finset.card_le_card hsub
  have hspace : Fintype.card (Input → Bool) = 2 ^ Fintype.card Input :=
    card_boolClassifierSpace Input
  simpa [hspace] using le_trans hclassifierCard hcard

/-- A fully expressive indexed family has no finite predictor-image cover below
the full Boolean classifier-space cardinality. -/
theorem not_finitePredictorCover_of_surjective_predict
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card Input)
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorCover N := by
  intro hcover
  exact Nat.not_le_of_lt hN
    (finitePredictorCover_card_le_of_surjective_predict hsurj hcover)

/-- If `G` factors through a finite summary family `H`, the view has a section,
and `H` is still surjective onto all Boolean classifiers on that summary, then
any finite predictor-image cover of `G` must be at least the full Boolean
classifier-space cardinality of the summary. -/
theorem finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
    {View : Type w} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    finitePredictorCover_card_le_of_surjective_predict
      (G := H) hsurj
      (finitePredictorCover_of_factorsThrough_of_rightInverse
        hfactor hsection hcover)

/-- Negative form of the section-backed reduced-view finite-image obstruction. -/
theorem not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_surjective_predict
    {View : Type w} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorCover N := by
  intro hcover
  exact Nat.not_le_of_lt hN
    (finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hcover)

/-- If `G` factors through a summary family `H`, the view has a section, and
`H` already realizes an injectively indexed finite probe family, then any finite
predictor-image cover of `G` must be at least the probe cardinality. -/
theorem finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    {Probe : Type*} [Fintype Probe] {View : Type w}
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N :=
  finitePredictorCover_card_le_of_injective_realization target hinj hreal
    (finitePredictorCover_of_factorsThrough_of_rightInverse
      hfactor hsection hcover)

/-- Negative form of the section-backed finite-probe lower bound. -/
theorem not_finitePredictorCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe] {View : Type w}
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FinitePredictorCover N := by
  intro hcover
  exact Nat.not_le_of_lt hN
    (finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hcover)

/-- The same reduced-view lower bound for representative-index covers. -/
theorem finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
    {View : Type w} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card View ≤ N := by
  exact
    finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj
      (finitePredictorCover_of_finiteIndexRepresentativeCover hrep)

/-- Negative representative-index form of the section-backed reduced-view
finite-image obstruction. -/
theorem not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_surjective_predict
    {View : Type w} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  intro hrep
  exact Nat.not_le_of_lt hN
    (finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hrep)

/-- Representative-index covers inherit the same section-backed finite-probe
lower bound. -/
theorem finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    {Probe : Type*} [Fintype Probe] {View : Type w}
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N :=
  finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    target hinj hreal hfactor hsection
    (finitePredictorCover_of_finiteIndexRepresentativeCover hrep)

/-- Negative representative-index form of the section-backed finite-probe lower
bound. -/
theorem not_finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe] {View : Type w}
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  intro hrep
  exact Nat.not_le_of_lt hN
    (finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hrep)

/-- A fully expressive indexed family forces every finite quotient-code
presentation to have at least the full Boolean classifier-space cardinality. -/
theorem finitePredictorQuotient_card_le_of_surjective_predict
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card Input ≤ N :=
  finitePredictorCover_card_le_of_surjective_predict hsurj
    (finitePredictorCover_of_finitePredictorQuotient hquot)

/-- Fully expressive indexed families have no finite quotient-code
presentation below the full Boolean classifier-space cardinality. -/
theorem not_finitePredictorQuotient_of_surjective_predict
    [Fintype Input]
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card Input)
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorQuotient N := by
  intro hquot
  exact Nat.not_le_of_lt hN
    (finitePredictorQuotient_card_le_of_surjective_predict hsurj hquot)

/-- Section-backed reduced-view lower bound for finite quotient-code
presentations. -/
theorem finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
    {View : Type w} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card View ≤ N :=
  finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
    hfactor hsection hsurj
    (finitePredictorCover_of_finitePredictorQuotient hquot)

/-- Negative quotient-code form of the section-backed reduced-view finite-image
obstruction. -/
theorem not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_surjective_predict
    {View : Type w} [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (hN : N < 2 ^ Fintype.card View)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hsurj : Function.Surjective H.predict) :
    ¬ G.FinitePredictorQuotient N := by
  intro hquot
  exact Nat.not_le_of_lt hN
    (finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      hfactor hsection hsurj hquot)

/-- Quotient-code presentations inherit the same section-backed finite-probe
lower bound. -/
theorem finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    {Probe : Type*} [Fintype Probe] {View : Type w}
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N :=
  finitePredictorCover_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
    target hinj hreal hfactor hsection
    (finitePredictorCover_of_finitePredictorQuotient hquot)

/-- Negative quotient-code form of the section-backed finite-probe lower
bound. -/
theorem not_finitePredictorQuotient_of_factorsThrough_of_rightInverse_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe] {View : Type w}
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View} {sec : View → Input} {N : ℕ}
    (target : Probe → View → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, H.predict i = target p)
    (hN : N < Fintype.card Probe)
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view) :
    ¬ G.FinitePredictorQuotient N := by
  intro hquot
  exact Nat.not_le_of_lt hN
    (finitePredictorQuotient_card_le_of_factorsThrough_of_rightInverse_of_injective_realization
      target hinj hreal hfactor hsection hquot)

end IndexedPredictorFamily

end Mettapedia.Computability.PNP
