import Mettapedia.Computability.PNP.ClockedKpolyBridgeEquivalence

/-!
# PNP `Kpoly` bridge: bit budgets are finite predictor-image covers

The clocked `Kpoly` bridge has already been reduced to
`ExactVisibleCompressionTarget`, i.e. to an exact `s`-bit budget for the indexed
visible predictor family.  This file makes the remaining mathematical content
even more explicit: an `s`-bit budget is exactly a finite cover of the predictor
image by at most `2^s` Boolean functions.

This is intentionally not a broad `Kpoly` closure theorem.  It is a foundation
result saying that any proposed bridge must prove a finite predictor-image bound
for the actual switched family.
-/

namespace Mettapedia.Computability.PNP

universe u v w

namespace IndexedPredictorFamily

variable {Index : Type u} {Input : Type v}

/-- A finite family of Boolean predictors covering every predictor selected by
an indexed family.  The numeric parameter is the allowed cover size, not a bit
length. -/
def FinitePredictorCover
    (G : IndexedPredictorFamily Index Input) (N : ℕ) : Prop :=
  ∃ S : Finset (Input → Bool), (∀ i, G.predict i ∈ S) ∧ S.card ≤ N

/-- A finite set of representative indices whose selected predictors cover the
whole predictor image.  This avoids assuming `DecidableEq Index`; the
representatives are carried by an arbitrary finite type. -/
def FiniteIndexRepresentativeCover
    (G : IndexedPredictorFamily Index Input) (N : ℕ) : Prop :=
  ∃ Rep : Type (max u v), ∃ _ : Fintype Rep, ∃ select : Rep → Index,
    (∀ i, ∃ r : Rep, G.predict (select r) = G.predict i) ∧
      Fintype.card Rep ≤ N

/-- A finite quotient-code presentation of the predictor image.  Each index is
encoded into a finite code type, and the decoder assigned to that code is
exactly the predictor selected by the index. -/
def FinitePredictorQuotient
    (G : IndexedPredictorFamily Index Input) (N : ℕ) : Prop :=
  ∃ Code : Type (max u v), ∃ _ : Fintype Code, ∃ encode : Index → Code,
    ∃ decode : Code → Input → Bool,
      (∀ i, decode (encode i) = G.predict i) ∧ Fintype.card Code ≤ N

/-- Any exact `s`-bit budget covers the predictor image by at most `2^s`
functions. -/
theorem finitePredictorCover_of_hasBitBudget
    {G : IndexedPredictorFamily Index Input} {s : ℕ}
    (hsmall : G.HasBitBudget s) :
    G.FinitePredictorCover (2 ^ s) := by
  classical
  rcases hsmall with ⟨F, hF⟩
  refine ⟨Finset.univ.image F.decode, ?_, ?_⟩
  · intro i
    rcases hF i with ⟨c, hc⟩
    rw [← hc]
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩
  · exact le_trans Finset.card_image_le (by simp)

/-- A finite predictor-image cover of size at most `2^s` can be encoded by
`s` bits. -/
theorem hasBitBudget_of_finitePredictorCover
    {G : IndexedPredictorFamily Index Input} {s : ℕ}
    (hcover : G.FinitePredictorCover (2 ^ s)) :
    G.HasBitBudget s := by
  classical
  rcases hcover with ⟨S, hmem, hcard⟩
  have hcardCode : 2 ^ s = Fintype.card (BitCode s) := by
    simp
  let Cover := {f : Input → Bool // f ∈ S}
  have hcoverCard : Fintype.card Cover = S.card := by
    simp [Cover]
  let toFin : Cover → Fin (2 ^ s) :=
    fun f => Fin.castLE hcard (Fin.cast hcoverCard ((Fintype.equivFin Cover) f))
  let toCode : Cover → BitCode s :=
    fun f =>
      (Fintype.equivFin (BitCode s)).symm (Fin.cast hcardCode (toFin f))
  have htoCode_inj : Function.Injective toCode := by
    intro x y hxy
    have hfinCast :
        Fin.cast hcardCode (toFin x) = Fin.cast hcardCode (toFin y) :=
      (Fintype.equivFin (BitCode s)).symm.injective hxy
    have hfin : toFin x = toFin y :=
      Fin.cast_injective hcardCode hfinCast
    have hequiv :
        (Fintype.equivFin Cover) x = (Fintype.equivFin Cover) y := by
      have hcast :
          Fin.cast hcoverCard ((Fintype.equivFin Cover) x) =
            Fin.cast hcoverCard ((Fintype.equivFin Cover) y) :=
        Fin.castLE_injective hcard hfin
      exact Fin.cast_injective hcoverCard hcast
    exact (Fintype.equivFin Cover).injective hequiv
  refine
    ⟨{ decode := fun c =>
          if h : ∃ f : Cover, toCode f = c then
            (Classical.choose h).1
          else
            fun _ => false },
      ?_⟩
  intro i
  let f : Cover := ⟨G.predict i, hmem i⟩
  refine ⟨toCode f, ?_⟩
  let hex : ∃ g : Cover, toCode g = toCode f := ⟨f, rfl⟩
  have hchoose : Classical.choose hex = f :=
    htoCode_inj (Classical.choose_spec hex)
  change
    (if h : ∃ g : Cover, toCode g = toCode f then
        (Classical.choose h).1
      else
        fun _ => false) = G.predict i
  rw [dif_pos hex]
  simp [f, hchoose]

/-- Exact bit budgets are exactly finite predictor-image covers of size at most
`2^s`. -/
theorem hasBitBudget_iff_finitePredictorCover
    {G : IndexedPredictorFamily Index Input} {s : ℕ} :
    G.HasBitBudget s ↔ G.FinitePredictorCover (2 ^ s) :=
  ⟨finitePredictorCover_of_hasBitBudget, hasBitBudget_of_finitePredictorCover⟩

/-- Finite predictor-image covers are monotone in the allowed cover size. -/
theorem finitePredictorCover_mono
    {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hcover : G.FinitePredictorCover N) :
    G.FinitePredictorCover M := by
  rcases hcover with ⟨S, hmem, hcard⟩
  exact ⟨S, hmem, le_trans hcard hNM⟩

/-- A cover for a factored summary family pulls back to a cover for the
original indexed family. -/
theorem finitePredictorCover_of_factorsThrough
    {View : Type w} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hcover : H.FinitePredictorCover N) :
    G.FinitePredictorCover N := by
  classical
  rcases hcover with ⟨S, hmem, hcard⟩
  refine ⟨S.image (fun f : View → Bool => fun x : Input => f (view x)), ?_, ?_⟩
  · intro i
    have hpull : (fun x : Input => H.predict i (view x)) = G.predict i := by
      funext x
      exact (hfactor i x).symm
    have hmemImage :
        (fun x : Input => H.predict i (view x)) ∈
          S.image (fun f : View → Bool => fun x : Input => f (view x)) :=
      Finset.mem_image.mpr ⟨H.predict i, hmem i, rfl⟩
    simpa [hpull] using
      hmemImage
  · exact le_trans Finset.card_image_le hcard

/-- If a factor map has a section, a cover of the pulled-back family pushes
back to a cover of the summary family. -/
theorem finitePredictorCover_of_factorsThrough_of_rightInverse
    {View : Type w} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hcover : G.FinitePredictorCover N) :
    H.FinitePredictorCover N := by
  classical
  rcases hcover with ⟨S, hmem, hcard⟩
  refine ⟨S.image (fun f : Input → Bool => fun y : View => f (sec y)), ?_, ?_⟩
  · intro i
    have hpush : (fun y : View => G.predict i (sec y)) = H.predict i := by
      funext y
      calc
        G.predict i (sec y) = H.predict i (view (sec y)) := hfactor i (sec y)
        _ = H.predict i y := by simp [hsection y]
    have hmemImage :
        (fun y : View => G.predict i (sec y)) ∈
          S.image (fun f : Input → Bool => fun y : View => f (sec y)) :=
      Finset.mem_image.mpr ⟨G.predict i, hmem i, rfl⟩
    simpa [hpush] using
      hmemImage
  · exact le_trans Finset.card_image_le hcard

/-- A finite representative-index cover induces a finite predictor-image cover. -/
theorem finitePredictorCover_of_finiteIndexRepresentativeCover
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hrep : G.FiniteIndexRepresentativeCover N) :
    G.FinitePredictorCover N := by
  classical
  rcases hrep with ⟨Rep, hRep, select, hcover, hcard⟩
  letI := hRep
  refine ⟨Finset.univ.image (fun r : Rep => G.predict (select r)), ?_, ?_⟩
  · intro i
    rcases hcover i with ⟨r, hr⟩
    rw [← hr]
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
  · exact le_trans Finset.card_image_le hcard

/-- A finite predictor-image cover can be represented by finitely many actual
indices from the family. -/
theorem finiteIndexRepresentativeCover_of_finitePredictorCover
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hcover : G.FinitePredictorCover N) :
    G.FiniteIndexRepresentativeCover N := by
  classical
  rcases hcover with ⟨S, hmem, hcard⟩
  let Cover :=
    {f : {f : Input → Bool // f ∈ S} // ∃ i, G.predict i = (f.1 : Input → Bool)}
  have hcoverCard : Fintype.card Cover ≤ S.card := by
    have hinj : Function.Injective (fun f : Cover => f.1) := by
      intro f g hfg
      exact Subtype.ext hfg
    have hle :
        Fintype.card Cover ≤ Fintype.card {f : Input → Bool // f ∈ S} :=
      Fintype.card_le_of_injective (fun f : Cover => f.1) hinj
    simpa [Cover] using hle
  let Rep := ULift.{max u v, max 0 v} Cover
  refine ⟨Rep, inferInstance, (fun f : Rep => Classical.choose f.down.2), ?_, ?_⟩
  · intro i
    let f : Rep := ULift.up (⟨⟨G.predict i, hmem i⟩, ⟨i, rfl⟩⟩ : Cover)
    refine ⟨f, ?_⟩
    exact Classical.choose_spec f.down.2
  · exact le_trans (by simpa [Rep] using hcoverCard) hcard

/-- Finite predictor covers are exactly finite representative-index covers. -/
theorem finitePredictorCover_iff_finiteIndexRepresentativeCover
    {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FinitePredictorCover N ↔ G.FiniteIndexRepresentativeCover N :=
  ⟨finiteIndexRepresentativeCover_of_finitePredictorCover,
    finitePredictorCover_of_finiteIndexRepresentativeCover⟩

/-- A finite quotient-code presentation induces a finite predictor-image cover. -/
theorem finitePredictorCover_of_finitePredictorQuotient
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hquot : G.FinitePredictorQuotient N) :
    G.FinitePredictorCover N := by
  classical
  rcases hquot with ⟨Code, hCode, encode, decode, hreal, hcard⟩
  letI := hCode
  refine ⟨Finset.univ.image decode, ?_, ?_⟩
  · intro i
    rw [← hreal i]
    exact Finset.mem_image.mpr ⟨encode i, Finset.mem_univ (encode i), rfl⟩
  · exact le_trans Finset.card_image_le hcard

/-- A finite representative-index cover gives a quotient-code presentation by
using representatives as codes. -/
theorem finitePredictorQuotient_of_finiteIndexRepresentativeCover
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hrep : G.FiniteIndexRepresentativeCover N) :
    G.FinitePredictorQuotient N := by
  classical
  rcases hrep with ⟨Rep, hRep, select, hcover, hcard⟩
  refine
    ⟨Rep, hRep, (fun i => Classical.choose (hcover i)),
      (fun r => G.predict (select r)), ?_, hcard⟩
  intro i
  exact Classical.choose_spec (hcover i)

/-- A finite predictor-image cover can be repackaged as a finite quotient-code
presentation. -/
theorem finitePredictorQuotient_of_finitePredictorCover
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hcover : G.FinitePredictorCover N) :
    G.FinitePredictorQuotient N :=
  finitePredictorQuotient_of_finiteIndexRepresentativeCover
    (finiteIndexRepresentativeCover_of_finitePredictorCover hcover)

/-- A finite quotient-code presentation can be represented by actual selected
indices. -/
theorem finiteIndexRepresentativeCover_of_finitePredictorQuotient
    {G : IndexedPredictorFamily Index Input} {N : ℕ}
    (hquot : G.FinitePredictorQuotient N) :
    G.FiniteIndexRepresentativeCover N :=
  finiteIndexRepresentativeCover_of_finitePredictorCover
    (finitePredictorCover_of_finitePredictorQuotient hquot)

/-- Finite predictor-image covers are exactly finite quotient-code
presentations. -/
theorem finitePredictorCover_iff_finitePredictorQuotient
    {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FinitePredictorCover N ↔ G.FinitePredictorQuotient N :=
  ⟨finitePredictorQuotient_of_finitePredictorCover,
    finitePredictorCover_of_finitePredictorQuotient⟩

/-- Finite representative-index covers are exactly finite quotient-code
presentations. -/
theorem finiteIndexRepresentativeCover_iff_finitePredictorQuotient
    {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FiniteIndexRepresentativeCover N ↔ G.FinitePredictorQuotient N :=
  ⟨finitePredictorQuotient_of_finiteIndexRepresentativeCover,
    finiteIndexRepresentativeCover_of_finitePredictorQuotient⟩

/-- Finite representative-index covers are monotone in the allowed number of
representatives. -/
theorem finiteIndexRepresentativeCover_mono
    {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hrep : G.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover M := by
  rcases hrep with ⟨Rep, hRep, select, hcover, hcard⟩
  exact ⟨Rep, hRep, select, hcover, le_trans hcard hNM⟩

/-- A representative-index cover for a factored summary family pulls back to
the original indexed family. -/
theorem finiteIndexRepresentativeCover_of_factorsThrough
    {View : Type w} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hrep : H.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover N := by
  exact finiteIndexRepresentativeCover_of_finitePredictorCover
    (finitePredictorCover_of_factorsThrough hfactor
      (finitePredictorCover_of_finiteIndexRepresentativeCover hrep))

/-- If a factor map has a section, a representative-index cover of the
pulled-back family pushes back to the summary family. -/
theorem finiteIndexRepresentativeCover_of_factorsThrough_of_rightInverse
    {View : Type w} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    H.FiniteIndexRepresentativeCover N := by
  exact finiteIndexRepresentativeCover_of_finitePredictorCover
    (finitePredictorCover_of_factorsThrough_of_rightInverse hfactor hsection
      (finitePredictorCover_of_finiteIndexRepresentativeCover hrep))

/-- Finite quotient-code presentations are monotone in the allowed code count. -/
theorem finitePredictorQuotient_mono
    {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hquot : G.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient M := by
  rcases hquot with ⟨Code, hCode, encode, decode, hreal, hcard⟩
  exact ⟨Code, hCode, encode, decode, hreal, le_trans hcard hNM⟩

/-- A quotient-code presentation for a factored summary family pulls back to
the original indexed family. -/
theorem finitePredictorQuotient_of_factorsThrough
    {View : Type w} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hquot : H.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient N :=
  finitePredictorQuotient_of_finitePredictorCover
    (finitePredictorCover_of_factorsThrough hfactor
      (finitePredictorCover_of_finitePredictorQuotient hquot))

/-- If a factor map has a section, a quotient-code presentation of the pulled
back family pushes back to the summary family. -/
theorem finitePredictorQuotient_of_factorsThrough_of_rightInverse
    {View : Type w} {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View} {view : Input → View}
    {sec : View → Input} {N : ℕ}
    (hfactor : G.FactorsThrough view H)
    (hsection : Function.RightInverse sec view)
    (hquot : G.FinitePredictorQuotient N) :
    H.FinitePredictorQuotient N :=
  finitePredictorQuotient_of_finitePredictorCover
    (finitePredictorCover_of_factorsThrough_of_rightInverse hfactor hsection
      (finitePredictorCover_of_finitePredictorQuotient hquot))

/-- Exact bit budgets are equivalently finite representative-index covers by
at most `2^s` selected indices. -/
theorem hasBitBudget_iff_finiteIndexRepresentativeCover
    {G : IndexedPredictorFamily Index Input} {s : ℕ} :
    G.HasBitBudget s ↔ G.FiniteIndexRepresentativeCover (2 ^ s) := by
  rw [hasBitBudget_iff_finitePredictorCover,
    finitePredictorCover_iff_finiteIndexRepresentativeCover]

/-- Exact bit budgets are equivalently finite quotient-code presentations by
at most `2^s` codes. -/
theorem hasBitBudget_iff_finitePredictorQuotient
    {G : IndexedPredictorFamily Index Input} {s : ℕ} :
    G.HasBitBudget s ↔ G.FinitePredictorQuotient (2 ^ s) := by
  rw [hasBitBudget_iff_finitePredictorCover,
    finitePredictorCover_iff_finitePredictorQuotient]

end IndexedPredictorFamily

end Mettapedia.Computability.PNP
