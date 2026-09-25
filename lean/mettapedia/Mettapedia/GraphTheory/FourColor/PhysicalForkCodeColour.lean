import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFaces

/-!
# The colour coordinate of the fork fold, on positions

`GoertzelV24ForkLocality.localForkTransition_exact` computes the realized
boundary colour support of a parent shore from its two children, testing
clashes only at shared middle vertices.  Read on positions, that transition is
the colour step of the abstract fork with the physical descriptor: a shared
vertex is a paired pair of positions, and the parent position reads the kept
mark together with its partner.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeColour

open Equiv Equiv.Perm
open GoertzelV24ForkInterfaceSupport GoertzelV24ForkProjection GoertzelV24ForkLocality
open EdgeShoreFaceForkFold PhysicalForkCodeFaces

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem V E}

/-- The colour coordinate: realized colour presentations, per position. -/
def codeColour (RS : RotationSystem V E) (S : Finset E) {n : ℕ} (ℓ : Fin n ≃ MidVertex RS S) :
    Finset (Fin n → Finset (Fin 3)) :=
  labelledSupport RS.endpoints S ℓ

section Fork

variable (hC : Cubic3 RS) {S T : Finset E} (hdisj : Disjoint S T)
variable {nL nR nP : ℕ} (ℓS : Fin nL ≃ MidVertex RS S) (ℓT : Fin nR ≃ MidVertex RS T)
  (ℓP : Fin nP ≃ MidVertex RS (S ∪ T))

/-- The vertex named by a kept mark is the parent vertex at that position. -/
theorem keep_vertex_inl {k : Fin nP} {i : Fin nL}
    (h : keepFun hC hdisj ℓS ℓT ℓP k = .inl i) : (ℓS i).1 = (ℓP k).1 := by
  have hd := toMarked_keep_dart hC hdisj ℓS ℓT ℓP k
  rw [h, toMarked_inl] at hd
  rw [← vertOf_alpha_faceLabel hC S ℓS i, ← vertOf_alpha_faceLabel hC (S ∪ T) ℓP k, hd]

theorem keep_vertex_inr {k : Fin nP} {j : Fin nR}
    (h : keepFun hC hdisj ℓS ℓT ℓP k = .inr j) : (ℓT j).1 = (ℓP k).1 := by
  have hd := toMarked_keep_dart hC hdisj ℓS ℓT ℓP k
  rw [h, toMarked_inr] at hd
  rw [← vertOf_alpha_faceLabel hC T ℓT j, ← vertOf_alpha_faceLabel hC (S ∪ T) ℓP k, hd]

theorem colourCompatible_iff (bA : Boundary RS.endpoints S) (bB : Boundary RS.endpoints T) :
    PhysicalForkCode.ColourCompatible (physGlue hC hdisj ℓS ℓT ℓP)
        (labelState RS.endpoints S ℓS bA) (labelState RS.endpoints T ℓT bB) ↔
      LocalCompatible RS.endpoints S T bA bB := by
  constructor
  · intro h v hA hB
    have hmem : (ℓS (ℓS.symm ⟨v, hA⟩)).1 ∈ mid RS.endpoints T := by simpa using hB
    have hp : (physGlue hC hdisj ℓS ℓT ℓP).pair (.inl (ℓS.symm ⟨v, hA⟩)) =
        .inr (ℓT.symm ⟨(ℓS (ℓS.symm ⟨v, hA⟩)).1, hmem⟩) :=
      physPair_inl_of_mem ℓS ℓT hmem
    have := h (.inl (ℓS.symm ⟨v, hA⟩)) (by rw [hp]; exact Sum.inr_ne_inl)
    rw [hp] at this
    simpa [PhysicalForkCode.valOf, labelState] using this
  · rintro h (i | j) hx
    · by_cases hm : (ℓS i).1 ∈ mid RS.endpoints T
      · change _root_.Disjoint _ (PhysicalForkCode.valOf _ _ (physPair ℓS ℓT _))
        rw [physPair_inl_of_mem ℓS ℓT hm]
        simpa [PhysicalForkCode.valOf, labelState] using h (ℓS i).1 (ℓS i).2 hm
      · exact absurd (physPair_inl_of_not_mem ℓS ℓT hm) hx
    · by_cases hm : (ℓT j).1 ∈ mid RS.endpoints S
      · change _root_.Disjoint _ (PhysicalForkCode.valOf _ _ (physPair ℓS ℓT _))
        rw [physPair_inr_of_mem ℓS ℓT hm]
        simpa [PhysicalForkCode.valOf, labelState] using (h (ℓT j).1 hm (ℓT j).2).symm
      · exact absurd (physPair_inr_of_not_mem ℓS ℓT hm) hx

theorem colourOut_eq (bA : Boundary RS.endpoints S) (bB : Boundary RS.endpoints T) :
    PhysicalForkCode.colourOut (physGlue hC hdisj ℓS ℓT ℓP)
        (labelState RS.endpoints S ℓS bA) (labelState RS.endpoints T ℓT bB) =
      labelState RS.endpoints (S ∪ T) ℓP
        (fun v => lift RS.endpoints S bA v.1 ∪ lift RS.endpoints T bB v.1) := by
  funext k
  simp only [PhysicalForkCode.colourOut, labelState]
  change PhysicalForkCode.valOf _ _ (keepFun hC hdisj ℓS ℓT ℓP k) ∪
    PhysicalForkCode.valOf _ _ (physPair ℓS ℓT (keepFun hC hdisj ℓS ℓT ℓP k)) = _
  generalize hkk : keepFun hC hdisj ℓS ℓT ℓP k = a
  rcases a with i | j
  · have hv := keep_vertex_inl hC hdisj ℓS ℓT ℓP hkk
    by_cases hm : (ℓS i).1 ∈ mid RS.endpoints T
    · rw [physPair_inl_of_mem ℓS ℓT hm]
      simp only [PhysicalForkCode.valOf, labelState, lift, ← hv, dif_pos (ℓS i).2, dif_pos hm]
      simp
    · rw [physPair_inl_of_not_mem ℓS ℓT hm]
      simp only [PhysicalForkCode.valOf, labelState, lift, ← hv, dif_pos (ℓS i).2, dif_neg hm,
        Finset.union_idempotent, Finset.union_empty]
  · have hv := keep_vertex_inr hC hdisj ℓS ℓT ℓP hkk
    by_cases hm : (ℓT j).1 ∈ mid RS.endpoints S
    · rw [physPair_inr_of_mem ℓS ℓT hm]
      simp only [PhysicalForkCode.valOf, labelState, lift, ← hv, dif_pos (ℓT j).2, dif_pos hm]
      rw [Finset.union_comm]
      simp
    · rw [physPair_inr_of_not_mem ℓS ℓT hm]
      simp only [PhysicalForkCode.valOf, labelState, lift, ← hv, dif_pos (ℓT j).2, dif_neg hm,
        Finset.union_idempotent, Finset.empty_union]

/-- **Fork correctness for the colour coordinate.** -/
theorem fork_colour
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ RS.endpoints e).card = 3)
    (L : PhysicalForkCode.Code nL) (R : PhysicalForkCode.Code nR)
    (hL : L.colour = codeColour RS S ℓS) (hR : R.colour = codeColour RS T ℓT) :
    (PhysicalForkCode.fork L R (physGlue hC hdisj ℓS ℓT ℓP)).colour =
      codeColour RS (S ∪ T) ℓP := by
  simp only [PhysicalForkCode.fork, hL, hR, codeColour, labelledSupport]
  rw [localForkTransition_exact RS.endpoints hcubic S T hdisj]
  ext w
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, localForkTransition]
  constructor
  · rintro ⟨⟨wA, wB⟩, ⟨⟨⟨bA, hbA, rfl⟩, ⟨bB, hbB, rfl⟩⟩, hc⟩, rfl⟩
    refine ⟨_, ⟨(bA, bB), ⟨⟨hbA, hbB⟩,
      (colourCompatible_iff hC hdisj ℓS ℓT ℓP bA bB).mp hc⟩, rfl⟩, ?_⟩
    exact (colourOut_eq hC hdisj ℓS ℓT ℓP bA bB).symm
  · rintro ⟨_, ⟨⟨bA, bB⟩, ⟨⟨hbA, hbB⟩, hc⟩, rfl⟩, rfl⟩
    refine ⟨(labelState RS.endpoints S ℓS bA, labelState RS.endpoints T ℓT bB),
      ⟨⟨⟨bA, hbA, rfl⟩, ⟨bB, hbB, rfl⟩⟩,
        (colourCompatible_iff hC hdisj ℓS ℓT ℓP bA bB).mpr hc⟩, ?_⟩
    exact colourOut_eq hC hdisj ℓS ℓT ℓP bA bB

end Fork

end

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeColour
