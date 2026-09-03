import Mettapedia.GraphTheory.FourColor.Compositional.FiveCutShoreLanguage
import Mettapedia.GraphTheory.FourColor.Compositional.FiveCutWordHeart
import Mettapedia.GraphTheory.FourColor.Compositional.CyclicMatchingRotation

/-!
# Dihedral transfers of five-cut shore words

The shore language, the cap supports, and the boundary-language closure
properties all transfer along the dihedral symmetries of the boundary
circle.  Reflections `i ↦ c - i` carry the retained successor pin to the
cap convention, so the caps of one shore ride the five reflections of the
shore's pinned coordinates; rotations `i ↦ i + k` preserve the cap
convention, so the complementary shore's caps ride the five rotations of
its anti-pinned coordinates.  All finite facts are checked by `decide`;
all word transfers are constructive.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace Compositional

namespace FiveCutWordTransfers

open BoundaryKempeSwitch
open CyclicBoundaryMatching
open CyclicMatchingRotation
open FiveCutShoreLanguage
open FiveCutWordHeart
open GoertzelV24PortTangleCutParity
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## Tait triples under permutation -/

theorem isTaitColorTriple_swap23 {a b c : Color}
    (h : IsTaitColorTriple a b c) : IsTaitColorTriple a c b :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.2.1, h.2.2.2.1, h.2.2.2.2.2.symm⟩

theorem isTaitColorTriple_rev {a b c : Color}
    (h : IsTaitColorTriple a b c) : IsTaitColorTriple c b a :=
  ⟨h.2.2.1, h.2.1, h.1, h.2.2.2.2.2.symm, h.2.2.2.2.1.symm,
    h.2.2.2.1.symm⟩

/-! ## The shore language under reindexing -/

section ShoreLanguage

universe u

variable {V I P : Type u}

/-- Reading the shore language in reindexed coordinates is reading the
reindexed word in the original coordinates. -/
theorem shoreLanguage_trans_iff (s : Fin 5 ≃ Fin 5) (order : Fin 5 ≃ P)
    (T : PortTangle V I P) (w : CAP5BoundaryWord) :
    shoreLanguage (s.trans order) T w ↔
      shoreLanguage order T (fun i => w (s.symm i)) := by
  constructor
  · rintro ⟨boundary, hmem, hval⟩
    exact ⟨fun i => boundary (s.symm i), hmem, fun i => hval (s.symm i)⟩
  · rintro ⟨boundary, hmem, hval⟩
    refine ⟨fun i => boundary (s i), ?_, ?_⟩
    · show (fun port => boundary (s ((s.trans order).symm port))) ∈
        taitSupport T
      have hfun : (fun port => boundary (s ((s.trans order).symm port))) =
          fun port => boundary (order.symm port) := by
        funext port
        show boundary (s (s.symm (order.symm port))) =
          boundary (order.symm port)
        rw [Equiv.apply_symm_apply]
      rw [hfun]
      exact hmem
    · intro i
      have := hval (s i)
      simpa using this

end ShoreLanguage

/-! ## Pin algebra: reflections flip the successor, rotations keep it -/

/-- Conjugation along a composite equivalence is successive conjugation. -/
theorem permCongr_trans_eq {A B C : Type*} (first : A ≃ B) (second : B ≃ C)
    (perm : Equiv.Perm A) :
    (first.trans second).permCongr perm =
      second.permCongr (first.permCongr perm) := by
  apply Equiv.ext
  intro point
  rfl

/-- Reflections conjugate the inverse rotation back to the rotation. -/
theorem subLeft_permCongr_finRotate_inv :
    ∀ c : Fin 5,
      (Equiv.subLeft c).permCongr (finRotate 5)⁻¹ = finRotate 5 := by
  decide

/-- Rotations commute with the inverse rotation. -/
theorem addRight_permCongr_finRotate_inv :
    ∀ k : Fin 5,
      (Equiv.addRight k).permCongr (finRotate 5)⁻¹ = (finRotate 5)⁻¹ := by
  decide

/-- A reflection of a positively pinned order is anti-pinned: it carries
the successor in the cap convention. -/
theorem anti_pin_of_pin_reflection {A : Type*} (orderR : Fin 5 ≃ A)
    (succ : Equiv.Perm A) (c : Fin 5)
    (hpin : orderR.permCongr (finRotate 5) = succ) :
    succ = ((Equiv.subLeft c).trans orderR).permCongr (finRotate 5)⁻¹ := by
  rw [permCongr_trans_eq, subLeft_permCongr_finRotate_inv c, hpin]

/-- A rotation of an anti-pinned order is anti-pinned. -/
theorem anti_pin_of_anti_pin_rotation {A : Type*} (orderAnti : Fin 5 ≃ A)
    (succ : Equiv.Perm A) (k : Fin 5)
    (hanti : succ = orderAnti.permCongr (finRotate 5)⁻¹) :
    succ =
      ((Equiv.addRight k).trans orderAnti).permCongr (finRotate 5)⁻¹ := by
  rw [permCongr_trans_eq, addRight_permCongr_finRotate_inv k]
  exact hanti

/-- The only self-maps of the five-cycle conjugating the inverse rotation
to the rotation are the five reflections. -/
theorem eq_subLeft_of_conj :
    ∀ σ : Fin 5 ≃ Fin 5,
      σ.permCongr (finRotate 5)⁻¹ = finRotate 5 →
      ∃ c : Fin 5, σ = Equiv.subLeft c := by
  decide

/-- A pinned and an anti-pinned order on the same carrier differ by one of
the five reflections. -/
theorem exists_reflection_of_pins {A : Type*} (orderR orderAnti : Fin 5 ≃ A)
    (succ : Equiv.Perm A)
    (hpin : orderR.permCongr (finRotate 5) = succ)
    (hanti : succ = orderAnti.permCongr (finRotate 5)⁻¹) :
    ∃ c : Fin 5, orderAnti = (Equiv.subLeft c).trans orderR := by
  set σ : Fin 5 ≃ Fin 5 := orderAnti.trans orderR.symm with hσ
  have hcomp : orderAnti = σ.trans orderR := by
    apply Equiv.ext
    intro i
    simp [hσ]
  have hconj : σ.permCongr (finRotate 5)⁻¹ = finRotate 5 := by
    apply orderR.permCongr.injective
    rw [← permCongr_trans_eq, ← hcomp, ← hanti, hpin]
  rcases eq_subLeft_of_conj σ hconj with ⟨c, hc⟩
  exact ⟨c, by rw [hcomp, hc]⟩

/-! ## Cap supports under reflection and rotation -/

/-- Y-cap support at position `0`, read through the reflection `i ↦ c - i`,
lands at position `c - 1`. -/
theorem yCapSupport_reflect (c : Fin 5) (w : CAP5BoundaryWord)
    (h : CAP5YCapSupport 0 w) :
    CAP5YCapSupport (c - 1) (fun i => w (c - i)) := by
  obtain ⟨hseam, hnonzero, htriple⟩ := h
  fin_cases c <;>
    exact ⟨hseam.symm, fun hzero => hnonzero (hseam.trans hzero),
      isTaitColorTriple_rev htriple⟩

/-- Y-cap support at position `0`, read through the rotation `i ↦ i - k`,
lands at position `k`. -/
theorem yCapSupport_rotate (k : Fin 5) (w : CAP5BoundaryWord)
    (h : CAP5YCapSupport 0 w) :
    CAP5YCapSupport k (fun i => w (i - k)) := by
  obtain ⟨hseam, hnonzero, htriple⟩ := h
  fin_cases k <;> exact ⟨hseam, hnonzero, htriple⟩

/-- Pentagon extendability survives reflection of the boundary circle. -/
theorem extendsAcrossCycle_reflect (c : Fin 5) (w : CAP5BoundaryWord)
    (h : CAP5WordExtendsAcrossCycle w) :
    CAP5WordExtendsAcrossCycle (fun i => w (c - i)) := by
  obtain ⟨x, h0, h1, h2, h3, h4⟩ := h
  refine ⟨fun i => x (c - 1 - i), ?_, ?_, ?_, ?_, ?_⟩ <;> fin_cases c
  · exact isTaitColorTriple_swap23 h0
  · exact isTaitColorTriple_swap23 h1
  · exact isTaitColorTriple_swap23 h2
  · exact isTaitColorTriple_swap23 h3
  · exact isTaitColorTriple_swap23 h4
  · exact isTaitColorTriple_swap23 h4
  · exact isTaitColorTriple_swap23 h0
  · exact isTaitColorTriple_swap23 h1
  · exact isTaitColorTriple_swap23 h2
  · exact isTaitColorTriple_swap23 h3
  · exact isTaitColorTriple_swap23 h3
  · exact isTaitColorTriple_swap23 h4
  · exact isTaitColorTriple_swap23 h0
  · exact isTaitColorTriple_swap23 h1
  · exact isTaitColorTriple_swap23 h2
  · exact isTaitColorTriple_swap23 h2
  · exact isTaitColorTriple_swap23 h3
  · exact isTaitColorTriple_swap23 h4
  · exact isTaitColorTriple_swap23 h0
  · exact isTaitColorTriple_swap23 h1
  · exact isTaitColorTriple_swap23 h1
  · exact isTaitColorTriple_swap23 h2
  · exact isTaitColorTriple_swap23 h3
  · exact isTaitColorTriple_swap23 h4
  · exact isTaitColorTriple_swap23 h0

/-- Pentagon extendability survives rotation of the boundary circle. -/
theorem extendsAcrossCycle_rotate (k : Fin 5) (w : CAP5BoundaryWord)
    (h : CAP5WordExtendsAcrossCycle w) :
    CAP5WordExtendsAcrossCycle (fun i => w (i - k)) := by
  obtain ⟨x, h0, h1, h2, h3, h4⟩ := h
  refine ⟨fun i => x (i - k), ?_, ?_, ?_, ?_, ?_⟩ <;> fin_cases k
  · exact h0
  · exact h4
  · exact h3
  · exact h2
  · exact h1
  · exact h1
  · exact h0
  · exact h4
  · exact h3
  · exact h2
  · exact h2
  · exact h1
  · exact h0
  · exact h4
  · exact h3
  · exact h3
  · exact h2
  · exact h1
  · exact h0
  · exact h4
  · exact h4
  · exact h3
  · exact h2
  · exact h1
  · exact h0

/-! ## The boundary language under reflection -/

/-- Noncrossing survives conjugation by a reflection of the boundary
circle. -/
theorem isNoncrossingMatching_of_reflection_conj :
    ∀ (c : Fin 5) (mate : Fin 5 → Fin 5),
      IsNoncrossingMatching mate →
      IsNoncrossingMatching (fun i => c - mate (c - i)) := by
  decide

/-- Colour counts are invariant under reflection of the positions. -/
theorem cap5BoundaryColorCount_reflect :
    ∀ (c : Fin 5) (w : CAP5BoundaryWord) (color : Color),
      cap5BoundaryColorCount (fun i => w (c - i)) color =
        cap5BoundaryColorCount w color := by
  decide

/-- The boundary-language closure properties survive reflection of the
boundary circle. -/
theorem boundaryLanguage_reflect {L : CAP5BoundaryWord → Prop} (c : Fin 5)
    (h : BoundaryLanguage L) :
    BoundaryLanguage (fun w => L (fun i => w (c - i))) := by
  have hdouble : ∀ w : CAP5BoundaryWord,
      (fun i => (fun j => w (c - j)) (c - i)) = w := by
    intro w
    funext i
    simp [sub_sub_cancel]
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨hnonzero, hodd⟩ := h.admissible _ hw
    constructor
    · intro i
      have := hnonzero (c - i)
      simpa [sub_sub_cancel] using this
    · have hcount : ∀ color, cap5BoundaryColorCount w color =
          cap5BoundaryColorCount (fun i => w (c - i)) color := by
        intro color
        have := cap5BoundaryColorCount_reflect c (fun i => w (c - i)) color
        rwa [hdouble w] at this
      obtain ⟨hred, hblue, hpurple⟩ := hodd
      rw [← hcount red] at hred
      rw [← hcount blue] at hblue
      rw [← hcount purple] at hpurple
      exact ⟨hred, hblue, hpurple⟩
  · intro σ hσ w hw
    have := h.colourClosed σ hσ _ hw
    exact this
  · intro w hw x y hx hy hxy
    obtain ⟨mate, hinv, hmoves, hnc, hswitch⟩ :=
      h.chainClosed _ hw x y hx hy hxy
    refine ⟨fun i => c - mate (c - i), ?_, ?_, ?_, ?_⟩
    · intro i
      show c - mate (c - (c - mate (c - i))) = i
      rw [sub_sub_cancel, hinv, sub_sub_cancel]
    · intro i
      constructor
      · intro hne
        have hmateNe : mate (c - i) ≠ c - i := by
          intro heq
          apply hne
          show c - mate (c - i) = i
          rw [heq, sub_sub_cancel]
        have := (hmoves (c - i)).1 hmateNe
        simpa [sub_sub_cancel] using this
      · intro hcolor
        have hcolor' : (fun j => w (c - j)) (c - i) = x ∨
            (fun j => w (c - j)) (c - i) = y := by
          simpa [sub_sub_cancel] using hcolor
        have hmateNe := (hmoves (c - i)).2 hcolor'
        intro heq
        apply hmateNe
        have hback := congrArg (fun t => c - t) heq
        simpa [sub_sub_cancel] using hback
    · exact isNoncrossingMatching_of_reflection_conj c mate hnc
    · intro T hTinv
      have hTinv' : ∀ i ∈ T.image (fun j => c - j), mate i ∈
          T.image (fun j => c - j) := by
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨j, hj, hji⟩
        have hmoved := hTinv j hj
        have hji' : c - j = i := hji
        refine Finset.mem_image.mpr ⟨c - mate i, ?_, by
          show c - (c - mate i) = mate i
          rw [sub_sub_cancel]⟩
        have himg : c - mate i = c - mate (c - j) := by rw [← hji']
        rw [himg]
        exact hmoved
      have hclosed := hswitch (T.image (fun j => c - j)) hTinv'
      have hrewrite :
          (fun i => cap5BoundarySwap x y T w (c - i)) =
          cap5BoundarySwap x y (T.image (fun j => c - j))
            (fun i => w (c - i)) := by
        funext i
        show (if c - i ∈ T then cap5SwapColor x y (w (c - i))
            else w (c - i)) =
          (if i ∈ T.image (fun j => c - j) then
            cap5SwapColor x y (w (c - i)) else w (c - i))
        have hmem : c - i ∈ T ↔ i ∈ T.image (fun j => c - j) := by
          constructor
          · intro hi
            exact Finset.mem_image.mpr ⟨c - i, hi, by rw [sub_sub_cancel]⟩
          · intro hi
            rcases Finset.mem_image.mp hi with ⟨j, hj, hji⟩
            have hjeq : j = c - i := by
              have := congrArg (fun t => c - t) hji
              simpa [sub_sub_cancel] using this
            rwa [← hjeq]
        rw [if_congr hmem rfl rfl]
      show L (fun i => cap5BoundarySwap x y T w (c - i))
      rw [hrewrite]
      exact hclosed

end FiveCutWordTransfers

end Compositional

end Mettapedia.GraphTheory.FourColor
