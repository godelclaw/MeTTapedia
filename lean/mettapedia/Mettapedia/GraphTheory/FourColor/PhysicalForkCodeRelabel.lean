import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFold

/-!
# Representation invariance of the fork code

A code depends on the chosen enumeration of the middle vertices only through
an explicit action of the permutations of the positions.  Changing the
labelling of a node by `σ` renames the positions of its code by `σ`; and the
closure `Reach` is closed under renaming, because renaming a parent only
reorders the kept marks of the fork that produced it, while the leaf code is
invariant.  So a closure may be computed on canonical representatives.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCode

open Equiv Equiv.Perm
open GoertzelV24OrderedCutFaceReturnProfile

variable {nL nR nP : ℕ}

/-- Rename the positions of a cut record. -/
def CutRecord.relabel {n : ℕ} (σ : Fin n ≃ Fin n) (r : CutRecord n) : CutRecord n :=
  ⟨r.bits ∘ σ, r.inside, r.outside, r.cost⟩

/-- Rename the positions of a code: position `i` of the result reads position
`σ i` of the input. -/
def Code.relabel {n : ℕ} (σ : Fin n ≃ Fin n) (c : Code n) : Code n where
  two := c.two ∘ σ
  colour := c.colour.image fun b => b ∘ σ
  ret := σ.symm.permCongr c.ret
  cut := c.cut.image (CutRecord.relabel σ)

/-- Reorder the kept marks of a descriptor. -/
def Glue.relabel {nL nR nP : ℕ} (σ : Fin nP ≃ Fin nP) (g : Glue nL nR nP) : Glue nL nR nP :=
  ⟨g.pair, σ.toEmbedding.trans g.keep⟩

/-- The leaf code is invariant under both permutations of its two positions. -/
theorem leafCode_relabel (σ : Fin 2 ≃ Fin 2) : leafCode.relabel σ = leafCode := by
  have hσ : σ = Equiv.refl _ ∨ σ = Equiv.swap 0 1 := by
    have h01 : σ 0 ≠ σ 1 := fun h => absurd (σ.injective h) (by decide)
    by_cases h0 : σ 0 = 0
    · left
      ext i
      fin_cases i
      · simp [h0]
      · simp only [Fin.mk_one, Equiv.refl_apply]
        omega
    · right
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Equiv.swap_apply_left]
        omega
      · simp only [Fin.mk_one, Equiv.swap_apply_right]
        omega
  rcases hσ with rfl | rfl
  · decide
  · have hrec : ∀ b : Bool × Bool, CutRecord.relabel (Equiv.swap 0 1)
        (PhysicalForkCodeFold.leafRecord b) = PhysicalForkCodeFold.leafRecord b.swap := by
      rintro ⟨b1, b2⟩
      ext1
      · funext i
        fin_cases i <;> rfl
      · exact Bool.or_comm _ _
      · simp only [CutRecord.relabel, PhysicalForkCodeFold.leafRecord, Prod.snd_swap,
          Prod.fst_swap, Bool.and_comm]
      · exact Bool.xor_comm _ _
    ext1
    · rfl
    · simp only [Code.relabel, leafCode, Finset.image_image]
      rfl
    · apply Equiv.ext
      intro i
      fin_cases i <;> decide
    · simp only [Code.relabel]
      rw [PhysicalForkCodeFold.leafCode_cut_eq, Finset.image_image]
      ext r
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, hrec]
      constructor
      · rintro ⟨b, rfl⟩; exact ⟨b.swap, rfl⟩
      · rintro ⟨b, rfl⟩; exact ⟨b.swap, by simp⟩

noncomputable section
attribute [local instance] Classical.propDecidable

theorem range_keep_relabel {nL nR nP : ℕ} (σ : Fin nP ≃ Fin nP) (g : Glue nL nR nP) :
    Set.range (g.relabel σ).keep = Set.range g.keep := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨σ k, rfl⟩
  · rintro ⟨k, rfl⟩; exact ⟨σ.symm k, by simp [Glue.relabel]⟩

/-- The kept mark of a fork's return, read through the kept marks. -/
theorem keep_fork_ret {nL nR nP : ℕ} (L : Code nL) (R : Code nR) (g : Glue nL nR nP)
    (k : Fin nP) :
    g.keep ((fork L R g).ret k) =
      (nextHitPerm (merged L R * g.pair) (fun x => x ∈ Set.range g.keep)
        ⟨g.keep k, Set.mem_range_self k⟩).1 := by
  show ((keepEquiv g) ((keepEquiv g).symm _)).1 = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem fork_relabel {nL nR nP : ℕ} (L : Code nL) (R : Code nR) (g : Glue nL nR nP)
    (σ : Fin nP ≃ Fin nP) :
    fork L R (g.relabel σ) = (fork L R g).relabel σ := by
  have hr := range_keep_relabel σ g
  ext1
  · rfl
  · simp only [fork, Code.relabel, Finset.image_image]
    rfl
  · apply Equiv.ext
    intro k
    apply (g.relabel σ).keep.injective
    rw [keep_fork_ret]
    change _ = g.keep (σ (σ.symm ((fork L R g).ret (σ k))))
    rw [Equiv.apply_symm_apply, keep_fork_ret]
    exact EdgeShoreFaceForkFold.nextHit_val_congr_pred (merged L R * g.pair)
      (fun x => x ∈ Set.range g.keep) (fun x => x ∈ Set.range (g.relabel σ).keep)
      (fun x => by rw [hr]) ⟨g.keep (σ k), Set.mem_range_self (σ k)⟩
  · simp only [fork, Code.relabel, Finset.image_image]
    rfl

/-- **The closure is closed under renaming positions.** -/
theorem reach_relabel {bound n : ℕ} {c : Code n} (h : Reach bound n c) (σ : Fin n ≃ Fin n) :
    Reach bound n (c.relabel σ) := by
  cases h with
  | leaf => rw [leafCode_relabel]; exact Reach.leaf
  | fork g hL hR hlegal heuler hbound =>
      rw [← fork_relabel]
      refine Reach.fork (g.relabel σ) hL hR ?_ heuler hbound
      have hr := range_keep_relabel σ g
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hlegal
      refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_⟩
      · intro x hx; rw [hr]; exact h6 x hx
      · intro x hx ho; rw [hr]; exact h7 x hx ho
      · intro x hx ho; rw [hr]; exact h8 x hx ho

end

end Mettapedia.GraphTheory.FourColor.PhysicalForkCode

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFold

open Equiv Equiv.Perm
open GoertzelV24ForkInterfaceSupport GoertzelV24ForkProjection
open PhysicalForkCodeFaces PhysicalForkCodeColour PhysicalForkCodeCut PhysicalForkCode

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem V E}

/-- **Changing the labelling of a node renames the positions of its code.** -/
theorem encode_relabel (hC : Cubic3 RS) (S : Finset E) {n : ℕ} (ℓ : Fin n ≃ MidVertex RS S)
    (σ : Fin n ≃ Fin n) :
    encode hC S (σ.trans ℓ) = (encode hC S ℓ).relabel σ := by
  ext1
  · rfl
  · change (boundarySupport RS.endpoints S).image (labelState RS.endpoints S (σ.trans ℓ)) =
      ((boundarySupport RS.endpoints S).image (labelState RS.endpoints S ℓ)).image _
    rw [Finset.image_image]
    rfl
  · apply Equiv.ext
    intro i
    rfl
  · change ((touched RS S).powerset.filter _).image (cutRecord RS S (σ.trans ℓ)) =
      (((touched RS S).powerset.filter _).image (cutRecord RS S ℓ)).image _
    rw [Finset.image_image]
    rfl

end

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFold
