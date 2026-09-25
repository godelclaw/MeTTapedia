import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeRelabel

/-!
# Renaming the children of a fork

`PhysicalForkCodeRelabel` renames the parent of a fork by reordering its kept
marks.  Renaming a child is absorbed by the descriptor in the same way: the
fork of renamed children under a descriptor is the fork of the original
children under the descriptor transported along the renamings.  Legality and
the Euler guard transport with it.  A closure computed on canonical
representatives therefore covers every fork of every renaming of its states.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCode

open Equiv Equiv.Perm
open GoertzelV24OrderedCutFaceReturnProfile

variable {nL nR nP : ℕ}

/-- Transport a descriptor along renamings of the two children. -/
def Glue.transport (τL : Fin nL ≃ Fin nL) (τR : Fin nR ≃ Fin nR) (g : Glue nL nR nP) :
    Glue nL nR nP :=
  ⟨(Equiv.sumCongr τL τR).permCongr g.pair, g.keep.trans (Equiv.sumCongr τL τR).toEmbedding⟩

noncomputable section
attribute [local instance] Classical.propDecidable

theorem Code.relabel_relabel {n : ℕ} (c : Code n) (σ τ : Fin n ≃ Fin n) :
    (c.relabel σ).relabel τ = c.relabel (τ.trans σ) := by
  ext1
  · rfl
  · simp only [Code.relabel, Finset.image_image]
    rfl
  · apply Equiv.ext
    intro i
    rfl
  · simp only [Code.relabel, Finset.image_image]
    rfl

theorem Code.relabel_refl {n : ℕ} (c : Code n) : c.relabel (Equiv.refl _) = c := by
  have hcut : CutRecord.relabel (Equiv.refl (Fin n)) = id := by
    funext r; rfl
  ext1
  · rfl
  · simp only [Code.relabel, Equiv.coe_refl, Function.comp_id, Finset.image_id']
  · apply Equiv.ext
    intro i
    rfl
  · simp only [Code.relabel, hcut, Finset.image_id]

theorem Code.relabel_symm {n : ℕ} (c : Code n) (σ : Fin n ≃ Fin n) :
    (c.relabel σ).relabel σ.symm = c := by
  rw [Code.relabel_relabel, Equiv.symm_trans_self, Code.relabel_refl]

section Transport

variable (τL : Fin nL ≃ Fin nL) (τR : Fin nR ≃ Fin nR)

theorem valOf_comp {α : Type*} (bL : Fin nL → α) (bR : Fin nR → α) (x : Fin nL ⊕ Fin nR) :
    valOf (bL ∘ τL) (bR ∘ τR) x = valOf bL bR (Equiv.sumCongr τL τR x) := by
  rcases x with i | j <;> rfl

theorem twoOf_relabel (L : Code nL) (R : Code nR) (x : Fin nL ⊕ Fin nR) :
    twoOf (L.relabel τL) (R.relabel τR) x = twoOf L R (Equiv.sumCongr τL τR x) := by
  rcases x with i | j <;> rfl

theorem transport_pair_apply (g : Glue nL nR nP) (x : Fin nL ⊕ Fin nR) :
    (g.transport τL τR).pair (Equiv.sumCongr τL τR x) = Equiv.sumCongr τL τR (g.pair x) := by
  simp [Glue.transport]

theorem transport_keep_apply (g : Glue nL nR nP) (k : Fin nP) :
    (g.transport τL τR).keep k = Equiv.sumCongr τL τR (g.keep k) := rfl

theorem colourCompatible_transport (g : Glue nL nR nP) (bL : Fin nL → Finset (Fin 3))
    (bR : Fin nR → Finset (Fin 3)) :
    ColourCompatible (g.transport τL τR) bL bR ↔ ColourCompatible g (bL ∘ τL) (bR ∘ τR) := by
  constructor
  · intro h x hx
    rw [valOf_comp, valOf_comp, ← transport_pair_apply]
    apply h
    rw [transport_pair_apply]
    exact fun e => hx ((Equiv.sumCongr τL τR).injective e)
  · intro h y hy
    obtain ⟨x, rfl⟩ := (Equiv.sumCongr τL τR).surjective y
    have := h x (fun e => hy (by rw [transport_pair_apply, e]))
    rwa [valOf_comp, valOf_comp, ← transport_pair_apply] at this

theorem colourOut_transport (g : Glue nL nR nP) (bL : Fin nL → Finset (Fin 3))
    (bR : Fin nR → Finset (Fin 3)) :
    colourOut (g.transport τL τR) bL bR = colourOut g (bL ∘ τL) (bR ∘ τR) := by
  funext k
  simp only [colourOut]
  rw [valOf_comp, valOf_comp, transport_keep_apply, transport_pair_apply]

theorem cutCompatible_transport (g : Glue nL nR nP) (rL : CutRecord nL) (rR : CutRecord nR) :
    CutCompatible (g.transport τL τR) rL rR ↔
      CutCompatible g (CutRecord.relabel τL rL) (CutRecord.relabel τR rR) := by
  constructor
  · rintro ⟨h, hc⟩
    refine ⟨fun x => ?_, hc⟩
    have := h (Equiv.sumCongr τL τR x)
    rw [transport_pair_apply] at this
    change valOf (rL.bits ∘ τL) (rR.bits ∘ τR) _ = valOf (rL.bits ∘ τL) (rR.bits ∘ τR) _
    rw [valOf_comp, valOf_comp]
    exact this
  · rintro ⟨h, hc⟩
    refine ⟨fun y => ?_, hc⟩
    obtain ⟨x, rfl⟩ := (Equiv.sumCongr τL τR).surjective y
    have := h x
    change valOf (rL.bits ∘ τL) (rR.bits ∘ τR) _ = valOf (rL.bits ∘ τL) (rR.bits ∘ τR) _ at this
    rw [valOf_comp, valOf_comp] at this
    rw [transport_pair_apply]
    exact this

theorem cutOut_transport (g : Glue nL nR nP) (rL : CutRecord nL) (rR : CutRecord nR) :
    cutOut (g.transport τL τR) rL rR =
      cutOut g (CutRecord.relabel τL rL) (CutRecord.relabel τR rR) := by
  simp only [cutOut, CutRecord.relabel]
  congr 1
  funext k
  rw [transport_keep_apply]
  exact (valOf_comp τL τR rL.bits rR.bits (g.keep k)).symm

theorem range_keep_transport (g : Glue nL nR nP) (x : Fin nL ⊕ Fin nR) :
    Equiv.sumCongr τL τR x ∈ Set.range (g.transport τL τR).keep ↔ x ∈ Set.range g.keep := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (Equiv.sumCongr τL τR).injective hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

theorem merged_relabel (L : Code nL) (R : Code nR) :
    merged (L.relabel τL) (R.relabel τR) =
      (Equiv.sumCongr τL τR).symm.permCongr (merged L R) := by
  apply Equiv.ext
  rintro (i | j) <;> rfl

/-- **Renaming the children is transporting the descriptor.** -/
theorem fork_relabel_children (L : Code nL) (R : Code nR) (g : Glue nL nR nP) :
    fork (L.relabel τL) (R.relabel τR) g = fork L R (g.transport τL τR) := by
  set θ := Equiv.sumCongr τL τR with hθ
  ext1
  · funext k
    simp only [fork]
    rw [transport_keep_apply, transport_pair_apply, twoOf_relabel]
    simp only [← hθ, EmbeddingLike.apply_eq_iff_eq]
  · simp only [fork, Code.relabel]
    ext b
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨_, _⟩, ⟨⟨⟨bL, hbL, rfl⟩, ⟨bR, hbR, rfl⟩⟩, hc⟩, rfl⟩
      exact ⟨(bL, bR), ⟨⟨hbL, hbR⟩, (colourCompatible_transport τL τR g bL bR).mpr hc⟩,
        colourOut_transport τL τR g bL bR⟩
    · rintro ⟨⟨bL, bR⟩, ⟨⟨hbL, hbR⟩, hc⟩, rfl⟩
      exact ⟨(bL ∘ τL, bR ∘ τR), ⟨⟨⟨bL, hbL, rfl⟩, ⟨bR, hbR, rfl⟩⟩,
        (colourCompatible_transport τL τR g bL bR).mp hc⟩,
        (colourOut_transport τL τR g bL bR).symm⟩
  · -- the face return: first return commutes with conjugation by θ
    have hmerged : θ.permCongr (merged (L.relabel τL) (R.relabel τR)) = merged L R := by
      apply Equiv.ext
      intro x
      simp [merged_relabel, hθ]
    have hp : merged L R * (g.transport τL τR).pair =
        θ.permCongr (merged (L.relabel τL) (R.relabel τR) * g.pair) := by
      rw [Equiv.permCongr_mul, hmerged]
      rfl
    have hN := PhysicalForkCodeFaces.nextHitPerm_permCongr θ
      (merged (L.relabel τL) (R.relabel τR) * g.pair)
      (fun x => x ∈ Set.range g.keep) (fun y => y ∈ Set.range (g.transport τL τR).keep)
      (range_keep_transport τL τR g)
    apply Equiv.ext
    intro k
    apply g.keep.injective
    rw [keep_fork_ret]
    apply θ.injective
    have hB := keep_fork_ret L R (g.transport τL τR) k
    change θ (g.keep ((fork L R (g.transport τL τR)).ret k)) = _ at hB
    rw [hB, hp]
    have hval := congrArg Subtype.val
      (Equiv.congr_fun hN ⟨θ (g.keep k), (range_keep_transport τL τR g _).mpr
        (Set.mem_range_self k)⟩)
    symm
    refine hval.trans ?_
    simp only [Equiv.permCongr_apply, Equiv.subtypeEquiv_apply]
    congr 2
    apply Subtype.ext
    simp
  · simp only [fork, Code.relabel]
    ext r
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨_, _⟩, ⟨⟨⟨rL, hrL, rfl⟩, ⟨rR, hrR, rfl⟩⟩, hc⟩, rfl⟩
      exact ⟨(rL, rR), ⟨⟨hrL, hrR⟩, (cutCompatible_transport τL τR g rL rR).mpr hc⟩,
        cutOut_transport τL τR g rL rR⟩
    · rintro ⟨⟨rL, rR⟩, ⟨⟨hrL, hrR⟩, hc⟩, rfl⟩
      exact ⟨(CutRecord.relabel τL rL, CutRecord.relabel τR rR),
        ⟨⟨⟨rL, hrL, rfl⟩, ⟨rR, hrR, rfl⟩⟩, (cutCompatible_transport τL τR g rL rR).mp hc⟩,
        (cutOut_transport τL τR g rL rR).symm⟩

theorem legal_transport (L : Code nL) (R : Code nR) (g : Glue nL nR nP)
    (h : Legal (L.relabel τL) (R.relabel τR) g) : Legal L R (g.transport τL τR) := by
  set θ := Equiv.sumCongr τL τR with hθ
  have hpair : ∀ x, (g.transport τL τR).pair (θ x) = θ (g.pair x) :=
    transport_pair_apply τL τR g
  have hrange := range_keep_transport τL τR g
  have htwo : ∀ x, twoOf L R (θ x) = twoOf (L.relabel τL) (R.relabel τR) x :=
    fun x => (twoOf_relabel τL τR L R x).symm
  have hopen : ∀ x, OpenAt L R (g.transport τL τR) (θ x) ↔
      OpenAt (L.relabel τL) (R.relabel τR) g x := by
    intro x
    simp only [OpenAt, hpair, htwo]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := θ.surjective y
    rw [hpair, hpair, h1]
  · intro i
    obtain ⟨i', rfl⟩ := τL.surjective i
    have := hpair (.inl i')
    rcases h2 i' with e | ⟨j, e⟩
    · left; simpa [hθ, e] using this
    · right; exact ⟨τR j, by simpa [hθ, e] using this⟩
  · intro j
    obtain ⟨j', rfl⟩ := τR.surjective j
    have := hpair (.inr j')
    rcases h3 j' with e | ⟨i, e⟩
    · left; simpa [hθ, e] using this
    · right; exact ⟨τL i, by simpa [hθ, e] using this⟩
  · obtain ⟨x, hx⟩ := h4
    exact ⟨θ x, by rw [hpair]; exact fun e => hx (θ.injective e)⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := θ.surjective y
    rw [hpair] at hy ⊢
    rw [htwo, htwo]
    exact h5 x (fun e => hy (by rw [e]))
  · intro y hy
    obtain ⟨x, rfl⟩ := θ.surjective y
    rw [hpair] at hy
    rw [hrange]
    exact h6 x (θ.injective hy)
  · intro y hy ho
    obtain ⟨x, rfl⟩ := θ.surjective y
    rw [hpair] at hy
    rw [hrange]
    exact h7 x (fun e => hy (by rw [e])) ((hopen x).not.mp ho)
  · intro y hy ho
    obtain ⟨x, rfl⟩ := θ.surjective y
    rw [hpair] at hy
    rw [hrange, hpair, hrange]
    exact h8 x (fun e => hy (by rw [e])) ((hopen x).mp ho)

theorem euler_transport (L : Code nL) (R : Code nR) (g : Glue nL nR nP)
    (h : Euler (L.relabel τL) (R.relabel τR) g) : Euler L R (g.transport τL τR) := by
  set θ := Equiv.sumCongr τL τR with hθ
  unfold Euler cyc at h ⊢
  have key : ∀ i, (g.transport τL τR).pair (.inl (τL i)) ≠ .inl (τL i) ↔
      g.pair (.inl i) ≠ .inl i := by
    intro i
    have := transport_pair_apply τL τR g (.inl i)
    simp only [hθ, Equiv.sumCongr_apply, Sum.map_inl] at this
    rw [this]
    constructor
    · intro hne e; apply hne; rw [e]; rfl
    · intro hne e; apply hne
      have := congrArg (Equiv.sumCongr τL τR).symm e
      simpa using this
  have hs : sharedCount (g.transport τL τR) = sharedCount g := by
    unfold sharedCount
    apply Finset.card_bij' (fun i _ => τL.symm i) (fun i _ => τL i)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [← key]; simpa using hi
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact (key i).mpr hi
    · intro i _; simp
    · intro i _; simp
  have hL : (L.relabel τL).ret.partition.parts.card = L.ret.partition.parts.card := by
    change (τL.symm.permCongr L.ret).partition.parts.card = _
    exact GoertzelV24RetainedSpliceFaceCount.card_permCongr_partition_parts _ _
  have hR : (R.relabel τR).ret.partition.parts.card = R.ret.partition.parts.card := by
    change (τR.symm.permCongr R.ret).partition.parts.card = _
    exact GoertzelV24RetainedSpliceFaceCount.card_permCongr_partition_parts _ _
  have hmerged : θ.permCongr (merged (L.relabel τL) (R.relabel τR)) = merged L R := by
    apply Equiv.ext
    intro x
    simp [merged_relabel, hθ]
  have hp : merged L R * (g.transport τL τR).pair =
      θ.permCongr (merged (L.relabel τL) (R.relabel τR) * g.pair) := by
    rw [Equiv.permCongr_mul, hmerged]
    rfl
  rw [hs, ← hL, ← hR, hp, GoertzelV24RetainedSpliceFaceCount.card_permCongr_partition_parts]
  exact h

end Transport

end

end Mettapedia.GraphTheory.FourColor.PhysicalForkCode
