import Mettapedia.GraphTheory.FourColor.KempeChainCertificate

/-!
# Kempe histories that only rename colours

If every pair of distinct colours occupies one connected chain, every physical
component switch is a global colour transposition. The equality pattern of the
colouring is therefore invariant along arbitrary finite GSLT histories.
The chains may revisit vertices; only their adjacency and exact support matter.
-/

namespace Mettapedia.GraphTheory.FourColor.KempePaletteRigidity

open KempeChainCertificate

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq V] [DecidableEq α]

def PaletteOrbit (base : V → α) (C : G.Coloring α) : Prop :=
  ∃ π : Equiv.Perm α, ∀ v, C v = π (base v)

/-- Exact connected supports suffice; no enumeration of recolouring histories
or restriction on their length is involved. -/
theorem paletteOrbit_switch (base : V → α) (chain : α → α → List V)
    (connected : ∀ a b, a ≠ b → (chain a b).IsChain G.Adj)
    (support : ∀ a b, a ≠ b → ∀ v, v ∈ chain a b ↔ base v = a ∨ base v = b)
    (C : G.Coloring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (hC : PaletteOrbit base C) : PaletteOrbit base (C.swapOnKempeComponent a b K) := by
  classical
  obtain ⟨π, hC⟩ := hC
  by_cases hab : a = b
  · subst b
    refine ⟨π, fun v => ?_⟩
    by_cases hv : v ∈ C.kempeComponentSet a a K
    · simpa using (C.swapOnKempeComponent_apply_of_mem hv).trans (by simpa using hC v)
    · exact (C.swapOnKempeComponent_apply_of_not_mem hv).trans (hC v)
  · have hpre : π.symm a ≠ π.symm b := fun h => hab (π.symm.injective h)
    have active (v : V) : (C v = a ∨ C v = b) ↔ v ∈ chain (π.symm a) (π.symm b) := by
      rw [support _ _ hpre, hC v]
      simp only [← Equiv.eq_symm_apply]
    obtain ⟨⟨x, hx⟩, hK⟩ := K.exists_rep
    have hxK : x ∈ C.kempeComponentSet a b K := ⟨hx, hK⟩
    have hxc := (active x).mp hx
    have hclosed : ∀ y ∈ chain (π.symm a) (π.symm b), ∀ z,
        G.Adj y z → (C z = a ∨ C z = b) → z ∈ chain (π.symm a) (π.symm b) :=
      fun _ _ z _ hz => (active z).mp hz
    refine ⟨π.trans (Equiv.swap a b), fun v => ?_⟩
    rw [C.swap_apply_of_chain a b K _ (connected _ _ hpre)
      (fun y hy => (active y).mpr hy) hclosed hxc hxK v]
    change (if v ∈ chain (π.symm a) (π.symm b) then Equiv.swap a b (C v) else C v) =
      Equiv.swap a b (π (base v))
    split_ifs with hv
    · rw [hC v]
    · have hn : ¬ (C v = a ∨ C v = b) := fun h => hv ((active v).mp h)
      rw [← hC v, Equiv.swap_apply_of_ne_of_ne (fun h => hn (Or.inl h))
        (fun h => hn (Or.inr h))]

/-- Every finite history preserves the base equality pattern up to one global
permutation, even when its successive colour pairs and components are adaptive. -/
theorem history_paletteOrbit (base : V → α) (chain : α → α → List V)
    (connected : ∀ a b, a ≠ b → (chain a b).IsChain G.Adj)
    (support : ∀ a b, a ≠ b → ∀ v, v ∈ chain a b ↔ base v = a ∨ base v = b)
    {C D : G.Coloring α} (p : History C D) (hC : PaletteOrbit base C) :
    PaletteOrbit base D :=
  history_preserves (PaletteOrbit base) (paletteOrbit_switch base chain connected support) p hC

end Mettapedia.GraphTheory.FourColor.KempePaletteRigidity
