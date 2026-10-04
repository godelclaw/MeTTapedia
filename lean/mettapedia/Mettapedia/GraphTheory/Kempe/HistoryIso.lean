import Mettapedia.GraphTheory.FourColor.KempeChainCertificate
import Mettapedia.GraphTheory.Kempe.Symm

/-! # Physical histories under graph isomorphisms

Renaming vertices transports actual components and preserves the exact
number of physical switches. No finite component enumeration is used.
-/

namespace SimpleGraph.KempeHistoryIso

open Mettapedia.GraphTheory.FourColor.KempeChainCertificate
open Mettapedia.GSLT.Ultrainfinite

variable {V W α : Type*} {G : SimpleGraph V} {H : SimpleGraph W} [DecidableEq α]

def pull (f : H ≃g G) (C : G.Coloring α) : H.Coloring α := C.comp f.toHom

def bicoloredIso (f : H ≃g G) (C : G.Coloring α) (a b : α) :
    (pull f C).bicoloredSubgraph a b ≃g C.bicoloredSubgraph a b where
  toFun x := ⟨f x.val, x.property⟩
  invFun x := ⟨f.symm x.val, by
    change C (f (f.symm x.val)) = a ∨ C (f (f.symm x.val)) = b
    rw [f.apply_symm_apply]
    exact x.property⟩
  left_inv _ := Subtype.ext (f.symm_apply_apply _)
  right_inv _ := Subtype.ext (f.apply_symm_apply _)
  map_rel_iff' := f.map_rel_iff

theorem step (f : H ≃g G) {C D : G.Coloring α} (s : Step C D) :
    Nonempty (Step (pull f C) (pull f D)) := by
  cases s with
  | switch a b K =>
      let e := bicoloredIso f C a b
      let L := K.map e.symm.toHom
      have membership (v : W) :
          v ∈ (pull f C).kempeComponentSet a b L ↔
            f v ∈ C.kempeComponentSet a b K := by
        constructor
        · rintro ⟨hv, h⟩
          refine ⟨hv, ?_⟩
          exact (ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map (φ := e.symm)).mpr h
        · rintro ⟨hv, h⟩
          refine ⟨hv, ?_⟩
          exact (ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map (φ := e.symm)).mp h
      have eq : (pull f C).swapOnKempeComponent a b L =
          pull f (C.swapOnKempeComponent a b K) := by
        ext v
        by_cases hv : v ∈ (pull f C).kempeComponentSet a b L
        · rw [Coloring.swapOnKempeComponent_apply_of_mem _ hv]
          exact (C.swapOnKempeComponent_apply_of_mem ((membership v).mp hv)).symm
        · rw [Coloring.swapOnKempeComponent_apply_of_not_mem _ hv]
          exact (C.swapOnKempeComponent_apply_of_not_mem
            (fun h => hv ((membership v).mpr h))).symm
      exact eq ▸ ⟨.switch (pull f C) a b L⟩

theorem history (f : H ≃g G) {C D : G.Coloring α} (p : History C D) :
    ∃ q : History (pull f C) (pull f D), q.length = p.length := by
  induction p with
  | refl => exact ⟨.refl _, rfl⟩
  | cons s p ih =>
      obtain ⟨s'⟩ := step f s
      obtain ⟨p', length⟩ := ih
      exact ⟨.cons s' p', by simpa only [Route.length] using congrArg (· + 1) length⟩

end SimpleGraph.KempeHistoryIso
