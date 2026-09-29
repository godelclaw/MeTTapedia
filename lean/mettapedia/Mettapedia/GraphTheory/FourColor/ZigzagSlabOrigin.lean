import Mettapedia.GraphTheory.FourColor.SlabAssembly
import Mettapedia.GraphTheory.FourColor.HexagonalTubeChain

/-!
# Changing the origin of an embedded zigzag row

Cyclic shifts act on the actual ring vertices and darts, preserving both
edge reversal and vertex rotation. Reindexing a recognized row therefore
changes only its coordinates, and can align its input with the preceding
row without losing geometric information.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24OpenTangleComposition

namespace ZigzagRing

variable {k : ℕ} [NeZero k]

def shiftVertex (a : Fin k) : Equiv.Perm (Vtx k) :=
  Equiv.sumCongr (Equiv.addRight a) (Equiv.addRight a)

def shiftInterior (a : Fin k) : Equiv.Perm (Dart k) :=
  let e := Equiv.prodCongr (Equiv.addRight a) (Equiv.refl Bool)
  Equiv.sumCongr e e

def shiftDart (a : Fin k) : Equiv.Perm (AllDart k) :=
  Equiv.sumCongr (shiftInterior a) (shiftVertex a)

theorem shiftDart_vert (a : Fin k) (d : AllDart k) :
    (ring k).vertOf (shiftDart a d) = shiftVertex a ((ring k).vertOf d) := by
  rcases d with (⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i) <;>
    simp [shiftDart, shiftInterior, shiftVertex, vertOf_apply,
      twoSidedOpenTangleVertOf, interiorVert, add_assoc, add_comm]

theorem shiftInterior_flip (a : Fin k) (d : Dart k) :
    flip k (shiftInterior a d) = shiftInterior a (flip k d) := by
  rcases d with ⟨i, b⟩ | ⟨i, b⟩ <;> rfl

theorem shiftDart_rho (a : Fin k) (d : AllDart k) :
    rho k (shiftDart a d) = shiftDart a (rho k d) := by
  rcases d with (⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i) <;>
    simp [shiftDart, shiftInterior, shiftVertex, rho, rhoFun,
      sub_eq_add_neg, add_assoc, add_comm]

end ZigzagRing

namespace TubeSlab

noncomputable section
universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {k : ℕ} [NeZero k] {inner : V → Prop}

namespace ZigzagSlab

open ZigzagRing

/-- The specialized ring embedding is an instance of the general slab. -/
def asSlab (S : ZigzagSlab RS k inner) : SlabOf RS (ring k) inner where
  ι := S.ι
  vtx := S.vtx
  ι_inj := S.ι_inj
  vtx_inj := S.vtx_inj
  vtx_not_inner := S.vtx_not_inner
  vert_ι := S.vert_ι
  alpha_interior := S.alpha_interior
  in_inner := S.in_inner
  out_not_inner := S.out_not_inner
  out_not_slab := S.out_not_slab
  cubic_slab := S.cubic_slab
  boundary_inner := S.boundary_inner

end ZigzagSlab

namespace SlabOf

open ZigzagRing

variable (S : SlabOf RS (ring k) inner)

/-- Shift the actual incidence embedding by a cyclic origin. -/
def shiftRing (a : Fin k) : SlabOf RS (ring k) inner where
  ι := S.ι ∘ shiftDart a
  vtx := S.vtx ∘ shiftVertex a
  ι_inj := S.ι_inj.comp (shiftDart a).injective
  vtx_inj := S.vtx_inj.comp (shiftVertex a).injective
  vtx_not_inner v := S.vtx_not_inner _
  vert_ι d := (S.vert_ι _).trans (congrArg S.vtx (shiftDart_vert a d))
  alpha_interior d := by
    change RS.alpha (S.ι (.inl (shiftInterior a d))) =
      S.ι (.inl (shiftInterior a (flip k d)))
    rw [S.alpha_interior]
    change S.ι (.inl (flip k (shiftInterior a d))) = _
    rw [shiftInterior_flip]
  in_inner i := S.in_inner (i + a)
  out_not_inner i := S.out_not_inner (i + a)
  out_not_slab i v := S.out_not_slab (i + a) (shiftVertex a v)
  cubic_slab := by
    rintro y ⟨v, hv⟩
    obtain ⟨x, hx⟩ := S.cubic_slab y ⟨shiftVertex a v, hv⟩
    exact ⟨(shiftDart a).symm x, by simpa using hx⟩
  boundary_inner b := by
    obtain ⟨i, hi⟩ := S.boundary_inner b
    refine ⟨i - a, ?_⟩
    change b.1.1 = RS.alpha (S.ι (.inr (.inl (i - a + a))))
    simpa only [sub_add_cancel] using hi

theorem shiftRing_inner' (a : Fin k) : (S.shiftRing a).inner' = S.inner' := by
  funext v
  apply propext
  change (inner v ∨ ∃ w, v = S.vtx (shiftVertex a w)) ↔ (inner v ∨ ∃ w, v = S.vtx w)
  constructor
  · rintro (h | ⟨w, hw⟩)
    · exact Or.inl h
    · exact Or.inr ⟨shiftVertex a w, hw⟩
  · rintro (h | ⟨w, hw⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(shiftVertex a).symm w, by simpa only [Equiv.apply_symm_apply] using hw⟩

theorem shiftRing_inEquiv (a : Fin k) :
    (S.shiftRing a).inEquiv = atOrigin S.inEquiv a := by
  ext i
  rfl

theorem shiftRing_rotationCompatible (a : Fin k) (hS : S.RotationCompatible) :
    (S.shiftRing a).RotationCompatible := by
  intro d
  change RS.rho (S.ι (shiftDart a d)) = S.ι (shiftDart a ((ring k).rho d))
  rw [hS]
  exact congrArg S.ι (shiftDart_rho a d)

end SlabOf
end
end TubeSlab
end Mettapedia.GraphTheory.FourColor
