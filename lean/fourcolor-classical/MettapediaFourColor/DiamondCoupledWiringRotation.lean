import MettapediaFourColor.DiamondCoupledWiring
import MettapediaFourColor.PhysicalKempeBoundary
import Mettapedia.GraphTheory.FourColor.OpenTangleClosedWitness

/-!
# Closing an actual exterior with the coupled diamond wiring

The exterior retains every vertex, dart and vertex rotation. Two pairs of its
ports become wires; four other ports meet two newly introduced cubic vertices.
The central edge couples these vertices. Separation of the endpoints of each
wire is an explicit geometric hypothesis, necessary for a loop-free map.
-/

namespace FourColor.DiamondCoupledWiring.Rotation

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24RotationSpliceConstructor
open OpenTangleClosedWitness GoertzelV24RotationDartColoring

noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev PhysicalColor := Mettapedia.GraphTheory.FourColor.Color
abbrev palette := PhysicalKempeBoundary.palette
abbrev Dart (I : Type*) := (I ⊕ Fin 8) ⊕ Fin 6

def coreVertex : Fin 6 → Fin 2 := ![0, 0, 0, 1, 1, 1]
def coreEdge : Fin 6 → Fin 7 := ![1, 2, 6, 4, 5, 6]

def coreRotation : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 0, 4, 5, 3]
  invFun := ![2, 0, 1, 5, 3, 4]
  left_inv := by decide
  right_inv := by decide

def seamFun : Fin 8 ⊕ Fin 6 → Fin 8 ⊕ Fin 6 := Sum.elim
  ![.inl 1, .inl 0, .inr 0, .inr 1, .inl 5, .inl 4, .inr 3, .inr 4]
  ![.inl 2, .inl 3, .inr 5, .inl 6, .inl 7, .inr 2]

def seam : Equiv.Perm (Fin 8 ⊕ Fin 6) where
  toFun := seamFun
  invFun := seamFun
  left_inv := by decide
  right_inv := by decide

variable {V I : Type*} (O : OpenTangleData V I (Fin 8))

/-- The free wires need distinct exterior endpoints. The four attachments to
new vertices and the new central edge cannot create a self-loop. -/
def Separated : Prop := O.boundaryVert 0 ≠ O.boundaryVert 1 ∧
  O.boundaryVert 4 ≠ O.boundaryVert 5

def alpha : Equiv.Perm (Dart I) :=
  (Equiv.sumAssoc I (Fin 8) (Fin 6)).trans
    ((Equiv.sumCongr O.interiorAlpha seam).trans
      (Equiv.sumAssoc I (Fin 8) (Fin 6)).symm)

def vertex : Dart I → V ⊕ Fin 2 :=
  Sum.elim (Sum.inl ∘ O.vertOf) (Sum.inr ∘ coreVertex)

variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- The complete rewired map, including the two new vertices. -/
def data (h : Separated O) : RewiredDartSystem (V ⊕ Fin 2) (Dart I) where
  vertOf := vertex O
  alpha := alpha O
  rho := Equiv.sumCongr O.rho coreRotation
  alpha_involutive := by
    rintro ((i | b) | j)
    · change Sum.inl (Sum.inl (O.interiorAlpha (O.interiorAlpha i))) = _
      rw [O.interiorAlpha_involutive]
    · fin_cases b <;> rfl
    · fin_cases j <;> rfl
  alpha_fixfree := by
    rintro ((i | b) | j)
    · exact fun he => O.interiorAlpha_fixfree i (Sum.inl.inj (Sum.inl.inj he))
    · fin_cases b <;> simp [alpha, seam, seamFun]
    · fin_cases j <;> simp [alpha, seam, seamFun]
  vert_rho := by
    rintro (d | j)
    · change Sum.inl (O.vertOf (O.rho d)) = Sum.inl (O.vertOf d)
      exact congrArg Sum.inl (O.vert_rho d)
    · fin_cases j <;> rfl
  outer := .inl O.outer
  no_self_loops := by
    rintro ((i | b) | j)
    · exact fun he => O.interior_no_self_loops i (Sum.inl.inj he)
    · fin_cases b <;> dsimp [vertex, alpha, seam, seamFun, coreVertex]
      · exact fun he => h.1 (Sum.inl.inj he)
      · exact fun he => h.1 (Sum.inl.inj he).symm
      · exact Sum.inl_ne_inr
      · exact Sum.inl_ne_inr
      · exact fun he => h.2 (Sum.inl.inj he)
      · exact fun he => h.2 (Sum.inl.inj he).symm
      · exact Sum.inl_ne_inr
      · exact Sum.inl_ne_inr
    · fin_cases j <;> dsimp [vertex, alpha, seam, seamFun, coreVertex]
      all_goals first | exact Sum.inr_ne_inl | exact fun he => by cases he

abbrev closed (h : Separated O) := (data O h).toRotationSystem

omit [DecidableEq V] in
/-- The closure introduces precisely two vertices; no auxiliary wire vertex
is hidden in the construction. -/
theorem vertex_count : Fintype.card (V ⊕ Fin 2) = Fintype.card V + 2 := by simp

end
end FourColor.DiamondCoupledWiring.Rotation
