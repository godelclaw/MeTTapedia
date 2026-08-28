import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSpliceConstructor
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceTwoSided
import Mettapedia.GraphTheory.FourColor.GoertzelV24StellarStructure

/-!
# The stellar subdivision as an actual rotation system

The existing stellar files construct and analyse the new dart permutations.
This adapter supplies their vertex and edge carriers.  Old and apex darts are
based at old vertices; rim darts are based at the old face in which the new
hub vertex was inserted.  Edges are the computed two-dart orbits of the
stellar flip.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24StellarRotationSystem

open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationSpliceConstructor
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24StellarEuler
open GoertzelV24StellarSubdivision

noncomputable section

universe u v

variable {V : Type u} {E : Type v}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Vertices after stellar subdivision: the old vertices and one new hub for
each old face orbit. -/
abbrev StellarVertex (RS : RotationSystem V E) := V ⊕ OrbitFace RS

/-- The vertex supporting each stellar dart. -/
def stellarVertOf (RS : RotationSystem V E) :
    StellarDart RS.D → StellarVertex RS
  | Sum.inl dart => Sum.inl (RS.vertOf dart)
  | Sum.inr (Sum.inl dart) => Sum.inl (RS.vertOf (RS.alpha dart))
  | Sum.inr (Sum.inr dart) => Sum.inr (dartOrbitFace RS dart)

@[simp] theorem stellarVertOf_old (RS : RotationSystem V E) (dart : RS.D) :
    stellarVertOf RS (old dart) = Sum.inl (RS.vertOf dart) := rfl

@[simp] theorem stellarVertOf_apex (RS : RotationSystem V E) (dart : RS.D) :
    stellarVertOf RS (apex dart) = Sum.inl (RS.vertOf (RS.alpha dart)) := rfl

@[simp] theorem stellarVertOf_rim (RS : RotationSystem V E) (dart : RS.D) :
    stellarVertOf RS (rim dart) = Sum.inr (dartOrbitFace RS dart) := rfl

/-- The stellar permutations with their vertex map, before naming the edge
orbits. -/
def rewiredDartSystem (RS : RotationSystem V E) :
    RewiredDartSystem (StellarVertex RS) (StellarDart RS.D) where
  vertOf := stellarVertOf RS
  alpha := stellarFlip RS.alpha
  rho := stellarRotation RS.rho RS.alpha
  alpha_involutive := stellarFlip_involutive RS.alpha_involutive
  alpha_fixfree := stellarFlip_ne RS.alpha_fixfree
  vert_rho := by
    rintro (dart | dart | dart)
    · simp [RS.alpha_involutive]
    · simp [RS.vert_rho]
    · change Sum.inr (dartOrbitFace RS (RS.phi⁻¹ dart)) =
        Sum.inr (dartOrbitFace RS dart)
      congr 1
      simpa using (dartOrbitFace_phi_eq RS (RS.phi⁻¹ dart)).symm
  outer := old RS.outer
  no_self_loops := by
    rintro (dart | dart | dart)
    · simpa using RS.no_self_loops dart
    · simp
    · simp

/-- The stellar subdivision packaged as a complete rotation system. -/
def rotationSystem (RS : RotationSystem V E) :
    RotationSystem (StellarVertex RS) (rewiredDartSystem RS).Edge :=
  (rewiredDartSystem RS).toRotationSystem

@[simp] theorem rotationSystem_vertOf (RS : RotationSystem V E)
    (dart : StellarDart RS.D) :
    (rotationSystem RS).vertOf dart = stellarVertOf RS dart := rfl

@[simp] theorem rotationSystem_alpha (RS : RotationSystem V E)
    (dart : StellarDart RS.D) :
    (rotationSystem RS).alpha dart = stellarFlip RS.alpha dart := rfl

@[simp] theorem rotationSystem_rho (RS : RotationSystem V E)
    (dart : StellarDart RS.D) :
    (rotationSystem RS).rho dart = stellarRotation RS.rho RS.alpha dart := rfl

@[simp] theorem rotationSystem_phi (RS : RotationSystem V E)
    (dart : StellarDart RS.D) :
    (rotationSystem RS).phi dart = stellarFace RS.rho RS.alpha dart := rfl

/-- The stored vertex is constant along powers of the vertex rotation. -/
theorem vertOf_rho_pow (RS : RotationSystem V E) (steps : Nat) (dart : RS.D) :
    RS.vertOf ((RS.rho ^ steps) dart) = RS.vertOf dart := by
  induction steps generalizing dart with
  | zero => simp
  | succ steps ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      exact RS.vert_rho dart

/-- Darts on one stored rotation cycle are based at the same vertex. -/
theorem vertOf_eq_of_rho_sameCycle (RS : RotationSystem V E)
    {left right : RS.D} (hsame : RS.rho.SameCycle left right) :
    RS.vertOf left = RS.vertOf right := by
  obtain ⟨steps, hsteps⟩ :=
    GoertzelV24PermutationOrbitSurgery.exists_nat_pow_apply_eq hsame
  rw [← hsteps, vertOf_rho_pow]

/-- Every stellar edge has two distinct facial sides. -/
theorem orbitFacesTwoSided (RS : RotationSystem V E) :
    OrbitFacesTwoSided (rotationSystem RS) := by
  intro dart hsame
  apply stellar_two_sided RS.alpha_involutive RS.alpha_fixfree
    (fun oldDart hcycle =>
      RS.no_self_loops oldDart (vertOf_eq_of_rho_sameCycle RS hcycle)) dart
  exact Quotient.exact hsame

/-- Each facial orbit of the stellar subdivision contains exactly three
darts.  This is the cubicity input for its dual map. -/
theorem orbitFaceDarts_card_three (RS : RotationSystem V E)
    (face : OrbitFace (rotationSystem RS)) :
    (GoertzelV24FaceOrbitIncidence.orbitFaceDarts
      (rotationSystem RS) face).card = 3 := by
  classical
  obtain ⟨dart, rfl⟩ := Quotient.exists_rep face
  change
    (GoertzelV24FaceOrbitIncidence.orbitFaceDarts
      (rotationSystem RS)
      (GoertzelV24FaceOrbitIncidence.dartOrbitFace
        (rotationSystem RS) dart)).card = 3
  rw [GoertzelV24FaceOrbitIncidence.orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
  change
    (Finset.univ.filter fun other : StellarDart RS.D =>
      (stellarFace RS.rho RS.alpha).SameCycle dart other).card = 3
  let index := faceIndex RS.rho RS.alpha dart
  have hsame :
      (stellarFace RS.rho RS.alpha).SameCycle (old index) dart := by
    simpa only using
      (sameCycle_old_faceIndex (σ := RS.rho) (α := RS.alpha)
        RS.alpha_involutive dart)
  have horbit :
      (Finset.univ.filter fun other : StellarDart RS.D =>
        (stellarFace RS.rho RS.alpha).SameCycle dart other) =
        stellarFaceFinset RS.rho RS.alpha index := by
    ext other
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_stellarFaceFinset]
    rw [← stellarFace_sameCycle_old_iff RS.alpha_involutive]
    exact ⟨fun h => hsame.trans h, fun h => hsame.symm.trans h⟩
  rw [horbit]
  exact card_stellarFaceFinset _ _ _

end

end GoertzelV24StellarRotationSystem

end Mettapedia.GraphTheory.FourColor
