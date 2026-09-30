import Mettapedia.GraphTheory.FourColor.PaddedCycleCapTangle
import Mettapedia.GraphTheory.FourColor.FacialCoronaTraversal
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCyclicOrder

/-!
# Tracing a padded cap from its actual faces

The central face and two surrounding collars determine all eight stars in
each sector. Hexagonal and pentagonal face closure supplies the remaining
internal edge reversals. Vertex separation and exposed final ports are
separate geometric obligations; neither is hidden in the traversal data.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap.FaceTraversal

open Equiv Equiv.Perm PhysicalForkCodeFaces GoertzelV24OrbitFaceCyclicOrder
open GoertzelV24OpenTangleComposition

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E) (m : ℕ) [NeZero m] (root : RS.D)

def center (i : Fin m) : RS.D := (RS.phi ^ i.val) root
def incoming (i : Fin m) : RS.D := RS.alpha (RS.rho (center RS m root i))
def middle (i : Fin m) : RS.D := RS.alpha (RS.rho (incoming RS m root i))
def lastMiddle (i : Fin m) : RS.D := RS.alpha (RS.rho (middle RS m root i))
def outerIncoming (i : Fin m) : RS.D := RS.alpha (RS.rho (RS.rho (middle RS m root i)))
def outerFirst (i : Fin m) : RS.D := RS.alpha (RS.rho (outerIncoming RS m root i))
def outerMiddle (i : Fin m) : RS.D := RS.alpha (RS.rho (RS.rho (lastMiddle RS m root i)))
def outerLast (i : Fin m) : RS.D := RS.alpha (RS.rho (outerMiddle RS m root i))

/-- Base darts are in slot zero of the literal cap's stars. -/
def base (i : Fin m) (v : Fin 8) : RS.D :=
  ![RS.rho (RS.rho (center RS m root i)),
    RS.rho (RS.rho (incoming RS m root i)),
    middle RS m root i, lastMiddle RS m root i,
    RS.rho (RS.rho (outerIncoming RS m root i)),
    outerFirst RS m root i,
    RS.rho (RS.rho (outerMiddle RS m root i)),
    outerLast RS m root i] v

def atStar (p : Position m) : RS.D :=
  (RS.rho ^ p.2.2.val) (base RS m root p.1 p.2.1)

def dart (d : Dart m) : RS.D := atStar RS m root (position m d)
def vertex (v : Vertex m) : V := RS.vertOf (base RS m root v.1 v.2)

/-- These hypotheses inspect actual face sizes, not patch equivalences. -/
structure FaceLengths : Prop where
  central : (RS.faceOrbit root).card = m
  innerHexagon : ∀ i, (RS.faceOrbit (RS.alpha (center RS m root i))).card = 6
  outerHexagon : ∀ i, (RS.faceOrbit (base RS m root i 1)).card = 6
  outerPentagon : ∀ i, (RS.faceOrbit (lastMiddle RS m root i)).card = 5

private theorem period_of_length (d : RS.D) {n : ℕ}
    (h : (RS.faceOrbit d).card = n) : (RS.phi ^ n) d = d := by
  have he := (phi_isCycleOn_faceOrbit RS d).pow_card_apply (RS.mem_faceOrbit_self d)
  simpa only [h] using he

variable (hC : Cubic3 RS) (hf : FaceLengths RS m root)

include hf in
theorem center_step (i : Fin m) :
    RS.phi (center RS m root i) = center RS m root (i+1) := by
  have hp := period_of_length RS root hf.central
  by_cases hi : i.val + 1 < m
  · simp [center, Fin.add_def, Nat.mod_eq_of_lt hi, pow_succ', Perm.mul_apply]
  · have he : i.val + 1 = m := by omega
    have hzero : i+1 = (0 : Fin m) := by
      apply Fin.ext
      simp [Fin.add_def, he]
    rw [hzero]
    simpa only [center, Fin.val_zero, pow_zero, Perm.one_apply,
      ← Perm.mul_apply, ← pow_succ', he] using hp

include hC hf in
/-- The first collar's closing edge comes from its hexagonal face. -/
theorem middle_closing (i : Fin m) :
    RS.alpha (RS.rho (lastMiddle RS m root i)) = base RS m root (i+1) 1 := by
  have he := FacialCoronaTraversal.hexagonal_last RS (center RS m root) hC
    (center_step RS m root hf) i
    (period_of_length RS _ (hf.innerHexagon i))
  change RS.rho (lastMiddle RS m root i) =
    RS.alpha (RS.rho (RS.rho (incoming RS m root (i+1)))) at he
  simpa only [RS.alpha_involutive, base, Matrix.cons_val_one, Matrix.cons_val_zero] using
    congrArg RS.alpha he

include hC hf in
omit [NeZero m] in
/-- The pentagon closes the edge between the two outer intermediate stars. -/
theorem outer_middle_edge (i : Fin m) :
    RS.alpha (RS.rho (outerFirst RS m root i)) =
      RS.rho (RS.rho (outerMiddle RS m root i)) := by
  have hp := period_of_length RS _ (hf.outerPentagon i)
  have hs : (RS.phi ^ 3) (lastMiddle RS m root i) =
      RS.rho (outerFirst RS m root i) := by
    simp [pow_succ', Perm.mul_apply, RotationSystem.phi, outerFirst,
      outerIncoming, middle, lastMiddle, RS.alpha_involutive]
  have ht : (RS.phi ^ 2) (RS.alpha (RS.rho (RS.rho (outerMiddle RS m root i)))) =
      lastMiddle RS m root i := by
    simp [pow_succ', Perm.mul_apply, RotationSystem.phi, outerMiddle,
      RS.alpha_involutive, hC.cube]
  have he : RS.rho (outerFirst RS m root i) =
      RS.alpha (RS.rho (RS.rho (outerMiddle RS m root i))) := by
    apply (RS.phi ^ 2).injective
    rw [← hs, ← Perm.mul_apply, ← pow_add, show 2+3=5 by decide, hp, ht]
  simpa only [RS.alpha_involutive] using congrArg RS.alpha he

include hC hf in
/-- The second hexagon closes the last outer edge into the next sector. -/
theorem outer_closing (i : Fin m) :
    RS.alpha (RS.rho (outerLast RS m root i)) = base RS m root (i+1) 4 := by
  have hp := period_of_length RS _ (hf.outerHexagon (i+1))
  have hm := middle_closing RS m root hC hf i
  have hback : RS.alpha (base RS m root (i+1) 1) =
      RS.rho (lastMiddle RS m root i) := by
    rw [← hm, RS.alpha_involutive]
  have hs : (RS.phi ^ 3) (base RS m root (i+1) 1) =
      RS.rho (outerLast RS m root i) := by
    simp [pow_succ', Perm.mul_apply, RotationSystem.phi, hback, outerLast,
      outerMiddle]
  have ht : (RS.phi ^ 3) (RS.alpha (base RS m root (i+1) 4)) =
      base RS m root (i+1) 1 := by
    simp [base, pow_succ', Perm.mul_apply, RotationSystem.phi,
      outerIncoming, middle, incoming, RS.alpha_involutive, hC.cube]
  have he : RS.rho (outerLast RS m root i) = RS.alpha (base RS m root (i+1) 4) := by
    apply (RS.phi ^ 3).injective
    rw [← hs, ← Perm.mul_apply, ← pow_add, show 3+3=6 by decide, hp, ht]
  simpa only [RS.alpha_involutive] using congrArg RS.alpha he

include hC hf in
theorem central_edge (i : Fin m) :
    RS.alpha (center RS m root i) = RS.rho (RS.rho (center RS m root (i+1))) := by
  have he := center_step RS m root hf i
  change RS.rho (RS.alpha (center RS m root i)) = center RS m root (i+1) at he
  have hh := congrArg (fun d => RS.rho (RS.rho d)) he
  simpa only [hC.cube] using hh

include hC in
theorem dart_false (i : Fin m) (e : Fin 11) :
    dart RS m root (.inl (i,e,false)) =
      ![center RS m root i, RS.rho (lastMiddle RS m root i),
        RS.rho (outerLast RS m root i), RS.rho (center RS m root i),
        RS.rho (incoming RS m root i), RS.rho (middle RS m root i),
        RS.rho (RS.rho (middle RS m root i)),
        RS.rho (RS.rho (lastMiddle RS m root i)),
        RS.rho (outerIncoming RS m root i), RS.rho (outerFirst RS m root i),
        RS.rho (outerMiddle RS m root i)] e := by
  fin_cases e <;> simp [dart, position, atStar, base, pow_succ', hC.cube]

include hC in
theorem dart_true (i : Fin m) (e : Fin 11) :
    dart RS m root (.inl (i,e,true)) =
      ![RS.rho (RS.rho (center RS m root (i+1))),
        RS.rho (RS.rho (incoming RS m root (i+1))),
        RS.rho (RS.rho (outerIncoming RS m root (i+1))),
        incoming RS m root i, middle RS m root i, lastMiddle RS m root i,
        outerIncoming RS m root i, outerMiddle RS m root i,
        outerFirst RS m root i, RS.rho (RS.rho (outerMiddle RS m root i)),
        outerLast RS m root i] e := by
  fin_cases e <;> simp [dart, position, atStar, base, pow_succ', hC.cube]

include hC hf in
/-- Every internal edge of the literal cap is an actual ambient edge. -/
theorem dart_alpha (d : Interior m) :
    dart RS m root (.inl (alpha m d)) = RS.alpha (dart RS m root (.inl d)) := by
  have hn (i : Fin m) (e : Fin 11) :
      dart RS m root (.inl (i,e,true)) = RS.alpha (dart RS m root (.inl (i,e,false))) := by
    rw [dart_false RS m root hC, dart_true RS m root hC]
    fin_cases e
    · exact (central_edge RS m root hC hf i).symm
    · simpa [base] using (middle_closing RS m root hC hf i).symm
    · simpa [base] using (outer_closing RS m root hC hf i).symm
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (outer_middle_edge RS m root hC hf i).symm
    · rfl
  rcases d with ⟨i,e,b⟩
  cases b
  · exact hn i e
  · have he := congrArg RS.alpha (hn i e)
    simpa only [alpha, flip, Bool.not_true, Equiv.coe_fn_mk, RS.alpha_involutive] using he.symm

include hC in
omit [NeZero m] in
theorem atStar_rotate (p : Position m) :
    atStar RS m root (rotatePosition m p) = RS.rho (atStar RS m root p) := by
  rcases p with ⟨i,v,s⟩
  fin_cases s <;> simp [atStar, rotatePosition, pow_succ', Perm.mul_apply, hC.cube]

include hC in
/-- The dart interpretation commutes with the original cyclic vertex stars. -/
theorem dart_rotation (d : Dart m) :
    dart RS m root (rotation m d) = RS.rho (dart RS m root d) := by
  change atStar RS m root (position m (star m (rotatePosition m (position m d)))) = _
  rw [position_star]
  exact atStar_rotate RS m root hC _

theorem dart_vertex (d : Dart m) :
    RS.vertOf (dart RS m root d) = vertex RS m root (vertexOf m d) := by
  generalize hp : position m d = p
  rcases p with ⟨i,v,s⟩
  change RS.vertOf (atStar RS m root (position m d)) =
    RS.vertOf (base RS m root (position m d).1 (position m d).2.1)
  rw [hp]
  fin_cases s <;> simp [atStar, pow_succ', Perm.mul_apply, RS.vert_rho]

end Mettapedia.GraphTheory.FourColor.PaddedCycleCap.FaceTraversal
