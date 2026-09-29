import Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphism

/-!
# Cofacial ports determine a cycle's orientation

A cycle with one exposed port at each vertex has two possible local rotations
at each vertex. A side mark on its darts is invariant under face traversal.
Consequently, ports on one face have the same local orientation. This holds
for every cycle length, without enumerating the possible assignments of turns.

The recognition interface records incidence and edge reversal only. Rotation
compatibility is a conclusion, obtained from cyclic vertex rotations and
cofaciality of the exposed ports.
-/

namespace Mettapedia.GraphTheory.FourColor.CycleBoundaryOrientation

open Equiv Equiv.Perm
open GoertzelV24OpenTangleComposition
open GoertzelV24CompositeSeamCubic
open SerialTangleFaceTransfer OpenTangleMarkedFace
open GoertzelV24PermutationOrbitSurgery GoertzelV24OrderedCutFaceReturnProfile

variable (k : ℕ) [NeZero k]

/-- Slot zero is the port; slots one and two point to the previous and next
cycle vertices respectively. -/
abbrev Dart := Fin k × Fin 3

def flipFun (d : Dart k) : Dart k :=
  match d.2 with
  | 0 => d
  | 1 => (d.1 - 1, 2)
  | 2 => (d.1 + 1, 1)

theorem flipFun_involutive : Function.Involutive (flipFun k) := by
  rintro ⟨i, j⟩
  fin_cases j <;> simp [flipFun]

def flip : Perm (Dart k) := (flipFun_involutive k).toPerm

/-- The two possible cyclic rotations of each three-dart vertex. -/
def turn (reverse : Fin k → Bool) : Perm (Dart k) where
  toFun d := (d.1, if reverse d.1 then d.2 - 1 else d.2 + 1)
  invFun d := (d.1, if reverse d.1 then d.2 + 1 else d.2 - 1)
  left_inv := by
    rintro ⟨i, j⟩
    cases h : reverse i <;> simp [h]
  right_inv := by
    rintro ⟨i, j⟩
    cases h : reverse i <;> simp [h]

def face (reverse : Fin k → Bool) : Perm (Dart k) := turn k reverse * flip k

/-- Internal directed edges have a fixed side; a port takes the side specified
by its local rotation. -/
def side (reverse : Fin k → Bool) (d : Dart k) : Bool :=
  match d.2 with
  | 0 => reverse d.1
  | 1 => false
  | 2 => true

theorem side_face (reverse : Fin k → Bool) (d : Dart k) :
    side k reverse (face k reverse d) = side k reverse d := by
  rcases d with ⟨i, j⟩
  fin_cases j
  · cases h : reverse i <;>
      simp [side, face, turn, flip, flipFun, h, show (-1 : Fin 3) = 2 by decide]
  · cases h : reverse (i - 1) <;> simp [side, face, turn, flip, flipFun, h]
  · cases h : reverse (i + 1) <;> simp [side, face, turn, flip, flipFun, h]

theorem side_eq_of_sameCycle (reverse : Fin k → Bool) {a b : Dart k}
    (h : (face k reverse).SameCycle a b) :
    side k reverse a = side k reverse b := by
  obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq h
  have hp : ∀ n : ℕ, ∀ d : Dart k,
      side k reverse ((face k reverse ^ n) d) = side k reverse d := by
    intro n
    induction n with
    | zero => intro d; rfl
    | succ n ih =>
        intro d
        rw [pow_succ, Perm.mul_apply, ih, side_face]
  rw [← hn, hp]

/-- Pairwise cofacial ports must agree on the direction of their local turns. -/
theorem turn_eq_of_cofacial_ports (reverse : Fin k → Bool) {i j : Fin k}
    (h : (face k reverse).SameCycle (i, 0) (j, 0)) :
    reverse i = reverse j := side_eq_of_sameCycle k reverse h

theorem constant_of_cofacial_ports (reverse : Fin k → Bool)
    (h : ∀ i j, (face k reverse).SameCycle (i, 0) (j, 0)) :
    ∃ b : Bool, reverse = fun _ => b := by
  refine ⟨reverse 0, funext fun i => ?_⟩
  exact turn_eq_of_cofacial_ports k reverse (h i 0)

theorem face_port_twice (b : Bool) (i : Fin k) :
    (face k (fun _ => b) ^ 2) (i, 0) = (if b then i + 1 else i - 1, 0) := by
  cases b <;>
    simp [pow_two, face, turn, flip, flipFun, show (-1 : Fin 3) = 2 by decide]

theorem face_port_internal (b : Bool) (i : Fin k) :
    (face k (fun _ => b) (i, 0)).2 ≠ 0 := by
  cases b <;>
    simp [face, turn, flip, flipFun, show (-1 : Fin 3) = 2 by decide]

/-- A finite three-dart rotation has just two fixed-point-free possibilities. -/
private theorem three_turns (p : Perm (Fin 3)) (h : ∀ j, p j ≠ j) :
    (∀ j, p j = j + 1) ∨ (∀ j, p j = j - 1) := by
  revert p
  decide +kernel

omit [NeZero k] in
/-- Every rotation which acts transitively within each three-dart vertex has
the displayed local form. -/
theorem exists_turn (p : Perm (Dart k))
    (hv : ∀ d, (p d).1 = d.1)
    (hc : ∀ i j l, p.SameCycle (i, j) (i, l)) :
    ∃ reverse : Fin k → Bool, p = turn k reverse := by
  classical
  have hvi (d : Dart k) : (p.symm d).1 = d.1 := by
    simpa using (hv (p.symm d)).symm
  let q (i : Fin k) : Perm (Fin 3) :=
    { toFun := fun j => (p (i, j)).2
      invFun := fun j => (p.symm (i, j)).2
      left_inv := by
        intro j
        have he : (i, (p (i, j)).2) = p (i, j) := Prod.ext (hv (i, j)).symm rfl
        change (p.symm (i, (p (i, j)).2)).2 = j
        rw [he, p.symm_apply_apply]
      right_inv := by
        intro j
        have he : (i, (p.symm (i, j)).2) = p.symm (i, j) :=
          Prod.ext (hvi (i, j)).symm rfl
        change (p (i, (p.symm (i, j)).2)).2 = j
        rw [he, p.apply_symm_apply] }
  have hq (i : Fin k) : ∀ j, q i j ≠ j := by
    intro j hj
    have hf : p (i, j) = (i, j) := Prod.ext (hv _) hj
    have hp : ∀ n : ℕ, (p ^ n) (i, j) = (i, j) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, Perm.mul_apply, hf, ih]
    obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq (hc i j (j + 1))
    rw [hp] at hn
    have he : j = j + 1 := congrArg Prod.snd hn
    have hne : ∀ j : Fin 3, j ≠ j + 1 := by decide +kernel
    exact hne j he
  have hex (i : Fin k) : ∃ b : Bool, ∀ j,
      p (i, j) = (i, if b then j - 1 else j + 1) := by
    rcases three_turns (q i) (hq i) with h | h
    · exact ⟨false, fun j => Prod.ext (hv _) (h j)⟩
    · exact ⟨true, fun j => Prod.ext (hv _) (h j)⟩
  choose reverse hr using hex
  refine ⟨reverse, Equiv.ext ?_⟩
  rintro ⟨i, j⟩
  exact hr i j

section Recognition

variable {V I B : Type*} (T : OpenTangleData V I B)

/-- Cycle incidence coordinates, without any assumption on local rotations.
The flip fixes exposed ports and pairs the two darts of each cycle edge. -/
structure Incidence where
  vertex : Fin k ≃ V
  port : Fin k ≃ B
  darts : Dart k ≃ I ⊕ B
  boundary : ∀ i, darts (i, 0) = Sum.inr (port i)
  vert : ∀ d, T.vertOf (darts d) = vertex d.1
  alpha : ∀ d, darts (flip k d) =
    Equiv.sumCongr T.interiorAlpha (Equiv.refl B) (darts d)

variable {k T} (C : Incidence k T)

def Incidence.rotation : Perm (Dart k) := C.darts.symm.permCongr T.rho

theorem Incidence.rotation_vertex (d : Dart k) : (C.rotation d).1 = d.1 := by
  apply C.vertex.injective
  rw [← C.vert, ← C.vert d]
  change T.vertOf (C.darts (C.darts.symm (T.rho (C.darts d)))) = _
  rw [C.darts.apply_symm_apply]
  exact T.vert_rho _

theorem Incidence.rotation_sameCycle (h : OpenRotationCyclic T)
    (i : Fin k) (j l : Fin 3) : (C.rotation).SameCycle (i, j) (i, l) := by
  have : Finite (I ⊕ B) := Finite.of_equiv (Dart k) C.darts
  have hs : T.rho.SameCycle (C.darts (i, j)) (C.darts (i, l)) := by
    apply h
    simp only [C.vert]
  simpa only [rotation, Equiv.symm_apply_apply] using
    (permCongr_sameCycle_iff C.darts.symm T.rho _ _).2 hs

theorem Incidence.exists_turn (h : OpenRotationCyclic T) :
    ∃ reverse : Fin k → Bool, C.rotation = turn k reverse :=
  CycleBoundaryOrientation.exists_turn k C.rotation C.rotation_vertex (C.rotation_sameCycle h)

theorem Incidence.face_congr {reverse : Fin k → Bool}
    (h : C.rotation = turn k reverse) :
    C.darts.permCongr (face k reverse) = openPhi T := by
  apply Equiv.ext
  intro d
  obtain ⟨d, rfl⟩ := C.darts.surjective d
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  change C.darts (turn k reverse (flip k d)) = T.rho _
  rw [← h]
  change C.darts (C.darts.symm (T.rho (C.darts (flip k d)))) = _
  rw [C.darts.apply_symm_apply, C.alpha]

/-- Cyclic vertex rotations and one exposed face determine the rotation of
the entire cycle, up to a single global reversal. -/
theorem Incidence.uniform_rotation
    (hrotation : OpenRotationCyclic T)
    (hface : ∀ b c : B, (openPhi T).SameCycle (.inr b) (.inr c)) :
    ∃ b : Bool, ∀ d, T.rho (C.darts d) = C.darts (turn k (fun _ => b) d) := by
  have : Finite (I ⊕ B) := Finite.of_equiv (Dart k) C.darts
  obtain ⟨reverse, hr⟩ := C.exists_turn hrotation
  have hc : ∀ i j, (face k reverse).SameCycle (i, 0) (j, 0) := by
    intro i j
    apply (permCongr_sameCycle_iff C.darts (face k reverse) _ _).1
    rw [C.face_congr hr, C.boundary, C.boundary]
    exact hface _ _
  obtain ⟨b, rfl⟩ := constant_of_cofacial_ports k reverse hc
  refine ⟨b, fun d => ?_⟩
  have he := Equiv.congr_fun hr d
  exact (C.darts.apply_symm_apply _).symm.trans (congrArg C.darts he)

theorem Incidence.boundary_iff (d : Dart k) :
    Boundary (C.darts d) ↔ d.2 = 0 := by
  constructor
  · intro h
    rcases hd : C.darts d with a | b
    · simp only [hd, Boundary] at h
    · obtain ⟨i, rfl⟩ := C.port.surjective b
      have he : C.darts d = C.darts (i, 0) := hd.trans (C.boundary i).symm
      exact congrArg Prod.snd (C.darts.injective he)
  · intro h
    rcases d with ⟨i, j⟩
    change j = 0 at h
    subst j
    rw [C.boundary]
    trivial

/-- The exact cyclic port order follows from the recognized rotation. There
is one internal dart between successive visits to the boundary. -/
theorem Incidence.returnCode_of_uniform_rotation
    [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
    {b : Bool}
    (hrotation : ∀ d, T.rho (C.darts d) = C.darts (turn k (fun _ => b) d))
    (i : Fin k) :
    OpenTanglePortReplacement.returnCode T (C.port i) =
      C.port (if b then i + 1 else i - 1) := by
  have hstep (d : Dart k) : openPhi T (C.darts d) = C.darts (face k (fun _ => b) d) := by
    change T.rho (Equiv.sumCongr T.interiorAlpha (Equiv.refl B) (C.darts d)) = _
    rw [← C.alpha, hrotation]
    rfl
  let first : {d : I ⊕ B // Boundary d} := ⟨.inr (C.port i), trivial⟩
  let last : {d : I ⊕ B // Boundary d} :=
    ⟨.inr (C.port (if b then i + 1 else i - 1)), trivial⟩
  have hreturn : PermutationFirstReturnRestriction.ReturnArc (openPhi T) Boundary
      first.1 last.1 2 := by
    refine ⟨by decide, ?_, ?_⟩
    · change (openPhi T ^ 2) (.inr (C.port i)) = .inr _
      rw [← C.boundary i, pow_two, Perm.mul_apply, hstep, hstep]
      have h := congrArg C.darts (face_port_twice k b i)
      simpa only [pow_two, Perm.mul_apply, C.boundary] using h
    · intro n hn hn2
      have he : n = 1 := by omega
      subst n
      change ¬ Boundary ((openPhi T ^ 1) (.inr (C.port i)))
      rw [pow_one, ← C.boundary, hstep, C.boundary_iff]
      exact face_port_internal k b i
  have hn := PermutationFirstReturnRestriction.nextHit_eq_of_returnArc
    (openPhi T) Boundary first last hreturn
  have hp := congrArg (SerialTangleFaceCode.boundaryCoordinate I B) hn
  change SerialTangleFaceCode.boundaryCoordinate I B
    (nextHitPerm (openPhi T) Boundary first) = _
  exact hp

end Recognition

end Mettapedia.GraphTheory.FourColor.CycleBoundaryOrientation
