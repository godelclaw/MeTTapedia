import Mettapedia.Computability.PNP.KernelFlipInvolution

/-!
# PNP v13: affine lock rigidity characterization

This file records the exact obstruction met by affine parity lock candidates.
For a satisfiable public system `A x = b`, a projected message coordinate is
rigid precisely when every homogeneous kernel direction fixes that coordinate.
Thus sparse parity syntax can obtain D.8 only by eliminating every
message-moving kernel direction.  A parity cycle retains a global complement
direction and fails D.8; a full-rank system can satisfy D.8, but its public
syndrome is then an algebraically decodable encoding rather than the sought
locked-CSP mechanism.

The theorem is a candidate-class boundary, not an Appendix-D construction.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-- One coordinate is constant across the affine fiber `A x = b`. -/
def LinearFiberCoordinateRigid {k m : Nat}
    (A : Matrix (Fin k) (Fin m) (ZMod 2)) (b : F2Vec k)
    (i : Fin m) : Prop :=
  forall x y : KernelFiber A b, x.val i = y.val i

/-- Every homogeneous direction of `A` fixes one coordinate. -/
def LinearKernelFixesCoordinate {k m : Nat}
    (A : Matrix (Fin k) (Fin m) (ZMod 2)) (i : Fin m) : Prop :=
  forall w : F2Vec m, IsKernelVector A w -> w i = 0

/-- Exact affine characterization: on a nonempty fiber, coordinate rigidity is
equivalent to the absence of a kernel flip at that coordinate. -/
theorem linearFiberCoordinateRigid_iff_kernelFixesCoordinate
    {k m : Nat} {A : Matrix (Fin k) (Fin m) (ZMod 2)}
    {b : F2Vec k} (i : Fin m) (hsat : Nonempty (KernelFiber A b)) :
    LinearFiberCoordinateRigid A b i <-> LinearKernelFixesCoordinate A i := by
  constructor
  · intro hrigid w hw
    rcases hsat with ⟨x⟩
    have heq := hrigid x (kernelFlip hw x)
    have hcancel : x.val i + 0 = x.val i + w i := by
      simpa [kernelFlip, f2AddVec] using heq
    exact add_left_cancel hcancel.symm
  · intro hkernel x y
    let w : F2Vec m := f2AddVec x.val y.val
    have hw : IsKernelVector A w := by
      unfold IsKernelVector w
      rw [f2MatVec_add, x.property, y.property]
      funext r
      exact f2_add_self (b r)
    have hzero := hkernel w hw
    change x.val i + y.val i = 0 at hzero
    calc
      x.val i = x.val i + (y.val i + y.val i) := by
        rw [f2_add_self, add_zero]
      _ = (x.val i + y.val i) + y.val i := by ac_rfl
      _ = y.val i := by rw [hzero, zero_add]

/-- A concrete message-moving kernel vector refutes coordinate rigidity on
every nonempty affine fiber. -/
theorem not_linearFiberCoordinateRigid_of_kernelFlip
    {k m : Nat} {A : Matrix (Fin k) (Fin m) (ZMod 2)}
    {b : F2Vec k} {i : Fin m} (hsat : Nonempty (KernelFiber A b))
    {w : F2Vec m} (hw : IsKernelVector A w) (hwi : w i = 1) :
    ¬ LinearFiberCoordinateRigid A b i := by
  intro hrigid
  have hfix :=
    (linearFiberCoordinateRigid_iff_kernelFixesCoordinate i hsat).mp hrigid w hw
  rw [hwi] at hfix
  exact one_ne_zero hfix

/-- A list-valued message projection is rigid across an affine fiber. -/
def LinearFiberMessageRigid {k m ell : Nat}
    (A : Matrix (Fin k) (Fin m) (ZMod 2)) (b : F2Vec k)
    (messageCoordinate : Fin ell -> Fin m) : Prop :=
  forall x y : KernelFiber A b,
    (fun j => x.val (messageCoordinate j)) =
      (fun j => y.val (messageCoordinate j))

/-- Multi-coordinate D.8 for an affine lock is exactly coordinatewise
annihilation of every homogeneous kernel direction. -/
theorem linearFiberMessageRigid_iff_kernelFixesMessage
    {k m ell : Nat} {A : Matrix (Fin k) (Fin m) (ZMod 2)}
    {b : F2Vec k} (messageCoordinate : Fin ell -> Fin m)
    (hsat : Nonempty (KernelFiber A b)) :
    LinearFiberMessageRigid A b messageCoordinate <->
      forall w : F2Vec m, IsKernelVector A w ->
        forall j, w (messageCoordinate j) = 0 := by
  constructor
  · intro hrigid w hw j
    have hcoord : LinearFiberCoordinateRigid A b (messageCoordinate j) := by
      intro x y
      exact congrFun (hrigid x y) j
    exact
      (linearFiberCoordinateRigid_iff_kernelFixesCoordinate
        (messageCoordinate j) hsat).mp hcoord w hw
  · intro hkernel x y
    funext j
    have hcoord : LinearFiberCoordinateRigid A b (messageCoordinate j) :=
      (linearFiberCoordinateRigid_iff_kernelFixesCoordinate
        (messageCoordinate j) hsat).mpr (fun w hw => hkernel w hw j)
    exact hcoord x y

end Mettapedia.Computability.PNP
