import Mettapedia.Computability.PNP.KernelFlipInvolution

/-!
# PNP v13 real rung one: admissible linear public surface

This file opens the replacement for the rejected scaled Phase E family.  The
public instance is `(A, A x)` over `F₂^m`, where `A` is a certified invertible
linear map.  The full public instance determines the selected witness
coordinate, but no elementary public coordinate of `A`, `A⁻¹`, or the
right-hand side is itself a target tag once the target index has a distinct
spare coordinate.

The hard adaptive row-observer counting theorem is not asserted here.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-- Certified invertible `F₂`-linear map on the square witness space. -/
structure V13F2LinearEquiv (m : Nat) where
  toEquiv : F2Vec m ≃ F2Vec m
  map_add :
    ∀ x y : F2Vec m,
      toEquiv (f2AddVec x y) =
        f2AddVec (toEquiv x) (toEquiv y)
  map_zero : toEquiv (f2ZeroVec m) = f2ZeroVec m

theorem v13RealLinearEquiv_ext {m : Nat} (A B : V13F2LinearEquiv m)
    (h : ∀ x : F2Vec m, A.toEquiv x = B.toEquiv x) :
    A = B := by
  cases A with
  | mk Ato Aadd Azero =>
      cases B with
      | mk Bto Badd Bzero =>
          have hto : Ato = Bto := Equiv.ext h
          subst hto
          rfl

def v13RealLinearComp {m : Nat}
    (B A : V13F2LinearEquiv m) : V13F2LinearEquiv m where
  toEquiv :=
    { toFun := fun x => B.toEquiv (A.toEquiv x)
      invFun := fun x => A.toEquiv.symm (B.toEquiv.symm x)
      left_inv := by
        intro x
        simp
      right_inv := by
        intro x
        simp }
  map_add := by
    intro x y
    change
      B.toEquiv (A.toEquiv (f2AddVec x y)) =
        f2AddVec (B.toEquiv (A.toEquiv x))
          (B.toEquiv (A.toEquiv y))
    rw [A.map_add, B.map_add]
  map_zero := by
    change B.toEquiv (A.toEquiv (f2ZeroVec m)) = f2ZeroVec m
    rw [A.map_zero, B.map_zero]

/-- Public instance for the real rung-one replacement family.  The certified
linear equivalence packages an invertible square `F₂`-linear map; the public
right-hand side is `b = A x`. -/
structure V13RealLinearPublic (m : Nat) where
  A : V13F2LinearEquiv m
  b : F2Vec m

/-- Hidden world: a witness vector and the sampled invertible public map. -/
structure V13RealLinearWorld (m : Nat) where
  x : F2Vec m
  A : V13F2LinearEquiv m

def v13RealLinearPublicInput {m : Nat}
    (omega : V13RealLinearWorld m) : V13RealLinearPublic m where
  A := omega.A
  b := omega.A.toEquiv omega.x

def v13RealLinearTarget {m : Nat} (i₀ : Fin m)
    (omega : V13RealLinearWorld m) : ZMod 2 :=
  omega.x i₀

def v13RealLinearFullDecoder {m : Nat} (i₀ : Fin m)
    (publicInput : V13RealLinearPublic m) : ZMod 2 :=
  publicInput.A.toEquiv.symm publicInput.b i₀

theorem v13RealLinear_fullPublic_decodes_target {m : Nat} (i₀ : Fin m)
    (omega : V13RealLinearWorld m) :
    v13RealLinearFullDecoder i₀ (v13RealLinearPublicInput omega) =
      v13RealLinearTarget i₀ omega := by
  simp [v13RealLinearFullDecoder, v13RealLinearPublicInput,
    v13RealLinearTarget]

theorem v13RealLinear_fullPublic_determines_target {m : Nat} (i₀ : Fin m) :
    ∀ omega₀ omega₁ : V13RealLinearWorld m,
      v13RealLinearPublicInput omega₀ =
        v13RealLinearPublicInput omega₁ →
      v13RealLinearTarget i₀ omega₀ =
        v13RealLinearTarget i₀ omega₁ := by
  intro omega₀ omega₁ hpublic
  rw [← v13RealLinear_fullPublic_decodes_target i₀ omega₀,
    ← v13RealLinear_fullPublic_decodes_target i₀ omega₁,
    hpublic]

/-- Elementary public-coordinate reads.  The `mapValue` and `inverseValue`
coordinates cover individual truth-table bits of the certified map and its
inverse; `rhs` covers one bit of `A x`. -/
inductive V13RealLinearPublicCoordinate (m : Nat) where
  | mapValue : F2Vec m → Fin m → V13RealLinearPublicCoordinate m
  | inverseValue : F2Vec m → Fin m → V13RealLinearPublicCoordinate m
  | rhs : Fin m → V13RealLinearPublicCoordinate m

def v13RealLinearCoordinateValue {m : Nat}
    (coordinate : V13RealLinearPublicCoordinate m)
    (publicInput : V13RealLinearPublic m) : ZMod 2 :=
  match coordinate with
  | .mapValue probe row => publicInput.A.toEquiv probe row
  | .inverseValue probe row => publicInput.A.toEquiv.symm probe row
  | .rhs row => publicInput.b row

def V13RealLinearCoordinateDeterminesTarget {m : Nat}
    (i₀ : Fin m) (coordinate : V13RealLinearPublicCoordinate m) : Prop :=
  ∀ omega : V13RealLinearWorld m,
    v13RealLinearCoordinateValue coordinate
        (v13RealLinearPublicInput omega) =
      v13RealLinearTarget i₀ omega

/-- The checked public-surface certificate for the square linear replacement:
full public input decodes and determines the target coordinate, while no
elementary public coordinate is a deterministic target tag when a spare
coordinate exists. -/
structure V13RealLinearPublicSurfaceCertificate (m : Nat) : Prop where
  fullPublicDecodes :
    ∀ i₀ : Fin m, ∀ omega : V13RealLinearWorld m,
      v13RealLinearFullDecoder i₀ (v13RealLinearPublicInput omega) =
        v13RealLinearTarget i₀ omega
  fullPublicDeterminesTarget :
    ∀ i₀ : Fin m, ∀ omega₀ omega₁ : V13RealLinearWorld m,
      v13RealLinearPublicInput omega₀ =
        v13RealLinearPublicInput omega₁ →
      v13RealLinearTarget i₀ omega₀ =
        v13RealLinearTarget i₀ omega₁
  noSingleCoordinateDeterminesTarget :
    ∀ i₀ spare : Fin m, spare ≠ i₀ →
      ∀ coordinate : V13RealLinearPublicCoordinate m,
        ¬ V13RealLinearCoordinateDeterminesTarget i₀ coordinate

def v13RealLinearSingleBit {m : Nat} (i : Fin m) : F2Vec m :=
  fun r => if r = i then 1 else 0

/-- Identity certified as an invertible `F₂`-linear map. -/
def v13RealLinearIdentity (m : Nat) : V13F2LinearEquiv m where
  toEquiv := Equiv.refl (F2Vec m)
  map_add := by
    intro x y
    rfl
  map_zero := rfl

/-- Coordinate permutation certified as an invertible `F₂`-linear map. -/
def v13RealLinearPerm {m : Nat} (σ : Equiv.Perm (Fin m)) :
    V13F2LinearEquiv m where
  toEquiv :=
    { toFun := fun x r => x (σ.symm r)
      invFun := fun x r => x (σ r)
      left_inv := by
        intro x
        funext r
        simp
      right_inv := by
        intro x
        funext r
        simp }
  map_add := by
    intro x y
    funext r
    simp [f2AddVec]
  map_zero := by
    funext r
    simp [f2ZeroVec]

lemma v13RealLinear_target_zero_world {m : Nat} (i₀ : Fin m)
    (A : V13F2LinearEquiv m) :
    v13RealLinearTarget i₀
        ({ x := f2ZeroVec m, A := A } : V13RealLinearWorld m) = 0 := by
  simp [v13RealLinearTarget, f2ZeroVec]

lemma v13RealLinear_target_one_world {m : Nat} (i₀ : Fin m)
    (A : V13F2LinearEquiv m) :
    v13RealLinearTarget i₀
        ({ x := v13RealLinearSingleBit i₀, A := A } :
          V13RealLinearWorld m) = 1 := by
  simp [v13RealLinearTarget, v13RealLinearSingleBit]

lemma v13RealLinear_same_map_coordinate_on_identity_pair {m : Nat}
    (i₀ : Fin m) (probe : F2Vec m) (row : Fin m) :
    v13RealLinearCoordinateValue (.mapValue probe row)
        (v13RealLinearPublicInput
          ({ x := f2ZeroVec m, A := v13RealLinearIdentity m } :
            V13RealLinearWorld m)) =
      v13RealLinearCoordinateValue (.mapValue probe row)
        (v13RealLinearPublicInput
          ({ x := v13RealLinearSingleBit i₀,
              A := v13RealLinearIdentity m } :
            V13RealLinearWorld m)) := by
  simp [v13RealLinearCoordinateValue, v13RealLinearPublicInput]

lemma v13RealLinear_same_inverse_coordinate_on_identity_pair {m : Nat}
    (i₀ : Fin m) (probe : F2Vec m) (row : Fin m) :
    v13RealLinearCoordinateValue (.inverseValue probe row)
        (v13RealLinearPublicInput
          ({ x := f2ZeroVec m, A := v13RealLinearIdentity m } :
            V13RealLinearWorld m)) =
      v13RealLinearCoordinateValue (.inverseValue probe row)
        (v13RealLinearPublicInput
          ({ x := v13RealLinearSingleBit i₀,
              A := v13RealLinearIdentity m } :
            V13RealLinearWorld m)) := by
  simp [v13RealLinearCoordinateValue, v13RealLinearPublicInput]

lemma v13RealLinear_same_rhs_coordinate_on_identity_pair {m : Nat}
    {i₀ row : Fin m} (hrow : row ≠ i₀) :
    v13RealLinearCoordinateValue (.rhs row)
        (v13RealLinearPublicInput
          ({ x := f2ZeroVec m, A := v13RealLinearIdentity m } :
            V13RealLinearWorld m)) =
      v13RealLinearCoordinateValue (.rhs row)
        (v13RealLinearPublicInput
          ({ x := v13RealLinearSingleBit i₀,
              A := v13RealLinearIdentity m } :
            V13RealLinearWorld m)) := by
  simp [v13RealLinearCoordinateValue, v13RealLinearPublicInput,
    v13RealLinearIdentity, f2ZeroVec, v13RealLinearSingleBit, hrow]

lemma v13RealLinear_same_target_rhs_coordinate_on_swap_pair {m : Nat}
    {i₀ spare : Fin m} (hspare : spare ≠ i₀) :
    v13RealLinearCoordinateValue (.rhs i₀)
        (v13RealLinearPublicInput
          ({ x := f2ZeroVec m,
              A := v13RealLinearPerm (Equiv.swap i₀ spare) } :
            V13RealLinearWorld m)) =
      v13RealLinearCoordinateValue (.rhs i₀)
        (v13RealLinearPublicInput
          ({ x := v13RealLinearSingleBit i₀,
              A := v13RealLinearPerm (Equiv.swap i₀ spare) } :
            V13RealLinearWorld m)) := by
  simp [v13RealLinearCoordinateValue, v13RealLinearPublicInput,
    v13RealLinearPerm, f2ZeroVec, v13RealLinearSingleBit,
    Equiv.swap_apply_left, hspare]

theorem v13RealLinear_no_single_public_coordinate_determines_target_of_spare
    {m : Nat} (i₀ spare : Fin m) (hspare : spare ≠ i₀) :
    ∀ coordinate : V13RealLinearPublicCoordinate m,
      ¬ V13RealLinearCoordinateDeterminesTarget i₀ coordinate := by
  intro coordinate hdet
  cases coordinate with
  | mapValue probe row =>
      have hsame :=
        v13RealLinear_same_map_coordinate_on_identity_pair i₀ probe row
      have htarget :
          v13RealLinearTarget i₀
              ({ x := f2ZeroVec m, A := v13RealLinearIdentity m } :
                V13RealLinearWorld m) =
            v13RealLinearTarget i₀
              ({ x := v13RealLinearSingleBit i₀,
                  A := v13RealLinearIdentity m } :
                V13RealLinearWorld m) := by
        rw [← hdet
              ({ x := f2ZeroVec m, A := v13RealLinearIdentity m } :
                V13RealLinearWorld m),
            ← hdet
              ({ x := v13RealLinearSingleBit i₀,
                  A := v13RealLinearIdentity m } :
                V13RealLinearWorld m)]
        exact hsame
      simp [v13RealLinear_target_zero_world,
        v13RealLinear_target_one_world] at htarget
  | inverseValue probe row =>
      have hsame :=
        v13RealLinear_same_inverse_coordinate_on_identity_pair i₀ probe row
      have htarget :
          v13RealLinearTarget i₀
              ({ x := f2ZeroVec m, A := v13RealLinearIdentity m } :
                V13RealLinearWorld m) =
            v13RealLinearTarget i₀
              ({ x := v13RealLinearSingleBit i₀,
                  A := v13RealLinearIdentity m } :
                V13RealLinearWorld m) := by
        rw [← hdet
              ({ x := f2ZeroVec m, A := v13RealLinearIdentity m } :
                V13RealLinearWorld m),
            ← hdet
              ({ x := v13RealLinearSingleBit i₀,
                  A := v13RealLinearIdentity m } :
                V13RealLinearWorld m)]
        exact hsame
      simp [v13RealLinear_target_zero_world,
        v13RealLinear_target_one_world] at htarget
  | rhs row =>
      by_cases hrow : row = i₀
      · subst row
        have hsame :=
          v13RealLinear_same_target_rhs_coordinate_on_swap_pair hspare
        have htarget :
            v13RealLinearTarget i₀
                ({ x := f2ZeroVec m,
                    A := v13RealLinearPerm (Equiv.swap i₀ spare) } :
                  V13RealLinearWorld m) =
              v13RealLinearTarget i₀
                ({ x := v13RealLinearSingleBit i₀,
                    A := v13RealLinearPerm (Equiv.swap i₀ spare) } :
                  V13RealLinearWorld m) := by
          rw [← hdet
                ({ x := f2ZeroVec m,
                    A := v13RealLinearPerm (Equiv.swap i₀ spare) } :
                  V13RealLinearWorld m),
              ← hdet
                ({ x := v13RealLinearSingleBit i₀,
                    A := v13RealLinearPerm (Equiv.swap i₀ spare) } :
                  V13RealLinearWorld m)]
          exact hsame
        simp [v13RealLinear_target_zero_world,
          v13RealLinear_target_one_world] at htarget
      · have hsame :=
          v13RealLinear_same_rhs_coordinate_on_identity_pair
            (i₀ := i₀) (row := row) hrow
        have htarget :
            v13RealLinearTarget i₀
                ({ x := f2ZeroVec m, A := v13RealLinearIdentity m } :
                  V13RealLinearWorld m) =
              v13RealLinearTarget i₀
                ({ x := v13RealLinearSingleBit i₀,
                    A := v13RealLinearIdentity m } :
                  V13RealLinearWorld m) := by
          rw [← hdet
                ({ x := f2ZeroVec m, A := v13RealLinearIdentity m } :
                  V13RealLinearWorld m),
              ← hdet
                ({ x := v13RealLinearSingleBit i₀,
                    A := v13RealLinearIdentity m } :
                  V13RealLinearWorld m)]
          exact hsame
        simp [v13RealLinear_target_zero_world,
          v13RealLinear_target_one_world] at htarget

theorem v13RealLinear_publicSurfaceCertificate {m : Nat} :
    V13RealLinearPublicSurfaceCertificate m := by
  exact
    { fullPublicDecodes := fun i₀ omega =>
        v13RealLinear_fullPublic_decodes_target i₀ omega
      fullPublicDeterminesTarget := fun i₀ omega₀ omega₁ hpublic =>
        v13RealLinear_fullPublic_determines_target i₀ omega₀ omega₁ hpublic
      noSingleCoordinateDeterminesTarget := fun i₀ spare hspare =>
        v13RealLinear_no_single_public_coordinate_determines_target_of_spare
          i₀ spare hspare }

end Mettapedia.Computability.PNP
