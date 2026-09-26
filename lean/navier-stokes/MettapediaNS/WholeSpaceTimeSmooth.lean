import Euler.OrdinaryWordTime
import Euler.OrdinaryStrongTime
import Euler.OrdinaryHelmholtzField
import Euler.SmoothL2CoefficientPath
import Euler.LpSmoothCoefficientContinuity
import MettapediaNS.WholeSpaceNSContinuation

/-!
# Time smoothness of the smooth Navier–Stokes evolutions on `ℝ³`

A path `B` of smooth `L²` fields is the time derivative of a path `A` when both have
continuous jets and, at every interior time and every point, the value of `A` is
differentiable in time with derivative the value of `B`. The upstream strong-time theorems
turn this pointwise statement into the `L²` derivative of every derivative word, and an
`L²` derivative back into pointwise derivatives up to the endpoints. Hence the relation is
preserved by sums, linear maps, directional derivatives, the Leray projection and the
Laplacian, and the product rule holds for the advection field.

The Navier–Stokes velocity has the pressure-free right-hand side `-P((u·∇)u) + ν Δu` as its
time derivative, and that right-hand side is built from the velocity by these operations.
Induction on the number of derivatives therefore gives time derivatives of every order,
each a path of smooth fields with continuous jets: the evolutions are smooth in time with
values in every Sobolev space.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceTimeSmooth

open Set Filter MeasureTheory
open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSolenoidal EulerMeanSobolevBoundedField EulerLpSmoothCoefficientProduct
  WholeSpaceViscousEnergy WholeSpaceViscousFlow Finset
open scoped Topology

/-- A path of smooth `L²` fields over `[0, T]`. -/
abbrev FieldPath (T : ℝ) := Icc (0 : ℝ) T → SmoothL2Field Space

/-- All jets of the path are continuous in time. -/
abbrev JetContinuous {T : ℝ} (A : FieldPath T) : Prop :=
  ∀ n, Continuous (fun t ↦ (A t).jetLp n)

/-! ## Advection of two paths -/

theorem advectionField_eq_product {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A B : K → SmoothL2Field Space) (hB : ∀ n, Continuous (fun t ↦ (B t).jetLp n)) (t : K) :
    advectionField (A t) (B t) =
      product (coefficientPath (fun s ↦ (B s).derivative) (continuous_jetLp_derivative B hB))
        t (A t) := by
  apply field_ext
  funext x
  rw [advectionField_field, product_field, coefficientPath_apply]
  rfl

theorem continuous_jetLp_advectionField {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A B : K → SmoothL2Field Space) (hA : ∀ n, Continuous (fun t ↦ (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t ↦ (B t).jetLp n)) (n : ℕ) :
    Continuous (fun t ↦ (advectionField (A t) (B t)).jetLp n) := by
  simp only [advectionField_eq_product A B hB]
  exact continuous_product_jet _ A hA n

theorem advectionField_field_sum (C D : SmoothL2Field Space) (x : Space) :
    (advectionField C D).field x =
      ∑ i : Fin 3, C.field x i • (D.directionalField (axis i)).field x := by
  rw [advectionField, sumField_field]
  simp only [coordinateProduct_field]

variable {T : ℝ} (hT : 0 ≤ T)

/-! ## The time-derivative relation -/

/-- `B` is the time derivative of `A`. -/
structure TimeDeriv (A B : FieldPath T) : Prop where
  left : JetContinuous A
  right : JetContinuous B
  deriv : ∀ t (ht : t ∈ Ioo 0 T) x,
    HasDerivAt (fun r ↦ (A (projIcc 0 T hT r)).field x) ((B ⟨t, ht.1.le, ht.2.le⟩).field x) t

namespace TimeDeriv

variable {hT} {A B : FieldPath T}

/-- Every derivative word has the corresponding `L²` time derivative, up to the endpoints. -/
theorem word (h : TimeDeriv hT A B) {n : ℕ} (w : Fin n → Fin 3) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r ↦ (wordField (A (projIcc 0 T hT r)) w).toLp)
      (wordField (B t) w).toLp (Icc (0 : ℝ) T) t :=
  ordinaryWord_hasDerivWithinAt T hT A B h.left h.right h.deriv w t

theorem toLp (h : TimeDeriv hT A B) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r ↦ (A (projIcc 0 T hT r)).toLp) (B ⟨t, ht.1.le, ht.2.le⟩).toLp t := by
  have hw := (h.word (Fin.elim0 : Fin 0 → Fin 3) ⟨t, ht.1.le, ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  simpa only [wordField_zero] using hw

/-- The pointwise derivative holds up to the endpoints, within the time interval. -/
theorem within (h : TimeDeriv hT A B) (t : Icc (0 : ℝ) T) (x : Space) :
    HasDerivWithinAt (fun r ↦ (A (projIcc 0 T hT r)).field x) ((B t).field x)
      (Icc (0 : ℝ) T) t :=
  pointwise_derivative_of_l2 T hT A B h.left h.right (fun t ht ↦ h.toLp t ht) t x

end TimeDeriv

/-- An interior `L²` derivative with continuous jets is a time derivative. -/
theorem timeDeriv_of_toLp {A B : FieldPath T} (hA : JetContinuous A) (hB : JetContinuous B)
    (hd : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r ↦ (A (projIcc 0 T hT r)).toLp) (B ⟨t, ht.1.le, ht.2.le⟩).toLp t) :
    TimeDeriv hT A B where
  left := hA
  right := hB
  deriv t ht x :=
    (pointwise_derivative_of_l2 T hT A B hA hB hd ⟨t, ht.1.le, ht.2.le⟩ x).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)

namespace TimeDeriv

variable {hT}

theorem add {A A' B B' : FieldPath T} (h : TimeDeriv hT A A') (h' : TimeDeriv hT B B') :
    TimeDeriv hT (fun t ↦ addField (A t) (B t)) (fun t ↦ addField (A' t) (B' t)) where
  left := continuous_jetLp_addField _ _ h.left h'.left
  right := continuous_jetLp_addField _ _ h.right h'.right
  deriv t ht x := by
    simpa only [addField_field] using (h.deriv t ht x).fun_add (h'.deriv t ht x)

theorem map (L : Space →L[ℝ] Space) {A A' : FieldPath T} (h : TimeDeriv hT A A') :
    TimeDeriv hT (fun t ↦ mapField L (A t)) (fun t ↦ mapField L (A' t)) where
  left := continuous_jetLp_mapField L _ h.left
  right := continuous_jetLp_mapField L _ h.right
  deriv t ht x := by
    simpa only [mapField_field, Function.comp_def] using
      L.hasFDerivAt.comp_hasDerivAt t (h.deriv t ht x)

theorem directional {A A' : FieldPath T} (h : TimeDeriv hT A A') (i : Fin 3) :
    TimeDeriv hT (fun t ↦ (A t).directionalField (axis i))
      (fun t ↦ (A' t).directionalField (axis i)) := by
  apply timeDeriv_of_toLp hT (fun n ↦ continuous_jetLp_directionalField A h.left (axis i) n)
    (fun n ↦ continuous_jetLp_directionalField A' h.right (axis i) n)
  intro t ht
  exact (h.word (fun _ : Fin 1 ↦ i) ⟨t, ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem solenoidal {A A' : FieldPath T} (h : TimeDeriv hT A A') :
    TimeDeriv hT (fun t ↦ solenoidalField (A t)) (fun t ↦ solenoidalField (A' t)) := by
  apply timeDeriv_of_toLp hT (solenoidalField_continuous A h.left)
    (solenoidalField_continuous A' h.right)
  intro t ht
  simp only [solenoidalField_toLp]
  exact solenoidalProjection.hasFDerivAt.comp_hasDerivAt t (h.toLp t ht)

theorem laplacian {A A' : FieldPath T} (h : TimeDeriv hT A A') :
    TimeDeriv hT (fun t ↦ laplacianField (A t)) (fun t ↦ laplacianField (A' t)) := by
  have e (C : FieldPath T) : (fun t ↦ laplacianField (C t)) = fun t ↦ addField (addField
      (((C t).directionalField (axis 0)).directionalField (axis 0))
      (((C t).directionalField (axis 1)).directionalField (axis 1)))
      (((C t).directionalField (axis 2)).directionalField (axis 2)) :=
    funext fun t ↦ laplacianField_eq_add (C t)
  rw [e A, e A']
  have hd (i : Fin 3) := (h.directional i).directional i
  exact ((hd 0).add (hd 1)).add (hd 2)

/-- **The product rule for advection.** -/
theorem advection {A A' B B' : FieldPath T} (hA : TimeDeriv hT A A') (hB : TimeDeriv hT B B') :
    TimeDeriv hT (fun t ↦ advectionField (A t) (B t))
      (fun t ↦ addField (advectionField (A' t) (B t)) (advectionField (A t) (B' t))) where
  left := continuous_jetLp_advectionField A B hA.left hB.left
  right := continuous_jetLp_addField _ _ (continuous_jetLp_advectionField A' B hA.right hB.left)
    (continuous_jetLp_advectionField A B' hA.left hB.right)
  deriv t ht x := by
    have hp : projIcc 0 T hT t = ⟨t, ht.1.le, ht.2.le⟩ := projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩
    have hterm (i : Fin 3) : HasDerivAt
        (fun r ↦ (A (projIcc 0 T hT r)).field x i •
          ((B (projIcc 0 T hT r)).directionalField (axis i)).field x)
        ((A ⟨t, ht.1.le, ht.2.le⟩).field x i •
            ((B' ⟨t, ht.1.le, ht.2.le⟩).directionalField (axis i)).field x +
          (A' ⟨t, ht.1.le, ht.2.le⟩).field x i •
            ((B ⟨t, ht.1.le, ht.2.le⟩).directionalField (axis i)).field x) t := by
      have h1 : HasDerivAt (fun r ↦ (A (projIcc 0 T hT r)).field x i)
          ((A' ⟨t, ht.1.le, ht.2.le⟩).field x i) t :=
        (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t (hA.deriv t ht x)
      have h2 := (hB.directional i).deriv t ht x
      have h3 := h1.fun_smul h2
      simp only [hp] at h3
      exact h3
    have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hterm i)
    have heq : (∑ i : Fin 3, ((A ⟨t, ht.1.le, ht.2.le⟩).field x i •
          ((B' ⟨t, ht.1.le, ht.2.le⟩).directionalField (axis i)).field x +
        (A' ⟨t, ht.1.le, ht.2.le⟩).field x i •
          ((B ⟨t, ht.1.le, ht.2.le⟩).directionalField (axis i)).field x)) =
        (∑ i : Fin 3, (A' ⟨t, ht.1.le, ht.2.le⟩).field x i •
          ((B ⟨t, ht.1.le, ht.2.le⟩).directionalField (axis i)).field x) +
        ∑ i : Fin 3, (A ⟨t, ht.1.le, ht.2.le⟩).field x i •
          ((B' ⟨t, ht.1.le, ht.2.le⟩).directionalField (axis i)).field x := by
      rw [Finset.sum_add_distrib, add_comm]
    simp only [advectionField_field_sum, addField_field]
    exact hs.congr_deriv heq

/-- The time derivative is unique, including at the endpoints. -/
theorem unique (hpos : 0 < T) {A B B' : FieldPath T} (h : TimeDeriv hT A B)
    (h' : TimeDeriv hT A B') : B = B' := by
  funext t
  apply field_ext
  funext x
  have hu : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) T) t := uniqueDiffOn_Icc hpos t t.property
  exact ((h.within t x).derivWithin hu).symm.trans ((h'.within t x).derivWithin hu)

end TimeDeriv

/-! ## Time derivatives of every order -/

/-- `A` has `k` successive time derivatives, each a path with continuous jets. -/
def HasTimeDerivs : ℕ → FieldPath T → Prop
  | 0, A => JetContinuous A
  | k + 1, A => ∃ B, TimeDeriv hT A B ∧ HasTimeDerivs k B

theorem HasTimeDerivs.jetContinuous {hT} : ∀ {k : ℕ} {A : FieldPath T},
    HasTimeDerivs hT k A → JetContinuous A
  | 0, _, h => h
  | _ + 1, _, ⟨_, hAB, _⟩ => hAB.left

theorem HasTimeDerivs.mono {hT} : ∀ {k : ℕ} {A : FieldPath T},
    HasTimeDerivs hT (k + 1) A → HasTimeDerivs hT k A
  | 0, _, ⟨_, hAB, _⟩ => hAB.left
  | _ + 1, _, ⟨B, hAB, hB⟩ => ⟨B, hAB, hB.mono⟩

/-- Closure under an operation that commutes with time derivatives. -/
theorem hasTimeDerivs_map (Φ : SmoothL2Field Space → SmoothL2Field Space)
    (hc : ∀ A : FieldPath T, JetContinuous A → JetContinuous (fun t ↦ Φ (A t)))
    (hd : ∀ A B : FieldPath T, TimeDeriv hT A B →
      TimeDeriv hT (fun t ↦ Φ (A t)) (fun t ↦ Φ (B t))) :
    ∀ (k : ℕ) (A : FieldPath T), HasTimeDerivs hT k A → HasTimeDerivs hT k (fun t ↦ Φ (A t))
  | 0, A, h => hc A h
  | k + 1, A, ⟨B, hAB, hB⟩ => ⟨fun t ↦ Φ (B t), hd A B hAB, hasTimeDerivs_map Φ hc hd k B hB⟩

theorem hasTimeDerivs_add :
    ∀ (k : ℕ) (A B : FieldPath T), HasTimeDerivs hT k A → HasTimeDerivs hT k B →
      HasTimeDerivs hT k (fun t ↦ addField (A t) (B t))
  | 0, _, _, hA, hB => continuous_jetLp_addField _ _ hA hB
  | k + 1, _, _, ⟨A', hA, hA'⟩, ⟨B', hB, hB'⟩ =>
      ⟨fun t ↦ addField (A' t) (B' t), hA.add hB, hasTimeDerivs_add k A' B' hA' hB'⟩

theorem hasTimeDerivs_advection :
    ∀ (k : ℕ) (A B : FieldPath T), HasTimeDerivs hT k A → HasTimeDerivs hT k B →
      HasTimeDerivs hT k (fun t ↦ advectionField (A t) (B t))
  | 0, A, B, hA, hB => continuous_jetLp_advectionField A B hA hB
  | k + 1, A, B, hAk, hBk => by
      have hAm := hAk.mono
      have hBm := hBk.mono
      obtain ⟨A', hA, hA'⟩ := hAk
      obtain ⟨B', hB, hB'⟩ := hBk
      exact ⟨_, hA.advection hB, hasTimeDerivs_add hT k _ _
        (hasTimeDerivs_advection k A' B hA' hBm)
        (hasTimeDerivs_advection k A B' hAm hB')⟩

theorem hasTimeDerivs_mapField (L : Space →L[ℝ] Space) (k : ℕ) (A : FieldPath T)
    (h : HasTimeDerivs hT k A) : HasTimeDerivs hT k (fun t ↦ mapField L (A t)) :=
  hasTimeDerivs_map hT (mapField L) (fun _ hA ↦ continuous_jetLp_mapField L _ hA)
    (fun _ _ hAB ↦ hAB.map L) k A h

theorem hasTimeDerivs_solenoidal (k : ℕ) (A : FieldPath T) (h : HasTimeDerivs hT k A) :
    HasTimeDerivs hT k (fun t ↦ solenoidalField (A t)) :=
  hasTimeDerivs_map hT solenoidalField (fun A hA ↦ solenoidalField_continuous A hA)
    (fun _ _ hAB ↦ hAB.solenoidal) k A h

theorem hasTimeDerivs_laplacian (k : ℕ) (A : FieldPath T) (h : HasTimeDerivs hT k A) :
    HasTimeDerivs hT k (fun t ↦ laplacianField (A t)) :=
  hasTimeDerivs_map hT laplacianField
    (fun A hA ↦ continuous_jetLp_laplacianField A hA)
    (fun _ _ hAB ↦ hAB.laplacian) k A h

theorem hasTimeDerivs_directional (i : Fin 3) (k : ℕ) (A : FieldPath T)
    (h : HasTimeDerivs hT k A) :
    HasTimeDerivs hT k (fun t ↦ (A t).directionalField (axis i)) :=
  hasTimeDerivs_map hT (fun C ↦ C.directionalField (axis i))
    (fun A hA ↦ fun n ↦ continuous_jetLp_directionalField A hA (axis i) n)
    (fun _ _ hAB ↦ hAB.directional i) k A h

/-- The pressure-free right-hand side has as many time derivatives as its argument. -/
theorem hasTimeDerivs_nsProjectedRhs (ν : ℝ) (k : ℕ) (A : FieldPath T)
    (h : HasTimeDerivs hT k A) : HasTimeDerivs hT k (fun t ↦ nsProjectedRhs ν (A t)) :=
  hasTimeDerivs_add hT k _ _
    (hasTimeDerivs_mapField hT _ k _
      (hasTimeDerivs_solenoidal hT k _ (hasTimeDerivs_advection hT k A A h h)))
    (hasTimeDerivs_mapField hT _ k _ (hasTimeDerivs_laplacian hT k A h))

/-- Time derivatives of every order. -/
def IsTimeSmooth (A : FieldPath T) : Prop := ∀ k, HasTimeDerivs hT k A

/-- A time-smooth path has a time-smooth time derivative. -/
theorem IsTimeSmooth.exists_deriv {hT} (hpos : 0 < T) {A : FieldPath T}
    (h : IsTimeSmooth hT A) : ∃ B, TimeDeriv hT A B ∧ IsTimeSmooth hT B := by
  obtain ⟨B, hAB, -⟩ := h 1
  refine ⟨B, hAB, fun k ↦ ?_⟩
  obtain ⟨B', hAB', hB'⟩ := h (k + 1)
  rwa [hAB.unique hpos hAB']

theorem isTimeSmooth_map (Φ : SmoothL2Field Space → SmoothL2Field Space)
    (hc : ∀ A : FieldPath T, JetContinuous A → JetContinuous (fun t ↦ Φ (A t)))
    (hd : ∀ A B : FieldPath T, TimeDeriv hT A B →
      TimeDeriv hT (fun t ↦ Φ (A t)) (fun t ↦ Φ (B t)))
    {A : FieldPath T} (h : IsTimeSmooth hT A) : IsTimeSmooth hT (fun t ↦ Φ (A t)) :=
  fun k ↦ hasTimeDerivs_map hT Φ hc hd k A (h k)

theorem IsTimeSmooth.directional {hT} {A : FieldPath T} (h : IsTimeSmooth hT A) (i : Fin 3) :
    IsTimeSmooth hT (fun t ↦ (A t).directionalField (axis i)) :=
  fun k ↦ hasTimeDerivs_directional hT i k A (h k)

theorem IsTimeSmooth.solenoidal {hT} {A : FieldPath T} (h : IsTimeSmooth hT A) :
    IsTimeSmooth hT (fun t ↦ solenoidalField (A t)) :=
  fun k ↦ hasTimeDerivs_solenoidal hT k A (h k)

theorem IsTimeSmooth.nsProjectedRhs {hT} {A : FieldPath T} (h : IsTimeSmooth hT A) (ν : ℝ) :
    IsTimeSmooth hT (fun t ↦ WholeSpaceViscousFlow.nsProjectedRhs ν (A t)) :=
  fun k ↦ hasTimeDerivs_nsProjectedRhs hT ν k A (h k)

theorem IsTimeSmooth.advection {hT} {A B : FieldPath T} (hA : IsTimeSmooth hT A)
    (hB : IsTimeSmooth hT B) : IsTimeSmooth hT (fun t ↦ advectionField (A t) (B t)) :=
  fun k ↦ hasTimeDerivs_advection hT k A B (hA k) (hB k)

theorem IsTimeSmooth.pressureField {hT} {A : FieldPath T} (h : IsTimeSmooth hT A) :
    IsTimeSmooth hT (fun t ↦ EulerOrdinarySobolev.pressureField (A t)) := by
  intro k
  have hs := hasTimeDerivs_solenoidal hT k _ (hasTimeDerivs_advection hT k A A (h k) (h k))
  have ha := hasTimeDerivs_mapField hT (-(ContinuousLinearMap.id ℝ Space)) k _
    (hasTimeDerivs_advection hT k A A (h k) (h k))
  exact hasTimeDerivs_add hT k _ _ hs ha

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceTimeSmooth

/-! ## The Navier–Stokes evolutions -/

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow.NSEvolution

open Set Filter MeasureTheory
open EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerMeanSolenoidal WholeSpaceTimeSmooth
open scoped Topology

variable {ν T : ℝ} {hT : 0 ≤ T}

/-- The velocity has the pressure-free right-hand side as its time derivative. -/
theorem timeDeriv (U : NSEvolution ν T hT) (hpos : 0 < T) :
    TimeDeriv hT U.velocity (fun t ↦ nsProjectedRhs ν (U.velocity t)) where
  left := U.velocity_continuous
  right := nsProjectedRhs_continuous ν U.velocity U.velocity_continuous
  deriv t ht x := by
    have h := U.time_law t ht x
    rw [U.pressureForce_eq hpos] at h
    rwa [nsProjectedRhs_field]

theorem hasTimeDerivs (U : NSEvolution ν T hT) (hpos : 0 < T) :
    ∀ k, HasTimeDerivs hT k U.velocity
  | 0 => U.velocity_continuous
  | k + 1 => ⟨fun t ↦ nsProjectedRhs ν (U.velocity t), U.timeDeriv hpos,
      hasTimeDerivs_nsProjectedRhs hT ν k _ (U.hasTimeDerivs hpos k)⟩

/-- **Time smoothness.** A smooth Navier–Stokes evolution on a nondegenerate interval has
time derivatives of every order, each a path of smooth fields with continuous jets. -/
theorem isTimeSmooth (U : NSEvolution ν T hT) (hpos : 0 < T) : IsTimeSmooth hT U.velocity :=
  U.hasTimeDerivs hpos

/-- The pressure force is smooth in time as well. -/
theorem pressure_isTimeSmooth (U : NSEvolution ν T hT) (hpos : 0 < T) :
    IsTimeSmooth hT U.pressureForce := by
  have h := (U.isTimeSmooth hpos).pressureField
  have e : U.pressureForce = fun t ↦ EulerOrdinarySobolev.pressureField (U.velocity t) :=
    funext fun t ↦ U.pressureForce_eq hpos t
  rw [e]
  exact h

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceViscousFlow.NSEvolution
