import Mettapedia.Computability.PNP.ExactZABDecisionListFamily
import Mettapedia.Computability.PNP.ExactVisibleCompressionObstruction
import Mettapedia.Computability.PNP.FirstActiveFeature
import Mettapedia.Computability.PNP.ProductSuccessKpolyBridgeObstructionCore

/-!
# PNP crux: raw exact ZAB decision-list structural obstruction

This module contains the route-level obstruction for raw exact
`(zfeat(z), a, b)` decision-list predictors.  The manuscript-facing
`ActualSwitchedLocalInterface` wrappers live in
`ExactZABDecisionListStructuralObstructionActualInterface`.
-/

namespace Mettapedia.Computability.PNP

section Structural

open Fin

variable {Z : Type*} [DecidableEq Z]

def zFiberAHeadRule
    {k : ℕ} (hk : 0 < k) (z0 : Z) :
    ExactVisibleRule Z k :=
  fun u => if u.z = z0 then u.a ⟨0, hk⟩ else false

def zHeadRule
    {n k : ℕ} (hn : 0 < n) :
    ExactVisibleRule (BitVec n) k :=
  fun u => u.z ⟨0, hn⟩

omit [DecidableEq Z] in
theorem rawExactZABDecisionListPredict_eq_of_firstActive_z
    {r k : ℕ}
    (zfeat : Z → BitVec r)
    (code : SharedAffineDecisionListCode (r + (k + k)))
    {z : Z} {j : Fin r}
    (hz : firstActiveFeature? (zfeat z) = some j)
    (a b : BitVec k) :
    rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code ⟨z, a, b⟩ =
      code.1 (Fin.castAdd (k + k) j) := by
  simp [rawExactZABDecisionListPredict, exactZABVisibleData, exactABVisibleData,
    firstActiveFeature?_append_left hz]

theorem zFiberAHeadRule_not_eq_rawExactZABDecisionListPredict_of_firstActive_z
    {r k : ℕ}
    (zfeat : Z → BitVec r)
    (hk : 0 < k)
    (z0 : Z)
    {j : Fin r}
    (hz : firstActiveFeature? (zfeat z0) = some j)
    (code : SharedAffineDecisionListCode (r + (k + k))) :
    zFiberAHeadRule (Z := Z) (k := k) hk z0 ≠
      rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code := by
  intro heq
  let u0 : ExactVisiblePostSwitchSurface Z k := ⟨z0, zeroVec, zeroVec⟩
  let u1 : ExactVisiblePostSwitchSurface Z k := ⟨z0, headOneVec hk, zeroVec⟩
  have hpred0 :
      rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code u0 =
        code.1 (Fin.castAdd (k + k) j) := by
    simpa [u0] using
      rawExactZABDecisionListPredict_eq_of_firstActive_z
        (Z := Z) (r := r) (k := k) zfeat code hz zeroVec zeroVec
  have hpred1 :
      rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code u1 =
        code.1 (Fin.castAdd (k + k) j) := by
    simpa [u1] using
      rawExactZABDecisionListPredict_eq_of_firstActive_z
        (Z := Z) (r := r) (k := k) zfeat code hz (headOneVec hk) zeroVec
  have hsamePred :
      rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code u0 =
        rawExactZABDecisionListPredict (Z := Z) (r := r) (k := k) zfeat code u1 := by
    rw [hpred0, hpred1]
  have hsameRule : zFiberAHeadRule (Z := Z) (k := k) hk z0 u0 =
      zFiberAHeadRule (Z := Z) (k := k) hk z0 u1 := by
    simpa [heq] using hsamePred
  have hu0 : zFiberAHeadRule (Z := Z) (k := k) hk z0 u0 = false := by
    simp [zFiberAHeadRule, u0, zeroVec]
  have hu1 : zFiberAHeadRule (Z := Z) (k := k) hk z0 u1 = true := by
    simp [zFiberAHeadRule, u1, headOneVec]
  simp [hu0, hu1] at hsameRule

theorem zHeadRule_not_eq_rawExactZABDecisionListPredict_of_forall_zero
    {n r k : ℕ}
    (zfeat : BitVec n → BitVec r)
    (hn : 0 < n)
    (hzero : ∀ z, zfeat z = zeroVec)
    (code : SharedAffineDecisionListCode (r + (k + k))) :
    zHeadRule (n := n) (k := k) hn ≠
      rawExactZABDecisionListPredict (Z := BitVec n) (r := r) (k := k) zfeat code := by
  intro heq
  let z0 : BitVec n := zeroVec
  let z1 : BitVec n := headOneVec hn
  let u0 : ExactVisiblePostSwitchSurface (BitVec n) k := ⟨z0, zeroVec, zeroVec⟩
  let u1 : ExactVisiblePostSwitchSurface (BitVec n) k := ⟨z1, zeroVec, zeroVec⟩
  have hpred :
      rawExactZABDecisionListPredict (Z := BitVec n) (r := r) (k := k) zfeat code u0 =
        rawExactZABDecisionListPredict (Z := BitVec n) (r := r) (k := k) zfeat code u1 := by
    simp [rawExactZABDecisionListPredict, exactZABVisibleData, exactABVisibleData, u0, u1, hzero]
  have hsameRule :
      zHeadRule (n := n) (k := k) hn u0 = zHeadRule (n := n) (k := k) hn u1 := by
    simpa [heq] using hpred
  have hu0 : zHeadRule (n := n) (k := k) hn u0 = false := by
    simp [zHeadRule, u0, z0, zeroVec]
  have hu1 : zHeadRule (n := n) (k := k) hn u1 = true := by
    simp [zHeadRule, u1, z1]
  simp [hu0, hu1] at hsameRule

theorem not_realizedByRawExactZABDecisionListFamily_of_surjective_predict_of_pos_widths
    {n r k : ℕ} {Index : Type*}
    (zfeat : BitVec n → BitVec r)
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (hn : 0 < n)
    (hk : 0 < k)
    (hsurj : Function.Surjective G.predict) :
    ¬ RealizedByRawExactZABDecisionListFamily
        (Z := BitVec n) (r := r) (k := k) zfeat G := by
  intro hreal
  by_cases hzero : ∀ z, zfeat z = zeroVec
  · rcases hsurj (zHeadRule (n := n) (k := k) hn) with ⟨i, hi⟩
    rcases hreal i with ⟨code, hcode⟩
    have hcode' :
        rawExactZABDecisionListPredict (Z := BitVec n) (r := r) (k := k) zfeat code =
          zHeadRule (n := n) (k := k) hn := by
      exact hcode.symm.trans hi
    exact
      zHeadRule_not_eq_rawExactZABDecisionListPredict_of_forall_zero
        (r := r) (k := k) zfeat hn hzero code hcode'.symm
  · have hnotzero : ∃ z0, zfeat z0 ≠ zeroVec := by
      exact not_forall.mp hzero
    rcases hnotzero with ⟨z0, hz0⟩
    rcases exists_firstActiveFeature?_eq_some_of_ne_zero hz0 with ⟨j, hj⟩
    rcases hsurj (zFiberAHeadRule (Z := BitVec n) (k := k) hk z0) with ⟨i, hi⟩
    rcases hreal i with ⟨code, hcode⟩
    have hcode' :
        rawExactZABDecisionListPredict (Z := BitVec n) (r := r) (k := k) zfeat code =
          zFiberAHeadRule (Z := BitVec n) (k := k) hk z0 := by
      exact hcode.symm.trans hi
    exact
      zFiberAHeadRule_not_eq_rawExactZABDecisionListPredict_of_firstActive_z
        (Z := BitVec n) (r := r) (k := k) zfeat hk z0 hj code hcode'.symm

theorem fullExactVisibleRuleFamily_not_realizedByRawExactZABDecisionListFamily_of_pos_widths
    {n r k : ℕ}
    (zfeat : BitVec n → BitVec r)
    (hn : 0 < n)
    (hk : 0 < k) :
    ¬ RealizedByRawExactZABDecisionListFamily
        (Z := BitVec n) (r := r) (k := k) zfeat
        (fullExactVisibleRuleFamily (BitVec n) k) := by
  exact
    not_realizedByRawExactZABDecisionListFamily_of_surjective_predict_of_pos_widths
      (n := n) (r := r) (k := k) zfeat hn hk
      (fullExactVisibleRuleFamily_surjective (BitVec n) k)

end Structural

end Mettapedia.Computability.PNP
