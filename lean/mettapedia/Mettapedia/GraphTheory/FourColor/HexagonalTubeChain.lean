import Mettapedia.GraphTheory.FourColor.HexagonalSlabSeam
import Mettapedia.GraphTheory.FourColor.TubeChain

/-!
# Aligned coordinates constructed along hexagonal tube chains

Every seam offset is read from the original boundary darts. Local hexagonal
geometry then supplies compatible coordinates along an arbitrarily long
chain. In those coordinates the actual side support is exactly the iterated
ring relation, so the established stabilization theorem applies.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab

open GoertzelV24RotationCutDartDecomposition ZigzagRing TubeRingOrbit

noncomputable section

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {k : ℕ} [NeZero k]

/-- Change only the cyclic origin of a boundary coordinate map. -/
def atOrigin {B : Type*} (e : Fin k ≃ B) (a : Fin k) : Fin k ≃ B :=
  (Equiv.addRight a).trans e

@[simp] theorem atOrigin_apply {B : Type*} (e : Fin k ≃ B) (a i : Fin k) :
    atOrigin e a i = e (i + a) := rfl

@[simp] theorem atOrigin_symm_apply {B : Type*} (e : Fin k ≃ B) (a : Fin k) (b : B) :
    (atOrigin e a).symm b = e.symm b - a := by simp [atOrigin, sub_eq_add_neg]

@[simp] theorem atOrigin_zero {B : Type*} (e : Fin k ≃ B) : atOrigin e 0 = e := by
  ext i
  simp

theorem atOrigin_atOrigin {B : Type*} (e : Fin k ≃ B) (a b : Fin k) :
    atOrigin (atOrigin e b) a = atOrigin e (a + b) := by
  ext i
  simp [add_assoc]

namespace ZigzagSlab

variable {inner : V → Prop} (S : ZigzagSlab RS k inner)

theorem support_atOrigin (a : Fin k) (y : Fin k → Color) :
    (fun b => y ((atOrigin S.outEquiv a).symm b)) ∈ sideSupport RS S.inner' ↔
      ∃ x, (fun b => x ((atOrigin S.inEquiv a).symm b)) ∈ sideSupport RS inner ∧
        Step k x y := by
  change (fun b => rotate k y (-a) (S.outEquiv.symm b)) ∈ sideSupport RS S.inner' ↔ _
  rw [S.mem_sideSupport_inner'_iff]
  constructor
  · rintro ⟨w, hw, hwy⟩
    refine ⟨rotate k w a, ?_, ?_⟩
    · simpa [rotate] using hw
    · have h := Step.rotate_step k hwy a
      have hy : rotate k (rotate k y (-a)) a = y := by
        funext i
        simp [rotate, add_assoc]
      rw [hy] at h
      exact h
  · rintro ⟨x, hx, hxy⟩
    refine ⟨rotate k x (-a), ?_, Step.rotate_step k hxy (-a)⟩
    simpa only [atOrigin_symm_apply, rotate, sub_eq_add_neg] using hx

theorem sideSet_atOrigin (a : Fin k) :
    sideSet S.inner' (atOrigin S.outEquiv a) =
      stepS k (sideSet inner (atOrigin S.inEquiv a)) := by
  ext Y
  simp only [sideSet, stepS, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hY, h⟩
    obtain ⟨w, hw, hring⟩ := (S.support_atOrigin a (wordOf k Y)).mp h
    have hw0 := ne_zero_of_mem_sideSupport (atOrigin S.inEquiv a) hw
    refine ⟨hY, encW k w, encW_lt k w, ⟨encW_lt k w, ?_⟩, ?_⟩
    · rw [wordOf_encW k w hw0]
      exact hw
    · rw [← accepts_iff_testBit k _ _ hY, wordOf_encW k w hw0]
      exact hring
  · rintro ⟨hY, X, hX, ⟨_, hx⟩, hb⟩
    exact ⟨hY, (S.support_atOrigin a (wordOf k Y)).mpr
      ⟨wordOf k X, hx, (accepts_iff_testBit k X Y hY).mpr hb⟩⟩

end ZigzagSlab

namespace Tube

/-- The seam from a row to the coordinates used by the rest of the chain. -/
def nextSeam {inner : V → Prop} (S : ZigzagSlab RS k inner) {n : ℕ}
    (rest : Tube RS k S.inner' n) : Fin k ≃ Fin k :=
  S.outEquiv.trans rest.firstEquiv.symm

/-- The output origin is fixed at the last row. At every internal seam the
conditions concern actual vertex rotations and actual hexagonal faces. -/
def Hexagonal : {inner : V → Prop} → {n : ℕ} → Tube RS k inner n → Prop
  | _, _, .nil _ _ => True
  | _, _, .cons S rest => S.RotationCompatible ∧
      (match rest with
       | .nil _ e => e = S.outEquiv
       | .cons _ _ => S.HexagonalSeam) ∧ rest.Hexagonal

/-- Coordinates may differ by a cyclic origin at each successive seam. -/
def CyclicCoherent : {inner : V → Prop} → {n : ℕ} → Tube RS k inner n → Prop
  | _, _, .nil _ _ => True
  | _, _, .cons S rest =>
      (∀ i, nextSeam S rest i = i + nextSeam S rest 0) ∧ rest.CyclicCoherent

theorem Hexagonal.cyclicCoherent : {inner : V → Prop} → {n : ℕ} →
    (t : Tube RS k inner n) → t.Hexagonal → t.CyclicCoherent
  | _, _, .nil _ _, _ => trivial
  | _, _, .cons S rest, h => by
    refine ⟨?_, Hexagonal.cyclicCoherent rest h.2.2⟩
    cases rest with
    | nil inner e =>
      have he : e = S.outEquiv := h.2.1
      subst e
      intro i
      simp [nextSeam, firstEquiv]
    | cons T tail =>
      exact S.seam_eq_add T h.1 h.2.2.1 h.2.1

/-- Accumulating the seam offsets constructs an aligned boundary map. -/
def alignedEquiv : {inner : V → Prop} → {n : ℕ} → (t : Tube RS k inner n) →
    (r : ℕ) → Fin k ≃ BoundaryDart RS (t.side r)
  | _, _, .nil _ e, _ => e
  | _, _, .cons S _, 0 => S.inEquiv
  | _, _, .cons S rest, r + 1 => atOrigin (rest.alignedEquiv r) (nextSeam S rest 0)

theorem next_origin {inner : V → Prop} (S : ZigzagSlab RS k inner) {n : ℕ}
    (rest : Tube RS k S.inner' n)
    (hs : ∀ i, nextSeam S rest i = i + nextSeam S rest 0) (a : Fin k) :
    atOrigin rest.firstEquiv (a + nextSeam S rest 0) = atOrigin S.outEquiv a := by
  ext i
  change rest.firstEquiv (i + (a + nextSeam S rest 0)) = S.outEquiv (i + a)
  rw [← add_assoc, ← hs]
  exact rest.firstEquiv.apply_symm_apply _

/-- The support formula is uniform in both chain length and cyclic origin.
All quantified support elements have actual ambient colouring witnesses. -/
theorem sideSet_aligned : {inner : V → Prop} → {n : ℕ} → (t : Tube RS k inner n) →
    t.CyclicCoherent → (r : ℕ) → r ≤ n → (a : Fin k) →
    sideSet (t.side r) (atOrigin (t.alignedEquiv r) a) =
      (stepS k)^[r] (sideSet inner (atOrigin t.firstEquiv a))
  | _, _, .nil _ _, _, r, hr, a => by
    have : r = 0 := by omega
    subst r
    rfl
  | _, _, .cons _ _, _, 0, _, _ => rfl
  | _, _, .cons S rest, hc, r + 1, hr, a => by
    change sideSet (rest.side r)
      (atOrigin (atOrigin (rest.alignedEquiv r) (nextSeam S rest 0)) a) = _
    rw [atOrigin_atOrigin, sideSet_aligned rest hc.2 r (by omega),
      next_origin S rest hc.1, S.sideSet_atOrigin, Function.iterate_succ_apply]
    rfl

theorem sideSet_aligned_stable {inner : V → Prop} {n : ℕ}
    (t : Tube RS k inner n) (hc : t.CyclicCoherent)
    (hk : stabilizes k = true) (j : ℕ) (hn : k + j ≤ n) :
    sideSet (t.side (k + j)) (t.alignedEquiv (k + j)) =
      sideSet (t.side (k - 1 + j)) (t.alignedEquiv (k - 1 + j)) := by
  have h₁ := t.sideSet_aligned hc (k + j) hn 0
  have h₂ := t.sideSet_aligned hc (k - 1 + j) (by omega) 0
  simp only [atOrigin_zero] at h₁ h₂
  rw [h₁, h₂, stepS_iterate_stable hk _ (fun _ h => h.1) j]

theorem sideSet_aligned_eq_of_le {inner : V → Prop} {n : ℕ}
    (t : Tube RS k inner n) (hc : t.CyclicCoherent)
    (hk : stabilizes k = true) (j : ℕ) (hn : k - 1 + j ≤ n) :
    sideSet (t.side (k - 1 + j)) (t.alignedEquiv (k - 1 + j)) =
      sideSet (t.side (k - 1)) (t.alignedEquiv (k - 1)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hkpos := NeZero.pos k
    rw [show k - 1 + (j + 1) = k + j by omega,
      t.sideSet_aligned_stable hc hk j (by omega)]
    exact ih (by omega)

end Tube
end
end Mettapedia.GraphTheory.FourColor.TubeSlab
