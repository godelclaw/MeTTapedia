import Mettapedia.GraphTheory.FourColor.CyclicPortSeam
import Mettapedia.GraphTheory.FourColor.TubeSlabEmbedding
import Mettapedia.GraphTheory.FourColor.ZigzagRingCursor
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexFaceRungType

/-!
# Hexagonal faces align consecutive embedded zigzag rows

The seam permutation is constructed from the two actual boundary bijections.
Compatibility with the ambient vertex rotation supplies the three-step face
arcs. Hexagonal seam faces force the permutation to be a cyclic translation,
so two recognized rows have the ordinary two-ring colouring semantics after
one explicit reindexing of the output boundary.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.ZigzagSlab

open ZigzagRing GoertzelV24RotationCutDartDecomposition
open GoertzelV24HexFaceRungType

noncomputable section

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {k : ℕ} [NeZero k]
  {inner : V → Prop} (S : ZigzagSlab RS k inner)

/-- The recognized incidence embedding also retains the ambient rotation. -/
def RotationCompatible : Prop :=
  ∀ d, RS.rho (S.ι d) = S.ι ((rho k) d)

theorem face_mate (hS : S.RotationCompatible) (d : AllDart k) :
    RS.phi (RS.alpha (S.ι d)) = S.ι ((rho k) d) := by
  rw [RotationSystem.phi_apply, RS.alpha_involutive, hS]

theorem face_internal (hS : S.RotationCompatible) (d : ZigzagRing.Dart k) :
    RS.phi (S.ι (.inl d)) = S.ι ((rho k) (.inl (flip k d))) := by
  rw [RotationSystem.phi_apply, S.alpha_interior, hS]

theorem input_three_steps (hS : S.RotationCompatible) (i : Fin k) :
    (RS.phi ^ 3) (RS.alpha (S.ι (.inr (.inl i)))) =
      S.ι (.inr (.inl (i + 1))) := by
  simp only [pow_succ', pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  rw [S.face_mate hS]
  change RS.phi (RS.phi (S.ι (.inl (.inl (i, false))))) = _
  rw [S.face_internal hS]
  change RS.phi (S.ι (.inl (.inr (i, false)))) = _
  rw [S.face_internal hS]
  rfl

theorem output_three_steps (hS : S.RotationCompatible) (i : Fin k) :
    (RS.phi ^ 3) (RS.alpha (S.ι (.inr (.inr i)))) =
      S.ι (.inr (.inr (i - 1))) := by
  simp only [pow_succ', pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  rw [S.face_mate hS]
  change RS.phi (RS.phi (S.ι (.inl (.inl (i, true))))) = _
  rw [S.face_internal hS]
  change RS.phi (S.ι (.inl (.inr (i - 1, true)))) = _
  rw [S.face_internal hS]
  rfl

variable (T : ZigzagSlab RS k S.inner')

/-- The actual wiring, derived from complete boundary maps, not supplied
as an arbitrary coordinate assumption. -/
def seam : Fin k ≃ Fin k := S.outEquiv.trans T.inEquiv.symm

theorem seam_partner (i : Fin k) : T.inPartner (S.seam T i) = S.outPort i := by
  change T.inEquiv (T.inEquiv.symm (S.outEquiv i)) = S.outEquiv i
  exact T.inEquiv.apply_symm_apply _

theorem seam_mate (i : Fin k) :
    RS.alpha (S.ι (.inr (.inr i))) = T.ι (.inr (.inl (S.seam T i))) := by
  have h := congrArg (fun b : BoundaryDart RS S.inner' => b.1.1) (S.seam_partner T i)
  change RS.alpha (T.ι (.inr (.inl (S.seam T i)))) = S.ι (.inr (.inr i)) at h
  have hh := congrArg RS.alpha h
  rw [RS.alpha_involutive] at hh
  exact hh.symm

/-- A face-size condition on original ambient darts. -/
def HexagonalSeam : Prop :=
  ∀ i, (RS.faceOrbit (S.ι (.inr (.inr i)))).card = 6

theorem seam_six_steps (hhex : S.HexagonalSeam) (i : Fin k) :
    (RS.phi ^ 6) (S.ι (.inr (.inr i))) = S.ι (.inr (.inr i)) := by
  have h := (faceOrbit_isCycleOn RS (S.ι (.inr (.inr i)))).pow_card_apply
    (RS.mem_faceOrbit_self (S.ι (.inr (.inr i))))
  rwa [hhex i] at h

/-- Hexagonal seam geometry determines the matching up to a cyclic origin. -/
theorem seam_eq_add (hS : S.RotationCompatible) (hT : T.RotationCompatible)
    (hhex : S.HexagonalSeam) (i : Fin k) : S.seam T i = i + S.seam T 0 := by
  apply CyclicPortSeam.translation_of_six_steps RS.phi RS.alpha
    (fun i => S.ι (.inr (.inr i))) (fun j => T.ι (.inr (.inl j)))
    (S.seam T) RS.alpha_involutive (S.seam_mate T)
    (S.output_three_steps hS) (T.input_three_steps hT)
    (fun _ _ h => Sum.inl.inj (Sum.inr.inj (T.ι_inj h))) (S.seam_six_steps hhex) i

theorem aligned_ports (hS : S.RotationCompatible) (hT : T.RotationCompatible)
    (hhex : S.HexagonalSeam) (i : Fin k) :
    T.inPartner (i + S.seam T 0) = S.outPort i := by
  rw [← S.seam_eq_add T hS hT hhex]
  exact S.seam_partner T i

theorem support_in_seam_coordinates (a : Fin k)
    (hseam : ∀ i, S.seam T i = i + a) (w : Fin k → Color) :
    (fun b => w (T.inEquiv.symm b)) ∈ sideSupport RS S.inner' ↔
      (fun b => rotate k w a (S.outEquiv.symm b)) ∈ sideSupport RS S.inner' := by
  have he : (fun b => w (T.inEquiv.symm b)) =
      (fun b => rotate k w a (S.outEquiv.symm b)) := by
    funext b
    obtain ⟨i, rfl⟩ := S.outEquiv.surjective b
    change w (S.seam T i) = rotate k w a (S.outEquiv.symm (S.outEquiv i))
    rw [hseam, Equiv.symm_apply_apply]
    rfl
  rw [he]

/-- Eliminating the seam retains genuine side-colouring witnesses. The
single cyclic offset reindexes the final word; no choices are separated. -/
theorem two_row_support (hS : S.RotationCompatible) (hT : T.RotationCompatible)
    (hhex : S.HexagonalSeam) (y : Fin k → Color) :
    (fun b => y (T.outEquiv.symm b)) ∈ sideSupport RS T.inner' ↔
      ∃ x z : Fin k → Color,
        (fun b => x (S.inEquiv.symm b)) ∈ sideSupport RS inner ∧
          Step k x z ∧ Step k z (rotate k y (S.seam T 0)) := by
  let a := S.seam T 0
  have hseam : ∀ i, S.seam T i = i + a := S.seam_eq_add T hS hT hhex
  rw [T.mem_sideSupport_inner'_iff]
  constructor
  · rintro ⟨w, hw, hwy⟩
    have hw' := (S.support_in_seam_coordinates T a hseam w).mp hw
    obtain ⟨x, hx, hxw⟩ := (S.mem_sideSupport_inner'_iff (rotate k w a)).mp hw'
    exact ⟨x, rotate k w a, hx, hxw, Step.rotate_step k hwy a⟩
  · rintro ⟨x, z, hx, hxz, hzy⟩
    refine ⟨rotate k z (-a), ?_, ?_⟩
    · apply (S.support_in_seam_coordinates T a hseam _).mpr
      have hz : rotate k (rotate k z (-a)) a = z := by
        funext i
        simp [rotate, add_assoc]
      rw [hz]
      exact (S.mem_sideSupport_inner'_iff z).mpr ⟨x, hx, hxz⟩
    · have hb := Step.rotate_step k hzy (-a)
      have hy : rotate k (rotate k y (S.seam T 0)) (-a) = y := by
        funext i
        simp [rotate, a, add_assoc]
      rw [hy] at hb
      exact hb

end
end Mettapedia.GraphTheory.FourColor.TubeSlab.ZigzagSlab
