import Mettapedia.GraphTheory.FourColor.ZigzagSlabOrigin
import Mettapedia.GraphTheory.FourColor.ZigzagTubeCompression

/-!
# A recognized hexagonal row chain realizes a literal tube

The proof assembles the original embedded darts and vertices. At each seam,
the cyclic offset derived from actual hexagonal faces selects a coordinate
shift of the next ring. The resulting serial constructor has exactly the
same vertices, internal edge mates, rotations and outer boundary darts.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.Tube

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData ZigzagRing
open GoertzelV24RotationCutDartDecomposition

noncomputable section
universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {k : ℕ} [NeZero k]

/-- Append recognized rows to an already embedded literal tangle. The
remaining chain determines every seam shift from its ambient face data. -/
theorem assembleRings {current : V → Prop} {n : ℕ}
    (t : Tube RS k current n) (ht : t.Hexagonal)
    {initial : V → Prop} (P : HiddenTangle (Fin k) (Fin k))
    (S : SlabOf RS P.data initial) (hS : S.RotationCompatible)
    (hside : S.inner' = current) (a : Fin k)
    (hjoin : ∀ i, (t.firstEquiv (i + a)).1.1 = S.ι (.inr (.inr i))) :
    ∃ U : SlabOf RS (HiddenTangle.appendRings k P n).data initial,
      U.RotationCompatible ∧ U.inner' = t.side n ∧
      (∀ i, U.ι (.inr (.inl i)) = S.ι (.inr (.inl i))) ∧
      (∀ i, U.ι (.inr (.inr i)) = (t.alignedEquiv n (i + a)).1.1) := by
  induction t generalizing initial P a with
  | nil current e =>
    exact ⟨S, hS, hside, fun _ => rfl, fun i => (hjoin i).symm⟩
  | @cons current R n rest ih =>
    subst current
    let R' := R.asSlab.shiftRing a
    have hR' : R'.RotationCompatible := R.asSlab.shiftRing_rotationCompatible a ht.1
    have hm : S.matching R' = Equiv.refl (Fin k) := by
      apply Equiv.ext
      intro i
      apply R'.inEquiv.injective
      change R'.inEquiv (R'.inEquiv.symm (S.outEquiv i)) = R'.inEquiv i
      rw [Equiv.apply_symm_apply]
      apply Subtype.ext
      apply Subtype.ext
      exact (hjoin i).symm
    let U := S.assembleWith R' (Equiv.refl _) hm
    have hU : U.RotationCompatible := S.assembleWith_rotationCompatible R' _ hm hS hR'
    have hUside : U.inner' = R.inner' :=
      (S.assembleWith_inner' R' _ hm).trans (R.asSlab.shiftRing_inner' a)
    let b := a + nextSeam R rest 0
    have hnext : ∀ i, (rest.firstEquiv (i + b)).1.1 = U.ι (.inr (.inr i)) := by
      intro i
      have h := congrArg (fun e => (e i).1.1)
        (next_origin R rest (ht.cyclicCoherent (.cons R rest)).1 a)
      change (rest.firstEquiv (i + b)).1.1 = (R.outEquiv (i + a)).1.1 at h
      rw [h]
      exact (S.assembleWith_output R' _ hm i).symm
    obtain ⟨Z, hZ, hZside, hZin, hZout⟩ :=
      ih ht.2.2 (HiddenTangle.appendRing k P) U hU hUside b hnext
    simp only [HiddenTangle.appendRings, Function.iterate_succ_apply]
    refine ⟨Z, hZ, hZside, ?_, ?_⟩
    · intro i
      exact (hZin i).trans (S.assembleWith_input R' _ hm i)
    · intro i
      exact (hZout i).trans (congrArg (fun j => (rest.alignedEquiv n j).1.1)
        (add_assoc i a (nextSeam R rest 0)).symm)

/-- A nonempty recognized chain embeds the literal tube with exactly its
original two boundary interfaces and all of its original strip vertices. -/
theorem literalSlab {inner : V → Prop} {n : ℕ}
    (t : Tube RS k inner (n + 1)) (ht : t.Hexagonal) :
    ∃ U : SlabOf RS (tube k n).data inner,
      U.RotationCompatible ∧ U.inner' = t.side (n + 1) ∧
      (∀ i, RS.alpha (U.ι (.inr (.inl i))) = (t.firstEquiv i).1.1) ∧
      (∀ i, U.ι (.inr (.inr i)) = (t.alignedEquiv (n + 1) i).1.1) := by
  unfold tube
  cases t with
  | cons R rest =>
    let a := nextSeam R rest 0
    have hjoin : ∀ i, (rest.firstEquiv (i + a)).1.1 = R.ι (.inr (.inr i)) := by
      intro i
      have h := congrArg (fun e => (e i).1.1)
        (next_origin R rest (ht.cyclicCoherent (.cons R rest)).1 0)
      simp only [zero_add, atOrigin_apply, add_zero] at h
      exact h
    obtain ⟨U, hU, hside, hin, hout⟩ := assembleRings rest ht.2.2
      ⟨Vtx k, Dart k, ring k⟩ R.asSlab ht.1 rfl a hjoin
    refine ⟨U, hU, hside, ?_, ?_⟩
    · intro i
      rw [hin]
      rfl
    · intro i
      exact hout i

end
end Mettapedia.GraphTheory.FourColor.TubeSlab.Tube
