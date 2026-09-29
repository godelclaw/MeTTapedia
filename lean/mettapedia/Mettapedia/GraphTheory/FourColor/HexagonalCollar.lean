import Mettapedia.GraphTheory.FourColor.HexagonalSlabSeam
import Mettapedia.GraphTheory.FourColor.CyclicPortChordExclusion
import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFaces

/-!
# Constructing the next row from a hexagonal collar

The candidate vertices and darts are read from the original edge reversal
and rotation. Six-step face closure supplies the next cyclic row's edges.
Distinct candidate vertices and short output-port faces suffice to construct
a complete new slab. No successor cycle or slab is an input.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24OpenTangleComposition GoertzelV24RotationCutDartDecomposition
open PhysicalForkCodeFaces GoertzelV24HexFaceRungType

namespace ZigzagRing

variable {k : ℕ} [NeZero k]

/-- A dart's vertex and its position in the oriented cubic star. At an
incoming vertex the origin is the input port; at an outgoing vertex it is
the preceding cycle edge. -/
def starCoordinates : AllDart k ≃ Vtx k × Fin 3 where
  toFun
    | .inr (.inl i) => (.inl i, 0)
    | .inl (.inl (i, false)) => (.inl i, 1)
    | .inl (.inr (i, true)) => (.inl (i + 1), 2)
    | .inl (.inl (i, true)) => (.inr i, 0)
    | .inl (.inr (i, false)) => (.inr i, 1)
    | .inr (.inr i) => (.inr i, 2)
  invFun
    | (.inl i, 0) => .inr (.inl i)
    | (.inl i, 1) => .inl (.inl (i, false))
    | (.inl i, 2) => .inl (.inr (i - 1, true))
    | (.inr i, 0) => .inl (.inl (i, true))
    | (.inr i, 1) => .inl (.inr (i, false))
    | (.inr i, 2) => .inr (.inr i)
  left_inv := by
    rintro ((⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i)) <;>
      simp [add_sub_cancel_right]
  right_inv := by
    rintro ⟨i | i, j⟩ <;> fin_cases j <;> simp [sub_add_cancel]

theorem starCoordinates_vertex (d : AllDart k) :
    (starCoordinates d).1 = (ring k).vertOf d := by
  rcases d with (⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i) <;> rfl

end ZigzagRing

namespace TubeSlab.ZigzagSlab

open ZigzagRing CyclicPortChordExclusion

noncomputable section
universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {k : ℕ} [NeZero k]
  {inner : V → Prop} (S : ZigzagSlab RS k inner)

/-- Cross the actual output edge to the first new vertex. -/
def collarInput (i : Fin k) : RS.D := RS.alpha (S.ι (.inr (.inr i)))

/-- Follow the next edge of the exterior hexagon to its middle vertex. -/
def collarMiddle (i : Fin k) : RS.D := RS.alpha (RS.rho (S.collarInput i))

def collarBase : Vtx k → RS.D
  | .inl i => S.collarInput i
  | .inr i => S.collarMiddle i

def collarVertex (v : Vtx k) : V := RS.vertOf (S.collarBase v)

/-- The entire new star is determined by the ambient rotation. -/
def collarDart (d : AllDart k) : RS.D :=
  (RS.rho ^ (starCoordinates d).2.val) (S.collarBase (starCoordinates d).1)

theorem collarDart_vertex (d : AllDart k) :
    RS.vertOf (S.collarDart d) = S.collarVertex ((ring k).vertOf d) := by
  rw [collarDart, vertOf_rho_pow, collarVertex, starCoordinates_vertex]

private theorem star_injective (hC : Cubic3 RS) (d : RS.D) :
    Function.Injective (fun j : Fin 3 => (RS.rho ^ j.val) d) := by
  have h10 := hC.moves d
  have h21 := hC.moves (RS.rho d)
  have h20 : RS.rho (RS.rho d) ≠ d := by
    intro h
    have hh := congrArg RS.rho h
    rw [hC.cube] at hh
    exact h10 hh.symm
  intro i j h
  fin_cases i <;> fin_cases j <;>
    norm_num only [pow_succ, pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h <;>
    first | rfl | exact (h10 h).elim | exact (h10 h.symm).elim |
      exact (h21 h).elim | exact (h21 h.symm).elim |
      exact (h20 h).elim | exact (h20 h.symm).elim

theorem collarDart_injective (hC : Cubic3 RS)
    (hv : Function.Injective S.collarVertex) : Function.Injective S.collarDart := by
  intro a b hab
  have h := hv ((S.collarDart_vertex a).symm.trans
    ((congrArg RS.vertOf hab).trans (S.collarDart_vertex b)))
  apply starCoordinates.injective
  apply Prod.ext
  · simpa only [starCoordinates_vertex] using h
  · apply star_injective hC (S.collarBase (starCoordinates b).1)
    simpa only [collarDart, starCoordinates_vertex, h] using hab

theorem collar_rotation (hC : Cubic3 RS) (d : AllDart k) :
    RS.rho (S.collarDart d) = S.collarDart (rho k d) := by
  rcases d with (⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i) <;>
    simp [collarDart, starCoordinates, rho, rhoFun,
      pow_succ, Equiv.Perm.mul_apply, sub_add_cancel, hC.cube]

theorem collar_fiber (hC : Cubic3 RS) (d : RS.D)
    (hd : ∃ v, RS.vertOf d = S.collarVertex v) : ∃ x, S.collarDart x = d := by
  obtain ⟨v, hv⟩ := hd
  rcases hC.fiber (S.collarBase v) d hv with h | h | h
  · exact ⟨starCoordinates.symm (v, 0), by simp [collarDart, h]⟩
  · exact ⟨starCoordinates.symm (v, 1), by simp [collarDart, h]⟩
  · exact ⟨starCoordinates.symm (v, 2), by simp [collarDart, h, pow_succ, Equiv.Perm.mul_apply]⟩

/-- The other half of each hexagon closes the two new cycle edges. -/
theorem collar_three_steps (hS : S.RotationCompatible) (hh : S.HexagonalSeam)
    (i : Fin k) : (RS.phi ^ 3) (S.ι (.inr (.inr i))) = S.collarInput (i + 1) := by
  have hold := S.output_three_steps hS (i + 1)
  simp only [add_sub_cancel_right] at hold
  apply (RS.phi ^ 3).injective
  rw [← Equiv.Perm.mul_apply, ← pow_add]
  exact (S.seam_six_steps hh i).trans hold.symm

theorem collar_second_edge (hC : Cubic3 RS) (hS : S.RotationCompatible)
    (hh : S.HexagonalSeam) (i : Fin k) :
    RS.alpha (RS.rho (S.collarMiddle i)) =
      RS.rho (RS.rho (S.collarInput (i + 1))) := by
  have h := S.collar_three_steps hS hh i
  change RS.rho (RS.alpha (RS.rho (S.collarMiddle i))) = S.collarInput (i + 1) at h
  have h' := congrArg (fun d => RS.rho (RS.rho d)) h
  simpa only [hC.cube] using h'

theorem collar_alpha (hC : Cubic3 RS) (hS : S.RotationCompatible)
    (hh : S.HexagonalSeam) (d : Dart k) :
    RS.alpha (S.collarDart (.inl d)) = S.collarDart (.inl (flip k d)) := by
  rcases d with ⟨i, _ | _⟩ | ⟨i, _ | _⟩
  · rfl
  · exact RS.alpha_involutive _
  · exact S.collar_second_edge hC hS hh i
  · have h := congrArg RS.alpha (S.collar_second_edge hC hS hh i)
    simpa [collarDart, starCoordinates, collarBase, ZigzagRing.flip,
      pow_succ, Equiv.Perm.mul_apply, RS.alpha_involutive] using h.symm

/-- Distinct candidate vertices force the whole new row to be outside the
old side. A premature return would identify two candidate star darts. -/
theorem collarVertex_outside (hC : Cubic3 RS)
    (hv : Function.Injective S.collarVertex) (v : Vtx k) :
    ¬ S.inner' (S.collarVertex v) := by
  cases v with
  | inl i => exact (S.outPort i).2
  | inr i =>
    intro hi
    have hx : ¬ S.inner' (RS.vertOf (RS.rho (S.collarInput i))) := by
      rw [RS.vert_rho]
      exact (S.outPort i).2
    let b : BoundaryDart RS S.inner' := ⟨⟨S.collarMiddle i, hi⟩, by
      simpa only [collarMiddle, RS.alpha_involutive] using hx⟩
    obtain ⟨j, hj⟩ := S.outPort_surjective b
    have he := congrArg (fun b : BoundaryDart RS S.inner' => b.1.1) hj
    have hmate := congrArg RS.alpha he
    change S.collarInput j = RS.alpha (S.collarMiddle i) at hmate
    simp only [collarMiddle, RS.alpha_involutive] at hmate
    have hd : S.collarDart (.inr (.inl j)) =
        S.collarDart (.inl (.inl (i, false))) := hmate
    cases S.collarDart_injective hC hv hd

theorem collarDart_outside (hC : Cubic3 RS)
    (hv : Function.Injective S.collarVertex) (d : AllDart k) :
    ¬ S.inner' (RS.vertOf (S.collarDart d)) := by
  rw [S.collarDart_vertex]
  exact S.collarVertex_outside hC hv _

def collarOutputArcs (hC : Cubic3 RS) (hS : S.RotationCompatible)
    (hh : S.HexagonalSeam) (hv : Function.Injective S.collarVertex) :
    Arcs RS.phi RS.alpha k where
  port i := S.collarDart (.inr (.inr (-i)))
  first i := S.collarDart (.inl (.inl (-i, true)))
  second i := S.collarDart (.inl (.inr (-i - 1, true)))
  start i := by
    rw [RotationSystem.phi_apply, RS.alpha_involutive, S.collar_rotation hC]
    rfl
  middle i := by
    rw [RotationSystem.phi_apply, S.collar_alpha hC hS hh, S.collar_rotation hC]
    rfl
  finish i := by
    rw [RotationSystem.phi_apply, S.collar_alpha hC hS hh, S.collar_rotation hC]
    change S.collarDart (.inr (.inr (-i - 1))) = S.collarDart (.inr (.inr (-(i + 1))))
    simp [sub_eq_add_neg, add_comm]
  disjoint i j := by
    intro he
    cases S.collarDart_injective hC hv he

/-- Only actual face lengths at the new output ports are required. -/
def CollarShortFaces : Prop := ∀ i : Fin k,
  (RS.faceOrbit (S.collarDart (.inr (.inr i)))).card = 5 ∨
    (RS.faceOrbit (S.collarDart (.inr (.inr i)))).card = 6

theorem collar_output_no_chord (hC : Cubic3 RS) (hS : S.RotationCompatible)
    (hh : S.HexagonalSeam) (hv : Function.Injective S.collarVertex)
    (hs : S.CollarShortFaces) (i j : Fin k) :
    RS.alpha (S.collarDart (.inr (.inr i))) ≠ S.collarDart (.inr (.inr j)) := by
  let A := S.collarOutputArcs hC hS hh hv
  have hc (a : Fin k) : (RS.faceOrbit (A.port a)).card = 5 ∨
      (RS.faceOrbit (A.port a)).card = 6 := hs (-a)
  have hn := A.no_chord RS.alpha_involutive RS.alpha_fixfree (fun a => by
    have hp := (faceOrbit_isCycleOn RS (A.port a)).pow_card_apply
      (RS.mem_faceOrbit_self (A.port a))
    rcases hc a with h | h
    · exact Or.inl (h ▸ hp)
    · exact Or.inr (h ▸ hp)) (fun a h => by
    have hdvd := (faceOrbit_isCycleOn RS (A.port a)).pow_apply_eq
      (RS.mem_faceOrbit_self (A.port a)) |>.mp h
    rcases hc a with he | he <;> norm_num [he] at hdvd) (-i) (-j)
  simpa only [A, collarOutputArcs, neg_neg] using hn

theorem collar_output_outside (hC : Cubic3 RS)
    (hv : Function.Injective S.collarVertex) (i : Fin k) :
    ¬ S.inner' (RS.vertOf (RS.alpha (S.collarDart (.inr (.inr i))))) := by
  intro hi
  let b : BoundaryDart RS S.inner' :=
    ⟨⟨RS.alpha (S.collarDart (.inr (.inr i))), hi⟩,
      by simpa only [RS.alpha_involutive] using S.collarDart_outside hC hv (.inr (.inr i))⟩
  obtain ⟨j, hj⟩ := S.outPort_surjective b
  have hm := congrArg RS.alpha (congrArg (fun b : BoundaryDart RS S.inner' => b.1.1) hj)
  rw [RS.alpha_involutive] at hm
  have he : S.collarDart (.inr (.inl j)) = S.collarDart (.inr (.inr i)) := hm
  cases S.collarDart_injective hC hv he

theorem collar_output_off_row (hC : Cubic3 RS) (hS : S.RotationCompatible)
    (hh : S.HexagonalSeam) (hv : Function.Injective S.collarVertex)
    (hs : S.CollarShortFaces) (i : Fin k) (v : Vtx k) :
    RS.vertOf (RS.alpha (S.collarDart (.inr (.inr i)))) ≠ S.collarVertex v := by
  intro he
  obtain ⟨d, hd⟩ := S.collar_fiber hC _ ⟨v, he⟩
  have hm := congrArg RS.alpha hd
  rw [RS.alpha_involutive] at hm
  cases d with
  | inl d =>
    rw [S.collar_alpha hC hS hh] at hm
    cases S.collarDart_injective hC hv hm
  | inr p =>
    cases p with
    | inl j =>
      have hj : S.inner' (RS.vertOf (RS.alpha (S.collarDart (.inr (.inl j))))) := by
        change S.inner' (RS.vertOf (RS.alpha (RS.alpha (S.ι (.inr (.inr j))))))
        rw [RS.alpha_involutive]
        exact S.slab_inner' _
      rw [hm] at hj
      exact S.collarDart_outside hC hv _ hj
    | inr j => exact S.collar_output_no_chord hC hS hh hv hs i j hd.symm

/-- A whole next row is constructed from its hexagonal collar. Its cyclic
order, chordlessness, complete cut maps and attachment geometry are outputs. -/
def nextRow (hC : Cubic3 RS) (hS : S.RotationCompatible)
    (hh : S.HexagonalSeam) (hv : Function.Injective S.collarVertex)
    (hs : S.CollarShortFaces) : ZigzagSlab RS k S.inner' where
  ι := S.collarDart
  vtx := S.collarVertex
  ι_inj := S.collarDart_injective hC hv
  vtx_inj := hv
  vtx_not_inner := S.collarVertex_outside hC hv
  vert_ι := S.collarDart_vertex
  alpha_interior := S.collar_alpha hC hS hh
  in_inner i := by
    change S.inner' (RS.vertOf (RS.alpha (RS.alpha (S.ι (.inr (.inr i))))))
    rw [RS.alpha_involutive]
    exact S.slab_inner' _
  out_not_inner := S.collar_output_outside hC hv
  out_not_slab := S.collar_output_off_row hC hS hh hv hs
  cubic_slab := S.collar_fiber hC
  boundary_inner b := by
    obtain ⟨i, hi⟩ := S.outPort_surjective b
    exact ⟨i, by
      change b.1.1 = RS.alpha (RS.alpha (S.ι (.inr (.inr i))))
      rw [RS.alpha_involutive]
      exact (congrArg (fun b : BoundaryDart RS S.inner' => b.1.1) hi).symm⟩

theorem nextRow_rotation (hC : Cubic3 RS) (hS : S.RotationCompatible)
    (hh : S.HexagonalSeam) (hv : Function.Injective S.collarVertex)
    (hs : S.CollarShortFaces) : (S.nextRow hC hS hh hv hs).RotationCompatible :=
  S.collar_rotation hC

/-- The new input labels are inherited from the original output, with no
extra seam permutation premise. -/
theorem nextRow_inEquiv (hC : Cubic3 RS) (hS : S.RotationCompatible)
    (hh : S.HexagonalSeam) (hv : Function.Injective S.collarVertex)
    (hs : S.CollarShortFaces) : (S.nextRow hC hS hh hv hs).inEquiv = S.outEquiv := by
  ext i
  apply Subtype.ext
  apply Subtype.ext
  exact RS.alpha_involutive (S.ι (.inr (.inr i)))

/-- Any oriented successor has these same candidate vertices, in the
coordinates determined by its actual input-boundary bijection. -/
theorem collarVertex_eq_successor (T : ZigzagSlab RS k S.inner')
    (hT : T.RotationCompatible) (v : Vtx k) :
    S.collarVertex v = T.vtx ((Equiv.sumCongr (S.seam T) (S.seam T)) v) := by
  have hx (i : Fin k) : S.collarInput i = T.ι (.inr (.inl (S.seam T i))) :=
    S.seam_mate T i
  have hy (i : Fin k) : S.collarMiddle i = T.ι (.inl (.inl (S.seam T i, true))) := by
    rw [collarMiddle, hx, hT]
    change RS.alpha (T.ι (.inl (.inl (S.seam T i, false)))) = _
    exact T.alpha_interior (.inl (S.seam T i, false))
  cases v with
  | inl i =>
    change RS.vertOf (S.collarInput i) = T.vtx (.inl (S.seam T i))
    rw [hx]
    exact T.vert_ι _
  | inr i =>
    change RS.vertOf (S.collarMiddle i) = T.vtx (.inr (S.seam T i))
    rw [hy]
    exact T.vert_ι _

theorem collarVertex_injective_of_successor (T : ZigzagSlab RS k S.inner')
    (hT : T.RotationCompatible) : Function.Injective S.collarVertex := by
  intro v w h
  rw [S.collarVertex_eq_successor T hT v, S.collarVertex_eq_successor T hT w] at h
  exact (Equiv.sumCongr (S.seam T) (S.seam T)).injective (T.vtx_inj h)

/-- Under the stated face conditions, distinct candidate vertices are the
exact criterion for an oriented successor row, not merely a sufficient test
for a chosen parametrization. -/
theorem exists_nextRow_iff (hC : Cubic3 RS) (hS : S.RotationCompatible)
    (hh : S.HexagonalSeam) (hs : S.CollarShortFaces) :
    (∃ T : ZigzagSlab RS k S.inner', T.RotationCompatible) ↔
      Function.Injective S.collarVertex := by
  constructor
  · rintro ⟨T, hT⟩
    exact S.collarVertex_injective_of_successor T hT
  · intro hv
    exact ⟨S.nextRow hC hS hh hv hs, S.nextRow_rotation hC hS hh hv hs⟩

/-- The constructed collar's two boundary words compose with genuine
colourings of the original side in its original output coordinates. -/
theorem nextRow_support (hC : Cubic3 RS) (hS : S.RotationCompatible)
    (hh : S.HexagonalSeam) (hv : Function.Injective S.collarVertex)
    (hs : S.CollarShortFaces) (y : Fin k → Color) :
    let T := S.nextRow hC hS hh hv hs
    (fun b => y (T.outEquiv.symm b)) ∈ sideSupport RS T.inner' ↔
      ∃ x : Fin k → Color, (fun b => x (S.outEquiv.symm b)) ∈ sideSupport RS S.inner' ∧
        Step k x y := by
  dsimp only
  rw [(S.nextRow hC hS hh hv hs).mem_sideSupport_inner'_iff,
    S.nextRow_inEquiv hC hS hh hv hs]

end
end TubeSlab.ZigzagSlab
end Mettapedia.GraphTheory.FourColor
