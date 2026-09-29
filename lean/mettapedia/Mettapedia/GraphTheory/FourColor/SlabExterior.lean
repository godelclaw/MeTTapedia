import Mettapedia.GraphTheory.FourColor.SlabAssembly
import Mettapedia.GraphTheory.FourColor.SerialTangleSmallCutTransfer
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideReassembly
import Mettapedia.GraphTheory.FourColor.RotationSystemExactTransport

/-!
# The actual exterior of an embedded slab

Removing exactly the slab's vertices exposes its two ordered interfaces.
Sewing the literal slab into this exterior recovers every ambient dart,
vertex, edge mate and rotation. No connectivity assumption on the exterior
is needed.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.SlabOf

open GoertzelV24OpenTangleComposition GoertzelV24RotationCutDartDecomposition
open SerialTangleSmallCutTransfer GoertzelV24VertexSideReassembly
open GoertzelV24TwoEdgeCutMinimality

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {k : ℕ} [NeZero k]
  {A I : Type*} {P : TwoSidedOpenTangleData A I (Fin k) (Fin k)}
  {inner : V → Prop} (S : SlabOf RS P inner)

/-- All original vertices outside the strip, including both end shores. -/
def outsideKeep (v : V) : Prop := ¬ ∃ a, v = S.vtx a

omit [NeZero k] in
theorem outsideKeep_inner {v : V} (hv : inner v) : S.outsideKeep v := by
  rintro ⟨a, rfl⟩
  exact S.vtx_not_inner a hv

omit [NeZero k] in
theorem not_outsideKeep_dart (d : SlabDart P) : ¬ S.outsideKeep (RS.vertOf (S.ι d)) :=
  fun h => h ⟨P.vertOf d, S.vert_ι d⟩

/-- The opposite half of each slab port lies in the actual exterior. -/
def outsidePort (b : Fin k ⊕ Fin k) : BoundaryDart RS S.outsideKeep :=
  ⟨⟨RS.alpha (S.ι (.inr b)), by
    cases b with
    | inl i => exact S.outsideKeep_inner (S.in_inner i)
    | inr i => exact fun ⟨a, ha⟩ => S.out_not_slab i a ha⟩,
    by simpa only [RS.alpha_involutive] using S.not_outsideKeep_dart (.inr b)⟩

theorem outsidePort_injective : Function.Injective S.outsidePort := by
  intro b c h
  exact Sum.inr.inj (S.ι_inj (RS.alpha.injective
    (congrArg (fun x : BoundaryDart RS S.outsideKeep => x.1.1) h)))

theorem outsidePort_surjective : Function.Surjective S.outsidePort := by
  classical
  intro b
  have hex : ∃ a, RS.vertOf (RS.alpha b.1.1) = S.vtx a := by
    simpa only [outsideKeep, not_not] using b.2
  obtain ⟨d, hd⟩ := S.cubic_slab (RS.alpha b.1.1) hex
  cases d with
  | inl i =>
    exfalso
    apply b.1.2
    refine ⟨P.vertOf (.inl (P.interiorAlpha i)), ?_⟩
    have h := congrArg RS.alpha hd
    rw [RS.alpha_involutive, S.alpha_interior] at h
    exact (congrArg RS.vertOf h).symm.trans (S.vert_ι _)
  | inr p =>
    refine ⟨p, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg RS.alpha hd).trans (RS.alpha_involutive _)

def outsideBoundaryEquiv : (Fin k ⊕ Fin k) ≃ BoundaryDart RS S.outsideKeep :=
  Equiv.ofBijective S.outsidePort ⟨S.outsidePort_injective, S.outsidePort_surjective⟩

/-- Cut out precisely the slab, leaving every exterior dart unchanged. -/
def exterior : OpenTangleData {v : V // S.outsideKeep v}
    (InternalDart RS S.outsideKeep) (BoundaryDart RS S.outsideKeep) :=
  OpenTangleData.ofVertexSide RS S.outsideKeep (S.outsidePort (.inl 0)).1

def exteriorDart : (InternalDart RS S.outsideKeep ⊕ BoundaryDart RS S.outsideKeep) → RS.D :=
  fun d => ((retainedDartEquivInternalSumBoundary RS S.outsideKeep).symm d).1

omit [NeZero k] in
theorem exteriorDart_injective : Function.Injective S.exteriorDart :=
  Subtype.val_injective.comp (retainedDartEquivInternalSumBoundary RS S.outsideKeep).symm.injective

omit [NeZero k] in
theorem exteriorDart_outside (d) : S.outsideKeep (RS.vertOf (S.exteriorDart d)) :=
  ((retainedDartEquivInternalSumBoundary RS S.outsideKeep).symm d).2

theorem exteriorDart_disjoint (d) (a : SlabDart P) : S.exteriorDart d ≠ S.ι a := by
  intro h
  apply S.not_outsideKeep_dart a
  rw [← h]
  exact S.exteriorDart_outside d

def exteriorVertexEquiv : ({v : V // S.outsideKeep v} ⊕ A) ≃ V :=
  Equiv.ofBijective (Sum.elim Subtype.val S.vtx) (by
    classical
    constructor
    · rintro (v | a) (w | b) h
      · exact congrArg Sum.inl (Subtype.ext h)
      · exact (v.2 ⟨b, h⟩).elim
      · exact (w.2 ⟨a, h.symm⟩).elim
      · exact congrArg Sum.inr (S.vtx_inj h)
    · intro v
      by_cases h : S.outsideKeep v
      · exact ⟨.inl ⟨v, h⟩, rfl⟩
      · obtain ⟨a, ha⟩ := not_not.mp h
        exact ⟨.inr a, ha.symm⟩)

def exteriorSumDartEquiv :
    ((InternalDart RS S.outsideKeep ⊕ BoundaryDart RS S.outsideKeep) ⊕ SlabDart P) ≃ RS.D :=
  Equiv.ofBijective (Sum.elim S.exteriorDart S.ι) (by
    classical
    constructor
    · rintro (d | a) (e | b) h
      · exact congrArg Sum.inl (S.exteriorDart_injective h)
      · exact (S.exteriorDart_disjoint d b h).elim
      · exact (S.exteriorDart_disjoint e a h.symm).elim
      · exact congrArg Sum.inr (S.ι_inj h)
    · intro d
      by_cases h : S.outsideKeep (RS.vertOf d)
      · refine ⟨.inl ((retainedDartEquivInternalSumBoundary RS S.outsideKeep) ⟨d, h⟩), ?_⟩
        change ((retainedDartEquivInternalSumBoundary RS S.outsideKeep).symm
          ((retainedDartEquivInternalSumBoundary RS S.outsideKeep) ⟨d, h⟩)).1 = d
        rw [Equiv.symm_apply_apply]
      · obtain ⟨a, ha⟩ := not_not.mp h
        obtain ⟨x, hx⟩ := S.cubic_slab d ⟨a, ha⟩
        exact ⟨.inr x, hx⟩)

variable [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

/-- Sew the literal slab back into its own exterior using its actual mates. -/
abbrev reassembled := S.exterior.composeRotationSystem (asOpen P) S.outsideBoundaryEquiv.symm

def reassemblyDartEquiv : S.reassembled.D ≃ RS.D :=
  composeDartEquiv.symm.trans S.exteriorSumDartEquiv

@[simp] theorem reassemblyDartEquiv_left (d) :
    S.reassemblyDartEquiv (composeDartEquiv (.inl d)) = S.exteriorDart d := by
  exact congrArg (Sum.elim S.exteriorDart S.ι) (composeDartEquiv.symm_apply_apply (.inl d))

@[simp] theorem reassemblyDartEquiv_right (d) :
    S.reassemblyDartEquiv (composeDartEquiv (.inr d)) = S.ι d := by
  exact congrArg (Sum.elim S.exteriorDart S.ι) (composeDartEquiv.symm_apply_apply (.inr d))

theorem reassemblyDartEquiv_alpha (d : S.reassembled.D) :
    S.reassemblyDartEquiv (S.reassembled.alpha d) = RS.alpha (S.reassemblyDartEquiv d) := by
  rcases d with (a | i) | (b | p)
  · rfl
  · exact (S.alpha_interior i).symm
  · have h := congrArg (fun b : BoundaryDart RS S.outsideKeep => b.1.1)
      (S.outsideBoundaryEquiv.apply_symm_apply b)
    change RS.alpha (S.ι (.inr (S.outsideBoundaryEquiv.symm b))) = b.1.1 at h
    have hh := congrArg RS.alpha h
    rw [RS.alpha_involutive] at hh
    exact hh
  · rfl

theorem reassemblyDartEquiv_vert (d : S.reassembled.D) :
    S.exteriorVertexEquiv (S.reassembled.vertOf d) = RS.vertOf (S.reassemblyDartEquiv d) := by
  rcases d with (a | i) | (b | p)
  · rfl
  · exact (S.vert_ι (.inl i)).symm
  · rfl
  · cases p with
    | inl i => exact (S.vert_ι (.inr (.inl i))).symm
    | inr i => exact (S.vert_ι (.inr (.inr i))).symm

theorem reassemblyDartEquiv_rho (hS : S.RotationCompatible) (d : S.reassembled.D) :
    S.reassemblyDartEquiv (S.reassembled.rho d) = RS.rho (S.reassemblyDartEquiv d) := by
  obtain ⟨x, rfl⟩ := composeDartEquiv.surjective d
  change S.reassemblyDartEquiv (composeDartEquiv
    ((Equiv.sumCongr S.exterior.rho (asOpen P).rho)
      (composeDartEquiv.symm (composeDartEquiv x)))) = _
  rw [Equiv.symm_apply_apply]
  cases x with
  | inl x =>
    simp only [Equiv.sumCongr_apply, Sum.map_inl, reassemblyDartEquiv_left]
    exact congrArg Subtype.val (OpenTangleData.ofVertexSide_rho_underlying
      RS S.outsideKeep (S.outsidePort (.inl 0)).1 x)
  | inr x =>
    simp only [Equiv.sumCongr_apply, Sum.map_inr, reassemblyDartEquiv_right]
    exact (hS x).symm

/-- Actual exterior sewing preserves colourability, without a planar premise. -/
theorem reassembled_colorable_iff :
    RotationSystemTaitColorable S.reassembled ↔ RotationSystemTaitColorable RS :=
  rotationSystemTaitColorable_iff_of_dartEquiv S.reassembled RS
    S.reassemblyDartEquiv S.exteriorVertexEquiv
    S.reassemblyDartEquiv_alpha S.reassemblyDartEquiv_vert

/-- Reassembly transports the ambient geometric class without an extra
assumption about either end shore. -/
theorem reassembled_class (hS : S.RotationCompatible)
    (h : BridgelessSphericalCubicMapData RS) :
    BridgelessSphericalCubicMapData S.reassembled := by
  apply RotationSystemExactTransport.mapClass RS S.reassembled
    S.reassemblyDartEquiv.symm S.exteriorVertexEquiv.symm _ _ _ h
  · intro x
    apply S.reassemblyDartEquiv.injective
    rw [Equiv.apply_symm_apply, S.reassemblyDartEquiv_alpha, Equiv.apply_symm_apply]
  · intro x
    apply S.exteriorVertexEquiv.injective
    rw [Equiv.apply_symm_apply, S.reassemblyDartEquiv_vert, Equiv.apply_symm_apply]
  · intro x
    apply S.reassemblyDartEquiv.injective
    rw [Equiv.apply_symm_apply, S.reassemblyDartEquiv_rho hS, Equiv.apply_symm_apply]

end
end Mettapedia.GraphTheory.FourColor.TubeSlab.SlabOf
