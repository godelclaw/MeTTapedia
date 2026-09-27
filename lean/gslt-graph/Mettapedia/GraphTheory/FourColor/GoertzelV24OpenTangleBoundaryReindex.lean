import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleComposition

/-!
# Reindexing literal open-tangle boundaries

An open tangle is unchanged when its boundary half-edges are given different
finite coordinates.  This small transport is deliberately separate from
serial composition: it only changes the displayed boundary carrier.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenTangleComposition

namespace OpenTangleData

variable {V I B B' : Type*}

/-- Reindex the boundary summand of an open-tangle dart carrier. -/
def boundaryReindexDartEquiv (boundaryEquiv : B' ≃ B) :
    I ⊕ B' ≃ I ⊕ B :=
  Equiv.sumCongr (Equiv.refl I) boundaryEquiv

@[simp]
theorem boundaryReindexDartEquiv_interior (boundaryEquiv : B' ≃ B)
    (dart : I) :
    boundaryReindexDartEquiv (I := I) boundaryEquiv (Sum.inl dart) =
      Sum.inl dart :=
  rfl

@[simp]
theorem boundaryReindexDartEquiv_boundary (boundaryEquiv : B' ≃ B)
    (dart : B') :
    boundaryReindexDartEquiv (I := I) boundaryEquiv (Sum.inr dart) =
      Sum.inr (boundaryEquiv dart) :=
  rfl

/-- The vertex map is unchanged after transporting a boundary coordinate. -/
theorem vertOf_boundaryReindexDartEquiv (data : OpenTangleData V I B)
    (boundaryEquiv : B' ≃ B) (dart : I ⊕ B') :
    openTangleVertOf data.interiorVert
        (fun boundary => data.boundaryVert (boundaryEquiv boundary))
        dart =
      data.vertOf ((boundaryReindexDartEquiv (I := I) boundaryEquiv) dart) := by
  rcases dart with interior | boundary <;> rfl

/-- Transport an ordinary literal open tangle along an equivalence of its
displayed boundary carrier. -/
noncomputable def reindexBoundary (data : OpenTangleData V I B)
    (boundaryEquiv : B' ≃ B) : OpenTangleData V I B' where
  interiorVert := data.interiorVert
  boundaryVert := fun boundary => data.boundaryVert (boundaryEquiv boundary)
  interiorAlpha := data.interiorAlpha
  interiorAlpha_involutive := data.interiorAlpha_involutive
  interiorAlpha_fixfree := data.interiorAlpha_fixfree
  rho :=
    (((boundaryReindexDartEquiv (I := I) boundaryEquiv).trans data.rho).trans
      (boundaryReindexDartEquiv (I := I) boundaryEquiv).symm)
  vert_rho := by
    intro dart
    let dartEquiv := boundaryReindexDartEquiv (I := I) boundaryEquiv
    change openTangleVertOf data.interiorVert
        (fun boundary => data.boundaryVert (boundaryEquiv boundary))
        (((dartEquiv.trans data.rho).trans dartEquiv.symm) dart) =
      openTangleVertOf data.interiorVert
        (fun boundary => data.boundaryVert (boundaryEquiv boundary)) dart
    simp only [Equiv.trans_apply]
    calc
      openTangleVertOf data.interiorVert
          (fun boundary => data.boundaryVert (boundaryEquiv boundary))
          (dartEquiv.symm (data.rho (dartEquiv dart))) =
        data.vertOf (data.rho (dartEquiv dart)) := by
          rw [vertOf_boundaryReindexDartEquiv]
          change data.vertOf
              (dartEquiv (dartEquiv.symm (data.rho (dartEquiv dart)))) = _
          rw [dartEquiv.apply_symm_apply]
      _ = data.vertOf (dartEquiv dart) := by
        exact data.vert_rho (dartEquiv dart)
      _ = openTangleVertOf data.interiorVert
          (fun boundary => data.boundaryVert (boundaryEquiv boundary)) dart := by
        exact (vertOf_boundaryReindexDartEquiv data boundaryEquiv dart).symm
  interior_no_self_loops := data.interior_no_self_loops
  outer := (boundaryReindexDartEquiv (I := I) boundaryEquiv).symm data.outer

end OpenTangleData

end GoertzelV24OpenTangleComposition

end Mettapedia.GraphTheory.FourColor
