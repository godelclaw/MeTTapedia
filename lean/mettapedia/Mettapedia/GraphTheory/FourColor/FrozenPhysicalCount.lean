import Mettapedia.GraphTheory.FourColor.FrozenCountSupport

/-!
# Frozen joint support of a literal sewn rotation system

Observations name darts of the input tangles. The physical predicate reads
their colours on the actual computed edge orbits of `composeRotationSystem`.
Both directions of the Count bridge preserve every such observation,
including seam darts and absent labels. Hence joint-support replacement
preserves each prescribed-colour problem, not just ordinary colourability.
-/

namespace Mettapedia.GraphTheory.FourColor.FrozenPhysicalCount

open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PhysicalClosedCountBridge GoertzelV24CompositeSeamMultigraph
open GoertzelV24OpenTangleComposition GoertzelV24RotationSpliceConstructor
open FrozenCountSupport

universe u v
variable {V W I J L R : Type u} {M : Type v}

def leftPortDart : I ⊕ L → I ⊕ (EmptyPort.{u} ⊕ L)
  | Sum.inl d => Sum.inl d
  | Sum.inr d => Sum.inr (Sum.inr d)

def rightPortDart (matching : L ≃ R) : J ⊕ R → J ⊕ (L ⊕ EmptyPort.{u})
  | Sum.inl d => Sum.inl d
  | Sum.inr d => Sum.inr (Sum.inl (matching.symm d))

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- The colours are read on actual physical edges, at the named source darts. -/
def PhysicalAccepts (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (lo : M → Option (I ⊕ L)) (ro : M → Option (J ⊕ R))
    (value : M → Color) : Prop :=
  ∃ c : (left.composeRotationSystem right matching).EdgeColoring Color,
    (left.composeRotationSystem right matching).IsTaitEdgeColoring c ∧
    Observes (fun d => c ((left.composeRotationSystem right matching).edgeOf
      (composeDartEquiv (Sum.inl d)))) lo value ∧
    Observes (fun d => c ((left.composeRotationSystem right matching).edgeOf
      (composeDartEquiv (Sum.inr d)))) ro value

theorem physical_read_left (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R)
    (c : Col (series (leftClosedPortTangle left) (rightClosedPortTangle right matching))
      (Sum.elim PEmpty.elim PEmpty.elim)) (d : I ⊕ L) :
    physicalEdgeColoring left right matching c
      ((left.composeRotationSystem right matching).edgeOf (composeDartEquiv (Sum.inl d))) =
      (restrict₁ (leftClosedPortTangle left) (rightClosedPortTangle right matching) c.val).color
        (leftPortDart d) := by
  change (compositeDarts left right matching).descendedEdgeColor
    (physicalDartColor left right matching c)
    ((compositeDarts left right matching).edgeOf (composeDartEquiv (Sum.inl d))) = _
  rw [RewiredDartSystem.descendedEdgeColor_edgeOf _ _ (physicalDartColor_alpha left right matching c)]
  cases d <;> rfl

theorem physical_read_right (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R)
    (c : Col (series (leftClosedPortTangle left) (rightClosedPortTangle right matching))
      (Sum.elim PEmpty.elim PEmpty.elim)) (d : J ⊕ R) :
    physicalEdgeColoring left right matching c
      ((left.composeRotationSystem right matching).edgeOf (composeDartEquiv (Sum.inr d))) =
      (restrict₂ (leftClosedPortTangle left) (rightClosedPortTangle right matching) c.val).color
        (rightPortDart matching d) := by
  change (compositeDarts left right matching).descendedEdgeColor
    (physicalDartColor left right matching c)
    ((compositeDarts left right matching).edgeOf (composeDartEquiv (Sum.inr d))) = _
  rw [RewiredDartSystem.descendedEdgeColor_edgeOf _ _ (physicalDartColor_alpha left right matching c)]
  cases d <;> rfl

theorem count_read_left (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (c : (compositeRS left right matching).EdgeColoring Color)
    (hc : (compositeRS left right matching).IsTaitEdgeColoring c) (d : I ⊕ L) :
    (restrict₁ (leftClosedPortTangle left) (rightClosedPortTangle right matching)
      (closedColOfPhysical left right matching c hc).val).color (leftPortDart d) =
      c ((left.composeRotationSystem right matching).edgeOf (composeDartEquiv (Sum.inl d))) := by
  cases d <;> rfl

theorem count_read_right (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (c : (compositeRS left right matching).EdgeColoring Color)
    (hc : (compositeRS left right matching).IsTaitEdgeColoring c) (d : J ⊕ R) :
    (restrict₂ (leftClosedPortTangle left) (rightClosedPortTangle right matching)
      (closedColOfPhysical left right matching c hc).val).color (rightPortDart matching d) =
      c ((left.composeRotationSystem right matching).edgeOf (composeDartEquiv (Sum.inr d))) := by
  cases d with
  | inl d => rfl
  | inr d =>
    change c ((compositeDarts left right matching).edgeOf
      (Sum.inr (Sum.inr (matching (matching.symm d))))) = _
    rw [Equiv.apply_symm_apply]
    rfl

/-- The physical/semantic bridge preserves every prescribed observation. -/
theorem physicalAccepts_iff (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (lo : M → Option (I ⊕ L)) (ro : M → Option (J ⊕ R))
    (value : M → Color) :
    PhysicalAccepts left right matching lo ro value ↔
      ClosedAccepts (leftClosedPortTangle left) (rightClosedPortTangle right matching)
        (fun m => (lo m).map leftPortDart) (fun m => (ro m).map (rightPortDart matching)) value := by
  constructor
  · rintro ⟨c, hc, hl, hr⟩
    refine ⟨closedColOfPhysical left right matching c hc, ?_, ?_⟩
    · rw [observes_map_iff]
      intro m d hd
      exact (count_read_left left right matching c hc d).trans (hl m d hd)
    · rw [observes_map_iff]
      intro m d hd
      exact (count_read_right left right matching c hc d).trans (hr m d hd)
  · rintro ⟨c, hl, hr⟩
    rw [observes_map_iff] at hl hr
    refine ⟨physicalEdgeColoring left right matching c,
      physicalEdgeColoring_isTait left right matching c, ?_, ?_⟩
    · intro m d hd
      exact (physical_read_left left right matching c d).trans (hl m d hd)
    · intro m d hd
      exact (physical_read_right left right matching c d).trans (hr m d hd)

variable {W' J' R' : Type u}
  [Fintype W'] [DecidableEq W'] [Fintype J'] [DecidableEq J']
  [Fintype R'] [DecidableEq R']

/-- Same joint support in the common seam coordinates preserves the actual
physical prescribed-colour problem under replacement. -/
theorem physicalAccepts_iff_of_joint_eq
    (left : OpenTangleData V I L) (old : OpenTangleData W J R)
    (new : OpenTangleData W' J' R') (oldMatching : L ≃ R) (newMatching : L ≃ R')
    (lo : M → Option (I ⊕ L)) (oo : M → Option (J ⊕ R)) (no : M → Option (J' ⊕ R'))
    (heq : innerJointSupport (rightClosedPortTangle old oldMatching)
      (fun m => (oo m).map (rightPortDart oldMatching)) =
      innerJointSupport (rightClosedPortTangle new newMatching)
      (fun m => (no m).map (rightPortDart newMatching))) (value : M → Color) :
    PhysicalAccepts left old oldMatching lo oo value ↔
      PhysicalAccepts left new newMatching lo no value := by
  rw [physicalAccepts_iff, physicalAccepts_iff]
  exact closedAccepts_iff_of_joint_eq _ _ _ _ _ _ heq value

theorem not_physicalAccepts_of_joint_eq
    (left : OpenTangleData V I L) (old : OpenTangleData W J R)
    (new : OpenTangleData W' J' R') (oldMatching : L ≃ R) (newMatching : L ≃ R')
    (lo : M → Option (I ⊕ L)) (oo : M → Option (J ⊕ R)) (no : M → Option (J' ⊕ R'))
    (heq : innerJointSupport (rightClosedPortTangle old oldMatching)
      (fun m => (oo m).map (rightPortDart oldMatching)) =
      innerJointSupport (rightClosedPortTangle new newMatching)
      (fun m => (no m).map (rightPortDart newMatching))) (value : M → Color)
    (hzero : ¬ PhysicalAccepts left old oldMatching lo oo value) :
    ¬ PhysicalAccepts left new newMatching lo no value :=
  fun h => hzero ((physicalAccepts_iff_of_joint_eq left old new oldMatching newMatching lo oo no heq value).mpr h)

end Mettapedia.GraphTheory.FourColor.FrozenPhysicalCount
