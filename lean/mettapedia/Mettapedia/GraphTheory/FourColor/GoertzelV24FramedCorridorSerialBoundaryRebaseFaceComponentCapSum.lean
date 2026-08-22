import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceComponentRepresentatives

/-!
# Finite predecessor face-cap sums for a serial rebase

Canonical representatives remove duplicate occurrence coordinates from the
predecessor face state.  This file turns that selector into the finite capped
sum seen from one successor switch occurrence: retain exactly the active old
components connected to the output through the old, local, or seam factors,
add each stored component weight once, and cap the result at five.

The decoder is graph-free after a semantic finite code is supplied.  Every
active predecessor occurrence connected to the output contributes through its
unique representative with the same stored cap.  The remaining geometric
adequacy theorem must identify this finite sum with the literal old-prefix
slice of the successor fragment; no reachable closure or numerical threshold
is claimed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

namespace BoundedCappedSerialBoundaryRebaseFaceStepCode

/-- Canonical active old components connected to one successor occurrence by
the finite rebase closure. -/
noncomputable def contributingOldComponentRepresentatives
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (output : Fin code.localCode.vertexCount.val) :
    Finset (Fin code.localCode.vertexCount.val) := by
  classical
  exact (code.oldComponentRepresentatives semantic).filter fun representative =>
    Relation.ReflTransGen
      (boundedSerialBoundaryRebaseFaceComponentStep
        code.toBoundedSerialBoundaryRebaseFaceStepCode) output representative

@[simp]
theorem mem_contributingOldComponentRepresentatives_iff
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (output representative : Fin code.localCode.vertexCount.val) :
    representative ∈
        code.contributingOldComponentRepresentatives semantic output ↔
      representative ∈ code.oldComponentRepresentatives semantic ∧
        Relation.ReflTransGen
          (boundedSerialBoundaryRebaseFaceComponentStep
            code.toBoundedSerialBoundaryRebaseFaceStepCode) output
            representative := by
  classical
  simp [contributingOldComponentRepresentatives]

/-- The predecessor contribution decoded from the finite rebase state.  Each
old component is counted at its canonical representative and the sum is capped
at the manuscript threshold five. -/
noncomputable def oldComponentCapSumAt
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (output : Fin code.localCode.vertexCount.val) : Nat :=
  min
    (∑ representative ∈
        code.contributingOldComponentRepresentatives semantic output,
      (code.oldComponentCap representative).val)
    5

theorem oldComponentCapSumAt_le_five
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (output : Fin code.localCode.vertexCount.val) :
    code.oldComponentCapSumAt semantic output ≤ 5 :=
  Nat.min_le_right _ _

/-- An active predecessor occurrence connected to the output contributes via
its canonical representative. -/
theorem oldComponentRepresentative_mem_contributing_of_active_of_reachable
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (output coordinate : Fin code.localCode.vertexCount.val)
    (hactive : code.oldActive coordinate = true)
    (hreachable : Relation.ReflTransGen
      (boundedSerialBoundaryRebaseFaceComponentStep
        code.toBoundedSerialBoundaryRebaseFaceStepCode) output coordinate) :
    code.oldComponentRepresentative semantic coordinate ∈
      code.contributingOldComponentRepresentatives semantic output := by
  rw [code.mem_contributingOldComponentRepresentatives_iff semantic]
  refine ⟨code.oldComponentRepresentative_mem_representatives semantic
    coordinate hactive, ?_⟩
  apply hreachable.tail
  exact Or.inl
    ((code.mem_oldComponentPartition_part_iff semantic coordinate
      (code.oldComponentRepresentative semantic coordinate)).1
        (code.oldComponentRepresentative_mem_part semantic coordinate))

/-- The contribution selected from an occurrence uses exactly that
occurrence's stored cap, independently of which occurrence named its old
component. -/
theorem oldComponentCap_of_contributingRepresentative
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (output coordinate : Fin code.localCode.vertexCount.val)
    (hactive : code.oldActive coordinate = true)
    (hreachable : Relation.ReflTransGen
      (boundedSerialBoundaryRebaseFaceComponentStep
        code.toBoundedSerialBoundaryRebaseFaceStepCode) output coordinate) :
    code.oldComponentCap
        (code.oldComponentRepresentative semantic coordinate) =
      code.oldComponentCap coordinate := by
  have _ := code.oldComponentRepresentative_mem_contributing_of_active_of_reachable
    semantic output coordinate hactive hreachable
  exact code.oldComponentCap_representative semantic coordinate

/-- Any selected representative related to a contributing occurrence is the
same canonical representative; hence no predecessor component can enter the
finite sum twice under two occurrence names. -/
theorem contributingRepresentative_unique
    (code : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (semantic : code.IsComponentSemantic)
    (output : Fin code.localCode.vertexCount.val)
    {representative coordinate : Fin code.localCode.vertexCount.val}
    (hrepresentative : representative ∈
      code.contributingOldComponentRepresentatives semantic output)
    (hsame : code.oldComponent representative coordinate = true) :
    representative = code.oldComponentRepresentative semantic coordinate := by
  exact code.eq_oldComponentRepresentative_of_mem_of_same semantic
    ((code.mem_contributingOldComponentRepresentatives_iff semantic output
      representative).1 hrepresentative).1 hsame

end BoundedCappedSerialBoundaryRebaseFaceStepCode

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
