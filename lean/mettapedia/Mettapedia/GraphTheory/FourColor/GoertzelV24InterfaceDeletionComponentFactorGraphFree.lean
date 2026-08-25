import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorReindex
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorTotal

/-!
# Graph-free closure of a deletion-stable interface code

The three Boolean rows of a bounded interface code already determine a finite
primitive step relation.  This file packages its reflexive-transitive closure
without retaining any ambient vertex type.  For an exact code extracted along
an injective interface enumeration, that graph-free closure is precisely
ambient graph reachability between the named interface vertices.

The closure is natural under every bijective renaming of coordinates.  This
is the representation-independent relation that a finite-state transition
may store and replay.  No corridor, canonical enumeration, or reachable-state
bound is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceDeletionComponentFactorGraphFree

open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorReindex
open GoertzelV24InterfaceDeletionComponentFactorTotal
open SimpleGraph

/-- The finite reachability relation represented by the three rows of an
interface code. -/
def InterfaceExteriorClosure {Interface : Type*}
    (code : BoundedInterfaceExteriorCode Interface)
    (left right : Interface) : Prop :=
  Relation.ReflTransGen (InterfaceExteriorFactoredStep code) left right

/-- With an empty deletion mask, the ambient names in the total presentation
matter only through equality.  An injective enumeration therefore reduces the
total presentation to the graph-free closure. -/
theorem totalFactoredReachability_false_iff_closure_of_injective
    {N Interface : Type*}
    (code : BoundedInterfaceExteriorCode Interface)
    (interfaceVertex : Interface → N)
    (hinjective : Function.Injective interfaceVertex)
    (left right : Interface) :
    InterfaceExteriorTotalFactoredReachability code interfaceVertex
        (fun _ => false) left right ↔
      InterfaceExteriorClosure code left right := by
  unfold InterfaceExteriorTotalFactoredReachability InterfaceExteriorClosure
  constructor
  · rintro (heq | ⟨_hleft, _hright, hclosure⟩)
    · exact hinjective heq ▸ Relation.ReflTransGen.refl
    · exact hclosure.lift Subtype.val (fun _ _ hstep => hstep)
  · intro hclosure
    have hsurvives (slot : Interface) :
        survivesMask interfaceVertex (fun _ => false)
          (interfaceVertex slot) := by
      simp [survivesMask]
    refine Or.inr ⟨hsurvives left, hsurvives right, ?_⟩
    let liftSlot (slot : Interface) :
        SurvivingInterfaceSlot interfaceVertex (fun _ => false) :=
      ⟨slot, hsurvives slot⟩
    change Relation.ReflTransGen
      (fun first second :
          SurvivingInterfaceSlot interfaceVertex (fun _ => false) =>
        InterfaceExteriorFactoredStep code first.1 second.1)
      (liftSlot left) (liftSlot right)
    exact hclosure.lift liftSlot (fun _ _ hstep => hstep)

/-- An empty interface mask leaves the ambient graph unchanged. -/
@[simp]
theorem restrictedByMask_false {N Interface : Type*}
    (graph : SimpleGraph N) (interfaceVertex : Interface → N) :
    restrictedByMask graph interfaceVertex (fun _ => false) = graph := by
  rw [restrictedByMask]
  have hkeep : survivesMask interfaceVertex (fun _ => false) =
      (fun _ => True) := by
    funext vertex
    apply propext
    simp [survivesMask]
  rw [hkeep]
  exact supportRestriction_true graph

/-- Exact extraction along injective finite coordinates loses no ambient
reachability information. -/
theorem exactInterfaceExteriorCode_closure_iff_of_injective
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N)
    (hinjective : Function.Injective interfaceVertex)
    (left right : Interface) :
    InterfaceExteriorClosure
        (exactInterfaceExteriorCode graph interfaceVertex) left right ↔
      graph.Reachable (interfaceVertex left) (interfaceVertex right) := by
  rw [← totalFactoredReachability_false_iff_closure_of_injective
    (exactInterfaceExteriorCode graph interfaceVertex) interfaceVertex
      hinjective left right]
  rw [exactInterfaceExteriorCode_totalFactoredReachability_iff]
  rw [restrictedByMask_false]

/-- Pulling a code and both endpoints through a coordinate equivalence leaves
its graph-free closure unchanged. -/
theorem reindexInterfaceExteriorCode_closure_iff
    {Old New : Type*} (code : BoundedInterfaceExteriorCode Old)
    (coordinate : New ≃ Old) (left right : New) :
    InterfaceExteriorClosure
        (reindexInterfaceExteriorCode code coordinate) left right ↔
      InterfaceExteriorClosure code (coordinate left) (coordinate right) := by
  constructor
  · intro hclosure
    exact hclosure.lift coordinate (fun first second hstep =>
      (reindexInterfaceExteriorCode_factoredStep_iff code coordinate first
        second).1 hstep)
  · intro hclosure
    have hpulled := hclosure.lift coordinate.symm
      (fun first second hstep =>
        (reindexInterfaceExteriorCode_factoredStep_iff code coordinate
          (coordinate.symm first) (coordinate.symm second)).2 (by
            simpa using hstep))
    simpa [InterfaceExteriorClosure] using hpulled

end GoertzelV24InterfaceDeletionComponentFactorGraphFree

end Mettapedia.GraphTheory.FourColor
