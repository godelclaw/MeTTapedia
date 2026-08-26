import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorMaskUpdate
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactor

/-!
# Masking a weighted interface/exterior factor

Deleting vertices represented by an injective finite interface leaves the
strict exterior unchanged.  The connectivity factor already has an exact
row-wise mask operation.  This file lifts that operation to exterior-label
caps: activity and incidences at deleted coordinates are zeroed, while every
surviving exterior component and its capped label weight are retained.

The construction is graph-generic.  In the facial application, incidences are
the two oriented face-neighbours attached to each represented dart.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceExteriorLabelCapFactorMaskUpdate

open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorMaskUpdate
open GoertzelV24InterfaceExteriorLabelCapFactor
open SimpleGraph

noncomputable section

/-- Zero every support-sensitive row at a removed interface coordinate.
Strict-exterior connectivity and weights survive unchanged at retained
incidences. -/
def maskInterfaceExteriorLabelCapCode
    {Interface Incidence : Type*} {cap : Nat}
    (code : BoundedInterfaceExteriorLabelCapCode Interface Incidence cap)
    (incidenceSlot : Incidence → Interface)
    (removed : Interface → Bool) :
    BoundedInterfaceExteriorLabelCapCode Interface Incidence cap where
  connectivity := maskInterfaceExteriorCode code.connectivity removed
  interfacePresent slot := (!removed slot) && code.interfacePresent slot
  incidencePresent incidence :=
    (!removed (incidenceSlot incidence)) && code.incidencePresent incidence
  incidenceConnected first second :=
    (!removed (incidenceSlot first)) &&
      (!removed (incidenceSlot second)) &&
        code.incidenceConnected first second
  incidenceCap incidence :=
    if removed (incidenceSlot incidence) then 0 else code.incidenceCap incidence

/-- A represented incidence survives an injective interface mask exactly when
its interface endpoint survives and the original incidence was live. -/
theorem exteriorIncidencePresent_restrictedByMask_iff
    {N Interface Incidence : Type*}
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (hinjective : Function.Injective interfaceVertex)
    (removed : Interface → Bool)
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (incidence : Incidence) :
    ExteriorIncidencePresent
        (restrictedByMask graph interfaceVertex removed) interfaceVertex
        incidenceSlot incidenceVertex incidence ↔
      removed (incidenceSlot incidence) = false ∧
        ExteriorIncidencePresent graph interfaceVertex incidenceSlot
          incidenceVertex incidence := by
  unfold ExteriorIncidencePresent
  constructor
  · rintro ⟨houtside, hadj⟩
    have hsurvives :=
      (restrictedByMask_adj_interface_outside_iff graph interfaceVertex
        hinjective removed (incidenceSlot incidence) houtside).1 hadj
    exact ⟨hsurvives.1, houtside, hsurvives.2⟩
  · rintro ⟨hretained, houtside, hadj⟩
    exact ⟨houtside,
      (restrictedByMask_adj_interface_outside_iff graph interfaceVertex
        hinjective removed (incidenceSlot incidence) houtside).2
          ⟨hretained, hadj⟩⟩

/-- The label support entered by a retained incidence is unchanged by an
interface mask; a deleted incidence enters the empty support. -/
theorem exteriorIncidenceLabelSupport_restrictedByMask_eq
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (hinjective : Function.Injective interfaceVertex)
    (removed : Interface → Bool)
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (incidence : Incidence) :
    exteriorIncidenceLabelSupport
        (restrictedByMask graph interfaceVertex removed) interfaceVertex
        incidenceSlot incidenceVertex label incidence =
      if removed (incidenceSlot incidence) then ∅ else
        exteriorIncidenceLabelSupport graph interfaceVertex incidenceSlot
          incidenceVertex label incidence := by
  classical
  ext value
  rw [mem_exteriorIncidenceLabelSupport_iff]
  cases hremoved : removed (incidenceSlot incidence)
  · simp only [Bool.false_eq_true, if_false]
    rw [mem_exteriorIncidenceLabelSupport_iff,
      exteriorIncidencePresent_restrictedByMask_iff graph interfaceVertex
        hinjective removed incidenceSlot incidenceVertex incidence,
      exteriorGraph_restrictedByMask_eq graph interfaceVertex removed]
    simp [hremoved]
  · rw [exteriorIncidencePresent_restrictedByMask_iff graph interfaceVertex
      hinjective removed incidenceSlot incidenceVertex incidence]
    simp [hremoved]

/-- Canonical exact weighted code of the masked graph.  This wrapper selects
the classical decision procedure for the ambient survival predicate; the
resulting finite code is independent of that proof-level choice. -/
noncomputable def exactRestrictedInterfaceExteriorLabelCapCode
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (removed : Interface → Bool) (present : N → Prop)
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (cap : Nat := 5) :
    BoundedInterfaceExteriorLabelCapCode Interface Incidence cap := by
  classical
  exact exactInterfaceExteriorLabelCapCode
    (restrictedByMask graph interfaceVertex removed) interfaceVertex
    (fun vertex ↦ present vertex ∧
      survivesMask interfaceVertex removed vertex)
    incidenceSlot incidenceVertex label cap

/-- Crown exactness theorem for masking a weighted interface/exterior code.
The target presence predicate is the old literal presence restricted to the
surviving ambient vertices. -/
theorem maskInterfaceExteriorLabelCapCode_exact_code_eq
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (hinjective : Function.Injective interfaceVertex)
    (removed : Interface → Bool)
    (present : N → Prop) [DecidablePred present]
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (cap : Nat := 5) :
    maskInterfaceExteriorLabelCapCode
        (exactInterfaceExteriorLabelCapCode graph interfaceVertex present
          incidenceSlot incidenceVertex label cap)
        incidenceSlot removed =
      exactRestrictedInterfaceExteriorLabelCapCode graph interfaceVertex
        removed present incidenceSlot incidenceVertex label cap := by
  classical
  unfold exactRestrictedInterfaceExteriorLabelCapCode
  apply BoundedInterfaceExteriorLabelCapCode.ext
  · exact maskInterfaceExteriorCode_exact_code_eq graph interfaceVertex
      hinjective removed
  · funext slot
    apply Bool.eq_iff_iff.mpr
    simp only [maskInterfaceExteriorLabelCapCode,
      exactInterfaceExteriorLabelCapCode, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_true_eq]
    rw [survivesMask_interfaceVertex_iff interfaceVertex hinjective removed slot]
    tauto
  · funext incidence
    apply Bool.eq_iff_iff.mpr
    simp only [maskInterfaceExteriorLabelCapCode,
      exactInterfaceExteriorLabelCapCode, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_true_eq]
    exact (exteriorIncidencePresent_restrictedByMask_iff graph interfaceVertex
      hinjective removed incidenceSlot incidenceVertex incidence).symm
  · funext first second
    apply Bool.eq_iff_iff.mpr
    simp only [maskInterfaceExteriorLabelCapCode,
      exactInterfaceExteriorLabelCapCode, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_true_eq]
    rw [exteriorIncidencePresent_restrictedByMask_iff graph interfaceVertex
        hinjective removed incidenceSlot incidenceVertex first,
      exteriorIncidencePresent_restrictedByMask_iff graph interfaceVertex
        hinjective removed incidenceSlot incidenceVertex second,
      exteriorGraph_restrictedByMask_eq graph interfaceVertex removed]
    tauto
  · funext incidence
    apply Fin.ext
    simp only [maskInterfaceExteriorLabelCapCode,
      exactInterfaceExteriorLabelCapCode]
    rw [exteriorIncidenceLabelSupport_restrictedByMask_eq graph interfaceVertex
      hinjective removed incidenceSlot incidenceVertex label incidence]
    cases removed (incidenceSlot incidence) <;> simp

end

end GoertzelV24InterfaceExteriorLabelCapFactorMaskUpdate

end Mettapedia.GraphTheory.FourColor
