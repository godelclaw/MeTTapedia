import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactor

/-!
# Label weights on a deletion-stable interface/exterior factor

The polynomial interface/exterior factor reconstructs connectivity after any
mask on a bounded interface.  A capped face-length update needs one additional
kind of information: the capped number of distinct labels in every exterior
component which can be entered from the interface.

This file adds that information without enumerating masks.  Each interface
slot is supplied with a fixed finite family of possible exterior incidences.
The code records which incidences are live, which enter the same strictly
exterior component, and the cap at five of that component's distinct labels.
The construction is graph-generic; the facial specialization uses the two
directions of the face permutation as its incidence family.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceExteriorLabelCapFactor

open GoertzelV24InterfaceDeletionComponentFactor
open SimpleGraph

/-- A deletion-stable interface factor together with exact exterior-component
label weights.  `interfacePresent` is separate from graph support because an
isolated represented vertex can be present in the underlying regional object.
-/
@[ext]
structure BoundedInterfaceExteriorLabelCapCode
    (Interface Incidence : Type*) (cap : Nat := 5) where
  connectivity : BoundedInterfaceExteriorCode Interface
  interfacePresent : Interface → Bool
  incidencePresent : Incidence → Bool
  incidenceConnected : Incidence → Incidence → Bool
  incidenceCap : Incidence → Fin (cap + 1)

private def boundedInterfaceExteriorLabelCapCodeEquiv
    (Interface Incidence : Type*) (cap : Nat) :
    BoundedInterfaceExteriorLabelCapCode Interface Incidence cap ≃
      BoundedInterfaceExteriorCode Interface ×
        (Interface → Bool) × (Incidence → Bool) ×
          (Incidence → Incidence → Bool) × (Incidence → Fin (cap + 1)) where
  toFun code :=
    ⟨code.connectivity, code.interfacePresent, code.incidencePresent,
      code.incidenceConnected, code.incidenceCap⟩
  invFun data :=
    ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1, data.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance {Interface Incidence : Type*} {cap : Nat} :
    DecidableEq
      (BoundedInterfaceExteriorLabelCapCode Interface Incidence cap) :=
  Classical.decEq _

noncomputable instance {Interface Incidence : Type*}
    [Fintype Interface] [Fintype Incidence] {cap : Nat} :
    Fintype (BoundedInterfaceExteriorLabelCapCode Interface Incidence cap) := by
  letI : Fintype (Interface → Bool) := Fintype.ofFinite _
  letI : Fintype (Incidence → Bool) := Fintype.ofFinite _
  letI : Fintype (Incidence → Incidence → Bool) := Fintype.ofFinite _
  letI : Fintype (Incidence → Fin (cap + 1)) := Fintype.ofFinite _
  exact Fintype.ofEquiv _
    (boundedInterfaceExteriorLabelCapCodeEquiv Interface Incidence cap).symm

/-- One possible entry from a bounded interface into the ambient graph. -/
def ExteriorIncidencePresent {N Interface Incidence : Type*}
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (incidence : Incidence) : Prop :=
  OutsideInterface interfaceVertex (incidenceVertex incidence) ∧
    graph.Adj (interfaceVertex (incidenceSlot incidence))
      (incidenceVertex incidence)

/-- Distinct labels in the strictly exterior component entered by one
incidence.  A non-live incidence denotes the empty support. -/
noncomputable def exteriorIncidenceLabelSupport
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (incidence : Incidence) : Finset Label := by
  classical
  if hpresent : ExteriorIncidencePresent graph interfaceVertex incidenceSlot
      incidenceVertex incidence then
    exact ((Finset.univ : Finset N).filter fun vertex =>
      (exteriorGraph graph interfaceVertex).Reachable
        (incidenceVertex incidence) vertex).image label
  else
    exact ∅

theorem mem_exteriorIncidenceLabelSupport_iff
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (incidence : Incidence) (value : Label) :
    value ∈ exteriorIncidenceLabelSupport graph interfaceVertex incidenceSlot
        incidenceVertex label incidence ↔
      ExteriorIncidencePresent graph interfaceVertex incidenceSlot
          incidenceVertex incidence ∧
        ∃ vertex : N,
          (exteriorGraph graph interfaceVertex).Reachable
              (incidenceVertex incidence) vertex ∧
            label vertex = value := by
  classical
  by_cases hpresent : ExteriorIncidencePresent graph interfaceVertex
      incidenceSlot incidenceVertex incidence
  · simp [exteriorIncidenceLabelSupport, hpresent]
  · simp [exteriorIncidenceLabelSupport, hpresent]

/-- Canonical exact weighted code extracted from a graph, a represented
interface, and a finite incidence family. -/
noncomputable def exactInterfaceExteriorLabelCapCode
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (present : N → Prop) [DecidablePred present]
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (cap : Nat := 5) :
    BoundedInterfaceExteriorLabelCapCode Interface Incidence cap where
  connectivity := exactInterfaceExteriorCode graph interfaceVertex
  interfacePresent slot := decide (present (interfaceVertex slot))
  incidencePresent incidence := by
    classical
    exact decide
      (ExteriorIncidencePresent graph interfaceVertex incidenceSlot
        incidenceVertex incidence)
  incidenceConnected first second := by
    classical
    exact decide
      (ExteriorIncidencePresent graph interfaceVertex incidenceSlot
          incidenceVertex first ∧
        ExteriorIncidencePresent graph interfaceVertex incidenceSlot
          incidenceVertex second ∧
        (exteriorGraph graph interfaceVertex).Reachable
          (incidenceVertex first) (incidenceVertex second))
  incidenceCap incidence :=
    ⟨min (exteriorIncidenceLabelSupport graph interfaceVertex incidenceSlot
        incidenceVertex label incidence).card cap,
      Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

@[simp] theorem exactInterfaceExteriorLabelCapCode_connectivity
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (present : N → Prop) [DecidablePred present]
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (cap : Nat := 5) :
    (exactInterfaceExteriorLabelCapCode graph interfaceVertex present
      incidenceSlot incidenceVertex label cap).connectivity =
        exactInterfaceExteriorCode graph interfaceVertex :=
  rfl

@[simp] theorem exactInterfaceExteriorLabelCapCode_interfacePresent_iff
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (present : N → Prop) [DecidablePred present]
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (slot : Interface) (cap : Nat := 5) :
    (exactInterfaceExteriorLabelCapCode graph interfaceVertex present
      incidenceSlot incidenceVertex label cap).interfacePresent slot = true ↔
        present (interfaceVertex slot) := by
  simp [exactInterfaceExteriorLabelCapCode]

@[simp] theorem exactInterfaceExteriorLabelCapCode_incidencePresent_iff
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (present : N → Prop) [DecidablePred present]
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (incidence : Incidence) (cap : Nat := 5) :
    (exactInterfaceExteriorLabelCapCode graph interfaceVertex present
      incidenceSlot incidenceVertex label cap).incidencePresent incidence = true ↔
        ExteriorIncidencePresent graph interfaceVertex incidenceSlot
          incidenceVertex incidence := by
  simp [exactInterfaceExteriorLabelCapCode]

@[simp] theorem exactInterfaceExteriorLabelCapCode_incidenceConnected_iff
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (present : N → Prop) [DecidablePred present]
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (first second : Incidence) (cap : Nat := 5) :
    (exactInterfaceExteriorLabelCapCode graph interfaceVertex present
      incidenceSlot incidenceVertex label cap).incidenceConnected first second =
        true ↔
      ExteriorIncidencePresent graph interfaceVertex incidenceSlot
          incidenceVertex first ∧
        ExteriorIncidencePresent graph interfaceVertex incidenceSlot
          incidenceVertex second ∧
        (exteriorGraph graph interfaceVertex).Reachable
          (incidenceVertex first) (incidenceVertex second) := by
  simp [exactInterfaceExteriorLabelCapCode]

@[simp] theorem exactInterfaceExteriorLabelCapCode_incidenceCap_val
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (present : N → Prop) [DecidablePred present]
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (incidence : Incidence) (cap : Nat := 5) :
    ((exactInterfaceExteriorLabelCapCode graph interfaceVertex present
      incidenceSlot incidenceVertex label cap).incidenceCap incidence).val =
        min (exteriorIncidenceLabelSupport graph interfaceVertex incidenceSlot
          incidenceVertex label incidence).card cap :=
  rfl

/-- Two incidence coordinates entering one exterior component carry the same
label support and therefore the same capped weight. -/
theorem exteriorIncidenceLabelSupport_eq_of_reachable
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    {first second : Incidence}
    (hfirst : ExteriorIncidencePresent graph interfaceVertex incidenceSlot
      incidenceVertex first)
    (hsecond : ExteriorIncidencePresent graph interfaceVertex incidenceSlot
      incidenceVertex second)
    (hreachable : (exteriorGraph graph interfaceVertex).Reachable
      (incidenceVertex first) (incidenceVertex second)) :
    exteriorIncidenceLabelSupport graph interfaceVertex incidenceSlot
        incidenceVertex label first =
      exteriorIncidenceLabelSupport graph interfaceVertex incidenceSlot
        incidenceVertex label second := by
  classical
  ext value
  rw [mem_exteriorIncidenceLabelSupport_iff,
    mem_exteriorIncidenceLabelSupport_iff]
  constructor
  · rintro ⟨_, vertex, hfirstVertex, rfl⟩
    exact ⟨hsecond, vertex, hreachable.symm.trans hfirstVertex, rfl⟩
  · rintro ⟨_, vertex, hsecondVertex, rfl⟩
    exact ⟨hfirst, vertex, hreachable.trans hsecondVertex, rfl⟩

theorem exactInterfaceExteriorLabelCapCode_incidenceCap_eq_of_connected
    {N Interface Incidence Label : Type*}
    [Fintype N] [DecidableEq N] [Fintype Label] [DecidableEq Label]
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (present : N → Prop) [DecidablePred present]
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (cap : Nat := 5)
    {first second : Incidence}
    (hconnected :
      (exactInterfaceExteriorLabelCapCode graph interfaceVertex present
        incidenceSlot incidenceVertex label cap).incidenceConnected first second =
          true) :
    (exactInterfaceExteriorLabelCapCode graph interfaceVertex present
        incidenceSlot incidenceVertex label cap).incidenceCap first =
      (exactInterfaceExteriorLabelCapCode graph interfaceVertex present
        incidenceSlot incidenceVertex label cap).incidenceCap second := by
  have hdata :=
    (exactInterfaceExteriorLabelCapCode_incidenceConnected_iff graph
      interfaceVertex present incidenceSlot incidenceVertex label first
      second cap).1 hconnected
  apply Fin.ext
  simp only [exactInterfaceExteriorLabelCapCode_incidenceCap_val]
  rw [exteriorIncidenceLabelSupport_eq_of_reachable graph interfaceVertex
    incidenceSlot incidenceVertex label hdata.1 hdata.2.1 hdata.2.2]

/-- A bounded family of weighted factors sharing one literal carrier.  The
incidence family is allowed to depend on the actual carrier size. -/
structure BoundedInterfaceExteriorLabelCapFamilyCode
    (bound : Nat) (Family : Type*) (cap : Nat := 5) where
  vertexCount : Fin (bound + 1)
  code : Family →
    BoundedInterfaceExteriorLabelCapCode
      (Fin vertexCount.val) (Fin vertexCount.val × Bool) cap

private def boundedInterfaceExteriorLabelCapFamilyCodeEquiv
    (bound : Nat) (Family : Type*) (cap : Nat) :
    BoundedInterfaceExteriorLabelCapFamilyCode bound Family cap ≃
      Σ vertexCount : Fin (bound + 1), Family →
        BoundedInterfaceExteriorLabelCapCode
          (Fin vertexCount.val) (Fin vertexCount.val × Bool) cap where
  toFun code := ⟨code.vertexCount, code.code⟩
  invFun code := ⟨code.1, code.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance {bound : Nat} {Family : Type*} {cap : Nat} :
    DecidableEq
      (BoundedInterfaceExteriorLabelCapFamilyCode bound Family cap) :=
  Classical.decEq _

noncomputable instance {bound : Nat} {Family : Type*} [Fintype Family]
    {cap : Nat} :
    Fintype (BoundedInterfaceExteriorLabelCapFamilyCode bound Family cap) := by
  letI (vertexCount : Fin (bound + 1)) : Fintype
      (Family → BoundedInterfaceExteriorLabelCapCode
        (Fin vertexCount.val) (Fin vertexCount.val × Bool) cap) :=
    Fintype.ofFinite _
  exact Fintype.ofEquiv _
    (boundedInterfaceExteriorLabelCapFamilyCodeEquiv bound Family cap).symm

end GoertzelV24InterfaceExteriorLabelCapFactor

end Mettapedia.GraphTheory.FourColor
