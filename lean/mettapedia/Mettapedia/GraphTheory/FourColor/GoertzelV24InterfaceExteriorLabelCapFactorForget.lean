import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorForgetExterior
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactor

/-!
# Exterior label caps under interface forgetting

Forgetting interface coordinates turns those coordinates into finite exterior
waypoints.  A component of the smaller strict exterior is therefore assembled
from two kinds of bounded atoms:

* forgotten coordinates, each carrying one label; and
* strict-exterior components of the larger interface, carrying their stored
  capped label weights.

This file defines the graph-free atom closure and its executable capped sum.
Old exterior components may have several incidence names, so only the least
live incidence in each stored component contributes its weight.  The
construction is representation-generic and does not select a corridor or
assert that an arbitrary finite table is realizable.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceExteriorLabelCapFactorForget

open GoertzelV24FiniteBoolRelationClosure
open GoertzelV24InterfaceDeletionComponentFactorForgetExterior
open GoertzelV24InterfaceExteriorLabelCapFactor

/-- Finite atoms of a smaller strict exterior: a forgotten larger-interface
coordinate or a named component of the old strict exterior. -/
abbrev ExteriorLabelCapContractionAtom (Larger Incidence : Type*) :=
  Larger ⊕ Incidence

/-- A contraction atom is physically available.  Forgotten coordinates must
be literally present and must not alias any retained coordinate.  Incidence
atoms use the weighted factor's exact activity bit. -/
def exteriorLabelCapContractionAtomPresent
    {Larger Retained Incidence : Type*} [Fintype Retained]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger) :
    ExteriorLabelCapContractionAtom Larger Incidence → Bool
  | .inl slot =>
      code.interfacePresent slot &&
        codeSurvivesPartialRetained code.connectivity retain slot
  | .inr incidence => code.incidencePresent incidence

/-- One finite move between exterior atoms.

Forgotten coordinates use the complete primitive interface/exterior row.
An incidence is attached to its interface slot, and two incidence names are
joined exactly when the stored code says that they enter the same old strict-
exterior component.  Activity guards prevent reflexive closure from reviving
padding. -/
def exteriorLabelCapContractionAtomStep
    {Larger Retained Incidence : Type*} [Fintype Retained]
    [DecidableEq Larger]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger)
    (left right : ExteriorLabelCapContractionAtom Larger Incidence) : Bool :=
  exteriorLabelCapContractionAtomPresent code retain left &&
    exteriorLabelCapContractionAtomPresent code retain right &&
      match left, right with
      | .inl first, .inl second =>
          interfaceExteriorFactoredStepBool code.connectivity first second
      | .inl slot, .inr incidence => decide (slot = incidenceSlot incidence)
      | .inr incidence, .inl slot => decide (incidenceSlot incidence = slot)
      | .inr first, .inr second => code.incidenceConnected first second

/-- Executable reachability in the contracted strict-exterior atom graph. -/
def exteriorLabelCapContractionAtomReachable
    {Larger Retained Incidence : Type*} [Fintype Larger]
    [DecidableEq Larger] [Fintype Retained] [Fintype Incidence]
    [DecidableEq Incidence]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger)
    (source target : ExteriorLabelCapContractionAtom Larger Incidence) : Bool :=
  boolRelationReachable
    (exteriorLabelCapContractionAtomStep code retain incidenceSlot)
    source target

/-- The least live name of an old strict-exterior component.  Malformed input
tables still define a total Boolean predicate; exact source tables make the
stored relation an equivalence on live incidences. -/
def exteriorLabelCapContractionIncidenceRepresentative
    {Larger Incidence : Type*} [Fintype Incidence] [LinearOrder Incidence]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (incidence : Incidence) : Bool :=
  code.incidencePresent incidence && decide (∀ candidate,
    code.incidenceConnected candidate incidence = true →
      incidence ≤ candidate)

/-- Weight contributed by one atom.  Every forgotten coordinate contributes
one label.  An old exterior component contributes its stored weight only at
its least live incidence name. -/
def exteriorLabelCapContractionAtomWeight
    {Larger Incidence : Type*} [Fintype Incidence] [LinearOrder Incidence]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap) :
    ExteriorLabelCapContractionAtom Larger Incidence → Nat
  | .inl _ => 1
  | .inr incidence =>
      if exteriorLabelCapContractionIncidenceRepresentative code incidence then
        (code.incidenceCap incidence).val
      else
        0

/-- Atoms contributing to the contracted exterior component entered at
`source`.  Both activity and finite reachability are checked explicitly. -/
def exteriorLabelCapContractionComponentAtoms
    {Larger Retained Incidence : Type*} [Fintype Larger]
    [DecidableEq Larger] [Fintype Retained] [Fintype Incidence]
    [DecidableEq Incidence]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger)
    (source : ExteriorLabelCapContractionAtom Larger Incidence) :
    Finset (ExteriorLabelCapContractionAtom Larger Incidence) :=
  Finset.univ.filter fun atom =>
    exteriorLabelCapContractionAtomPresent code retain atom &&
      exteriorLabelCapContractionAtomReachable code retain incidenceSlot
        source atom

/-- Capped weight of the contracted exterior component entered at one atom.
This is a closed computation over the finite larger interface and incidence
families. -/
def exteriorLabelCapContractionComponentCap
    {Larger Retained Incidence : Type*} [Fintype Larger]
    [DecidableEq Larger] [Fintype Retained] [Fintype Incidence]
    [LinearOrder Incidence]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger)
    (source : ExteriorLabelCapContractionAtom Larger Incidence) : Fin (cap + 1) :=
  ⟨min
      (∑ atom ∈ exteriorLabelCapContractionComponentAtoms code retain
          incidenceSlot source,
        exteriorLabelCapContractionAtomWeight code atom)
      cap,
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- Whether a target incidence decodes to a live contraction atom. -/
def exteriorLabelCapContractionEntryPresent
    {Larger Retained Incidence TargetIncidence : Type*} [Fintype Retained]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (entry : TargetIncidence →
      Option (ExteriorLabelCapContractionAtom Larger Incidence))
    (target : TargetIncidence) : Bool :=
  match entry target with
  | none => false
  | some atom => exteriorLabelCapContractionAtomPresent code retain atom

/-- Contract a weighted interface/exterior code to a partially reindexed
target interface.  Connectivity, incidence activity, incidence connectivity,
and capped component weights are all finite computations.  Literal target
presence is supplied independently because graph support does not detect an
isolated represented coordinate. -/
def partialContractedInterfaceExteriorLabelCapCode
    {Larger Retained Incidence TargetIncidence : Type*}
    [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained] [DecidableEq Retained]
    [Fintype Incidence] [LinearOrder Incidence]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger)
    (targetPresent : Retained → Bool)
    (entry : TargetIncidence →
      Option (ExteriorLabelCapContractionAtom Larger Incidence)) :
    BoundedInterfaceExteriorLabelCapCode Retained TargetIncidence cap where
  connectivity := partialContractedInterfaceExteriorCode code.connectivity retain
  interfacePresent := targetPresent
  incidencePresent :=
    exteriorLabelCapContractionEntryPresent code retain entry
  incidenceConnected := fun first second =>
    match entry first, entry second with
    | some firstAtom, some secondAtom =>
        exteriorLabelCapContractionAtomPresent code retain firstAtom &&
          exteriorLabelCapContractionAtomPresent code retain secondAtom &&
            exteriorLabelCapContractionAtomReachable code retain incidenceSlot
              firstAtom secondAtom
    | _, _ => false
  incidenceCap := fun target =>
    match entry target with
    | none => 0
    | some atom =>
        if exteriorLabelCapContractionAtomPresent code retain atom then
          exteriorLabelCapContractionComponentCap code retain incidenceSlot atom
        else
          0

@[simp]
theorem exteriorLabelCapContractionEntryPresent_eq_true_iff
    {Larger Retained Incidence TargetIncidence : Type*} [Fintype Retained]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (entry : TargetIncidence →
      Option (ExteriorLabelCapContractionAtom Larger Incidence))
    (target : TargetIncidence) :
    exteriorLabelCapContractionEntryPresent code retain entry target = true ↔
      ∃ atom, entry target = some atom ∧
        exteriorLabelCapContractionAtomPresent code retain atom = true := by
  cases hentry : entry target with
  | none => simp [exteriorLabelCapContractionEntryPresent, hentry]
  | some atom => simp [exteriorLabelCapContractionEntryPresent, hentry]

@[simp]
theorem partialContractedInterfaceExteriorLabelCapCode_incidencePresent_iff
    {Larger Retained Incidence TargetIncidence : Type*}
    [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained] [DecidableEq Retained]
    [Fintype Incidence] [LinearOrder Incidence]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger)
    (targetPresent : Retained → Bool)
    (entry : TargetIncidence →
      Option (ExteriorLabelCapContractionAtom Larger Incidence))
    (target : TargetIncidence) :
    (partialContractedInterfaceExteriorLabelCapCode code retain incidenceSlot
      targetPresent entry).incidencePresent target = true ↔
      ∃ atom, entry target = some atom ∧
        exteriorLabelCapContractionAtomPresent code retain atom = true := by
  exact exteriorLabelCapContractionEntryPresent_eq_true_iff code retain entry
    target

@[simp]
theorem partialContractedInterfaceExteriorLabelCapCode_incidenceConnected_iff
    {Larger Retained Incidence TargetIncidence : Type*}
    [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained] [DecidableEq Retained]
    [Fintype Incidence] [LinearOrder Incidence]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger)
    (targetPresent : Retained → Bool)
    (entry : TargetIncidence →
      Option (ExteriorLabelCapContractionAtom Larger Incidence))
    (first second : TargetIncidence) :
    (partialContractedInterfaceExteriorLabelCapCode code retain incidenceSlot
      targetPresent entry).incidenceConnected first second = true ↔
      ∃ firstAtom secondAtom,
        entry first = some firstAtom ∧
        entry second = some secondAtom ∧
        exteriorLabelCapContractionAtomPresent code retain firstAtom = true ∧
        exteriorLabelCapContractionAtomPresent code retain secondAtom = true ∧
        exteriorLabelCapContractionAtomReachable code retain incidenceSlot
          firstAtom secondAtom = true := by
  cases hfirst : entry first with
  | none => simp [partialContractedInterfaceExteriorLabelCapCode, hfirst]
  | some firstAtom =>
      cases hsecond : entry second with
      | none =>
          simp [partialContractedInterfaceExteriorLabelCapCode, hfirst, hsecond]
      | some secondAtom =>
          simp [partialContractedInterfaceExteriorLabelCapCode, hfirst, hsecond,
            Bool.and_eq_true]
          tauto

@[simp]
theorem partialContractedInterfaceExteriorLabelCapCode_incidenceCap_val
    {Larger Retained Incidence TargetIncidence : Type*}
    [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained] [DecidableEq Retained]
    [Fintype Incidence] [LinearOrder Incidence]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger)
    (targetPresent : Retained → Bool)
    (entry : TargetIncidence →
      Option (ExteriorLabelCapContractionAtom Larger Incidence))
    (target : TargetIncidence) :
    ((partialContractedInterfaceExteriorLabelCapCode code retain incidenceSlot
      targetPresent entry).incidenceCap target).val =
      match entry target with
      | none => 0
      | some atom =>
          if exteriorLabelCapContractionAtomPresent code retain atom then
            (exteriorLabelCapContractionComponentCap code retain incidenceSlot
              atom).val
          else
            0 := by
  cases hentry : entry target with
  | none => simp [partialContractedInterfaceExteriorLabelCapCode, hentry]
  | some atom =>
      by_cases hpresent :
          exteriorLabelCapContractionAtomPresent code retain atom = true
      · simp [partialContractedInterfaceExteriorLabelCapCode, hentry, hpresent]
      · simp [partialContractedInterfaceExteriorLabelCapCode, hentry, hpresent]

end GoertzelV24InterfaceExteriorLabelCapFactorForget

end Mettapedia.GraphTheory.FourColor
