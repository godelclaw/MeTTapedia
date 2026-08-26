import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactorForget

/-!
# Capped weights of contracted exterior atoms

This file isolates the finite arithmetic behind a label-cap contraction.
Each contraction atom denotes a finite label support.  Forgotten coordinates
denote singleton supports; the canonical incidence representative of an old
exterior component denotes that component's stored support; nonrepresentative
incidences denote the empty support.

If the supports of the atoms in one contracted component are pairwise
disjoint, their executable capped weight is exactly the cap of the cardinality
of their union.  The statement is graph-free and can be reused by every
bounded interface presentation; a concrete geometry only has to prove that
its atom supports form the intended partition.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceExteriorLabelCapFactorForgetWeight

open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorForget

/-- Label support denoted by one contraction atom. -/
def exteriorLabelCapContractionAtomLabelSupport
    {Larger Incidence Label : Type*} [DecidableEq Label]
    [Fintype Incidence] [LinearOrder Incidence]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (largerLabel : Larger → Label)
    (incidenceSupport : Incidence → Finset Label) :
    ExteriorLabelCapContractionAtom Larger Incidence → Finset Label
  | .inl slot => {largerLabel slot}
  | .inr incidence =>
      if exteriorLabelCapContractionIncidenceRepresentative code incidence then
        incidenceSupport incidence
      else
        ∅

/-- Capping each summand before summation does not change the cap of the
sum.  This small arithmetic fact is what permits an old component to store
only its capped weight. -/
theorem min_sum_eq_min_sum_of_pointwise
    {Index : Type*} [DecidableEq Index]
    (items : Finset Index) (left right : Index → Nat) (cap : Nat)
    (hpointwise : ∀ item ∈ items,
      min (left item) cap = min (right item) cap) :
    min (∑ item ∈ items, left item) cap =
      min (∑ item ∈ items, right item) cap := by
  induction items using Finset.induction_on with
  | empty => simp
  | @insert item items hnotMem ih =>
      have hitem := hpointwise item (by simp)
      have hitems := ih (fun other hother =>
        hpointwise other (by simp [hother]))
      simp only [Finset.sum_insert hnotMem]
      omega

/-- The stored atom weight and the denoted label support agree after applying
the ambient cap. -/
theorem min_exteriorLabelCapContractionAtomWeight_eq_support
    {Larger Incidence Label : Type*} [DecidableEq Label]
    [Fintype Incidence] [LinearOrder Incidence]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (largerLabel : Larger → Label)
    (incidenceSupport : Incidence → Finset Label)
    (hincidenceCap : ∀ incidence,
      (code.incidenceCap incidence).val =
        min (incidenceSupport incidence).card cap)
    (atom : ExteriorLabelCapContractionAtom Larger Incidence) :
    min (exteriorLabelCapContractionAtomWeight code atom) cap =
      min (exteriorLabelCapContractionAtomLabelSupport code largerLabel
        incidenceSupport atom).card cap := by
  cases atom with
  | inl slot =>
      simp [exteriorLabelCapContractionAtomWeight,
        exteriorLabelCapContractionAtomLabelSupport]
  | inr incidence =>
      by_cases hrepresentative :
          exteriorLabelCapContractionIncidenceRepresentative code incidence
      · simp [exteriorLabelCapContractionAtomWeight,
          exteriorLabelCapContractionAtomLabelSupport, hrepresentative,
          hincidenceCap]
      · simp [exteriorLabelCapContractionAtomWeight,
          exteriorLabelCapContractionAtomLabelSupport, hrepresentative]

/-- A contracted component's executable cap is the cap of the union of its
pairwise-disjoint atom label supports. -/
theorem exteriorLabelCapContractionComponentCap_val_eq_biUnion
    {Larger Retained Incidence Label : Type*}
    [Fintype Larger] [DecidableEq Larger]
    [Fintype Retained] [Fintype Incidence] [LinearOrder Incidence]
    [DecidableEq Label]
    (code : BoundedInterfaceExteriorLabelCapCode Larger Incidence cap)
    (retain : Retained → Option Larger)
    (incidenceSlot : Incidence → Larger)
    (source : ExteriorLabelCapContractionAtom Larger Incidence)
    (largerLabel : Larger → Label)
    (incidenceSupport : Incidence → Finset Label)
    (hincidenceCap : ∀ incidence,
      (code.incidenceCap incidence).val =
        min (incidenceSupport incidence).card cap)
    (hdisjoint :
      (↑(exteriorLabelCapContractionComponentAtoms code retain incidenceSlot
          source) : Set (ExteriorLabelCapContractionAtom Larger Incidence)
        ).PairwiseDisjoint
        (exteriorLabelCapContractionAtomLabelSupport code largerLabel
          incidenceSupport)) :
    (exteriorLabelCapContractionComponentCap code retain incidenceSlot source
      ).val =
      min ((exteriorLabelCapContractionComponentAtoms code retain incidenceSlot
        source).biUnion
          (exteriorLabelCapContractionAtomLabelSupport code largerLabel
            incidenceSupport)).card cap := by
  change min
      (∑ atom ∈ exteriorLabelCapContractionComponentAtoms code retain
        incidenceSlot source,
        exteriorLabelCapContractionAtomWeight code atom) cap = _
  rw [Finset.card_biUnion hdisjoint]
  exact min_sum_eq_min_sum_of_pointwise
    (exteriorLabelCapContractionComponentAtoms code retain incidenceSlot source)
    (exteriorLabelCapContractionAtomWeight code)
    (fun atom =>
      (exteriorLabelCapContractionAtomLabelSupport code largerLabel
        incidenceSupport atom).card)
    cap (fun atom _ =>
      min_exteriorLabelCapContractionAtomWeight_eq_support code largerLabel
        incidenceSupport hincidenceCap atom)

end GoertzelV24InterfaceExteriorLabelCapFactorForgetWeight

end Mettapedia.GraphTheory.FourColor
