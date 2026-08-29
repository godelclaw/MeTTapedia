import KrennX5OrbitWitnessCorrect

/-!
The official semantic connector for the
`X = {01,02,03,04,15}` normalization census.

It composes three independently checked facts:

1. every one of the `6^5 = 7776` labelled channel choices is carried by the
   exact vertex/colour symmetry to one of 336 representatives;
2. that symmetry preserves official `EqSystemN` and transports the selected
   channels literally;
3. every representative has a checked integer gauge right inverse, hence its
   five live channels can simultaneously be sent to one without roots.
-/

namespace Krenn.X5NormalizationConnector

open MonochromaticQuantumGraph
open Krenn.X5Symmetry
open Krenn.X5OrbitWitness
open Krenn.X5GaugeNormalizationData
open Krenn.GaugeNormalization

def encodeChoiceValue (choice : CaseChoice) : Nat :=
  1296 * (choice 0).val + 216 * (choice 1).val +
    36 * (choice 2).val + 6 * (choice 3).val + (choice 4).val

def encodeChoice (choice : CaseChoice) : Fin 7776 :=
  ⟨encodeChoiceValue choice, by
    unfold encodeChoiceValue
    have h0 := (choice 0).isLt
    have h1 := (choice 1).isLt
    have h2 := (choice 2).isLt
    have h3 := (choice 3).isLt
    have h4 := (choice 4).isLt
    omega⟩

theorem labelledCaseChoice_encode (choice : CaseChoice) :
    labelledCaseChoice (encodeChoice choice) = choice := by
  funext slot
  fin_cases slot <;>
    apply Fin.ext <;>
    simp [labelledCaseChoice, encodeChoice, encodeChoiceValue,
      casePlaceValue] <;>
    omega

/-- Every official witness with one live off-diagonal channel on each X5 edge
can be carried to a named audited representative and then gauge-normalized.
The final witness remains official and has exactly the transported support. -/
theorem exists_representative_normalized_witness
    (choice : CaseChoice) (W : WeightsN 6 3 ℂ)
    (hW : EqSystemN 6 3 W)
    (live : ∀ slot, W (supportEntry choice slot) ≠ 0) :
    ∃ (representative : Fin 336) (leaf : LeafSymmetry)
        (colour : ColourSymmetry) (normalized : WeightsN 6 3 ℂ),
      actCase leaf colour choice = representativeChoice representative ∧
      EqSystemN 6 3 normalized ∧
      (∀ edge, normalized edge = 0 ↔
        transportToAction leaf colour W edge = 0) ∧
      (∀ slot, normalized ((datum representative).selected slot) = 1) := by
  obtain ⟨witness, action⟩ :=
    exists_orbitWitness_correct (encodeChoice choice)
  have actionChoice :
      actCase witness.leaf witness.colour choice =
        representativeChoice witness.representative := by
    simpa only [labelledCaseChoice_encode] using action
  let transported := transportToAction witness.leaf witness.colour W
  have transportedSystem : EqSystemN 6 3 transported :=
    eqSystemN_transportToAction witness.leaf witness.colour W hW
  have transportedLive : ∀ slot,
      transported ((datum witness.representative).selected slot) ≠ 0 := by
    intro slot
    rw [← representativeChoice_eq_datum_selected]
    rw [← actionChoice]
    change transportToAction witness.leaf witness.colour W
      (supportEntry (actCase witness.leaf witness.colour choice) slot) ≠ 0
    rw [transportToAction_supportEntry]
    exact live (leafSourceSlot witness.leaf slot)
  obtain ⟨normalized, normalizedSystem, sameSupport, normalizedEntries⟩ :=
    exists_normalized_witness (datum witness.representative)
      transported transportedSystem transportedLive
  exact ⟨witness.representative, witness.leaf, witness.colour, normalized,
    actionChoice, normalizedSystem, sameSupport, normalizedEntries⟩

#print axioms Krenn.X5NormalizationConnector.labelledCaseChoice_encode
#print axioms Krenn.X5NormalizationConnector.exists_representative_normalized_witness

end Krenn.X5NormalizationConnector
