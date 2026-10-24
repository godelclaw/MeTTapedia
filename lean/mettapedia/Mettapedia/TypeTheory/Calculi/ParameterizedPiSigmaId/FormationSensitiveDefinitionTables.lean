import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDelta
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation

/-!
# Definition tables from checked closed judgments

Every row is checked in the preceding base rules. The table introduces no
new primitive computation: its only additional roots unfold its stored bodies.
Dependent declarations whose checks require earlier rows need the separate
ordered-admission interface.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration
open FormationSensitive
variable {Head : Type} {base : Rules Head}

theorem Signature.formed_of_base_judgments (entries : List (DeclName × Entry Head))
    (fresh : ∀ name entry, (name, entry) ∈ entries → base.constantType name = none)
    (types : ∀ name entry, (name, entry) ∈ entries →
      ∃ u, base.isUniverse u ∧ Typing base .nil entry.type (.head u))
    (values : ∀ name entry, (name, entry) ∈ entries → ∀ value,
      entry.value? = some value → Typing base .nil value entry.type)
    (noSelf : ∀ name entry, (name, entry) ∈ entries → ∀ value,
      entry.value? = some value → value ≠ .const name) :
    (Signature.ofList entries).Formed base where
  fresh := by
    intro name entry known
    exact fresh name entry (Signature.entries_ofList_mem entries known)
  types := by
    intro name type known
    obtain ⟨entry, found, typeEqual⟩ := Option.map_eq_some_iff.mp known
    obtain ⟨u, isUniverse, formed⟩ := types name entry (Signature.entries_ofList_mem entries found)
    cases typeEqual
    exact ⟨u, isUniverse, (formed.includeSignature (Signature.ofList entries)).toRaw⟩
  values := by
    intro name type value known selected
    obtain ⟨entry, found, typeEqual⟩ := Option.map_eq_some_iff.mp known
    have valueKnown : entry.value? = some value := by
      simpa only [Signature.valueOf?, found, Option.bind_some] using selected
    cases typeEqual
    exact ((values name entry (Signature.entries_ofList_mem entries found) value valueKnown).includeSignature
      (Signature.ofList entries)).toRaw
  noSelfDelta := by
    intro name value known
    cases found : (Signature.ofList entries).entries name with
    | none =>
      simp only [Signature.valueOf?, found, Option.bind_none] at known
      cases known
    | some entry =>
      have valueKnown : entry.value? = some value := by
        simpa only [Signature.valueOf?, found, Option.bind_some] using known
      exact noSelf name entry (Signature.entries_ofList_mem entries found) value valueKnown

#print axioms Signature.formed_of_base_judgments
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration
