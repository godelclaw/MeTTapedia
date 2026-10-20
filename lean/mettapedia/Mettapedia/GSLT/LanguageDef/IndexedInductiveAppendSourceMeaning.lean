import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendMeaning
import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendSource

/-!
# Meaning of the selected textual dependent append program

The common module's actual operation producer reaches the independently
checked closed function. Its application has a forward execution to the
encoding of the original polynomial source append. The full ordered payload
and its sum-of-lengths index survive this comparison.

The function judgment comes from independent replay. Arbitrary payload
quotations below are operational inputs, not automatically well-typed guest
arguments. This selected-source comparison does not prove correctness of
all parser outputs, all-run normalization, or a C/MeTTa implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.AppendSourceMeaning

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies Declaration.IndexedFamily
open IndexedInductiveNatVec VectorMeaning AppendMeaning

/-- Consume the producer's selected result; do not replace its clauses or
its checked function by the semantic reference operation. -/
theorem compiled_reduces (term : Tower.Tm 0) (compiled : AppendSource.proposedAppend = some term)
    {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    {n m : Natural.Carrier} (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    ProgramExecutes (applyArgs term [element, quoteIndex n, quoteIndex m,
      encodeVector element payload left, encodeVector element payload right])
      (encodeVector element payload (Vectors.append left right)) := by
  rw [AppendSource.append_matches_reference] at compiled
  cases Option.some.inj compiled
  exact appendTerm_program element payload left right

/-- One textual program supplies both the checked full dependent function
and its source append execution for every represented payload and length. -/
theorem authored_append : ∃ term : Tower.Tm 0,
    AppendSource.proposedAppend = some term ∧
    FormationSensitive.Judgment Programs.rules .nil term Programs.appendType ∧
    ∀ (A : Type) (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
      (n m : Natural.Carrier) (left : Vectors.Vector A n) (right : Vectors.Vector A m),
      ProgramExecutes (applyArgs term [element, quoteIndex n, quoteIndex m,
        encodeVector element payload left, encodeVector element payload right])
        (encodeVector element payload (Vectors.append left right)) := by
  refine ⟨Programs.appendTerm, AppendSource.append_matches_reference,
    AppendSource.append_typed _ AppendSource.append_matches_reference, ?_⟩
  intro A element payload n m left right
  exact compiled_reduces _ AppendSource.append_matches_reference element payload left right

/-- The observed result is compared with ordinary list concatenation and
natural addition independently of the textual producer and guest reduction. -/
theorem result_observation {A : Type} {n m : Natural.Carrier}
    (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    (Vectors.toList (Vectors.append left right)).val =
      (Vectors.toList left).val ++ (Vectors.toList right).val ∧
    (Vectors.toList (Vectors.append left right)).val.length = Natural.toNat n + Natural.toNat m := by
  exact ⟨Vectors.append_payload left right, by
    rw [(Vectors.toList (Vectors.append left right)).property, Natural.toNat_add]⟩

#print axioms authored_append
#print axioms result_observation

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.AppendSourceMeaning
