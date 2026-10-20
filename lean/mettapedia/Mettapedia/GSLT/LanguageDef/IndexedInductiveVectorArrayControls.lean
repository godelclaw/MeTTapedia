import Mettapedia.GSLT.LanguageDef.IndexedInductiveVectorArray
import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendTypingControls

/-!
# Ordered array realization controls

The executable controls run actual array append and independent guest
quotation. The semantic negative retains the correct length while reversing
the payload: it cannot decode to the source append result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.VectorArrayControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies Declaration.IndexedFamily SchemaElaboration
open IndexedInductiveNatVec VectorArray Guest.VectorMeaning Guest.AppendMeaning
open Guest.AppendTypingControls

def run (left right : Array Bool) : Array Bool :=
  (VectorArray.append (pack left) (pack right)).val

def expectedPair : Tower.Tm 0 :=
  vconsApp natTm (succApp zeroTm) (succApp zeroTm)
    (vconsApp natTm zeroTm zeroTm (vnilApp natTm))

def verdicts : List (String × Bool) := [
  ("nonempty ordered array append", run #[true] #[false] == #[true, false]),
  ("duplicate payloads retained", run #[true, true] #[false] == #[true, true, false]),
  ("empty left", run #[] #[false] == #[false]),
  ("empty right", run #[true] #[] == #[true]),
  ("array result reused as input", run (run #[true] #[false]) #[true] == #[true, false, true]),
  ("missing payload differs", run #[true] #[false] != #[true]),
  ("extra payload differs", run #[true] #[false] != #[true, false, false]),
  ("same-length permutation differs", run #[true] #[false] != #[false, true]),
  ("independent constructor quotation", quoteArray natTm payload (run #[true] #[false]) == expectedPair),
  ("quoted duplicate remains", quoteArray natTm payload #[true, true] != quoteArray natTm payload #[true]),
  ("quoted element type retained", quoteArray natTm payload #[true] != quoteArray zeroTm payload #[true])]

#eval verdicts

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

theorem quoted_arrays_are_faithful : Function.Injective (quoteArray natTm payload) :=
  quoteArray_injective natTm payload payload_injective

def wrong : Family Bool (Natural.add (Natural.fromNat 1) (Natural.fromNat 1)) :=
  ⟨#[false, true], rfl⟩

/-- A real source-meaning rejection, despite a correct output size. -/
theorem same_length_wrong_result :
    wrong.val.size = (VectorArray.append (pack #[true]) (pack #[false])).val.size ∧
    decode wrong ≠ Vectors.append (decode (pack #[true])) (decode (pack #[false])) := by
  refine ⟨rfl, ?_⟩
  have different : wrong ≠ VectorArray.append (pack #[true]) (pack #[false]) := by decide +kernel
  exact fun same => different ((result_iff (pack #[true]) (pack #[false]) wrong).mpr same)

/-- The nonempty array workload uses the actual module-produced function,
with its previously established typed payloads. -/
theorem nonempty_execution :
    ProgramExecutes
      (applyArgs Programs.appendTerm [natTm, numeral 1, numeral 1,
        quoteArray natTm payload #[true], quoteArray natTm payload #[false]])
      (quoteArray natTm payload #[true, false]) :=
  (compiled_contract _ AppendSource.append_matches_reference natTm payload
    natural_element payload_typed #[true] #[false]).2.1

theorem nonempty_result_judgment :
    FormationSensitive.Judgment Programs.rules .nil expectedPair
      (vecApp natTm (Programs.add (numeral 1) (numeral 1))) :=
  (compiled_contract _ AppendSource.append_matches_reference natTm payload
    natural_element payload_typed #[true] #[false]).2.2

#print axioms all_verdicts
#print axioms same_length_wrong_result
#print axioms nonempty_execution
#print axioms nonempty_result_judgment

end Mettapedia.GSLT.LanguageDef.IndexedInductive.VectorArrayControls
