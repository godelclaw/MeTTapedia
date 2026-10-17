import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaData
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

/-!
# The data boundary of the generated MeTTa program

An encoded guest term supplied at `Atom` demand has exactly its original data
and bindings as the result in the independent HE semantics. This uses HE's
existing evaluator relation, not a target relation defined by compilation.
Native C refinement and the surrounding generated calls remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings ResultPair)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval

theorem encoded_data_is_not_error (term : Term) : ¬ IsErrorRel (encode term) := by
  cases term <;> simp [IsErrorRel, encode]

theorem encoded_data_meta_type (term : Term) :
    MetaTypeRel (encode term) Atom.expressionType := by
  cases term <;> exact .expression _

/-- Both preservation and no additional result, for any space and host dispatch. -/
theorem data_evaluation_iff (space : Space) (dispatch : GroundedDispatch)
    (live : List Atom) (bindings : Bindings) (term : Term) (result : ResultPair)
    (typing : EvalTypeService) :
    EvalRel space dispatch live (encode term) Atom.atomType bindings result typing ↔
      result = (encode term, bindings) := by
  constructor
  · intro evaluated
    exact (BindingFrame.historicalResult_inj (left := result)
      (right := (encode term, bindings))).mp (Minimal.full_atom_expected_exact.mp evaluated)
  · rintro rfl
    exact Minimal.full_atom_expected_exact.mpr rfl

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaData
