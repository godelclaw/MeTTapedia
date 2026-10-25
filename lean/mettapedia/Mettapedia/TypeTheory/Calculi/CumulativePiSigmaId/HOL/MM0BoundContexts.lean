import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationMaterialSemantics
import Mettapedia.Languages.MM0.HOLContextRenaming

/-!
# MM0 bound-name independence at the material DTT interface

The actual cumulative set-operation signature accepts substitution that
identifies two object variables. Its material set and hyperset meanings
commute with that substitution. MM0's two-bound context rejects the same
identification. Consequently, ordinary DTT typing and value interpretation do
not discharge the additional name-independence obligation of an MM0 proof.

These results retain the native MM0 guard as a separate condition. They do
not interpret name inequality as inequality of sets or hypersets, and do not
claim a full proof compiler for the maintained `hol.mm0` presentation.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.MM0BoundContexts
open Mettapedia.Logic
open HOL.Embedding
open Mettapedia.Languages.MM0
open HOLContextRenaming
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open FormationSensitiveHOLInterface SetOperationMaterialSemantics
open ZFSetHenkinInterpretation (Symbol set member)

/-- The raw context map of the same intrinsic identifying substitution. -/
def rawIdentify : Ren pairContext.length singletonContext.length := fun _ => 0

theorem variableIndex_identify {type : HOL.Ty Unit} (index : HOL.Var pairContext type) :
    variableIndex (identify index) = rawIdentify (variableIndex index) := by
  cases index with
  | vz => rfl
  | vs index => cases index with
    | vz => rfl
    | vs index => nomatch index

/-- Every term in this actual two-variable context commutes with its DTT
translation under the identifying substitution. -/
theorem native_identification {type : HOL.Ty Unit} (term : HOL.Term Symbol pairContext type) :
    native (HOL.rename identify term) = rename rawIdentify (native term) :=
  HOLImpredicativeRepresentation.translate_rename SetOperationSignature.signature
    identify rawIdentify variableIndex_identify term

/-- DTT formation and typing continue to hold when the variables coincide. -/
theorem identified_term_typed {type : HOL.Ty Unit} (term : HOL.Term Symbol pairContext type) :
    FormationSensitive.Typing SetOperationSignature.signature.rules
      (context SetOperationSignature.types singletonContext)
      (native (HOL.rename identify term)) (typeAt SetOperationSignature.types singletonContext.length type) :=
  HOLImpredicativeRepresentation.translate_typed SetOperationSignature.signature _

universe u

/-- The independently computed material graph reading has the same context
naturality, even for a noninjective object-variable map. -/
theorem set_identification {type : HOL.Ty Unit} (term : HOL.Term Symbol pairContext type)
    (valuation : ZFSetHenkinInterpretation.model.{u}.Valuation singletonContext) :
    setGraphMeaning (HOL.rename identify term) valuation =
      setGraphMeaning term (fun index => valuation (identify index)) := by
  rw [setGraphMeaning_eq, setGraphMeaning_eq]
  exact HOL.Soundness.denote_rename _ identify term valuation

theorem hyperset_identification
    (presentation : Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.Presentation.{u})
    {type : HOL.Ty Unit} (term : HOL.Term Symbol pairContext type)
    (valuation : (HypersetHenkinInterpretation.model presentation).Valuation singletonContext) :
    hypersetGraphMeaning presentation (HOL.rename identify term) valuation =
      hypersetGraphMeaning presentation term (fun index => valuation (identify index)) := by
  rw [hypersetGraphMeaning_eq, hypersetGraphMeaning_eq]
  exact HOL.Soundness.denote_rename _ identify term valuation

/-- An explicitly typed native membership term still provides no authority
for collapsing two MM0 bound names. -/
theorem typing_does_not_admit_bound_collapse (signature : Kernel.TermSignature) :
    Kernel.Substitution.checkAdmissible signature [.bound 0, .bound 0] [.bound 0]
      [.var 0, .var 0] = false ∧
    FormationSensitive.Typing SetOperationSignature.signature.rules
      (context SetOperationSignature.types singletonContext)
      (native (member (.var .vz) (.var .vz)))
      (typeAt SetOperationSignature.types singletonContext.length .prop) :=
  ⟨identified_names_refused signature,
   identified_term_typed (member (.var .vz) (.var (.vs .vz)))⟩

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.MM0BoundContexts
