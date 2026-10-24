import Mettapedia.Languages.Megalodon.HOLTermEncoding
import Mettapedia.Languages.Megalodon.HOLNormalForms
import Mettapedia.Languages.Megalodon.RetainedNormalization
import Mettapedia.Languages.Megalodon.RelationEqualityComparison
import Mettapedia.Logic.HOL.ImpredicativeEncodingEquations

/-!
# Retained proof comparison for the complete Megalodon HOL term encoding

Binary-relation equality and impredicative connective expansion each have
constructed source equations. Their composition compares every source term
with its actual encoded term. Hypothesis substitution transports proofs in
both directions at the exact ordered assumption list.

The comparison concerns derivability in the existing extensional source
calculus. It does not recover the original proof presentation, turn these
comparison proofs into the native logical fragment, or add an ambient host
identity principle.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.Megalodon.HOLTermEncodingProofs
open Mettapedia.Logic.HOL
open ContextualTrinity HOLTermEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

/-- Construct the equality expansion equation through all term constructors. -/
def expandEqualityEquation {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type)
    (assumptions : List (Formula Const gamma)) :
    ProofSyntax Const assumptions (.eq source (expandEquality source)) :=
  match source with
  | .var index => .eqRefl (.var index)
  | .const symbol => .eqRefl (.const symbol)
  | .app function argument => ProofSyntax.appCongr (expandEqualityEquation function assumptions) (expandEqualityEquation argument assumptions)
  | .lam body => .eqLam (expandEqualityEquation body (weakenHyps assumptions))
  | .top => .eqRefl .top
  | .bot => .eqRefl .bot
  | .and first second => ProofSyntax.andCongr (expandEqualityEquation first assumptions) (expandEqualityEquation second assumptions)
  | .or first second => ProofSyntax.orCongr (expandEqualityEquation first assumptions) (expandEqualityEquation second assumptions)
  | .imp first second => ProofSyntax.impCongr (expandEqualityEquation first assumptions) (expandEqualityEquation second assumptions)
  | .not body => ProofSyntax.notCongr (expandEqualityEquation body assumptions)
  | .eq first second => .eqTrans
      (ProofSyntax.eqCongr (expandEqualityEquation first assumptions) (expandEqualityEquation second assumptions))
      (RelationEqualityComparison.equation (expandEquality first) (expandEquality second))
  | .all body => allCongr (expandEqualityEquation body (weakenHyps assumptions))
  | .ex body => exCongr (expandEqualityEquation body (weakenHyps assumptions))
termination_by structural source

def equation {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type)
    (assumptions : List (Formula Const gamma)) : ProofSyntax Const assumptions (.eq source (encode source)) :=
  .eqTrans (expandEqualityEquation source assumptions)
    (ImpredicativeEncodingEquations.equation (expandEquality source) assumptions)

def toEncoding {gamma : Ctx Base} {assumptions : List (Formula Const gamma)} {conclusion : Formula Const gamma}
    (source : ProofSyntax Const assumptions conclusion) :
    ProofSyntax Const (assumptions.map encode) (encode conclusion) := by
  let target := assumptions.map encode
  have supplied : ProofSyntax.HypothesisSubstitution assumptions target := by
    intro occurrence
    let mapped : Fin target.length := ⟨occurrence.val, by simp [target]⟩
    have value : ProofSyntax Const target (encode (assumptions.get occurrence)) := by
      have chosen := ProofSyntax.hyp (Const := Const) (Δ := target) mapped
      simpa only [target, List.get_eq_getElem, List.getElem_map, mapped] using chosen
    exact .impE (.eqPropER (equation (assumptions.get occurrence) target)) value
  exact .impE (.eqPropEL (equation conclusion target)) (source.substituteHypotheses supplied)

def fromEncoding {gamma : Ctx Base} {assumptions : List (Formula Const gamma)} {conclusion : Formula Const gamma}
    (source : ProofSyntax Const (assumptions.map encode) (encode conclusion)) :
    ProofSyntax Const assumptions conclusion := by
  have supplied : ProofSyntax.HypothesisSubstitution (assumptions.map encode) assumptions := by
    intro occurrence
    let original : Fin assumptions.length := occurrence.cast (by simp)
    have value : ProofSyntax Const assumptions (encode (assumptions.get original)) :=
      .impE (.eqPropEL (equation (assumptions.get original) assumptions)) (.hyp original)
    simpa only [List.get_eq_getElem, List.getElem_map, original, Fin.val_cast] using value
  exact .impE (.eqPropER (equation conclusion assumptions)) (source.substituteHypotheses supplied)

theorem fromEncoding_derivation {gamma : Ctx Base} {assumptions : List (Formula Const gamma)} {conclusion : Formula Const gamma}
    (source : ProofSyntax Const (assumptions.map encode) (encode conclusion)) :
    ExtDerivation Const assumptions conclusion := (fromEncoding source).erase

theorem roundTrip_changes_proof {gamma : Ctx Base} {type : Ty Base} (value : Term Const gamma type) :
    fromEncoding (toEncoding (ProofSyntax.eqRefl (Δ := []) value)) ≠ ProofSyntax.eqRefl value := by
  intro same
  have observation := congrArg ProofSyntax.rootObservation same
  cases observation

def normalFormEquation {environment : MathdataKernel.Environment}
    {gamma : Ctx HenkinTermInterpretation.Base} {type : Ty HenkinTermInterpretation.Base}
    (source : Term (HenkinTermInterpretation.Constant environment) gamma type) :
    ProofSyntax (HenkinTermInterpretation.Constant environment) [] (.eq source (HOLNormalForms.normalForm source)) := by
  let completed := NormalizationTermination.complete (encode source) (native_erased source)
  let retained := RetainedNormalization.readback completed.val.1 (encode source) (native_erased source) completed.property
  have same : retained.val.target = HOLNormalForms.normalForm source :=
    HenkinTermInterpretation.erase_injective_of_eq_some retained.property (HOLNormalForms.normalForm_erased source)
  exact .eqTrans (equation source [])
    (ProofSyntax.castIndices rfl (congrArg (Term.eq (encode source)) same) retained.val.proof)

#print axioms normalFormEquation
#print axioms expandEqualityEquation
#print axioms equation
#print axioms toEncoding
#print axioms fromEncoding
#print axioms roundTrip_changes_proof
end Mettapedia.Languages.Megalodon.HOLTermEncodingProofs
