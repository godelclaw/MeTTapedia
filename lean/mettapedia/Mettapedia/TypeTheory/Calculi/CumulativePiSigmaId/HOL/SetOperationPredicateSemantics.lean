import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLPredicateEqualitySemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationMaterialSemantics

/-!
# The predicate-equality operation in the four material interpretations

The actual native equality lambda has its intrinsic equality value in the
well-founded set, well-founded hyperset, full hyperset and coded hyperset
models. Each result uses the independently defined lambda/quantifier
interpretation over the original six-operation signature. The four carriers
retain their distinct membership relations. Proof-term denotation and native
identity policies are separate from this operation-value comparison.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationPredicateSemantics
open Mettapedia.Logic
open HOL.Embedding
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open NativeHOLSignatureDenotation
universe u

theorem sets_equality (type : HOL.Ty Unit) :
    Denotes SetOperationSignature.signature ZFSetHenkinInterpretation.model.{u}
      (gamma := []) (type := .arr type (.arr type .prop))
      (HOLPredicateEqualitySignature.equality SetOperationSignature.signature type)
      (fun _ left right => ULift.up (ZFSetHenkinInterpretation.model.Eqv type left right)) :=
  HOLPredicateEqualitySemantics.native_equality_value _ _
    (ZFSetHenkinInterpretation.model.functionsRespectEqv_of_fullDomains
      ZFSetHenkinInterpretation.fullDomains) type (ZFSetHenkinInterpretation.fullDomains type)

theorem sets_mapping_equality :
    Denotes SetOperationSignature.signature ZFSetHenkinInterpretation.model.{u}
      (gamma := []) (type := .arr ZFSetHenkinInterpretation.mapping
        (.arr ZFSetHenkinInterpretation.mapping .prop))
      (HOLPredicateEqualitySignature.equality SetOperationSignature.signature
        ZFSetHenkinInterpretation.mapping)
      (fun _ left right => ULift.up
        (ZFSetHenkinInterpretation.model.Eqv ZFSetHenkinInterpretation.mapping left right)) :=
  HOLPredicateEqualitySemantics.native_equality_value _ _
    (ZFSetHenkinInterpretation.model.functionsRespectEqv_of_fullDomains
      ZFSetHenkinInterpretation.fullDomains) ZFSetHenkinInterpretation.mapping
    (ZFSetHenkinInterpretation.fullDomains ZFSetHenkinInterpretation.mapping)

theorem wellFounded_equality (presentation : HSet.Presentation.{u}) (type : HOL.Ty Unit) :
    Denotes SetOperationSignature.signature (WellFoundedHypersetInterpretation.model presentation)
      (gamma := []) (type := .arr type (.arr type .prop))
      (HOLPredicateEqualitySignature.equality SetOperationSignature.signature type)
      (fun _ left right => ULift.up ((WellFoundedHypersetInterpretation.model presentation).Eqv type left right)) :=
  HOLPredicateEqualitySemantics.native_equality_value _ _
    ((WellFoundedHypersetInterpretation.model presentation).functionsRespectEqv_of_fullDomains
      (WellFoundedHypersetInterpretation.fullDomains presentation)) type
    (WellFoundedHypersetInterpretation.fullDomains presentation type)

theorem hypersets_equality (presentation : HSet.Presentation.{u}) (type : HOL.Ty Unit) :
    Denotes SetOperationSignature.signature (HypersetHenkinInterpretation.model presentation)
      (gamma := []) (type := .arr type (.arr type .prop))
      (HOLPredicateEqualitySignature.equality SetOperationSignature.signature type)
      (fun _ left right => ULift.up ((HypersetHenkinInterpretation.model presentation).Eqv type left right)) :=
  HOLPredicateEqualitySemantics.native_equality_value _ _
    ((HypersetHenkinInterpretation.model presentation).functionsRespectEqv_of_fullDomains
      (HypersetHenkinInterpretation.fullDomains presentation)) type
    (HypersetHenkinInterpretation.fullDomains presentation type)

theorem codes_equality (presentation : HSet.Presentation.{u}) (type : HOL.Ty Unit) :
    Denotes SetOperationSignature.signature (CodedHypersetInterpretation.model presentation)
      (gamma := []) (type := .arr type (.arr type .prop))
      (HOLPredicateEqualitySignature.equality SetOperationSignature.signature type)
      (fun _ left right => ULift.up ((CodedHypersetInterpretation.model presentation).Eqv type left right)) :=
  HOLPredicateEqualitySemantics.native_equality_value _ _
    ((CodedHypersetInterpretation.model presentation).functionsRespectEqv_of_fullDomains
      (CodedHypersetInterpretation.fullDomains presentation)) type
    (CodedHypersetInterpretation.fullDomains presentation type)

#print axioms sets_equality
#print axioms wellFounded_equality
#print axioms hypersets_equality
#print axioms codes_equality
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationPredicateSemantics
