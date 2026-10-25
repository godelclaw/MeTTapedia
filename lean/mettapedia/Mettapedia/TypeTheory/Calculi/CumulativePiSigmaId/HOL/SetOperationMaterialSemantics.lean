import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationSignature
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLModelTransport
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerConversion
import Mettapedia.Logic.HOL.Embedding.HypersetHOLTermInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetHOLTermInterpretation

/-!
# The set-operation DTT profile in actual material interpretations

One named cumulative Pi/Sigma/identity signature represents the common HOL
operations. Its computed native terms receive both the well-founded set
interpretation and the independently evaluated hyperset graph interpretation.
The comparison of native values is inherited from the actual constructor
semantics, with context substitution supplied by the total source translation.

Well-founded hypersets compare with sets. All hypersets instead compare with
valid interpreted codes; their membership is distinct from host membership.
The semantic judgment is scoped to the declared HOL fragment, and does not
assert soundness of arbitrary native conversion or reflection of whole-host
inhabitation. Material graph identity is extensional; no global identity
policy for the explored candidate space follows.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationMaterialSemantics

open Mettapedia.Logic
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open FormationSensitiveHOLInterface NativeHOLSignatureDenotation
open ZFSetHenkinInterpretation (Symbol)

universe u

/-- The existing total translation at this particular formed signature. -/
def native {Γ : HOL.Ctx Unit} {type : HOL.Ty Unit} (term : HOL.Term Symbol Γ type) : Tower.Tm Γ.length :=
  HOLImpredicativeRepresentation.translate SetOperationSignature.signature term

/-- Canonical simultaneous substitution, using the existing indexed-variable
lookup and the total representation of each source image. -/
def nativeSubstitution {Γ Δ : HOL.Ctx Unit} (substitution : HOL.Subst Symbol Γ Δ) :
    Sub Tower.Head Γ.length Δ.length :=
  fun index => native (substitution (HOLNativeGenericProofCompiler.Modulo.varAt Γ index).2)

theorem nativeSubstitution_at {Γ Δ : HOL.Ctx Unit} (substitution : HOL.Subst Symbol Γ Δ)
    {type : HOL.Ty Unit} (index : HOL.Var Γ type) :
    nativeSubstitution substitution (variableIndex index) = native (substitution index) := by
  unfold nativeSubstitution
  rw [HOLNativeGenericProofCompiler.Modulo.varAt_variableIndex]

theorem native_substitution {Γ Δ : HOL.Ctx Unit} {type : HOL.Ty Unit}
    (term : HOL.Term Symbol Γ type) (substitution : HOL.Subst Symbol Γ Δ) :
    native (HOL.subst substitution term) =
      subst (nativeSubstitution substitution) (native term) :=
  HOLImpredicativeRepresentation.translate_subst SetOperationSignature.signature substitution
    (nativeSubstitution substitution) (fun index => (nativeSubstitution_at substitution index).symm) term

def setGraphMeaning {Γ : HOL.Ctx Unit} {type : HOL.Ty Unit} (term : HOL.Term Symbol Γ type) :
    ZFSetHenkinInterpretation.model.{u}.Valuation Γ →
      HOL.Ty.denote.{0, u + 1} ZFSetHenkinInterpretation.carrier.{u} type :=
  fun valuation => ZFSetHOLTypeInterpretation.decode type
    (ZFSetHOLTermInterpretation.interpret ZFSetHOLTermInterpretation.constants term
      (ZFSetHOLTermInterpretation.encodeValuation valuation))

theorem setGraphMeaning_eq {Γ : HOL.Ctx Unit} {type : HOL.Ty Unit} (term : HOL.Term Symbol Γ type) :
    setGraphMeaning.{u} term = fun valuation => ZFSetHenkinInterpretation.model.denote term valuation := by
  funext valuation
  change ZFSetHOLTermInterpretation.RawValuation.{u} Γ at valuation
  unfold setGraphMeaning
  exact (ZFSetHOLTermInterpretation.core_term_agreement term
    (ZFSetHOLTermInterpretation.encodeValuation valuation)).trans
    (congrArg (fun environment : ZFSetHOLTermInterpretation.RawValuation Γ =>
      ZFSetHenkinInterpretation.model.denote term environment)
      (ZFSetHOLTermInterpretation.decode_encode_valuation valuation))

/-- The actual native term denotes the independently computed material graph value. -/
theorem set_denotation {Γ : HOL.Ctx Unit} {type : HOL.Ty Unit} (term : HOL.Term Symbol Γ type) :
    Denotes SetOperationSignature.signature ZFSetHenkinInterpretation.model.{u}
      (native term) (setGraphMeaning term) := by
  rw [setGraphMeaning_eq]
  exact NativeHOLImpredicativeDenotation.translate_denotes SetOperationSignature.signature _ term

def hypersetGraphMeaning (presentation : HSet.Presentation.{u}) {Γ : HOL.Ctx Unit} {type : HOL.Ty Unit}
    (term : HOL.Term Symbol Γ type) :
    (HypersetHenkinInterpretation.model presentation).Valuation Γ →
      HOL.Ty.denote.{0, u + 1} HypersetHenkinInterpretation.carrier.{u} type :=
  fun valuation => HypersetHOLTypeInterpretation.decode type
    (HypersetHOLTermInterpretation.interpret presentation term
      (HypersetHOLTermInterpretation.encodeValuation valuation))

theorem hypersetGraphMeaning_eq (presentation : HSet.Presentation.{u})
    {Γ : HOL.Ctx Unit} {type : HOL.Ty Unit} (term : HOL.Term Symbol Γ type) :
    hypersetGraphMeaning presentation term =
      fun valuation => (HypersetHenkinInterpretation.model presentation).denote term valuation := by
  funext valuation
  change HypersetHOLTermInterpretation.RawValuation.{u} Γ at valuation
  unfold hypersetGraphMeaning
  exact (HypersetHOLTermInterpretation.term_agreement presentation term
    (HypersetHOLTermInterpretation.encodeValuation valuation)).trans
    (congrArg (fun environment : HypersetHOLTermInterpretation.RawValuation Γ =>
      (HypersetHenkinInterpretation.model presentation).denote term environment)
      (HypersetHOLTermInterpretation.decode_encode_valuation valuation))

theorem hyperset_denotation (presentation : HSet.Presentation.{u})
    {Γ : HOL.Ctx Unit} {type : HOL.Ty Unit} (term : HOL.Term Symbol Γ type) :
    Denotes SetOperationSignature.signature (HypersetHenkinInterpretation.model presentation)
      (native term) (hypersetGraphMeaning presentation term) := by
  rw [hypersetGraphMeaning_eq]
  exact NativeHOLImpredicativeDenotation.translate_denotes SetOperationSignature.signature _ term

/-- The well-founded comparison transports any admitted native semantic
derivation at this signature, retaining its native syntax. -/
theorem wellFounded_native_transport (presentation : HSet.Presentation.{u})
    {Γ : HOL.Ctx Unit} {type : HOL.Ty Unit} {raw : Tower.Tm Γ.length}
    {value : (WellFoundedHypersetInterpretation.model presentation).Valuation Γ →
      HOL.Ty.denote.{0, u + 1} WellFoundedHypersetInterpretation.carrier.{u} type}
    (meaning : Denotes SetOperationSignature.signature (WellFoundedHypersetInterpretation.model presentation) raw value) :
    Denotes SetOperationSignature.signature ZFSetHenkinInterpretation.model raw
      (NativeHOLModelTransport.valueTransport _ _ WellFoundedHypersetInterpretation.baseEquiv value) :=
  NativeHOLModelTransport.denotes_transport _ _ WellFoundedHypersetInterpretation.baseEquiv
    (WellFoundedHypersetInterpretation.fullDomains presentation) ZFSetHenkinInterpretation.fullDomains
    (WellFoundedHypersetInterpretation.constants_transport presentation) meaning

/-- The interpreted-code comparison likewise retains actual native terms and
values, even though its two carriers occupy different meta-level universes. -/
theorem coded_native_transport (presentation : HSet.Presentation.{u})
    {Γ : HOL.Ctx Unit} {type : HOL.Ty Unit} {raw : Tower.Tm Γ.length}
    {value : (CodedHypersetInterpretation.model presentation).Valuation Γ →
      HOL.Ty.denote.{0, u + 2} CodedHypersetInterpretation.carrier.{u} type}
    (meaning : Denotes SetOperationSignature.signature (CodedHypersetInterpretation.model presentation) raw value) :
    Denotes SetOperationSignature.signature (HypersetHenkinInterpretation.model presentation) raw
      (NativeHOLModelTransport.valueTransport _ _ CodedHypersetInterpretation.baseEquiv value) :=
  NativeHOLModelTransport.denotes_transport _ _ CodedHypersetInterpretation.baseEquiv
    (CodedHypersetInterpretation.fullDomains presentation) (HypersetHenkinInterpretation.fullDomains presentation)
    (CodedHypersetInterpretation.constants_transport presentation) meaning

/-- Material set evaluation agrees with first interpreting in well-founded
hypersets, including function-valued variables and open higher-order terms. -/
theorem wellFounded_graph_square (presentation : HSet.Presentation.{u})
    {Γ : HOL.Ctx Unit} {type : HOL.Ty Unit} (term : HOL.Term Symbol Γ type)
    (valuation : (WellFoundedHypersetInterpretation.model presentation).Valuation Γ) :
    setGraphMeaning term
      (HOL.StandardTransport.valuationEquiv (WellFoundedHypersetInterpretation.model presentation)
        ZFSetHenkinInterpretation.model WellFoundedHypersetInterpretation.baseEquiv Γ valuation) =
      HOL.StandardTransport.liftEquiv WellFoundedHypersetInterpretation.baseEquiv type
        ((WellFoundedHypersetInterpretation.model presentation).denote term valuation) := by
  rw [setGraphMeaning_eq]
  exact WellFoundedHypersetInterpretation.denote_transport presentation term valuation

theorem coded_graph_square (presentation : HSet.Presentation.{u})
    {Γ : HOL.Ctx Unit} {type : HOL.Ty Unit} (term : HOL.Term Symbol Γ type)
    (valuation : (CodedHypersetInterpretation.model presentation).Valuation Γ) :
    hypersetGraphMeaning presentation term
      (HOL.StandardTransport.valuationEquiv (CodedHypersetInterpretation.model presentation)
        (HypersetHenkinInterpretation.model presentation) CodedHypersetInterpretation.baseEquiv Γ valuation) =
      HOL.StandardTransport.liftEquiv CodedHypersetInterpretation.baseEquiv type
        ((CodedHypersetInterpretation.model presentation).denote term valuation) := by
  rw [hypersetGraphMeaning_eq]
  exact CodedHypersetInterpretation.denote_transport presentation term valuation

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationMaterialSemantics
