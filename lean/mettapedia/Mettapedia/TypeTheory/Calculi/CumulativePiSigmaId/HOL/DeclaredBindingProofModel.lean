import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.DeclaredBindingProofConsumption
import Mettapedia.Logic.HOL.Embedding.ZFSetContextualIdentity

/-!
# The constructed model of the joined binding/proof consumer

The interpretation uses the actual uniform-List compiler and contextual set
families. The resulting section is the section of the compiled source proof,
at the original predicate and its computed value. No small-section carrier,
whole-term preservation law, or universal semantic algebra is postulated.
HOL equality is compared with this model's extensional identity explicitly;
that comparison imposes no identity-reflection rule on the native calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.DeclaredBindingProofModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Mettapedia.Logic HOL.UniformListInduction
open HOLNativeGenericProofCompiler HOLImpredicativeProofCompilation
open Mettapedia.Logic.HOL.Embedding
open ZFSetContextualInterpretation (SetFamily Section Extension)
open ZFSetUniformListTraceTermInterpretation (interpret)
open NativeHOLTraceDisplayedTerms (typeFamily)
open NativeTraceDisplayedSubstitution (castSection castSection_heq)
open DeclaredBindingProofConsumption

universe u
variable {a : ZFSet.{u}} {Γ : HOL.Ctx BaseSort}
  {Δ : List (HOL.Formula Symbol Γ)} {σ : HOL.Ty BaseSort}
  {n : Nat} {objects : Sub Tower.Head Γ.length n}

theorem proofConsumer_denotes {predicate : HOL.Term Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (state : UniformListSemantics.State a objects)
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (hypothesesMeaning : GenericSemantics.Hypotheses
      (UniformListSemantics.algebra a) state hypotheses) :
    ∃ evidence : Section (fun environment =>
        HOLProofCarryingPairTraceSemantics.invariantFamily state predicate
          ⟨environment, interpret value.term (state.valuation environment)⟩),
      DeclaredBindingTraceSemantics.Denotes a state.context
        (proofConsumer value context objects hypotheses)
        (fun environment => HOLProofCarryingPairTraceSemantics.invariantFamily state predicate
          ⟨environment, interpret value.term (state.valuation environment)⟩) evidence ∧
      NativeHOLTraceQualifiedExtensionalSemantics.Denotes a state.context
        (translateProof signature UniformList.proofName UniformList.operations uniformList_total
          value.evidence objects hypotheses)
        (fun environment => HOLProofCarryingPairTraceSemantics.invariantFamily state predicate
          ⟨environment, interpret value.term (state.valuation environment)⟩) evidence := by
  obtain ⟨_, evidence, _, proofMeaning⟩ :=
    HOLProofCarryingPairTraceSemantics.pack_second_square value state hypothesesMeaning
  let domain := typeFamily a state.context σ
  let family := HOLProofCarryingPairTraceSemantics.invariantFamily state predicate
  let objectValue : Section domain :=
    fun environment => interpret value.term (state.valuation environment)
  let pairValue := ZFSetContextualInterpretation.pair (b := family) objectValue evidence
  let pairFamily := ZFSetContextualInterpretation.sigmaFamily domain family
  let extended := state.context.snoc pairFamily
  have pairMeaning : NativeHOLTraceQualifiedExtensionalSemantics.Denotes a state.context
      (Packed value objects hypotheses) pairFamily pairValue :=
    .pair (codomain := family)
      (.mixed (.object (HOLProofCarryingPairTraceSemantics.translate_denotes value.term state)))
      proofMeaning
  have variableMeaning : NativeHOLTraceQualifiedExtensionalSemantics.Denotes a extended
      (.var 0)
      (ZFSetContextualInterpretation.sigmaFamily (domain ∘ Sigma.fst)
        (family ∘ ZFSetContextualInterpretation.extensionSubstitution Sigma.fst domain))
      (extended.projection 0) := .mixed (.variable extended 0)
  have bodyMeaning := NativeHOLTraceQualifiedExtensionalSemantics.Denotes.second variableMeaning
  have combined := DeclaredBindingTraceSemantics.Denotes.whereBinding
    (context.frame.freshName "certified")
    (DeclaredBindingTraceSemantics.Denotes.core pairMeaning)
    (DeclaredBindingTraceSemantics.Denotes.result
      (DeclaredBindingTraceSemantics.Denotes.core bodyMeaning))
  have familyEqual :
      (fun environment => family
        ⟨environment, ZFSetContextualInterpretation.fst pairValue environment⟩) =
      (fun environment => family ⟨environment, objectValue environment⟩) := by
    funext environment
    exact congrArg (fun first => family ⟨environment, first⟩)
      (congrFun (ZFSetContextualInterpretation.fst_pair (b := family) objectValue evidence) environment)
  have moved := combined.cast_family familyEqual
  have valueEqual : castSection familyEqual
      (ZFSetContextualInterpretation.snd pairValue) = evidence :=
    eq_of_heq ((castSection_heq familyEqual _).trans
      (ZFSetContextualInterpretation.snd_pair objectValue evidence))
  exact ⟨evidence, moved.change_value valueEqual, proofMeaning⟩

/-- The independently interpreted source and its compiled dependent term
retain one and the same section of the original invariant family. -/
theorem joined_interpretation {predicate : HOL.Term Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (state : UniformListSemantics.State a objects)
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (hypothesesMeaning : GenericSemantics.Hypotheses
      (UniformListSemantics.algebra a) state hypotheses) :
    ∃ evidence : Section (fun environment =>
        HOLProofCarryingPairTraceSemantics.invariantFamily state predicate
          ⟨environment, interpret value.term (state.valuation environment)⟩),
      NativeHOLTraceQualifiedExtensionalSemantics.Denotes a state.context
        (DeclaredBindingDependent.translate (proofConsumer value context objects hypotheses))
        (fun environment => HOLProofCarryingPairTraceSemantics.invariantFamily state predicate
          ⟨environment, interpret value.term (state.valuation environment)⟩) evidence ∧
      NativeHOLTraceQualifiedExtensionalSemantics.Denotes a state.context
        (translateProof signature UniformList.proofName UniformList.operations uniformList_total
          value.evidence objects hypotheses)
        (fun environment => HOLProofCarryingPairTraceSemantics.invariantFamily state predicate
          ⟨environment, interpret value.term (state.valuation environment)⟩) evidence := by
  obtain ⟨evidence, sourceMeaning, proofMeaning⟩ := proofConsumer_denotes value context state hypothesesMeaning
  exact ⟨evidence, DeclaredBindingTraceSemantics.translation_preserves sourceMeaning, proofMeaning⟩

/-- For the concrete List interpretation, source equality and contextual
identity have equal set codes. The proof does not identify native conversion. -/
theorem equality_identity_family (state : UniformListSemantics.State a objects)
    (left right : HOL.Term Symbol Γ σ) :
    ZFSetTraceProofDecoding.truthFamily
        (fun environment => ZFSetHOLTypeInterpretation.holds
          (interpret (.eq left right) (state.valuation environment))) =
      ZFSetContextualIdentity.identityFamily (typeFamily a state.context σ)
        (fun environment => interpret left (state.valuation environment))
        (fun environment => interpret right (state.valuation environment)) := by
  funext environment
  apply congrArg ZFSetTraceProofDecoding.truthCode
  exact propext (ZFSetHOLTypeInterpretation.holds_truth _)

/-- A second component indexed by the first proof, rather than only by the
number proved about. These are the existing contextual Sigma and Id codes. -/
noncomputable def exactEvidenceFamily {Ω : Type (u + 1)}
    (family : SetFamily Ω) (evidence : Section family) : SetFamily Ω :=
  ZFSetContextualInterpretation.sigmaFamily family
    (ZFSetContextualIdentity.identityFamily (family ∘ Sigma.fst)
      (fun point => point.2) (fun point => evidence point.1))

noncomputable def exactEvidence {Ω : Type (u + 1)}
    (family : SetFamily Ω) (evidence : Section family) :
    Section (exactEvidenceFamily family evidence) :=
  ZFSetContextualInterpretation.pair
    (b := ZFSetContextualIdentity.identityFamily (family ∘ Sigma.fst)
      (fun point => point.2) (fun point => evidence point.1)) evidence
    (ZFSetContextualIdentity.reflexivity.refl evidence)

theorem exactEvidence_first {Ω : Type (u + 1)}
    (family : SetFamily Ω) (evidence : Section family) :
    ZFSetContextualInterpretation.fst (exactEvidence family evidence) = evidence :=
  ZFSetContextualInterpretation.fst_pair _ _

/-- The source proof supplies the actual first component of an Id-indexed
dependent result in the constructed set model. No witness is chosen anew. -/
theorem joined_exact_evidence {predicate : HOL.Term Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (state : UniformListSemantics.State a objects)
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (hypothesesMeaning : GenericSemantics.Hypotheses
      (UniformListSemantics.algebra a) state hypotheses) :
    let family := fun environment =>
      HOLProofCarryingPairTraceSemantics.invariantFamily state predicate
        ⟨environment, interpret value.term (state.valuation environment)⟩
    ∃ evidence : Section family, ∃ output : Section (exactEvidenceFamily family evidence),
      NativeHOLTraceQualifiedExtensionalSemantics.Denotes a state.context
        (DeclaredBindingDependent.translate (proofConsumer value context objects hypotheses))
        family evidence ∧
      NativeHOLTraceQualifiedExtensionalSemantics.Denotes a state.context
        (translateProof signature UniformList.proofName UniformList.operations uniformList_total
          value.evidence objects hypotheses) family evidence ∧
      ZFSetContextualInterpretation.fst output = evidence := by
  obtain ⟨evidence, consumerMeaning, proofMeaning⟩ :=
    joined_interpretation value context state hypothesesMeaning
  exact ⟨evidence, exactEvidence _ evidence, consumerMeaning, proofMeaning,
    exactEvidence_first _ evidence⟩

/-- The authored exact-pair consumer's beta law is joined to the actual
compiler section and contextual Sigma/Id operations. This states the admitted
consumer connection, not a model of every extension of the core calculus. -/
theorem exact_pair_consumer_model {predicate : HOL.Term Symbol Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    (context : PrivateIdentityContexts.Context Tower.Head n)
    (state : UniformListSemantics.State a objects)
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (hypothesesMeaning : GenericSemantics.Hypotheses
      (UniformListSemantics.algebra a) state hypotheses) :
    let family := fun environment =>
      HOLProofCarryingPairTraceSemantics.invariantFamily state predicate
        ⟨environment, interpret value.term (state.valuation environment)⟩
    ∃ evidence : Section family, ∃ output : Section (exactEvidenceFamily family evidence),
      Step rules.headEq
        (DeclaredBindingDependent.translate (exactPairConsumer value context objects hypotheses))
        (.pair (.snd (Packed value objects hypotheses))
          (.refl (.snd (Packed value objects hypotheses)))) rules.computation ∧
      NativeHOLTraceQualifiedExtensionalSemantics.Denotes a state.context
        (translateProof signature UniformList.proofName UniformList.operations uniformList_total
          value.evidence objects hypotheses) family evidence ∧
      ZFSetContextualInterpretation.fst output = evidence := by
  obtain ⟨evidence, _, proofMeaning⟩ := joined_interpretation value context state hypothesesMeaning
  exact ⟨evidence, exactEvidence _ evidence, exactPairConsumer_beta value context objects hypotheses,
    proofMeaning, exactEvidence_first _ evidence⟩

namespace Controls

/-- The invariant mentions the ambient count, rather than a closed constant. -/
def ambientPredicate : HOL.Term Symbol [count] (.arr count .prop) :=
  .lam (.eq (.var .vz) (.var (.vs .vz)))

def ambientPremise : HOL.Formula Symbol [count] := .app ambientPredicate (.var .vz)

def ambientValue : HOL.ProofCarryingPipeline.Value ambientPredicate [ambientPremise] where
  term := .var .vz
  evidence := .hyp 0

abbrev objectContext : Tower.Ctx 1 :=
  FormationSensitiveHOLInterface.context signature.types [count]

abbrev objectSlots : Sub Tower.Head 1 1 := liftSub (Fin.elim0 : Sub Tower.Head 0 0)

def premiseCode : Tower.Tm 1 := HOLImpredicativeRepresentation.translate signature ambientPremise

def nativeContext : Tower.Ctx 2 :=
  .snoc objectContext (FormationSensitiveHOLGenericProofFamily.proof UniformList.proofName
    (subst objectSlots premiseCode))

def privateContext : PrivateIdentityContexts.Context Tower.Head 2 :=
  PrivateIdentityContexts.Context.ofCore nativeContext

abbrev ambientObjects : Sub Tower.Head 1 2 := fun i => rename wk (objectSlots i)

def ambientHypotheses : Fin ([ambientPremise].map HOL.ImpredicativeConnectives.expand).length →
    Tower.Tm 2 := Fin.cases (.var 0) (fun i => Fin.elim0 i)

theorem objectSlots_typed : GenericTyping.Objects signature (gamma := [count]) objectContext objectSlots := by
  exact GenericTyping.Objects.lift signature (gamma := []) (fun i => Fin.elim0 i) count

theorem ambientObjects_typed : GenericTyping.Objects signature (gamma := [count]) nativeContext ambientObjects :=
  objectSlots_typed.weaken signature _

theorem ambientHypotheses_typed : GenericTyping.Hypotheses signature UniformList.operations
    nativeContext ambientObjects ambientHypotheses := by
  have prior : GenericTyping.Hypotheses signature UniformList.operations
      (gamma := [count]) (delta := []) objectContext objectSlots Fin.elim0 := fun i => Fin.elim0 i
  have supplied := GenericTyping.Hypotheses.prepend signature prior
    (HOLImpredicativeRepresentation.translate_eq signature ambientPremise)
  intro i
  rcases i with ⟨i, valid⟩
  have equal : i = 0 := by
    have bound : i < 1 := by simpa using valid
    omega
  subst i
  exact supplied ⟨0, by decide⟩

theorem privateContext_formed : PrivateIdentityContexts.WellFormed rules privateContext := by
  apply PrivateIdentityContexts.Context.ofCore_formed
  have propositionTyped := GenericTyping.represented_typed signature UniformList.operations
    (HOLImpredicativeRepresentation.translate_eq signature ambientPremise) objectSlots_typed
  have proofFormed := FormationSensitiveHOLGenericProofFamily.proof_formed signature
    UniformList.proofName UniformList.operations.fresh
    (propositionTyped.includeSignature
      (FormationSensitiveHOLGenericProofFamily.declarations signature UniformList.proofName))
  have formedObjects : FormationSensitive.ContextFormation rules objectContext := by
    simpa only [Ctx.mapHead_id] using
      (FormationSensitiveHOLInterface.context_formed signature [count]).mapHead
        UniformList.operations.sourceMorphism
  exact .snoc formedObjects (UniformList.operations.includeProofTyping proofFormed)
    UniformList.operations.zeroUniverse

theorem ambient_consumer_typed : DeclaredBindingDependent.Typing rules privateContext
    (proofConsumer ambientValue privateContext ambientObjects ambientHypotheses)
    (inst0 (Packed ambientValue ambientObjects ambientHypotheses)
      (witnessFamily ambientPredicate ambientObjects)) := by
  apply proofConsumer_typed ambientValue privateContext privateContext_formed
  · simpa only [privateContext, PrivateIdentityContexts.Context.erase_ofCore] using ambientObjects_typed
  · simpa only [privateContext, PrivateIdentityContexts.Context.erase_ofCore] using ambientHypotheses_typed

theorem ambient_exact_consumer_typed : DeclaredBindingDependent.Typing rules privateContext
    (exactPairConsumer ambientValue privateContext ambientObjects ambientHypotheses)
    (inst0 (Packed ambientValue ambientObjects ambientHypotheses)
      (exactPairFamily ambientPredicate ambientObjects)) := by
  apply exactPairConsumer_typed ambientValue privateContext privateContext_formed
  · simpa only [privateContext, PrivateIdentityContexts.Context.erase_ofCore] using ambientObjects_typed
  · simpa only [privateContext, PrivateIdentityContexts.Context.erase_ofCore] using ambientHypotheses_typed

noncomputable def ambientObjectState (a : ZFSet.{u}) :
    UniformListSemantics.State a (gamma := [count]) objectSlots :=
  UniformListSemantics.objectExtension a
    (UniformListSemantics.Controls.assumptionState a []) count

noncomputable def ambientState (a : ZFSet.{u}) : UniformListSemantics.State a (gamma := [count]) ambientObjects :=
  UniformListSemantics.proofExtension a (ambientObjectState a)
    (HOL.ImpredicativeConnectives.expand ambientPremise)

theorem ambientHypotheses_meaning (a : ZFSet.{u}) : GenericSemantics.Hypotheses
    (UniformListSemantics.algebra a) (ambientState a) ambientHypotheses := by
  have prior : GenericSemantics.Hypotheses (UniformListSemantics.algebra a)
      (UniformListSemantics.objectExtension a
        (UniformListSemantics.Controls.assumptionState a []) count)
      (delta := []) Fin.elim0 := fun i => Fin.elim0 i
  have supplied := GenericSemantics.Hypotheses.prepend
    (UniformListSemantics.algebra a) _ prior (HOL.ImpredicativeConnectives.expand ambientPremise)
  intro i
  rcases i with ⟨i, valid⟩
  have equal : i = 0 := by
    have bound : i < 1 := by simpa using valid
    omega
  subst i
  exact supplied ⟨0, by decide⟩

/-- An actual open object and its retained assumption inhabit the joined
consumer. Both native positions are supplied by constructed context extensions. -/
theorem ambient_joined_model (a : ZFSet.{u}) :
    ∃ evidence : Section (fun environment =>
        HOLProofCarryingPairTraceSemantics.invariantFamily (ambientState a) ambientPredicate
          ⟨environment, interpret ambientValue.term ((ambientState a).valuation environment)⟩),
      NativeHOLTraceQualifiedExtensionalSemantics.Denotes a (ambientState a).context
        (DeclaredBindingDependent.translate
          (proofConsumer ambientValue privateContext ambientObjects ambientHypotheses))
        (fun environment => HOLProofCarryingPairTraceSemantics.invariantFamily
          (ambientState a) ambientPredicate
          ⟨environment, interpret ambientValue.term ((ambientState a).valuation environment)⟩)
        evidence ∧
      NativeHOLTraceQualifiedExtensionalSemantics.Denotes a (ambientState a).context
        (translateProof signature UniformList.proofName UniformList.operations uniformList_total
          ambientValue.evidence ambientObjects ambientHypotheses)
        (fun environment => HOLProofCarryingPairTraceSemantics.invariantFamily
          (ambientState a) ambientPredicate
          ⟨environment, interpret ambientValue.term ((ambientState a).valuation environment)⟩)
        evidence :=
  joined_interpretation ambientValue privateContext (ambientState a) (ambientHypotheses_meaning a)

theorem ambientPremise_true (a : ZFSet.{u})
    (point : (ambientObjectState a).context.Environment) :
    ZFSetHOLTypeInterpretation.holds
      (interpret (HOL.ImpredicativeConnectives.expand ambientPremise)
        ((ambientObjectState a).valuation point)) := by
  rw [ZFSetUniformListTraceTermInterpretation.interpret_expand]
  simp only [ambientPremise, ambientPredicate, interpret,
    ZFSetUniformListTraceTypeInterpretation.app_lam,
    ZFSetUniformListTraceTermInterpretation.extend, ZFSetHOLTypeInterpretation.holds_truth]

/-- Every natural index supplies an actual environment, including an actual
member of the assumed proof fibre. The open model is not vacuous. -/
noncomputable def ambientEnvironment (a : ZFSet.{u}) (index : Nat) :
    (ambientState a).context.Environment :=
  let point : (ambientObjectState a).context.Environment :=
    ⟨PUnit.unit, ZFSetUniformListModel.encodeCount index⟩
  ⟨point, ⟨∅, (ZFSetTraceProofDecoding.mem_truthCode _ ∅).mpr
    ⟨rfl, ambientPremise_true a point⟩⟩⟩

theorem ambient_value_at (a : ZFSet.{u}) (index : Nat) :
    interpret ambientValue.term ((ambientState a).valuation (ambientEnvironment a index)) =
      ZFSetUniformListModel.encodeCount index := rfl

/-- The varying invariant refuses a different material number at the same
ambient environment, independently of the representation of its proof. -/
theorem wrong_material_index_uninhabited (a : ZFSet.{u}) (ambient proposed : Nat)
    (different : proposed ≠ ambient) :
    ¬ Nonempty (ZFSetDependentProducts.Elements
      (HOLProofCarryingPairTraceSemantics.invariantFamily (ambientState a) ambientPredicate
        ⟨ambientEnvironment a ambient, ZFSetUniformListModel.encodeCount proposed⟩)) := by
  rintro ⟨witness⟩
  have equation := ((ZFSetTraceProofDecoding.mem_truthCode _ witness.val).mp witness.property).2
  simp only [ambientPredicate, interpret,
    ZFSetUniformListTraceTypeInterpretation.app_lam,
    ZFSetUniformListTraceTermInterpretation.extend, ZFSetHOLTypeInterpretation.holds_truth] at equation
  have decoded := congrArg ZFSetUniformListModel.decodeCount equation
  exact different (by simpa only [ambientState, ambientObjectState, ambientEnvironment,
    UniformListSemantics.proofExtension, UniformListSemantics.objectExtension,
    ZFSetUniformListTraceTermInterpretation.extend,
    ZFSetUniformListModel.decode_encodeCount] using decoded)

end Controls

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.DeclaredBindingProofModel
