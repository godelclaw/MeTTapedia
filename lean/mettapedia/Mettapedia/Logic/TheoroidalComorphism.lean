import Mettapedia.Logic.InstitutionBorrowing

/-!
# Theoroidal comorphisms: translations that state what the target assumes

An institution comorphism demands the satisfaction condition at every target
model.  Many real translations between logics satisfy it only at the target
models of some extra sentences: a translation from a logic whose function
equality is extensional into one whose functions are codes needs function
extensionality in the target; a translation of a classical logic into an
intuitionistic host needs excluded middle there.  A **theoroidal comorphism**
(Goguen and Roşu, "Institution morphisms", 2002; the simple theoroidal
comorphisms of heterogeneous specification) maps each source signature to a
target signature *together with a set of target sentences*, its
**commitments**, and requires the satisfaction condition only at the target
models of those commitments.

* **Transport** (`entails_transport`).  A source consequence `T ⊨ φ` becomes
  the target consequence `α(T) ∪ C ⊨ α(φ)`: the commitments travel with every
  transported theorem as explicit premises.
* **Plain comorphisms** are the theoroidal ones without commitments
  (`ofComorphism`, `ofComorphism_commitments`).
* **Composition** (`comp`, `comp_commitments`).  The commitments of a composite
  are those of the second leg at the image signature together with the
  translations of the first leg's commitments.  Identities add none
  (`identity_commitments`).
* **Commitments are forced by unreadable target models**
  (`commitmentModel_readable`, `entails_of_readable`).  Every model of the
  commitments has a source model with the same profile on translated
  sentences.  Hence every sentence that holds in all such readable target
  models follows from the commitments of every theoroidal comorphism with that
  sentence translation, and commitments holding in every readable model are
  the least up to consequence (`semanticConsequence_subset_of_readable`).
* **Reflection** (`entails_iff_of_coversModels`).  When every source model is
  read off some model of the commitments, transport is exact: the commitments
  create no new source consequences.  The transport is then a conservative
  route in the sense of `InstitutionBorrowing` (`transportRoute`,
  `transportRoute_conservative_of_coversModels`).
* **Kernels** (`kernel_transport`).  For entailment systems, a theorem of a
  sound source system becomes a theorem of a complete target system from the
  translated premises and the commitments.  A target system that is not
  complete needs a translation of proofs instead (`CarriesTheorems`).

## Control: function extensionality as a commitment

`TheoroidalComorphismControl` translates a logic of two Boolean functions,
compared extensionally, into a logic of two *codes* whose values ignore a tag.

* No institution comorphism has this sentence translation, whatever its model
  reading (`no_comorphism`): two codes that differ only in their tags agree at
  every argument and are unequal, and no pair of functions does both.
* With the commitment "codes that agree at every argument are equal" the
  translation is a theoroidal comorphism (`withExtensionality`).
* Every theoroidal comorphism with this sentence translation has commitments
  that entail extensionality (`commitments_entail_extensional`), so
  extensionality is the least commitment up to consequence
  (`extensionality_least`).
* The source theorem "agreement at both arguments gives equality" transports
  only with the commitment among the premises (`transport_uses_commitment`,
  `transport_fails_without_commitment`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic

open CategoryTheory
open Mettapedia.Logic.InstitutionBorrowing

universe uSignature uSignatureHom uSentence uModel uModelHom

namespace Institution

/-! ## Models of a set of sentences -/

section Satisfaction

variable {Signature : Type uSignature} [Category.{uSignatureHom} Signature]
  (institution : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
    Signature)

/-- A model satisfies every sentence of a set. -/
def SatisfiesAll (signature : Signature)
    (model : institution.model.obj (Opposite.op signature))
    (sentences : Set (institution.sentence.obj signature)) : Prop :=
  ∀ sentence ∈ sentences, institution.satisfies signature model sentence

variable {institution}

/-- A model of a set satisfies its semantic consequences. -/
theorem SatisfiesAll.of_entails {signature : Signature}
    {model : institution.model.obj (Opposite.op signature)}
    {sentences : Set (institution.sentence.obj signature)}
    (satisfied : institution.SatisfiesAll signature model sentences)
    {sentence : institution.sentence.obj signature}
    (entailed : institution.Entails signature sentences sentence) :
    institution.satisfies signature model sentence :=
  entailed model satisfied

/-- A model of a larger set is a model of a smaller one. -/
theorem SatisfiesAll.mono {signature : Signature}
    {model : institution.model.obj (Opposite.op signature)}
    {smaller larger : Set (institution.sentence.obj signature)}
    (included : smaller ⊆ larger)
    (satisfied : institution.SatisfiesAll signature model larger) :
    institution.SatisfiesAll signature model smaller :=
  fun sentence member => satisfied sentence (included member)

/-- The reduct of a model of `larger` along a signature morphism satisfies a
set whose translations `larger` entails. -/
theorem SatisfiesAll.reduct {first second : Signature} (map : first ⟶ second)
    {model : institution.model.obj (Opposite.op second)}
    {smaller : Set (institution.sentence.obj first)}
    {larger : Set (institution.sentence.obj second)}
    (translated : institution.sentence.map map '' smaller ⊆
      institution.semanticConsequence second larger)
    (satisfied : institution.SatisfiesAll second model larger) :
    institution.SatisfiesAll first (institution.reduct map model) smaller := by
  intro sentence member
  have mapped : institution.satisfies second model (institution.sentence.map map sentence) :=
    satisfied.of_entails (translated ⟨sentence, member, rfl⟩)
  exact (institution.satisfaction_condition map model sentence).mp mapped

end Satisfaction

/-! ## Theoroidal comorphisms -/

variable {SourceSignature TargetSignature : Type uSignature}
  [Category.{uSignatureHom} SourceSignature] [Category.{uSignatureHom} TargetSignature]

/-- A **theoroidal comorphism**: a signature translation, a natural sentence
translation, a set of target sentences (the *commitments*) at every translated
signature, and a reading of each target model of the commitments as a source
model.  The satisfaction condition is required at models of the commitments
only.  Commitments are carried along signature morphisms up to consequence,
and the model reading commutes with reducts. -/
structure TheoroidalComorphism
    (source : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      SourceSignature)
    (target : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      TargetSignature) where
  /-- The signature translation. -/
  mapSignature : SourceSignature ⥤ TargetSignature
  /-- The natural sentence translation. -/
  mapSentence : source.sentence ⟶ mapSignature ⋙ target.sentence
  /-- What the target must assume at each translated signature. -/
  commitments : (signature : SourceSignature) →
    Set (target.sentence.obj (mapSignature.obj signature))
  /-- Translated commitments are consequences of the commitments. -/
  commitments_natural : ∀ {first second : SourceSignature} (map : first ⟶ second),
    target.sentence.map (mapSignature.map map) '' commitments first ⊆
      target.semanticConsequence (mapSignature.obj second) (commitments second)
  /-- A model of the commitments read as a source model. -/
  mapModel : (signature : SourceSignature) →
    (targetModel : target.model.obj (Opposite.op (mapSignature.obj signature))) →
    target.SatisfiesAll (mapSignature.obj signature) targetModel (commitments signature) →
    source.model.obj (Opposite.op signature)
  /-- Reading commutes with reducts. -/
  mapModel_natural : ∀ {first second : SourceSignature} (map : first ⟶ second)
    (targetModel : target.model.obj (Opposite.op (mapSignature.obj second)))
    (committed : target.SatisfiesAll (mapSignature.obj second) targetModel
      (commitments second))
    (reductCommitted : target.SatisfiesAll (mapSignature.obj first)
      (target.reduct (mapSignature.map map) targetModel) (commitments first)),
    mapModel first (target.reduct (mapSignature.map map) targetModel) reductCommitted =
      source.reduct map (mapModel second targetModel committed)
  /-- The satisfaction condition at models of the commitments. -/
  satisfaction_condition : ∀ (signature : SourceSignature)
    (targetModel : target.model.obj (Opposite.op (mapSignature.obj signature)))
    (committed : target.SatisfiesAll (mapSignature.obj signature) targetModel
      (commitments signature))
    (sentence : source.sentence.obj signature),
    target.satisfies (mapSignature.obj signature) targetModel
        (mapSentence.app signature sentence) ↔
      source.satisfies signature (mapModel signature targetModel committed) sentence

namespace TheoroidalComorphism

variable {source : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
    SourceSignature}
  {target : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
    TargetSignature}

/-- The reading of a model depends on the model only. -/
theorem mapModel_congr (translation : TheoroidalComorphism source target)
    {signature : SourceSignature}
    {first second : target.model.obj (Opposite.op (translation.mapSignature.obj signature))}
    (equal : first = second)
    (firstCommitted : target.SatisfiesAll _ first (translation.commitments signature))
    (secondCommitted : target.SatisfiesAll _ second (translation.commitments signature)) :
    translation.mapModel signature first firstCommitted =
      translation.mapModel signature second secondCommitted := by
  subst equal
  rfl

/-! ### Transport -/

/-- **Transport.**  A source consequence becomes a target consequence of the
translated premises together with the commitments. -/
theorem entails_transport (translation : TheoroidalComorphism source target)
    (signature : SourceSignature) {premises : Set (source.sentence.obj signature)}
    {conclusion : source.sentence.obj signature}
    (entails : source.Entails signature premises conclusion) :
    target.Entails (translation.mapSignature.obj signature)
      (translation.mapSentence.app signature '' premises ∪ translation.commitments signature)
      (translation.mapSentence.app signature conclusion) := by
  intro targetModel satisfied
  have committed : target.SatisfiesAll _ targetModel (translation.commitments signature) :=
    fun sentence member => satisfied sentence (Or.inr member)
  rw [translation.satisfaction_condition signature targetModel committed]
  apply entails
  intro premise member
  rw [← translation.satisfaction_condition signature targetModel committed]
  exact satisfied _ (Or.inl ⟨premise, member, rfl⟩)

/-- Every source model is the reading of some model of the commitments. -/
def CoversModels (translation : TheoroidalComorphism source target) : Prop :=
  ∀ (signature : SourceSignature) (sourceModel : source.model.obj (Opposite.op signature)),
    ∃ (targetModel : target.model.obj (Opposite.op (translation.mapSignature.obj signature)))
      (committed : target.SatisfiesAll _ targetModel (translation.commitments signature)),
      translation.mapModel signature targetModel committed = sourceModel

/-- **Exact transport.**  When the readings of the models of the commitments
cover every source model, transport neither loses nor creates source
consequences. -/
theorem entails_iff_of_coversModels (translation : TheoroidalComorphism source target)
    (coverage : translation.CoversModels) (signature : SourceSignature)
    (premises : Set (source.sentence.obj signature)) (conclusion : source.sentence.obj signature) :
    source.Entails signature premises conclusion ↔
      target.Entails (translation.mapSignature.obj signature)
        (translation.mapSentence.app signature '' premises ∪ translation.commitments signature)
        (translation.mapSentence.app signature conclusion) := by
  refine ⟨translation.entails_transport signature, ?_⟩
  intro targetEntails sourceModel satisfiesPremises
  obtain ⟨targetModel, committed, read⟩ := coverage signature sourceModel
  have targetSatisfies := targetEntails targetModel <| by
    intro sentence member
    rcases member with ⟨premise, premiseMember, rfl⟩ | commitment
    · rw [translation.satisfaction_condition signature targetModel committed, read]
      exact satisfiesPremises premise premiseMember
    · exact committed sentence commitment
  rw [translation.satisfaction_condition signature targetModel committed, read] at targetSatisfies
  exact targetSatisfies

/-! ### Commitments are forced -/

/-- A target model is **readable** along a sentence translation when some
source model satisfies exactly the source sentences whose translations it
satisfies. -/
def Readable {Signature' : Type uSignature} [Category.{uSignatureHom} Signature']
    {signature : SourceSignature} {signature' : Signature'}
    {institution' : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      Signature'}
    (translate : source.sentence.obj signature → institution'.sentence.obj signature')
    (targetModel : institution'.model.obj (Opposite.op signature')) : Prop :=
  ∃ sourceModel : source.model.obj (Opposite.op signature),
    ∀ sentence, institution'.satisfies signature' targetModel (translate sentence) ↔
      source.satisfies signature sourceModel sentence

/-- Every model of the commitments is readable: its reading is a witness. -/
theorem commitmentModel_readable (translation : TheoroidalComorphism source target)
    (signature : SourceSignature)
    {targetModel : target.model.obj (Opposite.op (translation.mapSignature.obj signature))}
    (committed : target.SatisfiesAll _ targetModel (translation.commitments signature)) :
    Readable (source := source) (signature := signature)
      (translation.mapSentence.app signature) targetModel :=
  ⟨translation.mapModel signature targetModel committed,
    translation.satisfaction_condition signature targetModel committed⟩

/-- **Commitments are forced.**  A target sentence true in every readable
target model follows from the commitments of every theoroidal comorphism with
that sentence translation. -/
theorem entails_of_readable (translation : TheoroidalComorphism source target)
    (signature : SourceSignature)
    {sentence : target.sentence.obj (translation.mapSignature.obj signature)}
    (holds : ∀ targetModel, Readable (source := source) (signature := signature)
      (translation.mapSentence.app signature) targetModel →
        target.satisfies _ targetModel sentence) :
    target.Entails _ (translation.commitments signature) sentence :=
  fun _ committed => holds _ (translation.commitmentModel_readable signature committed)

/-- **Least commitments.**  Whatever holds in every readable target model is
a consequence of the commitments.  So a theoroidal comorphism whose
commitments hold in every readable model has the least commitments, up to
consequence, among those with its sentence translation. -/
theorem semanticConsequence_subset_of_readable
    (translation : TheoroidalComorphism source target) (signature : SourceSignature)
    {sentences : Set (target.sentence.obj (translation.mapSignature.obj signature))}
    (holds : ∀ targetModel, Readable (source := source) (signature := signature)
      (translation.mapSentence.app signature) targetModel →
        target.SatisfiesAll _ targetModel sentences) :
    target.semanticConsequence _ sentences ⊆
      target.semanticConsequence _ (translation.commitments signature) :=
  fun _ entailed => translation.entails_of_readable signature
    fun targetModel readable => entailed targetModel (holds targetModel readable)

/-! ### Plain comorphisms, identities and composites -/

/-- A comorphism is a theoroidal comorphism without commitments. -/
def ofComorphism (comorphism : Comorphism source target) : TheoroidalComorphism source target where
  mapSignature := comorphism.mapSignature
  mapSentence := comorphism.mapSentence
  commitments _ := ∅
  commitments_natural _ := by
    rw [Set.image_empty]
    exact Set.empty_subset _
  mapModel signature targetModel _ :=
    (comorphism.mapModel.app (Opposite.op signature)).toFunctor.obj targetModel
  mapModel_natural map targetModel _ _ :=
    congrArg (fun reading => reading.toFunctor.obj targetModel)
      (comorphism.mapModel.naturality map.op)
  satisfaction_condition signature targetModel _ sentence :=
    comorphism.satisfaction_condition signature targetModel sentence

@[simp] theorem ofComorphism_commitments (comorphism : Comorphism source target)
    (signature : SourceSignature) :
    (ofComorphism comorphism).commitments signature = ∅ := rfl

/-- Without commitments, transport is the forward half of the comorphism's
satisfaction-preservation: the translated premises alone suffice. -/
theorem ofComorphism_entails_transport (comorphism : Comorphism source target)
    (signature : SourceSignature) {premises : Set (source.sentence.obj signature)}
    {conclusion : source.sentence.obj signature}
    (entails : source.Entails signature premises conclusion) :
    target.Entails (comorphism.mapSignature.obj signature)
      (comorphism.mapSentence.app signature '' premises)
      (comorphism.mapSentence.app signature conclusion) := by
  have transported := (ofComorphism comorphism).entails_transport signature entails
  rw [ofComorphism_commitments, Set.union_empty] at transported
  exact transported

/-- Coverage of the plain comorphism is coverage of its theoroidal form. -/
theorem ofComorphism_coversModels_iff (comorphism : Comorphism source target) :
    (ofComorphism comorphism).CoversModels ↔ comorphism.CoversModels := by
  constructor
  · intro coverage signature sourceModel
    obtain ⟨targetModel, _, read⟩ := coverage signature sourceModel
    exact ⟨targetModel, read⟩
  · intro coverage signature sourceModel
    obtain ⟨targetModel, read⟩ := coverage signature sourceModel
    exact ⟨targetModel, fun _ member => member.elim, read⟩

/-- The identity translation, with no commitments. -/
def identity {Signature : Type uSignature} [Category.{uSignatureHom} Signature]
    (institution : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      Signature) :
    TheoroidalComorphism institution institution :=
  ofComorphism (Comorphism.identity institution)

@[simp] theorem identity_commitments {Signature : Type uSignature}
    [Category.{uSignatureHom} Signature]
    (institution : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      Signature) (signature : Signature) :
    (identity institution).commitments signature = ∅ := rfl

section Composition

variable {FirstSignature MiddleSignature LastSignature : Type uSignature}
  [Category.{uSignatureHom} FirstSignature] [Category.{uSignatureHom} MiddleSignature]
  [Category.{uSignatureHom} LastSignature]
  {first : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} FirstSignature}
  {middle : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
    MiddleSignature}
  {last : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} LastSignature}

/-- The commitments of a composite: the later leg's at the image signature and
the translations of the earlier leg's. -/
def compCommitments (earlier : TheoroidalComorphism first middle)
    (later : TheoroidalComorphism middle last) (signature : FirstSignature) :
    Set (last.sentence.obj (later.mapSignature.obj (earlier.mapSignature.obj signature))) :=
  later.commitments (earlier.mapSignature.obj signature) ∪
    later.mapSentence.app (earlier.mapSignature.obj signature) '' earlier.commitments signature

/-- A model of the composite's commitments satisfies the later leg's. -/
theorem compCommitments_later (earlier : TheoroidalComorphism first middle)
    (later : TheoroidalComorphism middle last) {signature : FirstSignature}
    {targetModel : last.model.obj
      (Opposite.op (later.mapSignature.obj (earlier.mapSignature.obj signature)))}
    (committed : last.SatisfiesAll _ targetModel (compCommitments earlier later signature)) :
    last.SatisfiesAll _ targetModel (later.commitments (earlier.mapSignature.obj signature)) :=
  fun sentence member => committed sentence (Or.inl member)

/-- The later leg's reading of a model of the composite's commitments
satisfies the earlier leg's commitments. -/
theorem compCommitments_earlier (earlier : TheoroidalComorphism first middle)
    (later : TheoroidalComorphism middle last) {signature : FirstSignature}
    {targetModel : last.model.obj
      (Opposite.op (later.mapSignature.obj (earlier.mapSignature.obj signature)))}
    (committed : last.SatisfiesAll _ targetModel (compCommitments earlier later signature)) :
    middle.SatisfiesAll _
      (later.mapModel (earlier.mapSignature.obj signature) targetModel
        (compCommitments_later earlier later committed))
      (earlier.commitments signature) := by
  intro sentence member
  exact (later.satisfaction_condition _ targetModel _ sentence).mp
    (committed _ (Or.inr ⟨sentence, member, rfl⟩))

/-- Pointwise naturality of a sentence translation. -/
theorem mapSentence_naturality (translation : TheoroidalComorphism source target)
    {firstSignature secondSignature : SourceSignature} (map : firstSignature ⟶ secondSignature)
    (sentence : source.sentence.obj firstSignature) :
    translation.mapSentence.app secondSignature (source.sentence.map map sentence) =
      target.sentence.map (translation.mapSignature.map map)
        (translation.mapSentence.app firstSignature sentence) :=
  ConcreteCategory.congr_hom (translation.mapSentence.naturality map) sentence

/-- **Composition.**  Sentence translations and signature maps compose
forward, readings compose backward, and commitments accumulate. -/
def comp (earlier : TheoroidalComorphism first middle)
    (later : TheoroidalComorphism middle last) : TheoroidalComorphism first last where
  mapSignature := earlier.mapSignature ⋙ later.mapSignature
  mapSentence := earlier.mapSentence ≫
    Functor.whiskerLeft earlier.mapSignature later.mapSentence
  commitments := compCommitments earlier later
  commitments_natural := by
    intro firstSignature secondSignature map sentence member
    rcases member with ⟨commitment, commitmentMember, rfl⟩
    rcases commitmentMember with laterMember | ⟨earlierCommitment, earlierMember, rfl⟩
    · have carried := later.commitments_natural (earlier.mapSignature.map map)
        ⟨commitment, laterMember, rfl⟩
      exact (last.semanticConsequence _).monotone Set.subset_union_left carried
    · have middleEntailed := earlier.commitments_natural map
        ⟨earlierCommitment, earlierMember, rfl⟩
      have transported := later.entails_transport (earlier.mapSignature.obj secondSignature)
        middleEntailed
      have rewritten : last.sentence.map (later.mapSignature.map (earlier.mapSignature.map map))
          (later.mapSentence.app (earlier.mapSignature.obj firstSignature) earlierCommitment) =
          later.mapSentence.app (earlier.mapSignature.obj secondSignature)
            (middle.sentence.map (earlier.mapSignature.map map) earlierCommitment) :=
        (later.mapSentence_naturality (earlier.mapSignature.map map) earlierCommitment).symm
      change last.Entails _ _ (last.sentence.map
        (later.mapSignature.map (earlier.mapSignature.map map))
          (later.mapSentence.app (earlier.mapSignature.obj firstSignature) earlierCommitment))
      rw [rewritten]
      refine (last.semanticConsequence _).monotone ?_ transported
      rw [Set.union_comm]
      rfl
  mapModel signature targetModel committed :=
    earlier.mapModel signature
      (later.mapModel (earlier.mapSignature.obj signature) targetModel
        (compCommitments_later earlier later committed))
      (compCommitments_earlier earlier later committed)
  mapModel_natural := by
    intro firstSignature secondSignature map targetModel committed reductCommitted
    have laterNatural := later.mapModel_natural (earlier.mapSignature.map map) targetModel
      (compCommitments_later earlier later committed)
      (compCommitments_later earlier later reductCommitted)
    have earlierCommitted : middle.SatisfiesAll _
        (middle.reduct (earlier.mapSignature.map map)
          (later.mapModel (earlier.mapSignature.obj secondSignature) targetModel
            (compCommitments_later earlier later committed)))
        (earlier.commitments firstSignature) :=
      laterNatural ▸ compCommitments_earlier earlier later reductCommitted
    calc earlier.mapModel firstSignature
          (later.mapModel (earlier.mapSignature.obj firstSignature)
            (last.reduct (later.mapSignature.map (earlier.mapSignature.map map)) targetModel)
            (compCommitments_later earlier later reductCommitted))
          (compCommitments_earlier earlier later reductCommitted)
        = earlier.mapModel firstSignature
            (middle.reduct (earlier.mapSignature.map map)
              (later.mapModel (earlier.mapSignature.obj secondSignature) targetModel
                (compCommitments_later earlier later committed)))
            earlierCommitted :=
          earlier.mapModel_congr laterNatural _ _
      _ = first.reduct map (earlier.mapModel secondSignature
            (later.mapModel (earlier.mapSignature.obj secondSignature) targetModel
              (compCommitments_later earlier later committed))
            (compCommitments_earlier earlier later committed)) :=
          earlier.mapModel_natural map _ _ _
  satisfaction_condition signature targetModel committed sentence :=
    (later.satisfaction_condition (earlier.mapSignature.obj signature) targetModel
      (compCommitments_later earlier later committed)
      (earlier.mapSentence.app signature sentence)).trans
      (earlier.satisfaction_condition signature _
        (compCommitments_earlier earlier later committed) sentence)

/-- The commitments of a composite, explicitly. -/
theorem comp_commitments (earlier : TheoroidalComorphism first middle)
    (later : TheoroidalComorphism middle last) (signature : FirstSignature) :
    (earlier.comp later).commitments signature =
      later.commitments (earlier.mapSignature.obj signature) ∪
        later.mapSentence.app (earlier.mapSignature.obj signature) ''
          earlier.commitments signature := rfl

/-- Composing two plain comorphisms adds no commitment. -/
theorem ofComorphism_comp_commitments (earlier : Comorphism first middle)
    (later : Comorphism middle last) (signature : FirstSignature) :
    ((ofComorphism earlier).comp (ofComorphism later)).commitments signature = ∅ := by
  rw [comp_commitments, ofComorphism_commitments, ofComorphism_commitments,
    Set.image_empty, Set.union_empty]
  rfl

end Composition

/-! ### Routes and kernels -/

/-- At a fixed signature and premise set, transport is a route from the source
theory to the target theory of the translated premises and the commitments. -/
def transportRoute (translation : TheoroidalComorphism source target)
    (signature : SourceSignature) (premises : Set (source.sentence.obj signature)) :
    TheoryRoute (source.semanticConsequence signature premises)
      (target.semanticConsequence (translation.mapSignature.obj signature)
        (translation.mapSentence.app signature '' premises ∪
          translation.commitments signature)) where
  translate := translation.mapSentence.app signature
  preserves := fun _ entails => translation.entails_transport signature entails

/-- Under coverage the transport route is conservative: the commitments
certify no source sentence that the premises do not entail. -/
theorem transportRoute_conservative_of_coversModels
    (translation : TheoroidalComorphism source target) (coverage : translation.CoversModels)
    (signature : SourceSignature) (premises : Set (source.sentence.obj signature)) :
    (translation.transportRoute signature premises).Conservative := by
  intro sentence borrowed
  exact (translation.entails_iff_of_coversModels coverage signature premises sentence).mpr borrowed

/-- A pair of entailment systems **carries theorems** along a theoroidal
comorphism when every source theorem's translation is a target theorem of the
translated premises and the commitments.  A translation of proofs establishes
this directly; `kernel_transport` obtains it from soundness and completeness. -/
def CarriesTheorems (translation : TheoroidalComorphism source target)
    (sourceSystem : EntailmentSystem source) (targetSystem : EntailmentSystem target) : Prop :=
  ∀ (signature : SourceSignature) (premises : Set (source.sentence.obj signature))
    (conclusion : source.sentence.obj signature),
    conclusion ∈ sourceSystem.consequence signature premises →
      translation.mapSentence.app signature conclusion ∈
        targetSystem.consequence (translation.mapSignature.obj signature)
          (translation.mapSentence.app signature '' premises ∪
            translation.commitments signature)

/-- **Kernel transport.**  A sound source system and a complete target system
carry theorems along every theoroidal comorphism. -/
theorem kernel_transport (translation : TheoroidalComorphism source target)
    {sourceSystem : EntailmentSystem source} {targetSystem : EntailmentSystem target}
    (sound : sourceSystem.Sound) (complete : targetSystem.Complete) :
    translation.CarriesTheorems sourceSystem targetSystem :=
  fun signature premises _ derived =>
    complete _ _ (translation.entails_transport signature (sound signature premises derived))

/-- A carried theorem of a sound target system is a semantic target
consequence: what a carrying pair proves about translated sentences holds in
every model of the commitments and the translated premises. -/
theorem carried_entails (translation : TheoroidalComorphism source target)
    {sourceSystem : EntailmentSystem source} {targetSystem : EntailmentSystem target}
    (carries : translation.CarriesTheorems sourceSystem targetSystem)
    (targetSound : targetSystem.Sound) {signature : SourceSignature}
    {premises : Set (source.sentence.obj signature)} {conclusion : source.sentence.obj signature}
    (derived : conclusion ∈ sourceSystem.consequence signature premises) :
    target.Entails (translation.mapSignature.obj signature)
      (translation.mapSentence.app signature '' premises ∪ translation.commitments signature)
      (translation.mapSentence.app signature conclusion) :=
  targetSound _ _ (carries signature premises conclusion derived)

end TheoroidalComorphism

end Institution

/-! ## Control: function extensionality as a commitment -/

namespace TheoroidalComorphismControl

open Mettapedia.Logic.InstitutionCanary (OneSignature)
open Institution

/-- Sentences about a pair of Boolean functions: they agree at an argument;
they are equal. -/
inductive PairSentence where
  | agreeAt (argument : Bool)
  | equal

/-- The source sentences over the unique signature. -/
def pairCarrier : OneSignature ⥤ Type where
  obj _ := PairSentence
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Source models: two Boolean functions. -/
abbrev FunctionPair := (Bool → Bool) × (Bool → Bool)

/-- Functions are compared extensionally. -/
def functionSatisfies (model : FunctionPair) : PairSentence → Prop
  | .agreeAt argument => model.1 argument = model.2 argument
  | .equal => model.1 = model.2

/-- The constant model category of function pairs. -/
def functionModels : OneSignatureᵒᵖ ⥤ Cat :=
  (Functor.const OneSignatureᵒᵖ).obj (Cat.of (Discrete FunctionPair))

/-- The source logic: equality of functions is extensional in every model. -/
def extensionalLogic : Institution OneSignature where
  sentence := pairCarrier
  model := functionModels
  satisfies _ model sentence :=
    functionSatisfies (show Discrete FunctionPair from model).as sentence
  satisfaction_condition := by
    intro _ _ _ targetModel sentence
    exact Iff.rfl

/-- A code for a Boolean function: its value at `true`, its value at `false`,
and a tag that the values ignore. -/
abbrev Code := Bool × Bool × Bool

/-- The function a code computes. -/
def Code.apply (code : Code) (argument : Bool) : Bool :=
  if argument then code.1 else code.2.1

/-- Target sentences: agreement, equality of codes, and extensionality. -/
inductive CodeSentence where
  | agreeAt (argument : Bool)
  | equal
  | extensional

/-- The target sentences over the unique signature. -/
def codeCarrier : OneSignature ⥤ Type where
  obj _ := CodeSentence
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Codes are compared as codes. -/
def codeSatisfies (model : Code × Code) : CodeSentence → Prop
  | .agreeAt argument => model.1.apply argument = model.2.apply argument
  | .equal => model.1 = model.2
  | .extensional => (∀ argument, model.1.apply argument = model.2.apply argument) →
      model.1 = model.2

/-- The constant model category of code pairs. -/
def codeModels : OneSignatureᵒᵖ ⥤ Cat :=
  (Functor.const OneSignatureᵒᵖ).obj (Cat.of (Discrete (Code × Code)))

/-- The target logic: equality of codes is intensional. -/
def intensionalLogic : Institution OneSignature where
  sentence := codeCarrier
  model := codeModels
  satisfies _ model sentence :=
    codeSatisfies (show Discrete (Code × Code) from model).as sentence
  satisfaction_condition := by
    intro _ _ _ targetModel sentence
    exact Iff.rfl

/-- The sentence translation: agreement to agreement, equality to equality. -/
def embed : PairSentence → CodeSentence
  | .agreeAt argument => .agreeAt argument
  | .equal => .equal

/-- The sentence translation as a natural transformation. -/
def embedSentence : pairCarrier ⟶ 𝟭 OneSignature ⋙ codeCarrier where
  app _ := TypeCat.ofHom embed
  naturality := by
    intro _ _ _
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext sentence
    rfl

/-- Two codes with equal values and different tags. -/
def twinCodes : Code × Code := ((true, false, false), (true, false, true))

theorem twinCodes_agree (argument : Bool) :
    twinCodes.1.apply argument = twinCodes.2.apply argument := by
  cases argument <;> rfl

theorem twinCodes_ne : twinCodes.1 ≠ twinCodes.2 := by
  intro equal
  have tags := congrArg (fun code : Code => code.2.2) equal
  exact Bool.false_ne_true tags

/-- **No comorphism has this sentence translation.**  The twin codes satisfy
both translated agreements and not translated equality; their reading would
be a pair of functions agreeing everywhere and unequal. -/
theorem no_comorphism (comorphism : Comorphism extensionalLogic intensionalLogic)
    (translates : ∀ sentence : PairSentence,
      comorphism.mapSentence.app (Discrete.mk ()) sentence = embed sentence) : False := by
  let twins : intensionalLogic.model.obj
      (Opposite.op (comorphism.mapSignature.obj (Discrete.mk ()))) := Discrete.mk twinCodes
  let reading : FunctionPair :=
    (show Discrete FunctionPair from
      (comorphism.mapModel.app (Opposite.op (Discrete.mk ()))).toFunctor.obj twins).as
  have agree : ∀ argument, reading.1 argument = reading.2 argument := by
    intro argument
    have condition := comorphism.satisfaction_condition (Discrete.mk ()) twins
      (PairSentence.agreeAt argument)
    rw [translates] at condition
    exact condition.mp (twinCodes_agree argument)
  have unequal : ¬ reading.1 = reading.2 := by
    intro equal
    have condition := comorphism.satisfaction_condition (Discrete.mk ()) twins
      PairSentence.equal
    rw [translates] at condition
    exact twinCodes_ne (condition.mpr equal)
  exact unequal (funext agree)

/-- Read a pair of codes as the pair of functions they compute. -/
def readCodes (model : Code × Code) : FunctionPair := (model.1.apply, model.2.apply)

/-- **With the extensionality commitment the translation is theoroidal.**
The commitment says that codes agreeing at every argument are equal. -/
def withExtensionality : TheoroidalComorphism extensionalLogic intensionalLogic where
  mapSignature := 𝟭 OneSignature
  mapSentence := embedSentence
  commitments _ := {CodeSentence.extensional}
  commitments_natural _ := by
    rintro _ ⟨sentence, member, rfl⟩
    intro model satisfied
    exact satisfied sentence member
  mapModel _ targetModel _ :=
    Discrete.mk (readCodes (show Discrete (Code × Code) from targetModel).as)
  mapModel_natural _ _ _ _ := rfl
  satisfaction_condition _ targetModel committed sentence := by
    cases sentence with
    | agreeAt argument => exact Iff.rfl
    | equal =>
        have extensional := committed CodeSentence.extensional rfl
        change (show Discrete (Code × Code) from targetModel).as.1 =
            (show Discrete (Code × Code) from targetModel).as.2 ↔
          (show Discrete (Code × Code) from targetModel).as.1.apply =
            (show Discrete (Code × Code) from targetModel).as.2.apply
        constructor
        · intro equal
          rw [equal]
        · intro equal
          exact extensional (fun argument => congrFun equal argument)

theorem withExtensionality_commitments (signature : OneSignature) :
    withExtensionality.commitments signature = {CodeSentence.extensional} := rfl

/-- Every target model readable along the translation is extensional: a
source reading of two codes that agree everywhere is a pair of functions that
agree everywhere, hence equal, so the codes satisfy translated equality. -/
theorem readable_extensional
    (translation : TheoroidalComorphism extensionalLogic intensionalLogic)
    (translates : ∀ sentence : PairSentence,
      translation.mapSentence.app (Discrete.mk ()) sentence = embed sentence)
    (targetModel : intensionalLogic.model.obj
      (Opposite.op (translation.mapSignature.obj (Discrete.mk ()))))
    (readable : TheoroidalComorphism.Readable (source := extensionalLogic)
      (signature := Discrete.mk ()) (translation.mapSentence.app (Discrete.mk ())) targetModel) :
    intensionalLogic.satisfies _ targetModel CodeSentence.extensional := by
  obtain ⟨sourceModel, readable⟩ := readable
  intro agree
  have agreement : ∀ argument,
      (show Discrete FunctionPair from sourceModel).as.1 argument =
        (show Discrete FunctionPair from sourceModel).as.2 argument := by
    intro argument
    have condition := readable (PairSentence.agreeAt argument)
    rw [translates] at condition
    exact condition.mp (agree argument)
  have condition := readable PairSentence.equal
  rw [translates] at condition
  exact condition.mpr (funext agreement)

/-- **Extensionality is forced.**  The commitments of every theoroidal
comorphism with this sentence translation entail extensionality. -/
theorem commitments_entail_extensional
    (translation : TheoroidalComorphism extensionalLogic intensionalLogic)
    (translates : ∀ sentence : PairSentence,
      translation.mapSentence.app (Discrete.mk ()) sentence = embed sentence) :
    intensionalLogic.Entails (translation.mapSignature.obj (Discrete.mk ()))
      (translation.commitments (Discrete.mk ())) CodeSentence.extensional :=
  translation.entails_of_readable (Discrete.mk ())
    (readable_extensional translation translates)

/-- **Extensionality is the least commitment.**  Every consequence of the
extensionality commitment of `withExtensionality` follows from the
commitments of any theoroidal comorphism with the same sentence translation. -/
theorem extensionality_least
    (translation : TheoroidalComorphism extensionalLogic intensionalLogic)
    (translates : ∀ sentence : PairSentence,
      translation.mapSentence.app (Discrete.mk ()) sentence = embed sentence) :
    intensionalLogic.semanticConsequence (translation.mapSignature.obj (Discrete.mk ()))
        {CodeSentence.extensional} ⊆
      intensionalLogic.semanticConsequence (translation.mapSignature.obj (Discrete.mk ()))
        (translation.commitments (Discrete.mk ())) :=
  translation.semanticConsequence_subset_of_readable (Discrete.mk ()) fun targetModel readable =>
    fun _ member => member ▸ readable_extensional translation translates targetModel readable

/-- The source theorem: agreement at both arguments gives equality. -/
theorem source_extensionality :
    extensionalLogic.Entails (Discrete.mk ())
      {PairSentence.agreeAt true, PairSentence.agreeAt false} PairSentence.equal := by
  intro model satisfied
  have atTrue := satisfied (PairSentence.agreeAt true) (Or.inl rfl)
  have atFalse := satisfied (PairSentence.agreeAt false) (Or.inr rfl)
  change (show Discrete FunctionPair from model).as.1 = (show Discrete FunctionPair from model).as.2
  funext argument
  cases argument
  · exact atFalse
  · exact atTrue

/-- **Transport carries the commitment as a premise.** -/
theorem transport_uses_commitment :
    intensionalLogic.Entails ((𝟭 OneSignature).obj (Discrete.mk ()))
      (embed '' {PairSentence.agreeAt true, PairSentence.agreeAt false} ∪
        {CodeSentence.extensional})
      CodeSentence.equal :=
  withExtensionality.entails_transport (Discrete.mk ()) source_extensionality

/-- **Without the commitment the translated theorem fails** at the twin codes. -/
theorem transport_fails_without_commitment :
    ¬ intensionalLogic.Entails ((𝟭 OneSignature).obj (Discrete.mk ()))
      (embed '' {PairSentence.agreeAt true, PairSentence.agreeAt false})
      CodeSentence.equal := by
  intro entails
  have twinsEqual := entails (Discrete.mk twinCodes) <| by
    rintro sentence ⟨original, member, rfl⟩
    rcases member with rfl | rfl
    · exact twinCodes_agree true
    · exact twinCodes_agree false
  exact twinCodes_ne twinsEqual

/-- Positive control: the identity translation of the extensional logic
needs no commitment and transports the same theorem unchanged. -/
theorem identity_transport :
    extensionalLogic.Entails ((TheoroidalComorphism.identity extensionalLogic).mapSignature.obj (Discrete.mk ()))
      ((TheoroidalComorphism.identity extensionalLogic).mapSentence.app (Discrete.mk ()) ''
          {PairSentence.agreeAt true, PairSentence.agreeAt false} ∪
        (TheoroidalComorphism.identity extensionalLogic).commitments (Discrete.mk ()))
      ((TheoroidalComorphism.identity extensionalLogic).mapSentence.app (Discrete.mk ()) PairSentence.equal) :=
  (TheoroidalComorphism.identity extensionalLogic).entails_transport (Discrete.mk ()) source_extensionality

end TheoroidalComorphismControl

end Mettapedia.Logic
