import Mettapedia.Logic.TheoryModel.InstitutionBridge
import Mettapedia.Logic.TheoryModel.Weakness
import Mettapedia.Logic.Consequence.PiInstitution

/-!
# Borrowing consequence along comorphisms, and choosing among routes

A route from one logic to another translates sentences and preserves
theorems.  What the target certifies about source sentences is the
**borrowed theory** of the route: the source sentences whose translations the
target proves.  It always contains the source theory.  The route is
**conservative** when it contains nothing more; otherwise the difference is
the set of **commitments the route adds** (`TheoryRoute`).

**Borrowing** (Cerioli and Meseguer, "May I borrow your logic?").  For an
institution comorphism, the borrowed theory of a source theory is its
consequence computed among the reducts of target models
(`borrowed_ofComorphism`).  Given an entailment system of the target logic,
pulling it back along the comorphism gives an entailment system of the source
logic (`borrow`):

* it is always complete when the target system is (`borrow_complete`);
* it is sound when the comorphism is conservative and the target system is
  sound (`borrow_sound_of_conservative`), and, for a sound and complete target
  system, it is sound exactly when the comorphism is conservative
  (`borrow_sound_iff_conservative`);
* along a conservative comorphism a decision procedure for target consequence
  decides source consequence (`decideEntails`).

Negative control: borrowing the collapsing comorphism's target consequence
derives `true` from `false`, which the source does not entail
(`Control.collapse_borrows_false_conclusion`).

**Choosing a route.**  Routes out of one source theory are compared by their
borrowed theories, which live in the source logic: comparison across logics is
made after translating back (`FewerCommitments`).  A conservative route is
below every route (`Conservative.fewerCommitments`), and a route below the
identity is conservative.  A composite keeps every commitment of its first leg
(`borrowed_subset_comp`), adds exactly the pullback of the second leg's
commitments (`addedCommitments_comp`), and adds nothing through a
conservative second leg (`borrowed_comp_of_conservative`).  A composite is
conservative exactly when its first leg is and its second leg reflects
theoremhood on the first leg's image (`conservative_comp_iff`): for a route
through a framework, adequacy of the framework encoding plus conservativity of
the framework's interpretation on that image.  For a monotone
weakness measure of model classes, fewer commitments mean at least as much
weakness, and a conservative route keeps the source theory's weakness
(`weakness_le_of_fewerCommitments`, `Conservative.weakness_eq`).

Control: two routes that restrict a three-structure logic to one structure
each borrow incomparable theories of equal cardinal weakness, so the least
commitments need not be unique among non-conservative routes, while the route
to the region of both structures is conservative and below both
(`Control.incomparable_optima`, `Control.region_route_conservative`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.InstitutionBorrowing

open CategoryTheory
open Mettapedia.Logic.TheoryModel

universe uS uS' uS'' uSignature uSignatureHom uSentence uModel uModelHom uStr uW

/-! ## Routes between theories -/

/-- A route from one theory to another: a translation of sentences under which
every theorem of the source theory becomes a theorem of the target theory. -/
structure TheoryRoute {Sentence : Type uS} {Sentence' : Type uS'}
    (theory : Set Sentence) (theory' : Set Sentence') where
  /-- Translate a source sentence. -/
  translate : Sentence → Sentence'
  /-- Theorems are carried to theorems. -/
  preserves : ∀ ⦃sentence⦄, sentence ∈ theory → translate sentence ∈ theory'

namespace TheoryRoute

variable {Sentence : Type uS} {Sentence' : Type uS'} {Sentence'' : Type uS''}
  {theory : Set Sentence} {theory' : Set Sentence'} {theory'' : Set Sentence''}

/-- **The borrowed theory**: the source sentences the target certifies. -/
def borrowed (route : TheoryRoute theory theory') : Set Sentence :=
  route.translate ⁻¹' theory'

theorem mem_borrowed_iff (route : TheoryRoute theory theory') (sentence : Sentence) :
    sentence ∈ route.borrowed ↔ route.translate sentence ∈ theory' :=
  Iff.rfl

/-- Every source theorem is borrowed back. -/
theorem subset_borrowed (route : TheoryRoute theory theory') : theory ⊆ route.borrowed :=
  fun _ member => route.preserves member

/-- A route is conservative when the target certifies no source sentence that
the source theory lacks. -/
def Conservative (route : TheoryRoute theory theory') : Prop :=
  route.borrowed ⊆ theory

theorem conservative_iff_borrowed_eq (route : TheoryRoute theory theory') :
    route.Conservative ↔ route.borrowed = theory :=
  ⟨fun conservative => Set.Subset.antisymm conservative route.subset_borrowed,
    fun equal => equal.le⟩

/-- **The commitments a route adds**: sentences the target certifies and the
source does not prove. -/
def addedCommitments (route : TheoryRoute theory theory') : Set Sentence :=
  route.borrowed \ theory

theorem conservative_iff_addedCommitments_eq_empty (route : TheoryRoute theory theory') :
    route.Conservative ↔ route.addedCommitments = ∅ := by
  rw [addedCommitments, Set.sdiff_eq_empty]
  rfl

/-- A route that is not conservative certifies a sentence the source theory
does not contain: borrowing along it reaches a false conclusion. -/
theorem exists_unproved_of_not_conservative (route : TheoryRoute theory theory')
    (notConservative : ¬ route.Conservative) :
    ∃ sentence, route.translate sentence ∈ theory' ∧ sentence ∉ theory := by
  by_contra none
  apply notConservative
  intro sentence borrowedMember
  by_contra absent
  exact none ⟨sentence, borrowedMember, absent⟩

/-- **Borrowing a decision procedure**: along a conservative route, deciding
membership in the target theory decides membership in the source theory. -/
@[reducible] def decide (route : TheoryRoute theory theory') (conservative : route.Conservative)
    (decideTarget : DecidablePred (· ∈ theory')) : DecidablePred (· ∈ theory) :=
  fun sentence =>
    decidable_of_iff (route.translate sentence ∈ theory')
      ⟨fun certified => conservative certified, fun proved => route.preserves proved⟩

/-- The identity route. -/
def id (theory : Set Sentence) : TheoryRoute theory theory where
  translate sentence := sentence
  preserves _ member := member

theorem id_conservative (theory : Set Sentence) : (id theory).Conservative :=
  fun _ member => member

/-- Routes compose. -/
def comp (first : TheoryRoute theory theory') (second : TheoryRoute theory' theory'') :
    TheoryRoute theory theory'' where
  translate sentence := second.translate (first.translate sentence)
  preserves _ member := second.preserves (first.preserves member)

/-- **A composite keeps every commitment of its first leg.** -/
theorem borrowed_subset_comp (first : TheoryRoute theory theory')
    (second : TheoryRoute theory' theory'') :
    first.borrowed ⊆ (first.comp second).borrowed :=
  fun _ certified => second.preserves certified

/-- **A conservative second leg adds nothing.** -/
theorem borrowed_comp_of_conservative (first : TheoryRoute theory theory')
    {second : TheoryRoute theory' theory''} (conservative : second.Conservative) :
    (first.comp second).borrowed = first.borrowed :=
  Set.Subset.antisymm (fun _ certified => conservative certified)
    (first.borrowed_subset_comp second)

/-- **The commitments of a composite**: those of the first leg, and the source
sentences whose translations are commitments of the second leg. -/
theorem addedCommitments_comp (first : TheoryRoute theory theory')
    (second : TheoryRoute theory' theory'') :
    (first.comp second).addedCommitments =
      first.addedCommitments ∪ (first.translate ⁻¹' second.addedCommitments \ theory) := by
  ext sentence
  simp only [addedCommitments, borrowed, comp, Set.mem_sdiff, Set.mem_union, Set.mem_preimage]
  constructor
  · rintro ⟨certified, unproved⟩
    by_cases middle : first.translate sentence ∈ theory'
    · exact Or.inl ⟨middle, unproved⟩
    · exact Or.inr ⟨⟨certified, middle⟩, unproved⟩
  · rintro (⟨middle, unproved⟩ | ⟨⟨certified, _⟩, unproved⟩)
    · exact ⟨second.preserves middle, unproved⟩
    · exact ⟨certified, unproved⟩

theorem Conservative.comp {first : TheoryRoute theory theory'}
    {second : TheoryRoute theory' theory''} (firstConservative : first.Conservative)
    (secondConservative : second.Conservative) : (first.comp second).Conservative := by
  rw [Conservative, borrowed_comp_of_conservative first secondConservative]
  exact firstConservative

/-- **Conservativity of a composite**: a composite route is conservative exactly
when its first leg is conservative and its second leg reflects theoremhood on
the image of the first.  For a route through a framework, `K → FW(K) → C`, the
first condition is adequacy of the framework encoding and the second is
conservativity of the framework's interpretation on that encoding's image. -/
theorem conservative_comp_iff (first : TheoryRoute theory theory')
    (second : TheoryRoute theory' theory'') :
    (first.comp second).Conservative ↔
      first.Conservative ∧
        ∀ sentence, second.translate (first.translate sentence) ∈ theory'' →
          first.translate sentence ∈ theory' := by
  constructor
  · intro conservative
    exact ⟨fun _ translated => conservative (second.preserves translated),
      fun _ translated => first.preserves (conservative translated)⟩
  · rintro ⟨firstConservative, reflects⟩ sentence translated
    exact firstConservative (reflects sentence translated)

/-- A composite whose first leg is not conservative is not conservative. -/
theorem not_conservative_comp_of_first {first : TheoryRoute theory theory'}
    (second : TheoryRoute theory' theory'') (notConservative : ¬ first.Conservative) :
    ¬ (first.comp second).Conservative :=
  fun conservative => notConservative
    (Set.Subset.trans (first.borrowed_subset_comp second) conservative)

/-! ### Choosing among routes out of one theory -/

/-- `route` adds no commitment that `other` does not add.  Both borrowed
theories live in the source logic, so the comparison is made there. -/
def FewerCommitments (route : TheoryRoute theory theory') (other : TheoryRoute theory theory'') :
    Prop :=
  route.borrowed ⊆ other.borrowed

theorem FewerCommitments.refl (route : TheoryRoute theory theory') :
    route.FewerCommitments route :=
  Set.Subset.rfl

theorem FewerCommitments.trans {Sentence''' : Type uS} {theory''' : Set Sentence'''}
    {first : TheoryRoute theory theory'} {second : TheoryRoute theory theory''}
    {third : TheoryRoute theory theory'''} (earlier : first.FewerCommitments second)
    (later : second.FewerCommitments third) : first.FewerCommitments third :=
  Set.Subset.trans earlier later

/-- **A conservative route is below every route out of the same theory.** -/
theorem Conservative.fewerCommitments {route : TheoryRoute theory theory'}
    (conservative : route.Conservative) (other : TheoryRoute theory theory'') :
    route.FewerCommitments other :=
  Set.Subset.trans conservative other.subset_borrowed

/-- A route below the identity route is conservative. -/
theorem conservative_of_fewerCommitments_id {route : TheoryRoute theory theory'}
    (below : route.FewerCommitments (id theory)) : route.Conservative :=
  below

/-- A composite never has fewer commitments than its first leg. -/
theorem fewerCommitments_comp (first : TheoryRoute theory theory')
    (second : TheoryRoute theory' theory'') : first.FewerCommitments (first.comp second) :=
  first.borrowed_subset_comp second

/-! ### Weakness of a route -/

section Weakness

variable {Str : Type uStr} (Sat : Str → Sentence → Prop) {W : Type uW} [Preorder W]

/-- The weakness of a route under a measure of model classes: the weakness of
its borrowed theory in the source logic. -/
def weakness (μ : Set Str → W) (route : TheoryRoute theory theory') : W :=
  weaknessOf Sat μ route.borrowed

variable {Sat}

/-- **Fewer commitments, at least as much weakness.** -/
theorem weakness_le_of_fewerCommitments {μ : Set Str → W} (monotone : MonotoneMeasure μ)
    {route : TheoryRoute theory theory'} {other : TheoryRoute theory theory''}
    (fewer : route.FewerCommitments other) :
    weakness Sat μ other ≤ weakness Sat μ route :=
  weaknessOf_anti monotone fewer

/-- No route is weaker than its source theory. -/
theorem weakness_le_source {μ : Set Str → W} (monotone : MonotoneMeasure μ)
    (route : TheoryRoute theory theory') :
    weakness Sat μ route ≤ weaknessOf Sat μ theory :=
  weaknessOf_anti monotone route.subset_borrowed

omit [Preorder W] in
/-- **A conservative route keeps the source theory's weakness.** -/
theorem Conservative.weakness_eq {μ : Set Str → W} {route : TheoryRoute theory theory'}
    (conservative : route.Conservative) :
    weakness Sat μ route = weaknessOf Sat μ theory := by
  rw [weakness, (route.conservative_iff_borrowed_eq).mp conservative]

end Weakness

end TheoryRoute

/-! ## Comorphisms of institutions -/

section Institutions

variable {SourceSignature TargetSignature : Type uSignature}
  [Category.{uSignatureHom} SourceSignature] [Category.{uSignatureHom} TargetSignature]
  {source : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
    SourceSignature}
  {target : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
    TargetSignature}

/-- A comorphism is conservative when target consequence between translated
sentences implies source consequence. -/
def Conservative (comorphism : Institution.Comorphism source target) : Prop :=
  ∀ (signature : SourceSignature) (premises : Set (source.sentence.obj signature))
    (conclusion : source.sentence.obj signature),
    target.Entails (comorphism.mapSignature.obj signature)
        (comorphism.mapSentence.app signature '' premises)
        (comorphism.mapSentence.app signature conclusion) →
      source.Entails signature premises conclusion

/-- Satisfaction preservation alone transports consequence forward. -/
theorem entails_mapped (comorphism : Institution.Comorphism source target)
    (signature : SourceSignature) {premises : Set (source.sentence.obj signature)}
    {conclusion : source.sentence.obj signature}
    (entails : source.Entails signature premises conclusion) :
    target.Entails (comorphism.mapSignature.obj signature)
      (comorphism.mapSentence.app signature '' premises)
      (comorphism.mapSentence.app signature conclusion) := by
  intro model satisfied
  rw [comorphism.satisfaction_condition]
  apply entails
  intro premise member
  rw [← comorphism.satisfaction_condition]
  exact satisfied _ ⟨premise, member, rfl⟩

/-- **Borrowing**: along a conservative comorphism, source consequence is
target consequence between translations. -/
theorem entails_iff_of_conservative {comorphism : Institution.Comorphism source target}
    (conservative : Conservative comorphism) (signature : SourceSignature)
    (premises : Set (source.sentence.obj signature))
    (conclusion : source.sentence.obj signature) :
    source.Entails signature premises conclusion ↔
      target.Entails (comorphism.mapSignature.obj signature)
        (comorphism.mapSentence.app signature '' premises)
        (comorphism.mapSentence.app signature conclusion) :=
  ⟨entails_mapped comorphism signature, conservative signature premises conclusion⟩

/-- Coverage of models makes a comorphism conservative. -/
theorem conservative_of_coversModels {comorphism : Institution.Comorphism source target}
    (coverage : comorphism.CoversModels) : Conservative comorphism :=
  fun signature premises conclusion =>
    (comorphism.entails_mapped_iff_of_coversModels coverage signature premises conclusion).mpr

/-- Conservativity is faithful hosting by the universe of reducts, at every
signature and theory. -/
theorem conservative_iff_hostsFaithfully (comorphism : Institution.Comorphism source target) :
    Conservative comorphism ↔
      ∀ (signature : SourceSignature) (premises : Set (source.sentence.obj signature)),
        HostsFaithfully (source.satisfies signature)
          (InstitutionBridge.reductUniverse comorphism signature) premises := by
  constructor
  · intro conservative signature premises
    refine (InstitutionBridge.conservative_iff_hostsFaithfully comorphism signature premises).mp ?_
    intro conclusion
    exact ⟨entails_mapped comorphism signature, conservative signature premises conclusion⟩
  · intro faithful signature premises conclusion
    exact ((InstitutionBridge.conservative_iff_hostsFaithfully comorphism signature premises).mpr
      (faithful signature premises) conclusion).mpr

/-- **Borrowing a decision procedure.** -/
@[reducible] def decideEntails {comorphism : Institution.Comorphism source target}
    (conservative : Conservative comorphism)
    (decideTarget : ∀ (signature : TargetSignature) (premises : Set (target.sentence.obj signature))
      (conclusion : target.sentence.obj signature),
      Decidable (target.Entails signature premises conclusion))
    (signature : SourceSignature) (premises : Set (source.sentence.obj signature))
    (conclusion : source.sentence.obj signature) :
    Decidable (source.Entails signature premises conclusion) :=
  decidable_of_iff _ (entails_iff_of_conservative conservative signature premises conclusion).symm

theorem Conservative.comp
    {FirstSignature MiddleSignature LastSignature : Type uSignature}
    [Category.{uSignatureHom} FirstSignature] [Category.{uSignatureHom} MiddleSignature]
    [Category.{uSignatureHom} LastSignature]
    {first : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      FirstSignature}
    {middle : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      MiddleSignature}
    {last : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      LastSignature}
    {earlier : Institution.Comorphism first middle} {later : Institution.Comorphism middle last}
    (earlierConservative : Conservative earlier) (laterConservative : Conservative later) :
    Conservative (earlier.comp later) := by
  intro signature premises conclusion entails
  apply earlierConservative signature premises conclusion
  apply laterConservative _ _ _
  rw [Set.image_image]
  exact entails

/-- A composite through a non-conservative first leg is not conservative. -/
theorem conservative_of_comp
    {FirstSignature MiddleSignature LastSignature : Type uSignature}
    [Category.{uSignatureHom} FirstSignature] [Category.{uSignatureHom} MiddleSignature]
    [Category.{uSignatureHom} LastSignature]
    {first : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      FirstSignature}
    {middle : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      MiddleSignature}
    {last : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      LastSignature}
    {earlier : Institution.Comorphism first middle} (later : Institution.Comorphism middle last)
    (compositeConservative : Conservative (earlier.comp later)) :
    Conservative earlier := by
  intro signature premises conclusion entails
  apply compositeConservative signature premises conclusion
  have transported := entails_mapped later _ entails
  rw [Set.image_image] at transported
  exact transported

/-- The route that a comorphism gives at one signature and one theory. -/
def ofComorphism (comorphism : Institution.Comorphism source target)
    (signature : SourceSignature) (premises : Set (source.sentence.obj signature)) :
    TheoryRoute (source.semanticConsequence signature premises)
      (target.semanticConsequence (comorphism.mapSignature.obj signature)
        (comorphism.mapSentence.app signature '' premises)) where
  translate := comorphism.mapSentence.app signature
  preserves _ entails := entails_mapped comorphism signature entails

/-- **The borrowed theory of a comorphism is consequence among the reducts of
target models.** -/
theorem borrowed_ofComorphism (comorphism : Institution.Comorphism source target)
    (signature : SourceSignature) (premises : Set (source.sentence.obj signature)) :
    (ofComorphism comorphism signature premises).borrowed =
      consequencesIn (source.satisfies signature)
        (InstitutionBridge.reductUniverse comorphism signature) premises :=
  InstitutionBridge.preimage_targetConsequence comorphism signature premises

theorem ofComorphism_conservative_iff (comorphism : Institution.Comorphism source target)
    (signature : SourceSignature) (premises : Set (source.sentence.obj signature)) :
    (ofComorphism comorphism signature premises).Conservative ↔
      HostsFaithfully (source.satisfies signature)
        (InstitutionBridge.reductUniverse comorphism signature) premises := by
  rw [TheoryRoute.conservative_iff_borrowed_eq, borrowed_ofComorphism,
    InstitutionBridge.semanticConsequence_eq]
  rfl

theorem conservative_iff_routes (comorphism : Institution.Comorphism source target) :
    Conservative comorphism ↔
      ∀ (signature : SourceSignature) (premises : Set (source.sentence.obj signature)),
        (ofComorphism comorphism signature premises).Conservative := by
  rw [conservative_iff_hostsFaithfully]
  exact forall_congr' fun signature => forall_congr' fun premises =>
    (ofComorphism_conservative_iff comorphism signature premises).symm

/-! ## Borrowing an entailment system -/

/-- An entailment system of an institution: closure operators on its own
sentences, compatible with signature translation. -/
structure EntailmentSystem {Signature : Type uSignature} [Category.{uSignatureHom} Signature]
    (institution : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
      Signature) where
  consequence : (signature : Signature) → ClosureOperator (Set (institution.sentence.obj signature))
  translation : ∀ {first second : Signature} (map : first ⟶ second)
      (premises : Set (institution.sentence.obj first)),
    institution.sentence.map map '' consequence first premises ⊆
      consequence second (institution.sentence.map map '' premises)

namespace EntailmentSystem

variable {Signature : Type uSignature} [Category.{uSignatureHom} Signature]
  {institution : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} Signature}

/-- An entailment system is a Pi-institution over the institution's
sentences. -/
def toPiInstitution (system : EntailmentSystem institution) :
    Mettapedia.Logic.Consequence.PiInstitution.{uSignature, uSignatureHom, uSentence} Signature where
  sentence := institution.sentence
  consequence := system.consequence
  translation := system.translation

/-- Soundness: whatever the system derives is entailed. -/
def Sound (system : EntailmentSystem institution) : Prop :=
  ∀ signature premises, system.consequence signature premises ⊆
    institution.semanticConsequence signature premises

/-- Completeness: whatever is entailed the system derives. -/
def Complete (system : EntailmentSystem institution) : Prop :=
  ∀ signature premises, institution.semanticConsequence signature premises ⊆
    system.consequence signature premises

/-- The semantic entailment system, sound and complete by construction. -/
def semantic (institution : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}
    Signature) : EntailmentSystem institution where
  consequence := institution.semanticConsequence
  translation := institution.map_semanticConsequence

theorem semantic_sound : (semantic institution).Sound := fun _ _ => Set.Subset.rfl

theorem semantic_complete : (semantic institution).Complete := fun _ _ => Set.Subset.rfl

end EntailmentSystem

/-- **The borrowed entailment system**: derive a source sentence when the
target system derives its translation from the translated premises. -/
def borrow (comorphism : Institution.Comorphism source target)
    (system : EntailmentSystem target) : EntailmentSystem source where
  consequence signature :=
    ClosureOperator.mk'
      (fun premises => comorphism.mapSentence.app signature ⁻¹'
        system.consequence (comorphism.mapSignature.obj signature)
          (comorphism.mapSentence.app signature '' premises))
      (fun _ _ included => Set.preimage_mono
        ((system.consequence _).monotone (Set.image_mono included)))
      (fun premises sentence member =>
        (system.consequence _).le_closure _ ⟨sentence, member, rfl⟩)
      (fun premises sentence twice => by
        have narrowed : comorphism.mapSentence.app signature ''
            (comorphism.mapSentence.app signature ⁻¹'
              system.consequence (comorphism.mapSignature.obj signature)
                (comorphism.mapSentence.app signature '' premises)) ⊆
            system.consequence (comorphism.mapSignature.obj signature)
              (comorphism.mapSentence.app signature '' premises) :=
          Set.image_preimage_subset _ _
        have closed := (system.consequence _).monotone narrowed twice
        rw [(system.consequence _).idempotent] at closed
        exact closed)
  translation := by
    intro first second map premises sentence member
    rcases member with ⟨original, derived, rfl⟩
    change comorphism.mapSentence.app second (source.sentence.map map original) ∈
      system.consequence (comorphism.mapSignature.obj second)
        (comorphism.mapSentence.app second '' (source.sentence.map map '' premises))
    have naturality : ∀ value : source.sentence.obj first,
        comorphism.mapSentence.app second (source.sentence.map map value) =
          target.sentence.map (comorphism.mapSignature.map map)
            (comorphism.mapSentence.app first value) := fun value => by
      have pointwise := ConcreteCategory.congr_hom (comorphism.mapSentence.naturality map) value
      exact pointwise
    rw [naturality]
    have translated := system.translation (comorphism.mapSignature.map map)
      (comorphism.mapSentence.app first '' premises) ⟨_, derived, rfl⟩
    have images : target.sentence.map (comorphism.mapSignature.map map) ''
        (comorphism.mapSentence.app first '' premises) =
          comorphism.mapSentence.app second '' (source.sentence.map map '' premises) := by
      rw [Set.image_image, Set.image_image]
      exact Set.image_congr fun value _ => (naturality value).symm
    rw [images] at translated
    exact translated

theorem mem_borrow_iff (comorphism : Institution.Comorphism source target)
    (system : EntailmentSystem target) (signature : SourceSignature)
    (premises : Set (source.sentence.obj signature)) (conclusion : source.sentence.obj signature) :
    conclusion ∈ (borrow comorphism system).consequence signature premises ↔
      comorphism.mapSentence.app signature conclusion ∈
        system.consequence (comorphism.mapSignature.obj signature)
          (comorphism.mapSentence.app signature '' premises) :=
  Iff.rfl

/-- **The borrowed system is complete** whenever the target system is. -/
theorem borrow_complete (comorphism : Institution.Comorphism source target)
    {system : EntailmentSystem target} (complete : system.Complete) :
    (borrow comorphism system).Complete :=
  fun signature _ _ entails => complete _ _ (entails_mapped comorphism signature entails)

/-- **The borrowed system is sound** when the comorphism is conservative and
the target system is sound. -/
theorem borrow_sound_of_conservative {comorphism : Institution.Comorphism source target}
    (conservative : Conservative comorphism) {system : EntailmentSystem target}
    (sound : system.Sound) : (borrow comorphism system).Sound :=
  fun signature premises conclusion derived =>
    conservative signature premises conclusion (sound _ _ derived)

/-- **Borrowing theorem**: for a sound and complete target system, the
borrowed system is sound exactly when the comorphism is conservative. -/
theorem borrow_sound_iff_conservative (comorphism : Institution.Comorphism source target)
    {system : EntailmentSystem target} (sound : system.Sound) (complete : system.Complete) :
    (borrow comorphism system).Sound ↔ Conservative comorphism :=
  ⟨fun borrowedSound signature premises _ entails =>
      borrowedSound signature premises (complete _ _ entails),
    fun conservative => borrow_sound_of_conservative conservative sound⟩

/-- A borrowed system that is not sound derives a non-consequence. -/
theorem exists_unsound_of_not_conservative (comorphism : Institution.Comorphism source target)
    {system : EntailmentSystem target} (sound : system.Sound) (complete : system.Complete)
    (notConservative : ¬ Conservative comorphism) :
    ∃ (signature : SourceSignature) (premises : Set (source.sentence.obj signature))
      (conclusion : source.sentence.obj signature),
      conclusion ∈ (borrow comorphism system).consequence signature premises ∧
        ¬ source.Entails signature premises conclusion := by
  by_contra none
  apply notConservative
  apply (borrow_sound_iff_conservative comorphism sound complete).mp
  intro signature premises conclusion derived
  by_contra notEntailed
  exact none ⟨signature, premises, conclusion, derived, notEntailed⟩

end Institutions

/-! ## Relativization and inclusion along expansions

A richer language describes expansions of base structures by an
interpretation of new constants; `base` forgets the interpretation.  A theory
`axioms` of the richer language is hosted by the base language in two ways.

* **Relativization** reads a rich sentence `φ` at a base structure as: every
  expansion of it that satisfies the axioms satisfies `φ`.  It is exact: the
  relativization of `φ` holds in every base structure exactly when the axioms
  entail `φ` (`relativize_valid_iff`); as a route it is conservative
  (`relativizationRoute_conservative`).
* **Inclusion** reads a base sentence in an expansion through its base.  It
  carries base validities to consequences of the axioms, and it is
  conservative exactly when every base structure satisfying the sentence's
  failure has an expansion that is a model of the axioms; in particular,
  when every base structure expands (`inclusion_conservative_of_expands`).
  A base structure with no model expansion can make it non-conservative
  (`Control.inclusion_not_conservative`).
-/

section Expansions

variable {Base : Type uStr} {Expansion : Type uS} {Sentence : Type uS'} {BaseSentence : Type uS''}
  (base : Expansion → Base) (Sat : Expansion → Sentence → Prop)
  (BaseSat : Base → BaseSentence → Prop) (axioms : Set Sentence)

/-- The relativization of a rich sentence, read at a base structure. -/
def Relativized (sentence : Sentence) (structure_ : Base) : Prop :=
  ∀ expansion, base expansion = structure_ → expansion ∈ models Sat axioms → Sat expansion sentence

/-- **Relativization is exact**: a relativized sentence holds in every base
structure exactly when the axioms entail the sentence. -/
theorem relativize_valid_iff (sentence : Sentence) :
    (∀ structure_, Relativized base Sat axioms sentence structure_) ↔
      Entails Sat axioms sentence :=
  ⟨fun valid expansion model => valid (base expansion) expansion rfl model,
    fun entails _ _ _ model => entails model⟩

/-- Relativization as a route from the consequences of the axioms to the
sentences whose relativizations are valid. -/
def relativizationRoute :
    TheoryRoute (theoryOf Sat (models Sat axioms))
      {sentence | ∀ structure_, Relativized base Sat axioms sentence structure_} where
  translate sentence := sentence
  preserves _ entails := (relativize_valid_iff base Sat axioms _).mpr entails

theorem relativizationRoute_conservative :
    (relativizationRoute base Sat axioms).Conservative :=
  fun _ valid => (relativize_valid_iff base Sat axioms _).mp valid

/-- Inclusion as a route: base validities become consequences of the axioms
in the language where base sentences are read through `base`. -/
def includedRoute :
    TheoryRoute {sentence : BaseSentence | ∀ structure_, BaseSat structure_ sentence}
      (theoryOf (fun expansion sentence => BaseSat (base expansion) sentence)
        {expansion | expansion ∈ models Sat axioms}) where
  translate sentence := sentence
  preserves _ valid expansion _ := valid (base expansion)

/-- **Inclusion is conservative when every base structure expands to a model
of the axioms.** -/
theorem inclusion_conservative_of_expands
    (expands : ∀ structure_, ∃ expansion, base expansion = structure_ ∧
      expansion ∈ models Sat axioms) :
    (includedRoute base Sat BaseSat axioms).Conservative := by
  intro sentence certified structure_
  obtain ⟨expansion, rfl, model⟩ := expands structure_
  exact certified model

end Expansions

/-! ## Controls -/

namespace Control

open Mettapedia.Logic.InstitutionCanary

/-- **Negative control**: borrowing the target consequence of the collapsing
comorphism derives `true` from `{false}`, which the source does not entail. -/
theorem collapse_borrows_false_conclusion :
    true ∈ (borrow collapseComorphism
        (EntailmentSystem.semantic (PredicateInstitution.ofCarrier unitCarrier))).consequence
          (CategoryTheory.Discrete.mk ()) ({false} : Set Bool) ∧
      ¬ (PredicateInstitution.ofCarrier boolCarrier).Entails (CategoryTheory.Discrete.mk ())
        ({false} : Set Bool) true :=
  collapseComorphism_does_not_reflect_entailment

/-- The collapsing comorphism is therefore not conservative. -/
theorem collapse_not_conservative : ¬ Conservative collapseComorphism :=
  fun conservative => collapseComorphism_does_not_reflect_entailment.2
    (conservative _ _ _ collapseComorphism_does_not_reflect_entailment.1)

/-- **Positive control**: the representative comorphism covers models up to
isomorphism over an isomorphism-invariant institution, so its borrowed
consequence is exactly the source consequence. -/
theorem representative_borrow_exact (premises : Set Unit) (conclusion : Unit) :
    conclusion ∈ (borrow invariantRepresentativeComorphism
        (EntailmentSystem.semantic _)).consequence (CategoryTheory.Discrete.mk ()) premises ↔
      isoInvariantInstitution.Entails (CategoryTheory.Discrete.mk ()) premises conclusion :=
  (invariantRepresentativeComorphism.entails_mapped_iff_of_coversModelsUpToIso
    isoInvariantInstitution_satisfactionIsoInvariant
    invariantRepresentativeComorphism_coversModelsUpToIso _ premises conclusion).symm

open Mettapedia.Logic.TheoryModel.Control

/-- The route restricting the three-structure logic to one structure: its
target theory is the theory of that structure. -/
def restrictRoute (fragment : Set Point) :
    TheoryRoute (theoryOf atomSat (models atomSat (∅ : Set Bool))) (theoryOf atomSat fragment) where
  translate sentence := sentence
  preserves _ valid := theoryOf_anti (Set.subset_univ fragment)
    (by rw [models_empty] at valid; exact valid)

theorem borrowed_restrictRoute (fragment : Set Point) :
    (restrictRoute fragment).borrowed = theoryOf atomSat fragment :=
  rfl

theorem source_theory_empty : theoryOf atomSat (models atomSat (∅ : Set Bool)) = ∅ := by
  rw [models_empty]
  ext sentence
  simp only [Set.mem_empty_iff_false, iff_false]
  intro valid
  exact valid (Set.mem_univ Point.c)

/-- **Incomparable optima**: restricting to `a` and to `b` borrow incomparable
theories, neither route is conservative, and their cardinal weaknesses are
equal. -/
theorem incomparable_optima :
    ¬ (restrictRoute {Point.a}).FewerCommitments (restrictRoute {Point.b}) ∧
      ¬ (restrictRoute {Point.b}).FewerCommitments (restrictRoute {Point.a}) ∧
      ¬ (restrictRoute {Point.a}).Conservative ∧ ¬ (restrictRoute {Point.b}).Conservative ∧
      TheoryRoute.weakness atomSat Set.encard (restrictRoute {Point.a}) =
        TheoryRoute.weakness atomSat Set.encard (restrictRoute {Point.b}) := by
  have theoryA : theoryOf atomSat ({Point.a} : Set Point) = {false} := by
    ext sentence
    constructor
    · intro valid
      cases sentence
      · rfl
      · exact (valid rfl).elim
    · rintro rfl _ rfl
      trivial
  have theoryB : theoryOf atomSat ({Point.b} : Set Point) = {true} := by
    ext sentence
    constructor
    · intro valid
      cases sentence
      · exact (valid rfl).elim
      · rfl
    · rintro rfl _ rfl
      trivial
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro fewer
    have member : false ∈ (restrictRoute {Point.b}).borrowed :=
      fewer (show false ∈ (restrictRoute {Point.a}).borrowed by
        rw [borrowed_restrictRoute, theoryA]; rfl)
    rw [borrowed_restrictRoute, theoryB] at member
    exact Bool.false_ne_true member
  · intro fewer
    have member : true ∈ (restrictRoute {Point.a}).borrowed :=
      fewer (show true ∈ (restrictRoute {Point.b}).borrowed by
        rw [borrowed_restrictRoute, theoryB]; rfl)
    rw [borrowed_restrictRoute, theoryA] at member
    exact Bool.false_ne_true member.symm
  · intro conservative
    have member := conservative (show false ∈ (restrictRoute {Point.a}).borrowed by
      rw [borrowed_restrictRoute, theoryA]; rfl)
    rw [source_theory_empty] at member
    exact member
  · intro conservative
    have member := conservative (show true ∈ (restrictRoute {Point.b}).borrowed by
      rw [borrowed_restrictRoute, theoryB]; rfl)
    rw [source_theory_empty] at member
    exact member
  · unfold TheoryRoute.weakness
    rw [borrowed_restrictRoute, borrowed_restrictRoute, theoryA, theoryB]
    exact atoms_equal_cardinal_weakness

/-- **Positive**: the route to the region of both structures is conservative,
so it is below both incomparable routes. -/
theorem region_route_conservative :
    (restrictRoute region).Conservative ∧
      (restrictRoute region).FewerCommitments (restrictRoute {Point.a}) ∧
      (restrictRoute region).FewerCommitments (restrictRoute {Point.b}) := by
  have conservative : (restrictRoute region).Conservative := by
    intro sentence member
    rw [borrowed_restrictRoute, theoryOf_region] at member
    exact member.elim
  exact ⟨conservative, conservative.fewerCommitments _, conservative.fewerCommitments _⟩

end Control

namespace Control

/-- A miniature of hosting a theory that names two distinct elements.  A base
structure is a finite carrier `Fin size`; the one base sentence says that the
carrier has two distinct points. -/
def hasTwoPoints : ℕ → Unit → Prop := fun size _ => ∃ first second : Fin size, first ≠ second

/-- An expansion names two points of its carrier. -/
abbrev NamedPair := Σ size : ℕ, Fin size × Fin size

/-- The carrier in which an expansion names its points. -/
def carrierOf : NamedPair → ℕ := Sigma.fst

/-- The one sentence of the richer language says that the named points differ. -/
def namedPointsDiffer : NamedPair → Unit → Prop := fun pair _ => pair.2.1 ≠ pair.2.2

/-- **Negative control**: no expansion of the one-point carrier names two
different points, and the inclusion certifies "there are two distinct points",
which the one-point carrier refutes. -/
theorem inclusion_not_conservative :
    ¬ (includedRoute carrierOf namedPointsDiffer hasTwoPoints Set.univ).Conservative := by
  intro conservative
  have certified :
      () ∈ (includedRoute carrierOf namedPointsDiffer hasTwoPoints Set.univ).borrowed :=
    fun pair model => ⟨pair.2.1, pair.2.2, model (Set.mem_univ ())⟩
  obtain ⟨first, second, different⟩ := conservative certified 1
  exact different (Subsingleton.elim first second)

/-- **Positive control**: relativization in the same setting is conservative. -/
theorem relativization_conservative :
    (relativizationRoute carrierOf namedPointsDiffer (Set.univ : Set Unit)).Conservative :=
  relativizationRoute_conservative carrierOf namedPointsDiffer Set.univ

/-- Carriers of at least two points. -/
abbrev LargeCarrier := {size : ℕ // 2 ≤ size}

/-- An expansion of a large carrier names two of its points. -/
abbrev LargeNamedPair := Σ size : LargeCarrier, Fin size.1 × Fin size.1

def largeCarrierOf : LargeNamedPair → LargeCarrier := Sigma.fst

def largeNamedPointsDiffer : LargeNamedPair → Unit → Prop := fun pair _ => pair.2.1 ≠ pair.2.2

def largeHasTwoPoints : LargeCarrier → Unit → Prop :=
  fun size _ => ∃ first second : Fin size.1, first ≠ second

/-- **Positive control**: every carrier of at least two points expands to a
model, so the inclusion over large carriers is conservative. -/
theorem large_inclusion_conservative :
    (includedRoute largeCarrierOf largeNamedPointsDiffer largeHasTwoPoints Set.univ).Conservative :=
  inclusion_conservative_of_expands _ _ _ _ fun size =>
    ⟨⟨size, ⟨0, by have := size.2; omega⟩, ⟨1, by have := size.2; omega⟩⟩, rfl,
      fun _ _ equal => Nat.zero_ne_one (congrArg Fin.val equal)⟩

end Control

#print axioms TheoryRoute.addedCommitments_comp
#print axioms TheoryRoute.borrowed_comp_of_conservative
#print axioms TheoryRoute.conservative_comp_iff
#print axioms TheoryRoute.Conservative.fewerCommitments
#print axioms TheoryRoute.Conservative.weakness_eq
#print axioms TheoryRoute.decide
#print axioms entails_iff_of_conservative
#print axioms conservative_iff_hostsFaithfully
#print axioms decideEntails
#print axioms borrowed_ofComorphism
#print axioms borrow
#print axioms borrow_complete
#print axioms borrow_sound_iff_conservative
#print axioms exists_unsound_of_not_conservative
#print axioms Control.collapse_borrows_false_conclusion
#print axioms Control.collapse_not_conservative
#print axioms Control.representative_borrow_exact
#print axioms Control.incomparable_optima
#print axioms Control.region_route_conservative
#print axioms relativize_valid_iff
#print axioms relativizationRoute_conservative
#print axioms inclusion_conservative_of_expands
#print axioms Control.inclusion_not_conservative
#print axioms Control.large_inclusion_conservative

end Mettapedia.Logic.InstitutionBorrowing
