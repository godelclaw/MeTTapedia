import Mettapedia.GSLT.LanguageDef.TheoryGraph
import Mettapedia.Logic.InstitutionBorrowing

/-!
# Carrying proofs, not only theorems, along routes of the theory graph

An arrow of the theory graph preserves theoremhood.  A proof calculus of a
Pi-institution keeps proof fibres over each closed theory.  A route carries
**certificates** when a natural map sends every proof over a closed theory to
a proof over its direct image, projecting to the translated sentence
(`CertificateRoute`).  Then every certificate of a theorem becomes a
certificate of its translation (`CertificateRoute.carry_projects`), so
theoremhood is preserved with evidence (`CertificateRoute.translated_mem`).

* Every comorphism carries certificates between the thin calculi
  (`thinRoute`): carrying truth is the proof-irrelevant special case.
* Certificate routes compose along composite comorphisms
  (`CertificateRoute.comp`), through the identification of the direct image
  along a composite with the iterated direct image
  (`directImageFunctor_comp`).
* A route can carry certificates and still lose their distinctions.  The
  hosting contract asks a host to preserve the guest's distinctions, so
  faithfulness on certificates is recorded separately
  (`CertificateRoute.Faithful`).  Control: erasing the tags of the tagged
  calculus carries every certificate and identifies two distinct proofs of
  every theorem (`eraseTags_not_faithful`); keeping them is faithful
  (`keepTags_faithful`).
* Certificates move back only through conservativity.  At a closed theory
  the comorphism gives a route between the theory and its direct image
  (`theoryRoute`); a target certificate of a translated sentence yields a
  source certificate when that route is conservative and the source calculus
  is adequate (`source_certificate_of_conservative`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.TheoryGraphProofTransport

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.Logic.Consequence
open Mettapedia.GSLT.LanguageDef.TheoryGraph
open Mettapedia.Logic.InstitutionBorrowing

universe uSignature uHom uSentence

section Routes

variable {SourceSignature TargetSignature : Type uSignature}
  [Category.{uHom} SourceSignature] [Category.{uHom} TargetSignature]
  {source : PiInstitution.{uSignature, uHom, uSentence} SourceSignature}
  {target : PiInstitution.{uSignature, uHom, uSentence} TargetSignature}

/-- Sentence translation between the sentence functors of closed theories. -/
def sentenceTranslation (route : PiInstitution.Comorphism source target) :
    PiInstitution.theorySentence source ⟶
      directImageFunctor route ⋙ PiInstitution.theorySentence target where
  app theory := TypeCat.ofHom (route.mapSentence theory.signature)
  naturality first second morphism := by
    ext sentence
    exact (route.mapSentence_natural morphism.mapSignature sentence).symm

/-- **A certificate route** along a comorphism: every proof over a closed
theory is carried to a proof over its direct image that projects to the
translated sentence. -/
structure CertificateRoute (route : PiInstitution.Comorphism source target)
    (sourceCalculus : PiInstitution.ProofCalculus source)
    (targetCalculus : PiInstitution.ProofCalculus target) where
  carry : sourceCalculus.proof ⟶ directImageFunctor route ⋙ targetCalculus.proof
  projects : carry ≫ Functor.whiskerLeft (directImageFunctor route) targetCalculus.projection =
    sourceCalculus.projection ≫ sentenceTranslation route

namespace CertificateRoute

variable {route : PiInstitution.Comorphism source target}
  {sourceCalculus : PiInstitution.ProofCalculus source}
  {targetCalculus : PiInstitution.ProofCalculus target}

/-- A carried certificate proves the translated sentence. -/
theorem carry_projects (carrier : CertificateRoute route sourceCalculus targetCalculus)
    (theory : PiInstitution.TheoryObject source) (certificate : sourceCalculus.proof.obj theory) :
    targetCalculus.projection.app (directImage route theory) (carrier.carry.app theory certificate) =
      route.mapSentence theory.signature (sourceCalculus.projection.app theory certificate) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app carrier.projects theory) certificate

/-- **Theoremhood with evidence**: the translation of a certified sentence is
a theorem of the direct image, witnessed by the carried certificate. -/
theorem translated_mem (carrier : CertificateRoute route sourceCalculus targetCalculus)
    (theory : PiInstitution.TheoryObject source) (certificate : sourceCalculus.proof.obj theory) :
    route.mapSentence theory.signature (sourceCalculus.projection.app theory certificate) ∈
      (directImage route theory).theory.1 := by
  rw [← carrier.carry_projects theory certificate]
  exact (targetCalculus.theorem_image _ _).mp ⟨_, rfl⟩

/-- Faithfulness on certificates: distinct proofs stay distinct. -/
def Faithful (carrier : CertificateRoute route sourceCalculus targetCalculus) : Prop :=
  ∀ theory, Function.Injective (carrier.carry.app theory)

end CertificateRoute

/-- **Every comorphism carries thin certificates**: a theorem of a closed
theory goes to its translation in the direct image. -/
def thinRoute (route : PiInstitution.Comorphism source target) :
    CertificateRoute route (PiInstitution.ProofCalculus.thin source)
      (PiInstitution.ProofCalculus.thin target) where
  carry :=
    { app := fun theory => TypeCat.ofHom fun certificate =>
        ⟨route.mapSentence theory.signature certificate.1,
          mapSentence_mem_directImage route theory certificate.2⟩
      naturality := by
        intro first second morphism
        ext certificate
        apply Subtype.ext
        exact (route.mapSentence_natural morphism.mapSignature certificate.1).symm }
  projects := by
    ext theory certificate
    rfl

/-- At a closed theory, a comorphism gives a route from the theory to its
direct image. -/
def theoryRoute (route : PiInstitution.Comorphism source target)
    (theory : PiInstitution.TheoryObject source) :
    TheoryRoute theory.theory.1 (directImage route theory).theory.1 where
  translate := route.mapSentence theory.signature
  preserves _ member := mapSentence_mem_directImage route theory member

/-- **Certificates move back only through conservativity**: with an adequate
source calculus, a target certificate of a translated sentence yields a source
certificate when the route at that theory is conservative. -/
theorem source_certificate_of_conservative (route : PiInstitution.Comorphism source target)
    (sourceCalculus : PiInstitution.ProofCalculus source)
    (targetCalculus : PiInstitution.ProofCalculus target)
    (theory : PiInstitution.TheoryObject source)
    (conservative : (theoryRoute route theory).Conservative)
    (sentence : source.sentence.obj theory.signature)
    (targetCertificate : targetCalculus.proof.obj (directImage route theory))
    (projected : targetCalculus.projection.app _ targetCertificate =
      route.mapSentence theory.signature sentence) :
    ∃ certificate : sourceCalculus.proof.obj theory,
      sourceCalculus.projection.app theory certificate = sentence := by
  apply sourceCalculus.proof_of_theorem
  apply conservative
  change route.mapSentence theory.signature sentence ∈ (directImage route theory).theory.1
  rw [← projected]
  exact (targetCalculus.theorem_image _ _).mp ⟨_, rfl⟩

end Routes

/-! ## Composition -/

section Composition

variable {FirstSignature MiddleSignature LastSignature : Type uSignature}
  [Category.{uHom} FirstSignature] [Category.{uHom} MiddleSignature]
  [Category.{uHom} LastSignature]
  {first : PiInstitution.{uSignature, uHom, uSentence} FirstSignature}
  {middle : PiInstitution.{uSignature, uHom, uSentence} MiddleSignature}
  {last : PiInstitution.{uSignature, uHom, uSentence} LastSignature}

/-- The direct image along a composite comorphism is the iterated direct
image, as functors. -/
theorem directImageFunctor_comp (earlier : PiInstitution.Comorphism first middle)
    (later : PiInstitution.Comorphism middle last) :
    directImageFunctor (PiInstitution.Comorphism.comp earlier later) =
      directImageFunctor earlier ⋙ directImageFunctor later :=
  congrArg Cat.Hom.toFunctor
    (closedTheories.map_comp
      (X := ⟨Cat.of FirstSignature, first⟩) (Y := ⟨Cat.of MiddleSignature, middle⟩)
      (Z := ⟨Cat.of LastSignature, last⟩) earlier later)

/-- **Certificate routes compose.** -/
def CertificateRoute.comp {earlier : PiInstitution.Comorphism first middle}
    {later : PiInstitution.Comorphism middle last}
    {firstCalculus : PiInstitution.ProofCalculus first}
    {middleCalculus : PiInstitution.ProofCalculus middle}
    {lastCalculus : PiInstitution.ProofCalculus last}
    (earlierRoute : CertificateRoute earlier firstCalculus middleCalculus)
    (laterRoute : CertificateRoute later middleCalculus lastCalculus) :
    CertificateRoute (PiInstitution.Comorphism.comp earlier later) firstCalculus lastCalculus where
  carry := earlierRoute.carry ≫
    Functor.whiskerLeft (directImageFunctor earlier) laterRoute.carry ≫
      eqToHom (by rw [directImageFunctor_comp]; rfl)
  projects := by
    ext theory certificate
    have earlierLaw := earlierRoute.carry_projects theory certificate
    have laterLaw := laterRoute.carry_projects (directImage earlier theory)
      (earlierRoute.carry.app theory certificate)
    have equalObjects : directImage (PiInstitution.Comorphism.comp earlier later) theory =
        directImage later (directImage earlier theory) := directImage_comp earlier later theory
    have transport : ∀ {X Y : PiInstitution.TheoryObject last} (equal : X = Y)
        (value : lastCalculus.proof.obj X),
        lastCalculus.projection.app Y (eqToHom (congrArg lastCalculus.proof.obj equal) value) =
          eqToHom (congrArg (PiInstitution.theorySentence last).obj equal)
            (lastCalculus.projection.app X value) := by
      intro X Y equal value
      subst equal
      rfl
    have step := transport equalObjects.symm
      (laterRoute.carry.app _ (earlierRoute.carry.app theory certificate))
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
    change lastCalculus.projection.app _ (eqToHom (congrArg lastCalculus.proof.obj
        equalObjects.symm) (laterRoute.carry.app _ (earlierRoute.carry.app theory certificate))) =
      later.mapSentence _ (earlier.mapSentence theory.signature
        (firstCalculus.projection.app theory certificate))
    rw [step]
    change lastCalculus.projection.app _
        (laterRoute.carry.app _ (earlierRoute.carry.app theory certificate)) = _
    exact laterLaw.trans (congrArg (later.mapSentence _) earlierLaw)

end Composition

/-! ## Controls: carrying certificates and keeping their distinctions -/

section Tags

variable {Signature : Type uSignature} [Category.{uHom} Signature]
  (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)

/-- Along the identity, the tagged calculus is carried into the thin calculus
by forgetting the tag. -/
def eraseTags :
    CertificateRoute (PiInstitution.Comorphism.identity institution)
      (PiInstitution.ProofCalculus.tagged institution)
      (PiInstitution.ProofCalculus.thin institution) where
  carry :=
    { app := fun theory => TypeCat.ofHom fun certificate =>
        ⟨certificate.1.1, mapSentence_mem_directImage _ theory certificate.1.2⟩
      naturality := by
        intro first second morphism
        ext certificate
        rfl }
  projects := by
    ext theory certificate
    rfl

/-- Along the identity, the tagged calculus is carried into itself with its
tags. -/
def keepTags :
    CertificateRoute (PiInstitution.Comorphism.identity institution)
      (PiInstitution.ProofCalculus.tagged institution)
      (PiInstitution.ProofCalculus.tagged institution) where
  carry :=
    { app := fun theory => TypeCat.ofHom fun certificate =>
        (⟨certificate.1.1, mapSentence_mem_directImage _ theory certificate.1.2⟩, certificate.2)
      naturality := by
        intro first second morphism
        ext certificate
        rfl }
  projects := by
    ext theory certificate
    rfl

/-- **Negative control**: erasing tags carries every certificate yet identifies
the two distinct proofs of any theorem, so it is not faithful. -/
theorem eraseTags_not_faithful (theory : PiInstitution.TheoryObject institution)
    (formula : institution.sentence.obj theory.signature)
    (theoremhood : formula ∈ theory.theory.1) :
    ¬ (eraseTags institution).Faithful := by
  intro faithful
  have same := @faithful theory (⟨formula, theoremhood⟩, false) (⟨formula, theoremhood⟩, true) rfl
  exact Bool.false_ne_true (congrArg Prod.snd same)

/-- **Positive control**: keeping the tags is faithful. -/
theorem keepTags_faithful : (keepTags institution).Faithful := by
  intro theory first second same
  have tags : first.2 = second.2 := by
    have projected := congrArg Prod.snd same
    exact projected
  have formulas : first.1.1 = second.1.1 := by
    have projected := congrArg (fun certificate => certificate.1.1) same
    exact projected
  exact Prod.ext (Subtype.ext formulas) tags

end Tags

#print axioms CertificateRoute.carry_projects
#print axioms CertificateRoute.translated_mem
#print axioms thinRoute
#print axioms source_certificate_of_conservative
#print axioms directImageFunctor_comp
#print axioms CertificateRoute.comp
#print axioms eraseTags_not_faithful
#print axioms keepTags_faithful

end Mettapedia.GSLT.LanguageDef.TheoryGraphProofTransport
