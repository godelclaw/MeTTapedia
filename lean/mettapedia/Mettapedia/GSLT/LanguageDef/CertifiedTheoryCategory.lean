import Mettapedia.GSLT.LanguageDef.HeterogeneousTheory

/-!
# Categories of certified theories and certified translations

`HeterogeneousTheory` defines identity and composition for semantic theory
translations and exact certified translations.  This module
closes their category laws, bundles the varying theory families as categorical
objects, and proves that forgetting certificate transport is a functor.

This is the external-certificate subcategory, not a characterization of every
SemanticService service.  Direct decision kernels and meaning-preserving native operations
need no certificate transport; their common service boundary and
request-local selection live in `Mettapedia.GSLT.LanguageDef.SemanticService`.

The conservative tagged sum is also shown to satisfy the coproduct universal
property.  These results characterize the codomain in which a future SemanticService
generation functor can land; they do not assume that generation is already
functorial on presentation morphisms.

Finally, semantic host irrelevance is stated at its strongest justified scope:
two conservative realizations of the same guest agree on translated scope and
meaning.  Certificate representation and execution cost are deliberately not
part of that theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory

open CategoryTheory
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.SemanticEvidence
open Mettapedia.GSLT.LanguageDef.HeterogeneousTheory

universe uKind uSignature uClaim uCertificate

/-! ## Unbundled category laws -/

namespace TheoryTranslation

variable {A B C D : Type uKind}
    {ta : TheoryFamily.{uSignature, uKind, uClaim} A}
    {tb : TheoryFamily.{uSignature, uKind, uClaim} B}
    {tc : TheoryFamily.{uSignature, uKind, uClaim} C}
    {td : TheoryFamily.{uSignature, uKind, uClaim} D}

theorem identity_comp
    (f : HeterogeneousTheory.TheoryTranslation ta tb) :
    HeterogeneousTheory.TheoryTranslation.comp
        (HeterogeneousTheory.TheoryTranslation.identity ta) f = f :=
  rfl

theorem comp_identity
    (f : HeterogeneousTheory.TheoryTranslation ta tb) :
    HeterogeneousTheory.TheoryTranslation.comp f
        (HeterogeneousTheory.TheoryTranslation.identity tb) = f :=
  rfl

theorem comp_assoc
    (f : HeterogeneousTheory.TheoryTranslation ta tb)
    (g : HeterogeneousTheory.TheoryTranslation tb tc)
    (h : HeterogeneousTheory.TheoryTranslation tc td) :
    HeterogeneousTheory.TheoryTranslation.comp
        (HeterogeneousTheory.TheoryTranslation.comp f g) h =
      HeterogeneousTheory.TheoryTranslation.comp f
        (HeterogeneousTheory.TheoryTranslation.comp g h) :=
  rfl

end TheoryTranslation

namespace CertifiedTranslation

variable {A B C D : Type uKind}
    {ta : TheoryFamily.{uSignature, uKind, uClaim} A}
    {tb : TheoryFamily.{uSignature, uKind, uClaim} B}
    {tc : TheoryFamily.{uSignature, uKind, uClaim} C}
    {td : TheoryFamily.{uSignature, uKind, uClaim} D}
    {ca : AuthorityContract.{uKind, uCertificate, uSignature, uClaim} ta}
    {cb : AuthorityContract.{uKind, uCertificate, uSignature, uClaim} tb}
    {cc : AuthorityContract.{uKind, uCertificate, uSignature, uClaim} tc}
    {cd : AuthorityContract.{uKind, uCertificate, uSignature, uClaim} td}

theorem identity_comp
    (f : HeterogeneousTheory.CertifiedTranslation ca cb) :
    HeterogeneousTheory.CertifiedTranslation.comp
        (HeterogeneousTheory.CertifiedTranslation.identity ca) f = f :=
  rfl

theorem comp_identity
    (f : HeterogeneousTheory.CertifiedTranslation ca cb) :
    HeterogeneousTheory.CertifiedTranslation.comp f
        (HeterogeneousTheory.CertifiedTranslation.identity cb) = f :=
  rfl

theorem comp_assoc
    (f : HeterogeneousTheory.CertifiedTranslation ca cb)
    (g : HeterogeneousTheory.CertifiedTranslation cb cc)
    (h : HeterogeneousTheory.CertifiedTranslation cc cd) :
    HeterogeneousTheory.CertifiedTranslation.comp
        (HeterogeneousTheory.CertifiedTranslation.comp f g) h =
      HeterogeneousTheory.CertifiedTranslation.comp f
        (HeterogeneousTheory.CertifiedTranslation.comp g h) :=
  rfl

theorem toTheoryTranslation_identity :
    (HeterogeneousTheory.CertifiedTranslation.identity ca).toTheoryTranslation =
      HeterogeneousTheory.TheoryTranslation.identity ta :=
  rfl

theorem toTheoryTranslation_comp
    (f : HeterogeneousTheory.CertifiedTranslation ca cb)
    (g : HeterogeneousTheory.CertifiedTranslation cb cc) :
    (HeterogeneousTheory.CertifiedTranslation.comp f g).toTheoryTranslation =
      HeterogeneousTheory.TheoryTranslation.comp
        f.toTheoryTranslation g.toTheoryTranslation :=
  rfl

/-- Exact authority translations are determined by their transported data;
the commuting and preservation fields are propositions. -/
theorem ext_data
    {f g : HeterogeneousTheory.CertifiedTranslation ca cb}
    (kindEqual : forall kind, f.mapKind kind = g.mapKind kind)
    (signatureEqual : forall signature,
      f.mapSignature signature = g.mapSignature signature)
    (claimEqual : forall kind claim,
      HEq (f.mapClaim kind claim) (g.mapClaim kind claim))
    (certificateEqual : forall kind certificate,
      HEq (f.mapCertificate kind certificate)
        (g.mapCertificate kind certificate)) :
    f = g := by
  cases f with
  | mk fKind fSignature fSignatureCommutes fClaim fCertificate
      fCheckCommutes fMeaningPreserved =>
    cases g with
    | mk gKind gSignature gSignatureCommutes gClaim gCertificate
        gCheckCommutes gMeaningPreserved =>
      simp only at kindEqual signatureEqual claimEqual certificateEqual
      have kindFunctionEqual : fKind = gKind := funext kindEqual
      subst kindFunctionEqual
      have signatureFunctionEqual : fSignature = gSignature :=
        funext signatureEqual
      subst signatureFunctionEqual
      have claimFunctionEqual : fClaim = gClaim :=
        funext fun kind => funext fun claim =>
          eq_of_heq (claimEqual kind claim)
      subst claimFunctionEqual
      have certificateFunctionEqual : fCertificate = gCertificate :=
        funext fun kind => funext fun certificate =>
          eq_of_heq (certificateEqual kind certificate)
      subst certificateFunctionEqual
      rfl

end CertifiedTranslation

/-! ## Bundled categories and certificate forgetting -/

-- Bundled signature and authority carriers retain independent universes.
set_option linter.checkUnivs false in
/-- A heterogeneous semantic theory is an object together with its own kind
index. -/
structure TheoryObject where
  Kind : Type uKind
  family : TheoryFamily.{uSignature, uKind, uClaim} Kind

-- Certificate carriers remain independent of the other bundled carriers.
set_option linter.checkUnivs false in
/-- An exact authority object adds native certificate fibres to a semantic
theory object. -/
structure CertifiedTheory where
  Kind : Type uKind
  family : TheoryFamily.{uSignature, uKind, uClaim} Kind
  contract : AuthorityContract.{uKind, uCertificate, uSignature, uClaim} family

instance : CategoryTheory.Category
    (TheoryObject.{uKind, uSignature, uClaim}) where
  Hom source target :=
    HeterogeneousTheory.TheoryTranslation source.family target.family
  id object := HeterogeneousTheory.TheoryTranslation.identity object.family
  comp earlier later :=
    HeterogeneousTheory.TheoryTranslation.comp earlier later
  id_comp := TheoryTranslation.identity_comp
  comp_id := TheoryTranslation.comp_identity
  assoc := TheoryTranslation.comp_assoc

instance : CategoryTheory.Category
    (CertifiedTheory.{uKind, uSignature, uClaim, uCertificate}) where
  Hom source target :=
    HeterogeneousTheory.CertifiedTranslation
      source.contract target.contract
  id object :=
    HeterogeneousTheory.CertifiedTranslation.identity object.contract
  comp earlier later :=
    HeterogeneousTheory.CertifiedTranslation.comp earlier later
  id_comp := CertifiedTranslation.identity_comp
  comp_id := CertifiedTranslation.comp_identity
  assoc := CertifiedTranslation.comp_assoc

/-- Forget native certificates and exact replay while retaining the semantic
translation.  This is the categorical distinction between theorem meaning and
one operational host. -/
def forgetCertificates :
    CategoryTheory.Functor
      (CertifiedTheory.{uKind, uSignature, uClaim, uCertificate})
      (TheoryObject.{uKind, uSignature, uClaim}) where
  obj object := ⟨object.Kind, object.family⟩
  map translation := translation.toTheoryTranslation
  map_id _object := CertifiedTranslation.toTheoryTranslation_identity
  map_comp earlier later :=
    CertifiedTranslation.toTheoryTranslation_comp earlier later

/-! ## Bundled conservative routes into a selected host -/

/-- A source authority together with an exact, conservative route into one
selected host.  This is the proof-relevant payload of an authority selector:
the selector returns a checker translation and reflection theorem, rather
than merely claiming that a host supports a capability. -/
structure ConservativeAuthorityRoute
    (target : CertifiedTheory.{uKind, uSignature, uClaim, uCertificate}) where
  source : CertifiedTheory.{uKind, uSignature, uClaim, uCertificate}
  translation : source ⟶ target
  conservative : translation.toTheoryTranslation.Conservative

namespace ConservativeAuthorityRoute

/-- Every authority has the reflexive conservative route. -/
def identity
    (object : CertifiedTheory.{uKind, uSignature, uClaim, uCertificate}) :
    ConservativeAuthorityRoute object where
  source := object
  translation :=
    HeterogeneousTheory.CertifiedTranslation.identity object.contract
  conservative := by
    constructor <;> intro kind claim assumption <;> exact assumption

/-- Postcomposition transports a bundled guest route to a larger host while
retaining exact checker replay and semantic reflection. -/
def postcompose
    {middle target :
      CertifiedTheory.{uKind, uSignature, uClaim, uCertificate}}
    (route : ConservativeAuthorityRoute middle)
    (translation : middle ⟶ target)
    (conservative : translation.toTheoryTranslation.Conservative) :
    ConservativeAuthorityRoute target where
  source := route.source
  translation :=
    HeterogeneousTheory.CertifiedTranslation.comp
      route.translation translation
  conservative :=
    HeterogeneousTheory.TheoryTranslation.Conservative.comp
      route.translation.toTheoryTranslation
      translation.toTheoryTranslation
      route.conservative conservative

/-- The selected host replays every routed certificate exactly as its source
authority does. -/
theorem check_eq_source
    {target : CertifiedTheory.{uKind, uSignature, uClaim, uCertificate}}
    (route : ConservativeAuthorityRoute target)
    (kind : route.source.Kind)
    (claim : route.source.family.Claim kind)
    (certificate : route.source.contract.Certificate kind) :
    (target.contract.checker (route.translation.mapKind kind)).check
        (route.translation.mapClaim kind claim)
        (route.translation.mapCertificate kind certificate) =
      (route.source.contract.checker kind).check claim certificate :=
  route.translation.check_commutes kind claim certificate

/-- Conservative routing makes source and hosted proof scope equivalent on
the translated image. -/
theorem scope_iff_source
    {target : CertifiedTheory.{uKind, uSignature, uClaim, uCertificate}}
    (route : ConservativeAuthorityRoute target)
    (kind : route.source.Kind)
    (claim : route.source.family.Claim kind) :
    target.family.Scope (route.translation.mapKind kind)
        (route.translation.mapClaim kind claim) <->
      route.source.family.Scope kind claim :=
  HeterogeneousTheory.TheoryTranslation.scope_iff_of_conservative
    route.translation.toTheoryTranslation route.conservative kind claim

/-- Independently authored meaning is likewise invariant on a conservative
routed image. -/
theorem meaning_iff_source
    {target : CertifiedTheory.{uKind, uSignature, uClaim, uCertificate}}
    (route : ConservativeAuthorityRoute target)
    (kind : route.source.Kind)
    (claim : route.source.family.Claim kind) :
    target.family.Meaning (route.translation.mapKind kind)
        (route.translation.mapClaim kind claim) <->
      route.source.family.Meaning kind claim :=
  HeterogeneousTheory.TheoryTranslation.meaning_iff_of_conservative
    route.translation.toTheoryTranslation route.conservative kind claim

end ConservativeAuthorityRoute

/-! ## The conservative tagged sum is a coproduct -/

namespace Coproduct

variable {LeftKind RightKind TargetKind : Type uKind}
    {left : TheoryFamily.{uSignature, uKind, uClaim} LeftKind}
    {right : TheoryFamily.{uSignature, uKind, uClaim} RightKind}
    {target : TheoryFamily.{uSignature, uKind, uClaim} TargetKind}

/-- Copairing of semantic translations out of the tagged theory sum. -/
def descTheory
    (leftMap : HeterogeneousTheory.TheoryTranslation left target)
    (rightMap : HeterogeneousTheory.TheoryTranslation right target) :
    HeterogeneousTheory.TheoryTranslation
      (HeterogeneousTheory.Coproduct.theory left right) target where
  mapKind
    | .inl kind => leftMap.mapKind kind
    | .inr kind => rightMap.mapKind kind
  mapSignature
    | .inl signature => leftMap.mapSignature signature
    | .inr signature => rightMap.mapSignature signature
  signature_commutes := by
    intro kind
    cases kind with
    | inl kind => exact leftMap.signature_commutes kind
    | inr kind => exact rightMap.signature_commutes kind
  mapClaim
    | .inl kind => leftMap.mapClaim kind
    | .inr kind => rightMap.mapClaim kind
  scope_preserved := by
    intro kind claim inScope
    cases kind with
    | inl kind => exact leftMap.scope_preserved kind claim inScope
    | inr kind => exact rightMap.scope_preserved kind claim inScope
  meaning_preserved := by
    intro kind claim meaningful
    cases kind with
    | inl kind => exact leftMap.meaning_preserved kind claim meaningful
    | inr kind => exact rightMap.meaning_preserved kind claim meaningful

variable
    {leftContract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} left}
    {rightContract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} right}
    {targetContract :
      AuthorityContract.{uKind, uCertificate, uSignature, uClaim} target}

/-- Copairing of exact authority translations out of the tagged authority
sum. -/
def desc
    (leftMap : HeterogeneousTheory.CertifiedTranslation
      leftContract targetContract)
    (rightMap : HeterogeneousTheory.CertifiedTranslation
      rightContract targetContract) :
    HeterogeneousTheory.CertifiedTranslation
      (HeterogeneousTheory.Coproduct.contract
        left right leftContract rightContract)
      targetContract where
  mapKind
    | .inl kind => leftMap.mapKind kind
    | .inr kind => rightMap.mapKind kind
  mapSignature
    | .inl signature => leftMap.mapSignature signature
    | .inr signature => rightMap.mapSignature signature
  signature_commutes := by
    intro kind
    cases kind with
    | inl kind => exact leftMap.signature_commutes kind
    | inr kind => exact rightMap.signature_commutes kind
  mapClaim
    | .inl kind => leftMap.mapClaim kind
    | .inr kind => rightMap.mapClaim kind
  mapCertificate
    | .inl kind => leftMap.mapCertificate kind
    | .inr kind => rightMap.mapCertificate kind
  check_commutes := by
    intro kind claim certificate
    cases kind with
    | inl kind => exact leftMap.check_commutes kind claim certificate
    | inr kind => exact rightMap.check_commutes kind claim certificate
  meaning_preserved := by
    intro kind claim meaningful
    cases kind with
    | inl kind => exact leftMap.meaning_preserved kind claim meaningful
    | inr kind => exact rightMap.meaning_preserved kind claim meaningful

theorem leftInclusion_desc
    (leftMap : HeterogeneousTheory.CertifiedTranslation
      leftContract targetContract)
    (rightMap : HeterogeneousTheory.CertifiedTranslation
      rightContract targetContract) :
    HeterogeneousTheory.CertifiedTranslation.comp
        (HeterogeneousTheory.Coproduct.leftInclusion
          left right leftContract rightContract)
        (desc leftMap rightMap) = leftMap :=
  rfl

theorem rightInclusion_desc
    (leftMap : HeterogeneousTheory.CertifiedTranslation
      leftContract targetContract)
    (rightMap : HeterogeneousTheory.CertifiedTranslation
      rightContract targetContract) :
    HeterogeneousTheory.CertifiedTranslation.comp
        (HeterogeneousTheory.Coproduct.rightInclusion
          left right leftContract rightContract)
        (desc leftMap rightMap) = rightMap :=
  rfl

/-- The mediator out of the tagged authority sum is unique. -/
theorem desc_unique
    (candidate : HeterogeneousTheory.CertifiedTranslation
      (HeterogeneousTheory.Coproduct.contract
        left right leftContract rightContract)
      targetContract)
    (leftMap : HeterogeneousTheory.CertifiedTranslation
      leftContract targetContract)
    (rightMap : HeterogeneousTheory.CertifiedTranslation
      rightContract targetContract)
    (leftTriangle :
      HeterogeneousTheory.CertifiedTranslation.comp
          (HeterogeneousTheory.Coproduct.leftInclusion
            left right leftContract rightContract)
          candidate = leftMap)
    (rightTriangle :
      HeterogeneousTheory.CertifiedTranslation.comp
          (HeterogeneousTheory.Coproduct.rightInclusion
            left right leftContract rightContract)
          candidate = rightMap) :
    candidate = desc leftMap rightMap := by
  subst leftTriangle
  subst rightTriangle
  apply CertifiedTranslation.ext_data
  · intro kind
    cases kind <;> rfl
  · intro signature
    cases signature <;> rfl
  · intro kind claim
    cases kind <;> exact HEq.rfl
  · intro kind certificate
    cases kind <;> exact HEq.rfl

end Coproduct

/-! ## Semantic host irrelevance -/

namespace HostIrrelevance

variable {GuestKind FirstKind SecondKind : Type uKind}
    {guest : TheoryFamily.{uSignature, uKind, uClaim} GuestKind}
    {firstHost : TheoryFamily.{uSignature, uKind, uClaim} FirstKind}
    {secondHost : TheoryFamily.{uSignature, uKind, uClaim} SecondKind}

/-- Two exact authority realizations of one guest replay identically after
each host receives its own translated certificate.  Unlike semantic host
irrelevance, this operational statement needs no conservativity hypothesis:
both sides commute with the same guest checker by definition of exact
authority translation. -/
theorem check_eq
    {guestContract : AuthorityContract.{uKind, uCertificate, uSignature, uClaim}
      guest}
    {firstContract : AuthorityContract.{uKind, uCertificate, uSignature, uClaim}
      firstHost}
    {secondContract : AuthorityContract.{uKind, uCertificate, uSignature, uClaim}
      secondHost}
    (first : HeterogeneousTheory.CertifiedTranslation
      guestContract firstContract)
    (second : HeterogeneousTheory.CertifiedTranslation
      guestContract secondContract)
    (kind : GuestKind) (claim : guest.Claim kind)
    (certificate : guestContract.Certificate kind) :
    (firstContract.checker (first.mapKind kind)).check
        (first.mapClaim kind claim) (first.mapCertificate kind certificate) =
      (secondContract.checker (second.mapKind kind)).check
        (second.mapClaim kind claim)
        (second.mapCertificate kind certificate) :=
  (first.check_commutes kind claim certificate).trans
    (second.check_commutes kind claim certificate).symm

/-- Two conservative semantic realizations of one guest agree on whether the
translated claim is in proof scope.  No direct translation between the hosts
is required. -/
theorem scope_iff
    (first : HeterogeneousTheory.TheoryTranslation guest firstHost)
    (second : HeterogeneousTheory.TheoryTranslation guest secondHost)
    (firstConservative : first.Conservative)
    (secondConservative : second.Conservative)
    (kind : GuestKind) (claim : guest.Claim kind) :
    firstHost.Scope (first.mapKind kind) (first.mapClaim kind claim) <->
      secondHost.Scope (second.mapKind kind) (second.mapClaim kind claim) :=
  (HeterogeneousTheory.TheoryTranslation.scope_iff_of_conservative
      first firstConservative kind claim).trans
    (HeterogeneousTheory.TheoryTranslation.scope_iff_of_conservative
      second secondConservative kind claim).symm

/-- Semantic host irrelevance: conservative realizations agree on the
independently declared meaning of every translated guest claim. -/
theorem meaning_iff
    (first : HeterogeneousTheory.TheoryTranslation guest firstHost)
    (second : HeterogeneousTheory.TheoryTranslation guest secondHost)
    (firstConservative : first.Conservative)
    (secondConservative : second.Conservative)
    (kind : GuestKind) (claim : guest.Claim kind) :
    firstHost.Meaning (first.mapKind kind) (first.mapClaim kind claim) <->
      secondHost.Meaning (second.mapKind kind) (second.mapClaim kind claim) :=
  (HeterogeneousTheory.TheoryTranslation.meaning_iff_of_conservative
      first firstConservative kind claim).trans
    (HeterogeneousTheory.TheoryTranslation.meaning_iff_of_conservative
      second secondConservative kind claim).symm

end HostIrrelevance

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.HeterogeneousTheory.Canary

/-- The two coproduct injections semantically agree with their original hosts
on a concrete true claim. -/
theorem left_host_meaning_is_unchanged :
    (HeterogeneousTheory.Coproduct.theory leftTheory rightTheory).Meaning
        (.inl .only) true <->
      leftTheory.Meaning .only true :=
  HostIrrelevance.meaning_iff
    (HeterogeneousTheory.TheoryTranslation.identity leftTheory)
    (HeterogeneousTheory.Coproduct.leftInclusion
      leftTheory rightTheory leftContract rightContract).toTheoryTranslation
    ⟨by intro kind claim inScope; exact inScope,
      by intro kind claim meaningful; exact meaningful⟩
    (HeterogeneousTheory.Coproduct.leftInclusion_conservative
      leftTheory rightTheory leftContract rightContract)
    .only true

/-- Host irrelevance is not a license to cross authority tags: a right-kernel
certificate remains rejected at a left-kernel claim. -/
theorem semantic_agreement_does_not_erase_authority_tags :
    HeterogeneousTheory.Canary.pluralContract.toAuthorityFamily.packedChecker.check
      ⟨.inl .only, true⟩ ⟨.inr .only, ()⟩ = false :=
  HeterogeneousTheory.Canary.wrong_kernel_certificate_rejected

end Canary

#print axioms TheoryTranslation.comp_assoc
#print axioms CertifiedTranslation.comp_assoc
#print axioms CertifiedTranslation.toTheoryTranslation_comp
#print axioms ConservativeAuthorityRoute.postcompose
#print axioms ConservativeAuthorityRoute.check_eq_source
#print axioms ConservativeAuthorityRoute.scope_iff_source
#print axioms ConservativeAuthorityRoute.meaning_iff_source
#print axioms Coproduct.desc_unique
#print axioms HostIrrelevance.check_eq
#print axioms HostIrrelevance.scope_iff
#print axioms HostIrrelevance.meaning_iff
#print axioms Canary.left_host_meaning_is_unchanged
#print axioms Canary.semantic_agreement_does_not_erase_authority_tags

end Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
