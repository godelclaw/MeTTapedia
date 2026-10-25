import Mettapedia.TypeTheory.HypercubeHOLHub
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# LF formation profiles as MeTTa data

This module gives the existing profile-parametric LF checker a lossless
first-order boundary in the existing MeTTa `Atom` carrier.  The wire contains
both sort axioms and the ordered list of product rules.  A generator is not
trusted: the decoder accepts only the tagged shape, and formation-profile
joins pass the executable functionality gate before they are published.

The join service in this module is deliberately narrower than an arbitrary
union.  It joins profiles with identical sort axioms and refuses a product
union that would assign two result sorts to one pair of premise sorts.  Its
soundness theorem states that both input profiles embed in every published
result and that the result satisfies the functionality premise used by the
existing uniqueness-of-types theorem.

Conversion bubbles are separate inputs.  Serializing or joining a formation
profile here grants no beta, eta, iota, delta, equality-reflection or logical
authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.LFProfileAtomWire

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef.LF (Srt)
open Mettapedia.GSLT.LanguageDef.LFProfile
open Mettapedia.GSLT.LanguageDef.LFProfileChecker
open Mettapedia.TypeTheory.HypercubeBubbles
open Mettapedia.TypeTheory.HypercubeHOLHub
open Mettapedia.GSLT.Dedukti (Functional)

def encodeSort : Srt → Atom
  | .type => .symbol "lf-sort-type-v1"
  | .kind => .symbol "lf-sort-kind-v1"

def decodeSort : Atom → Option Srt
  | .symbol "lf-sort-type-v1" => some .type
  | .symbol "lf-sort-kind-v1" => some .kind
  | _ => none

@[simp] theorem decodeSort_encodeSort (sort : Srt) :
    decodeSort (encodeSort sort) = some sort := by
  cases sort <;> rfl

def encodeOptionalSort : Option Srt → Atom
  | none => .symbol "lf-sort-none-v1"
  | some sort => .expression [.symbol "lf-sort-some-v1", encodeSort sort]

def decodeOptionalSort : Atom → Option (Option Srt)
  | .symbol "lf-sort-none-v1" => some none
  | .expression [.symbol "lf-sort-some-v1", sort] => some <$> decodeSort sort
  | _ => none

@[simp] theorem decodeOptionalSort_encodeOptionalSort (sort : Option Srt) :
    decodeOptionalSort (encodeOptionalSort sort) = some sort := by
  cases sort with
  | none => rfl
  | some sort => simp [encodeOptionalSort, decodeOptionalSort]

def encodeProductRule (rule : ProductRule) : Atom :=
  .expression [.symbol "lf-product-rule-v1", encodeSort rule.domain,
    encodeSort rule.codomain, encodeSort rule.result]

def decodeProductRule : Atom → Option ProductRule
  | .expression [.symbol "lf-product-rule-v1", domain, codomain, result] => do
      return ⟨← decodeSort domain, ← decodeSort codomain, ← decodeSort result⟩
  | _ => none

@[simp] theorem decodeProductRule_encodeProductRule (rule : ProductRule) :
    decodeProductRule (encodeProductRule rule) = some rule := by
  cases rule
  simp [encodeProductRule, decodeProductRule]

def encodeProductRules (rules : List ProductRule) : Atom :=
  .expression (.symbol "lf-product-rules-v1" :: rules.map encodeProductRule)

def decodeProductRules : Atom → Option (List ProductRule)
  | .expression (.symbol "lf-product-rules-v1" :: rules) =>
      rules.mapM decodeProductRule
  | _ => none

private theorem mapM_decodeProductRule_encodeProductRule
    (rules : List ProductRule) :
    (rules.map encodeProductRule).mapM decodeProductRule = some rules := by
  induction rules with
  | nil => rfl
  | cons rule rules ih => simp [ih]

@[simp] theorem decodeProductRules_encodeProductRules
    (rules : List ProductRule) :
    decodeProductRules (encodeProductRules rules) = some rules := by
  exact mapM_decodeProductRule_encodeProductRule rules

/-- Canonical atom data for both sort axioms and every product rule. -/
def encode (profile : Profile) : Atom :=
  .expression [.symbol "lf-formation-profile-v1",
    encodeOptionalSort (profile.sortAxiom .type),
    encodeOptionalSort (profile.sortAxiom .kind),
    encodeProductRules profile.products]

/-- Decode only the canonical tagged profile shape. -/
def decode : Atom → Option Profile
  | .expression [.symbol "lf-formation-profile-v1", typeAxiomCode,
      kindAxiomCode, productCode] => do
      let typeResult ← decodeOptionalSort typeAxiomCode
      let kindResult ← decodeOptionalSort kindAxiomCode
      let products ← decodeProductRules productCode
      return {
        sortAxiom := fun
          | .type => typeResult
          | .kind => kindResult
        products := products
      }
  | _ => none

@[simp] theorem decode_encode (profile : Profile) :
    decode (encode profile) = some profile := by
  cases profile with
  | mk sortAxiom products =>
      have sortAxiomRoundtrip :
          (fun
            | .type => sortAxiom .type
            | .kind => sortAxiom .kind) = sortAxiom := by
        funext sort
        cases sort <;> rfl
      simp [encode, decode, sortAxiomRoundtrip]

theorem encode_injective : Function.Injective encode := by
  intro first second equal
  have decoded := congrArg decode equal
  simpa only [decode_encode, Option.some.injEq] using decoded

/-- Equality of the finite sort-axiom tables. -/
def sameSortAxioms (first second : Profile) : Prop :=
  ∀ sort, first.sortAxiom sort = second.sortAxiom sort

def sameSortAxiomsCheck (first second : Profile) : Bool :=
  decide (first.sortAxiom .type = second.sortAxiom .type) &&
    decide (first.sortAxiom .kind = second.sortAxiom .kind)

theorem sameSortAxiomsCheck_eq_true_iff (first second : Profile) :
    sameSortAxiomsCheck first second = true ↔ sameSortAxioms first second := by
  simp only [sameSortAxiomsCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨types, kinds⟩ sort
    cases sort
    · exact types
    · exact kinds
  · intro same
    exact ⟨same .type, same .kind⟩

/-- Join profiles only when their sort axioms agree and their product-rule
union passes the existing functionality admission test. -/
def admitProfileJoin (first second : Profile) : Option Profile :=
  if sameSortAxiomsCheck first second then
    match admitProductJoin first.products second.products with
    | some products => some { sortAxiom := first.sortAxiom, products := products }
    | none => none
  else none

/-- Every admitted profile join contains the complete left and right
formation judgments and satisfies the functionality premise used by
uniqueness of types. -/
theorem admitProfileJoin_sound {first second joined : Profile}
    (accepted : admitProfileJoin first second = some joined) :
    first ⊑ joined ∧ second ⊑ joined ∧ Functional joined := by
  unfold admitProfileJoin at accepted
  split at accepted
  · rename_i sameCheck
    cases productJoin : admitProductJoin first.products second.products with
    | none => simp [productJoin] at accepted
    | some products =>
        simp only [productJoin, Option.some.injEq] at accepted
        cases accepted
        have same := (sameSortAxiomsCheck_eq_true_iff first second).1 sameCheck
        have leftProducts := admitted_join_contains_left productJoin
        have rightProducts := admitted_join_contains_right productJoin
        have productFunctional :=
          (admitProductJoin_eq_some_iff _ _ _).1 productJoin |>.2
        refine ⟨?_, ?_, ?_⟩
        · exact ⟨fun _ _ axiomProof => axiomProof,
            fun _ member => leftProducts member⟩
        · constructor
          · intro source target axiomProof
            rw [same source]
            exact axiomProof
          · intro rule member
            exact rightProducts member
        · change Functional (profileOfProducts products)
          exact (functionalProducts_iff_profileFunctional products).1
              productFunctional
  · simp at accepted

/-- The atom-level service decodes two submitted profiles, applies the proved
formation join, and publishes only its canonical encoding. -/
def joinEncoded (first second : Atom) : Option Atom := do
  match decode first with
  | none => none
  | some firstProfile =>
      match decode second with
      | none => none
      | some secondProfile =>
          (admitProfileJoin firstProfile secondProfile).map encode

@[simp] theorem joinEncoded_encode (first second : Profile) :
    joinEncoded (encode first) (encode second) =
      (admitProfileJoin first second).map encode := by
  simp [joinEncoded]

/-- Successful atom-level publication exposes the exact decoded inputs and an
admitted functional upper profile. -/
theorem joinEncoded_sound {firstCode secondCode joinedCode : Atom}
    (accepted : joinEncoded firstCode secondCode = some joinedCode) :
    ∃ first second joined,
      decode firstCode = some first ∧
      decode secondCode = some second ∧
      joinedCode = encode joined ∧
      first ⊑ joined ∧ second ⊑ joined ∧ Functional joined := by
  unfold joinEncoded at accepted
  cases firstDecoded : decode firstCode with
  | none => simp [firstDecoded] at accepted
  | some first =>
      cases secondDecoded : decode secondCode with
      | none => simp [firstDecoded, secondDecoded] at accepted
      | some second =>
          cases joinedAccepted : admitProfileJoin first second with
          | none => simp [firstDecoded, secondDecoded, joinedAccepted] at accepted
          | some joined =>
              simp [firstDecoded, secondDecoded, joinedAccepted] at accepted
              obtain ⟨left, right, functional⟩ :=
                admitProfileJoin_sound joinedAccepted
              exact ⟨first, second, joined, rfl, rfl,
                accepted.symm,
                left, right, functional⟩

/-- Positive wire control: dependency and type operators have compatible
formation rules. -/
theorem dependent_operator_join_encoded :
    joinEncoded
      (encode (profileOfProducts dependentProducts))
      (encode (profileOfProducts [kindKindKind])) =
    some (encode (profileOfProducts sharedDependentOperatorProducts)) := by
  decide

/-- Negative wire control: the blind CoC/MettaKernel-prototype union remains
refused after serialization. -/
theorem coc_mettaKernelPrototype_join_encoded_refused :
    joinEncoded
      (encode (profileOfProducts constructionProducts))
      (encode mettaKernelKindResultPrototype) = none := by
  decide

private def conflictingTypeAxiomProfile : Profile where
  sortAxiom
    | .type => some .type
    | .kind => none
  products := []

/-- A profile with a conflicting sort axiom cannot be joined merely because
its product list is harmless. -/
theorem conflicting_sort_axiom_join_refused :
    joinEncoded (encode standardLF) (encode conflictingTypeAxiomProfile) = none := by
  decide

/-- Malformed data never reaches the profile admission decision. -/
theorem malformed_profile_refused :
    joinEncoded (.symbol "lf-formation-profile-v1")
      (encode standardLF) = none := by
  rfl

#print axioms decode_encode
#print axioms encode_injective
#print axioms sameSortAxiomsCheck_eq_true_iff
#print axioms admitProfileJoin_sound
#print axioms joinEncoded_encode
#print axioms joinEncoded_sound
#print axioms dependent_operator_join_encoded
#print axioms coc_mettaKernelPrototype_join_encoded_refused
#print axioms conflicting_sort_axiom_join_refused
#print axioms malformed_profile_refused

end Mettapedia.Languages.MeTTa.Bridges.GSLT.LFProfileAtomWire
