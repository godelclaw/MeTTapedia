import Mettapedia.Logic.HOL.ConversionRecipes
import Mettapedia.Languages.MeTTa.Bridges.GSLT.FinitePolicyAtomWire

/-!
# Finite HOL conversion policies as MeTTa data

The existing conversion-recipe checker selects beta, eta and licensed
equations through a typed `ConversionRecipes.Policy`.  This module presents a
finite first-order source for those policies and a lossless encoding in the
existing MeTTa `Atom` carrier.

A manifest may enable beta or eta globally, enable either at selected HOL
types, enable all declarations, or select individual declaration indices.
Joining manifests is finite set union, and its denotation is exactly the
existing policy join.  It follows that both input conversion judgments embed
in the joined policy.

This is permission data.  A joined policy is not automatically normalizing,
confluent, decidable, conservative or cheap.  Those properties remain
separate certificates of the selected conversion package.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.HOLConversionPolicyAtomWire

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.Bridges.GSLT.FinitePolicyAtomWire
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.ConversionRecipes

universe u

variable {Base : Type u} {declarations : Nat}

/-- Finite selectors for the three fields of an existing conversion policy. -/
inductive Feature (Base : Type u) (declarations : Nat) where
  | betaAll
  | betaAt (type : Ty Base)
  | etaAll
  | etaAt (domain codomain : Ty Base)
  | equationAll
  | equation (index : Fin declarations)
  deriving DecidableEq, Repr

abbrev Manifest (Base : Type u) (declarations : Nat) :=
  List (Feature Base declarations)

def enabled [DecidableEq Base] (manifest : Manifest Base declarations)
    (feature : Feature Base declarations) : Bool :=
  decide (feature ∈ manifest)

/-- Interpret finite feature data as the existing typed policy. -/
def denote [DecidableEq Base] (manifest : Manifest Base declarations) :
    Policy Base declarations where
  beta type := enabled manifest .betaAll || enabled manifest (.betaAt type)
  eta domain codomain :=
    enabled manifest .etaAll || enabled manifest (.etaAt domain codomain)
  equation index :=
    enabled manifest .equationAll || enabled manifest (.equation index)

def join [DecidableEq Base]
    (first second : Manifest Base declarations) : Manifest Base declarations :=
  (first ++ second).eraseDups

@[simp] theorem enabled_join [DecidableEq Base]
    (first second : Manifest Base declarations)
    (feature : Feature Base declarations) :
    enabled (join first second) feature =
      (enabled first feature || enabled second feature) := by
  simp [enabled, join]

private theorem or_four (a b c d : Bool) :
    ((a || b) || (c || d)) = ((a || c) || (b || d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem policy_extensionality
    {first second : Policy Base declarations}
    (beta : first.beta = second.beta)
    (eta : first.eta = second.eta)
    (equation : first.equation = second.equation) : first = second := by
  cases first
  cases second
  simp_all

/-- Finite union agrees exactly with the existing pointwise policy join. -/
theorem denote_join [DecidableEq Base]
    (first second : Manifest Base declarations) :
    denote (join first second) = (denote first).join (denote second) := by
  apply policy_extensionality
  · funext type
    change (enabled (join first second) .betaAll ||
        enabled (join first second) (.betaAt type)) =
      ((enabled first .betaAll || enabled first (.betaAt type)) ||
        (enabled second .betaAll || enabled second (.betaAt type)))
    rw [enabled_join, enabled_join]
    exact or_four
      (enabled first (.betaAll : Feature Base declarations))
      (enabled second (.betaAll : Feature Base declarations))
      (enabled first (.betaAt type)) (enabled second (.betaAt type))
  · funext domain codomain
    change (enabled (join first second) .etaAll ||
        enabled (join first second) (.etaAt domain codomain)) =
      ((enabled first .etaAll || enabled first (.etaAt domain codomain)) ||
        (enabled second .etaAll || enabled second (.etaAt domain codomain)))
    rw [enabled_join, enabled_join]
    exact or_four
      (enabled first (.etaAll : Feature Base declarations))
      (enabled second (.etaAll : Feature Base declarations))
      (enabled first (.etaAt domain codomain))
      (enabled second (.etaAt domain codomain))
  · funext index
    change (enabled (join first second) .equationAll ||
        enabled (join first second) (.equation index)) =
      ((enabled first .equationAll || enabled first (.equation index)) ||
        (enabled second .equationAll || enabled second (.equation index)))
    rw [enabled_join, enabled_join]
    exact or_four
      (enabled first (.equationAll : Feature Base declarations))
      (enabled second (.equationAll : Feature Base declarations))
      (enabled first (.equation index)) (enabled second (.equation index))

theorem denote_extends_join_left [DecidableEq Base]
    (first second : Manifest Base declarations) :
    (denote first).Extends (denote (join first second)) := by
  rw [denote_join]
  exact Policy.extends_join_left _ _

theorem denote_extends_join_right [DecidableEq Base]
    (first second : Manifest Base declarations) :
    (denote second).Extends (denote (join first second)) := by
  rw [denote_join]
  exact Policy.extends_join_right _ _

/-! ## Lossless atom wire -/

/-- A caller supplies the atom representation of its base type names. -/
structure BaseCodec (Base : Type u) where
  encode : Base → Atom
  decode : Atom → Option Base
  decode_encode : ∀ name, decode (encode name) = some name

def encodeType (codec : BaseCodec Base) : Ty Base → Atom
  | .prop => .symbol "hol-type-prop-v1"
  | .base name =>
      .expression [.symbol "hol-type-base-v1", codec.encode name]
  | .arr domain codomain =>
      .expression [.symbol "hol-type-arrow-v1",
        encodeType codec domain, encodeType codec codomain]

def decodeType (codec : BaseCodec Base) : Atom → Option (Ty Base)
  | .symbol "hol-type-prop-v1" => some .prop
  | .expression [.symbol "hol-type-base-v1", name] =>
      .base <$> codec.decode name
  | .expression [.symbol "hol-type-arrow-v1", domain, codomain] => do
      return .arr (← decodeType codec domain) (← decodeType codec codomain)
  | _ => none

@[simp] theorem decodeType_encodeType (codec : BaseCodec Base)
    (type : Ty Base) : decodeType codec (encodeType codec type) = some type := by
  induction type with
  | prop => rfl
  | base name => simp [encodeType, decodeType, codec.decode_encode]
  | arr domain codomain ihDomain ihCodomain =>
      simp [encodeType, decodeType, ihDomain, ihCodomain]

def encodeFeature (codec : BaseCodec Base) :
    Feature Base declarations → Atom
  | .betaAll => .symbol "hol-conversion-beta-all-v1"
  | .betaAt type =>
      .expression [.symbol "hol-conversion-beta-at-v1", encodeType codec type]
  | .etaAll => .symbol "hol-conversion-eta-all-v1"
  | .etaAt domain codomain =>
      .expression [.symbol "hol-conversion-eta-at-v1",
        encodeType codec domain, encodeType codec codomain]
  | .equationAll => .symbol "hol-conversion-equation-all-v1"
  | .equation index =>
      .expression [.symbol "hol-conversion-equation-v1", encodeFin index]

def decodeFeature (codec : BaseCodec Base) (declarations : Nat) :
    Atom → Option (Feature Base declarations)
  | .symbol "hol-conversion-beta-all-v1" => some .betaAll
  | .expression [.symbol "hol-conversion-beta-at-v1", type] =>
      .betaAt <$> decodeType codec type
  | .symbol "hol-conversion-eta-all-v1" => some .etaAll
  | .expression [.symbol "hol-conversion-eta-at-v1", domain, codomain] => do
      return .etaAt (← decodeType codec domain) (← decodeType codec codomain)
  | .symbol "hol-conversion-equation-all-v1" => some .equationAll
  | .expression [.symbol "hol-conversion-equation-v1", index] =>
      match decodeFin declarations index with
      | some decoded => some (Feature.equation (Base := Base) decoded)
      | none => none
  | _ => none

@[simp] theorem decodeFeature_encodeFeature (codec : BaseCodec Base)
    (feature : Feature Base declarations) :
    decodeFeature codec declarations (encodeFeature codec feature) =
      some feature := by
  cases feature <;> simp [encodeFeature, decodeFeature]

def encode (codec : BaseCodec Base) (manifest : Manifest Base declarations) : Atom :=
  .expression (.symbol "hol-conversion-policy-v1" ::
    manifest.map (encodeFeature codec))

def decode (codec : BaseCodec Base) (declarations : Nat) :
    Atom → Option (Manifest Base declarations)
  | .expression (.symbol "hol-conversion-policy-v1" :: features) =>
      features.mapM (decodeFeature codec declarations)
  | _ => none

private theorem mapM_decodeFeature_encodeFeature (codec : BaseCodec Base)
    (manifest : Manifest Base declarations) :
    (manifest.map (encodeFeature codec)).mapM
      (decodeFeature codec declarations) = some manifest := by
  induction manifest with
  | nil => rfl
  | cons feature manifest ih => simp [ih]

@[simp] theorem decode_encode (codec : BaseCodec Base)
    (manifest : Manifest Base declarations) :
    decode codec declarations (encode codec manifest) = some manifest :=
  mapM_decodeFeature_encodeFeature codec manifest

theorem encode_injective (codec : BaseCodec Base) :
    Function.Injective (encode codec : Manifest Base declarations → Atom) := by
  intro first second same
  have decoded := congrArg (decode codec declarations) same
  simpa only [decode_encode, Option.some.injEq] using decoded

def joinEncoded [DecidableEq Base] (declarations : Nat) (codec : BaseCodec Base)
    (first second : Atom) : Option Atom :=
  match decode codec declarations first, decode codec declarations second with
  | some firstManifest, some secondManifest =>
      some (encode codec (join firstManifest secondManifest))
  | _, _ => none

@[simp] theorem joinEncoded_encode [DecidableEq Base]
    (codec : BaseCodec Base) (first second : Manifest Base declarations) :
    joinEncoded declarations codec (encode codec first) (encode codec second) =
      some (encode codec (join first second)) := by
  simp [joinEncoded]

/-- Every published atom is the canonical encoding of the union of the two
exactly decoded manifests. -/
theorem joinEncoded_sound [DecidableEq Base] (codec : BaseCodec Base)
    {firstCode secondCode output : Atom}
    (accepted : joinEncoded declarations codec firstCode secondCode = some output) :
    ∃ first second : Manifest Base declarations,
      decode codec declarations firstCode = some first ∧
      decode codec declarations secondCode = some second ∧
      output = encode codec (join first second) := by
  unfold joinEncoded at accepted
  cases firstDecoded : decode codec declarations firstCode with
  | none => simp [firstDecoded] at accepted
  | some first =>
      cases secondDecoded : decode codec declarations secondCode with
      | none => simp [firstDecoded, secondDecoded] at accepted
      | some second =>
          simp [firstDecoded, secondDecoded] at accepted
          exact ⟨first, second, rfl, rfl, accepted.symm⟩

/-! ## Positive and negative controls -/

def unitCodec : BaseCodec Unit where
  encode _ := .symbol "hol-base-unit-v1"
  decode
    | .symbol "hol-base-unit-v1" => some ()
    | _ => none
  decode_encode _ := rfl

def betaOnlyManifest : Manifest Unit 2 := [.betaAll]
def etaOnlyManifest : Manifest Unit 2 := [.etaAll]

theorem beta_eta_manifest_join :
    denote (join betaOnlyManifest etaOnlyManifest) =
      (Policy.betaEta (Base := Unit) 2) := by
  apply policy_extensionality <;> funext <;> rfl

theorem beta_eta_encoded_join :
    joinEncoded 2 unitCodec (encode unitCodec betaOnlyManifest)
      (encode unitCodec etaOnlyManifest) =
        some (encode unitCodec (join betaOnlyManifest etaOnlyManifest)) := by
  exact joinEncoded_encode unitCodec betaOnlyManifest etaOnlyManifest

theorem out_of_range_equation_refused :
    decodeFeature unitCodec 2
      (.expression [.symbol "hol-conversion-equation-v1", encodeNat 2]) = none := by
  simp [decodeFeature, decodeFin]

theorem malformed_policy_refused :
    decode unitCodec 2 (.symbol "hol-conversion-policy-v1") = none := by
  rfl

#print axioms enabled_join
#print axioms denote_join
#print axioms denote_extends_join_left
#print axioms denote_extends_join_right
#print axioms decodeType_encodeType
#print axioms decodeFeature_encodeFeature
#print axioms decode_encode
#print axioms encode_injective
#print axioms joinEncoded_encode
#print axioms joinEncoded_sound
#print axioms beta_eta_manifest_join
#print axioms beta_eta_encoded_join
#print axioms out_of_range_equation_refused
#print axioms malformed_policy_refused

end Mettapedia.Languages.MeTTa.Bridges.GSLT.HOLConversionPolicyAtomWire
