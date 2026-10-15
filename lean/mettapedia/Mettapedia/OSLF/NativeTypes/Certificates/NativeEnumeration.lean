import Mettapedia.OSLF.NativeTypes.Certificates.NativeRuleCoding
import Mettapedia.OSLF.NativeTypes.Certificates.RefinementChecking
import Mettapedia.OSLF.NativeTypes.Certificates.SeededSearch

/-!
# Constructive enumeration and fair search of the complete native grammar

Primitive symbol encodings generate the full scoped syntax and rule-payload
codec. The certificate search then uses the earned finite-tree encoding. No
candidate-stream completeness is supplied as a premise. Negative certificate
checks do not become refutations of native semantic membership.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.NativeEnumeration

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.TypeTheory.Calculi

deriving instance Encodable for Data

def atomicCodec {α : Type} [Encodable α] : Codec α :=
  Codec.nat.mapped Encodable.encode Encodable.decode Encodable.encodek

variable {S : NativeDependent.Refinement.Symbols}
variable [Encodable S.TypeSymbol] [Encodable S.TermSymbol] [Encodable S.PredicateSymbol]

def symbolCodecs : NativeWire.SymbolCodecs S where
  typeSymbol := atomicCodec
  termSymbol := atomicCodec
  predicateSymbol := atomicCodec

instance nativeRuleEncodable (D : NativeDependent.Refinement.Signature S) : Encodable (NativeDependent.Refinement.RuleCode D) :=
  Encodable.ofLeftInjection (NativeWire.rule symbolCodecs D).put
    (NativeWire.rule symbolCodecs D).get (NativeWire.rule symbolCodecs D).get_put

instance nativeRuleDecidableEq (D : NativeDependent.Refinement.Signature S) :
    DecidableEq (NativeDependent.Refinement.RuleCode D) :=
  (NativeWire.rule symbolCodecs D).decEq

variable {D : NativeDependent.Refinement.Signature S}
variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]

def search (judgment : NativeDependent.Refinement.Judgment S) (budget : Nat) :
    Search.State (Certificates.Refinement.presentation D) :=
  Search.search (P := Certificates.Refinement.presentation D) judgment budget

theorem search_sound (judgment : NativeDependent.Refinement.Judgment S) (budget : Nat)
    (certificate : Certificates.Refinement.Certificate D)
    (found : (search (D := D) judgment budget).found = some certificate) :
    ∃ derivation : NativeDependent.Refinement.Derivation D judgment,
      Certificates.Refinement.erase derivation = certificate :=
  Search.search_sound (P := Certificates.Refinement.presentation D) judgment budget certificate found

theorem discover_within_wire_bound (judgment : NativeDependent.Refinement.Judgment S)
    (certificate : Certificates.Refinement.Certificate D)
    (accepted : Certificates.Refinement.check certificate judgment = true) :
    ∃ result,
      (search (D := D) judgment (Tree.discoveryBound (Tree.wireSize certificate))).found = some result :=
  Search.discover_within_wire_bound (P := Certificates.Refinement.presentation D) judgment certificate accepted

theorem exact_resume (judgment : NativeDependent.Refinement.Judgment S) (first second : Nat) :
    search (D := D) judgment (first + second) =
      Search.run judgment second (search (D := D) judgment first) :=
  Search.run_add (P := Certificates.Refinement.presentation D) judgment first second Search.initial

theorem stable_conclusion (judgment : NativeDependent.Refinement.Judgment S) (budget extra : Nat)
    (certificate : Certificates.Refinement.Certificate D)
    (found : (search (D := D) judgment budget).found = some certificate) :
    search (D := D) judgment (budget + extra) = search (D := D) judgment budget :=
  Search.stable_conclusion (P := Certificates.Refinement.presentation D) judgment budget extra certificate found

def searchWithSeeds (seeds : List (Certificates.Refinement.Certificate D))
    (judgment : NativeDependent.Refinement.Judgment S) (budget : Nat) :
    Search.State (Certificates.Refinement.presentation D) :=
  SeededSearch.search seeds judgment budget

theorem seeded_search_sound (seeds : List (Certificates.Refinement.Certificate D))
    (judgment : NativeDependent.Refinement.Judgment S) (budget : Nat)
    (certificate : Certificates.Refinement.Certificate D)
    (found : (searchWithSeeds seeds judgment budget).found = some certificate) :
    ∃ derivation : NativeDependent.Refinement.Derivation D judgment,
      Certificates.Refinement.erase derivation = certificate :=
  SeededSearch.search_sound seeds judgment budget certificate found

theorem seeded_discover_within_wire_bound (seeds : List (Certificates.Refinement.Certificate D))
    (judgment : NativeDependent.Refinement.Judgment S) (certificate : Certificates.Refinement.Certificate D)
    (accepted : Certificates.Refinement.check certificate judgment = true) :
    ∃ result, (searchWithSeeds seeds judgment
      (SeededSearch.discoveryBound seeds.length (Tree.wireSize certificate))).found = some result :=
  SeededSearch.discover_within_wire_bound seeds judgment certificate accepted

theorem seeded_exact_resume (seeds : List (Certificates.Refinement.Certificate D))
    (judgment : NativeDependent.Refinement.Judgment S) (first second : Nat) :
    searchWithSeeds seeds judgment (first + second) =
      SeededSearch.run seeds judgment second (searchWithSeeds seeds judgment first) :=
  SeededSearch.run_add seeds judgment first second Search.initial

theorem seeded_stable_conclusion (seeds : List (Certificates.Refinement.Certificate D))
    (judgment : NativeDependent.Refinement.Judgment S) (budget extra : Nat)
    (certificate : Certificates.Refinement.Certificate D)
    (found : (searchWithSeeds seeds judgment budget).found = some certificate) :
    searchWithSeeds seeds judgment (budget + extra) = searchWithSeeds seeds judgment budget :=
  SeededSearch.stable_conclusion seeds judgment budget extra certificate found

end Mettapedia.OSLF.NativeTypes.Certificates.NativeEnumeration
