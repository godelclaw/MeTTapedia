import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeHeaderRanks

/-!
# Full native certificates and fair search for cube-enriched declarations

The same certificate checker and wire search used for the operational native
signature consume the generated cube signature. Every emitted primitive tree
has its independently formed contextual header, ordered substitution and
selected result. Certificate failure is not a semantic absence claim.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeDeclarations

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Certificates
open CubeEnrichment

deriving instance Encodable for HSort

def typeAlphabet (D : CubeEnrichment.Signature) : TypeSymbol D ≃ (D.Carrier ⊕ D.Carrier) where
  toFun symbol := match symbol with | .code carrier => .inl carrier | .typing carrier => .inr carrier
  invFun symbol := match symbol with | .inl carrier => .code carrier | .inr carrier => .typing carrier
  left_inv symbol := by cases symbol <;> rfl
  right_inv symbol := by cases symbol <;> rfl

def termAlphabet (D : CubeEnrichment.Signature) : TermSymbol D ≃
    ((D.Carrier × HSort) ⊕ (D.Former ⊕ (D.Carrier ⊕ D.Former))) where
  toFun symbol := match symbol with
    | .sort carrier sort => .inl (carrier, sort)
    | .former declaration => .inr (.inl declaration)
    | .starBox carrier => .inr (.inr (.inl carrier))
    | .formation declaration => .inr (.inr (.inr declaration))
  invFun symbol := match symbol with
    | .inl (carrier, sort) => .sort carrier sort
    | .inr (.inl declaration) => .former declaration
    | .inr (.inr (.inl carrier)) => .starBox carrier
    | .inr (.inr (.inr declaration)) => .formation declaration
  left_inv symbol := by cases symbol <;> rfl
  right_inv symbol := by
    cases symbol with
    | inl pair => cases pair; rfl
    | inr remaining => cases remaining with
      | inl declaration => rfl
      | inr remaining => cases remaining <;> rfl

instance typeSymbolDecidableEq {D : CubeEnrichment.Signature} [DecidableEq D.Carrier] :
    DecidableEq (TypeSymbol D) := fun first second =>
  decidable_of_iff ((typeAlphabet D) first = (typeAlphabet D) second) (typeAlphabet D).injective.eq_iff

instance termSymbolDecidableEq {D : CubeEnrichment.Signature} [DecidableEq D.Carrier] [DecidableEq D.Former] :
    DecidableEq (TermSymbol D) := fun first second =>
  decidable_of_iff ((termAlphabet D) first = (termAlphabet D) second) (termAlphabet D).injective.eq_iff

instance typeSymbolEncodable {D : CubeEnrichment.Signature} [Encodable D.Carrier] :
    Encodable (TypeSymbol D) := Encodable.ofEquiv _ (typeAlphabet D)

instance termSymbolEncodable {D : CubeEnrichment.Signature} [Encodable D.Carrier] [Encodable D.Former] :
    Encodable (TermSymbol D) := Encodable.ofEquiv _ (termAlphabet D)

variable {D : CubeEnrichment.Signature} (vertex : Vertex D)

/-- Every actual primitive occurrence uses the generated parameter telescope
and exact declared result; no separate formation checker is introduced. -/
def primitiveFormation (symbol : TermSymbol D) :
    Derivation (signature vertex) (.term ((signature vertex).termParameters symbol)
      (.primitive symbol TermExpr.var) ((signature vertex).termResult symbol)) := by
  have tree := deriveList (D := signature vertex)
    (.primitive ((signature vertex).termParameters symbol) symbol TermExpr.var)
    (.cons ((headers vertex).termHeader symbol) (.cons ((headers vertex).termHeader symbol)
      (.cons ((headers vertex).termResult symbol)
        (.cons (deriveList (.substitutionIdentity ((signature vertex).termParameters symbol))
          (.cons ((headers vertex).termHeader symbol) .nil)) .nil))))
  have equal : (RuleCode.primitive (D := signature vertex) ((signature vertex).termParameters symbol)
      symbol TermExpr.var).conclusion =
      .term ((signature vertex).termParameters symbol) (.primitive symbol TermExpr.var)
        ((signature vertex).termResult symbol) := by
    simp only [RuleCode.conclusion, TypeExpr.substitute_identity]
  exact equal ▸ tree

variable [DecidableEq D.Carrier] [DecidableEq D.Former]

/-- Emission erases actual common-native derivations to finite raw trees. -/
def primitiveCertificate (symbol : TermSymbol D) : Refinement.Certificate (signature vertex) :=
  Refinement.erase (primitiveFormation vertex symbol)

theorem primitiveCertificate_checked (symbol : TermSymbol D) :
    Refinement.check (primitiveCertificate vertex symbol)
      (.term ((signature vertex).termParameters symbol) (.primitive symbol TermExpr.var)
        ((signature vertex).termResult symbol)) = true :=
  Refinement.check_erase (primitiveFormation vertex symbol)

variable [Encodable D.Carrier] [Encodable D.Former]

/-- Countable symbol coding gives the complete common native grammar's fair
search, including dependent and logical certificates beyond primitive trees. -/
def search (judgment : Judgment (symbols D)) (budget : Nat) :
    Search.State (Refinement.presentation (signature vertex)) :=
  NativeEnumeration.search (D := signature vertex) judgment budget

theorem search_sound (judgment : Judgment (symbols D)) (budget : Nat)
    (certificate : Refinement.Certificate (signature vertex))
    (found : (search vertex judgment budget).found = some certificate) :
    ∃ tree : Derivation (signature vertex) judgment, Refinement.erase tree = certificate :=
  NativeEnumeration.search_sound judgment budget certificate found

theorem search_discovers (judgment : Judgment (symbols D))
    (certificate : Refinement.Certificate (signature vertex))
    (accepted : Refinement.check certificate judgment = true) :
    ∃ certificate',
      (search vertex judgment (Tree.discoveryBound (Tree.wireSize certificate))).found = some certificate' :=
  NativeEnumeration.discover_within_wire_bound judgment certificate accepted

theorem search_resume (judgment : Judgment (symbols D)) (first second : Nat) :
    search vertex judgment (first + second) =
      Search.run judgment second (search vertex judgment first) :=
  NativeEnumeration.exact_resume judgment first second

theorem search_stable (judgment : Judgment (symbols D)) (budget extra : Nat)
    (certificate : Refinement.Certificate (signature vertex))
    (found : (search vertex judgment budget).found = some certificate) :
    search vertex judgment (budget + extra) = search vertex judgment budget :=
  NativeEnumeration.stable_conclusion judgment budget extra certificate found

theorem no_budget_no_conclusion (judgment : Judgment (symbols D)) :
    (search vertex judgment 0).found = none := rfl

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeDeclarations
