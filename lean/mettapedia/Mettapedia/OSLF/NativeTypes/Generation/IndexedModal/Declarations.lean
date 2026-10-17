import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Parameters
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EarlierDeclarations
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureExtensionFormation

/-!
# Target-premised modal classifier declarations

The original free-code signature is preserved. The additional operations
consume index bundles, rely classifiers and a mandatory dependent target
classifier, and return a certified classifier of the focus carrier. These
operations are distinct from the older free-code former operations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Declarations

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open CubeEnrichment CubeNativeDeclarations

variable {D : CubeEnrichment.Signature} {I : Type}
    (vertex : Vertex D) (interfaces : I → Interface D.Carrier)

abbrev extraSymbols : Symbols where
  TypeSymbol := Empty
  TermSymbol := I
  PredicateSymbol := Empty
  typeArity symbol := nomatch symbol
  termArity index := arity (interfaces index)
  predicateArity symbol := nomatch symbol

abbrev symbols := SignatureSum.symbols (CubeNativeDeclarations.symbols D)
  (extraSymbols interfaces)

def extraRanks : SignatureSum.Ranks (extraSymbols interfaces) :=
  ⟨(fun symbol => nomatch symbol), (fun _ => 5), (fun symbol => nomatch symbol)⟩

theorem typeRank_earlier (symbol : (CubeNativeDeclarations.symbols D).TypeSymbol) :
    (Theory vertex).typeRank symbol < 5 := by cases symbol <;> simp [Theory, CubeNativeDeclarations.signature, CubeNativeDeclarations.ranks]

theorem termRank_earlier (symbol : (CubeNativeDeclarations.symbols D).TermSymbol) :
    (Theory vertex).termRank symbol < 5 := by cases symbol <;> simp [Theory, CubeNativeDeclarations.signature, CubeNativeDeclarations.ranks]

theorem predicateRank_earlier (symbol : (CubeNativeDeclarations.symbols D).PredicateSymbol) :
    (Theory vertex).predicateRank symbol < 5 := nomatch symbol

def signature : Signature (symbols interfaces) where
  typeRank := (SignatureSum.sumRanks (SignatureSum.ranks (Theory vertex))
    (extraRanks interfaces)).typeRank
  termRank := (SignatureSum.sumRanks (SignatureSum.ranks (Theory vertex))
    (extraRanks interfaces)).termRank
  predicateRank := (SignatureSum.sumRanks (SignatureSum.ranks (Theory vertex))
    (extraRanks interfaces)).predicateRank
  typeParameters symbol := match symbol with
    | .inl symbol => SignatureSum.contextLeft ((Theory vertex).typeParameters symbol)
    | .inr impossible => nomatch impossible
  termParameters symbol := match symbol with
    | .inl symbol => SignatureSum.contextLeft ((Theory vertex).termParameters symbol)
    | .inr index => SignatureSum.contextLeft (parameters (interfaces index))
  predicateParameters symbol := match symbol with
    | .inl symbol => SignatureSum.contextLeft ((Theory vertex).predicateParameters symbol)
    | .inr impossible => nomatch impossible
  termResult symbol := match symbol with
    | .inl symbol => SignatureSum.typeLeft ((Theory vertex).termResult symbol)
    | .inr index => SignatureSum.typeLeft (result (interfaces index))
  typeParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
      exact (SignatureSum.contextLeft_before _ _ _ _).mpr
            ((Theory vertex).typeParameters_before symbol)
    | inr impossible =>
      exact nomatch impossible
  termParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
      exact (SignatureSum.contextLeft_before _ _ _ _).mpr
            ((Theory vertex).termParameters_before symbol)
    | inr index =>
      exact (SignatureSum.contextLeft_before _ _ _ _).mpr
            (EarlierDeclarations.contextEarlier (Theory vertex) 5 (typeRank_earlier vertex)
              (termRank_earlier vertex) (predicateRank_earlier vertex) _)
  predicateParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
      exact (SignatureSum.contextLeft_before _ _ _ _).mpr
            ((Theory vertex).predicateParameters_before symbol)
    | inr impossible =>
      exact nomatch impossible
  termResult_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
      exact (SignatureSum.typeLeft_before _ _ _ _).mpr
            ((Theory vertex).termResult_before symbol)
    | inr index =>
      exact (SignatureSum.typeLeft_before _ _ _ _).mpr
            (EarlierDeclarations.typeEarlier (Theory vertex) 5 (typeRank_earlier vertex)
              (termRank_earlier vertex) (predicateRank_earlier vertex) _)

theorem preserves : SignatureExtension.Preserves (Theory vertex) (signature vertex interfaces) where
  typeParameters _ := rfl
  termParameters _ := rfl
  predicateParameters _ := rfl
  termResult _ := rfl
  typeRank _ := rfl
  termRank _ := rfl
  predicateRank _ := rfl

def carry {judgment : Judgment (CubeNativeDeclarations.symbols D)}
    (tree : Derivation (Theory vertex) judgment) :
    Derivation (signature vertex interfaces) (SignatureSum.judgmentLeft judgment) :=
  SignatureExtension.derivation _ _ (preserves vertex interfaces) tree

def headerFormation : HeaderFormation (signature vertex interfaces) where
  typeHeader symbol := match symbol with
    | .inl symbol => carry vertex interfaces ((CubeNativeDeclarations.headers vertex).typeHeader symbol)
    | .inr impossible => nomatch impossible
  typeHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
      exact SignatureExtension.derivation_before _ _ (preserves vertex interfaces) _ _
            ((CubeNativeDeclarations.headers vertex).typeHeader_before symbol)
    | inr impossible =>
      exact nomatch impossible
  termHeader symbol := match symbol with
    | .inl symbol => carry vertex interfaces ((CubeNativeDeclarations.headers vertex).termHeader symbol)
    | .inr index => carry vertex interfaces (parametersFormed vertex (interfaces index))
  termHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
      exact SignatureExtension.derivation_before _ _ (preserves vertex interfaces) _ _
            ((CubeNativeDeclarations.headers vertex).termHeader_before symbol)
    | inr index =>
      exact SignatureExtension.derivation_before _ _ (preserves vertex interfaces) _ 5
            (EarlierDeclarations.derivationEarlier (Theory vertex) 5 (typeRank_earlier vertex)
              (termRank_earlier vertex) (predicateRank_earlier vertex) _)
  termResult symbol := match symbol with
    | .inl symbol => carry vertex interfaces ((CubeNativeDeclarations.headers vertex).termResult symbol)
    | .inr index => carry vertex interfaces (resultFormed vertex (interfaces index))
  termResult_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
      exact SignatureExtension.derivation_before _ _ (preserves vertex interfaces) _ _
            ((CubeNativeDeclarations.headers vertex).termResult_before symbol)
    | inr index =>
      exact SignatureExtension.derivation_before _ _ (preserves vertex interfaces) _ 5
            (EarlierDeclarations.derivationEarlier (Theory vertex) 5 (typeRank_earlier vertex)
              (termRank_earlier vertex) (predicateRank_earlier vertex) _)
  predicateHeader symbol := match symbol with
    | .inl symbol => carry vertex interfaces ((CubeNativeDeclarations.headers vertex).predicateHeader symbol)
    | .inr impossible => nomatch impossible
  predicateHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
      exact SignatureExtension.derivation_before _ _ (preserves vertex interfaces) _ _
            ((CubeNativeDeclarations.headers vertex).predicateHeader_before symbol)
    | inr impossible =>
      exact nomatch impossible

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Declarations
