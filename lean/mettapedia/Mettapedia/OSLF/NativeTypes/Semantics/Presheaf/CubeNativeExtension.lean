import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeHeaderRanks
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureExtensionFormation

/-!
# Operational injection into a left-preserving native cube enrichment

All existing constructor and operational declarations remain on the left.
A new injection consumes a value at its already formed authored carrier and
returns a value of the freely adjoined code carrier. The old carrier is not
silently replaced with a predicate power or an internal universe.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeExtension

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

variable {S : Symbols} {D : CubeEnrichment.Signature}

/-- Existing authored carrier trees are retained, including their exact scope
and earlier-declaration proofs. They introduce no new semantic oracle. -/
structure SourceCarriers (source : Signature S) (D : CubeEnrichment.Signature) (bound : Nat) where
  type : D.Carrier → TypeExpr S 0
  formed : ∀ carrier, Derivation source (.type .nil (type carrier))
  before : ∀ carrier, (formed carrier).before bound

abbrev injectionSymbols (D : CubeEnrichment.Signature) : Symbols where
  TypeSymbol := Empty
  TermSymbol := D.Carrier
  PredicateSymbol := Empty
  typeArity symbol := nomatch symbol
  termArity _ := 1
  predicateArity symbol := nomatch symbol

variable (source : Signature S) (vertex : CubeEnrichment.Vertex D) (bound : Nat)
    (carriers : SourceCarriers source D bound)

abbrev core (source : Signature S) (vertex : CubeEnrichment.Vertex D) := SignatureSum.signature source (CubeNativeDeclarations.signature vertex)
abbrev symbols (S : Symbols) (D : CubeEnrichment.Signature) := SignatureSum.symbols (SignatureSum.symbols S (CubeNativeDeclarations.symbols D)) (injectionSymbols D)

abbrev sourceType (source : Signature S) (bound : Nat)
    (carriers : SourceCarriers source D bound) (carrier : D.Carrier) : TypeExpr (symbols S D) 0 :=
  SignatureSum.typeLeft (SignatureSum.typeLeft (carriers.type carrier))

abbrev codeType (S : Symbols) (D : CubeEnrichment.Signature) (carrier : D.Carrier) (n : Nat) : TypeExpr (symbols S D) n :=
  .family (.inl (.inr (.code carrier))) Fin.elim0

def injectionContext (source : Signature S) (bound : Nat)
    (carriers : SourceCarriers source D bound) (carrier : D.Carrier) : ContextExpr (symbols S D) 1 :=
  .snoc .nil (sourceType source bound carriers carrier)

def extraRanks (D : CubeEnrichment.Signature) (bound : Nat) : SignatureSum.Ranks (injectionSymbols D) :=
  ⟨(fun symbol => nomatch symbol), (fun _ => bound), (fun symbol => nomatch symbol)⟩

def signature (source : Signature S) (vertex : CubeEnrichment.Vertex D)
    (bound : Nat) (carriers : SourceCarriers source D bound) (positive : 0 < bound) : Signature (symbols S D) where
  typeRank := (SignatureSum.sumRanks (SignatureSum.ranks (core source vertex)) (extraRanks D bound)).typeRank
  termRank := (SignatureSum.sumRanks (SignatureSum.ranks (core source vertex)) (extraRanks D bound)).termRank
  predicateRank := (SignatureSum.sumRanks (SignatureSum.ranks (core source vertex)) (extraRanks D bound)).predicateRank
  typeParameters symbol := match symbol with
    | .inl symbol => SignatureSum.contextLeft ((core source vertex).typeParameters symbol)
    | .inr impossible => nomatch impossible
  termParameters symbol := match symbol with
    | .inl symbol => SignatureSum.contextLeft ((core source vertex).termParameters symbol)
    | .inr carrier => injectionContext source bound carriers carrier
  predicateParameters symbol := match symbol with
    | .inl symbol => SignatureSum.contextLeft ((core source vertex).predicateParameters symbol)
    | .inr impossible => nomatch impossible
  termResult symbol := match symbol with
    | .inl symbol => SignatureSum.typeLeft ((core source vertex).termResult symbol)
    | .inr carrier => codeType S D carrier 1
  typeParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (SignatureSum.contextLeft_before _ _ _ _).mpr
          ((core source vertex).typeParameters_before symbol)
    | inr impossible => exact nomatch impossible
  termParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (SignatureSum.contextLeft_before _ _ _ _).mpr
          ((core source vertex).termParameters_before symbol)
    | inr carrier =>
        refine ⟨True.intro, ?_⟩
        apply (SignatureSum.typeLeft_before _ _ _ _).mpr
        apply (SignatureSum.typeLeft_signature_before source (CubeNativeDeclarations.signature vertex) _ _).mpr
        exact ((carriers.formed carrier).before_judgment (carriers.before carrier)).2
  predicateParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (SignatureSum.contextLeft_before _ _ _ _).mpr
          ((core source vertex).predicateParameters_before symbol)
    | inr impossible => exact nomatch impossible
  termResult_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (SignatureSum.typeLeft_before _ _ _ _).mpr
          ((core source vertex).termResult_before symbol)
    | inr carrier => exact ⟨positive, fun position => Fin.elim0 position⟩

variable (positive : 0 < bound)

theorem preserves : SignatureExtension.Preserves (core source vertex) (signature source vertex bound carriers positive) where
  typeParameters _ := rfl
  termParameters _ := rfl
  predicateParameters _ := rfl
  termResult _ := rfl
  typeRank _ := rfl
  termRank _ := rfl
  predicateRank _ := rfl

def carry {judgment : Judgment (SignatureSum.symbols S (CubeNativeDeclarations.symbols D))}
    (tree : Derivation (core source vertex) judgment) :
    Derivation (signature source vertex bound carriers positive) (SignatureSum.judgmentLeft judgment) :=
  SignatureExtension.derivation _ _ (preserves source vertex bound carriers positive) tree

def sourceCarrierFormed (carrier : D.Carrier) :
    Derivation (signature source vertex bound carriers positive)
      (.type .nil (sourceType source bound carriers carrier)) :=
  carry source vertex bound carriers positive
    (SignatureSum.derivationLeft source (CubeNativeDeclarations.signature vertex) (carriers.formed carrier))

def emptyFormed : Derivation (signature source vertex bound carriers positive) (.context .nil) :=
  deriveList .contextNil .nil

def injectionContextFormed (carrier : D.Carrier) :
    Derivation (signature source vertex bound carriers positive)
      (.context (injectionContext source bound carriers carrier)) :=
  deriveList (.contextExtend .nil (sourceType source bound carriers carrier))
    (.cons (emptyFormed source vertex bound carriers positive)
      (.cons (sourceCarrierFormed source vertex bound carriers positive carrier) .nil))

def codeFormed (carrier : D.Carrier) {n : Nat} {context : ContextExpr (symbols S D) n}
    (formed : Derivation (signature source vertex bound carriers positive) (.context context)) :
    Derivation (signature source vertex bound carriers positive) (.type context (codeType S D carrier n)) :=
  deriveList (.typeFamily context (.inl (.inr (.code carrier))) Fin.elim0)
    (.cons formed (.cons (emptyFormed source vertex bound carriers positive)
      (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil)))

theorem emptyFormed_before (limit : Nat) :
    (emptyFormed source vertex bound carriers positive).before limit :=
  deriveList_before .contextNil .nil limit True.intro True.intro

theorem sourceCarrierFormed_before (carrier : D.Carrier) :
    (sourceCarrierFormed source vertex bound carriers positive carrier).before bound :=
  SignatureExtension.derivation_before _ _ (preserves source vertex bound carriers positive) _ bound
    (SignatureSum.derivationLeft_before source (CubeNativeDeclarations.signature vertex) _ bound
      (carriers.before carrier))

theorem injectionContextFormed_before (carrier : D.Carrier) :
    (injectionContextFormed source vertex bound carriers positive carrier).before bound := by
  apply deriveList_before
  · refine ⟨True.intro, ?_⟩
    exact ((sourceCarrierFormed source vertex bound carriers positive carrier).before_judgment
      (sourceCarrierFormed_before source vertex bound carriers positive carrier)).2
  · exact ⟨emptyFormed_before source vertex bound carriers positive bound,
      sourceCarrierFormed_before source vertex bound carriers positive carrier, True.intro⟩

theorem codeFormed_before (carrier : D.Carrier) {n : Nat} {context : ContextExpr (symbols S D) n}
    (formed : Derivation (signature source vertex bound carriers positive) (.context context))
    (ordered : formed.before bound) :
    (codeFormed source vertex bound carriers positive carrier formed).before bound := by
  have contextBefore := formed.before_judgment ordered
  apply deriveList_before
  · exact ⟨contextBefore, positive, fun position => Fin.elim0 position⟩
  · exact ⟨ordered, emptyFormed_before source vertex bound carriers positive bound,
      deriveList_before (.substitutionNil context) _ bound
        ⟨contextBefore, True.intro, fun position => Fin.elim0 position⟩ ⟨ordered, True.intro⟩,
      True.intro⟩

/-- The source alphabet's declarations and all its derivations survive before
new source-to-code injections are installed. -/
def headers (sourceHeaders : HeaderFormation source)
    (cubeHeaders : HeaderFormation (CubeNativeDeclarations.signature vertex)) :
    HeaderFormation (signature source vertex bound carriers positive) where
  typeHeader symbol := match symbol with
    | .inl symbol => carry source vertex bound carriers positive
          ((SignatureSum.headers source _ sourceHeaders cubeHeaders).typeHeader symbol)
    | .inr impossible => nomatch impossible
  typeHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact SignatureExtension.derivation_before _ _
          (preserves source vertex bound carriers positive) _ _
          ((SignatureSum.headers source _ sourceHeaders cubeHeaders).typeHeader_before symbol)
    | inr impossible => exact nomatch impossible
  termHeader symbol := match symbol with
    | .inl symbol => carry source vertex bound carriers positive
          ((SignatureSum.headers source _ sourceHeaders cubeHeaders).termHeader symbol)
    | .inr carrier => injectionContextFormed source vertex bound carriers positive carrier
  termHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact SignatureExtension.derivation_before _ _
          (preserves source vertex bound carriers positive) _ _
          ((SignatureSum.headers source _ sourceHeaders cubeHeaders).termHeader_before symbol)
    | inr carrier => exact injectionContextFormed_before source vertex bound carriers positive carrier
  termResult symbol := match symbol with
    | .inl symbol => carry source vertex bound carriers positive
          ((SignatureSum.headers source _ sourceHeaders cubeHeaders).termResult symbol)
    | .inr carrier => codeFormed source vertex bound carriers positive carrier
        (injectionContextFormed source vertex bound carriers positive carrier)
  termResult_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact SignatureExtension.derivation_before _ _
          (preserves source vertex bound carriers positive) _ _
          ((SignatureSum.headers source _ sourceHeaders cubeHeaders).termResult_before symbol)
    | inr carrier =>
        exact codeFormed_before source vertex bound carriers positive carrier _
          (injectionContextFormed_before source vertex bound carriers positive carrier)
  predicateHeader symbol := match symbol with
    | .inl symbol => carry source vertex bound carriers positive
          ((SignatureSum.headers source _ sourceHeaders cubeHeaders).predicateHeader symbol)
    | .inr impossible => nomatch impossible
  predicateHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact SignatureExtension.derivation_before _ _
          (preserves source vertex bound carriers positive) _ _
          ((SignatureSum.headers source _ sourceHeaders cubeHeaders).predicateHeader_before symbol)
    | inr impossible => exact nomatch impossible



/-- The computed enrichment needs no caller-supplied cube formation record. -/
def computedHeaders (sourceHeaders : HeaderFormation source) :
    HeaderFormation (signature source vertex bound carriers positive) :=
  headers source vertex bound carriers positive sourceHeaders (CubeNativeDeclarations.headers vertex)

def inject {n : Nat} (carrier : D.Carrier) (value : TermExpr (symbols S D) n) :
    TermExpr (symbols S D) n := .primitive (.inr carrier) ((fun _ => value))

@[simp] theorem codeType_substitute (carrier : D.Carrier) {n m : Nat}
    (mapping : Substitution (symbols S D) n m) :
    (codeType S D carrier n).substitute mapping = codeType S D carrier m := by
  apply congrArg (TypeExpr.family (S := symbols S D) (.inl (.inr (.code carrier))))
  funext position
  exact Fin.elim0 position

theorem closed_empty_substitute (type : TypeExpr (symbols S D) 0) {n : Nat} :
    type.substitute (Fin.elim0 : Substitution (symbols S D) 0 n) =
      type.rename (Fin.elim0 : Renaming 0 n) := by
  rw [← TypeExpr.substitute_variables]
  congr 1
  funext position
  exact Fin.elim0 position

/-- Actual native rule application embeds an authored value into the new
carrier while retaining its original contextual formation and typing tree. -/
def injectFormation {n : Nat} {context : ContextExpr (symbols S D) n}
    (carrier : D.Carrier) (value : TermExpr (symbols S D) n)
    (formed : Derivation (signature source vertex bound carriers positive) (.context context))
    (typed : Derivation (signature source vertex bound carriers positive)
      (.term context value ((sourceType source bound carriers carrier).rename Fin.elim0))) :
    Derivation (signature source vertex bound carriers positive)
      (.term context (inject carrier value) (codeType S D carrier n)) := by
  have adjusted : Derivation (signature source vertex bound carriers positive)
      (.term context value ((sourceType source bound carriers carrier).substitute Fin.elim0)) :=
    (congrArg (Judgment.term context value)
      (closed_empty_substitute (sourceType source bound carriers carrier))).symm ▸ typed
  let arguments := deriveList (.substitutionExtend context .nil
    (sourceType source bound carriers carrier) Fin.elim0 value)
    (.cons (deriveList (.substitutionNil context) (.cons formed .nil))
      (.cons (sourceCarrierFormed source vertex bound carriers positive carrier) (.cons adjusted .nil)))
  have same : extendSubstitution (Fin.elim0 : Substitution (symbols S D) 0 n) value =
      (fun _ => value) := by
    funext position
    cases position using Fin.cases with
    | zero => rfl
    | succ impossible => exact Fin.elim0 impossible
  have arguments' : Derivation (signature source vertex bound carriers positive)
      (.substitution context (injectionContext source bound carriers carrier) ((fun _ => value))) :=
    (congrArg (Judgment.substitution context (injectionContext source bound carriers carrier)) same) ▸ arguments
  have tree := deriveList (D := signature source vertex bound carriers positive) (.primitive context (.inr carrier)
    ((fun _ => value) : Substitution (symbols S D) 1 n))
    (.cons formed (.cons (injectionContextFormed source vertex bound carriers positive carrier)
      (.cons (codeFormed source vertex bound carriers positive carrier
        (injectionContextFormed source vertex bound carriers positive carrier)) (.cons arguments' .nil))))
  have equal : (RuleCode.primitive (D := signature source vertex bound carriers positive)
      context (.inr carrier) ((fun _ => value))).conclusion =
      .term context (inject carrier value) (codeType S D carrier n) := by
    simp only [RuleCode.conclusion, signature, inject, codeType_substitute]
  exact equal ▸ tree

/-- Every prior source derivation, including operational projection terms,
continues to use precisely its former native rule tree. -/
def sourceDerivation {judgment : Judgment S} (tree : Derivation source judgment) :
    Derivation (signature source vertex bound carriers positive)
      (SignatureSum.judgmentLeft (SignatureSum.judgmentLeft judgment)) :=
  carry source vertex bound carriers positive
    (SignatureSum.derivationLeft source (CubeNativeDeclarations.signature vertex) tree)

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeExtension
