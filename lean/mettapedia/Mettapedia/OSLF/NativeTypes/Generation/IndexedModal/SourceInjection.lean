import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Pipeline
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureExtensionFormation

/-!
# Operational injection into a left-preserving indexed modal enrichment

All existing constructor and operational declarations remain on the left.
A new injection consumes a value at its already formed authored carrier and
returns a value of the freely adjoined code carrier. The old carrier is not
silently replaced with a predicate power or an internal universe.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SourceInjection

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf

variable (installed : Pipeline.Installed)

abbrev D := Pipeline.classifierSignature installed.operational
abbrev S := installed.operational.symbols
abbrev source := installed.operational.signature
abbrev vertex := installed.classifierVertex
abbrev bound : Nat := 4
abbrev carriers := NativeCubeProfile.sourceCarriers installed.operational
abbrev positive : 0 < bound := by decide
abbrev core := installed.signature
abbrev injectionSymbols := CubeNativeExtension.injectionSymbols (D installed)
abbrev symbols := SignatureSum.symbols installed.symbols (injectionSymbols installed)

abbrev sourceType (carrier : (D installed).Carrier) : TypeExpr (symbols installed) 0 :=
  SignatureSum.typeLeft (SignatureSum.typeLeft ((carriers installed).type carrier))

abbrev codeType (carrier : (D installed).Carrier) (n : Nat) : TypeExpr (symbols installed) n :=
  .family (.inl (.inr (.inl (.code carrier)))) Fin.elim0

def injectionContext (carrier : (D installed).Carrier) : ContextExpr (symbols installed) 1 :=
  .snoc .nil (sourceType installed carrier)

def extraRanks : SignatureSum.Ranks (injectionSymbols installed) :=
  ⟨(fun symbol => nomatch symbol), (fun _ => bound), (fun symbol => nomatch symbol)⟩

def signature : Signature (symbols installed) where
  typeRank := (SignatureSum.sumRanks (SignatureSum.ranks (core installed)) (extraRanks installed)).typeRank
  termRank := (SignatureSum.sumRanks (SignatureSum.ranks (core installed)) (extraRanks installed)).termRank
  predicateRank := (SignatureSum.sumRanks (SignatureSum.ranks (core installed)) (extraRanks installed)).predicateRank
  typeParameters symbol := match symbol with
    | .inl symbol => SignatureSum.contextLeft ((core installed).typeParameters symbol)
    | .inr impossible => nomatch impossible
  termParameters symbol := match symbol with
    | .inl symbol => SignatureSum.contextLeft ((core installed).termParameters symbol)
    | .inr carrier => injectionContext installed carrier
  predicateParameters symbol := match symbol with
    | .inl symbol => SignatureSum.contextLeft ((core installed).predicateParameters symbol)
    | .inr impossible => nomatch impossible
  termResult symbol := match symbol with
    | .inl symbol => SignatureSum.typeLeft ((core installed).termResult symbol)
    | .inr carrier => codeType installed carrier 1
  typeParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (SignatureSum.contextLeft_before _ _ _ _).mpr
          ((core installed).typeParameters_before symbol)
    | inr impossible => exact nomatch impossible
  termParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (SignatureSum.contextLeft_before _ _ _ _).mpr
          ((core installed).termParameters_before symbol)
    | inr carrier =>
        refine ⟨True.intro, ?_⟩
        apply (SignatureSum.typeLeft_before _ _ _ _).mpr
        apply (SignatureSum.typeLeft_signature_before (source installed) installed.classifiers _ _).mpr
        exact (((carriers installed).formed carrier).before_judgment ((carriers installed).before carrier)).2
  predicateParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (SignatureSum.contextLeft_before _ _ _ _).mpr
          ((core installed).predicateParameters_before symbol)
    | inr impossible => exact nomatch impossible
  termResult_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (SignatureSum.typeLeft_before _ _ _ _).mpr
          ((core installed).termResult_before symbol)
    | inr carrier => exact ⟨positive, fun position => Fin.elim0 position⟩


theorem preserves : SignatureExtension.Preserves (core installed) (signature installed) where
  typeParameters _ := rfl
  termParameters _ := rfl
  predicateParameters _ := rfl
  termResult _ := rfl
  typeRank _ := rfl
  termRank _ := rfl
  predicateRank _ := rfl

def carry {judgment : Judgment installed.symbols}
    (tree : Derivation (core installed) judgment) :
    Derivation (signature installed) (SignatureSum.judgmentLeft judgment) :=
  SignatureExtension.derivation _ _ (preserves installed) tree

def sourceCarrierFormed (carrier : (D installed).Carrier) :
    Derivation (signature installed)
      (.type .nil (sourceType installed carrier)) :=
  carry installed
    (installed.sourceDerivation ((carriers installed).formed carrier))

def emptyFormed : Derivation (signature installed) (.context .nil) :=
  deriveList .contextNil .nil

def injectionContextFormed (carrier : (D installed).Carrier) :
    Derivation (signature installed)
      (.context (injectionContext installed carrier)) :=
  deriveList (.contextExtend .nil (sourceType installed carrier))
    (.cons (emptyFormed installed)
      (.cons (sourceCarrierFormed installed carrier) .nil))

def codeFormed (carrier : (D installed).Carrier) {n : Nat} {context : ContextExpr (symbols installed) n}
    (formed : Derivation (signature installed) (.context context)) :
    Derivation (signature installed) (.type context (codeType installed carrier n)) :=
  deriveList (.typeFamily context (.inl (.inr (.inl (.code carrier)))) Fin.elim0)
    (.cons formed (.cons (emptyFormed installed)
      (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil)))

theorem emptyFormed_before (limit : Nat) :
    (emptyFormed installed).before limit :=
  deriveList_before .contextNil .nil limit True.intro True.intro

theorem sourceCarrierFormed_before (carrier : (D installed).Carrier) :
    (sourceCarrierFormed installed carrier).before bound :=
  SignatureExtension.derivation_before _ _ (preserves installed) _ bound
    (SignatureSum.derivationLeft_before (source installed) installed.classifiers _ bound
      ((carriers installed).before carrier))

theorem injectionContextFormed_before (carrier : (D installed).Carrier) :
    (injectionContextFormed installed carrier).before bound := by
  apply deriveList_before
  · refine ⟨True.intro, ?_⟩
    exact ((sourceCarrierFormed installed carrier).before_judgment
      (sourceCarrierFormed_before installed carrier)).2
  · exact ⟨emptyFormed_before installed bound,
      sourceCarrierFormed_before installed carrier, True.intro⟩

theorem codeFormed_before (carrier : (D installed).Carrier) {n : Nat} {context : ContextExpr (symbols installed) n}
    (formed : Derivation (signature installed) (.context context))
    (ordered : formed.before bound) :
    (codeFormed installed carrier formed).before bound := by
  have contextBefore := formed.before_judgment ordered
  apply deriveList_before
  · exact ⟨contextBefore, positive, fun position => Fin.elim0 position⟩
  · exact ⟨ordered, emptyFormed_before installed bound,
      deriveList_before (.substitutionNil context) _ bound
        ⟨contextBefore, True.intro, fun position => Fin.elim0 position⟩ ⟨ordered, True.intro⟩,
      True.intro⟩

/-- The source alphabet's declarations and all its derivations survive before
new source-to-code injections are installed. -/
def headers :
    HeaderFormation (signature installed) where
  typeHeader symbol := match symbol with
    | .inl symbol => carry installed
          (installed.formation.typeHeader symbol)
    | .inr impossible => nomatch impossible
  typeHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact SignatureExtension.derivation_before _ _
          (preserves installed) _ _
          (installed.formation.typeHeader_before symbol)
    | inr impossible => exact nomatch impossible
  termHeader symbol := match symbol with
    | .inl symbol => carry installed
          (installed.formation.termHeader symbol)
    | .inr carrier => injectionContextFormed installed carrier
  termHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact SignatureExtension.derivation_before _ _
          (preserves installed) _ _
          (installed.formation.termHeader_before symbol)
    | inr carrier => exact injectionContextFormed_before installed carrier
  termResult symbol := match symbol with
    | .inl symbol => carry installed
          (installed.formation.termResult symbol)
    | .inr carrier => codeFormed installed carrier
        (injectionContextFormed installed carrier)
  termResult_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact SignatureExtension.derivation_before _ _
          (preserves installed) _ _
          (installed.formation.termResult_before symbol)
    | inr carrier =>
        exact codeFormed_before installed carrier _
          (injectionContextFormed_before installed carrier)
  predicateHeader symbol := match symbol with
    | .inl symbol => carry installed
          (installed.formation.predicateHeader symbol)
    | .inr impossible => nomatch impossible
  predicateHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact SignatureExtension.derivation_before _ _
          (preserves installed) _ _
          (installed.formation.predicateHeader_before symbol)
    | inr impossible => exact nomatch impossible



/-- The computed enrichment needs no caller-supplied cube formation record. -/
def computedHeaders :
    HeaderFormation (signature installed) :=
  headers installed

def inject {n : Nat} (carrier : (D installed).Carrier) (value : TermExpr (symbols installed) n) :
    TermExpr (symbols installed) n := .primitive (.inr carrier) ((fun _ => value))

@[simp] theorem codeType_substitute (carrier : (D installed).Carrier) {n m : Nat}
    (mapping : Substitution (symbols installed) n m) :
    (codeType installed carrier n).substitute mapping = codeType installed carrier m := by
  apply congrArg (TypeExpr.family (S := symbols installed) (.inl (.inr (.inl (.code carrier)))))
  funext position
  exact Fin.elim0 position

theorem closed_empty_substitute (type : TypeExpr (symbols installed) 0) {n : Nat} :
    type.substitute (Fin.elim0 : Substitution (symbols installed) 0 n) =
      type.rename (Fin.elim0 : Renaming 0 n) := by
  rw [← TypeExpr.substitute_variables]
  congr 1
  funext position
  exact Fin.elim0 position

/-- Actual native rule application embeds an authored value into the new
carrier while retaining its original contextual formation and typing tree. -/
def injectFormation {n : Nat} {context : ContextExpr (symbols installed) n}
    (carrier : (D installed).Carrier) (value : TermExpr (symbols installed) n)
    (formed : Derivation (signature installed) (.context context))
    (typed : Derivation (signature installed)
      (.term context value ((sourceType installed carrier).rename Fin.elim0))) :
    Derivation (signature installed)
      (.term context (inject installed carrier value) (codeType installed carrier n)) := by
  have adjusted : Derivation (signature installed)
      (.term context value ((sourceType installed carrier).substitute Fin.elim0)) :=
    (congrArg (Judgment.term context value)
      (closed_empty_substitute installed (sourceType installed carrier))).symm ▸ typed
  let arguments := deriveList (.substitutionExtend context .nil
    (sourceType installed carrier) Fin.elim0 value)
    (.cons (deriveList (.substitutionNil context) (.cons formed .nil))
      (.cons (sourceCarrierFormed installed carrier) (.cons adjusted .nil)))
  have same : extendSubstitution (Fin.elim0 : Substitution (symbols installed) 0 n) value =
      (fun _ => value) := by
    funext position
    cases position using Fin.cases with
    | zero => rfl
    | succ impossible => exact Fin.elim0 impossible
  have arguments' : Derivation (signature installed)
      (.substitution context (injectionContext installed carrier) ((fun _ => value))) :=
    (congrArg (Judgment.substitution context (injectionContext installed carrier)) same) ▸ arguments
  have tree := deriveList (D := signature installed) (.primitive context (.inr carrier)
    ((fun _ => value) : Substitution (symbols installed) 1 n))
    (.cons formed (.cons (injectionContextFormed installed carrier)
      (.cons (codeFormed installed carrier
        (injectionContextFormed installed carrier)) (.cons arguments' .nil))))
  have equal : (RuleCode.primitive (D := signature installed)
      context (.inr carrier) ((fun _ => value))).conclusion =
      .term context (inject installed carrier value) (codeType installed carrier n) := by
    simp only [RuleCode.conclusion, signature, inject, codeType_substitute]
  exact equal ▸ tree

/-- Every indexed classifier derivation survives the operational injections. -/
def classifierDerivation {judgment : Judgment installed.symbols} (tree : Derivation installed.signature judgment) :
    Derivation (signature installed) (SignatureSum.judgmentLeft judgment) := carry installed tree

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SourceInjection
