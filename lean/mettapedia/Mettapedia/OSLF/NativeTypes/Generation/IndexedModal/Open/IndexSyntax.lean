import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.ClassifierFormation
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeKindEncoding

/-! # The classified index value and membership are original native projections -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.IndexSyntax

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open CubeEnrichment CubeNativeDeclarations CubeNativeKindEncoding

variable {D : CubeEnrichment.Signature} (vertex : Vertex D)

@[simp] theorem classifierValue_substitute (carrier : D.Carrier) (kind : HSort) {n m : Nat}
    (expression : TermExpr (symbols D) n) (mapping : Substitution (symbols D) n m) :
    (classifierValue carrier kind expression).substitute mapping =
      classifierValue carrier kind (expression.substitute mapping) := by
  simp only [classifierValue, TermExpr.substitute, CubeNativeDeclarations.codeType_substitute,
    typingType_substitute, sortCode_substitute, liftSubstitution_zero]

abbrev outerBody (carrier : D.Carrier) (kind : HSort) (n : Nat) : TypeExpr (symbols D) (n + 1) :=
  .sigma (codeType carrier (n + 1)) (typingType carrier (.var 0) (classifierValue carrier kind (.var 1)))

def classifierBundle (carrier : D.Carrier) (kind : HSort) {n : Nat}
    (bundle : TermExpr (symbols D) n) : TermExpr (symbols D) n :=
  .fst (certifiedCode carrier kind n) (outerBody carrier kind n) bundle

def classifier (carrier : D.Carrier) (kind : HSort) {n : Nat}
    (bundle : TermExpr (symbols D) n) : TermExpr (symbols D) n :=
  classifierValue carrier kind (classifierBundle carrier kind bundle)

def valueBundle (carrier : D.Carrier) (kind : HSort) {n : Nat}
    (bundle : TermExpr (symbols D) n) : TermExpr (symbols D) n :=
  .snd (certifiedCode carrier kind n) (outerBody carrier kind n) bundle

abbrev valueBody (carrier : D.Carrier) (kind : HSort) {n : Nat}
    (bundle : TermExpr (symbols D) n) : TypeExpr (symbols D) (n + 1) :=
  typingType carrier (.var 0) ((classifier carrier kind bundle).rename Fin.succ)

def value (carrier : D.Carrier) (kind : HSort) {n : Nat}
    (bundle : TermExpr (symbols D) n) : TermExpr (symbols D) n :=
  .fst (codeType carrier n) (valueBody carrier kind bundle) (valueBundle carrier kind bundle)

def membership (carrier : D.Carrier) (kind : HSort) {n : Nat}
    (bundle : TermExpr (symbols D) n) : TermExpr (symbols D) n :=
  .snd (codeType carrier n) (valueBody carrier kind bundle) (valueBundle carrier kind bundle)

def outerBodyFormed (carrier : D.Carrier) (kind : HSort) {n : Nat}
    {context : ContextExpr (symbols D) n} (formed : Derivation (Theory vertex) (.context context)) :
    Derivation (Theory vertex) (.type (.snoc context (certifiedCode carrier kind n)) (outerBody carrier kind n)) := by
  let withClassifier := extendFormed vertex formed (certifiedFormed vertex carrier kind formed)
  let domain := codeFormed vertex carrier withClassifier
  let withValue := extendFormed vertex withClassifier domain
  have previous := weakenTerm vertex (certifiedVariable vertex carrier kind formed) domain
  rw [certifiedCode_rename] at previous
  let evidence := typingFormed vertex carrier withValue (.var 0) (classifierValue carrier kind (.var 1))
    (codeVariable vertex carrier withClassifier) (classifierValueFormed vertex carrier kind withValue previous)
  exact deriveList (.sigmaFormation _ _ _) (.cons domain (.cons evidence .nil))

def classifierBundleTyped (carrier : D.Carrier) (kind : HSort) {n : Nat}
    {context : ContextExpr (symbols D) n} (formed : Derivation (Theory vertex) (.context context))
    {bundle : TermExpr (symbols D) n}
    (typed : Derivation (Theory vertex) (.term context bundle (indexType carrier kind n))) :
    Derivation (Theory vertex) (.term context (classifierBundle carrier kind bundle) (certifiedCode carrier kind n)) :=
  deriveList (.firstProjection context (certifiedCode carrier kind n) (outerBody carrier kind n) bundle)
    (.cons (certifiedFormed vertex carrier kind formed)
      (.cons (outerBodyFormed vertex carrier kind formed) (.cons typed .nil)))

def classifierTyped (carrier : D.Carrier) (kind : HSort) {n : Nat}
    {context : ContextExpr (symbols D) n} (formed : Derivation (Theory vertex) (.context context))
    {bundle : TermExpr (symbols D) n}
    (typed : Derivation (Theory vertex) (.term context bundle (indexType carrier kind n))) :
    Derivation (Theory vertex) (.term context (classifier carrier kind bundle) (codeType carrier n)) :=
  classifierValueFormed vertex carrier kind formed (classifierBundleTyped vertex carrier kind formed typed)

theorem outerBody_instantiated (carrier : D.Carrier) (kind : HSort) {n : Nat}
    (bundle : TermExpr (symbols D) n) :
    (outerBody carrier kind n).substitute (instantiate (classifierBundle carrier kind bundle)) =
      .sigma (codeType carrier n) (valueBody carrier kind bundle) := by
  simp only [TypeExpr.substitute, CubeNativeDeclarations.codeType_substitute,
    typingType_substitute, classifierValue_substitute, TermExpr.substitute]
  change TypeExpr.sigma (codeType carrier n)
      (typingType carrier (.var 0) (classifierValue carrier kind ((classifierBundle carrier kind bundle).rename Fin.succ))) =
    TypeExpr.sigma (codeType carrier n)
      (typingType carrier (.var 0) ((classifierValue carrier kind (classifierBundle carrier kind bundle)).rename Fin.succ))
  rw [classifierValue_rename]

def valueBundleTyped (carrier : D.Carrier) (kind : HSort) {n : Nat}
    {context : ContextExpr (symbols D) n} (formed : Derivation (Theory vertex) (.context context))
    {bundle : TermExpr (symbols D) n}
    (typed : Derivation (Theory vertex) (.term context bundle (indexType carrier kind n))) :
    Derivation (Theory vertex) (.term context (valueBundle carrier kind bundle)
      (.sigma (codeType carrier n) (valueBody carrier kind bundle))) := by
  have result := deriveList (.secondProjection context (certifiedCode carrier kind n) (outerBody carrier kind n) bundle)
    (.cons (certifiedFormed vertex carrier kind formed)
      (.cons (outerBodyFormed vertex carrier kind formed) (.cons typed .nil)))
  exact (congrArg (Judgment.term context (valueBundle carrier kind bundle))
    (outerBody_instantiated carrier kind bundle)) ▸ result

def valueBodyFormed (carrier : D.Carrier) (kind : HSort) {n : Nat}
    {context : ContextExpr (symbols D) n} (formed : Derivation (Theory vertex) (.context context))
    {bundle : TermExpr (symbols D) n}
    (typed : Derivation (Theory vertex) (.term context bundle (indexType carrier kind n))) :
    Derivation (Theory vertex) (.type (.snoc context (codeType carrier n)) (valueBody carrier kind bundle)) := by
  let domain := codeFormed vertex carrier formed
  have classifierThere := weakenTerm vertex (classifierTyped vertex carrier kind formed typed) domain
  rw [codeType_rename] at classifierThere
  exact typingFormed vertex carrier (extendFormed vertex formed domain) (.var 0)
    ((classifier carrier kind bundle).rename Fin.succ) (codeVariable vertex carrier formed) classifierThere

def valueTyped (carrier : D.Carrier) (kind : HSort) {n : Nat}
    {context : ContextExpr (symbols D) n} (formed : Derivation (Theory vertex) (.context context))
    {bundle : TermExpr (symbols D) n}
    (typed : Derivation (Theory vertex) (.term context bundle (indexType carrier kind n))) :
    Derivation (Theory vertex) (.term context (value carrier kind bundle) (codeType carrier n)) :=
  deriveList (.firstProjection context (codeType carrier n) (valueBody carrier kind bundle)
    (valueBundle carrier kind bundle))
    (.cons (codeFormed vertex carrier formed) (.cons (valueBodyFormed vertex carrier kind formed typed)
      (.cons (valueBundleTyped vertex carrier kind formed typed) .nil)))

def membershipTyped (carrier : D.Carrier) (kind : HSort) {n : Nat}
    {context : ContextExpr (symbols D) n} (formed : Derivation (Theory vertex) (.context context))
    {bundle : TermExpr (symbols D) n}
    (typed : Derivation (Theory vertex) (.term context bundle (indexType carrier kind n))) :
    Derivation (Theory vertex) (.term context (membership carrier kind bundle)
      (typingType carrier (value carrier kind bundle) (classifier carrier kind bundle))) := by
  have result := deriveList (.secondProjection context (codeType carrier n) (valueBody carrier kind bundle)
    (valueBundle carrier kind bundle))
    (.cons (codeFormed vertex carrier formed) (.cons (valueBodyFormed vertex carrier kind formed typed)
      (.cons (valueBundleTyped vertex carrier kind formed typed) .nil)))
  have typeRead : (valueBody carrier kind bundle).substitute (instantiate (value carrier kind bundle)) =
      typingType carrier (value carrier kind bundle) (classifier carrier kind bundle) := by
    simp only [valueBody, typingType_substitute, TermExpr.substitute, instantiate_zero, TermExpr.instantiate_weaken]
  exact (congrArg (Judgment.term context (membership carrier kind bundle)) typeRead) ▸ result

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.IndexSyntax
