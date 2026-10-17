import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeHeaderRanks

/-!
# Dependent classifier parameters in the common native grammar

An index parameter packages its classifier, value and membership evidence.
Continuation parameters bind rely values and their membership evidence.
Classifier codes carry their selected sort evidence; none of these parameters
asserts that the resulting modal classifier has a program inhabitant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open CubeEnrichment CubeNativeDeclarations

variable {D : CubeEnrichment.Signature} (vertex : Vertex D)

def classifierValue (carrier : D.Carrier) (sort : HSort) {n : Nat}
    (value : TermExpr (symbols D) n) : TermExpr (symbols D) n :=
  .fst (codeType carrier n)
    (typingType carrier (.var 0) (sortCode carrier sort (n + 1))) value

@[simp] theorem classifierValue_rename (carrier : D.Carrier) (sort : HSort)
    {n m : Nat} (value : TermExpr (symbols D) n) (mapping : Renaming n m) :
    (classifierValue carrier sort value).rename mapping =
      classifierValue carrier sort (value.rename mapping) := by
  simp only [classifierValue, TermExpr.rename, codeType_rename, typingType,
    TypeExpr.rename]
  congr 2
  funext position
  cases position using Fin.cases with
  | zero => rfl
  | succ _ => exact sortCode_rename carrier sort _

def classifierValueFormed (carrier : D.Carrier) (sort : HSort) {n : Nat}
    {context : ContextExpr (symbols D) n} {value : TermExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context))
    (typed : Derivation (Theory vertex) (.term context value (certifiedCode carrier sort n))) :
    Derivation (Theory vertex) (.term context (classifierValue carrier sort value)
      (codeType carrier n)) :=
  let domain := codeFormed vertex carrier formed
  let extended := extendFormed vertex formed domain
  let body := typingFormed vertex carrier extended (.var 0) (sortCode carrier sort (n + 1))
    (codeVariable vertex carrier formed) (sortFormed vertex carrier sort extended)
  deriveList (.firstProjection context (codeType carrier n)
    (typingType carrier (.var 0) (sortCode carrier sort (n + 1))) value)
    (.cons domain (.cons body (.cons typed .nil)))

def weakenTerm {n : Nat} {context : ContextExpr (symbols D) n}
    {value : TermExpr (symbols D) n} {type extra : TypeExpr (symbols D) n}
    (typed : Derivation (Theory vertex) (.term context value type))
    (extraFormed : Derivation (Theory vertex) (.type context extra)) :
    Derivation (Theory vertex) (.term (.snoc context extra)
      (value.rename Fin.succ) (type.rename Fin.succ)) := by
  have tree := deriveList (.substituteTerm (.snoc context extra) context
      (fun index => .var index.succ) value type)
    (.cons (deriveList (.substitutionWeaken context extra) (.cons extraFormed .nil))
      (.cons typed .nil))
  simpa only [RuleCode.conclusion, TypeExpr.substitute_variables,
    TermExpr.substitute_variables] using tree

def certifiedVariable (carrier : D.Carrier) (sort : HSort) {n : Nat}
    {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) :
    Derivation (Theory vertex)
      (.term (.snoc context (certifiedCode carrier sort n)) (.var 0)
        (certifiedCode carrier sort (n + 1))) := by
  have tree := deriveList (.variable (.snoc context (certifiedCode carrier sort n)) 0)
    (.cons (extendFormed vertex formed (certifiedFormed vertex carrier sort formed)) .nil)
  simpa only [RuleCode.conclusion, ContextExpr.lookup_zero, certifiedCode_rename] using tree

def indexType (carrier : D.Carrier) (sort : HSort) (n : Nat) : TypeExpr (symbols D) n :=
  .sigma (certifiedCode carrier sort n)
    (.sigma (codeType carrier (n + 1))
      (typingType carrier (.var 0) (classifierValue carrier sort (.var 1))))

def indexFormed (carrier : D.Carrier) (sort : HSort) {n : Nat}
    {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) :
    Derivation (Theory vertex) (.type context (indexType carrier sort n)) := by
  let classifierTree := certifiedFormed vertex carrier sort formed
  let withClassifier := extendFormed vertex formed classifierTree
  let valueTree := codeFormed vertex carrier withClassifier
  let withValue := extendFormed vertex withClassifier valueTree
  have classifierThere := weakenTerm vertex (certifiedVariable vertex carrier sort formed) valueTree
  rw [certifiedCode_rename] at classifierThere
  let membership := typingFormed vertex carrier withValue (.var 0)
    (classifierValue carrier sort (.var 1))
    (codeVariable vertex carrier withClassifier)
    (classifierValueFormed vertex carrier sort withValue classifierThere)
  let pair := deriveList (.sigmaFormation _ (codeType carrier (n + 1))
    (typingType carrier (.var 0) (classifierValue carrier sort (.var 1))))
    (.cons valueTree (.cons membership .nil))
  exact deriveList (.sigmaFormation context (certifiedCode carrier sort n)
    (.sigma (codeType carrier (n + 1))
      (typingType carrier (.var 0) (classifierValue carrier sort (.var 1)))))
    (.cons classifierTree (.cons pair .nil))

/-- The target classifier is a dependent function over supplied rely values
and evidence. Its body may refer to all those values and the ambient indices. -/
def relyFunction (carrier : D.Carrier) {n : Nat}
    (classifier : TermExpr (symbols D) n)
    (body : TypeExpr (symbols D) (n + 2)) : TypeExpr (symbols D) n :=
  .pi (codeType carrier n)
    (.pi (typingType carrier (.var 0) (classifier.rename Fin.succ)) body)

def relyFunctionFormed (carrier : D.Carrier) {n : Nat}
    {context : ContextExpr (symbols D) n} {classifier : TermExpr (symbols D) n}
    {body : TypeExpr (symbols D) (n + 2)}
    (formed : Derivation (Theory vertex) (.context context))
    (classifierTyped : Derivation (Theory vertex)
      (.term context classifier (codeType carrier n)))
    (bodyFormed : Derivation (Theory vertex)
      (.type (.snoc (.snoc context (codeType carrier n))
        (typingType carrier (.var 0) (classifier.rename Fin.succ))) body)) :
    Derivation (Theory vertex) (.type context (relyFunction carrier classifier body)) := by
  let domain := codeFormed vertex carrier formed
  let extended := extendFormed vertex formed domain
  have classifierThere := weakenTerm vertex classifierTyped domain
  rw [codeType_rename] at classifierThere
  let evidence := typingFormed vertex carrier extended (.var 0)
    (classifier.rename Fin.succ) (codeVariable vertex carrier formed) classifierThere
  exact deriveList (.piFormation context (codeType carrier n) _)
    (.cons domain (.cons (deriveList (.piFormation _ _ body)
      (.cons evidence (.cons bodyFormed .nil))) .nil))

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal
