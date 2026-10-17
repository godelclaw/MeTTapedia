import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.ClassifierFormation

/-! # Ordered rely binders for a mandatory dependent target classifier -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open CubeEnrichment CubeNativeDeclarations

variable {D : CubeEnrichment.Signature} (vertex : Vertex D)

def twice {n m : Nat} (mapping : Renaming n m) : Renaming n (m + 2) :=
  fun position => (mapping position).succ.succ

def continuationType {n m : Nat} (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n))
    (mapping : Renaming n m) : TypeExpr (symbols D) m :=
  match relies with
  | [] => certifiedCode target sort m
  | (carrier, classifier) :: remaining =>
      relyFunction carrier (classifier.rename mapping)
        (continuationType target sort remaining (twice mapping))

def continuationFormed (vertex : Vertex D) {n m : Nat} (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n))
    (mapping : Renaming n m) {context : ContextExpr (symbols D) m}
    (formed : Derivation (Theory vertex) (.context context))
    (classifiers : ∀ position : Fin relies.length, Derivation (Theory vertex)
      (.term context (relies[position].2.rename mapping) (codeType relies[position].1 m))) :
    Derivation (Theory vertex) (.type context (continuationType target sort relies mapping)) := by
  cases relies with
  | nil => exact certifiedFormed vertex target sort formed
  | cons entry remaining =>
      let domain := codeFormed vertex entry.1 formed
      let withValue := extendFormed vertex formed domain
      have classifierThere := weakenTerm vertex (classifiers 0) domain
      rw [codeType_rename] at classifierThere
      let evidence := typingFormed vertex entry.1 withValue (.var 0)
        ((entry.2.rename mapping).rename Fin.succ)
        (codeVariable vertex entry.1 formed) classifierThere
      let withEvidence := extendFormed vertex withValue evidence
      apply relyFunctionFormed vertex entry.1 formed (classifiers 0)
      apply continuationFormed vertex target sort remaining (twice mapping) withEvidence
      intro position
      let other := remaining[position]
      have first := weakenTerm vertex (classifiers position.succ) domain
      rw [codeType_rename] at first
      have second := weakenTerm vertex first evidence
      have equation : ((other.2.rename mapping).rename Fin.succ).rename Fin.succ =
          other.2.rename (twice mapping) := by
        rw [TermExpr.rename_comp, TermExpr.rename_comp]
        rfl
      change Derivation (Theory vertex) (.term _
        (((other.2.rename mapping).rename Fin.succ).rename Fin.succ)
        ((codeType other.1 (m + 1)).rename Fin.succ)) at second
      rw [equation, codeType_rename] at second
      exact second
termination_by relies.length

/-- The empty-rely case still requires a classifier at the target carrier. -/
theorem continuation_nil {n m : Nat} (target : D.Carrier) (sort : HSort)
    (mapping : Renaming n m) : continuationType target sort [] mapping =
      certifiedCode target sort m := rfl

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal
