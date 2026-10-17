import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Continuation
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeClosedFormation

/-! # Native parameter contexts computed from the full modal interface -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open CubeEnrichment CubeNativeDeclarations

variable {D : CubeEnrichment.Signature} (vertex : Vertex D)

structure Interface (Carrier : Type) where
  indices : List (Carrier × HSort)
  relies : List (Carrier × HSort)
  target : Carrier
  focus : Carrier
  resultSort : HSort

variable (interface : Interface D.Carrier)

def prefixSize : Nat := interface.relies.length + interface.indices.length

/-- Native variables use newest-first order. The index bundles therefore
precede the rely classifier parameters in the actual context telescope. -/
def prefixType : Fin (prefixSize interface) → TypeExpr (symbols D) 0 :=
  Fin.addCases
    (fun position => certifiedCode interface.relies[position].1 interface.relies[position].2 0)
    (fun position => indexType interface.indices[position].1 interface.indices[position].2 0)

def parameterPrefix : ContextExpr (symbols D) (prefixSize interface) :=
  vectorTelescope (prefixType interface)

def prefixFormed : Derivation (Theory vertex) (.context (parameterPrefix interface)) :=
  CubeNativeClosedFormation.vectorFormation vertex (prefixType interface) (by
    intro position
    refine Fin.addCases ?_ ?_ position
    · intro rely
      simpa only [prefixType, Fin.addCases_left] using
        certifiedFormed vertex interface.relies[rely].1 interface.relies[rely].2 (emptyFormed vertex)
    · intro index
      simpa only [prefixType, Fin.addCases_right] using
        indexFormed vertex interface.indices[index].1 interface.indices[index].2 (emptyFormed vertex))

def relyArguments : List (D.Carrier × TermExpr (symbols D) (prefixSize interface)) :=
  List.ofFn fun position : Fin interface.relies.length =>
    (interface.relies[position].1,
      classifierValue interface.relies[position].1 interface.relies[position].2
        (.var (position.castAdd interface.indices.length)))

def relyArgumentFormed (position : Fin interface.relies.length) :
    Derivation (Theory vertex) (.term (parameterPrefix interface)
      (classifierValue interface.relies[position].1 interface.relies[position].2
        (.var (position.castAdd interface.indices.length)))
      (codeType interface.relies[position].1 (prefixSize interface))) := by
  apply classifierValueFormed vertex _ _ (prefixFormed vertex interface)
  have tree := vectorVariable vertex (prefixType interface) (prefixFormed vertex interface)
    (position.castAdd interface.indices.length)
  simpa only [prefixType, Fin.addCases_left, certifiedCode_rename, parameterPrefix] using tree

def targetParameter : TypeExpr (symbols D) (prefixSize interface) :=
  continuationType interface.target interface.resultSort (relyArguments interface) id

def targetParameterFormed :
    Derivation (Theory vertex) (.type (parameterPrefix interface) (targetParameter interface)) := by
  apply continuationFormed vertex interface.target interface.resultSort (relyArguments interface) id
    (prefixFormed vertex interface)
  intro position
  let named : Fin interface.relies.length := ⟨position.val, by
    simpa only [relyArguments, List.length_ofFn] using position.isLt⟩
  have entryEq : (relyArguments interface)[position] =
      (interface.relies[named].1, classifierValue interface.relies[named].1 interface.relies[named].2
        (.var (named.castAdd interface.indices.length))) := by
    change (List.ofFn (fun position : Fin interface.relies.length =>
      (interface.relies[position].1, classifierValue interface.relies[position].1 interface.relies[position].2
        (.var (position.castAdd interface.indices.length))))).get position = _
    rw [List.get_ofFn]
    rfl
  rw [entryEq, TermExpr.rename_identity]
  exact relyArgumentFormed vertex interface named

def arity : Nat := prefixSize interface + 1

def parameters : ContextExpr (symbols D) (arity interface) :=
  .snoc (parameterPrefix interface) (targetParameter interface)

def parametersFormed : Derivation (Theory vertex) (.context (parameters interface)) :=
  extendFormed vertex (prefixFormed vertex interface) (targetParameterFormed vertex interface)

def result : TypeExpr (symbols D) (arity interface) :=
  certifiedCode interface.focus interface.resultSort (arity interface)

def resultFormed : Derivation (Theory vertex) (.type (parameters interface) (result interface)) :=
  certifiedFormed vertex interface.focus interface.resultSort (parametersFormed vertex interface)

theorem arity_full : arity interface =
    interface.indices.length + interface.relies.length + 1 := by
  simp only [arity, prefixSize, Nat.add_comm interface.relies.length interface.indices.length]

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal
