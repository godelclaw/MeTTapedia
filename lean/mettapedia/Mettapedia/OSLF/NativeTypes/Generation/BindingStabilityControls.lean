import Mettapedia.OSLF.NativeTypes.Generation.BindingStability
import Mettapedia.OSLF.NativeTypes.Generation.BindingControls

open Mettapedia.OSLF.Framework

/-!
# Captured dependencies, binder contexts and actual source substitution

The source law is compiled by the same generator's law checker. Its body
uses a captured variable beyond the declared dependency prefix. An additional
lambda context and intrinsic substitution retain that captured value. A
nonidentity simultaneous substitution contracts two free variables while
preserving the binder and the complete function readout.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingStabilityControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.BindingCodec Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.BindingControls
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Generation.BindingCenter Mettapedia.OSLF.NativeTypes.Generation.BindingStability
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.NullaryGuards

abbrev sourceSignature := signatureOf language
abbrev sourceMetas := metaArities (language := language) (lawRule law) compiled.spec

def capturedBody : ContextualAssignment sourceSignature sourceMetas [term, term] := fun index => by
  change Fin 1 at index
  have ordinal : index.val = 0 := by omega
  have only : index = ⟨0, by decide⟩ := Fin.ext ordinal
  subst index
  exact .var (.succ (.succ .zero))

def ambient : Sub sourceSignature [term, term] [term, term] := fun _ position => .var position
def ordinary : Sub sourceSignature [] [term, term] := fun _ impossible => nomatch impossible

def first : Term sourceSignature [term, term] (.arrow term term) :=
  ContextualAssignment.instantiate capturedBody ambient ordinary compiled.left.term

def second : Term sourceSignature [term, term] (.arrow term term) :=
  ContextualAssignment.instantiate capturedBody ambient ordinary compiled.right.term

theorem actual_source_compilation : compileLaw? language law (.arrow term term) = some compiled := by
  exact (Option.some_get actual_scoped_law_compiles).symm

theorem actual_original_law_selected
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex Mettapedia.OSLF.NativeTypes.Generation.BindingControls.chosen.language) :
    law ∈ selectedEquationLaws (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language
      (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).languageFragment.operational := by
  change law ∈ [law]
  exact List.Mem.head _

theorem captured_source_instance
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex Mettapedia.OSLF.NativeTypes.Generation.BindingControls.chosen.language) :
    SourceInstance (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language
      (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.provider
      (selectedEquationLaws (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language
        (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).languageFragment.operational) first second := by
  exact .source law (actual_original_law_selected vertex) (.arrow term term) (by decide +kernel)
    compiled actual_source_compilation [] (.nil 0) rfl capturedBody ambient ordinary

theorem captured_consequence
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex Mettapedia.OSLF.NativeTypes.Generation.BindingControls.chosen.language) :
    Consequence (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language
      (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.provider
      (selectedEquationLaws (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language
        (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).languageFragment.operational) first second :=
  .source (captured_source_instance vertex)

def binderFirst : Term sourceSignature [term] (.arrow term (.arrow term term)) :=
  .op (.lambda term (.arrow term term)) (.cons first .nil)

def binderSecond : Term sourceSignature [term] (.arrow term (.arrow term term)) :=
  .op (.lambda term (.arrow term term)) (.cons second .nil)

def substitutionFirst : Term sourceSignature [term] (.arrow term term) :=
  .op (.subst term (.arrow term term)) (.cons first (.cons (.var .zero) .nil))

def substitutionSecond : Term sourceSignature [term] (.arrow term term) :=
  .op (.subst term (.arrow term term)) (.cons second (.cons (.var .zero) .nil))

theorem actual_binder_context_preserved
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex Mettapedia.OSLF.NativeTypes.Generation.BindingControls.chosen.language) :
    Consequence (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language
      (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.provider
      (selectedEquationLaws (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language
        (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).languageFragment.operational) binderFirst binderSecond :=
  .constructor (.lambda term (.arrow term term)) (.cons (captured_consequence vertex) .nil)

theorem intrinsic_substitution_context_preserved
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex Mettapedia.OSLF.NativeTypes.Generation.BindingControls.chosen.language) :
    Consequence (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language
      (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.provider
      (selectedEquationLaws (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language
        (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).languageFragment.operational)
      substitutionFirst substitutionSecond :=
  .constructor (.subst term (.arrow term term))
    (.cons (captured_consequence vertex) (.cons (.reflexive (.var .zero)) .nil))

def contraction : Sub sourceSignature [term, term] [term] := fun _ position =>
  match position with
  | .zero => .var .zero
  | .succ .zero => .var .zero
  | .succ (.succ impossible) => nomatch impossible

theorem simultaneous_substitution_preserved
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex Mettapedia.OSLF.NativeTypes.Generation.BindingControls.chosen.language) :
    Consequence (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language
      (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.provider
      (selectedEquationLaws (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language
        (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).languageFragment.operational)
      (bind contraction first) (bind contraction second) :=
  .substituted contraction (captured_consequence vertex)

theorem contracted_source_retains_native_binders :
    erase (bind contraction first) = .lambda none (.subst (.bvar 2) (.bvar 0)) := by
  decide +kernel

theorem contracted_target_retains_captured_variable :
    erase (bind contraction second) = .lambda none (.bvar 1) := by
  decide +kernel

def oneVariable : (type : TypeExpr) → Var [term] type → Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.Value type :=
  fun _ position =>
    match position with
    | .zero => .box
    | .succ impossible => nomatch impossible

theorem captured_variable_is_not_replaced_by_dependency :
    Valuation.read constructors (Valuation.interpret constructors substitutionSecond) oneVariable .star = .box := by
  rfl

theorem actual_generated_substitution_readout
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex Mettapedia.OSLF.NativeTypes.Generation.BindingControls.chosen.language) :
    Valuation.read
        (literalConstructors (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language vertex.2)
        (Valuation.interpret
          (literalConstructors (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language vertex.2)
          (bind contraction first)) oneVariable =
      Valuation.read
        (literalConstructors (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language vertex.2)
        (Valuation.interpret
          (literalConstructors (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language vertex.2)
          second)
        (fun type position => Valuation.read
          (literalConstructors (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language vertex.2)
          (Valuation.interpret
            (literalConstructors (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.generated vertex).snapshot.language vertex.2)
            (contraction type position)) oneVariable) :=
  generated_binding_substitution_readout _ _
    (Mettapedia.OSLF.NativeTypes.Generation.BindingControls.whole_original_equation_stream_checks vertex)
    (captured_consequence vertex) contraction oneVariable

end Mettapedia.OSLF.NativeTypes.Generation.BindingStabilityControls
