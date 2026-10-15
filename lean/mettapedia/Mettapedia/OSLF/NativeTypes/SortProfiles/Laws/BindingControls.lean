import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.BindingCodec
import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.CompilerOrigins

open Mettapedia.OSLF.Framework

/-!
# A scoped source equation checked over every dependency function

The actual source occurrence below the lambda refers to its declared bound
parameter. Explicit substitution applies the whole dependency function.
The positive law is extensional identity substitution under that binder;
the negative law wrongly replaces an arbitrary body function by identity.
Both are compiled from original authored source and binding metadata.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.BindingControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration.SchemaElaboration
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.BindingCodec
open ModalHypercube (HSort)

def term : TypeExpr := .base "Term"

def specification : RuleBindingSpec :=
  {dependencies := [("B", [term])], occurrences :=
    [{name := "B", site := .left, path := [0, 0], arguments := [.bvar 0]},
     {name := "B", site := .right, path := [0], arguments := [.bvar 0]}]}

def equation : Equation :=
  {name := "SubstitutionUnderLambda", typeContext := [("B", term)], premises := [],
    left := .lambda none (.subst (.fvar "B") (.bvar 0)),
    right := .lambda none (.fvar "B"), bindings := some specification}

def language : LanguageDef :=
  {name := "IntrinsicBinder", types := ["Term"], terms := [],
    equations := [equation], rewrites := []}

def law : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Law := Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.equationLaw equation 0

theorem actual_binding_metadata_admitted : admittedFor (lawRule law) specification = true := by
  decide +kernel

theorem actual_scoped_law_compiles : (compileLaw? language law (.arrow term term)).isSome = true := by
  decide +kernel

def compiled : CompiledLaw language law (.arrow term term) :=
  (compileLaw? language law (.arrow term term)).get actual_scoped_law_compiles

def constructors : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.Constructors language where
  ordinary _ member _ _ := False.elim (List.not_mem_nil member)
  collection _ member _ _ _ _ := False.elim (List.not_mem_nil member)

theorem all_dependency_functions_satisfy_the_actual_law : compiled.check? constructors = some true := by
  decide +kernel

theorem scoped_semantic_comparison :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.Satisfies language constructors
      (metaArities (language := language) (lawRule law) compiled.spec)
      compiled.left.term compiled.right.term :=
  ((compiled_semantic_check_exact compiled constructors).mp all_dependency_functions_satisfy_the_actual_law).2.2

theorem dependency_is_retained : compiled.spec.dependencies = [("B", [term])] := by
  decide +kernel

theorem original_occurrences_are_retained : compiled.spec.occurrences = specification.occurrences := by
  decide +kernel

def falseEquation : Equation :=
  {equation with
    name := "EveryBodyIsIdentity"
    right := .lambda none (.bvar 0)
    bindings := some {specification with occurrences := specification.occurrences.take 1}}

def falseLanguage : LanguageDef := {language with equations := [falseEquation]}
def falseLaw : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.Law := Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.equationLaw falseEquation 0

theorem wrong_scoped_law_is_still_classified :
    (compileLaw? falseLanguage falseLaw (.arrow term term)).isSome = true := by
  decide +kernel

def falseCompiled : CompiledLaw falseLanguage falseLaw (.arrow term term) :=
  (compileLaw? falseLanguage falseLaw (.arrow term term)).get wrong_scoped_law_is_still_classified

def falseConstructors : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.Constructors falseLanguage where
  ordinary _ member _ _ := False.elim (List.not_mem_nil member)
  collection _ member _ _ _ _ := False.elim (List.not_mem_nil member)

theorem arbitrary_body_is_not_identity : falseCompiled.check? falseConstructors = some false := by
  decide +kernel

theorem wrong_scoped_semantics_refuted :
    ¬ Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.Satisfies falseLanguage falseConstructors
      (metaArities (language := falseLanguage) (lawRule falseLaw) falseCompiled.spec)
      falseCompiled.left.term falseCompiled.right.term := by
  intro satisfied
  have finiteMetas : Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.finiteMetaContext
      (metaArities (language := falseLanguage) (lawRule falseLaw) falseCompiled.spec) = true := by
    decide +kernel
  have accepted := (compiled_semantic_check_exact falseCompiled falseConstructors).mpr
    ⟨finiteMetas, by rfl, satisfied⟩
  rw [arbitrary_body_is_not_identity] at accepted
  cases accepted

end Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.BindingControls
