import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
import Mettapedia.GSLT.LanguageDef.RegexTheory
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable

/-!
# Regex theory in the shared human authoring notation

This independent declaration uses the existing `languageDef!` elaborator.
The exact equality below checks every field against the structured theory
used by the derivative correspondence proofs. A native `.module` frontend
can reuse these declaration meanings without adding new core primitives.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexAuthoring

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

def authored : LanguageDef := languageDef! {
  name : "RegexDerivatives"
  types { ![str] as Scalar Regex Word Bool }
  terms {
    «rx:zero». |- "rx:zero" : Regex;
    «rx:epsilon». |- "rx:epsilon" : Regex;
    «rx:literal». a:Scalar |- "rx:literal" a : Regex;
    «rx:any». |- "rx:any" : Regex;
    «rx:union». p:Regex, q:Regex |- "rx:union" p q : Regex;
    «rx:concat». p:Regex, q:Regex |- "rx:concat" p q : Regex;
    «rx:star». p:Regex |- "rx:star" p : Regex;
    «rx:false». |- "rx:false" : Bool;
    «rx:true». |- "rx:true" : Bool;
    «rx:nil». |- "rx:nil" : Word;
    «rx:cons». a:Scalar, rest:Word |- "rx:cons" a rest : Word;
    «rx:nullable». p:Regex |- "rx:nullable" p : Bool;
    «rx:derivative». a:Scalar, p:Regex |- "rx:derivative" a p : Regex;
    «rx:match». p:Regex, input:Word |- "rx:match" p input : Bool;
    «rx:or». left:Bool, right:Bool |- "rx:or" left right : Bool;
    «rx:and». left:Bool, right:Bool |- "rx:and" left right : Bool;
  }
  equations {}
  rewrites {
    «OR-FF». |- "rx:or"("rx:false"(), "rx:false"()) ~> "rx:false"();
    «OR-FT». |- "rx:or"("rx:false"(), "rx:true"()) ~> "rx:true"();
    «OR-TF». |- "rx:or"("rx:true"(), "rx:false"()) ~> "rx:true"();
    «OR-TT». |- "rx:or"("rx:true"(), "rx:true"()) ~> "rx:true"();
    «AND-FF». |- "rx:and"("rx:false"(), "rx:false"()) ~> "rx:false"();
    «AND-FT». |- "rx:and"("rx:false"(), "rx:true"()) ~> "rx:false"();
    «AND-TF». |- "rx:and"("rx:true"(), "rx:false"()) ~> "rx:false"();
    «AND-TT». |- "rx:and"("rx:true"(), "rx:true"()) ~> "rx:true"();
    «NULL-ZERO». |- "rx:nullable"("rx:zero"()) ~> "rx:false"();
    «NULL-EPSILON». |- "rx:nullable"("rx:epsilon"()) ~> "rx:true"();
    «NULL-LITERAL». a:Scalar |- "rx:nullable"("rx:literal"(a)) ~> "rx:false"();
    «NULL-ANY». |- "rx:nullable"("rx:any"()) ~> "rx:false"();
    «NULL-UNION». p:Regex, q:Regex, left:Bool, right:Bool, result:Bool |
      "rx:nullable"(p) ~> left, "rx:nullable"(q) ~> right,
      "rx:or"(left, right) ~> result |-
      "rx:nullable"("rx:union"(p, q)) ~> result;
    «NULL-CONCAT». p:Regex, q:Regex, left:Bool, right:Bool, result:Bool |
      "rx:nullable"(p) ~> left, "rx:nullable"(q) ~> right,
      "rx:and"(left, right) ~> result |-
      "rx:nullable"("rx:concat"(p, q)) ~> result;
    «NULL-STAR». p:Regex |- "rx:nullable"("rx:star"(p)) ~> "rx:true"();
    «DERIV-ZERO». a:Scalar |- "rx:derivative"(a, "rx:zero"()) ~> "rx:zero"();
    «DERIV-EPSILON». a:Scalar |- "rx:derivative"(a, "rx:epsilon"()) ~> "rx:zero"();
    «DERIV-LITERAL-EQ». a:Scalar, expected:Scalar | «rx:scalar_eq»(expected, a) |-
      "rx:derivative"(a, "rx:literal"(expected)) ~> "rx:epsilon"();
    «DERIV-LITERAL-NE». a:Scalar, expected:Scalar | «rx:scalar_ne»(expected, a) |-
      "rx:derivative"(a, "rx:literal"(expected)) ~> "rx:zero"();
    «DERIV-ANY». a:Scalar |- "rx:derivative"(a, "rx:any"()) ~> "rx:epsilon"();
    «DERIV-UNION». a:Scalar, p:Regex, q:Regex, dp:Regex, dq:Regex |
      "rx:derivative"(a, p) ~> dp, "rx:derivative"(a, q) ~> dq |-
      "rx:derivative"(a, "rx:union"(p, q)) ~> "rx:union"(dp, dq);
    «DERIV-CONCAT-NULLABLE». a:Scalar, p:Regex, q:Regex, dp:Regex, dq:Regex |
      "rx:nullable"(p) ~> "rx:true"(),
      "rx:derivative"(a, p) ~> dp, "rx:derivative"(a, q) ~> dq |-
      "rx:derivative"(a, "rx:concat"(p, q)) ~>
      "rx:union"("rx:concat"(dp, q), dq);
    «DERIV-CONCAT-NONNULLABLE». a:Scalar, p:Regex, q:Regex, dp:Regex |
      "rx:nullable"(p) ~> "rx:false"(), "rx:derivative"(a, p) ~> dp |-
      "rx:derivative"(a, "rx:concat"(p, q)) ~> "rx:concat"(dp, q);
    «DERIV-STAR». a:Scalar, p:Regex, dp:Regex | "rx:derivative"(a, p) ~> dp |-
      "rx:derivative"(a, "rx:star"(p)) ~> "rx:concat"(dp, "rx:star"(p));
    «MATCH-NIL». p:Regex, result:Bool | "rx:nullable"(p) ~> result |-
      "rx:match"(p, "rx:nil"()) ~> result;
    «MATCH-CONS». p:Regex, a:Scalar, rest:Word, next:Regex, result:Bool |
      "rx:derivative"(a, p) ~> next, "rx:match"(next, rest) ~> result |-
      "rx:match"(p, "rx:cons"(a, rest)) ~> result;
  }
}

/-- Independent authored declarations elaborate to the complete semantic core. -/
theorem authored_exact : authored = RegexTheory.theory := by rfl

theorem authored_portable_recovery :
    Portable.coreCodec.decode (Portable.coreCodec.encode authored) = some RegexTheory.theory := by
  rw [Portable.coreCodec.decode_encode, authored_exact]

def namingControl : LanguageDef := languageDef! {
  name : "ExactNames"
  types { Proc }
  terms {
    «rx:k». |- "k" : Proc;
    Scope.K. x:Proc |- "K" x : Proc;
  }
  equations {
    «eq-name». |- «rx:k»() = "rx:k"();
    «bare-name». |- «rx:k» = "rx:k"();
  }
  rewrites {
    «rule-name». x:Proc | «rx:rel»(x), Scope.Rel(x) |- Scope.K(x) ~> «rx:k»();
  }
}

theorem escaped_constructor_label_exact :
    namingControl.terms.head?.map GrammarRule.label = some "rx:k" := rfl

theorem escaped_equation_name_exact :
    namingControl.equations.head?.map Equation.name = some "eq-name" := rfl

theorem escaped_bare_nullary_resolves_to_declared_constructor :
    namingControl.equations[1]?.map Equation.left = some (.apply "rx:k" []) := rfl

theorem escaped_rule_name_exact :
    namingControl.rewrites.head?.map RewriteRule.name = some "rule-name" := rfl

theorem escaped_and_qualified_relations_exact :
    namingControl.rewrites.head?.map RewriteRule.premises = some [
      .relationQuery "rx:rel" [.fvar "x"], .relationQuery "Scope.Rel" [.fvar "x"]] := rfl

theorem qualified_constructor_head_exact :
    namingControl.rewrites.head?.map RewriteRule.left =
      some (.apply "Scope.K" [.fvar "x"]) := rfl

theorem qualified_name_is_not_shortened :
    namingControl.terms[1]?.map GrammarRule.label ≠ some "K" := by decide

theorem escaped_guillemets_are_not_core_data :
    namingControl.terms.head?.map GrammarRule.label ≠ some "«rx:k»" := by decide

def escapedNamesControl : LanguageDef := languageDef! {
  name : "EscapedNames"
  types { «Object:Term» ![str] as «Native:Text» Scope.Kind }
  terms {
    «core:leaf». «arg:name»:«Object:Term» |- "leaf" «arg:name» : «Object:Term»;
    «core:bind». ^ «slot:name» . «body:name» : [«Object:Term» -> «Object:Term»]
      |- "bind" «body:name» : «Object:Term»;
    «core:many». ^[«x:slot», Scope.Y].«many:body» : [«Object:Term» * -> «Object:Term»]
      |- "many" «many:body» : «Object:Term»;
    «core:map». «items:list»:HashBag(«Object:Term»)
      |- *map(«items:list», |«each:item»| «each:item») : «Object:Term»;
    «core:zip». «left:items»:HashBag(«Object:Term»), «right:items»:HashBag(«Object:Term»)
      |- *zip(«left:items», «right:items»).*sep(",") : «Object:Term»;
  }
  equations {
    «eq:escaped». «arg:name»:«Object:Term» | «fresh:name» # «arg:name»
      |- «arg:name» = «arg:name»;
  }
  rewrites {
    «step:escaped». «arg:name»:«Object:Term» |
      «core:holds»(«arg:name»), forAll(«items:list», «each:item», «core:holds»(«each:item»))
      |- «core:leaf»(«arg:name») ~> ^«slot:name».«arg:name»;
    «step:multi». «arg:name»:Scope.Kind |- ^[«x:slot», Scope.Y].«arg:name» ~> {«arg:name», ...«tail:items»};
    «step:bare». |- «core:leaf»() ~> «core:leaf»();
    «step:spaced-escaped». «arg:name»:«Object:Term»
      |- «arg:name» ~> ^ «slot:name» . («arg:name»);
    «step:spaced-ordinary». argument:Scope.Kind
      |- argument ~> ^ slot . (argument);
  }
}

theorem escaped_categories_and_carriers_agree :
    escapedNamesControl.types = [⟨"Object:Term", .ast⟩, ⟨"Native:Text", .builtinString⟩,
      ⟨"Scope.Kind", .ast⟩] ∧
    escapedNamesControl.terms.head?.map GrammarRule.category = some "Object:Term" := by
  constructor <;> rfl

theorem escaped_parameters_types_and_syntax_agree :
    escapedNamesControl.terms.head?.map (fun rule => (rule.params, rule.syntaxPattern)) =
      some ([.simple "arg:name" (.base "Object:Term")],
        [.terminal "leaf", .nonTerminal "arg:name"]) := rfl

theorem escaped_binder_parameter_agrees :
    escapedNamesControl.terms[1]?.map GrammarRule.params = some [
      .abstractionNamed (some "slot:name") "body:name"
        (.arrow (.base "Object:Term") (.base "Object:Term"))] := rfl

theorem escaped_multi_binder_parameter_agrees :
    escapedNamesControl.terms[2]?.map GrammarRule.params = some [
      .multiAbstractionNamed ["x:slot", "Scope.Y"] "many:body"
        (.arrow (.multiBinder (.base "Object:Term")) (.base "Object:Term"))] := rfl

theorem escaped_syntax_map_names_agree :
    escapedNamesControl.terms[3]?.map GrammarRule.syntaxPattern = some [
      .op (.map (.var "items:list") ["each:item"] [.nonTerminal "each:item"])] := rfl

theorem escaped_syntax_zip_names_agree :
    escapedNamesControl.terms[4]?.map GrammarRule.syntaxPattern = some [
      .op (.sep "__chain__" "," (some (.zip "left:items" "right:items")))] := rfl

theorem escaped_fvars_contexts_and_binders_agree :
    escapedNamesControl.rewrites.head?.map (fun rule => (rule.typeContext, rule.left, rule.right)) =
      some ([("arg:name", .base "Object:Term")],
        .apply "core:leaf" [.fvar "arg:name"],
        .lambda (some "slot:name") (.fvar "arg:name")) := rfl

theorem escaped_quantified_names_agree :
    escapedNamesControl.rewrites.head?.map RewriteRule.premises = some [
      .relationQuery "core:holds" [.fvar "arg:name"],
      .forAll "items:list" "each:item" (.relationQuery "core:holds" [.fvar "each:item"])] := rfl

theorem escaped_freshness_names_agree :
    escapedNamesControl.equations.head?.map Equation.premises = some [
      .freshness ⟨"fresh:name", .fvar "arg:name"⟩] := rfl

theorem escaped_rest_and_multi_binder_names_agree :
    escapedNamesControl.rewrites[1]?.map (fun rule => (rule.typeContext, rule.left, rule.right)) =
      some ([("arg:name", .base "Scope.Kind")],
        .multiLambda 2 ["x:slot", "Scope.Y"] (.fvar "arg:name"),
        .collection .hashBag [.fvar "arg:name"] (some "tail:items")) := rfl

theorem escaped_category_is_not_quoted :
    escapedNamesControl.terms.head?.map GrammarRule.category ≠ some "«Object:Term»" := by decide

theorem escaped_spaced_parenthesized_binder_agrees :
    escapedNamesControl.rewrites[3]?.map RewriteRule.right =
      some (.lambda (some "slot:name") (.fvar "arg:name")) := rfl

theorem ordinary_spaced_parenthesized_binder_agrees :
    escapedNamesControl.rewrites[4]?.map RewriteRule.right =
      some (.lambda (some "slot") (.fvar "argument")) := rfl

theorem qualified_sort_is_not_shortened :
    escapedNamesControl.types[2]?.map TypeDecl.name ≠ some "Kind" := by decide

end Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexAuthoring
