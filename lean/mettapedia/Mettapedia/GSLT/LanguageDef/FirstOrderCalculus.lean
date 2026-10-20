import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef

/-!
# Constructors for binder-free first-order calculus declarations

These helpers build existing grammar and rule records. They add no semantic
laws or admission bypass: validation and interpretation remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FirstOrderCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A constructor with simple sorted parameters and no surface syntax. -/
def term (label category : String) (params : List (String × String)) : GrammarRule :=
  { label, category, params := params.map fun (name, sort) =>
      TermParam.simple name (.base sort), syntaxPattern := [] }

def fv (name : String) : Pattern := .fvar name

def app (head : String) (arguments : List Pattern) : Pattern := .apply head arguments

/-- Every parameter occurs outside binders, at depth zero. -/
def rule (id : String) (vars : List String) (premises : List Pattern)
    (conclusion : Pattern) : RuleSchema :=
  { id := ⟨id⟩, metavariables := vars.map (·, 0), premises, conclusion }

end Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
