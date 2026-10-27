import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RegexControls
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef

/-!
# Controls: CeTTa's core module format, read by the Lean reader

CeTTa's regex module (`RegexCore.module`) is written in the core rows of CeTTa's module format: a type with a carrier
(`Scalar = String;`), constructors with string labels, and rewrites with typed contexts and premises
(`"NULL-UNION". p:Regex, … | "rx:nullable"(p) ~> left, … |- "rx:nullable"("rx:union"(p, q)) ~> result;`). It declares
a theory and no entry.

- **The Lean reader reads it to the language CeTTa's reader elaborates** (`RegexControls.regex`, the transcription of
  CeTTa's elaboration), field for field; the reader qualifies the theory's name by its module.
- **A carrier without an interpretation is refused**, as CeTTa refuses it.
- **Sorts that constructors use and nothing declares are declared**, as CeTTa's reader declares them: GödelClaw's
  component schema has no `Types` block, and its rule rows use the token categories `String` and `Integer`.
- **The language has a core**: its evaluation premises, an instance of a pattern stepping to a pattern, are lowered
  (`LanguageDef.toCore`), so the command line answers over it (`artifacts/oslf-languages/matrix.txt`).
-/

set_option autoImplicit false

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

#module_file "../../../../artifacts/oslf-languages/RegexCore.module"
#module_file "../../../../../../metta/gslt/module/godelclaw/ComponentAPI.module"

namespace Mettapedia.OSLF.NativeTypes.Product.ReaderParityControls

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The regex theory as the Lean reader reads it. -/
def read : Except Mettapedia.GSLT.LanguageDef.ModuleSource.Error LanguageDef :=
  Mettapedia.GSLT.LanguageDef.ModuleSource.elaborateTheory RegexCore.library RegexCore.module ["RegexDerivatives"]

#guard match read with
  | .ok language =>
    language.«name» == "RegexCore.RegexDerivatives" &&
      decide (language.types = GeneratedLogic.RegexControls.regex.types) &&
      decide (language.terms = GeneratedLogic.RegexControls.regex.terms) &&
      decide (language.equations = GeneratedLogic.RegexControls.regex.equations) &&
      decide (language.rewrites = GeneratedLogic.RegexControls.regex.rewrites)
  | .error _ => false

#guard match read with
  | .ok language => decide (language.types.head? = some ⟨"Scalar", .builtinString⟩)
  | .error _ => false

#guard match read with
  | .ok language =>
    match Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.toCore language with
    | .ok _ => true
    | .error _ => false
  | .error _ => false

/-- GödelClaw's component schema as CeTTa's module reader elaborates it: the rule category with the abstract syntax,
and the token categories of labelled BNF its rule rows use with raw token carriers, in order of first use. -/
def componentTypes : List TypeDecl := [⟨"Field", .ast⟩, ⟨"String", .tokenRaw⟩, ⟨"Integer", .tokenRaw⟩]

/-- Its constructors' parameters, as CeTTa's reader names and sorts them. -/
def componentParameters : List (String × List TermParam) :=
  [("CommandField", ["String", "String", "Integer", "Integer", "String", "String"].zipIdx.map fun (sort, index) =>
      .simple s!"argument:{index}" (.base sort)),
   ("SettingField", (List.replicate 9 "String").zipIdx.map fun (sort, index) =>
      .simple s!"argument:{index}" (.base sort))]

#guard match ComponentAPI.language with
  | .ok language =>
    decide (language.types = componentTypes) &&
      decide (language.terms.map (fun rule => (rule.label, rule.params)) = componentParameters)
  | .error _ => false

end Mettapedia.OSLF.NativeTypes.Product.ReaderParityControls

/-- error: the carrier `Float` needs an explicit interpretation -/
#guard_msgs in
Module Floats { Theory Measures() { Types { Length = Float; } } }
