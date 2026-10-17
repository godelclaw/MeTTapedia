import Mettapedia.GSLT.LanguageDef.ModuleSource.Syntax
import Mettapedia.GSLT.LanguageDef.ModuleSource.Elaborate
import Mettapedia.GSLT.LanguageDef.ModuleSource.Printer
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.ModuleSource.Controls
import Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode

/-!
# The `.module` format

The human text format of language definitions: theories with parameters, joins over shared
origins, replacements and renamed exports, imports, and an entry theory. `#module_file` reads a
`.module` file in Lean and `ModuleSource.elaborate` gives it its `LanguageDef`;
`ModuleSource.Printer.print` writes it back. The same format is LBNF data
(`metta/gslt/module/module_v1.cf`) for grammar-driven readers; `ModuleSource.LbnfDecode` reads
their trees as the same module data.
-/
