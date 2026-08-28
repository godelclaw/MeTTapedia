import Mettapedia.OSLF.MeTTaIL.Export
import GFCore.Json
import GFCore.SigGen
import Algorithms.GF.Generated.PaperAmbiguitySig
import Mettapedia.Languages.GF.GFRealSyntaxBridge
import Mettapedia.Languages.Metamath.LanguageDefDSL
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefDSL

open Mettapedia.OSLF.MeTTaIL

namespace Mettapedia.Tools.WriteLanguageFixtures

private def fixtureBase : IO System.FilePath := do
  match (← IO.getEnv "METTAIL_RUST_LEAN_EXPORT_DIR") with
  | some path => pure path
  | none => pure "../externals/mettail-rust/macros/tests/fixtures/lean_export"

private def gfPaperSyntaxLang :=
  Mettapedia.Languages.GF.GFCoreOSLFBridge.gfSyntaxLanguageDef
    Algorithms.GF.Generated.PaperAmbiguitySig.sig

private def gfProjectCoreEngPath : System.FilePath :=
  "../algorithms/gf_fragments/generated/GrammarEng.project_core.json"

def writeLanguageFixtures : IO Unit := do
  let fixtureBase ← fixtureBase
  IO.FS.createDirAll fixtureBase
  let metamathPath := fixtureBase / "metamath_core.language"
  let rhocalcPath := fixtureBase / "rhocalc_core.language"
  let gfPaperPath := fixtureBase / "gf_paper_ambiguity.language"
  let gfProjectCorePath := fixtureBase / "gf_project_core.language"
  let gfProjectCoreSig ← GFCore.sigFromPGFJsonFile gfProjectCoreEngPath
  let gfProjectCoreLang :=
    Mettapedia.Languages.GF.GFCoreOSLFBridge.gfSyntaxLanguageDef gfProjectCoreSig
  IO.FS.writeFile metamathPath
    (Export.renderLanguage
      Mettapedia.Languages.Metamath.LanguageDefDSL.metamathCore ++ "\n")
  IO.FS.writeFile rhocalcPath
    (Export.renderLanguage
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Extended.rhoCalcExtended ++ "\n")
  IO.FS.writeFile gfPaperPath
    (Export.renderLanguage gfPaperSyntaxLang ++ "\n")
  IO.FS.writeFile gfProjectCorePath
    (Export.renderLanguage gfProjectCoreLang ++ "\n")
  IO.println s!"Wrote fixtures:\n  {metamathPath}\n  {rhocalcPath}\n  {gfPaperPath}\n  {gfProjectCorePath}"

end Mettapedia.Tools.WriteLanguageFixtures
