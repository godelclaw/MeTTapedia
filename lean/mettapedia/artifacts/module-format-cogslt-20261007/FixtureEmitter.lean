import Mettapedia.GSLT.LanguageDef.ModuleFormat.Controls
import Lean.Data.Json

open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.GSLT.LanguageDef.ModuleFormat.Controls

private def quoted (text : String) : String := (Lean.Json.str text).compress

/-- Rendering for independent Rust comparison, outside the proof kernel. -/
private partial def rustValue : Value → String
  | .record fields =>
      "RhoValue::Map(BTreeMap::from([" ++
        String.intercalate "," (fields.map fun (key, value) =>
          "(" ++ quoted key ++ ".into()," ++ rustValue value ++ ")") ++ "]))"
  | .list values => "RhoValue::List(vec![" ++
      String.intercalate "," (values.map rustValue) ++ "])"
  | .string text => "RhoValue::String(" ++ quoted text ++ ".into())"
  | .bytes values => "RhoValue::Bytes(vec![" ++
      String.intercalate "," (values.map fun byte => toString byte.toNat) ++ "])"
  | .integer value => "RhoValue::Integer(" ++ toString value ++ "i128)"
  | .floatBits value => "RhoValue::FloatBits(" ++ toString value.toNat ++ "u64)"
  | .boolean value => "RhoValue::Boolean(" ++ toString value ++ ")"
  | .nil => "RhoValue::Nil"

def main : IO Unit := do
  IO.println "#[test] fn lean_generated_fixture_projection_comparison() {"
  IO.println "use crate::canonical::RhoValue; use crate::module::CanonicalModuleValue; use std::collections::BTreeMap;"
  for fixture in fixtures do
    let expected := match decode? upstreamLimits fixture.2.1 with
      | none => "None"
      | some declaration => "Some(" ++ rustValue (encodeRaw declaration.val) ++ ")"
    IO.println ("{let input = " ++ rustValue fixture.2.1 ++
      "; let expected: Option<RhoValue> = " ++ expected ++
      "; let actual = CanonicalModuleValue::from_rho_value(&input).ok().map(|m|m.to_rho_value());" ++
      "assert_eq!(actual, expected, " ++ quoted fixture.1 ++
      ");println!(\"PASS: {}\", " ++ quoted fixture.1 ++ ");}")
  IO.println "}"
