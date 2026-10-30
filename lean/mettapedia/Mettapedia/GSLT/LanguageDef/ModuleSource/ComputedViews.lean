import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.Parsing.ParserProfileSemantics
import Lean

/-! Propose closed data views of computed module values. The elaborators
only quote data; they supply no equality theorem or admission authority.
Consumers must separately certify a view against its authored source or
encoded payload before using it as a source interpretation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

open Lean Elab Term
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.ParserProfileSemantics

scoped syntax (name := languageView) "module_language_view% " term:max : term
scoped syntax (name := profileView) "module_profile_view% " term:max : term

private def quotedContents : List Char → List Char × List Char
  | [] => ([], [])
  | '\\' :: escaped :: rest =>
      let (quoted, remaining) := quotedContents rest
      ('\\' :: escaped :: quoted, remaining)
  | '"' :: rest => (['"'], rest)
  | character :: rest =>
      let (quoted, remaining) := quotedContents rest
      (character :: quoted, remaining)

private def fieldCharacter (character : Char) : Bool :=
  character.isAlphanum || character == '_' || character == '?' || character == '!'

/-- Repr field names may have become keywords in the caller's parser scopes.
Quote record fields and flatten layout while copying string literals,
including escapes, intact. Changed field widths cannot change indentation.
This still proposes data only; consumers certify the quoted value separately. -/
private def protectFields : Nat → List Char → List Char
  | 0, input => input
  | _ + 1, [] => []
  | fuel + 1, '"' :: rest =>
      let (quoted, remaining) := quotedContents rest
      '"' :: (quoted ++ protectFields fuel remaining)
  | fuel + 1, input@(character :: rest) =>
      if character.isAlpha || character == '_' then
        let token := input.takeWhile fieldCharacter
        let remaining := input.dropWhile fieldCharacter
        let following := remaining.dropWhile Char.isWhitespace
        let field := if following.take 2 == [':', '='] then
            '«' :: (token ++ ['»']) else token
        field ++ protectFields fuel remaining
      else (if character.isWhitespace then ' ' else character) :: protectFields fuel rest

private def readDataTerm (text : String) : TermElabM Syntax := do
  let characters := text.toList
  let protectedText := String.ofList (protectFields characters.length characters)
  match Parser.runParserCategory (← getEnv) `term protectedText with
  | .ok parsed => pure parsed
  | .error message => throwError "computed module data could not be quoted: {message}"

@[term_elab languageView] unsafe def elabLanguageView : TermElab := fun stx expected => do
  let `(module_language_view% $source:term) := stx | throwUnsupportedSyntax
  let type := mkApp (mkConst ``Option [Level.zero]) (mkConst ``LanguageDef)
  let expression ← elabTermEnsuringType source type
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let value ← Meta.evalExpr (Option LanguageDef) type expression
  let some language := value | throwError "the requested module language did not elaborate"
  elabTerm (← readDataTerm (reprStr language)) expected

@[term_elab profileView] unsafe def elabProfileView : TermElab := fun stx expected => do
  let `(module_profile_view% $source:term) := stx | throwUnsupportedSyntax
  let type := mkApp (mkConst ``Option [Level.zero]) (mkConst ``ParserProfileLayer)
  let expression ← elabTermEnsuringType source type
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let value ← Meta.evalExpr (Option ParserProfileLayer) type expression
  let some profile := value | throwError "the requested lexical-profile value did not decode"
  elabTerm (← readDataTerm (reprStr profile)) expected

end Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews
