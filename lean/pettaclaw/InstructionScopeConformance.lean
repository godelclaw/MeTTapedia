import InstructionScope

/-!
# Lean-to-MeTTa instruction-scope conformance generator

Lean owns the concrete scope chain below.  Running this file emits a complete
MeTTa probe containing both the input chain and the expected results computed
by `InstructionScope.resolve`.  The runtime test therefore cannot remain green
merely because a second handwritten fixture copied the same mistake.
-/

namespace PettaClaw.InstructionScopeConformance

open PettaClaw.InstructionScope

abbrev StringScope := Scope String String String

def keys : List String :=
  ["may-edit", "session-refresh-sec", "reply-format", "absent-key"]

def rootRules : Rules String String
  | "may-edit" => some "allowed"
  | "reply-format" => some "concise"
  | _ => none

def middleRules : Rules String String
  | "session-refresh-sec" => some "259200"
  | _ => none

def nearestRules : Rules String String
  | "may-edit" => some "forbidden"
  | _ => none

def root : StringScope := ⟨["work"], rootRules⟩
def middle : StringScope := ⟨["work", "project"], middleRules⟩
def nearest : StringScope :=
  ⟨["work", "project", "component"], nearestRules⟩

def target : Path String := ["work", "project", "component", "file"]
def scopes : List StringScope := [nearest, middle, root]

def quoted (text : String) : String := reprStr text

def directoryName (directory : Path String) : String :=
  String.intercalate "/" directory

def renderRules (scope : StringScope) : String :=
  keys.foldr
    (fun key outer =>
      match scope.rules key with
      | none => outer
      | some value =>
          "(coordinate " ++ quoted key ++ " " ++ quoted value ++ " " ++
            outer ++ ")")
    "coordinates-empty"

def renderChain : List StringScope → String
  | [] => "instruction-scope-chain-empty"
  | scope :: outer =>
      "(instruction-scope-chain (instruction-scope-layer " ++
        quoted (directoryName scope.directory) ++ " " ++ renderRules scope ++
        ") " ++ renderChain outer ++ ")"

def renderExpected (key : String) : String :=
  match resolve target key scopes with
  | none => "(no-instruction " ++ quoted key ++ ")"
  | some result =>
      "(resolved-instruction " ++ quoted (directoryName result.directory) ++
        " " ++ quoted key ++ " " ++ quoted result.value ++ ")"

def renderAssertion (key : String) : String :=
  "         ($_ (assertEqual (instruction-resolve " ++ quoted key ++
    " $chain) " ++ renderExpected key ++ "))"

def generatedProbe : String :=
  String.intercalate "\n"
    (["!(import! &self (library lib_import))",
      "!(import! &self ./src/open_assemblage)",
      "!(import! &self ./src/instruction_scope)",
      "",
      "(= (assertEqual $A $B) (assert (== $A $B)))",
      "",
      "!(let* (($chain " ++ renderChain scopes ++ ")"] ++
      keys.map renderAssertion ++
      ["         )",
       "     (println! LEAN_METTA_INSTRUCTION_SCOPE_OK))"])

end PettaClaw.InstructionScopeConformance

def main : IO Unit :=
  IO.println PettaClaw.InstructionScopeConformance.generatedProbe
