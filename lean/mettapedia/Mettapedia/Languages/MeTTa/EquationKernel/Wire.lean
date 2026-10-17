import Mettapedia.Languages.MeTTa.EquationKernel.Certificate

/-!
# MeTTa text of programs, certificates and claims

The MeTTa checker reads object atoms as data. Every object symbol and variable
name becomes a string, so no object atom is evaluated by the host, and every
integer becomes its canonical decimal string, so every engine's reader accepts
it (HE's reader refuses integer literals beyond 64 bits):

* `(ek:sym "name")`, `(ek:var "name")`, `(ek:int "decimal")`, `(ek:str "text")`,
  `(ek:bool "True")`, `(ek:gnd "type" "data")`, `(ek:expr list)`;
* lists are `ek:nil` and `(ek:cons head tail)`.

Rows, bindings and certificates use `ek:refl`, `ek:step`, `ek:congr`,
`ek:trans`, `ek:cite`, `ek:bind`, `ek:cert` and `ek:claim`.

Reading this text back into the same data is the host reader's part of the
trust account; no reader theorem is stated here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EquationKernel.Wire

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.EquationKernel

/-- A string literal; quote and backslash are escaped. -/
def quoteChars : List Char → List Char
  | [] => []
  | c :: rest =>
      if c = '"' then '\\' :: '"' :: quoteChars rest
      else if c = '\\' then '\\' :: '\\' :: quoteChars rest
      else c :: quoteChars rest

def quoteString (text : String) : String := "\"" ++ String.ofList (quoteChars text.toList) ++ "\""

def intText (n : Int) : String := toString n

def groundedText : GroundedValue → String
  | .int n => "(ek:int " ++ quoteString (intText n) ++ ")"
  | .string text => "(ek:str " ++ quoteString text ++ ")"
  | .bool value => "(ek:bool " ++ quoteString (if value then "True" else "False") ++ ")"
  | .custom type data => "(ek:gnd " ++ quoteString type ++ " " ++ quoteString data ++ ")"

def listText (items : List String) : String :=
  items.foldr (fun item rest => "(ek:cons " ++ item ++ " " ++ rest ++ ")") "ek:nil"

/-- The MeTTa data text of an atom. -/
def atomText : Atom → String
  | .symbol name => "(ek:sym " ++ quoteString name ++ ")"
  | .var name => "(ek:var " ++ quoteString name ++ ")"
  | .grounded value => groundedText value
  | .expression atoms => "(ek:expr " ++ listText (atomsText atoms) ++ ")"
where
  atomsText : List Atom → List String
    | [] => []
    | atom :: atoms => atomText atom :: atomsText atoms

def natListText (numbers : List Nat) : String := listText (numbers.map toString)

def bindingsText (bindings : Bindings) : String :=
  listText (bindings.map fun (name, value) => "(ek:bind " ++ quoteString name ++ " " ++ atomText value ++ ")")

def citationText (citation : Citation) : String :=
  "(ek:cite " ++ atomText citation.equation ++ " " ++ toString citation.copy ++ ")"

def rowText : Row → String
  | .refl atom => "(ek:refl " ++ atomText atom ++ ")"
  | .step prior citation path bindings =>
      "(ek:step " ++ toString prior ++ " " ++ citationText citation ++ " " ++ natListText path ++ " " ++
        bindingsText bindings ++ ")"
  | .congr left inner right =>
      "(ek:congr " ++ listText (atomText.atomsText left) ++ " " ++ toString inner ++ " " ++
        listText (atomText.atomsText right) ++ ")"
  | .trans first second => "(ek:trans " ++ toString first ++ " " ++ toString second ++ ")"

def certificateText (certificate : Certificate) : String :=
  "(ek:cert " ++ listText (certificate.rows.map rowText) ++ " " ++ toString certificate.root ++ ")"

def programText (program : List Atom) : String := listText (program.map atomText)

def claimText (claim : Claim) : String :=
  "(ek:claim " ++ atomText claim.1 ++ " " ++ atomText claim.2 ++ ")"

/-- A certificate as atoms of a space, under a name: its size, its root and
one atom per row. -/
def certificateFacts (name : String) (certificate : Certificate) : String :=
  "(ek:size " ++ name ++ " " ++ toString certificate.rows.length ++ ")\n" ++
  "(ek:root " ++ name ++ " " ++ toString certificate.root ++ ")\n" ++
  String.join (certificate.rows.zipIdx.map fun (row, index) =>
    "(ek:row " ++ name ++ " " ++ toString index ++ " " ++ rowText row ++ ")\n")

end Mettapedia.Languages.MeTTa.EquationKernel.Wire
