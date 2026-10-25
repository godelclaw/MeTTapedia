import Mettapedia.Languages.MM0.HOLKernelSyntax
import Mettapedia.Languages.MM0.Formats.MMB.Statements

/-!
# Reading the HOL constructor interface from decoded MM0 tables

The decoder checks sort flags, retained name references and every native
constructor declaration against the maintained HOL profiles. Its successful
result supplies the actual kernel signature required by the all-constructor
sorting theorem. Definition bodies use the existing MMB declaration reader.

Names are supplied by the caller's name-resolution table. Checking these
constructor profiles is distinct from verifying the artifact's proofs or
establishing its agreement with a textual specification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelSignature

open Kernel Formats.MMB HOLKernelSyntax

def sortSignature (tables : Tables) : SortSignature := fun index => tables.sorts[index]?

def termSignature (tables : Tables) : TermSignature := fun index => do
  let entry ← tables.terms[index]?
  let declaration ← Statements.termDecl tables.terms entry
  pure declaration.1

def theoremSignature (tables : Tables) : TheoremSignature := fun index => do
  let entry ← tables.thms[index]?
  Statements.theoremDecl tables.terms entry

def definitionSignature (tables : Tables) : Definition.Signature := fun index => do
  let entry ← tables.terms[index]?
  let declaration ← Statements.termDecl tables.terms entry
  declaration.2

def readSignature? (tables : Tables) (ids : SortIds) (references : Symbol → Nat)
    (names : Nat → Option String) :
    Option (Signature (sortSignature tables) (termSignature tables)) :=
  if wff : sortSignature tables ids.wff = some { strict := true, provable := true } then
  if typeFound : sortSignature tables ids.type = some { strict := true } then
  if objectFound : sortSignature tables ids.object = some {} then
  if named : Symbol.all.all (fun constructor =>
      decide (names (references constructor) = some constructor.name)) = true then
  if declared : Symbol.all.all (fun constructor =>
      decide (termSignature tables (references constructor) = some (constructor.profile ids))) = true then
    some {
      ids := ids
      wffDeclared := wff
      typeDeclared := typeFound
      objectDeclared := objectFound
      symbol := references
      names := names
      named := fun constructor => of_decide_eq_true
        ((List.all_eq_true.mp named) constructor (Symbol.mem_all constructor))
      declared := fun constructor => of_decide_eq_true
        ((List.all_eq_true.mp declared) constructor (Symbol.mem_all constructor)) }
  else none else none else none else none else none

#print axioms readSignature?

end Mettapedia.Languages.MM0.HOLKernelSignature
