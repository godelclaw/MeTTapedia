import Mettapedia.GSLT.LanguageDef.FreshNamedContext

/-!
# Structural macro substitution and printed binding positions

The template markers are expression/syntax argument slots, type argument slots,
local binder slots and explicit captures. Literal symbols and strings remain distinct. Instantiation traverses
the whole tree; a supplied argument is inserted without renaming its contents.
Finite indices represent the definition check's resolved slot identities.

The symbol-origin theorem connects that substitution to printed local names:
under independently checked freshness and injectivity, a printed local name
can occur only at that local marker. The existing named-context calculus then
connects admitted printed names to exact binder positions and preserves old
positions across an inserted frame, including contexts that already shadow.

These laws do not prove C parsing, C namespace admission, native header name
inventory, C type checking, evaluation counts, or the native C implementation.
Those connections require their own source data and implementation evidence.
-/

namespace Mettapedia.GSLT.LanguageDef.MacroTemplateNames

open Mettapedia.GSLT.LanguageDef.NamedFreeContext
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

inductive Namespace where
  | ordinary | tag | member | label
  deriving DecidableEq, Repr

inductive Atom where
  | symbol (name : String)
  | text (bytes : String)
  | list (items : List Atom)
  deriving Repr

inductive Template (arguments locals : Nat) where
  | symbol (name : String)
  | text (bytes : String)
  | list (items : List (Template arguments locals))
  | argument (slot : Fin arguments)
  | typeArgument (slot : Fin arguments)
  | bound (slot : Fin locals)
  | capture (space : Namespace) (name : String)
  deriving Repr

mutual
  def instantiate {arguments locals : Nat} (actual : Fin arguments → Atom)
      (names : Fin locals → String) : Template arguments locals → Atom
    | .symbol name => .symbol name
    | .text bytes => .text bytes
    | .list items => .list (instantiateMany actual names items)
    | .argument slot => actual slot
    | .typeArgument slot => actual slot
    | .bound slot => .symbol (names slot)
    | .capture _ name => .symbol name

  def instantiateMany {arguments locals : Nat} (actual : Fin arguments → Atom)
      (names : Fin locals → String) : List (Template arguments locals) → List Atom
    | [] => []
    | first :: rest => instantiate actual names first :: instantiateMany actual names rest
end

mutual
  def argumentCount {arguments locals : Nat} : Template arguments locals → Fin arguments → Nat
    | .symbol _, _ => 0
    | .text _, _ => 0
    | .list items, slot => argumentCountMany items slot
    | .argument present, slot => if present = slot then 1 else 0
    | .typeArgument _, _ => 0
    | .bound _, _ => 0
    | .capture _ _, _ => 0

  def argumentCountMany {arguments locals : Nat} :
      List (Template arguments locals) → Fin arguments → Nat
    | [], _ => 0
    | first :: rest, slot => argumentCount first slot + argumentCountMany rest slot
end

mutual
  def typeArgumentCount {arguments locals : Nat} : Template arguments locals → Fin arguments → Nat
    | .symbol _, _ => 0
    | .text _, _ => 0
    | .list items, slot => typeArgumentCountMany items slot
    | .argument _, _ => 0
    | .typeArgument present, slot => if present = slot then 1 else 0
    | .bound _, _ => 0
    | .capture _ _, _ => 0

  def typeArgumentCountMany {arguments locals : Nat} :
      List (Template arguments locals) → Fin arguments → Nat
    | [], _ => 0
    | first :: rest, slot => typeArgumentCount first slot + typeArgumentCountMany rest slot
end

mutual
  def symbols : Atom → List String
    | .symbol name => [name]
    | .text _ => []
    | .list items => symbolsMany items

  def symbolsMany : List Atom → List String
    | [] => []
    | first :: rest => symbols first ++ symbolsMany rest
end

mutual
  def literalSymbols {arguments locals : Nat} : Template arguments locals → List String
    | .symbol name => [name]
    | .text _ => []
    | .list items => literalSymbolsMany items
    | .argument _ => []
    | .typeArgument _ => []
    | .bound _ => []
    | .capture _ name => [name]

  def literalSymbolsMany {arguments locals : Nat} : List (Template arguments locals) → List String
    | [] => []
    | first :: rest => literalSymbols first ++ literalSymbolsMany rest
end

mutual
  def localSlots {arguments locals : Nat} : Template arguments locals → List (Fin locals)
    | .symbol _ => []
    | .text _ => []
    | .list items => localSlotsMany items
    | .argument _ => []
    | .typeArgument _ => []
    | .bound slot => [slot]
    | .capture _ _ => []

  def localSlotsMany {arguments locals : Nat} : List (Template arguments locals) → List (Fin locals)
    | [] => []
    | first :: rest => localSlots first ++ localSlotsMany rest
end

mutual
  theorem symbol_origins {arguments locals : Nat} (actual : Fin arguments → Atom)
      (names : Fin locals → String) (template : Template arguments locals) (name : String)
      (occurs : name ∈ symbols (instantiate actual names template)) :
      name ∈ literalSymbols template ∨
        (∃ slot, name ∈ symbols (actual slot)) ∨
        ∃ slot ∈ localSlots template, name = names slot := by
    cases template with
    | symbol literal =>
        exact Or.inl (by simpa [instantiate, symbols, literalSymbols] using occurs)
    | text bytes => simp [instantiate, symbols] at occurs
    | list items => exact symbol_origins_many actual names items name occurs
    | argument slot =>
        exact Or.inr (Or.inl ⟨slot, occurs⟩)
    | typeArgument slot =>
        exact Or.inr (Or.inl ⟨slot, occurs⟩)
    | bound slot =>
        have same : name = names slot := by simpa [instantiate, symbols] using occurs
        exact Or.inr (Or.inr ⟨slot, by simp [localSlots], same⟩)
    | capture space literal =>
        exact Or.inl (by simpa [instantiate, symbols, literalSymbols] using occurs)
  termination_by sizeOf template

  theorem symbol_origins_many {arguments locals : Nat} (actual : Fin arguments → Atom)
      (names : Fin locals → String) (templates : List (Template arguments locals)) (name : String)
      (occurs : name ∈ symbolsMany (instantiateMany actual names templates)) :
      name ∈ literalSymbolsMany templates ∨
        (∃ slot, name ∈ symbols (actual slot)) ∨
        ∃ slot ∈ localSlotsMany templates, name = names slot := by
    cases templates with
    | nil => simp [instantiateMany, symbolsMany] at occurs
    | cons first rest =>
        simp only [instantiateMany, symbolsMany, List.mem_append] at occurs
        rcases occurs with head | tail
        · rcases symbol_origins actual names first name head with literal | argument | bound
          · exact Or.inl (by simpa [literalSymbolsMany] using
              List.mem_append_left (literalSymbolsMany rest) literal)
          · exact Or.inr (Or.inl argument)
          · rcases bound with ⟨slot, present, same⟩
            exact Or.inr (Or.inr ⟨slot, by simp [localSlotsMany, present], same⟩)
        · rcases symbol_origins_many actual names rest name tail with literal | argument | bound
          · exact Or.inl (by simpa [literalSymbolsMany] using
              List.mem_append_right (literalSymbols first) literal)
          · exact Or.inr (Or.inl argument)
          · rcases bound with ⟨slot, present, same⟩
            exact Or.inr (Or.inr ⟨slot, by simp [localSlotsMany, present], same⟩)
  termination_by sizeOf templates
end

/-- Distinct identities have distinct printed names, and those names avoid
both literal/captured symbols and all symbols in every inserted argument. -/
def NamesAdmitted {arguments locals : Nat} (actual : Fin arguments → Atom)
    (names : Fin locals → String) (template : Template arguments locals) : Prop :=
  Function.Injective names ∧
    (∀ slot, names slot ∉ literalSymbols template) ∧
    ∀ binder argument, names binder ∉ symbols (actual argument)

instance {arguments locals : Nat} (actual : Fin arguments → Atom)
    (names : Fin locals → String) (template : Template arguments locals) :
    Decidable (NamesAdmitted actual names template) := by
  unfold NamesAdmitted Function.Injective
  infer_instance

/-- Executable admission examines only names and symbol inventories; it does
not assume that an emitted reference already resolves correctly. -/
def checkNames {arguments locals : Nat} (actual : Fin arguments → Atom)
    (names : Fin locals → String) (template : Template arguments locals) : Bool :=
  decide (NamesAdmitted actual names template)

theorem checkNames_sound {arguments locals : Nat} (actual : Fin arguments → Atom)
    (names : Fin locals → String) (template : Template arguments locals)
    (checked : checkNames actual names template = true) :
    NamesAdmitted actual names template := by
  exact of_decide_eq_true checked

/-- An emitted local name witnesses that exact local slot in the template.
An equal-looking name from a caller or a literal cannot supply the witness. -/
theorem emitted_local_reflects {arguments locals : Nat} (actual : Fin arguments → Atom)
    (names : Fin locals → String) (template : Template arguments locals)
    (admitted : NamesAdmitted actual names template) (slot : Fin locals)
    (occurs : names slot ∈ symbols (instantiate actual names template)) :
    slot ∈ localSlots template := by
  rcases symbol_origins actual names template (names slot) occurs with literal | argument | bound
  · exact False.elim (admitted.2.1 slot literal)
  · rcases argument with ⟨argument, present⟩
    exact False.elim (admitted.2.2 slot argument present)
  · rcases bound with ⟨other, present, same⟩
    have equal : slot = other := admitted.1 same
    simpa [equal] using present

/-- A checked local frame resolves a printed name to its exact intrinsic
position. This reuses the binding-signature owner, rather than a string-only
notion of equal answers. -/
theorem admitted_local_position (frame : List (String × TypeExpr)) (reserved : List String)
    (checked : admitNames frame reserved = true) {sort : TypeExpr}
    (position : Var (contextSorts frame) sort) :
    lookupPosition? frame (nameAt frame position) sort = some position :=
  admitted_printed_position frame reserved checked position

/-- Freshness against the old context preserves a previously resolved name,
even when that old context itself contains shadowed duplicate spellings. -/
theorem admitted_frame_preserves_existing (frame entries : List (String × TypeExpr))
    (checked : admitNames frame (entries.map Prod.fst) = true)
    (name : String) (sort : TypeExpr) (position : Var (contextSorts entries) sort)
    (resolved : lookupPosition? entries name sort = some position) :
    lookupPosition? (frame ++ entries) name sort =
      some (prependPosition frame entries position) := by
  have oldName : name ∈ entries.map Prod.fst := by
    rw [← lookupPosition?_sound entries name sort resolved]
    exact nameAt_mem_names entries position
  have fresh : name ∉ frame.map Prod.fst := by
    have admission : (frame.map Prod.fst).Nodup ∧
        ∀ spelling ∈ frame.map Prod.fst, spelling ∉ entries.map Prod.fst := by
      simpa [admitNames] using checked
    intro present
    exact admission.2 name present oldName
  rw [lookup_fresh_prefix frame entries name sort fresh, resolved]
  rfl

def duplicateArgument : Template 1 0 := .list [.argument 0, .argument 0]
def suppliedType : Template 1 0 := .list [.symbol "var", .typeArgument 0]
def capturedLocal : Template 0 1 := .list [.capture .ordinary "tmp", .bound 0]

example : symbols (instantiate (fun _ => .symbol "caller") Fin.elim0 duplicateArgument) =
    ["caller", "caller"] := rfl

example : argumentCount suppliedType 0 = 0 ∧ typeArgumentCount suppliedType 0 = 1 := by decide
example : instantiate (fun _ => .list [.symbol "unsigned", .symbol "long"])
    Fin.elim0 suppliedType = .list [.symbol "var", .list [.symbol "unsigned", .symbol "long"]] := rfl

example : ¬ NamesAdmitted Fin.elim0 (fun _ => "tmp") capturedLocal := by
  intro admitted
  exact admitted.2.1 0 (by simp [capturedLocal, literalSymbols, literalSymbolsMany])

example : checkNames Fin.elim0 (fun _ => "tmp") capturedLocal = false := by decide
example : checkNames Fin.elim0 (fun _ => "fresh") capturedLocal = true := by decide

example : lookupPosition? [("caller", .base "Expr"), ("caller", .base "Expr")]
    "caller" (.base "Expr") = some Var.zero := by
  simp [lookupPosition?]; rfl

#print axioms symbol_origins
#print axioms emitted_local_reflects
#print axioms admitted_local_position
#print axioms admitted_frame_preserves_existing

end Mettapedia.GSLT.LanguageDef.MacroTemplateNames
