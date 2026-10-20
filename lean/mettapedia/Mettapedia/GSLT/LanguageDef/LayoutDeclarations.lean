import Mettapedia.GSLT.LanguageDef.LayoutCodes
import Mettapedia.GSLT.LanguageDef.MacroExportPlan

/-!
# Declared layouts, as Cesta prints them

`cesta layout check` reads the layouts a module declares, evaluates their
constants, builds the prefix trie of their cases and prints each in a
normalized form:

    (cesta-layout/1 NAME WIDTH (Fields (FIELD KIND WRITTEN) …) TRIE
      (Location DISCIPLINE) (Aliases …) (Requires …))
    TRIE ::= (Leaf "admits"|"reserved" (Place SHIFT WIDTH OFFSET LO HI) …)
           | (Node TRIE TRIE)

`decodeLayout` reads that form back into a `LayoutCodes.Code`. The admission
decides, for each declared layout, that it decodes and that the decoded code
is well formed, so the generic laws of `LayoutCodes` hold of the layout the
module actually declares. Its normalized kinds, write phases, location,
aliases and slot-width requirements are checked as declaration conditions.
This does not prove that a user's C program obeys the declared write discipline.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.LayoutDeclarations

open Mettapedia.GSLT.LanguageDef.LayoutAlgebra (Slot)
open Mettapedia.GSLT.LanguageDef.LayoutCodes
open Mettapedia.GSLT.LanguageDef.MacroExportPlan (Atom)

/-- A decimal numeral, as Cesta prints numbers. -/
def decimal (s : String) : Option Nat :=
  if s.isEmpty then none
  else s.toList.foldl (fun acc c => acc.bind fun n =>
    if c.isDigit then some (10 * n + (c.toNat - '0'.toNat)) else none) (some 0)

def number : Atom → Option Nat
  | .symbol s => decimal s
  | _ => none

def decodePlace : Atom → Option Place
  | .list [.symbol "Place", s, w, o, lo, hi] => do
      pure ⟨⟨← number s, ← number w⟩, ← number o, ← number lo, ← number hi⟩
  | _ => none

def decodeTrie : Atom → Option Trie
  | .list (.symbol "Leaf" :: .text kind :: places) => do
      let reserved ← match kind with
        | "admits" => some false
        | "reserved" => some true
        | _ => none
      pure (.leaf ⟨← places.mapM decodePlace, reserved⟩)
  | .list [.symbol "Node", zero, one] => do
      pure (.node (← decodeTrie zero) (← decodeTrie one))
  | _ => none

/-- A field: its name, its kind and when it is written. -/
structure Field where
  name : String
  kind : String
  written : String
deriving DecidableEq, Repr

def decodeField : Atom → Option Field
  | .list [.symbol name, .text kind, .text written] => some ⟨name, kind, written⟩
  | _ => none

structure Declaration where
  name : String
  fields : List Field
  code : Code

def decodeLayout : Atom → Option Declaration
  | .list (.symbol "cesta-layout/1" :: .symbol name :: width :: .list (.symbol "Fields" :: fields) :: trie :: _) => do
      pure ⟨name, ← fields.mapM decodeField, ⟨← number width, ← decodeTrie trie⟩⟩
  | _ => none

/-- Each case places every field, in the order the fields are declared. -/
def arityOk (d : Declaration) : Bool :=
  d.code.trie.leaves.all fun l => l.1.places.length == d.fields.length

/-- The field annotations accepted by the declaration language. -/
def fieldMetadataOk (f : Field) : Bool :=
  ["value", "any-child", "all-children", "fact", "cache", "occurrence", "reference"].contains f.kind &&
    ["construction", "after-publication"].contains f.written

def aliasOk (fields : List Field) : Atom → Bool
  | .list [.symbol name, .symbol field, .text condition] =>
      fields.any (fun f => f.name == field) && !(fields.any fun f => f.name == name) && !condition.isEmpty
  | _ => false

/-- `AtMost` constrains the stored slot width, as the Cesta declaration does;
it does not constrain a field's logical value after adding its offset. -/
def requirementOk (d : Declaration) : Atom → Bool
  | .list [.symbol field, bits, .text _] =>
      match number bits with
      | some width => d.fields.any (fun f => f.name == field) &&
          d.code.trie.leaves.all fun l =>
            (d.fields.zip l.1.places).all fun fp => fp.1.name != field || decide (fp.2.slot.width ≤ width)
      | none => false
  | _ => false

/-- The normalized metadata is checked independently of the word algebra.
An atomic declaration is a requirement on its users, not a proof that any
particular C program obeys the C11 memory model. Identifier and exported-name
collision checks remain in Cesta's native module checker; logical field names
need not be literal C binder names. -/
def metadataContentsOk (d : Declaration) (discipline : String) (aliases requirements : List Atom) : Bool :=
  decide (1 ≤ d.code.width ∧ d.code.width ≤ 64) &&
    ["immutable", "single-owner", "construction", "atomic"].contains discipline &&
    d.fields.all fieldMetadataOk &&
    pairwiseB (fun a b => a.name != b.name) d.fields &&
    d.fields.all (fun f => f.written != "after-publication" || discipline == "atomic") &&
    (match d.code.trie with
      | .leaf _ => true
      | .node _ _ => d.fields.all fun f => ["value", "fact", "reference"].contains f.kind) &&
    aliases.all (aliasOk d.fields) && requirements.all (requirementOk d)

/-! ## Keys -/

/-- The position of a field. -/
def fieldIndex (d : Declaration) (name : String) : Option Nat :=
  d.fields.findIdx? (·.name == name)

/-- The cases that admit values, in prefix order. -/
def admitting (k : Code) : List (Case × Nat × Nat) :=
  k.trie.leaves.filter fun l => !l.1.reserved

/-- Field `j` of an earlier admitting case lies wholly below field `j` of a
later one. -/
def below (j : Nat) (a b : Case × Nat × Nat) : Bool :=
  match a.1.places[j]?, b.1.places[j]? with
  | some p, some q => decide (p.hi < q.lo)
  | _, _ => false

/-- Field `j` keys the code: its ranges ascend through the admitting cases in
prefix order, so the case of an admitted value is the one whose range holds
its field `j`. -/
def keyAscending (k : Code) (j : Nat) : Bool := pairwiseB (below j) (admitting k)

/-! ## Constants -/

/-- A hexadecimal numeral, as Cesta reads it: each digit is taken only while
the value read so far is below `2 ^ 60`, so the result fits 64 bits. -/
def hexadecimal (s : String) : Option Nat :=
  if s.isEmpty then none
  else s.toList.foldl (fun acc c => acc.bind fun n =>
    if n < 2 ^ 60 then
      if c.isDigit then some (16 * n + (c.toNat - '0'.toNat))
      else if 'a' ≤ c ∧ c ≤ 'f' then some (16 * n + (c.toNat - 'a'.toNat + 10))
      else if 'A' ≤ c ∧ c ≤ 'F' then some (16 * n + (c.toNat - 'A'.toNat + 10))
      else none
    else none) (some 0)

/-- A sum or product that stays below `2 ^ 64` at every step. -/
def fold64 (f : Nat → Nat → Nat) (acc : Nat) : List Nat → Option Nat
  | [] => some acc
  | x :: xs => if f acc x < 2 ^ 64 then fold64 f (f acc x) xs else none

mutual
/-- A constant expression, as Cesta evaluates it: a decimal integer, an earlier
constant, `(Hex "…")`, `(Pow2 E)`, `(Sum E …)`, `(Times E …)` or `(Minus A B)`,
exact in 64 bits. -/
def evalConst (env : List (String × Nat)) : Atom → Option Nat
  | .symbol s =>
      if s.front.isDigit then (decimal s).bind fun n => if n < 2 ^ 64 then some n else none
      else env.lookup s
  | .list [.symbol "Hex", .text s] => hexadecimal s
  | .list [.symbol "Pow2", e] => (evalConst env e).bind fun n => if n ≤ 63 then some (2 ^ n) else none
  | .list (.symbol "Sum" :: e :: es) => (evalConsts env (e :: es)).bind (fold64 (· + ·) 0)
  | .list (.symbol "Times" :: e :: es) => (evalConsts env (e :: es)).bind (fold64 (· * ·) 1)
  | .list [.symbol "Minus", a, b] =>
      (evalConst env a).bind fun x => (evalConst env b).bind fun y => if y ≤ x then some (x - y) else none
  | _ => none

def evalConsts (env : List (String × Nat)) : List Atom → Option (List Nat)
  | [] => some []
  | e :: es => (evalConst env e).bind fun x => (evalConsts env es).map (x :: ·)
end

/-- `(Const NAME VALUE EXPR) …`: each name is new, and each value is its
expression's, evaluated with the constants before it. -/
def constantsFrom (env : List (String × Nat)) : List Atom → Option (List (String × Nat))
  | [] => some env
  | .list [.symbol "Const", .symbol name, value, e] :: rest =>
      match number value, evalConst env e with
      | some v, some x =>
          if v == x && !(env.any fun c => c.1 == name) then constantsFrom (env ++ [(name, v)]) rest else none
      | _, _ => none
  | _ => none

/-- The optional sections after the requirements, in order: `(From OLD)`,
`(Key FIELD)` and `(Constants …)`. -/
def keyAndConstantsOk (d : Declaration) : List Atom → Bool
  | [] => true
  | [.list (.symbol "Constants" :: cs)] => (constantsFrom [] cs).isSome
  | .list [.symbol "Key", .symbol f] :: rest =>
      (match fieldIndex d f with
        | some j => keyAscending d.code j
        | none => false) &&
      (match rest with
        | [] => true
        | [.list (.symbol "Constants" :: cs)] => (constantsFrom [] cs).isSome
        | _ => false)
  | _ => false

def extrasOk (d : Declaration) : List Atom → Bool
  | .list [.symbol "From", .symbol _] :: rest => keyAndConstantsOk d rest
  | rest => keyAndConstantsOk d rest

def metadataWellFormed (d : Declaration) : List Atom → Bool
  | .list [.symbol "Location", .text discipline] :: .list (.symbol "Aliases" :: aliases) ::
      .list (.symbol "Requires" :: requirements) :: extras =>
      metadataContentsOk d discipline aliases requirements && extrasOk d extras
  | _ => false

/-- The declared key field's position, if the layout declares one. -/
def keyOf (a : Atom) : Option Nat :=
  match decodeLayout a, a with
  | some d, .list (_ :: _ :: _ :: _ :: _ :: metadata) =>
      metadata.findSome? (fun
        | .list [.symbol "Key", .symbol f] => fieldIndex d f
        | _ => none)
  | _, _ => none

/-- The declared constants, with their values. -/
def constantsOf (a : Atom) : List (String × Nat) :=
  match a with
  | .list (_ :: _ :: _ :: _ :: _ :: metadata) =>
      (metadata.findSome? (fun
        | .list (.symbol "Constants" :: cs) => constantsFrom [] cs
        | _ => none)).getD []
  | _ => []

def declarationMetadataOk (a : Atom) : Bool :=
  match decodeLayout a, a with
  | some d, .list (_ :: _ :: _ :: _ :: _ :: metadata) => metadataWellFormed d metadata
  | _, _ => false

/-- What the admission decides of a declared layout. -/
def admitted (a : Atom) : Bool :=
  match decodeLayout a with
  | some d => d.code.wellFormed && arityOk d && declarationMetadataOk a
  | none => false

theorem facts_of_admitted {a : Atom} (h : admitted a = true) :
    ∃ d, decodeLayout a = some d ∧ d.code.Facts := by
  unfold admitted at h
  cases hd : decodeLayout a with
  | none => rw [hd] at h; simp at h
  | some d =>
      rw [hd] at h
      simp only [Bool.and_eq_true] at h
      exact ⟨d, rfl, Code.facts_of_wellFormed h.1.1⟩

theorem metadata_of_admitted {a : Atom} (h : admitted a = true) : declarationMetadataOk a = true := by
  unfold admitted at h
  cases hd : decodeLayout a with
  | none => rw [hd] at h; simp at h
  | some d =>
      rw [hd] at h
      simp only [Bool.and_eq_true] at h
      exact h.2

/-! ## Examples -/

/-- A byte with a flag and a 7-bit count, as Cesta prints it. -/
def byteLayout : Atom :=
  .list [.symbol "cesta-layout/1", .symbol "Byte", .symbol "8",
    .list [.symbol "Fields", .list [.symbol "flag", .text "fact", .text "construction"],
      .list [.symbol "count", .text "value", .text "construction"]],
    .list [.symbol "Leaf", .text "admits",
      .list [.symbol "Place", .symbol "0", .symbol "1", .symbol "0", .symbol "0", .symbol "1"],
      .list [.symbol "Place", .symbol "1", .symbol "7", .symbol "0", .symbol "0", .symbol "127"]],
    .list [.symbol "Location", .text "immutable"], .list [.symbol "Aliases"], .list [.symbol "Requires"]]

example : admitted byteLayout = true := by decide
example : (decodeLayout byteLayout).map (fun d => d.code.encode [1, 5]) = some (some 11) := by decide

/-- A printed layout whose count overlaps the flag is not admitted. -/
example : admitted (.list [.symbol "cesta-layout/1", .symbol "Byte", .symbol "8",
    .list [.symbol "Fields", .list [.symbol "flag", .text "fact", .text "construction"],
      .list [.symbol "count", .text "value", .text "construction"]],
    .list [.symbol "Leaf", .text "admits",
      .list [.symbol "Place", .symbol "0", .symbol "1", .symbol "0", .symbol "0", .symbol "1"],
      .list [.symbol "Place", .symbol "0", .symbol "8", .symbol "0", .symbol "0", .symbol "255"]],
    .list [.symbol "Location", .text "immutable"], .list [.symbol "Aliases"], .list [.symbol "Requires"]]) = false := by
  decide

end Mettapedia.GSLT.LanguageDef.LayoutDeclarations
