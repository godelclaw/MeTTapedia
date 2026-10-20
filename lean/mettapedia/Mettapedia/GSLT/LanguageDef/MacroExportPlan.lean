/-!
# The readable export of a macro use, as a function of its source

Cesta writes a macro use as readable C: one block that acquires each evaluated
argument once, in declared order, into a named local, checks the local's exact
type, and then runs the module template with those locals in place of the
arguments. This file states that lowering as a total function of the source
data: the rule's contract and template exactly as the module declares them,
the arguments exactly as written, and the names the exporter chose.

`lower` is the lowering itself, not a reconstruction of one export. An export
is admitted when the target Cesta actually handed to its printer equals
`fill (lower rule use)`; `checkUse` decides that equality on the recorded
data, so a target that differs anywhere, with every name right, is refused.

The meaning of the lowered structure is given separately by the semantics in
`MacroExportStateful`. This file is syntax: atoms, the contract decoder, the
lowering and the filling of written arguments.
-/

namespace Mettapedia.GSLT.LanguageDef.MacroExportPlan

set_option autoImplicit false

/-! ## Atoms as Cesta writes them -/

inductive Atom where
  | symbol (name : String)
  | text (bytes : String)
  | list (items : List Atom)
  deriving Repr, Inhabited

/-- An atom as the token stream Cesta prints: equality of atoms is equality of
these streams. -/
inductive Token where
  | openList | closeList
  | symbol (name : String)
  | text (bytes : String)
  deriving Repr, DecidableEq

mutual
  def Atom.tokens : Atom → List Token
    | .symbol s => [.symbol s]
    | .text s => [.text s]
    | .list items => .openList :: Atom.tokensMany items ++ [.closeList]
  def Atom.tokensMany : List Atom → List Token
    | [] => []
    | a :: rest => Atom.tokens a ++ Atom.tokensMany rest
end

/-- Atoms with the template's slot markers and the lowering's own leaves. -/
inductive Marked where
  | symbol (name : String)
  | text (bytes : String)
  | list (items : List Marked)
  /-- `(Argument x)` of a template. -/
  | arg (slot : Nat)
  /-- `(TypeArgument x)` of a template. -/
  | typeArg (slot : Nat)
  /-- `(LocalRef space x)` of a template. -/
  | localRef (slot : Nat)
  /-- A name the lowering declares. -/
  | name (spelling : String)
  /-- An argument exactly as written at the use. -/
  | operand (slot : Nat)
  /-- `X`, for an argument written `(* X)`. -/
  | inner (slot : Nat)
  deriving Repr, Inhabited

/-! ## The contract -/

inductive Category where
  | value | addressable | modifiable | syntax
  deriving Repr, DecidableEq

structure Argument where
  name : String
  category : Category
  once : Bool
  ctype : Marked
  deriving Repr

structure Rule where
  label : String
  head : String
  expression : Bool
  gnu : Bool
  arguments : List Argument
  result : Marked
  locals : List (String × String)
  body : Marked
  deriving Repr

def indexOf (names : List String) (x : String) : Option Nat := names.findIdx? (· = x)

mutual
  /-- Template markers: arguments and locals by declared identity, ports by
  key. Definition-site references and captures are outside the readable
  fragment and are refused. -/
  def mark (args : List String) (locals : List (String × String)) (ports : List (String × String)) :
      Atom → Option Marked
    | .symbol s => some (.symbol s)
    | .text s => some (.text s)
    | .list [.symbol "Argument", .symbol x] => (indexOf args x).map .arg
    | .list [.symbol "TypeArgument", .symbol x] => (indexOf args x).map .typeArg
    | .list [.symbol "LocalRef", .text space, .symbol x] =>
        (locals.findIdx? (· = (x, space))).map .localRef
    | .list [.symbol "CompilerRef", .symbol p] => (ports.lookup p).map .symbol
    | .list (.symbol "DefinitionRef" :: _) => none
    | .list (.symbol "Capture" :: _) => none
    | .list items => (markMany args locals ports items).map .list
  def markMany (args : List String) (locals : List (String × String)) (ports : List (String × String)) :
      List Atom → Option (List Marked)
    | [] => some []
    | a :: rest => do
        let m ← mark args locals ports a
        let ms ← markMany args locals ports rest
        pure (m :: ms)
end


/-- The fields of a list headed by a symbol. -/
def fields (head : String) : Atom → Option (List Atom)
  | .list (.symbol h :: rest) => if h = head then some rest else none
  | _ => none

/-- The first item of a list headed by `head`. -/
def find? (head : String) : List Atom → Option (List Atom)
  | [] => none
  | a :: rest => match fields head a with
    | some found => some found
    | none => find? head rest

def category : String → Option Category
  | "value" => some .value
  | "addressable" => some .addressable
  | "addressable-modifiable" => some .modifiable
  | "syntax" => some .syntax
  | _ => none

def argName : Atom → Option String
  | .list [.symbol "Arg", .symbol x, _, _, _] => some x
  | _ => none

def port : Atom → Option (String × String)
  | .list [.symbol "CompilerBuiltin", .symbol key, .text name] => some (key, name)
  | _ => none

def localOf : Atom → Option (String × String)
  | .list [.symbol "Local", .symbol x, .text space] => some (x, space)
  | _ => none

def argument (args : List String) (ports : List (String × String)) : Atom → Option Argument
  | .list [.symbol "Arg", .symbol x, ctype, .text cat, .list (.symbol "Evaluation" :: .text policy :: _)] => do
      let c ← category cat
      let t ← mark args [] ports ctype
      pure { name := x, category := c, once := policy == "once", ctype := t }
  | _ => none

/-- A rule record of `cesta check-macros`, decoded. -/
def decodeRule : Atom → Option Rule
  | .list [.symbol "rule", .text label, .text head, .text _,
      .list (.symbol "Macro" :: .text _ :: contract)] => do
      let profile ← find? "Profile" contract
      let gnu ← match profile with
        | [.text "gnu11"] => some true
        | [.text "c11"] => some false
        | _ => none
      let ports := ((find? "Ports" contract).getD []).filterMap port
      let argAtoms ← find? "Arguments" contract
      let args ← argAtoms.mapM argName
      let arguments ← argAtoms.mapM (argument args ports)
      let result ← find? "Result" contract
      let (resultType, expression) ← match result with
        | [ctype, .text "value"] => (mark args [] ports ctype).map (·, true)
        | [ctype, .text "statement"] => (mark args [] ports ctype).map (·, false)
        | _ => none
      let localAtoms ← find? "Locals" contract
      let locals ← localAtoms.mapM localOf
      let template ← find? "Template" contract
      let body ← match template with
        | [b] => mark args locals ports b
        | _ => none
      pure { label, head, expression, gnu, arguments, result := resultType, locals, body }
  | _ => none

/-! ## Instantiation and the exporter's rewrites -/

mutual
  /-- Arguments and type arguments by the slot map, locals by their chosen names. -/
  def instantiate (slots : Nat → Marked) (locals : Nat → String) : Marked → Marked
    | .arg i => slots i
    | .typeArg i => slots i
    | .localRef j => .name (locals j)
    | .list items => .list (instantiateMany slots locals items)
    | m => m
  def instantiateMany (slots : Nat → Marked) (locals : Nat → String) : List Marked → List Marked
    | [] => []
    | m :: rest => instantiate slots locals m :: instantiateMany slots locals rest
end

/-- `&*E` is `E` without evaluating either operator (C11 6.5.3.2). -/
def addressOfObjectNode : Marked → Marked
  | .list [.symbol "&", .list [.symbol "*", x]] => x
  | m => m

mutual
  def addressOfObject : Marked → Marked
    | .list items => addressOfObjectNode (.list (addressOfObjectMany items))
    | m => m
  def addressOfObjectMany : List Marked → List Marked
    | [] => []
    | m :: rest => addressOfObject m :: addressOfObjectMany rest
end

def effects : List String :=
  ["=", "+=", "-=", "*=", "/=", "%=", "<<=", ">>=", "&=", "^=", "|=",
   "++", "--", "post++", "post--", "call", "block"]

mutual
  /-- An expression whose second, unevaluated copy in `_Generic` is harmless.
  An argument as written may have effects; the head of a list is never
  examined except as an operator. -/
  def effectFree : Marked → Bool
    | .list (.symbol h :: rest) => !(effects.contains h) && effectFreeMany rest
    | .list (_ :: rest) => effectFreeMany rest
    | .operand _ => false
    | .inner _ => false
    | _ => true
  def effectFreeMany : List Marked → Bool
    | [] => true
    | m :: rest => effectFree m && effectFreeMany rest
end

/-! ## Filling the written arguments -/

mutual
  def fill (written : List Atom) : Marked → Option Atom
    | .symbol s => some (.symbol s)
    | .text s => some (.text s)
    | .name s => some (.symbol s)
    | .operand i => written[i]?
    | .inner i => match written[i]? with
      | some (.list [.symbol "*", x]) => some x
      | _ => none
    | .list items => (fillMany written items).map .list
    | _ => none
  def fillMany (written : List Atom) : List Marked → Option (List Atom)
    | [] => some []
    | m :: rest => do
        let a ← fill written m
        let as ← fillMany written rest
        pure (a :: as)
end

/-! ## The lowering -/

/-- A symbol or a declared name: what C sees as a symbol atom. -/
def spelling? : Marked → Option String
  | .symbol s => some s
  | .name s => some s
  | _ => none

mutual
  /-- `TypeSlot` replaced by a declared name; written arguments kept. -/
  def withDeclarator (alias : String) : Marked → Marked
    | .symbol "TypeSlot" => .name alias
    | .list items => .list (withDeclaratorMany alias items)
    | m => m
  def withDeclaratorMany (alias : String) : List Marked → List Marked
    | [] => []
    | m :: rest => withDeclarator alias m :: withDeclaratorMany alias rest
end

def stars : Nat → String
  | 1 => "*"
  | 2 => "**"
  | _ => "***"

def starDepth : String → Nat
  | "*" => 1
  | "**" => 2
  | "***" => 3
  | _ => 0

/-- The type name an exact `_Generic` association uses for an instantiated
CType: pointer chains inline, other declarators through a named typedef. -/
def admittedType (ctype : Marked) (place : Bool) (supply : List String) :
    Option (Marked × Option Marked × List String) :=
  match ctype with
  | .list [.symbol "CType", specs] =>
      some (if place then .list [specs, .symbol "*"] else specs, none, supply)
  | .list [.symbol "CType", specs, decl] =>
      let depth := match decl with
        | .list [.symbol s, .symbol "TypeSlot"] => starDepth s
        | _ => 0
      let extra := if place then 1 else 0
      if depth ≠ 0 ∧ depth + extra ≤ 3 then
        some (.list [specs, .symbol (stars (depth + extra))], none, supply)
      else match supply with
        | alias :: rest =>
            let item := Marked.list [.symbol "typedef", specs, withDeclarator alias decl]
            some (if place then .list [.name alias, .symbol "*"] else .name alias, some item, rest)
        | [] => none
  | _ => none

def admission (subject type : Marked) (message : String) : Marked :=
  .list [.symbol "_Static_assert",
         .list [.symbol "_Generic", subject, .list [type, .symbol "1"], .list [.symbol "default", .symbol "0"]],
         .text ("\"" ++ message ++ "\"")]

/-- A local declared with exactly the result type: its value needs no check. -/
def declaresResult (written : List Atom) (declared item : Marked) (others : List Marked) : Bool :=
  match spelling? item, declared with
  | some s, .list [.symbol "CType", specs] =>
      others.any fun d => match d with
        | .list (.symbol "var" :: dspecs :: dname :: _) =>
            spelling? dname == some s &&
              match fill written dspecs, fill written specs with
              | some a, some b => a.tokens == b.tokens
              | _, _ => false
        | _ => false
  | _, _ => false

/-- Acquire the evaluated arguments in declared order. Returns the acquisition
items, the slot map and the remaining names. -/
def acquire (rule : Rule) (written : List Atom) :
    List (Nat × Argument) → List String → Option (List Marked × List (Nat × Marked) × List String)
  | [], supply => some ([], [], supply)
  | (i, a) :: rest, supply =>
      if a.category = .syntax then do
        let (items, slots, supply) ← acquire rule written rest supply
        pure (items, (i, .operand i) :: slots, supply)
      else do
        if !a.once then none
        let place := a.category ≠ .value
        let (n, supply) ← match supply with
          | n :: s => some (n, s)
          | [] => none
        let initial := if place then
            match written[i]? with
            | some (.list [.symbol "*", _]) => Marked.inner i
            | _ => .list [.symbol "&", .operand i]
          else .operand i
        let declaration := Marked.list [.symbol "var", .symbol "__auto_type", .name n, initial]
        let typed := instantiate (fun k => .operand k) (fun _ => "") a.ctype
        let (type, typedefItem, supply) ← admittedType typed place supply
        let check := admission (.name n) type (rule.head ++ " argument " ++ a.name ++ " has its declared type")
        let here := [declaration] ++ typedefItem.toList ++ [check]
        let (items, slots, supply) ← acquire rule written rest supply
        pure (here ++ items, (i, if place then .list [.symbol "*", .name n] else .name n) :: slots, supply)

/-- The body items after the acquisitions: the template, and for a value its
declared-type check. -/
def bodyItems (rule : Rule) (written : List Atom) (declared : Marked) (all : List Marked) :
    List Marked → List String → Option (List Marked × List String)
  | [], supply => some ([], supply)
  | [last], supply =>
      if rule.expression then
        if declaresResult written declared last (all.dropLast) then some ([last], supply)
        else do
          let (value, temporary, supply) ←
            if spelling? last == none && !effectFree last then
              match supply with
              | r :: s => some (Marked.name r, [Marked.list [.symbol "var", .symbol "__auto_type", .name r, last]], s)
              | [] => none
            else some (last, [], supply)
          let (type, typedefItem, supply) ← admittedType declared false supply
          pure (temporary ++ typedefItem.toList ++
                [admission value type (rule.head ++ " result has its declared type"), value], supply)
      else some ([last], supply)
  | item :: rest, supply => do
      let (items, supply) ← bodyItems rule written declared all rest supply
      pure (item :: items, supply)

def blockOf (items : List Marked) : Marked := .list (.symbol "block" :: items)

/-- A template body as block items: a block's own items, or the body alone. -/
def bodyView : Marked → Bool × List Marked
  | .list (.symbol "block" :: xs) => (true, xs)
  | b => (false, [b])

/-- The exported block: the acquisitions, then the template items; a block
template keeps its own scope after acquisitions. -/
def assemble (acquired template : List Marked) (isBlock : Bool) : Marked :=
  let acquiredCount := if template = [] then 0 else acquired.length
  let all := acquired ++ template
  if acquiredCount = 0 then blockOf all
  else if !isBlock then blockOf all
  else blockOf (acquired ++ [blockOf template])

/-- The block a use exports to, from the rule, the written arguments and the
exporter's names in the order it chose them. All names must be used. -/
def lower (rule : Rule) (written : List Atom) (supply : List String) : Option Marked := do
  if !rule.gnu then none
  if written.length ≠ rule.arguments.length then none
  let (acquired, slotList, supply) ← acquire rule written (List.zip (List.range rule.arguments.length) rule.arguments) supply
  let slots := fun k => (slotList.lookup k).getD (.operand k)
  let (localNames, supply) ←
    if rule.locals.length ≤ supply.length then some (supply.take rule.locals.length, supply.drop rule.locals.length)
    else none
  let body := addressOfObject (instantiate slots (fun j => localNames.getD j "") rule.body)
  let (isBlock, items) := bodyView body
  let declared := instantiate slots (fun j => localNames.getD j "") rule.result
  let (template, supply) ← bodyItems rule written declared items items supply
  if supply ≠ [] then none
  pure (assemble acquired template isBlock)

/-! ## Admission of a recorded use -/

/-- A use record of `cesta export-c --plan`. -/
structure Use where
  label : String
  written : List Atom
  picked : List String
  expression : Bool
  target : Atom

def decodeUse : Atom → Option Use
  | .list [.symbol "use", .symbol "cesta-export-plan/2", .list [.symbol "rule", .text _, .text _, .text label],
      .list (.symbol "arguments" :: written), .list (.symbol "acquired" :: _), .list (.symbol "locals" :: _),
      .list (.symbol "picked" :: picked), .list [.symbol "position", .symbol position], .list [.symbol "target", target]] => do
      let names ← picked.mapM fun a => match a with
        | .text s => some s
        | _ => none
      let expression ← match position with
        | "expression" => some true
        | "statement" => some false
        | _ => none
      pure { label, written, picked := names, expression, target }
  | _ => none

/-- The recorded target is exactly the lowering of its source. -/
def checkUse (ruleAtom useAtom : Atom) : Bool :=
  match decodeRule ruleAtom, decodeUse useAtom with
  | some rule, some use =>
      rule.label == use.label && rule.expression == use.expression &&
        match lower rule use.written use.picked with
        | some lowered => match fill use.written lowered with
          | some atom => atom.tokens == use.target.tokens
          | none => false
        | none => false
  | _, _ => false

end Mettapedia.GSLT.LanguageDef.MacroExportPlan
