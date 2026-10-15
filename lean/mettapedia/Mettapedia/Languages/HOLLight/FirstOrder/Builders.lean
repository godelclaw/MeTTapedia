import Mettapedia.Languages.HOLLight.FirstOrder.Calculus

/-!
# Proofs in HOL Light's first-order calculus, built from the data

For every encoded datum the calculus has a canonical proof that it is well formed, and for
every de Bruijn term a canonical proof of its type, built by the same recursion as the
encoding and as `DBTerm.inferType`. The builders are the constructive half of exactness:
they turn HOL Light's data and its computations into certificates of the calculus.

* `charProof`: a character outside plane zero by the plane rule; in plane zero by the first
  of the five rules whose fixed bit excludes the surrogate block.
* `stringProof`, `nameProof`, and the mutual `tyProof`, `typeOpProof`, `constProof`,
  `sourceProof` with their provenances.
* `nthProof` and `typeProof`: context lookup and type inference.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
open Mettapedia.Languages.OpenTheory

/-- One proof node: the rule, its arguments in formal order, its premise proofs. -/
def proofNode (id : String) (arguments : List Pattern) (children : List RawProof) : RawProof :=
  .node ⟨⟨id⟩, arguments⟩ children

/-! ## Characters, strings and names -/

def bitProof (bit : Nat) : RawProof := proofNode ("hol.wf-bit-" ++ toString bit) [] []

/-- The bit of a character at a position. -/
def charBit (character : Char) (position : Nat) : Nat := character.toNat / 2 ^ position % 2

/-- The five plane-zero rules, as position and fixed bit; one holds off the surrogate block. -/
def planeZeroCases : List (Nat × Nat) := [(15, 0), (14, 0), (13, 1), (12, 0), (11, 0)]

def charProof (character : Char) : RawProof :=
  let plane := character.toNat / 65536
  let positions := (List.range 16).reverse
  if plane ≠ 0 then
    proofNode "hol.wf-char-plane"
      (groundP (encodeUnary plane) :: positions.map fun position => bitP (charBit character position))
      (proofNode ("hol.wf-plane-" ++ toString plane) [] [] ::
        positions.map fun position => bitProof (charBit character position))
  else
    match planeZeroCases.find? fun (position, bit) => charBit character position = bit with
    | some (fixed, _) =>
        let others := positions.filter (· ≠ fixed)
        proofNode ("hol.wf-char-zero-" ++ toString fixed)
          (others.map fun position => bitP (charBit character position))
          (others.map fun position => bitProof (charBit character position))
    | none => proofNode "hol.wf-char-surrogate" [] []

def charsP (characters : List Char) : Pattern := listP (characters.map fun c => groundP (encodeChar c))

def charsProof : List Char → RawProof
  | [] => proofNode "hol.wf-chars-nil" [] []
  | character :: rest =>
      proofNode "hol.wf-chars-cons" [groundP (encodeChar character), charsP rest]
        [charProof character, charsProof rest]

def stringProof (text : String) : RawProof :=
  proofNode "hol.wf-string" [charsP text.toList] [charsProof text.toList]

def stringsP (texts : List String) : Pattern := listP (texts.map fun text => groundP (encodeString text))

def stringsProof : List String → RawProof
  | [] => proofNode "hol.wf-strings-nil" [] []
  | text :: rest =>
      proofNode "hol.wf-strings-cons" [groundP (encodeString text), stringsP rest]
        [stringProof text, stringsProof rest]

def nameProof (name : Name) : RawProof :=
  proofNode "hol.wf-name" [stringsP name.namespaceComponents, groundP (encodeString name.component)]
    [stringsProof name.namespaceComponents, stringProof name.component]

def namesP (names : List Name) : Pattern := listP (names.map fun name => groundP (encodeName name))

def namesProof : List Name → RawProof
  | [] => proofNode "hol.wf-names-nil" [] []
  | name :: rest =>
      proofNode "hol.wf-names-cons" [groundP (encodeName name), namesP rest] [nameProof name, namesProof rest]

/-! ## Types, constants and source terms -/

def tysP (types : List Ty) : Pattern := listP ((encodeTys types).map groundP)

mutual
  def tyProof : Ty → RawProof
    | .var name => proofNode "hol.wf-ty-var" [groundP (encodeName name)] [nameProof name]
    | .op operator arguments =>
        proofNode "hol.wf-ty-op" [groundP (encodeTypeOp operator), tysP arguments]
          [typeOpProof operator, tysProof arguments]

  def tysProof : List Ty → RawProof
    | [] => proofNode "hol.wf-tys-nil" [] []
    | type :: rest =>
        proofNode "hol.wf-tys-cons" [groundP (encodeTy type), tysP rest] [tyProof type, tysProof rest]

  def typeOpProof : TypeOp → RawProof
    | .mk name provenance =>
        proofNode "hol.wf-typeop" [groundP (encodeName name), groundP (encodeTypeOpProvenance provenance)]
          [nameProof name, typeOpProvenanceProof provenance]

  def typeOpProvenanceProof : TypeOpProvenance → RawProof
    | .undefined => proofNode "hol.wf-typeop-undefined" [] []
    | .defined predicate parameters =>
        proofNode "hol.wf-typeop-defined" [groundP (encodeSourceTerm predicate), namesP parameters]
          [sourceProof predicate, namesProof parameters]

  def constProof : Const → RawProof
    | .mk name provenance =>
        proofNode "hol.wf-const" [groundP (encodeName name), groundP (encodeConstProvenance provenance)]
          [nameProof name, constProvenanceProof provenance]

  def constProvenanceProof : ConstProvenance → RawProof
    | .undefined => proofNode "hol.wf-const-undefined" [] []
    | .defined definition =>
        proofNode "hol.wf-const-defined" [groundP (encodeSourceTerm definition)] [sourceProof definition]
    | .abstraction operator =>
        proofNode "hol.wf-const-abstraction" [groundP (encodeTypeOp operator)] [typeOpProof operator]
    | .representation operator =>
        proofNode "hol.wf-const-representation" [groundP (encodeTypeOp operator)] [typeOpProof operator]

  def sourceProof : SourceTerm → RawProof
    | .const constant type =>
        proofNode "hol.wf-source-const" [groundP (encodeConst constant), groundP (encodeTy type)]
          [constProof constant, tyProof type]
    | .var name type =>
        proofNode "hol.wf-source-var" [groundP (encodeName name), groundP (encodeTy type)]
          [nameProof name, tyProof type]
    | .app function argument =>
        proofNode "hol.wf-source-app" [groundP (encodeSourceTerm function), groundP (encodeSourceTerm argument)]
          [sourceProof function, sourceProof argument]
    | .abs name type body =>
        proofNode "hol.wf-source-abs"
          [groundP (encodeName name), groundP (encodeTy type), groundP (encodeSourceTerm body)]
          [nameProof name, tyProof type, sourceProof body]
end

/-! ## Context lookup and type inference -/

def contextP (context : List Ty) : Pattern := listP (context.map fun type => groundP (encodeTy type))

/-- Context lookup at a unary index, the context listed with its tail. -/
def nthProofAt : List Ty → Nat → RawProof
  | [], _ => proofNode "hol.nth-out-of-range" [] []
  | type :: rest, 0 => proofNode "hol.nth-zero" [groundP (encodeTy type), contextP rest] []
  | type :: rest, index + 1 =>
      proofNode "hol.nth-succ"
        [groundP (encodeTy type), contextP rest, groundP (encodeUnary index),
          groundP (encodeTy ((rest[index]?).getD type))]
        [nthProofAt rest index]

/-- The canonical proof of `TypeOf(context, term, type)`, its types read off by inference. -/
def typeProof (context : List Ty) : DBTerm → RawProof
  | .const constant type =>
      proofNode "hol.type-const" [groundP (encodeConst constant), groundP (encodeTy type), contextP context]
        [constProof constant, tyProof type]
  | .free sourceVar =>
      proofNode "hol.type-free" [groundP (encodeName sourceVar.name), groundP (encodeTy sourceVar.ty), contextP context]
        [nameProof sourceVar.name, tyProof sourceVar.ty]
  | .bound index =>
      proofNode "hol.type-bound"
        [groundP (encodeUnary index), groundP (encodeTy ((context[index]?).getD (.var (Name.global "")))),
          contextP context]
        [nthProofAt context index]
  | .app function argument =>
      let argumentType := ((argument.inferType context).getD (.var (Name.global "")))
      let resultType := match (function.inferType context).bind Ty.destFunction? with
        | some (_, codomain) => codomain
        | none => .var (Name.global "")
      proofNode "hol.type-app"
        [groundP (encodeTerm function), groundP (encodeTerm argument), groundP (encodeTy argumentType),
          groundP (encodeTy resultType), contextP context]
        [typeProof context function, typeProof context argument]
  | .abs domain body =>
      let bodyType := (body.inferType (domain :: context)).getD (.var (Name.global ""))
      proofNode "hol.type-abs"
        [groundP (encodeTy domain), groundP (encodeTerm body), groundP (encodeTy bodyType), contextP context]
        [tyProof domain, typeProof (domain :: context) body]

end Mettapedia.Languages.HOLLight.FirstOrder
