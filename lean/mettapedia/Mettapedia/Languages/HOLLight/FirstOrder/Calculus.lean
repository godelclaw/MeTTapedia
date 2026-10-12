import Mettapedia.Languages.HOLLight.FirstOrder.Encoding
import Mettapedia.Languages.MM0.Translation.CalculusSimulation

/-!
# HOL Light's kernel as a first-order calculus

The judgment `hol.Thm(H, c)` says that the sequent with the sorted hypothesis list `H` and the
conclusion `c` is derivable. Its rules are HOL Light's inference operations, written over the
labeled-tree encoding of the syntax. Every computation an operation performs is a premise of
an auxiliary judgment with its own rules, so no rule has a side condition:

* `hol.Nth` and `hol.TypeOf`: de Bruijn type inference, `DBTerm.inferType`;
* `hol.ToDB` with `hol.BoundIndex` and `hol.NotBound`: `SourceTerm.toDB`;
* `hol.NotFree` and `hol.NotFreeAll`: absence of a free variable, `DBTerm.hasFree`;
* `hol.Close`: `DBTerm.closeFreeAt`; `hol.Instantiate`: `DBTerm.instantiateAt`;
* `hol.Union` and `hol.Erase` on strictly increasing lists: `Finset` union and erase;
* `hol.Neq`: the structural order of trees in either direction (`LabeledTreeOrder`);
* `hol.WfName`, `hol.WfTy`, `hol.WfConst`, `hol.WfSource` and their parts: well-formed data,
  exactly the encodings. Every rule that takes a datum from its arguments rather than from a
  premise checks it, so a derivation never handles a pattern that encodes nothing.

Instantiation has its own judgments:

* `hol.VarType`, `hol.TyAct` and `hol.TermTyAct`: the first-match type action
  `SourceSubstitution.typeAction`, on types and through every type annotation of a term;
* `hol.AdmitTm`: admission of term maplets, each replacement read from its source term;
  `hol.TmLookup`, `hol.TmNoKey` and `hol.TmApply`: the first-match term action of the raw
  term table;
* `hol.Insert` and `hol.Sort`: the image of a hypothesis set, sorted without duplicates.

The rules for `hol.Thm` are the ten inference operations of `HOLLight.Rules`, REFL, ASSUME,
TRANS, MK_COMB, ABS, BETA, EQ_MP, DEDUCT_ANTISYM_RULE, INST and INST_TYPE, and one rule per
sequent of a finite axiom list.

`holCalculus axioms` is valid and first-order for the empty axiom list (`holCalculus_valid`,
`holCalculus_firstOrder`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.RuleSchemaArityProjection
open Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.MM0.Translation.CalculusSimulation (firstOrderCheck)

/-! ## Patterns of the encoded syntax -/

/-- A tree node with the given label and children, as a pattern. -/
def treeP (label : Nat) (children : List Pattern) : Pattern := nodeP (numeralP label) (listP children)

def mv (name : String) : Pattern := .fvar name

/-- An encoded tree as a ground pattern. -/
def groundP (tree : LabeledTree) : Pattern := tree.toPattern

def functionOpP : Pattern := groundP (encodeTypeOp TypeOp.function)
def boolP : Pattern := groundP (encodeTy Ty.bool)
def equalityConstP : Pattern := groundP (encodeConst Const.equality)

def functionTyP (domain codomain : Pattern) : Pattern :=
  treeP tyOpLabel [functionOpP, treeP listLabel [domain, codomain]]

def constTermP (constant type : Pattern) : Pattern := treeP termConstLabel [constant, type]
def freeTermP (name type : Pattern) : Pattern := treeP termFreeLabel [name, type]
def boundTermP (index : Pattern) : Pattern := treeP termBoundLabel [index]
def appTermP (function argument : Pattern) : Pattern := treeP termAppLabel [function, argument]
def absTermP (type body : Pattern) : Pattern := treeP termAbsLabel [type, body]

/-- `equalityDB` at an operand type. -/
def equalityTermP (type left right : Pattern) : Pattern :=
  appTermP (appTermP (constTermP equalityConstP (functionTyP type (functionTyP type boolP))) left) right

def unaryZeroP : Pattern := treeP unaryZeroLabel []
def unarySuccP (count : Pattern) : Pattern := treeP unarySuccLabel [count]

def sourceConstP (constant type : Pattern) : Pattern := treeP sourceConstLabel [constant, type]
def sourceVarP (name type : Pattern) : Pattern := treeP sourceVarLabel [name, type]
def sourceAppP (function argument : Pattern) : Pattern := treeP sourceAppLabel [function, argument]
def sourceAbsP (name type body : Pattern) : Pattern := treeP sourceAbsLabel [name, type, body]

def tyVarP (name : Pattern) : Pattern := treeP tyVarLabel [name]
/-- A type operator applied to the argument list `arguments` (the list's children). -/
def tyOpP (operator arguments : Pattern) : Pattern :=
  treeP tyOpLabel [operator, nodeP (numeralP listLabel) arguments]
def typeMapletP (replacement key : Pattern) : Pattern := treeP typeMapletLabel [replacement, key]
def termMapletP (source key : Pattern) : Pattern := treeP termMapletLabel [source, key]
def pairP (key value : Pattern) : Pattern := treeP pairLabel [key, value]
def bitP (bit : Nat) : Pattern := treeP bit []
def listNodeP (items : Pattern) : Pattern := nodeP (numeralP listLabel) items

/-! ## Judgments -/

def thmJ (hypotheses conclusion : Pattern) : Pattern := .apply "hol.Thm" [hypotheses, conclusion]
def neqJ (first second : Pattern) : Pattern := .apply "hol.Neq" [first, second]
def nthJ (list index value : Pattern) : Pattern := .apply "hol.Nth" [list, index, value]
def typeOfJ (context term type : Pattern) : Pattern := .apply "hol.TypeOf" [context, term, type]
def boundIndexJ (binders needle index : Pattern) : Pattern :=
  .apply "hol.BoundIndex" [binders, needle, index]
def notBoundJ (binders needle : Pattern) : Pattern := .apply "hol.NotBound" [binders, needle]
def toDBJ (binders source term : Pattern) : Pattern := .apply "hol.ToDB" [binders, source, term]
def notFreeJ (needle term : Pattern) : Pattern := .apply "hol.NotFree" [needle, term]
def notFreeAllJ (needle terms : Pattern) : Pattern := .apply "hol.NotFreeAll" [needle, terms]
def closeJ (needle depth term result : Pattern) : Pattern :=
  .apply "hol.Close" [needle, depth, term, result]
def instantiateJ (replacement depth term result : Pattern) : Pattern :=
  .apply "hol.Instantiate" [replacement, depth, term, result]
def unionJ (first second result : Pattern) : Pattern := .apply "hol.Union" [first, second, result]
def eraseJ (term terms result : Pattern) : Pattern := .apply "hol.Erase" [term, terms, result]
def insertJ (term terms result : Pattern) : Pattern := .apply "hol.Insert" [term, terms, result]
def sortJ (terms result : Pattern) : Pattern := .apply "hol.Sort" [terms, result]
def varTypeJ (entries name type : Pattern) : Pattern := .apply "hol.VarType" [entries, name, type]
def tyActJ (entries type result : Pattern) : Pattern := .apply "hol.TyAct" [entries, type, result]
def tyActListJ (entries types results : Pattern) : Pattern :=
  .apply "hol.TyActList" [entries, types, results]
def termTyActJ (entries term result : Pattern) : Pattern := .apply "hol.TermTyAct" [entries, term, result]
def termTyActListJ (entries terms results : Pattern) : Pattern :=
  .apply "hol.TermTyActList" [entries, terms, results]
def admitTmJ (maplets table : Pattern) : Pattern := .apply "hol.AdmitTm" [maplets, table]
def tmLookupJ (table needle value : Pattern) : Pattern := .apply "hol.TmLookup" [table, needle, value]
def tmNoKeyJ (table needle : Pattern) : Pattern := .apply "hol.TmNoKey" [table, needle]
def tmApplyJ (table term result : Pattern) : Pattern := .apply "hol.TmApply" [table, term, result]
def tmApplyListJ (table terms results : Pattern) : Pattern :=
  .apply "hol.TmApplyList" [table, terms, results]
def wfJ (kind : String) (datum : Pattern) : Pattern := .apply ("hol.Wf" ++ kind) [datum]

def holJudgments : List JudgmentDecl :=
  [{ head := "hol.Thm", arity := 2 }, { head := "hol.Neq", arity := 2 },
    { head := "hol.Nth", arity := 3 }, { head := "hol.TypeOf", arity := 3 },
    { head := "hol.BoundIndex", arity := 3 }, { head := "hol.NotBound", arity := 2 },
    { head := "hol.ToDB", arity := 3 }, { head := "hol.NotFree", arity := 2 },
    { head := "hol.NotFreeAll", arity := 2 }, { head := "hol.Close", arity := 4 },
    { head := "hol.Instantiate", arity := 4 }, { head := "hol.Union", arity := 3 },
    { head := "hol.Erase", arity := 3 }, { head := "hol.Insert", arity := 3 },
    { head := "hol.Sort", arity := 2 }, { head := "hol.VarType", arity := 3 },
    { head := "hol.TyAct", arity := 3 }, { head := "hol.TyActList", arity := 3 },
    { head := "hol.TermTyAct", arity := 3 }, { head := "hol.TermTyActList", arity := 3 },
    { head := "hol.AdmitTm", arity := 2 }, { head := "hol.TmLookup", arity := 3 },
    { head := "hol.TmNoKey", arity := 2 }, { head := "hol.TmApply", arity := 3 },
    { head := "hol.TmApplyList", arity := 3 }] ++
  (["Bit", "Plane", "Char", "Chars", "String", "Strings", "Name", "Names", "Ty", "Tys", "TypeOp",
      "TypeOpProv", "Const", "ConstProv", "Source", "TypeMaplets"].map fun kind =>
    ({ head := "hol.Wf" ++ kind, arity := 1 } : JudgmentDecl))

/-! ## Rules -/

/-- A rule over the named metavariables, all of arity zero. -/
def rule (id : String) (names : List String) (premises : List Pattern) (conclusion : Pattern) :
    RuleSchema where
  id := ⟨id⟩
  metavariables := names.map fun name => (name, 0)
  premises := premises
  conclusion := conclusion

/-- Disequality is the tree order in either direction. -/
def neqRules : List RuleSchema :=
  [rule "hol.neq-lt" ["x", "y"] [ltJudgment (mv "x") (mv "y")] (neqJ (mv "x") (mv "y")),
    rule "hol.neq-gt" ["x", "y"] [ltJudgment (mv "y") (mv "x")] (neqJ (mv "x") (mv "y"))]

/-- The bit metavariables of a character, most significant first. -/
def bitNames : List String := (List.range 16).reverse.map fun position => "b" ++ toString position

/-- A character with the given plane and bits, most significant first. -/
def charP (plane : Pattern) (bits : List Pattern) : Pattern := treeP charLabel (plane :: bits)

/-- A plane-zero character with bit `position` fixed to `bit`, every other bit checked. -/
def planeZeroRule (position bit : Nat) : RuleSchema :=
  let names := bitNames.filter (· ≠ "b" ++ toString position)
  rule ("hol.wf-char-zero-" ++ toString position) names (names.map fun name => wfJ "Bit" (mv name))
    (wfJ "Char" (charP (groundP (encodeUnary 0))
      ((List.range 16).reverse.map fun index => if index = position then bitP bit else mv ("b" ++ toString index))))

/-- Bits, and the planes above zero. -/
def bitPlaneRules : List RuleSchema :=
  [rule "hol.wf-bit-0" [] [] (wfJ "Bit" (bitP 0)),
    rule "hol.wf-bit-1" [] [] (wfJ "Bit" (bitP 1))] ++
  ((List.range 16).map fun plane =>
    rule ("hol.wf-plane-" ++ toString (plane + 1)) [] [] (wfJ "Plane" (groundP (encodeUnary (plane + 1)))))

/-- Characters. Outside plane zero every position is valid; in plane zero the surrogate
block, top bits `11011`, is excluded by five rules, each fixing one of those bits. -/
def charRules : List RuleSchema :=
  [rule "hol.wf-char-plane" ("p" :: bitNames) (wfJ "Plane" (mv "p") :: bitNames.map fun name => wfJ "Bit" (mv name))
      (wfJ "Char" (charP (mv "p") (bitNames.map mv))),
    planeZeroRule 15 0, planeZeroRule 14 0, planeZeroRule 13 1, planeZeroRule 12 0, planeZeroRule 11 0]

/-- Strings and names. -/
def textRules : List RuleSchema :=
  [rule "hol.wf-chars-nil" [] [] (wfJ "Chars" nilP),
    rule "hol.wf-chars-cons" ["c", "cs"] [wfJ "Char" (mv "c"), wfJ "Chars" (mv "cs")]
      (wfJ "Chars" (consP (mv "c") (mv "cs"))),
    rule "hol.wf-string" ["cs"] [wfJ "Chars" (mv "cs")] (wfJ "String" (nodeP (numeralP stringLabel) (mv "cs"))),
    rule "hol.wf-strings-nil" [] [] (wfJ "Strings" nilP),
    rule "hol.wf-strings-cons" ["s", "ss"] [wfJ "String" (mv "s"), wfJ "Strings" (mv "ss")]
      (wfJ "Strings" (consP (mv "s") (mv "ss"))),
    rule "hol.wf-name" ["ss", "s"] [wfJ "Strings" (mv "ss"), wfJ "String" (mv "s")]
      (wfJ "Name" (treeP nameLabel [listNodeP (mv "ss"), mv "s"])),
    rule "hol.wf-names-nil" [] [] (wfJ "Names" nilP),
    rule "hol.wf-names-cons" ["x", "xs"] [wfJ "Name" (mv "x"), wfJ "Names" (mv "xs")]
      (wfJ "Names" (consP (mv "x") (mv "xs")))]

/-- Types, constants, source terms and type maplets. -/
def syntaxRules : List RuleSchema :=
  [rule "hol.wf-ty-var" ["x"] [wfJ "Name" (mv "x")] (wfJ "Ty" (tyVarP (mv "x"))),
    rule "hol.wf-ty-op" ["o", "as"] [wfJ "TypeOp" (mv "o"), wfJ "Tys" (mv "as")] (wfJ "Ty" (tyOpP (mv "o") (mv "as"))),
    rule "hol.wf-tys-nil" [] [] (wfJ "Tys" nilP),
    rule "hol.wf-tys-cons" ["a", "as"] [wfJ "Ty" (mv "a"), wfJ "Tys" (mv "as")] (wfJ "Tys" (consP (mv "a") (mv "as"))),
    rule "hol.wf-typeop" ["x", "p"] [wfJ "Name" (mv "x"), wfJ "TypeOpProv" (mv "p")]
      (wfJ "TypeOp" (treeP typeOpLabel [mv "x", mv "p"])),
    rule "hol.wf-typeop-undefined" [] [] (wfJ "TypeOpProv" (treeP typeOpUndefinedLabel [])),
    rule "hol.wf-typeop-defined" ["s", "xs"] [wfJ "Source" (mv "s"), wfJ "Names" (mv "xs")]
      (wfJ "TypeOpProv" (treeP typeOpDefinedLabel [mv "s", listNodeP (mv "xs")])),
    rule "hol.wf-const" ["x", "p"] [wfJ "Name" (mv "x"), wfJ "ConstProv" (mv "p")]
      (wfJ "Const" (treeP constLabel [mv "x", mv "p"])),
    rule "hol.wf-const-undefined" [] [] (wfJ "ConstProv" (treeP constUndefinedLabel [])),
    rule "hol.wf-const-defined" ["s"] [wfJ "Source" (mv "s")] (wfJ "ConstProv" (treeP constDefinedLabel [mv "s"])),
    rule "hol.wf-const-abstraction" ["o"] [wfJ "TypeOp" (mv "o")]
      (wfJ "ConstProv" (treeP constAbstractionLabel [mv "o"])),
    rule "hol.wf-const-representation" ["o"] [wfJ "TypeOp" (mv "o")]
      (wfJ "ConstProv" (treeP constRepresentationLabel [mv "o"])),
    rule "hol.wf-source-const" ["c", "a"] [wfJ "Const" (mv "c"), wfJ "Ty" (mv "a")]
      (wfJ "Source" (sourceConstP (mv "c") (mv "a"))),
    rule "hol.wf-source-var" ["x", "a"] [wfJ "Name" (mv "x"), wfJ "Ty" (mv "a")]
      (wfJ "Source" (sourceVarP (mv "x") (mv "a"))),
    rule "hol.wf-source-app" ["f", "e"] [wfJ "Source" (mv "f"), wfJ "Source" (mv "e")]
      (wfJ "Source" (sourceAppP (mv "f") (mv "e"))),
    rule "hol.wf-source-abs" ["x", "a", "t"] [wfJ "Name" (mv "x"), wfJ "Ty" (mv "a"), wfJ "Source" (mv "t")]
      (wfJ "Source" (sourceAbsP (mv "x") (mv "a") (mv "t"))),
    rule "hol.wf-typemaplets-nil" [] [] (wfJ "TypeMaplets" nilP),
    rule "hol.wf-typemaplets-cons" ["r", "k", "rest"]
      [wfJ "Ty" (mv "r"), wfJ "Ty" (mv "k"), wfJ "TypeMaplets" (mv "rest")]
      (wfJ "TypeMaplets" (consP (typeMapletP (mv "r") (mv "k")) (mv "rest")))]

/-- Well-formed data: exactly the encodings. -/
def wellFormedRules : List RuleSchema := bitPlaneRules ++ charRules ++ textRules ++ syntaxRules

/-- Context lookup by a unary index. -/
def nthRules : List RuleSchema :=
  [rule "hol.nth-zero" ["t", "ts"] [] (nthJ (consP (mv "t") (mv "ts")) unaryZeroP (mv "t")),
    rule "hol.nth-succ" ["t", "ts", "n", "u"] [nthJ (mv "ts") (mv "n") (mv "u")]
      (nthJ (consP (mv "t") (mv "ts")) (unarySuccP (mv "n")) (mv "u"))]

/-- `DBTerm.inferType`. -/
def typeRules : List RuleSchema :=
  [rule "hol.type-const" ["c", "a", "g"] [wfJ "Const" (mv "c"), wfJ "Ty" (mv "a")]
      (typeOfJ (mv "g") (constTermP (mv "c") (mv "a")) (mv "a")),
    rule "hol.type-free" ["x", "a", "g"] [wfJ "Name" (mv "x"), wfJ "Ty" (mv "a")]
      (typeOfJ (mv "g") (freeTermP (mv "x") (mv "a")) (mv "a")),
    rule "hol.type-bound" ["i", "a", "g"] [nthJ (mv "g") (mv "i") (mv "a")]
      (typeOfJ (mv "g") (boundTermP (mv "i")) (mv "a")),
    rule "hol.type-app" ["f", "e", "a", "b", "g"]
      [typeOfJ (mv "g") (mv "f") (functionTyP (mv "a") (mv "b")), typeOfJ (mv "g") (mv "e") (mv "a")]
      (typeOfJ (mv "g") (appTermP (mv "f") (mv "e")) (mv "b")),
    rule "hol.type-abs" ["a", "t", "b", "g"] [wfJ "Ty" (mv "a"), typeOfJ (consP (mv "a") (mv "g")) (mv "t") (mv "b")]
      (typeOfJ (mv "g") (absTermP (mv "a") (mv "t")) (functionTyP (mv "a") (mv "b")))]

/-- `boundIndex` and its failure, over binder lists of free-variable terms. -/
def binderRules : List RuleSchema :=
  [rule "hol.bound-here" ["v", "vs"] [] (boundIndexJ (consP (mv "v") (mv "vs")) (mv "v") unaryZeroP),
    rule "hol.bound-there" ["w", "vs", "v", "i"]
      [neqJ (mv "v") (mv "w"), boundIndexJ (mv "vs") (mv "v") (mv "i")]
      (boundIndexJ (consP (mv "w") (mv "vs")) (mv "v") (unarySuccP (mv "i"))),
    rule "hol.notbound-nil" ["v"] [] (notBoundJ nilP (mv "v")),
    rule "hol.notbound-cons" ["w", "vs", "v"] [neqJ (mv "v") (mv "w"), notBoundJ (mv "vs") (mv "v")]
      (notBoundJ (consP (mv "w") (mv "vs")) (mv "v"))]

/-- `SourceTerm.toDB`. -/
def toDBRules : List RuleSchema :=
  [rule "hol.todb-const" ["bs", "c", "a"] [wfJ "Const" (mv "c"), wfJ "Ty" (mv "a")]
      (toDBJ (mv "bs") (sourceConstP (mv "c") (mv "a")) (constTermP (mv "c") (mv "a"))),
    rule "hol.todb-bound" ["bs", "x", "a", "i"]
      [wfJ "Name" (mv "x"), wfJ "Ty" (mv "a"), boundIndexJ (mv "bs") (freeTermP (mv "x") (mv "a")) (mv "i")]
      (toDBJ (mv "bs") (sourceVarP (mv "x") (mv "a")) (boundTermP (mv "i"))),
    rule "hol.todb-free" ["bs", "x", "a"]
      [wfJ "Name" (mv "x"), wfJ "Ty" (mv "a"), notBoundJ (mv "bs") (freeTermP (mv "x") (mv "a"))]
      (toDBJ (mv "bs") (sourceVarP (mv "x") (mv "a")) (freeTermP (mv "x") (mv "a"))),
    rule "hol.todb-app" ["bs", "f", "e", "f2", "e2"]
      [toDBJ (mv "bs") (mv "f") (mv "f2"), toDBJ (mv "bs") (mv "e") (mv "e2")]
      (toDBJ (mv "bs") (sourceAppP (mv "f") (mv "e")) (appTermP (mv "f2") (mv "e2"))),
    rule "hol.todb-abs" ["bs", "x", "a", "t", "t2"]
      [wfJ "Name" (mv "x"), wfJ "Ty" (mv "a"), toDBJ (consP (freeTermP (mv "x") (mv "a")) (mv "bs")) (mv "t") (mv "t2")]
      (toDBJ (mv "bs") (sourceAbsP (mv "x") (mv "a") (mv "t")) (absTermP (mv "a") (mv "t2")))]

/-- `DBTerm.hasFree` is false, for one term and for a list of terms. -/
def notFreeRules : List RuleSchema :=
  [rule "hol.notfree-const" ["v", "c", "a"] [] (notFreeJ (mv "v") (constTermP (mv "c") (mv "a"))),
    rule "hol.notfree-free" ["v", "x", "a"] [neqJ (mv "v") (freeTermP (mv "x") (mv "a"))]
      (notFreeJ (mv "v") (freeTermP (mv "x") (mv "a"))),
    rule "hol.notfree-bound" ["v", "i"] [] (notFreeJ (mv "v") (boundTermP (mv "i"))),
    rule "hol.notfree-app" ["v", "f", "e"] [notFreeJ (mv "v") (mv "f"), notFreeJ (mv "v") (mv "e")]
      (notFreeJ (mv "v") (appTermP (mv "f") (mv "e"))),
    rule "hol.notfree-abs" ["v", "a", "t"] [notFreeJ (mv "v") (mv "t")]
      (notFreeJ (mv "v") (absTermP (mv "a") (mv "t"))),
    rule "hol.notfreeall-nil" ["v"] [] (notFreeAllJ (mv "v") nilP),
    rule "hol.notfreeall-cons" ["v", "t", "ts"] [notFreeJ (mv "v") (mv "t"), notFreeAllJ (mv "v") (mv "ts")]
      (notFreeAllJ (mv "v") (consP (mv "t") (mv "ts")))]

/-- `DBTerm.closeFreeAt`, the variable given as its free-variable term. -/
def closeRules : List RuleSchema :=
  [rule "hol.close-const" ["v", "d", "c", "a"] []
      (closeJ (mv "v") (mv "d") (constTermP (mv "c") (mv "a")) (constTermP (mv "c") (mv "a"))),
    rule "hol.close-same" ["x", "a", "d"] []
      (closeJ (freeTermP (mv "x") (mv "a")) (mv "d") (freeTermP (mv "x") (mv "a")) (boundTermP (mv "d"))),
    rule "hol.close-other" ["v", "d", "x", "a"] [neqJ (mv "v") (freeTermP (mv "x") (mv "a"))]
      (closeJ (mv "v") (mv "d") (freeTermP (mv "x") (mv "a")) (freeTermP (mv "x") (mv "a"))),
    rule "hol.close-bound" ["v", "d", "i"] []
      (closeJ (mv "v") (mv "d") (boundTermP (mv "i")) (boundTermP (mv "i"))),
    rule "hol.close-app" ["v", "d", "f", "e", "f2", "e2"]
      [closeJ (mv "v") (mv "d") (mv "f") (mv "f2"), closeJ (mv "v") (mv "d") (mv "e") (mv "e2")]
      (closeJ (mv "v") (mv "d") (appTermP (mv "f") (mv "e")) (appTermP (mv "f2") (mv "e2"))),
    rule "hol.close-abs" ["v", "d", "a", "t", "t2"]
      [closeJ (mv "v") (unarySuccP (mv "d")) (mv "t") (mv "t2")]
      (closeJ (mv "v") (mv "d") (absTermP (mv "a") (mv "t")) (absTermP (mv "a") (mv "t2")))]

/-- `DBTerm.instantiateAt`. -/
def instantiateRules : List RuleSchema :=
  [rule "hol.inst-const" ["r", "d", "c", "a"] []
      (instantiateJ (mv "r") (mv "d") (constTermP (mv "c") (mv "a")) (constTermP (mv "c") (mv "a"))),
    rule "hol.inst-free" ["r", "d", "x", "a"] []
      (instantiateJ (mv "r") (mv "d") (freeTermP (mv "x") (mv "a")) (freeTermP (mv "x") (mv "a"))),
    rule "hol.inst-target" ["r", "d"] [] (instantiateJ (mv "r") (mv "d") (boundTermP (mv "d")) (mv "r")),
    rule "hol.inst-other" ["r", "d", "i"] [neqJ (mv "i") (mv "d")]
      (instantiateJ (mv "r") (mv "d") (boundTermP (mv "i")) (boundTermP (mv "i"))),
    rule "hol.inst-app" ["r", "d", "f", "e", "f2", "e2"]
      [instantiateJ (mv "r") (mv "d") (mv "f") (mv "f2"), instantiateJ (mv "r") (mv "d") (mv "e") (mv "e2")]
      (instantiateJ (mv "r") (mv "d") (appTermP (mv "f") (mv "e")) (appTermP (mv "f2") (mv "e2"))),
    rule "hol.inst-abs" ["r", "d", "a", "t", "t2"]
      [instantiateJ (mv "r") (unarySuccP (mv "d")) (mv "t") (mv "t2")]
      (instantiateJ (mv "r") (mv "d") (absTermP (mv "a") (mv "t")) (absTermP (mv "a") (mv "t2")))]

/-- Union and erase on strictly increasing lists. -/
def setRules : List RuleSchema :=
  [rule "hol.union-left" ["h"] [] (unionJ nilP (mv "h") (mv "h")),
    rule "hol.union-right" ["x", "xs"] [] (unionJ (consP (mv "x") (mv "xs")) nilP (consP (mv "x") (mv "xs"))),
    rule "hol.union-lt" ["x", "xs", "y", "ys", "zs"]
      [ltJudgment (mv "x") (mv "y"), unionJ (mv "xs") (consP (mv "y") (mv "ys")) (mv "zs")]
      (unionJ (consP (mv "x") (mv "xs")) (consP (mv "y") (mv "ys")) (consP (mv "x") (mv "zs"))),
    rule "hol.union-gt" ["x", "xs", "y", "ys", "zs"]
      [ltJudgment (mv "y") (mv "x"), unionJ (consP (mv "x") (mv "xs")) (mv "ys") (mv "zs")]
      (unionJ (consP (mv "x") (mv "xs")) (consP (mv "y") (mv "ys")) (consP (mv "y") (mv "zs"))),
    rule "hol.union-eq" ["x", "xs", "ys", "zs"] [unionJ (mv "xs") (mv "ys") (mv "zs")]
      (unionJ (consP (mv "x") (mv "xs")) (consP (mv "x") (mv "ys")) (consP (mv "x") (mv "zs"))),
    rule "hol.erase-nil" ["t"] [] (eraseJ (mv "t") nilP nilP),
    rule "hol.erase-here" ["t", "xs"] [] (eraseJ (mv "t") (consP (mv "t") (mv "xs")) (mv "xs")),
    rule "hol.erase-skip" ["t", "x", "xs", "ys"] [neqJ (mv "t") (mv "x"), eraseJ (mv "t") (mv "xs") (mv "ys")]
      (eraseJ (mv "t") (consP (mv "x") (mv "xs")) (consP (mv "x") (mv "ys")))]

/-- Sorted insertion without duplicates, and sorting by insertion. -/
def sortRules : List RuleSchema :=
  [rule "hol.insert-nil" ["t"] [] (insertJ (mv "t") nilP (consP (mv "t") nilP)),
    rule "hol.insert-eq" ["t", "xs"] [] (insertJ (mv "t") (consP (mv "t") (mv "xs")) (consP (mv "t") (mv "xs"))),
    rule "hol.insert-lt" ["t", "x", "xs"] [ltJudgment (mv "t") (mv "x")]
      (insertJ (mv "t") (consP (mv "x") (mv "xs")) (consP (mv "t") (consP (mv "x") (mv "xs")))),
    rule "hol.insert-gt" ["t", "x", "xs", "ys"] [ltJudgment (mv "x") (mv "t"), insertJ (mv "t") (mv "xs") (mv "ys")]
      (insertJ (mv "t") (consP (mv "x") (mv "xs")) (consP (mv "x") (mv "ys"))),
    rule "hol.sort-nil" [] [] (sortJ nilP nilP),
    rule "hol.sort-cons" ["x", "xs", "ys", "zs"] [sortJ (mv "xs") (mv "ys"), insertJ (mv "x") (mv "ys") (mv "zs")]
      (sortJ (consP (mv "x") (mv "xs")) (mv "zs"))]

/-- `SourceSubstitution.variableType` and `typeAction`, on types and through terms. -/
def typeActionRules : List RuleSchema :=
  [rule "hol.vartype-nil" ["x"] [] (varTypeJ nilP (mv "x") (tyVarP (mv "x"))),
    rule "hol.vartype-hit" ["r", "x", "rest"] []
      (varTypeJ (consP (typeMapletP (mv "r") (tyVarP (mv "x"))) (mv "rest")) (mv "x") (mv "r")),
    rule "hol.vartype-miss" ["r", "k", "rest", "x", "t"] [neqJ (mv "x") (mv "k"), varTypeJ (mv "rest") (mv "x") (mv "t")]
      (varTypeJ (consP (typeMapletP (mv "r") (tyVarP (mv "k"))) (mv "rest")) (mv "x") (mv "t")),
    rule "hol.vartype-skip" ["r", "o", "as", "rest", "x", "t"] [varTypeJ (mv "rest") (mv "x") (mv "t")]
      (varTypeJ (consP (typeMapletP (mv "r") (tyOpP (mv "o") (mv "as"))) (mv "rest")) (mv "x") (mv "t")),
    rule "hol.tyact-var" ["es", "x", "t"] [varTypeJ (mv "es") (mv "x") (mv "t")]
      (tyActJ (mv "es") (tyVarP (mv "x")) (mv "t")),
    rule "hol.tyact-op" ["es", "o", "as", "bs"] [tyActListJ (mv "es") (mv "as") (mv "bs")]
      (tyActJ (mv "es") (tyOpP (mv "o") (mv "as")) (tyOpP (mv "o") (mv "bs"))),
    rule "hol.tyactlist-nil" ["es"] [] (tyActListJ (mv "es") nilP nilP),
    rule "hol.tyactlist-cons" ["es", "a", "as", "b", "bs"]
      [tyActJ (mv "es") (mv "a") (mv "b"), tyActListJ (mv "es") (mv "as") (mv "bs")]
      (tyActListJ (mv "es") (consP (mv "a") (mv "as")) (consP (mv "b") (mv "bs"))),
    rule "hol.termtyact-const" ["es", "c", "a", "b"] [tyActJ (mv "es") (mv "a") (mv "b")]
      (termTyActJ (mv "es") (constTermP (mv "c") (mv "a")) (constTermP (mv "c") (mv "b"))),
    rule "hol.termtyact-free" ["es", "x", "a", "b"] [tyActJ (mv "es") (mv "a") (mv "b")]
      (termTyActJ (mv "es") (freeTermP (mv "x") (mv "a")) (freeTermP (mv "x") (mv "b"))),
    rule "hol.termtyact-bound" ["es", "i"] [] (termTyActJ (mv "es") (boundTermP (mv "i")) (boundTermP (mv "i"))),
    rule "hol.termtyact-app" ["es", "f", "e", "f2", "e2"]
      [termTyActJ (mv "es") (mv "f") (mv "f2"), termTyActJ (mv "es") (mv "e") (mv "e2")]
      (termTyActJ (mv "es") (appTermP (mv "f") (mv "e")) (appTermP (mv "f2") (mv "e2"))),
    rule "hol.termtyact-abs" ["es", "a", "t", "b", "t2"]
      [tyActJ (mv "es") (mv "a") (mv "b"), termTyActJ (mv "es") (mv "t") (mv "t2")]
      (termTyActJ (mv "es") (absTermP (mv "a") (mv "t")) (absTermP (mv "b") (mv "t2"))),
    rule "hol.termtyactlist-nil" ["es"] [] (termTyActListJ (mv "es") nilP nilP),
    rule "hol.termtyactlist-cons" ["es", "t", "ts", "u", "us"]
      [termTyActJ (mv "es") (mv "t") (mv "u"), termTyActListJ (mv "es") (mv "ts") (mv "us")]
      (termTyActListJ (mv "es") (consP (mv "t") (mv "ts")) (consP (mv "u") (mv "us")))]

/-- Term maplets: admission, the first-match lookup of the raw table, and its action. -/
def termActionRules : List RuleSchema :=
  [rule "hol.admit-nil" [] [] (admitTmJ nilP nilP),
    rule "hol.admit-cons" ["s", "x", "a", "c", "rest", "table"]
      [wfJ "Name" (mv "x"), toDBJ nilP (mv "s") (mv "c"), typeOfJ nilP (mv "c") (mv "a"),
        admitTmJ (mv "rest") (mv "table")]
      (admitTmJ (consP (termMapletP (mv "s") (sourceVarP (mv "x") (mv "a"))) (mv "rest"))
        (consP (pairP (freeTermP (mv "x") (mv "a")) (mv "c")) (mv "table"))),
    rule "hol.lookup-here" ["v", "r", "rest"] [] (tmLookupJ (consP (pairP (mv "v") (mv "r")) (mv "rest")) (mv "v") (mv "r")),
    rule "hol.lookup-there" ["w", "s", "rest", "v", "r"] [neqJ (mv "v") (mv "w"), tmLookupJ (mv "rest") (mv "v") (mv "r")]
      (tmLookupJ (consP (pairP (mv "w") (mv "s")) (mv "rest")) (mv "v") (mv "r")),
    rule "hol.nokey-nil" ["v"] [] (tmNoKeyJ nilP (mv "v")),
    rule "hol.nokey-cons" ["w", "s", "rest", "v"] [neqJ (mv "v") (mv "w"), tmNoKeyJ (mv "rest") (mv "v")]
      (tmNoKeyJ (consP (pairP (mv "w") (mv "s")) (mv "rest")) (mv "v")),
    rule "hol.tmapply-const" ["table", "c", "a"] []
      (tmApplyJ (mv "table") (constTermP (mv "c") (mv "a")) (constTermP (mv "c") (mv "a"))),
    rule "hol.tmapply-hit" ["table", "x", "a", "r"] [tmLookupJ (mv "table") (freeTermP (mv "x") (mv "a")) (mv "r")]
      (tmApplyJ (mv "table") (freeTermP (mv "x") (mv "a")) (mv "r")),
    rule "hol.tmapply-miss" ["table", "x", "a"] [tmNoKeyJ (mv "table") (freeTermP (mv "x") (mv "a"))]
      (tmApplyJ (mv "table") (freeTermP (mv "x") (mv "a")) (freeTermP (mv "x") (mv "a"))),
    rule "hol.tmapply-bound" ["table", "i"] [] (tmApplyJ (mv "table") (boundTermP (mv "i")) (boundTermP (mv "i"))),
    rule "hol.tmapply-app" ["table", "f", "e", "f2", "e2"]
      [tmApplyJ (mv "table") (mv "f") (mv "f2"), tmApplyJ (mv "table") (mv "e") (mv "e2")]
      (tmApplyJ (mv "table") (appTermP (mv "f") (mv "e")) (appTermP (mv "f2") (mv "e2"))),
    rule "hol.tmapply-abs" ["table", "a", "t", "t2"] [tmApplyJ (mv "table") (mv "t") (mv "t2")]
      (tmApplyJ (mv "table") (absTermP (mv "a") (mv "t")) (absTermP (mv "a") (mv "t2"))),
    rule "hol.tmapplylist-nil" ["table"] [] (tmApplyListJ (mv "table") nilP nilP),
    rule "hol.tmapplylist-cons" ["table", "t", "ts", "u", "us"]
      [tmApplyJ (mv "table") (mv "t") (mv "u"), tmApplyListJ (mv "table") (mv "ts") (mv "us")]
      (tmApplyListJ (mv "table") (consP (mv "t") (mv "ts")) (consP (mv "u") (mv "us")))]

/-- INST and INST_TYPE: act on the conclusion and on every hypothesis, then sort. -/
def instantiationRules : List RuleSchema :=
  [rule "hol.inst" ["h", "c", "ms", "table", "h1", "h2", "c2"]
      [thmJ (mv "h") (mv "c"), admitTmJ (mv "ms") (mv "table"), tmApplyListJ (mv "table") (mv "h") (mv "h1"),
        sortJ (mv "h1") (mv "h2"), tmApplyJ (mv "table") (mv "c") (mv "c2")]
      (thmJ (mv "h2") (mv "c2")),
    rule "hol.inst-type" ["h", "c", "es", "h1", "h2", "c2"]
      [thmJ (mv "h") (mv "c"), wfJ "TypeMaplets" (mv "es"), termTyActListJ (mv "es") (mv "h") (mv "h1"),
        sortJ (mv "h1") (mv "h2"),
        termTyActJ (mv "es") (mv "c") (mv "c2")]
      (thmJ (mv "h2") (mv "c2"))]

/-- The inference operations other than instantiation. -/
def inferenceRules : List RuleSchema :=
  [rule "hol.refl" ["t", "a"] [typeOfJ nilP (mv "t") (mv "a")]
      (thmJ nilP (equalityTermP (mv "a") (mv "t") (mv "t"))),
    rule "hol.assume" ["t"] [typeOfJ nilP (mv "t") boolP] (thmJ (consP (mv "t") nilP) (mv "t")),
    rule "hol.trans" ["h1", "h2", "h", "a", "l", "m", "r"]
      [thmJ (mv "h1") (equalityTermP (mv "a") (mv "l") (mv "m")),
        thmJ (mv "h2") (equalityTermP (mv "a") (mv "m") (mv "r")), unionJ (mv "h1") (mv "h2") (mv "h")]
      (thmJ (mv "h") (equalityTermP (mv "a") (mv "l") (mv "r"))),
    rule "hol.mk-comb" ["h1", "h2", "h", "a", "b", "f", "g", "x", "y"]
      [thmJ (mv "h1") (equalityTermP (functionTyP (mv "a") (mv "b")) (mv "f") (mv "g")),
        thmJ (mv "h2") (equalityTermP (mv "a") (mv "x") (mv "y")), unionJ (mv "h1") (mv "h2") (mv "h")]
      (thmJ (mv "h") (equalityTermP (mv "b") (appTermP (mv "f") (mv "x")) (appTermP (mv "g") (mv "y")))),
    rule "hol.abs" ["h", "a", "s", "t", "x", "b", "s2", "t2"]
      [thmJ (mv "h") (equalityTermP (mv "a") (mv "s") (mv "t")), wfJ "Name" (mv "x"), wfJ "Ty" (mv "b"),
        notFreeAllJ (freeTermP (mv "x") (mv "b")) (mv "h"),
        closeJ (freeTermP (mv "x") (mv "b")) unaryZeroP (mv "s") (mv "s2"),
        closeJ (freeTermP (mv "x") (mv "b")) unaryZeroP (mv "t") (mv "t2")]
      (thmJ (mv "h") (equalityTermP (functionTyP (mv "b") (mv "a"))
        (absTermP (mv "b") (mv "s2")) (absTermP (mv "b") (mv "t2")))),
    rule "hol.beta" ["x", "a", "t", "body", "u", "reduced"]
      [toDBJ nilP (sourceAppP (sourceAbsP (mv "x") (mv "a") (mv "t")) (sourceVarP (mv "x") (mv "a")))
          (appTermP (absTermP (mv "a") (mv "body")) (freeTermP (mv "x") (mv "a"))),
        typeOfJ nilP (appTermP (absTermP (mv "a") (mv "body")) (freeTermP (mv "x") (mv "a"))) (mv "u"),
        instantiateJ (freeTermP (mv "x") (mv "a")) unaryZeroP (mv "body") (mv "reduced")]
      (thmJ nilP (equalityTermP (mv "u")
        (appTermP (absTermP (mv "a") (mv "body")) (freeTermP (mv "x") (mv "a"))) (mv "reduced"))),
    rule "hol.eq-mp" ["h1", "h2", "h", "a", "p", "q"]
      [thmJ (mv "h1") (equalityTermP (mv "a") (mv "p") (mv "q")), thmJ (mv "h2") (mv "p"),
        unionJ (mv "h1") (mv "h2") (mv "h")]
      (thmJ (mv "h") (mv "q")),
    rule "hol.deduct-antisym" ["h1", "h2", "k1", "k2", "h", "p", "q", "a"]
      [thmJ (mv "h1") (mv "p"), thmJ (mv "h2") (mv "q"), typeOfJ nilP (mv "p") (mv "a"),
        typeOfJ nilP (mv "q") (mv "a"), eraseJ (mv "q") (mv "h1") (mv "k1"),
        eraseJ (mv "p") (mv "h2") (mv "k2"), unionJ (mv "k1") (mv "k2") (mv "h")]
      (thmJ (mv "h") (equalityTermP (mv "a") (mv "p") (mv "q")))]

/-- A rendered sequent: the sorted hypotheses and the conclusion. -/
def sequentHypothesesP (sequent : Sequent) : Pattern :=
  listP ((sortedHypotheses sequent.hyp).map fun term => groundP (encodeCanonical term))

def sequentConclusionP (sequent : Sequent) : Pattern := groundP (encodeCanonical sequent.concl)

/-- The claim that a sequent is derivable. -/
def sequentJ (sequent : Sequent) : Pattern := thmJ (sequentHypothesesP sequent) (sequentConclusionP sequent)

/-- One rule per axiom, numbered in order. -/
def axiomRules (axioms : List Sequent) : List RuleSchema :=
  axioms.zipIdx.map fun (sequent, index) => rule ("hol.axiom-" ++ toString index) [] [] (sequentJ sequent)

def holRules (axioms : List Sequent) : List RuleSchema :=
  orderRules ++ neqRules ++ nthRules ++ typeRules ++ binderRules ++ toDBRules ++ notFreeRules ++
    wellFormedRules ++ closeRules ++ instantiateRules ++ setRules ++ sortRules ++ typeActionRules ++
    termActionRules ++
    inferenceRules ++ instantiationRules ++ axiomRules axioms

/-- The calculus over the constructors of the tree encoding. -/
def holCalculus (axioms : List Sequent) : CalculusLanguageDef :=
  cacheDefinition { dataSort := "Tree", cacheName := "HOLLightKernel" } orderConstructors
    (orderJudgments ++ holJudgments) (holRules axioms)

theorem holCalculus_valid : (holCalculus []).isValid = true := by
  decide +kernel

theorem holCalculus_firstOrder : firstOrderCheck (holCalculus []) = true := by
  decide +kernel

end Mettapedia.Languages.HOLLight.FirstOrder
