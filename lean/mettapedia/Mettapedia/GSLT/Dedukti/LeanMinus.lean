import Mettapedia.GSLT.Dedukti.TypingSubstitution
import Mettapedia.GSLT.Dedukti.Render

/-!
# The Dedukti theory of Blanqui and Vaishnav for Lean⁻

Source: F. Blanqui and R. Vaishnav, *Encoding Lean's Type Theory in Dedukti*,
arXiv 2609.24604 (September 2026).  The paper gives a theory `Σ` of the
λΠ-calculus modulo and a translation into it of Lean⁻, the theory that
Lean4Less produces from Lean by removing the K-like recursor rule, proof
irrelevance and unit eta.  This module transcribes `Σ` as a `Theory`, the way
`TwoRoutes.holTheory` transcribes the theory of Holide.

## The fragment

* `ΣU` (Fig. 1 of the paper): type codes `T`, `τ`; comparisons; Booleans;
  natural numbers; ordered sets; sets of naturals; sublevels; sets of
  sublevels; and the levels `L` with `zero`, `succ`, `max`, `imax` and the
  Géran normal form `Max`.  Every declaration and every rule of the figure.
* `Σpoly` (Section 5): `v` and `inst`, for universe-polymorphic constants.
* `ΣP` (Section 3): `U`, `u`, `π`, `ε` and the two rules on `ε`.
* The translations of three Lean declarations, with the rules of Section 6:
  `Eq` (a K-like inductive type, with its recursor rule, linearised as in the
  paper), `PUnit` (a structure with no field, with the rule (β-rec-S) for
  structures, which for no field is `PUnit.rec … x ↪ h`), and `Quot` with its
  axioms `Quot.mk`, `Quot.lift` and the rule (β-quot).

Universe levels: a closed level `l` is the term `|l|` of Definition 2 (`zero`,
`succ`, `max`, `imax`); a level variable `α` of a declaration is the term
`v α ι_α` of Definition 3, with `ι` numbering the level variables of each
declaration from `0`.  A universe-polymorphic constant `x[α]` is declared with
the type `Π α : L, ‖A‖` of Definition 4, written as the paper writes its
example on page 14, "modulo some rewriting": `‖Sort u‖` is written `U |u|`
and `‖A‖` is written `ε |l| |A|`.  Lean's other inductive types, primitive
projections with fields, and the non-left-linear rule for (η-proj) are not
transcribed; Section 6 gives them schematically.

## Names

Dedukti needs one name per symbol where the paper uses typography: the type
code `ᴄ` and the type `C := τ ᴄ` become `C_code` and `C`, and likewise for
`B`, `N`, `S` and `G`; `⊤`, `⊥`, `∧`, `=_N`, `≤_N`, `≤` on sublevels, `π` and
`ε` become `true`, `false`, `and`, `eqN`, `leN`, `leS`, `pi` and `eps`; Lean's
`Eq.refl`, `Eq.rec`, `PUnit.unit`, `PUnit.rec`, `Quot.mk` (the paper's
`class`) and `Quot.lift` (the paper's `lift`) become `Eq_refl`, `Eq_rec`,
`PUnit_unit`, `PUnit_rec`, `Quot_mk` and `Quot_lift`.  Where the figure omits
a comparison argument (`incl_N H G`), it is `incl N_code cmpN H G`, the only
argument of that type.

## Two theories

* `leanTheory`: everything above.
* `pureTheory`: `ΣU` and `ΣP` without `Σpoly` and without the Lean
  declarations, the theory for the constructions of a pure type system at
  closed levels.  `pureTheory_extends` places it inside `leanTheory`.

What is proved about them is in `LeanMinusConversion` and `LeanMinusExamples`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig Decl sigT lookupType lookupBody lift subst subst0 Ctx)

/-! ## Writing terms with named variables -/

/-- The placeholder of a named variable.  Its name begins with `?`, which no
constant of the theory does. -/
def nv (name : String) : Term := .con ("?" ++ name)

/-- Replace the placeholder of `name`, met beneath `depth` binders, by the
variable bound `depth` binders up. -/
def close (name : String) : Nat → Term → Term
  | depth, .con other => if other = "?" ++ name then .var depth else .con other
  | _, .var index => .var index
  | _, .srt sort => .srt sort
  | depth, .pi domain body => .pi (close name depth domain) (close name (depth + 1) body)
  | depth, .lam domain body => .lam (close name depth domain) (close name (depth + 1) body)
  | depth, .app function argument => .app (close name depth function) (close name depth argument)

/-- `Π name : domain. body`. -/
def piN (name : String) (domain body : Term) : Term := .pi domain (close name 0 body)

/-- `λ name : domain. body`. -/
def lamN (name : String) (domain body : Term) : Term := .lam domain (close name 0 body)

/-- `domain → codomain`.  The codomain is built from constants and
placeholders, so it does not mention the bound variable. -/
def arrow (domain codomain : Term) : Term := .pi domain codomain

/-- `A₁ → … → Aₙ → B`. -/
def arrows : List Term → Term → Term
  | [], result => result
  | domain :: rest, result => arrow domain (arrows rest result)

/-- A term applied to arguments. -/
def apT (head : Term) (arguments : List Term) : Term := arguments.foldl .app head

/-- A constant applied to arguments. -/
def ap (head : String) (arguments : List Term) : Term := apT (.con head) arguments

/-- The position of a placeholder among the names of the pattern variables. -/
def placeholderIndex : List String → String → Option Nat
  | [], _ => none
  | candidate :: rest, name =>
      if name = "?" ++ candidate then some 0 else (placeholderIndex rest name).map (· + 1)

/-- Replace the placeholder of the `i`-th pattern variable, met beneath
`depth` binders, by the free variable `depth + i`. -/
def closePattern (names : List String) : Nat → Term → Term
  | depth, .con other =>
      match placeholderIndex names other with
      | some index => .var (depth + index)
      | none => .con other
  | _, .var index => .var index
  | _, .srt sort => .srt sort
  | depth, .pi domain body =>
      .pi (closePattern names depth domain) (closePattern names (depth + 1) body)
  | depth, .lam domain body =>
      .lam (closePattern names depth domain) (closePattern names (depth + 1) body)
  | depth, .app function argument =>
      .app (closePattern names depth function) (closePattern names depth argument)

/-- A rewrite rule whose pattern variables are named; the `i`-th name is the
pattern variable `i`.  A wildcard `_` of the paper is a pattern variable used
once, and an alias `p as T` is the pattern `p` written again on the right. -/
def mkRule (names : List String) (lhs rhs : Term) : RewriteRule :=
  ⟨closePattern names 0 lhs, closePattern names 0 rhs⟩

/-! ## Common terms -/

def typ : Term := .srt .type
def tCode : Term := .con "T"
def tau (code : Term) : Term := ap "tau" [code]
def setOf (code : Term) : Term := ap "set" [code]
def tauSet (code : Term) : Term := tau (setOf code)
def C : Term := .con "C"
def B : Term := .con "B"
def N : Term := .con "N"
def G : Term := .con "G"
def S : Term := .con "S"
def E : Term := .con "E"
def L : Term := .con "L"
/-- The type of a comparison on the elements of a code. -/
def cmpType (code : Term) : Term := arrows [tau code, tau code] C
def zeroN : Term := .con "0"
def oneN : Term := ap "s" [zeroN]
def zero : Term := .con "zero"
def succ (level : Term) : Term := ap "succ" [level]
def imax (first second : Term) : Term := ap "imax" [first, second]
def U (level : Term) : Term := ap "U" [level]
def eps (level code : Term) : Term := ap "eps" [level, code]
def instOf (level : Term) : Term := ap "inst" [level]
/-- The Géran normal form of the level variable numbered `index`. -/
def levelVariable (index : Term) : Term :=
  ap "Max" [ap "cons" [.con "S_code", ap "var" [ap "nil" [.con "N_code"], index, zeroN],
    ap "nil" [.con "S_code"]]]
/-- `|α| = v α ι_α` (Definition 3). -/
def lv (name : String) (index : Term) : Term := ap "v" [nv name, index]

/-! ## `ΣU`: Figure 1 -/

def sigmaT : Sig := [.const "T" typ, .const "tau" (arrow tCode typ)]

def sigmaC : Sig :=
  [.const "C_code" tCode, .defn "C" typ (tau (.con "C_code")),
    .const "lt" C, .const "eq" C, .const "gt" C,
    .const "case" (piN "a" tCode
      (arrows [C, tau (nv "a"), tau (nv "a"), tau (nv "a")] (tau (nv "a"))))]

def rulesC : List RewriteRule :=
  [mkRule ["w0", "x", "w1", "w2"] (ap "case" [nv "w0", .con "lt", nv "x", nv "w1", nv "w2"]) (nv "x"),
    mkRule ["w0", "w1", "x", "w2"] (ap "case" [nv "w0", .con "eq", nv "w1", nv "x", nv "w2"]) (nv "x"),
    mkRule ["w0", "w1", "w2", "x"] (ap "case" [nv "w0", .con "gt", nv "w1", nv "w2", nv "x"]) (nv "x")]

def sigmaB : Sig :=
  [.const "B_code" tCode, .defn "B" typ (tau (.con "B_code")),
    .const "true" B, .const "false" B, .const "and" (arrows [B, B] B),
    .const "if" (piN "a" tCode (arrows [B, tau (nv "a"), tau (nv "a")] (tau (nv "a"))))]

def rulesB : List RewriteRule :=
  [mkRule [] (ap "and" [.con "true", .con "true"]) (.con "true"),
    mkRule ["w"] (ap "and" [.con "false", nv "w"]) (.con "false"),
    mkRule ["w"] (ap "and" [nv "w", .con "false"]) (.con "false"),
    mkRule ["w0", "x", "w1"] (ap "if" [nv "w0", .con "true", nv "x", nv "w1"]) (nv "x"),
    mkRule ["w0", "w1", "x"] (ap "if" [nv "w0", .con "false", nv "w1", nv "x"]) (nv "x")]

def sigmaN : Sig :=
  [.const "N_code" tCode, .defn "N" typ (tau (.con "N_code")),
    .const "0" N, .const "s" (arrow N N), .const "cmpN" (arrows [N, N] C),
    .defn "eqN" (arrows [N, N] B) (lamN "x" N (lamN "y" N
      (ap "case" [.con "B_code", ap "cmpN" [nv "x", nv "y"], .con "false", .con "true",
        .con "false"]))),
    .defn "leN" (arrows [N, N] B) (lamN "x" N (lamN "y" N
      (ap "case" [.con "B_code", ap "cmpN" [nv "x", nv "y"], .con "true", .con "true",
        .con "false"])))]

def rulesN : List RewriteRule :=
  [mkRule [] (ap "cmpN" [zeroN, zeroN]) (.con "eq"),
    mkRule ["w"] (ap "cmpN" [ap "s" [nv "w"], zeroN]) (.con "gt"),
    mkRule ["w"] (ap "cmpN" [zeroN, ap "s" [nv "w"]]) (.con "lt"),
    mkRule ["x", "y"] (ap "cmpN" [ap "s" [nv "x"], ap "s" [nv "y"]]) (ap "cmpN" [nv "x", nv "y"])]

def sigmaSet : Sig :=
  [.const "set" (arrow tCode tCode),
    .const "nil" (piN "a" tCode (tauSet (nv "a"))),
    .const "cons" (piN "a" tCode (arrows [tau (nv "a"), tauSet (nv "a")] (tauSet (nv "a")))),
    .const "fold" (piN "a" tCode (piN "b" tCode
      (arrows [arrows [tau (nv "a"), tau (nv "b")] (tau (nv "b")), tauSet (nv "a"), tau (nv "b")]
        (tau (nv "b"))))),
    .const "add" (piN "a" tCode
      (arrows [cmpType (nv "a"), tau (nv "a"), tauSet (nv "a")] (tauSet (nv "a")))),
    .const "union" (piN "a" tCode
      (arrows [cmpType (nv "a"), tauSet (nv "a"), tauSet (nv "a")] (tauSet (nv "a")))),
    .const "incl" (piN "a" tCode (arrows [cmpType (nv "a"), tauSet (nv "a"), tauSet (nv "a")] B)),
    .const "cmpset" (piN "a" tCode (arrows [cmpType (nv "a"), tauSet (nv "a"), tauSet (nv "a")] C))]

/-- `f x y`, for a pattern variable `f`. -/
def call (function first second : Term) : Term := apT function [first, second]

def rulesSet : List RewriteRule :=
  [mkRule ["a", "b", "f", "w", "y"]
      (ap "fold" [nv "a", nv "b", nv "f", ap "nil" [nv "w"], nv "y"]) (nv "y"),
    mkRule ["a", "b", "f", "w", "x", "s1", "y"]
      (ap "fold" [nv "a", nv "b", nv "f", ap "cons" [nv "w", nv "x", nv "s1"], nv "y"])
      (ap "fold" [nv "a", nv "b", nv "f", nv "s1", call (nv "f") (nv "x") (nv "y")]),
    mkRule ["a", "w0", "x", "w1"] (ap "add" [nv "a", nv "w0", nv "x", ap "nil" [nv "w1"]])
      (ap "cons" [nv "a", nv "x", ap "nil" [nv "a"]]),
    mkRule ["a", "f", "x", "w", "y", "s1"]
      (ap "add" [nv "a", nv "f", nv "x", ap "cons" [nv "w", nv "y", nv "s1"]])
      (ap "case" [setOf (nv "a"), call (nv "f") (nv "x") (nv "y"),
        ap "cons" [nv "a", nv "x", ap "cons" [nv "w", nv "y", nv "s1"]],
        ap "cons" [nv "w", nv "y", nv "s1"],
        ap "cons" [nv "a", nv "y", ap "add" [nv "a", nv "f", nv "x", nv "s1"]]]),
    mkRule ["w0", "w1", "w2", "t1"] (ap "union" [nv "w0", nv "w1", ap "nil" [nv "w2"], nv "t1"])
      (nv "t1"),
    mkRule ["a", "f", "w", "x", "s1", "t1"]
      (ap "union" [nv "a", nv "f", ap "cons" [nv "w", nv "x", nv "s1"], nv "t1"])
      (ap "add" [nv "a", nv "f", nv "x", ap "union" [nv "a", nv "f", nv "s1", nv "t1"]]),
    mkRule ["w0", "w1", "w2", "w3"] (ap "incl" [nv "w0", nv "w1", ap "nil" [nv "w2"], nv "w3"])
      (.con "true"),
    mkRule ["w0", "w1", "w2", "w3", "w4", "w5"]
      (ap "incl" [nv "w0", nv "w1", ap "cons" [nv "w2", nv "w3", nv "w4"], ap "nil" [nv "w5"]])
      (.con "false"),
    mkRule ["a", "f", "w0", "x", "s1", "w1", "y", "t1"]
      (ap "incl" [nv "a", nv "f", ap "cons" [nv "w0", nv "x", nv "s1"],
        ap "cons" [nv "w1", nv "y", nv "t1"]])
      (ap "case" [.con "B_code", call (nv "f") (nv "x") (nv "y"), .con "false",
        ap "incl" [nv "a", nv "f", nv "s1", nv "t1"],
        ap "incl" [nv "a", nv "f", ap "cons" [nv "w0", nv "x", nv "s1"], nv "t1"]]),
    mkRule ["w0", "w1", "w2", "w3"]
      (ap "cmpset" [nv "w0", nv "w1", ap "nil" [nv "w2"], ap "nil" [nv "w3"]]) (.con "eq"),
    mkRule ["w0", "w1", "w2", "w3", "w4", "w5"]
      (ap "cmpset" [nv "w0", nv "w1", ap "nil" [nv "w2"], ap "cons" [nv "w3", nv "w4", nv "w5"]])
      (.con "lt"),
    mkRule ["w0", "w1", "w2", "w3", "w4", "w5"]
      (ap "cmpset" [nv "w0", nv "w1", ap "cons" [nv "w2", nv "w3", nv "w4"], ap "nil" [nv "w5"]])
      (.con "gt"),
    mkRule ["a", "f", "w0", "x", "s1", "w1", "y", "t1"]
      (ap "cmpset" [nv "a", nv "f", ap "cons" [nv "w0", nv "x", nv "s1"],
        ap "cons" [nv "w1", nv "y", nv "t1"]])
      (ap "case" [.con "C_code", call (nv "f") (nv "x") (nv "y"), .con "lt",
        ap "cmpset" [nv "a", nv "f", nv "s1", nv "t1"], .con "gt"])]

def sigmaG : Sig :=
  [.defn "G_code" tCode (setOf (.con "N_code")),
    .defn "G" typ (tau (.con "G_code")),
    .defn "cmpG" (arrows [G, G] C) (ap "cmpset" [.con "N_code", .con "cmpN"])]

def sigmaS : Sig :=
  [.const "S_code" tCode, .defn "S" typ (tau (.con "S_code")),
    .const "var" (arrows [G, N, N] S), .const "cst" (arrows [G, N] S),
    .const "cmpS" (arrows [S, S] C), .const "guard" (arrow S G),
    .const "addguard" (arrows [S, S] S), .const "incr" (arrow S S),
    .const "leS" (arrows [S, S] B)]

/-- `incl_N H G`. -/
def inclN (first second : Term) : Term := ap "incl" [.con "N_code", .con "cmpN", first, second]

def rulesS : List RewriteRule :=
  [mkRule ["w0", "w1", "w2", "w3", "w4"]
      (ap "cmpS" [ap "cst" [nv "w0", nv "w1"], ap "var" [nv "w2", nv "w3", nv "w4"]]) (.con "lt"),
    mkRule ["w0", "w1", "w2", "w3", "w4"]
      (ap "cmpS" [ap "var" [nv "w0", nv "w1", nv "w2"], ap "cst" [nv "w3", nv "w4"]]) (.con "gt"),
    mkRule ["g", "i", "h", "j"]
      (ap "cmpS" [ap "cst" [nv "g", nv "i"], ap "cst" [nv "h", nv "j"]])
      (ap "case" [.con "C_code", ap "cmpG" [nv "g", nv "h"], .con "lt", ap "cmpN" [nv "i", nv "j"],
        .con "gt"]),
    mkRule ["g", "x", "i", "h", "y", "j"]
      (ap "cmpS" [ap "var" [nv "g", nv "x", nv "i"], ap "var" [nv "h", nv "y", nv "j"]])
      (ap "case" [.con "C_code", ap "cmpG" [nv "g", nv "h"], .con "lt",
        ap "case" [.con "C_code", ap "cmpN" [nv "x", nv "y"], .con "lt", ap "cmpN" [nv "i", nv "j"],
          .con "gt"],
        .con "gt"]),
    mkRule ["g", "w0", "w1"] (ap "guard" [ap "var" [nv "g", nv "w0", nv "w1"]]) (nv "g"),
    mkRule ["g", "w"] (ap "guard" [ap "cst" [nv "g", nv "w"]]) (nv "g"),
    mkRule ["g", "i", "o"] (ap "addguard" [ap "cst" [nv "g", nv "i"], nv "o"])
      (ap "cst" [ap "union" [.con "N_code", .con "cmpN", nv "g", ap "guard" [nv "o"]], nv "i"]),
    mkRule ["g", "x", "i", "o"] (ap "addguard" [ap "var" [nv "g", nv "x", nv "i"], nv "o"])
      (ap "var" [ap "union" [.con "N_code", .con "cmpN", nv "g", ap "guard" [nv "o"]], nv "x",
        nv "i"]),
    mkRule ["g", "x", "i"] (ap "incr" [ap "var" [nv "g", nv "x", nv "i"]])
      (ap "var" [nv "g", nv "x", ap "s" [nv "i"]]),
    mkRule ["g", "i"] (ap "incr" [ap "cst" [nv "g", nv "i"]]) (ap "cst" [nv "g", ap "s" [nv "i"]]),
    mkRule ["w0", "w1", "w2", "w3", "w4"]
      (ap "leS" [ap "var" [nv "w0", nv "w1", nv "w2"], ap "cst" [nv "w3", nv "w4"]]) (.con "false"),
    mkRule ["g", "i", "h", "j"] (ap "leS" [ap "cst" [nv "g", nv "i"], ap "cst" [nv "h", nv "j"]])
      (ap "and" [inclN (nv "h") (nv "g"), ap "leN" [nv "i", nv "j"]]),
    mkRule ["g", "i", "h", "w", "j"]
      (ap "leS" [ap "cst" [nv "g", nv "i"], ap "var" [nv "h", nv "w", nv "j"]])
      (ap "and" [inclN (nv "h") (nv "g"), ap "leN" [nv "i", ap "s" [nv "j"]]]),
    mkRule ["g", "x", "i", "h", "y", "j"]
      (ap "leS" [ap "var" [nv "g", nv "x", nv "i"], ap "var" [nv "h", nv "y", nv "j"]])
      (ap "and" [inclN (nv "h") (nv "g"),
        ap "and" [ap "eqN" [nv "x", nv "y"], ap "leN" [nv "i", nv "j"]]])]

def sigmaE : Sig :=
  [.defn "E" typ (tauSet (.con "S_code")),
    .const "Incr" (arrow E E), .const "Add" (arrows [S, E] E)]

def rulesE : List RewriteRule :=
  [mkRule ["w"] (ap "Incr" [ap "nil" [nv "w"]]) (ap "nil" [.con "S_code"]),
    mkRule ["w", "o", "s1"] (ap "Incr" [ap "cons" [nv "w", nv "o", nv "s1"]])
      (ap "cons" [.con "S_code", ap "incr" [nv "o"], ap "Incr" [nv "s1"]]),
    mkRule ["o", "w"] (ap "Add" [nv "o", ap "nil" [nv "w"]])
      (ap "cons" [.con "S_code", nv "o", ap "nil" [.con "S_code"]]),
    mkRule ["o", "w", "o1", "e1"] (ap "Add" [nv "o", ap "cons" [nv "w", nv "o1", nv "e1"]])
      (ap "if" [setOf (.con "S_code"), ap "leS" [nv "o", nv "o1"],
        ap "cons" [nv "w", nv "o1", nv "e1"],
        ap "if" [setOf (.con "S_code"), ap "leS" [nv "o1", nv "o"],
          ap "add" [.con "S_code", .con "cmpS", nv "o", nv "e1"],
          ap "add" [.con "S_code", .con "cmpS", nv "o1", ap "Add" [nv "o", nv "e1"]]]])]

def sigmaI : Sig :=
  [.const "L" typ, .const "zero" L, .const "succ" (arrow L L),
    .const "max" (arrows [L, L] L), .const "imax" (arrows [L, L] L),
    .const "Max" (arrow E L),
    .defn "Fold" (arrows [arrows [S, E] E, E, E] E) (ap "fold" [.con "S_code", setOf (.con "S_code")]),
    .defn "Addguard" (arrows [S, S, E] E)
      (lamN "u" S (lamN "v" S (ap "Add" [ap "addguard" [nv "u", nv "v"]]))),
    .defn "FoldAddguard" (arrows [E, S, E] E)
      (lamN "f" E (lamN "u" S (ap "Fold" [ap "Addguard" [nv "u"], nv "f"])))]

def rulesI : List RewriteRule :=
  [mkRule [] zero (ap "Max" [ap "nil" [.con "S_code"]]),
    mkRule ["e1"] (succ (ap "Max" [nv "e1"]))
      (ap "Max" [ap "Add" [ap "cst" [ap "nil" [.con "N_code"], oneN], ap "Incr" [nv "e1"]]]),
    mkRule ["e1", "f1"] (ap "max" [ap "Max" [nv "e1"], ap "Max" [nv "f1"]])
      (ap "Max" [ap "Fold" [.con "Add", nv "e1", nv "f1"]]),
    mkRule ["w0", "w1"] (imax (ap "Max" [nv "w0"]) (ap "Max" [ap "nil" [nv "w1"]]))
      (ap "Max" [ap "nil" [.con "S_code"]]),
    mkRule ["e1", "w0", "w1", "w2"]
      (imax (ap "Max" [nv "e1"]) (ap "Max" [ap "cons" [nv "w0", nv "w1", nv "w2"]]))
      (ap "Max" [ap "Fold" [ap "FoldAddguard" [ap "cons" [nv "w0", nv "w1", nv "w2"]], nv "e1",
        ap "cons" [nv "w0", nv "w1", nv "w2"]]])]

/-! ## `ΣP`: Section 3 -/

def sigmaP : Sig :=
  [.const "U" (arrow L typ),
    .const "eps" (piN "al" L (arrow (U (nv "al")) typ)),
    .const "u" (piN "al" L (U (succ (nv "al")))),
    .const "pi" (piN "al" L (piN "be" L (piN "t" (U (nv "al"))
      (arrow (arrow (eps (nv "al") (nv "t")) (U (nv "be"))) (U (imax (nv "al") (nv "be")))))))]

def rulesP : List RewriteRule :=
  [mkRule ["w", "al"] (eps (nv "w") (ap "u" [nv "al"])) (U (nv "al")),
    mkRule ["w", "al", "be", "t", "t1"] (eps (nv "w") (ap "pi" [nv "al", nv "be", nv "t", nv "t1"]))
      (piN "x" (eps (nv "al") (nv "t")) (eps (nv "be") (apT (nv "t1") [nv "x"])))]

/-! ## `Σpoly`: Section 5 -/

def sigmaPoly : Sig := [.const "v" (arrows [L, N] L), .const "inst" (arrow L L)]

/-- `v (inst l) _ ↪ l`. -/
def instRule : RewriteRule := mkRule ["l", "w"] (ap "v" [instOf (nv "l"), nv "w"]) (nv "l")

/-- `v _ i ↪ Max (cons_S (var (nil_N) i 0) nil_S)`. -/
def variableRule : RewriteRule := mkRule ["w", "i"] (ap "v" [nv "w", nv "i"]) (levelVariable (nv "i"))

def rulesPoly : List RewriteRule := [instRule, variableRule]

/-! ## Three Lean declarations, translated (Definition 4 and Section 6) -/

/-- `|α|` for the first level variable of a declaration. -/
def levelA : Term := lv "al" zeroN
/-- `|β|` for the second level variable of a declaration. -/
def levelB : Term := lv "be" oneN
/-- The type of a relation `A → A → Prop`, translated. -/
def relationType (level code : Term) : Term := arrows [eps level code, eps level code] (U zero)
/-- `Eq[α] A x y`, translated. -/
def eqCode (level code first second : Term) : Term := ap "Eq" [instOf level, code, first, second]

def sigmaLean : Sig :=
  [.const "Eq" (piN "al" L (piN "A" (U levelA)
      (arrows [eps levelA (nv "A"), eps levelA (nv "A")] (U zero)))),
    .const "Eq_refl" (piN "al" L (piN "A" (U levelA) (piN "a" (eps levelA (nv "A"))
      (eps zero (eqCode levelA (nv "A") (nv "a") (nv "a")))))),
    .const "Eq_rec" (piN "al" L (piN "be" L (piN "A" (U levelA) (piN "a" (eps levelA (nv "A"))
      (piN "Q" (piN "b" (eps levelA (nv "A"))
          (arrow (eps zero (eqCode levelA (nv "A") (nv "a") (nv "b"))) (U levelB)))
        (arrow (eps levelB (apT (nv "Q") [nv "a", ap "Eq_refl" [instOf levelA, nv "A", nv "a"]]))
          (piN "b" (eps levelA (nv "A"))
            (piN "e" (eps zero (eqCode levelA (nv "A") (nv "a") (nv "b")))
              (eps levelB (apT (nv "Q") [nv "b", nv "e"])))))))))),
    .const "PUnit" (piN "al" L (U levelA)),
    .const "PUnit_unit" (piN "al" L (eps levelA (ap "PUnit" [instOf levelA]))),
    .const "PUnit_rec" (piN "al" L (piN "be" L
      (piN "Q" (arrow (eps levelA (ap "PUnit" [instOf levelA])) (U levelB))
        (arrow (eps levelB (apT (nv "Q") [ap "PUnit_unit" [instOf levelA]]))
          (piN "x" (eps levelA (ap "PUnit" [instOf levelA])) (eps levelB (apT (nv "Q") [nv "x"]))))))),
    .const "Quot" (piN "al" L (piN "A" (U levelA)
      (arrow (relationType levelA (nv "A")) (U levelA)))),
    .const "Quot_mk" (piN "al" L (piN "A" (U levelA) (piN "R" (relationType levelA (nv "A"))
      (arrow (eps levelA (nv "A")) (eps levelA (ap "Quot" [instOf levelA, nv "A", nv "R"])))))),
    .const "Quot_lift" (piN "al" L (piN "be" L (piN "A" (U levelA)
      (piN "R" (relationType levelA (nv "A")) (piN "B" (U levelB)
        (piN "f" (arrow (eps levelA (nv "A")) (eps levelB (nv "B")))
          (arrow (piN "x" (eps levelA (nv "A")) (piN "y" (eps levelA (nv "A"))
              (arrow (eps zero (apT (nv "R") [nv "x", nv "y"]))
                (eps zero (eqCode levelB (nv "B") (apT (nv "f") [nv "x"]) (apT (nv "f") [nv "y"]))))))
            (arrow (eps levelA (ap "Quot" [instOf levelA, nv "A", nv "R"])) (eps levelB (nv "B"))))))))))]

/-- `Eq.rec α β A a Q h _ (Eq.refl α' A' a') ↪ h`, the recursor rule of `Eq`
linearised as in Section 6. -/
def eqRecRule : RewriteRule :=
  mkRule ["al", "be", "A", "a", "Q", "h", "w", "al1", "A1", "a1"]
    (ap "Eq_rec" [nv "al", nv "be", nv "A", nv "a", nv "Q", nv "h", nv "w",
      ap "Eq_refl" [nv "al1", nv "A1", nv "a1"]])
    (nv "h")

/-- `PUnit.rec α β Q h x ↪ h`: rule (β-rec-S) for a structure with no field. -/
def punitRecRule : RewriteRule :=
  mkRule ["al", "be", "Q", "h", "x"] (ap "PUnit_rec" [nv "al", nv "be", nv "Q", nv "h", nv "x"]) (nv "h")

/-- `lift α β A R B f h (class α' A' R' a) ↪ f a` (β-quot). -/
def quotLiftRule : RewriteRule :=
  mkRule ["al", "be", "A", "R", "B", "f", "h", "al1", "A1", "R1", "a"]
    (ap "Quot_lift" [nv "al", nv "be", nv "A", nv "R", nv "B", nv "f", nv "h",
      ap "Quot_mk" [nv "al1", nv "A1", nv "R1", nv "a"]])
    (apT (nv "f") [nv "a"])

def rulesLean : List RewriteRule := [eqRecRule, punitRecRule, quotLiftRule]

/-! ## The two theories -/

/-- The declarations of `ΣU` and `ΣP`. -/
def pureSig : Sig :=
  sigmaT ++ sigmaC ++ sigmaB ++ sigmaN ++ sigmaSet ++ sigmaG ++ sigmaS ++ sigmaE ++ sigmaI ++ sigmaP

/-- The rules of `ΣU` and `ΣP`. -/
def pureRules : List RewriteRule :=
  rulesC ++ rulesB ++ rulesN ++ rulesSet ++ rulesS ++ rulesE ++ rulesI ++ rulesP

/-- All declarations, in an order that Dedukti accepts. -/
def leanSig : Sig := pureSig ++ sigmaPoly ++ sigmaLean

/-- All rules. -/
def leanRules : List RewriteRule := pureRules ++ rulesPoly ++ rulesLean

/-- **The theory for the constructions of a pure type system at closed
levels**: `ΣU` and `ΣP`. -/
def pureTheory : Theory := Theory.ofSig pureSig pureRules

/-- **The theory of the paper**, as far as transcribed: `ΣU`, `Σpoly`, `ΣP`
and the declarations of `Eq`, `PUnit` and `Quot`. -/
def leanTheory : Theory := Theory.ofSig leanSig leanRules

theorem lookupType_append (first second : Sig) (name : String) :
    lookupType (first ++ second) name = (lookupType first name).or (lookupType second name) := by
  induction first with
  | nil => simp [lookupType]
  | cons head rest ih =>
      cases head with
      | const declared type =>
          by_cases same : name = declared <;> simp [lookupType, same, ih]
      | defn declared type body =>
          by_cases same : name = declared <;> simp [lookupType, same, ih]

theorem lookupBody_append (first second : Sig) (name : String) :
    lookupBody (first ++ second) name = (lookupBody first name).or (lookupBody second name) := by
  induction first with
  | nil => simp [lookupBody]
  | cons head rest ih =>
      cases head with
      | const declared type => simp [lookupBody, ih]
      | defn declared type body =>
          by_cases same : name = declared <;> simp [lookupBody, same, ih]

/-- **The theory of a pure type system at closed levels is part of the
theory of the paper.** -/
theorem pureTheory_extends : pureTheory.Extends leanTheory where
  constType := fun name type declared => by
    have here : lookupType pureSig name = some type := declared
    show lookupType (pureSig ++ sigmaPoly ++ sigmaLean) name = some type
    rw [List.append_assoc, lookupType_append, here]
    rfl
  body := fun name term defined => by
    have here : lookupBody pureSig name = some term := defined
    show lookupBody (pureSig ++ sigmaPoly ++ sigmaLean) name = some term
    rw [List.append_assoc, lookupBody_append, here]
    rfl
  rule := fun rule member => List.mem_append_left _ (List.mem_append_left _ member)

/-! ## Rendering for the Dedukti checker -/

/-- The constants that head a rule. -/
def ruleHeads (rules : List RewriteRule) : List String :=
  rules.filterMap fun rule => headConst rule.lhs

/-- The names of the pattern variables of a rule, by position. -/
def patternNamesOf (count : Nat) : List String :=
  (List.range count).map fun index => s!"p{index}"

/-- The number of pattern variables a rule uses. -/
def patternCount : Nat → Term → Nat
  | depth, .var index => if index < depth then 0 else index - depth + 1
  | _, .srt _ => 0
  | _, .con _ => 0
  | depth, .pi domain body => max (patternCount depth domain) (patternCount (depth + 1) body)
  | depth, .lam domain body => max (patternCount depth domain) (patternCount (depth + 1) body)
  | depth, .app function argument =>
      max (patternCount depth function) (patternCount depth argument)

/-- The sections of the theory, each with the rules on its symbols, in the
order of the paper except that `ΣP` comes before `Σpoly`, as the declarations
of the Lean constants need both. -/
def sections : List (Sig × List RewriteRule) :=
  [(sigmaT, []), (sigmaC, rulesC), (sigmaB, rulesB), (sigmaN, rulesN), (sigmaSet, rulesSet),
    (sigmaG, []), (sigmaS, rulesS), (sigmaE, rulesE), (sigmaI, rulesI), (sigmaP, rulesP),
    (sigmaPoly, rulesPoly), (sigmaLean, rulesLean)]

/-- Sections as a Dedukti file: each section's declarations, then its rules,
so that a rule is read after every symbol it mentions and before every
declaration whose typing needs it. -/
def render (parts : List (Sig × List RewriteRule)) : String :=
  let heads := ruleHeads (parts.flatMap Prod.snd)
  String.join <| parts.map fun (signature, rules) =>
    String.join (signature.map fun
      | .const name type => Render.declaration (heads.contains name) name type
      | .defn name type body => Render.renderDefinition name type body) ++
    String.join (rules.map fun rule =>
      Render.rule (patternNamesOf (max (patternCount 0 rule.lhs) (patternCount 0 rule.rhs))) rule)

end Mettapedia.GSLT.Dedukti.LeanMinus
