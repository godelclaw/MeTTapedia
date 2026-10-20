/-
Prints `tests/petta/gslt_canonical_controls.metta`. Every expected value is the Lean canonical
form (`CanonicalBags.canon`, `CanonicalBags.lawNormal`) or model normal form (`Wrappers.modelNormal`)
with the table `CanonicalCompare.nameTable`.
Run from `lean/mettapedia`: `lake env lean ../../metta/gslt/tools/generate_canonical_controls.lean`.
-/
import Mettapedia.OSLF.MeTTaIL.CanonicalTable
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire
import Mettapedia.OSLF.MeTTaIL.Complete.RhoQuoteDrop

open Mettapedia.OSLF.MeTTaIL Syntax CanonicalBags CanonicalCompare CollectionLaws
open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def render (term : Term) : String := Term.render term

def table : List String := nameTable ["PZero", "PDrop", "NQuote", "PInput", "POutput", "PPar", "a", "b"]

def tableTerm : Term := CettaWire.encodeList Term.string table

def rhoLaws : List Laws := [⟨.hashBag, some "PZero"⟩]

/-- Rho's law and a set law without a unit. -/
def setLaws : List Laws := [⟨.hashBag, some "PZero"⟩, ⟨.hashSet, none⟩]

def rhoPresentation : ReflectivePresentationDecl := Mettapedia.OSLF.MeTTaIL.Complete.RhoQuoteDrop.presentation

def lawsTerm (laws : List Laws) : Term := CettaWire.encodeList StandardWire.lawTerm laws

def zero : Pattern := .apply "PZero" []
def quote (process : Pattern) : Pattern := .apply "NQuote" [process]
def drop (name : Pattern) : Pattern := .apply "PDrop" [name]
def output (name process : Pattern) : Pattern := .apply "POutput" [name, process]
def input (name body : Pattern) : Pattern := .apply "PInput" [name, .lambda none body]
def bag (elements : List Pattern) : Pattern := .collection .hashBag elements none
def set (elements : List Pattern) : Pattern := .collection .hashSet elements none
def vec (elements : List Pattern) : Pattern := .collection .vec elements none

def canonControl (label : String) (pattern : Pattern) : String :=
  "!(let* (($t (quote " ++ render tableTerm ++ "))\n" ++
  "        ($x (quote " ++ render (encodePattern pattern) ++ "))\n" ++
  "        ($r (gslt:canon:canon $t $x)))\n" ++
  "  (println! (CanonicalControl " ++ reprStr label ++ " (== $r (quote " ++
    render (encodePattern (canon pattern)) ++ ")))))"

def canonicalControl (label : String) (laws : List Laws) (pattern : Pattern) : String :=
  "!(let* (($t (quote " ++ render tableTerm ++ "))\n" ++
  "        ($l (quote " ++ render (lawsTerm laws) ++ "))\n" ++
  "        ($x (quote " ++ render (encodePattern pattern) ++ "))\n" ++
  "        ($r (gslt:canon:canonical $t $l LNil $x)))\n" ++
  "  (println! (CanonicalControl " ++ reprStr label ++ " (== $r (quote " ++
    render (encodePattern (lawNormal laws pattern)) ++ ")))))"

/-- Two presentations: equal canonical forms exactly when Lean's are equal. -/
def sameControl (label : String) (laws : List Laws) (left right : Pattern) : String :=
  let expected := if lawNormal laws left = lawNormal laws right then "True" else "False"
  "!(let* (($t (quote " ++ render tableTerm ++ "))\n" ++
  "        ($w (quote " ++ render (lawsTerm laws) ++ "))\n" ++
  "        ($x (quote " ++ render (encodePattern left) ++ "))\n" ++
  "        ($y (quote " ++ render (encodePattern right) ++ "))\n" ++
  "        ($l (gslt:canon:canonical $t $w LNil $x))\n" ++
  "        ($r (gslt:canon:canonical $t $w LNil $y)))\n" ++
  "  (println! (CanonicalControl " ++ reprStr label ++ " (== (== $l $r) " ++ expected ++ "))))"

/-- The model normal form: the Lean `Wrappers.modelNormal` under rho's quote and drop. -/
def modelControl (label : String) (laws : List Laws) (pattern : Pattern) : String :=
  "!(let* (($t (quote " ++ render tableTerm ++ "))\n" ++
  "        ($l (quote " ++ render (lawsTerm laws) ++ "))\n" ++
  "        ($x (quote " ++ render (encodePattern pattern) ++ "))\n" ++
  "        ($r (gslt:canon:model-normal $t \"NQuote\" \"PDrop\" $l $x)))\n" ++
  "  (println! (CanonicalControl " ++ reprStr label ++ " (== $r (quote " ++
    render (encodePattern (Wrappers.modelNormal laws rhoPresentation pattern)) ++ ")))))"

def p1 : Pattern := output (quote zero) zero
def p2 : Pattern := input (quote zero) (drop (.bvar 0))
def p3 : Pattern := drop (quote zero)
def p4 : Pattern := output (.fvar "a") (drop (.fvar "b"))

def controls : List String := [
  canonControl "leaf" zero,
  canonControl "sorted" (bag [p1, p2, p3]),
  canonControl "nested-sorted" (bag [bag [p2, p1], p3]),
  canonControl "vec-order-kept" (vec [p1, p3, p2]),
  canonControl "set-sorted" (set [p3, p1]),
  canonControl "under-binder" (input (quote zero) (bag [output (.bvar 0) zero, drop (.bvar 0)])),
  canonControl "free-names" (bag [p4, output (.fvar "b") zero, drop (.fvar "a")]),
  canonControl "indices" (bag [.bvar 3, .bvar 1, .bvar 2]),
  canonicalControl "unit-removed" rhoLaws (bag [zero, p1]),
  canonicalControl "flattened-sorted" rhoLaws (bag [bag [p1, zero], p2, p3]),
  canonicalControl "quote-bag" rhoLaws (output (quote (bag [p3, zero, p1])) zero),
  sameControl "commuted-one-form" rhoLaws (bag [p1, p2, p3]) (bag [p3, bag [p2, zero], p1]),
  sameControl "different-two-forms" rhoLaws (bag [p1, p2]) (bag [p1, p3]),
  sameControl "multiplicity-kept" rhoLaws (bag [p1, p1, p2]) (bag [p1, p2, p2]),
  canonControl "set-dedup" (set [p1, p3, p1]),
  canonControl "set-nested-dedup" (set [bag [p1, p2], bag [p2, p1]]),
  canonControl "set-under-vec" (vec [set [p1, p1], set [p1]]),
  canonicalControl "set-dedup-after-laws" rhoLaws (set [bag [zero, p1], bag [p1, zero]]),
  sameControl "set-multiplicity-dropped" rhoLaws (set [p1, p1, p2]) (set [p1, p2]),
  sameControl "set-of-bags-two-forms" rhoLaws (set [bag [p1, p1]]) (set [bag [p1]]),
  modelControl "model-set-without-law" rhoLaws (set [bag [zero, p1], p1]),
  modelControl "model-set-with-law" setLaws (set [set [p1], p1, p1])]

#eval IO.println ("; Expected values are the Lean canonical forms (CanonicalBags.canon, CanonicalBags.lawNormal) and model normal forms (Wrappers.modelNormal).\n" ++
  String.intercalate "\n" controls)
