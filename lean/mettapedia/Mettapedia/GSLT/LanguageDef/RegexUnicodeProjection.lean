import Mettapedia.GSLT.LanguageDef.RegexClassMaterialization
import Mettapedia.GSLT.LanguageDef.RegexClassSyntax

/-!
# Unicode interpretation of the actual regex CST family

The structural attributed projector is reused. This view supplies the newer
property, hexadecimal and shorthand forms and interprets case flags through
the proved symbolic-class interval lowerer. Explicit properties remain
Unicode properties even with `u` disabled; shorthand classes, word assertions
and simple folding use the selected mode. The original scalar alphabet is
unchanged. Extended-mode source preparation precedes this CST boundary.

The catalog is supplied data. The generic lowerer is proved correct; no claim
about a particular external Unicode file follows from choosing its version.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexUnicodeProjection

open RegexSourceProjection
open RegexClassInterpretation (Expr meaning)
open RegexClassMaterialization (Catalog Ranges provider lower)
open RegexSelection (Pattern)
open CettaWire (Term)
open Mettapedia.GSLT.Parsing.ParserProfileSemantics (isUnicodeScalar)

def asciiFoldClasses : List (List Nat) := (List.range 26).map (fun offset => [65 + offset, 97 + offset])

def selectedCatalog (catalog : Catalog) (flags : Flags) : Catalog :=
  if flags.unicode then catalog else { catalog with folds := asciiFoldClasses }

def text? (one more : String) : Nat → Term → Option String
  | 0, _ => none
  | fuel + 1, tree => do
      let (name, children) ← fields? tree
      if name = one then
        let [value] := children | none
        let point ← scalar? value
        some (String.singleton (Char.ofNat point))
      else if name = more then
        let [value, rest] := children | none
        let point ← scalar? value
        let after ← text? one more fuel rest
        some (String.singleton (Char.ofNat point) ++ after)
      else none

def propertyName? (fuel : Nat) (tree : Term) : Option String :=
  text? "re-src:property-one" "re-src:property-more" fuel tree

def hexDigit? (point : Nat) : Option Nat :=
  if 48 ≤ point ∧ point ≤ 57 then some (point - 48)
  else if 65 ≤ point ∧ point ≤ 70 then some (point - 55)
  else if 97 ≤ point ∧ point ≤ 102 then some (point - 87)
  else none

def hexAux? : Nat → Term → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, tree, before => do
      let (name, children) ← fields? tree
      match name, children with
      | "re-src:hex-one", [digit] => do
          let value ← hexDigit? (← scalar? digit)
          some (before * 16 + value)
      | "re-src:hex-more", [digit, rest] => do
          let value ← hexDigit? (← scalar? digit)
          hexAux? fuel rest (before * 16 + value)
      | _, _ => none

def hex? (fuel : Nat) (tree : Term) : Option Nat :=
  (hexAux? fuel tree 0).filter isUnicodeScalar

def asciiWord : Expr :=
  .union (.range 65 90) (.union (.range 97 122) (.union (.range 48 57) (.range 95 95)))

def unicodeWord : Expr :=
  .union (.property "Alphabetic") (.union (.property "M")
    (.union (.property "Nd") (.union (.property "Pc") (.property "Join_Control"))))

def shorthand (flags : Flags) (kind : Char) : Option Expr :=
  match kind with
  | 'd' => some (if flags.unicode then .property "Nd" else .range 48 57)
  | 'w' => some (if flags.unicode then unicodeWord else asciiWord)
  | 's' => some (if flags.unicode then .property "White_Space"
      else .union (.range 9 13) (.range 32 32))
  | _ => none

def caseClass (flags : Flags) (negative : Bool) (positive : Expr) : Expr :=
  let closed := if flags.insensitive then .fold positive else positive
  if negative then .complement closed else closed

def escapedClass? (flags : Flags) (point : Nat) : Option Expr :=
  match point with
  | 100 => shorthand flags 'd'
  | 119 => shorthand flags 'w'
  | 115 => shorthand flags 's'
  | 68 => (caseClass flags true ·) <$> shorthand flags 'd'
  | 87 => (caseClass flags true ·) <$> shorthand flags 'w'
  | 83 => (caseClass flags true ·) <$> shorthand flags 's'
  | 98 => some (.range 8 8)
  | other => do
      let .literal scalar ← escaped? other | none
      some (.range scalar scalar)

def classes? (flags : Flags) : Nat → Term → Option Expr
  | 0, _ => none
  | fuel + 1, tree => do
      let (name, children) ← fields? tree
      match name, children with
      | "re-src:class-empty", [] | "re-src:class-tail-empty", [] => some .empty
      | "re-src:class-tail-dash", [] => some (.range 45 45)
      | "re-src:class-initial-dash", [rest] => (.union (.range 45 45) ·) <$> classes? flags fuel rest
      | "re-src:class-first", [first, rest] | "re-src:class-tail", [first, rest] => do
          if setOperation? first rest then none else
            some (.union (← classes? flags fuel first) (← classes? flags fuel rest))
      | "re-src:first-char", [scalar] | "re-src:class-char", [scalar] => do
          let point ← scalar? scalar
          some (.range point point)
      | "re-src:first-range", [low, high] | "re-src:class-range", [low, high] => do
          let low ← scalar? low
          let high ← scalar? high
          if low ≤ high then some (.range low high) else none
      | "re-src:first-escape", [scalar] | "re-src:class-escape", [scalar] =>
          escapedClass? flags (← scalar? scalar)
      | "re-src:first-property", [name] | "re-src:class-property", [name] =>
          (Expr.property ·) <$> propertyName? fuel name
      | "re-src:first-not-property", [name] | "re-src:class-not-property", [name] =>
          (caseClass flags true ∘ Expr.property) <$> propertyName? fuel name
      | "re-src:first-hex", [digits] | "re-src:class-hex", [digits] => do
          let point ← hex? fuel digits
          some (.range point point)
      | _, _ => none

def classPattern? (catalog : Catalog) (flags : Flags) (negative : Bool) (positive : Expr) : Option Pattern :=
  Pattern.class_ <$> lower (selectedCatalog catalog flags) (caseClass flags negative positive)

/-- Range endpoints must denote one scalar, not a shorthand set. -/
def endpoint? (fuel : Nat) (tree : Term) : Option Nat := do
  let (name, children) ← fields? tree
  match name, children with
  | "re-src:endpoint-amp", [] | "re-src:first-endpoint-amp", [] => some 38
  | "re-src:endpoint-tilde", [] | "re-src:first-endpoint-tilde", [] => some 126
  | "re-src:endpoint-open", [] | "re-src:first-endpoint-open", [] => some 91
  | "re-src:endpoint-char", [source] | "re-src:first-endpoint-char", [source] => scalar? source
  | "re-src:endpoint-hex", [digits] | "re-src:first-endpoint-hex", [digits]
  | "re-src:endpoint-unicode-hex", [digits] | "re-src:first-endpoint-unicode-hex", [digits] => hex? fuel digits
  | "re-src:endpoint-escape", [source] | "re-src:first-endpoint-escape", [source] => do
      let point ← scalar? source
      if point = 98 then some 8 else do
        let .literal value ← escaped? point | none
        some value
  | _, _ => scalar? tree

/-- Folding is applied at positive leaves, before subtraction or negation. -/
def classAtom? (flags : Flags) (fuel : Nat) (tree : Term) : Option Expr := do
  let (name, children) ← fields? tree
  match name, children with
  | "re-src:class-empty", [] | "re-src:class-tail-empty", []
  | "re-src:class-amp-empty", [] | "re-src:class-tilde-empty", [] => some .empty
  | "re-src:class-tail-dash", [] => some (caseClass flags false (.range 45 45))
  | "re-src:first-open", [] => some (caseClass flags false (.range 91 91))
  | "re-src:first-char", [source] | "re-src:class-char", [source] => do
      let point ← scalar? source
      some (caseClass flags false (.range point point))
  | "re-src:first-range", [low, high] | "re-src:class-range", [low, high] => do
      let low ← endpoint? fuel low
      let high ← endpoint? fuel high
      if low ≤ high then some (caseClass flags false (.range low high)) else none
  | "re-src:first-escape", [source] | "re-src:class-escape", [source] => do
      let point ← scalar? source
      if point = 68 ∨ point = 87 ∨ point = 83 then escapedClass? flags point
      else (caseClass flags false ·) <$> escapedClass? flags point
  | "re-src:first-property", [source] | "re-src:class-property", [source] =>
      (caseClass flags false ∘ Expr.property) <$> propertyName? fuel source
  | "re-src:first-not-property", [source] | "re-src:class-not-property", [source] =>
      (caseClass flags true ∘ Expr.property) <$> propertyName? fuel source
  | "re-src:first-hex", [digits] | "re-src:class-hex", [digits] => do
      let point ← hex? fuel digits
      some (caseClass flags false (.range point point))
  | _, _ => none

def algebraPattern? (catalog : Catalog) (flags : Flags) (fuel : Nat) (tree : Term) : Option Pattern := do
  let parsed ← RegexClassSyntax.project (classAtom? flags fuel) flags.insensitive fuel tree
  Pattern.class_ <$> lower (selectedCatalog catalog flags) (RegexClassSyntax.elaborate parsed)

def literalPattern? (catalog : Catalog) (flags : Flags) (scalar : Nat) : Option Pattern :=
  if flags.insensitive then classPattern? catalog flags false (.range scalar scalar)
  else some (.literal scalar)

def ordinaryEscapePattern? (catalog : Catalog) (flags : Flags) (point : Nat) : Option Pattern :=
  match point with
  | 100 => do classPattern? catalog flags false (← shorthand flags 'd')
  | 119 => do classPattern? catalog flags false (← shorthand flags 'w')
  | 115 => do classPattern? catalog flags false (← shorthand flags 's')
  | 68 => do classPattern? catalog flags true (← shorthand flags 'd')
  | 87 => do classPattern? catalog flags true (← shorthand flags 'w')
  | 83 => do classPattern? catalog flags true (← shorthand flags 's')
  | other => do
      let escaped ← escaped? other
      match escaped with
      | .literal scalar => literalPattern? catalog flags scalar
      | assertion => some assertion

def view? (catalog : Catalog) (fuel : Nat) (flags : Flags) (tree : Term) : Option Form := do
  let (name, children) ← fields? tree
  match name, children with
  | "re-src:literal", [scalar] =>
      Form.leaf <$> literalPattern? catalog flags (← scalar? scalar)
  | "re-src:property", [name] =>
      Form.leaf <$> classPattern? catalog flags false (.property (← propertyName? fuel name))
  | "re-src:not-property", [name] =>
      Form.leaf <$> classPattern? catalog flags true (.property (← propertyName? fuel name))
  | "re-src:hex", [digits] | "re-src:unicode-hex", [digits] =>
      Form.leaf <$> literalPattern? catalog flags (← hex? fuel digits)
  | "re-src:escape", [source] => do
      let point ← scalar? source
      if point = 98 ∨ point = 66 then
        some (.leaf (.assertion (if point = 98 then
          (if flags.unicode then "word-boundary" else "ascii-word-boundary") else
          (if flags.unicode then "not-word-boundary" else "not-ascii-word-boundary"))))
      else Form.leaf <$> ordinaryEscapePattern? catalog flags point
  | "re-src:class", [_] | "re-src:class-not", [_] =>
      Form.leaf <$> algebraPattern? catalog flags fuel tree
  | _, _ => RegexSourceProjection.view? fuel flags tree

/-- The actual class result is licensed by the symbolic source expression,
not merely by a matching constructor name in a module file. -/
theorem classPattern_exact (catalog : Catalog) (flags : Flags) (negative : Bool)
    (positive : Expr) (ranges : Ranges)
    (computed : classPattern? catalog flags negative positive = some (.class_ ranges)) (scalar : Nat) :
    RegexSourceProjection.InRanges scalar ranges ↔
      scalar ∈ meaning (provider (selectedCatalog catalog flags)) (caseClass flags negative positive) := by
  unfold classPattern? at computed
  cases lowered : lower (selectedCatalog catalog flags) (caseClass flags negative positive) with
  | none => simp [lowered] at computed
  | some actual =>
      simp [lowered] at computed
      subst ranges
      exact RegexClassMaterialization.lower_exact _ _ actual lowered scalar

theorem attributed_projection_exact (catalog : Catalog) (payloadDepth : Nat)
    (state : State) (tree : Term) (answer : Output) :
    (∃ depth, project (view? catalog payloadDepth) depth state tree = some answer) ↔
      Projects (view? catalog payloadDepth) state tree answer := project_iff _ _ _ _

theorem algebra_projection_exact (catalog : Catalog) (flags : Flags) (fuel : Nat)
    (tree : Term) (parsed : RegexClassSyntax.Syntax) (ranges : Ranges)
    (selected : RegexClassSyntax.project (classAtom? flags fuel) flags.insensitive fuel tree = some parsed)
    (compiled : lower (selectedCatalog catalog flags) (RegexClassSyntax.elaborate parsed) = some ranges)
    (scalar : Nat) :
    RegexClassSyntax.Projects (classAtom? flags fuel) flags.insensitive tree parsed ∧
      (InRanges scalar ranges ↔ scalar ∈ RegexClassSyntax.meaning
        (provider (selectedCatalog catalog flags)) parsed) :=
  RegexClassSyntax.selected_intervals_exact _ _ _ _ _ _ ⟨fuel, selected⟩ compiled scalar

theorem unicode_off_preserves_explicit_properties (catalog : Catalog) (flags : Flags)
    (name : String) : (selectedCatalog catalog flags).properties name = catalog.properties name := by
  unfold selectedCatalog
  split_ifs <;> rfl

namespace Controls

private def catalog : Catalog where
  version := "example"
  properties := fun name => if name = "Nd" then some [(1632, 1641)]
    else if name = "Alphabetic" then some [(65, 90), (97, 122), (955, 955)]
    else if name = "M" then some [(769, 769)]
    else if name = "Pc" then some [(95, 95)]
    else if name = "Join_Control" then some [(8204, 8205)]
    else if name = "White_Space" then some [(9, 13), (32, 32), (160, 160)] else none
  folds := [[65, 97], [75, 107, 8490]]

private def escape (point : Nat) : Term := cst "re-src:escape" [cst "re-src:lex-escaped" [cp point]]
private def scalar (point : Nat) : Term := cst "re-src:lex-class" [cp point]

theorem unicode_and_ascii_digits_have_distinct_declared_meanings :
    ((shorthand {} 'd').bind (classPattern? catalog {} false)).map
      (fun pattern => match pattern with | .class_ ranges => RegexClassInterpretation.testRanges ranges 1635 | _ => false) = some true ∧
    ((shorthand { unicode := false } 'd').bind (classPattern? catalog { unicode := false } false)).map
      (fun pattern => match pattern with | .class_ ranges => RegexClassInterpretation.testRanges ranges 1635 | _ => false) = some false := by decide

theorem negative_class_folds_before_complement :
    (classPattern? catalog { insensitive := true } true (.range 97 97)).map
      (fun pattern => match pattern with | .class_ ranges => RegexClassInterpretation.testRanges ranges 65 | _ => false) = some false ∧
    (classPattern? catalog { insensitive := true } true (.range 97 97)).map
      (fun pattern => match pattern with | .class_ ranges => RegexClassInterpretation.testRanges ranges 98 | _ => false) = some true := by decide

theorem word_assertion_mode_and_class_backspace_are_distinct :
    (view? catalog 20 { unicode := false } (escape 98)).map
      (fun form => match form with | .leaf (.assertion name) => name | _ => "") = some "ascii-word-boundary" ∧
    classes? {} 20 (cst "re-src:class-escape" [scalar 98]) = some (.range 8 8) := by decide

theorem hexadecimal_digit_profile_is_explicit :
    hexDigit? 1633 = none ∧ hexDigit? 71 = none ∧
    (hexAux? 8 (cst "re-src:hex-one" [cp 70]) 0) = some 15 := by decide

private def hexDigits : List Nat → Term
  | [] => cst "re-src:hex-one" [cp 48]
  | [point] => cst "re-src:hex-one" [cp point]
  | point :: rest => cst "re-src:hex-more" [cp point, hexDigits rest]

theorem hex_scalar_rejects_surrogate_and_above_universe :
    hex? 20 (hexDigits [68, 56, 48, 48]) = none ∧
    hex? 20 (hexDigits [49, 49, 48, 48, 48, 48]) = none ∧
    hex? 20 (hexDigits [51, 66, 66]) = some 955 := by decide

end Controls

#print axioms classPattern_exact
#print axioms attributed_projection_exact
#print axioms unicode_off_preserves_explicit_properties

end Mettapedia.GSLT.LanguageDef.RegexUnicodeProjection
