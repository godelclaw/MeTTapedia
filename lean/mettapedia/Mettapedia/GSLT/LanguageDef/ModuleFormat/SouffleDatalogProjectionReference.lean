import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogScalars

/-! Independent structural projection of source constructor data.
Literal and identifier subtrees are copied exactly; no numeric or escape
interpretation takes place here. Raw projection checks constructor layout.
Source typing and the authored compiler relation are separate contracts. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Reference

open Mettapedia.OSLF.MeTTaIL.Syntax

def vector (values : List Pattern) : Pattern := .collection .vec values none
def program (statements : List Pattern) : Pattern := .apply "Program" [vector statements]
def tuple (arguments : List Pattern) : Pattern := .apply "Tuple" [vector arguments]
def groundTuple (values : List Pattern) : Pattern := .apply "GroundTuple" [vector values]
def projectedAttributes (values : List Pattern) : Pattern := .apply "ProjectedAttributes" [vector values]
def projectedBody (values : List Pattern) : Pattern := .apply "ProjectedBody" [vector values]
def relation (source : Pattern) : Pattern := .apply "Relation" [source]

def constant? : Pattern → Option Pattern
  | .apply "dl-src:constant-symbol" [source] => some (.apply "SymbolValue" [source])
  | .apply "dl-src:constant-integer" [source] => some (.apply "IntegerValue" [source])
  | .apply "dl-src:constant-unsigned" [source] => some (.apply "UnsignedValue" [source])
  | .apply "dl-src:constant-float" [source] => some (.apply "FloatValue" [source])
  | _ => none

def term? : Pattern → Option Pattern
  | .apply "dl-src:term-variable" [source] => some (.apply "VariableArgument" [.apply "Variable" [source]])
  | .apply "dl-src:term-anonymous" [] => some (.apply "AnonymousArgument" [])
  | .apply "dl-src:term-constant" [source] => (constant? source).map fun value => .apply "ValueArgument" [value]
  | _ => none

def constants? : Pattern → Option (List Pattern)
  | .apply "dl-src:constants-empty" [] => some []
  | .apply "dl-src:constants-one" [source, _] => (constant? source).map (· :: [])
  | .apply "dl-src:constants-more" [head, _, _, tail] => do
      let first ← constant? head
      let rest ← constants? tail
      pure (first :: rest)
  | _ => none

def terms? : Pattern → Option (List Pattern)
  | .apply "dl-src:terms-empty" [] => some []
  | .apply "dl-src:terms-one" [source, _] => (term? source).map (· :: [])
  | .apply "dl-src:terms-more" [head, _, _, tail] => do
      let first ← term? head
      let rest ← terms? tail
      pure (first :: rest)
  | _ => none

def comparisonOperator? (source left right : Pattern) : Option Pattern :=
  match source with
  | .apply "dl-src:comparison-equal" [] => some (.apply "Equal" [left,right])
  | .apply "dl-src:comparison-different" [] => some (.apply "Different" [left,right])
  | .apply "dl-src:comparison-less" [] => some (.apply "Less" [left,right])
  | .apply "dl-src:comparison-less-equal" [] => some (.apply "LessEqual" [left,right])
  | .apply "dl-src:comparison-greater" [] => some (.apply "Greater" [left,right])
  | .apply "dl-src:comparison-greater-equal" [] => some (.apply "GreaterEqual" [left,right])
  | _ => none

def comparison? : Pattern → Option Pattern
  | .apply "dl-src:comparison" [left, _, operator, _, right] => do
      let first ← term? left
      let second ← term? right
      comparisonOperator? operator first second
  | _ => none

def atom? : Pattern → Option (Pattern × Pattern)
  | .apply "dl-src:atom" [name, _, _, arguments] =>
      (terms? arguments).map fun values => (relation name, tuple values)
  | _ => none

def groundAtom? : Pattern → Option Pattern
  | .apply "dl-src:ground-atom" [name, _, _, arguments] =>
      (constants? arguments).map fun values => .apply "GroundFact" [relation name, groundTuple values]
  | _ => none

def positiveLiteral? : Pattern → Option Pattern
  | .apply "dl-src:positive-atom" [source] =>
      (atom? source).map fun (name, arguments) => .apply "PositiveAtom" [name, arguments]
  | .apply "dl-src:positive-comparison" [source] =>
      (comparison? source).map fun value => .apply "Comparison" [value]
  | _ => none

def body? : Pattern → Option (List Pattern)
  | .apply "dl-src:body-one" [source, _] => (positiveLiteral? source).map (· :: [])
  | .apply "dl-src:body-more" [source, _, _, tail] => do
      let first ← positiveLiteral? source
      let rest ← body? tail
      pure (first :: rest)
  | _ => none

def fact? : Pattern → Option Pattern
  | .apply "dl-src:fact" [source, _] => groundAtom? source
  | _ => none

def rule? : Pattern → Option Pattern
  | .apply "dl-src:rule" [head, _, _, body] => do
      let (name, arguments) ← atom? head
      let literals ← body? body
      pure (.apply "PositiveRule" [.apply "Clause" [name, arguments, vector literals]])
  | _ => none

def attributeType? : Pattern → Option Pattern
  | .apply "dl-src:type-symbol" [] => some (.apply "SymbolType" [])
  | .apply "dl-src:type-number" [] => some (.apply "NumberType" [])
  | .apply "dl-src:type-unsigned" [] => some (.apply "UnsignedType" [])
  | .apply "dl-src:type-float" [] => some (.apply "FloatType" [])
  | _ => none

def attribute? : Pattern → Option Pattern
  | .apply "dl-src:attr" [identifier, _, _, sourceType] =>
      (attributeType? sourceType).map fun targetType => .apply "Attribute" [identifier, targetType]
  | _ => none

def attributes? : Pattern → Option (List Pattern)
  | .apply "dl-src:attributes-empty" [] => some []
  | .apply "dl-src:attributes-one" [source, _] => (attribute? source).map (· :: [])
  | .apply "dl-src:attributes-more" [source, _, _, tail] => do
      let first ← attribute? source
      let rest ← attributes? tail
      pure (first :: rest)
  | _ => none

def declaration (identifier : Pattern) (attributes : List Pattern) : Pattern :=
  .apply "Declaration" [.apply "RelationDeclaration"
    [relation (.apply "dl-src:qualified-name-one" [identifier]), vector attributes]]

def relationsInto? (source : Pattern) (attributes tail : List Pattern) : Option (List Pattern) :=
  match source with
  | .apply "dl-src:relations-one" [identifier] => some (declaration identifier attributes :: tail)
  | .apply "dl-src:relations-more" [identifier, _, _, rest] =>
      (relationsInto? rest attributes tail).map (declaration identifier attributes :: ·)
  | _ => none

def itemInto? (source : Pattern) (tail : List Pattern) : Option (List Pattern) :=
  match source with
  | .apply "dl-src:item-declaration"
      [.apply "dl-src:declaration" [_, relations, _, _, attributes]] => do
      let fields ← attributes? attributes
      relationsInto? relations fields tail
  | .apply "dl-src:item-fact" [source] => (fact? source).map (· :: tail)
  | .apply "dl-src:item-rule" [source] => (rule? source).map (· :: tail)
  | .apply "dl-src:item-input" [.apply "dl-src:input" [_, name]] =>
      some (.apply "InputRelation" [relation name] :: tail)
  | .apply "dl-src:item-output" [.apply "dl-src:output" [_, name]] =>
      some (.apply "OutputRelation" [relation name] :: tail)
  | _ => none

def itemsInto? (source : Pattern) (tail : List Pattern) : Option (List Pattern) :=
  match source with
  | .apply "dl-src:items-empty" [] => some tail
  | .apply "dl-src:items-more" [head, _, rest] => do
      let afterTail ← itemsInto? rest tail
      itemInto? head afterTail
  | _ => none

def projectProgram? : Pattern → Option Pattern
  | .apply "dl-src:program" [_, items] => (itemsInto? items []).map program
  | _ => none

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.Reference
