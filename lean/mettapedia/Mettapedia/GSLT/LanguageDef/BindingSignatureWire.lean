import Mettapedia.GSLT.LanguageDef.BindingSignature
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.OSLF.Syntax.BindingWireCodec
import Mettapedia.OSLF.Syntax.BindingWireBinary
import Mettapedia.OSLF.Syntax.BindingEqualityWire

/-!
# Exact descriptors for the original authored binding signature

The descriptor codec is indexed by the literal authored language inventory.
Row indices select complete original rows, including metadata omitted by raw
pattern erasure. The six source operators retain their original type and
binding arity; the existing generic codec owns all Term/Args recursion.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.Wire
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.WireCodec

private abbrev Physical := Mettapedia.GSLT.LanguageDef.CettaWire.Term

mutual
private def putPhysical : Physical → Data
  | .symbol name => .pair (.atom 0) (Codec.string.put name)
  | .string value => .pair (.atom 1) (Codec.string.put value)
  | .natural value => .pair (.atom 2) (.atom value)
  | .application head arguments => .pair (.atom 3) (.pair (Codec.string.put head) (putPhysicalList arguments))
private def putPhysicalList : List Physical → Data
  | [] => .atom 0
  | head :: tail => .pair (putPhysical head) (putPhysicalList tail)
end

mutual
private def getPhysical : Data → Option Physical
  | .pair (.atom 0) value => (Codec.string.get value).map (fun name => .symbol name)
  | .pair (.atom 1) value => (Codec.string.get value).map (fun text => .string text)
  | .pair (.atom 2) (.atom value) => some (.natural value)
  | .pair (.atom 3) (.pair head arguments) => do
      return .application (← Codec.string.get head) (← getPhysicalList arguments)
  | _ => none
private def getPhysicalList : Data → Option (List Physical)
  | .atom 0 => some []
  | .pair head tail => do return (← getPhysical head) :: (← getPhysicalList tail)
  | _ => none
end

mutual
private theorem get_putPhysical : ∀ value, getPhysical (putPhysical value) = some value
  | .symbol name => by simp only [putPhysical, getPhysical, Codec.string.get_put]; rfl
  | .string value => by simp only [putPhysical, getPhysical, Codec.string.get_put]; rfl
  | .natural value => rfl
  | .application head arguments => by
      simp only [putPhysical, getPhysical, Codec.string.get_put, get_putPhysicalList arguments]
      rfl
private theorem get_putPhysicalList : ∀ values, getPhysicalList (putPhysicalList values) = some values
  | [] => rfl
  | head :: tail => by
      simp only [putPhysicalList, getPhysicalList, get_putPhysical head, get_putPhysicalList tail]
      rfl
end

def physicalCodec : Codec Physical := ⟨putPhysical, getPhysical, get_putPhysical⟩

def typeCodec : Codec TypeExpr := physicalCodec.mapped
  InferenceCettaWire.AuthoredRule.typeTerm InferenceCettaWire.AuthoredRule.decodeType?
  InferenceCettaWire.AuthoredRule.decodeType?_typeTerm

def kindCodec : Codec CollType := physicalCodec.mapped
  InferenceCettaWire.encodeCollectionType InferenceCettaWire.decodeCollectionType
  InferenceCettaWire.decodeCollectionType_encodeCollectionType

/-- Read the original scope constructor from its exact declared indices.
The count of a multiple binder is the actual submitted binder-list length. -/
def scope? (parameter : TermParam) (bound : List TypeExpr) (result : TypeExpr) :
    Option (ParameterScope parameter bound result) :=
  match parameter with
  | .simple name type =>
      if boundSame : [] = bound then
        if resultSame : type = result then some (boundSame ▸ resultSame ▸ .simple name type)
        else none
      else none
  | .abstractionNamed binder name (.arrow domain codomain) =>
      if boundSame : [domain] = bound then
        if resultSame : codomain = result then
          some (boundSame ▸ resultSame ▸ .abstraction binder name domain codomain)
        else none
      else none
  | .abstractionNamed binder name (.base sort) =>
      if boundSame : [.base sort] = bound then
        if resultSame : .base sort = result then
          some (boundSame ▸ resultSame ▸ .abstractionBase binder name sort)
        else none
      else none
  | .multiAbstractionNamed names name (.arrow (.multiBinder domain) codomain) =>
      if boundSame : List.replicate bound.length domain = bound then
        if resultSame : codomain = result then
          some (boundSame ▸ resultSame ▸ .multiAbstraction names name domain codomain bound.length)
        else none
      else none
  | .multiAbstractionNamed names name (.base sort) =>
      if boundSame : List.replicate bound.length (.base sort) = bound then
        if resultSame : .base sort = result then
          some (boundSame ▸ resultSame ▸ .multiAbstractionBase names name sort bound.length)
        else none
      else none
  | _ => none

theorem scope?_complete {parameter : TermParam} {bound : List TypeExpr} {result : TypeExpr}
    (scope : ParameterScope parameter bound result) : scope? parameter bound result = some scope := by
  cases scope <;> simp [scope?, List.length_replicate]
  all_goals exact Subsingleton.elim _ _

def scopes? : (parameters : List TermParam) → (arity : List (List TypeExpr × TypeExpr)) →
    Option (ParameterScopes parameters arity)
  | [], [] => some .nil
  | parameter :: rest, (bound, result) :: tail => do
      return .cons (← scope? parameter bound result) (← scopes? rest tail)
  | _, _ => none

theorem scopes?_complete {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
    (scopes : ParameterScopes parameters arity) : scopes? parameters arity = some scopes := by
  induction scopes with
  | nil => rfl
  | cons scope rest ih => simp only [scopes?, scope?_complete scope, ih]; rfl

/-- This codec is bound to the complete fixed inventory, rather than to a
label search. An external service must retain that same inventory header. -/
def rowCodec (language : LanguageDef) : Codec {rule : GrammarRule // rule ∈ language.terms} :=
  Codec.nat.mapped (fun rule => language.terms.idxOf rule.val)
    (fun index => if bound : index < language.terms.length then
      some ⟨language.terms[index], List.getElem_mem bound⟩ else none)
    (fun rule => by
      have bound := List.idxOf_lt_length_iff.mpr rule.property
      simp only [bound, dite_true]
      apply congrArg some
      exact Subtype.ext (List.getElem_idxOf bound))

/-- Literal expected-row comparison detects metadata changes even when the
printed label and typing fields coincide. -/
def checkRow (language : LanguageDef) (expected : GrammarRule) (data : Data) : Bool :=
  match (rowCodec language).get data with
  | none => false
  | some actual => decide (actual.val = expected)

theorem checkRow_exact (language : LanguageDef) (expected : GrammarRule) (data : Data) :
    checkRow language expected data = true ↔
      ∃ actual, (rowCodec language).get data = some actual ∧ actual.val = expected := by
  unfold checkRow
  split <;> simp_all

def arityCodec : Codec (List (List TypeExpr × TypeExpr)) :=
  Codec.list (Codec.prod (Codec.list typeCodec) typeCodec)

private def constructorCodec (language : LanguageDef) := Codec.prod (rowCodec language) arityCodec
private def collectionConstructorCodec (language : LanguageDef) :=
  Codec.prod (rowCodec language) (Codec.prod Codec.string (Codec.prod kindCodec (Codec.prod typeCodec (Codec.list typeCodec))))
private def arrowCodec := Codec.prod typeCodec typeCodec
private def multiCodec := Codec.prod typeCodec (Codec.prod typeCodec (Codec.list typeCodec))
private def collectionCodec := Codec.prod kindCodec (Codec.prod typeCodec (Codec.list typeCodec))

def putOperator {language : LanguageDef} : (Σ sort, Operator language sort) → Data
  | ⟨_, .constructor rule member _ (arity := arity) _⟩ =>
      .pair (.atom 0) ((constructorCodec language).put (⟨rule, member⟩, arity))
  | ⟨_, .collectionConstructor rule member parameter kind element _ count⟩ =>
      .pair (.atom 1) ((collectionConstructorCodec language).put (⟨rule, member⟩, parameter, kind, element, List.replicate count element))
  | ⟨_, .lambda domain codomain⟩ => .pair (.atom 2) (arrowCodec.put (domain, codomain))
  | ⟨_, .multiLambda domain codomain count⟩ => .pair (.atom 3) (multiCodec.put (domain, codomain, List.replicate count domain))
  | ⟨_, .subst domain codomain⟩ => .pair (.atom 4) (arrowCodec.put (domain, codomain))
  | ⟨_, .collection kind element count⟩ => .pair (.atom 5) (collectionCodec.put (kind, element, List.replicate count element))

def getOperator (language : LanguageDef) : Data → Option (Σ sort, Operator language sort)
  | .pair (.atom 0) payload => do
      let (row, arity) ← (constructorCodec language).get payload
      if ordinaryCheck : WellSorted.usesBareCollection? row.val = false then
        let ordinary : ¬ WellSorted.UsesBareCollection row.val := fun bare => by
          have checked := (WellSorted.usesBareCollection?_eq_true_iff row.val).mpr bare
          rw [ordinaryCheck] at checked
          cases checked
        let scopes ← scopes? row.val.params arity
        return ⟨_, .constructor row.val row.property ordinary scopes⟩
      else none
  | .pair (.atom 1) payload => do
      let (row, parameter, kind, element, spine) ← (collectionConstructorCodec language).get payload
      if shape : row.val.bareParams = [.simple parameter (.collection kind element)] then
        if spine.all (fun actual => decide (actual = element)) then
          return ⟨_, .collectionConstructor row.val row.property parameter kind element shape spine.length⟩
        else none
      else none
  | .pair (.atom 2) payload => do
      let (domain, codomain) ← arrowCodec.get payload
      return ⟨_, .lambda domain codomain⟩
  | .pair (.atom 3) payload => do
      let (domain, codomain, spine) ← multiCodec.get payload
      if spine.all (fun actual => decide (actual = domain)) then
        return ⟨_, .multiLambda domain codomain spine.length⟩
      else none
  | .pair (.atom 4) payload => do
      let (domain, codomain) ← arrowCodec.get payload
      return ⟨_, .subst domain codomain⟩
  | .pair (.atom 5) payload => do
      let (kind, element, spine) ← collectionCodec.get payload
      if spine.all (fun actual => decide (actual = element)) then
        return ⟨_, .collection kind element spine.length⟩
      else none
  | _ => none

private theorem repeated_types_match (type : TypeExpr) (count : Nat) :
    (List.replicate count type).all (fun actual => decide (actual = type)) = true := by
  apply List.all_eq_true.mpr
  intro actual member
  have same := List.eq_of_mem_replicate member
  simp only [same, decide_true]

theorem get_putOperator {language : LanguageDef} :
    ∀ value : (Σ sort, Operator language sort), getOperator language (putOperator value) = some value
  | ⟨_, .constructor rule member ordinary scopes⟩ => by
      have notBare : WellSorted.usesBareCollection? rule = false := by
        cases read : WellSorted.usesBareCollection? rule with
        | false => rfl
        | true => exact (ordinary ((WellSorted.usesBareCollection?_eq_true_iff rule).mp read)).elim
      simp only [putOperator, getOperator, (constructorCodec language).get_put,
        Bind.bind, Option.bind, notBare, dite_true, scopes?_complete scopes]
      rfl
  | ⟨_, .collectionConstructor rule member parameter kind element shape count⟩ => by
      simp only [putOperator, getOperator, (collectionConstructorCodec language).get_put,
        Bind.bind, Option.bind, shape, dite_true, repeated_types_match, ite_true, List.length_replicate]
      rfl
  | ⟨_, .lambda domain codomain⟩ => by
      simp only [putOperator, getOperator, arrowCodec.get_put, Bind.bind, Option.bind]
      rfl
  | ⟨_, .multiLambda domain codomain count⟩ => by
      simp only [putOperator, getOperator, multiCodec.get_put, Bind.bind, Option.bind, repeated_types_match, ite_true, List.length_replicate]
      rfl
  | ⟨_, .subst domain codomain⟩ => by
      simp only [putOperator, getOperator, arrowCodec.get_put, Bind.bind, Option.bind]
      rfl
  | ⟨_, .collection kind element count⟩ => by
      simp only [putOperator, getOperator, collectionCodec.get_put, Bind.bind, Option.bind, repeated_types_match, ite_true, List.length_replicate]
      rfl

def operatorCodec (language : LanguageDef) : Codec (Σ sort, Operator language sort) :=
  ⟨putOperator, getOperator language, get_putOperator⟩

/-- Term and argument serialization is the original generic implementation. -/
def termCodec (language : LanguageDef) (context : List TypeExpr) (sort : TypeExpr) :
    Codec (Term (signatureOf language) context sort) :=
  WireCodec.term (S := signatureOf language) (operatorCodec language) context sort

def argumentsCodec (language : LanguageDef) (context : List TypeExpr)
    (arity : List (List TypeExpr × TypeExpr)) : Codec (Args (signatureOf language) arity context) :=
  WireCodec.args (S := signatureOf language) (operatorCodec language) context arity

/-! ## Source equation packets -/

/-- The retained equation table, context and result sort determine the proof
fibre. Every term, metavariable body and simultaneous substitution is decoded
by the existing sorted binding-wire implementation. -/
def equationCodec (language : LanguageDef) {metas : List (MetaArity (signatureOf language))}
    (equations : List (EqAxiom (signatureOf language) metas))
    (context : List TypeExpr) (sort : TypeExpr) :
    Codec (EqualityCertificates.Certificate (signatureOf language) metas equations context sort) :=
  EqualityCertificates.Wire.certificate typeCodec (operatorCodec language) equations context sort

def checkEquation (language : LanguageDef) {metas : List (MetaArity (signatureOf language))}
    (equations : List (EqAxiom (signatureOf language) metas))
    {context : List TypeExpr} {sort : TypeExpr} (raw : Data)
    (left right : Term (signatureOf language) context sort) : Bool :=
  EqualityCertificates.Wire.check typeCodec (operatorCodec language) equations raw left right

theorem checkEquation_exact (language : LanguageDef)
    {metas : List (MetaArity (signatureOf language))}
    (equations : List (EqAxiom (signatureOf language) metas))
    {context : List TypeExpr} {sort : TypeExpr} (raw : Data)
    (left right : Term (signatureOf language) context sort) :
    checkEquation language equations raw left right = true ↔
      ∃ proof : EqualityCertificates.Certificate (signatureOf language) metas equations context sort,
        (equationCodec language equations context sort).put proof = raw ∧
          EqualityCertificates.check proof left right = true :=
  EqualityCertificates.Wire.check_exact (S := signatureOf language)
    typeCodec (operatorCodec language) equations raw left right

theorem checkEquation_complete (language : LanguageDef)
    {metas : List (MetaArity (signatureOf language))}
    (equations : List (EqAxiom (signatureOf language) metas))
    {context : List TypeExpr} {sort : TypeExpr}
    (left right : Term (signatureOf language) context sort) :
    EqClosure equations left right ↔ ∃ raw : Data,
      checkEquation language equations raw left right = true :=
  EqualityCertificates.Wire.check_complete (S := signatureOf language)
    typeCodec (operatorCodec language) equations left right

/-- Complete physical words must match the canonical certificate encoding;
trailing symbols and alternate scalar representations are rejected. -/
def checkEquationBinary (language : LanguageDef)
    {metas : List (MetaArity (signatureOf language))}
    (equations : List (EqAxiom (signatureOf language) metas))
    {context : List TypeExpr} {sort : TypeExpr} (word : List Binary.Alphabet)
    (left right : Term (signatureOf language) context sort) : Bool :=
  match Binary.canonicalDecodeWith (equationCodec language equations context sort) word with
  | none => false
  | some proof => EqualityCertificates.check proof left right

theorem checkEquationBinary_exact (language : LanguageDef)
    {metas : List (MetaArity (signatureOf language))}
    (equations : List (EqAxiom (signatureOf language) metas))
    {context : List TypeExpr} {sort : TypeExpr} (word : List Binary.Alphabet)
    (left right : Term (signatureOf language) context sort) :
    checkEquationBinary language equations word left right = true ↔
      ∃ proof : EqualityCertificates.Certificate (signatureOf language) metas equations context sort,
        Binary.encodeWith (equationCodec language equations context sort) proof = word ∧
          EqualityCertificates.check proof left right = true := by
  let codec := equationCodec language equations context sort
  change (match Binary.canonicalDecodeWith codec word with
    | none => false | some proof => EqualityCertificates.check proof left right) = true ↔ _
  cases decoded : Binary.canonicalDecodeWith codec word with
  | none =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨proof, encoded, _⟩
        have accepted := (Binary.canonicalDecodeWith_exact codec word proof).mpr encoded
        rw [decoded] at accepted
        cases accepted
  | some proof =>
      constructor
      · intro checked
        exact ⟨proof, (Binary.canonicalDecodeWith_exact codec word proof).mp decoded, checked⟩
      · rintro ⟨candidate, encoded, checked⟩
        have accepted := (Binary.canonicalDecodeWith_exact codec word candidate).mpr encoded
        rw [decoded] at accepted
        cases Option.some.inj accepted
        exact checked

theorem checkEquationBinary_complete (language : LanguageDef)
    {metas : List (MetaArity (signatureOf language))}
    (equations : List (EqAxiom (signatureOf language) metas))
    {context : List TypeExpr} {sort : TypeExpr}
    (left right : Term (signatureOf language) context sort) :
    EqClosure equations left right ↔ ∃ word : List Binary.Alphabet,
      checkEquationBinary language equations word left right = true := by
  constructor
  · intro derived
    obtain ⟨proof, checked⟩ := (EqualityCertificates.check_complete left right).mp derived
    exact ⟨Binary.encodeWith (equationCodec language equations context sort) proof,
      (checkEquationBinary_exact language equations _ left right).mpr ⟨proof, rfl, checked⟩⟩
  · rintro ⟨word, accepted⟩
    obtain ⟨proof, _, checked⟩ := (checkEquationBinary_exact language equations word left right).mp accepted
    exact EqualityCertificates.check_sound proof left right checked

theorem checkEquationBinary_trailing_refused (language : LanguageDef)
    {metas : List (MetaArity (signatureOf language))}
    (equations : List (EqAxiom (signatureOf language) metas))
    {context : List TypeExpr} {sort : TypeExpr}
    (proof : EqualityCertificates.Certificate (signatureOf language) metas equations context sort)
    (tail : List Binary.Alphabet) (nonempty : tail.isEmpty = false)
    (left right : Term (signatureOf language) context sort) :
    checkEquationBinary language equations
      (Binary.encodeWith (equationCodec language equations context sort) proof ++ tail) left right = false := by
  simp only [checkEquationBinary, Binary.canonicalDecodeWith_trailing_refused _ _ _ nonempty]

/-! ## Reversible literal declaration names -/

private def descriptorName {Value : Type} (scope : Lean.Name) (role : String)
    (codec : Codec Value) (value : Value) : Lean.Name :=
  .str (.str scope role) (Binary.Text.render (Binary.encodeWith codec value))

private def readDescriptorName {Value : Type} (scope : Lean.Name) (role : String)
    (codec : Codec Value) : Lean.Name → Option Value
  | .str (.str foundScope foundRole) text =>
      if foundScope = scope ∧ foundRole = role then do
        let word ← Binary.Text.parse text
        Binary.canonicalDecodeWith codec word
      else none
  | _ => none

private theorem readDescriptorName_roundtrip {Value : Type} (scope : Lean.Name) (role : String)
    (codec : Codec Value) (value : Value) :
    readDescriptorName scope role codec (descriptorName scope role codec value) = some value := by
  simp only [descriptorName, readDescriptorName, and_self, ite_true,
    Binary.Text.parse_render, Bind.bind, Option.bind, Binary.canonicalDecodeWith_encodeWith]

private theorem descriptorName_injective {Value : Type} (scope : Lean.Name) (role : String)
    (codec : Codec Value) : Function.Injective (descriptorName scope role codec) := by
  intro first second same
  have text := (Lean.Name.str.inj same).2
  have parsed := congrArg Binary.Text.parse text
  simp only [Binary.Text.parse_render, Option.some.injEq] at parsed
  exact Binary.encodeWith_injective codec parsed

/-- Names retain the complete source sort. The surrounding namespace belongs
to the fixed declaration inventory; no digest is used as identity evidence. -/
def sortName (scope : Lean.Name) (sort : TypeExpr) : Lean.Name :=
  descriptorName scope "sort" typeCodec sort

def operatorName (scope : Lean.Name) (language : LanguageDef)
    {sort : TypeExpr} (operator : Operator language sort) : Lean.Name :=
  descriptorName scope "operator" (operatorCodec language) ⟨sort, operator⟩

def readSortName (scope : Lean.Name) : Lean.Name → Option TypeExpr :=
  readDescriptorName scope "sort" typeCodec

def readOperatorName (scope : Lean.Name) (language : LanguageDef) :
    Lean.Name → Option (Σ sort, Operator language sort) :=
  readDescriptorName scope "operator" (operatorCodec language)

@[simp] theorem readSortName_sortName (scope : Lean.Name) (sort : TypeExpr) :
    readSortName scope (sortName scope sort) = some sort :=
  readDescriptorName_roundtrip scope "sort" typeCodec sort

@[simp] theorem readOperatorName_operatorName (scope : Lean.Name) (language : LanguageDef)
    {sort : TypeExpr} (operator : Operator language sort) :
    readOperatorName scope language (operatorName scope language operator) = some ⟨sort, operator⟩ :=
  readDescriptorName_roundtrip scope "operator" (operatorCodec language) ⟨sort, operator⟩

theorem sortName_injective (scope : Lean.Name) : Function.Injective (sortName scope) :=
  descriptorName_injective scope "sort" typeCodec

theorem operatorName_injective (scope : Lean.Name) (language : LanguageDef) {sort : TypeExpr} :
    Function.Injective (operatorName scope language (sort := sort)) := by
  intro first second same
  have original := descriptorName_injective scope "operator" (operatorCodec language) same
  exact eq_of_heq (Sigma.mk.inj original).2

theorem sortName_ne_operatorName (scope : Lean.Name) (language : LanguageDef)
    (sort : TypeExpr) {result : TypeExpr} (operator : Operator language result) :
    sortName scope sort ≠ operatorName scope language operator := by
  intro same
  have roles := (Lean.Name.str.inj (Lean.Name.str.inj same).1).2
  exact (by decide : ("sort" : String) ≠ "operator") roles

/-! ## Exact declaration-header metadata -/

namespace Header

private def putCarrier : CarrierKind → Nat
  | .ast => 0 | .tokenLabel => 1 | .tokenRaw => 2 | .tokenProof => 3
  | .tokenPath => 4 | .builtinInt => 5 | .builtinString => 6 | .builtinBool => 7

private def getCarrier : Nat → Option CarrierKind
  | 0 => some .ast | 1 => some .tokenLabel | 2 => some .tokenRaw | 3 => some .tokenProof
  | 4 => some .tokenPath | 5 => some .builtinInt | 6 => some .builtinString | 7 => some .builtinBool
  | _ => none

def carrierCodec : Codec CarrierKind := Codec.nat.mapped putCarrier getCarrier
  (fun carrier => by cases carrier <;> rfl)

def typeDeclarationCodec : Codec TypeDecl :=
  (Codec.prod Codec.string carrierCodec).mapped
    (fun declaration => (declaration.name, declaration.carrier))
    (fun fields => some ⟨fields.1, fields.2⟩) (fun _ => rfl)

/-- Named binder metadata uses the existing lossless source parameter wire. -/
def parameterCodec : Codec TermParam := physicalCodec.mapped
  Mettapedia.GSLT.LanguageDef.InferenceCettaWire.AuthoredRule.parameterTerm
  Mettapedia.GSLT.LanguageDef.InferenceCettaWire.AuthoredRule.decodeParameter?
  Mettapedia.GSLT.LanguageDef.InferenceCettaWire.AuthoredRule.decodeParameter?_parameterTerm

mutual
private def putItem : SyntaxItem → Data
  | .terminal text => .pair (.atom 0) (Codec.string.put text)
  | .nonTerminal name => .pair (.atom 1) (Codec.string.put name)
  | .separator text => .pair (.atom 2) (Codec.string.put text)
  | .delimiter first second => .pair (.atom 3) ((Codec.prod Codec.string Codec.string).put (first, second))
  | .op operator => .pair (.atom 4) (putOperator operator)

private def putItems : List SyntaxItem → Data
  | [] => .atom 0
  | first :: later => .pair (putItem first) (putItems later)

private def putOperator : SyntaxPatternOp → Data
  | .var name => .pair (.atom 0) (Codec.string.put name)
  | .sep name separator later => .pair (.atom 1)
      (.pair ((Codec.prod Codec.string Codec.string).put (name, separator)) (putOptionalOperator later))
  | .zip first second => .pair (.atom 2) ((Codec.prod Codec.string Codec.string).put (first, second))
  | .map source names body => .pair (.atom 3)
      (.pair (putOperator source) (.pair ((Codec.list Codec.string).put names) (putItems body)))
  | .opt body => .pair (.atom 4) (putItems body)

private def putOptionalOperator : Option SyntaxPatternOp → Data
  | none => .atom 0
  | some operator => .pair (.atom 1) (putOperator operator)
end

mutual
private def getItem : Data → Option SyntaxItem
  | .pair (.atom 0) text => (Codec.string.get text).map .terminal
  | .pair (.atom 1) name => (Codec.string.get name).map .nonTerminal
  | .pair (.atom 2) text => (Codec.string.get text).map .separator
  | .pair (.atom 3) fields => do
      let (first, second) ← (Codec.prod Codec.string Codec.string).get fields
      some (.delimiter first second)
  | .pair (.atom 4) operator => (getOperator operator).map .op
  | _ => none

private def getItems : Data → Option (List SyntaxItem)
  | .atom 0 => some []
  | .pair first later => do return (← getItem first) :: (← getItems later)
  | _ => none

private def getOperator : Data → Option SyntaxPatternOp
  | .pair (.atom 0) name => (Codec.string.get name).map .var
  | .pair (.atom 1) (.pair fields later) => do
      let (name, separator) ← (Codec.prod Codec.string Codec.string).get fields
      some (.sep name separator (← getOptionalOperator later))
  | .pair (.atom 2) fields => do
      let (first, second) ← (Codec.prod Codec.string Codec.string).get fields
      some (.zip first second)
  | .pair (.atom 3) (.pair source (.pair names body)) => do
      some (.map (← getOperator source) (← (Codec.list Codec.string).get names) (← getItems body))
  | .pair (.atom 4) body => (getItems body).map .opt
  | _ => none

private def getOptionalOperator : Data → Option (Option SyntaxPatternOp)
  | .atom 0 => some none
  | .pair (.atom 1) operator => (getOperator operator).map some
  | _ => none
end

mutual
private theorem get_putItem : ∀ item, getItem (putItem item) = some item
  | .terminal text => by simp only [getItem, putItem, Codec.string.get_put]; rfl
  | .nonTerminal name => by simp only [getItem, putItem, Codec.string.get_put]; rfl
  | .separator text => by simp only [getItem, putItem, Codec.string.get_put]; rfl
  | .delimiter first second => by simp only [getItem, putItem, Codec.get_put]; rfl
  | .op operator => by simp only [getItem, putItem, get_putOperator operator]; rfl

private theorem get_putItems : ∀ items, getItems (putItems items) = some items
  | [] => rfl
  | first :: later => by simp only [getItems, putItems, get_putItem first, get_putItems later]; rfl

private theorem get_putOperator : ∀ operator, getOperator (putOperator operator) = some operator
  | .var name => by simp only [getOperator, putOperator, Codec.string.get_put]; rfl
  | .sep name separator later => by
      simp only [getOperator, putOperator, Codec.get_put, get_putOptionalOperator later]; rfl
  | .zip first second => by simp only [getOperator, putOperator, Codec.get_put]; rfl
  | .map source names body => by
      simp only [getOperator, putOperator, get_putOperator source, Codec.get_put, get_putItems body]; rfl
  | .opt body => by simp only [getOperator, putOperator, get_putItems body]; rfl

private theorem get_putOptionalOperator : ∀ operator, getOptionalOperator (putOptionalOperator operator) = some operator
  | none => rfl
  | some operator => by simp only [getOptionalOperator, putOptionalOperator, get_putOperator operator]; rfl
end

def syntaxItemCodec : Codec SyntaxItem := ⟨putItem, getItem, get_putItem⟩
def syntaxOperatorCodec : Codec SyntaxPatternOp := ⟨putOperator, getOperator, get_putOperator⟩

private def putPolicy : Option TermEvalPolicy → Nat
  | none => 0 | some .rewrite => 1 | some .fold => 2 | some .oracle => 3
private def getPolicy : Nat → Option (Option TermEvalPolicy)
  | 0 => some none | 1 => some (some .rewrite) | 2 => some (some .fold) | 3 => some (some .oracle)
  | _ => none

def policyCodec : Codec (Option TermEvalPolicy) :=
  Codec.nat.mapped putPolicy getPolicy (fun policy => by
    cases policy with | none => rfl | some policy => cases policy <;> rfl)

private def putUnit : Option String → Data
  | none => .atom 0 | some name => .pair (.atom 1) (Codec.string.put name)
private def getUnit : Data → Option (Option String)
  | .atom 0 => some none
  | .pair (.atom 1) name => (Codec.string.get name).map some
  | _ => none
private theorem get_putUnit : ∀ unit, getUnit (putUnit unit) = some unit
  | none => rfl | some name => by simp only [getUnit, putUnit, Codec.string.get_put]; rfl

private def putAlgebra : Option CollectionAlgebra → Data
  | none => .atom 0
  | some algebra => .pair (.atom 1)
      (.pair (.atom (if algebra.flatten then 1 else 0)) (putUnit algebra.unit))
private def getAlgebra : Data → Option (Option CollectionAlgebra)
  | .atom 0 => some none
  | .pair (.atom 1) (.pair (.atom flag) unit) => do
      let flatten ← match flag with | 0 => some false | 1 => some true | _ => none
      some (some ⟨flatten, ← getUnit unit⟩)
  | _ => none
private theorem get_putAlgebra : ∀ algebra, getAlgebra (putAlgebra algebra) = some algebra
  | none => rfl
  | some ⟨flatten, unit⟩ => by
    cases flatten <;> simp only [getAlgebra, putAlgebra, get_putUnit]; all_goals rfl

def algebraCodec : Codec (Option CollectionAlgebra) := ⟨putAlgebra, getAlgebra, get_putAlgebra⟩

private def putRepresentation : CollectionRepresentation → Nat
  | .bare => 0 | .wrapped => 1
private def getRepresentation : Nat → Option CollectionRepresentation
  | 0 => some .bare | 1 => some .wrapped | _ => none

def representationCodec : Codec CollectionRepresentation :=
  Codec.nat.mapped putRepresentation getRepresentation (fun mode => by cases mode <;> rfl)

/-- Full original grammar metadata is retained, including syntax operators,
evaluation policy and collection algebra omitted by typing-only wires. -/
def grammarRuleCodec : Codec GrammarRule :=
  (Codec.prod Codec.string (Codec.prod Codec.string (Codec.prod (Codec.list parameterCodec)
    (Codec.prod (Codec.list syntaxItemCodec)
      (Codec.prod policyCodec (Codec.prod algebraCodec representationCodec)))))).mapped
    (fun row => (row.label, row.category, row.params, row.syntaxPattern, row.evalPolicy?,
      row.algebra?, row.collectionRepresentation))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
      fields.2.2.2.2.1, fields.2.2.2.2.2.1, fields.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-- This footprint authorizes the source binding signature and its declared
collection equations. It includes the language name, types and complete
constructor rows. It does not authorize arbitrary source rewrite rules. -/
def codec : Codec (String × List TypeDecl × List GrammarRule) :=
  Codec.prod Codec.string (Codec.prod (Codec.list typeDeclarationCodec) (Codec.list grammarRuleCodec))

def value (language : LanguageDef) : String × List TypeDecl × List GrammarRule :=
  (language.name, language.types, language.terms)

theorem encode_injective : Function.Injective codec.put := codec.put_injective

end Header

end Mettapedia.GSLT.LanguageDef.BindingSyntax.Wire
