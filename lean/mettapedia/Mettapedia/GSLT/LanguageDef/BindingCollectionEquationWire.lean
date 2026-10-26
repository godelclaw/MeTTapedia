import Mettapedia.GSLT.LanguageDef.BindingSignatureWire
import Mettapedia.GSLT.LanguageDef.BindingCollectionEquationGenerators
import Mettapedia.GSLT.LanguageDef.CertificateDataEncoding

/-!
# Checked source packets for the original collection equation family

Law packets retain the declaring row and original raw decomposition. Kind
packets check the actual declared parameter/type occurrence and complete raw
data typing through the existing Term codec. Algebra variants retain their
base-sort endpoint, row, switches and unit inventory checks. Literal endpoints
are checked in every case; external packets supply no authorization proof.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationWire

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.WireCodec
open EquationSemantics CollectionEquationFamily

variable {language : LanguageDef}

private def patternCodec := CertificateDataEncoding.patternCodec
private def patternsCodec := Codec.list patternCodec
private def pairPatterns := Codec.prod patternsCodec patternsCodec
private def dedupCodec := Codec.prod patternCodec patternsCodec
private def flattenCodec := Codec.prod Wire.kindCodec (Codec.prod patternsCodec (Codec.prod patternsCodec patternsCodec))
private def singletonCodec := Codec.prod Wire.kindCodec patternCodec
private def unitCodec := Codec.prod Wire.kindCodec (Codec.prod Codec.string (Codec.prod patternsCodec patternsCodec))
private def emptyCodec := Codec.prod Wire.kindCodec Codec.string


private def edgeNumber : CollectionTypeEdge → Nat
  | .domain => 0 | .codomain => 1 | .binder => 2 | .element => 3
private def edgeOfNumber? : Nat → Option CollectionTypeEdge
  | 0 => some .domain | 1 => some .codomain | 2 => some .binder | 3 => some .element
  | _ => none
private def edgeCodec : Codec CollectionTypeEdge :=
  Codec.nat.mapped edgeNumber edgeOfNumber? (by intro edge; cases edge <;> rfl)

private def kindReceiptFieldsCodec (rule : GrammarRule) (kind : CollType) (elements : List Pattern) :
    Codec (Σ _parameterIndex : Fin rule.params.length,Σ _path : List CollectionTypeEdge,
      Σ elementType : TypeExpr,Σ bound : List TypeExpr,
        Wire.SourceReceipt language bound (.collection kind elementType) (.collection kind elements none)) :=
  Codec.sigma (Codec.fin rule.params.length) (fun _ =>
    Codec.sigma (Codec.list edgeCodec) (fun _ =>
      Codec.sigma Wire.typeCodec (fun elementType =>
        Codec.sigma (Codec.list Wire.typeCodec) (fun bound =>
          Wire.sourceReceiptCodec language bound (.collection kind elementType) (.collection kind elements none)))))

/-- The actual parameter index and type route are checked before the source
kind law is reconstructed. The Term receipt checks the original raw domain. -/
private def kindReceiptCodec (rule : GrammarRule) (kind : CollType) (elements : List Pattern) :
    Codec (CollectionTypedReceipt language rule kind elements) :=
  (kindReceiptFieldsCodec rule kind elements).mapped
    (fun receipt => ⟨receipt.parameterIndex,receipt.path,receipt.elementType,receipt.bound,
      ⟨receipt.data,receipt.accepted⟩⟩)
    (fun ⟨slot,path,elementType,bound,receipt⟩ =>
      if selected : collectionTypeAt? kind path (rule.params.get slot).typeExpr = some elementType then
        some ⟨slot,path,elementType,selected,bound,receipt.val,receipt.property⟩
      else none)
    (by
      intro receipt
      cases receipt with
      | mk slot path elementType selected bound data accepted => simp only [selected,dite_true])

private def algebra? (row : {rule : GrammarRule // rule ∈ language.terms}) (kind : CollType) :
    Option (Σ algebra : CollectionAlgebra, PLift (AlgebraRule language row.val kind algebra)) :=
  match row.val.algebra? with
  | none => none
  | some algebra =>
    match row.val.params with
    | [.simple parameter (.collection _ _)] =>
      (checkedAlgebra? language row.val kind algebra parameter).map (fun receipt => ⟨algebra, receipt⟩)
    | _ => none

private theorem algebra?_complete (row : {rule : GrammarRule // rule ∈ language.terms})
    (kind : CollType) (algebra : CollectionAlgebra) (declaration : AlgebraRule language row.val kind algebra) :
    algebra? row kind = some ⟨algebra, ⟨declaration⟩⟩ := by
  obtain ⟨parameter, shape⟩ := declaration.selfSorted
  obtain ⟨receipt, accepted⟩ := checkedAlgebra?_complete declaration shape
  have same : receipt = ⟨declaration⟩ := Subsingleton.elim _ _
  cases same
  simp only [algebra?, declaration.declared, shape, accepted, Option.map_some]

private def endpoints? (first second left right : Pattern) :
    Option (PLift (first = left ∧ second = right)) :=
  if same : first = left ∧ second = right then some ⟨same⟩ else none

abbrev WitnessAt (language : LanguageDef) (category : String) (left right : Pattern) :=
  {witness : DerivedGeneratorWitness language left right // (declaringRule witness).category = category}

private def castWitness {category : String} {first second left right : Pattern}
    (witness : WitnessAt language category first second) (firstSame : first = left) (secondSame : second = right) :
    WitnessAt language category left right := firstSame ▸ secondSame ▸ witness

def putWitness : {left right : Pattern} → DerivedGeneratorWitness language left right → Data
  | _, _, .bagPerm rule first second member receipt _ =>
      .pair (.atom 0) (.pair ((Wire.rowCodec language).put ⟨rule,member⟩)
        (.pair (pairPatterns.put (first,second)) ((kindReceiptCodec rule .hashBag first).put receipt)))
  | _, _, .setPerm rule first second member receipt _ =>
      .pair (.atom 1) (.pair ((Wire.rowCodec language).put ⟨rule,member⟩)
        (.pair (pairPatterns.put (first,second)) ((kindReceiptCodec rule .hashSet first).put receipt)))
  | _, _, .setDedup rule element rest member receipt =>
      .pair (.atom 2) (.pair ((Wire.rowCodec language).put ⟨rule,member⟩)
        (.pair (dedupCodec.put (element,rest))
          ((kindReceiptCodec rule .hashSet (element::element::rest)).put receipt)))
  | _, _, .flatten rule kind _ pre inner post algebra _ _ =>
      .pair (.atom 3) (.pair ((Wire.rowCodec language).put ⟨rule, algebra.authored⟩) (flattenCodec.put (kind, pre, inner, post)))
  | _, _, .singleton rule kind _ element algebra _ _ =>
      .pair (.atom 4) (.pair ((Wire.rowCodec language).put ⟨rule, algebra.authored⟩) (singletonCodec.put (kind, element)))
  | _, _, .unitElim rule kind _ unit pre post algebra _ _ =>
      .pair (.atom 5) (.pair ((Wire.rowCodec language).put ⟨rule, algebra.authored⟩) (unitCodec.put (kind, unit, pre, post)))
  | _, _, .emptyUnit rule kind _ unit algebra _ _ =>
      .pair (.atom 6) (.pair ((Wire.rowCodec language).put ⟨rule, algebra.authored⟩) (emptyCodec.put (kind, unit)))


/-- Intrinsic kind laws need data typing at the actual declared type, not a
base-sort carrier. The packet supplies no semantic authorization proof. -/
def getKindWitness (category : String) (left right : Pattern) :
    Data → Option (WitnessAt language category left right)
  | .pair (.atom 0) (.pair rowData (.pair payload typingData)) => do
      let row ← (Wire.rowCodec language).get rowData
      if sameCategory : row.val.category = category then
        let (first,second) ← pairPatterns.get payload
        let receipt ← (kindReceiptCodec row.val .hashBag first).get typingData
        if permutation : first.Perm second then
          let ⟨same⟩ ← endpoints? (.collection .hashBag first none) (.collection .hashBag second none) left right
          return castWitness ⟨.bagPerm row.val first second row.property receipt permutation,sameCategory⟩ same.1 same.2
        else none
      else none
  | .pair (.atom 1) (.pair rowData (.pair payload typingData)) => do
      let row ← (Wire.rowCodec language).get rowData
      if sameCategory : row.val.category = category then
        let (first,second) ← pairPatterns.get payload
        let receipt ← (kindReceiptCodec row.val .hashSet first).get typingData
        if permutation : first.Perm second then
          let ⟨same⟩ ← endpoints? (.collection .hashSet first none) (.collection .hashSet second none) left right
          return castWitness ⟨.setPerm row.val first second row.property receipt permutation,sameCategory⟩ same.1 same.2
        else none
      else none
  | .pair (.atom 2) (.pair rowData (.pair payload typingData)) => do
      let row ← (Wire.rowCodec language).get rowData
      if sameCategory : row.val.category = category then
        let (element,rest) ← dedupCodec.get payload
        let receipt ← (kindReceiptCodec row.val .hashSet (element::element::rest)).get typingData
        let ⟨same⟩ ← endpoints? (.collection .hashSet (element::element::rest) none)
          (.collection .hashSet (element::rest) none) left right
        return castWitness ⟨.setDedup row.val element rest row.property receipt,sameCategory⟩ same.1 same.2
      else none
  | _ => none

/-- The legacy sorted endpoint supplies the base-sort premise for algebra
variants. Intrinsic kinds delegate to the typed-data reader above. -/
def getWitness (category : String) (left right : Pattern) (sorted : SortedAt language left category) :
    Data → Option (WitnessAt language category left right)
  | .pair (.atom 0) payload => getKindWitness category left right (.pair (.atom 0) payload)
  | .pair (.atom 1) payload => getKindWitness category left right (.pair (.atom 1) payload)
  | .pair (.atom 2) payload => getKindWitness category left right (.pair (.atom 2) payload)
  | .pair (.atom 3) (.pair rowData payload) => do
      let row ← (Wire.rowCodec language).get rowData
      if sameCategory : row.val.category = category then
        let (kind, pre, inner, post) ← flattenCodec.get payload
        let ⟨algebra, ⟨declared⟩⟩ ← algebra? row kind
        if enabled : algebra.flatten = true then
          let ⟨same⟩ ← endpoints? (.collection kind (pre ++ .collection kind inner none :: post) none)
            (.collection kind (pre ++ inner ++ post) none) left right
          let sourceSorted : SortedAt language (.collection kind (pre ++ .collection kind inner none :: post) none) row.val.category := by
            simpa only [same.1, sameCategory] using sorted
          return castWitness ⟨.flatten row.val kind algebra pre inner post declared enabled sourceSorted, sameCategory⟩ same.1 same.2
        else none
      else none
  | .pair (.atom 4) (.pair rowData payload) => do
      let row ← (Wire.rowCodec language).get rowData
      if sameCategory : row.val.category = category then
        let (kind, element) ← singletonCodec.get payload
        let ⟨algebra, ⟨declared⟩⟩ ← algebra? row kind
        if enabled : algebra.flatten = true then
          let ⟨same⟩ ← endpoints? (.collection kind [element] none) element left right
          let sourceSorted : SortedAt language (.collection kind [element] none) row.val.category := by
            simpa only [same.1, sameCategory] using sorted
          return castWitness ⟨.singleton row.val kind algebra element declared enabled sourceSorted, sameCategory⟩ same.1 same.2
        else none
      else none
  | .pair (.atom 5) (.pair rowData payload) => do
      let row ← (Wire.rowCodec language).get rowData
      if sameCategory : row.val.category = category then
        let (kind, unit, pre, post) ← unitCodec.get payload
        let ⟨algebra, ⟨declared⟩⟩ ← algebra? row kind
        if isUnit : algebra.unit = some unit then
          let ⟨same⟩ ← endpoints? (.collection kind (pre ++ .apply unit [] :: post) none)
            (.collection kind (pre ++ post) none) left right
          let sourceSorted : SortedAt language (.collection kind (pre ++ .apply unit [] :: post) none) row.val.category := by
            simpa only [same.1, sameCategory] using sorted
          return castWitness ⟨.unitElim row.val kind algebra unit pre post declared isUnit sourceSorted, sameCategory⟩ same.1 same.2
        else none
      else none
  | .pair (.atom 6) (.pair rowData payload) => do
      let row ← (Wire.rowCodec language).get rowData
      if sameCategory : row.val.category = category then
        let (kind, unit) ← emptyCodec.get payload
        let ⟨algebra, ⟨declared⟩⟩ ← algebra? row kind
        if isUnit : algebra.unit = some unit then
          let ⟨same⟩ ← endpoints? (.collection kind [] none) (.apply unit []) left right
          let sourceSorted : SortedAt language (.collection kind [] none) row.val.category := by
            simpa only [same.1, sameCategory] using sorted
          return castWitness ⟨.emptyUnit row.val kind algebra unit declared isUnit sourceSorted, sameCategory⟩ same.1 same.2
        else none
      else none
  | _ => none


/-- A wrapped or nested bag law needs no invented base-sort typing. -/
theorem get_putBagPerm {rule : GrammarRule} {first second : List Pattern}
    (member : rule ∈ language.terms) (receipt : CollectionTypedReceipt language rule .hashBag first)
    (permutation : first.Perm second) :
    getKindWitness rule.category (.collection .hashBag first none) (.collection .hashBag second none)
      (putWitness (.bagPerm rule first second member receipt permutation)) =
        some ⟨.bagPerm rule first second member receipt permutation,rfl⟩ := by
  simp only [putWitness,getKindWitness,Codec.get_put,Bind.bind,Option.bind]
  simp only [dite_true,permutation,endpoints?,and_self,castWitness]
  rfl

theorem get_putSetPerm {rule : GrammarRule} {first second : List Pattern}
    (member : rule ∈ language.terms) (receipt : CollectionTypedReceipt language rule .hashSet first)
    (permutation : first.Perm second) :
    getKindWitness rule.category (.collection .hashSet first none) (.collection .hashSet second none)
      (putWitness (.setPerm rule first second member receipt permutation)) =
        some ⟨.setPerm rule first second member receipt permutation,rfl⟩ := by
  simp only [putWitness,getKindWitness,Codec.get_put,Bind.bind,Option.bind]
  simp only [dite_true,permutation,endpoints?,and_self,castWitness]
  rfl

theorem get_putSetDedup {rule : GrammarRule} {element : Pattern} {rest : List Pattern}
    (member : rule ∈ language.terms)
    (receipt : CollectionTypedReceipt language rule .hashSet (element::element::rest)) :
    getKindWitness rule.category (.collection .hashSet (element::element::rest) none)
      (.collection .hashSet (element::rest) none) (putWitness (.setDedup rule element rest member receipt)) =
        some ⟨.setDedup rule element rest member receipt,rfl⟩ := by
  simp only [putWitness,getKindWitness,Codec.get_put,Bind.bind,Option.bind]
  simp only [dite_true,endpoints?,and_self,castWitness]
  rfl

theorem get_putWitness {category : String} {left right : Pattern}
    (sorted : SortedAt language left category) (witness : DerivedGeneratorWitness language left right)
    (sameCategory : (declaringRule witness).category = category) :
    getWitness category left right sorted (putWitness witness) = some ⟨witness, sameCategory⟩ := by
  cases witness with
  | bagPerm rule first second member receipt permutation =>
      simp only [putWitness, getWitness, getKindWitness, Codec.get_put, Bind.bind, Option.bind,
        declaringRule] at sameCategory ⊢
      simp only [sameCategory, dite_true, permutation,
        endpoints?, and_self, castWitness]
      rfl
  | setPerm rule first second member receipt permutation =>
      simp only [putWitness, getWitness, getKindWitness, Codec.get_put, Bind.bind, Option.bind,
        declaringRule] at sameCategory ⊢
      simp only [sameCategory, dite_true, permutation,
        endpoints?, and_self, castWitness]
      rfl
  | setDedup rule element rest member receipt =>
      simp only [putWitness, getWitness, getKindWitness, Codec.get_put, Bind.bind, Option.bind,
        declaringRule] at sameCategory ⊢
      simp only [sameCategory, dite_true,
        endpoints?, and_self, castWitness]
      rfl
  | flatten rule kind algebra pre inner post declared enabled sortedOriginal =>
      simp only [putWitness, getWitness, Codec.get_put, Bind.bind, Option.bind,
        declaringRule] at sameCategory ⊢
      simp only [sameCategory, dite_true, algebra?_complete ⟨rule, declared.authored⟩ kind algebra declared, enabled,
        endpoints?, and_self, castWitness]
      rfl
  | singleton rule kind algebra element declared enabled sortedOriginal =>
      simp only [putWitness, getWitness, Codec.get_put, Bind.bind, Option.bind,
        declaringRule] at sameCategory ⊢
      simp only [sameCategory, dite_true, algebra?_complete ⟨rule, declared.authored⟩ kind algebra declared, enabled,
        endpoints?, and_self, castWitness]
      rfl
  | unitElim rule kind algebra unit pre post declared isUnit sortedOriginal =>
      simp only [putWitness, getWitness, Codec.get_put, Bind.bind, Option.bind,
        declaringRule] at sameCategory ⊢
      simp only [sameCategory, dite_true, algebra?_complete ⟨rule, declared.authored⟩ kind algebra declared, isUnit,
        endpoints?, and_self, castWitness]
      rfl
  | emptyUnit rule kind algebra unit declared isUnit sortedOriginal =>
      simp only [putWitness, getWitness, Codec.get_put, Bind.bind, Option.bind,
        declaringRule] at sameCategory ⊢
      simp only [sameCategory, dite_true, algebra?_complete ⟨rule, declared.authored⟩ kind algebra declared, isUnit,
        endpoints?, and_self, castWitness]
      rfl

private def endpointCodec (language : LanguageDef) :
    Codec (Σ context : List TypeExpr, Σ category : String,
      Term (signatureOf language) context (.base category) × Term (signatureOf language) context (.base category)) :=
  Codec.sigma (Codec.list Wire.typeCodec) (fun context =>
    Codec.sigma Codec.string (fun category =>
      Codec.prod (Wire.termCodec language context (.base category))
        (Wire.termCodec language context (.base category))))

def putDeclaration (declaration : DeclaredAxiom language) : Data :=
  .pair ((endpointCodec language).put
    ⟨declaration.context, declaration.category, declaration.left, declaration.right⟩)
    (putWitness declaration.witness)

/-- Both endpoint terms are decoded at the submitted original context and
category. Their source typing supplies exactly the sort premise used by the
law reader; no external semantic guard is accepted. -/
def getDeclaration (language : LanguageDef) : Data → Option (DeclaredAxiom language)
  | .pair endpointData witnessData => do
      let ⟨context, category, left, right⟩ ← (endpointCodec language).get endpointData
      let sorted : SortedAt language (erase left) category :=
        ⟨WellSorted.FreeTypeContext.empty, context, erase_typed left⟩
      let ⟨witness, sameCategory⟩ ← getWitness category (erase left) (erase right) sorted witnessData
      return ⟨context, category, left, right, erase left, erase right, rfl, rfl, witness, sameCategory⟩
  | _ => none

theorem get_putDeclaration (declaration : DeclaredAxiom language) :
    getDeclaration language (putDeclaration declaration) = some declaration := by
  cases declaration with
  | mk context category left right source target leftErases rightErases witness sameCategory =>
      cases leftErases
      cases rightErases
      simp only [putDeclaration, getDeclaration, Codec.get_put,
        Bind.bind, Option.bind]
      rw [get_putWitness (⟨WellSorted.FreeTypeContext.empty, context, erase_typed left⟩ :
        SortedAt language (erase left) category) witness sameCategory]
      rfl

def declarationCodec (language : LanguageDef) : Codec (DeclaredAxiom language) :=
  ⟨putDeclaration, getDeclaration language, get_putDeclaration⟩

/-- Each decoded table entry contains its actual checked original law
witness, including the declaring row and any alternative typed elaboration.
The list preserves row order and multiplicity. -/
def tableCodec (language : LanguageDef) : Codec (List (DeclaredAxiom language)) :=
  Codec.list (declarationCodec language)

namespace Controls
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.NamedFreeContext

private def atomRule (label : String) : GrammarRule where
  label := label
  category := "Term"
  params := []
  syntaxPattern := []

private def wrapperRule : GrammarRule where
  label := "Wrap"
  category := "Term"
  params := [.simple "tag" (.base "Term"),
    .simple "values" (.collection .hashBag (.collection .hashSet (.base "Term")))]
  syntaxPattern := []
  collectionRepresentation := .wrapped

private def packetLanguage : LanguageDef :=
  LanguageDef.ofCore "NestedKindPacket" ["Term"] [atomRule "A",atomRule "B",wrapperRule] [] []

theorem language_valid : packetLanguage.validate = [] := by decide +kernel

private def atom (label : String) (member : atomRule label ∈ packetLanguage.terms) :
    Term (signatureOf packetLanguage) [] (.base "Term") :=
  .op (.constructor (atomRule label) member (by simp [UsesBareCollection,atomRule]) .nil) .nil

private def a : Term (signatureOf packetLanguage) [] (.base "Term") := atom "A" (by decide +kernel)
private def b : Term (signatureOf packetLanguage) [] (.base "Term") := atom "B" (by decide +kernel)
private def first : List Pattern := [erase a,erase a,erase b]
private def second : List Pattern := [erase a,erase b]
private theorem wrapper_member : wrapperRule ∈ packetLanguage.terms := by decide +kernel

private def receipt : CollectionTypedReceipt packetLanguage wrapperRule .hashSet first where
  parameterIndex := ⟨1,by decide⟩
  path := [.element]
  elementType := .base "Term"
  selected := rfl
  bound := []
  data := SourceReceiptData.ofTerm (dataNode .hashSet [a,a,b])
  accepted := by decide +kernel

private def witness : DerivedGeneratorWitness packetLanguage (.collection .hashSet first none)
    (.collection .hashSet second none) :=
  .setDedup wrapperRule (erase a) [erase b] wrapper_member receipt

private def packet : Data := putWitness witness

/-- The declared nested field licenses set data without a bare carrier. -/
theorem nested_set_packet_roundtrip :
    getKindWitness (language := packetLanguage) "Term" (.collection .hashSet first none) (.collection .hashSet second none) packet =
      some ⟨witness,rfl⟩ := get_putSetDedup wrapper_member receipt

theorem nested_set_packet_source_law : DerivedInstance packetLanguage (.collection .hashSet first none)
    (.collection .hashSet second none) := witness.erase

theorem nested_set_data_has_no_base_carrier :
    ¬ SortedAt packetLanguage (.collection .hashSet first none) "Term" := by
  rintro ⟨free,bound,typed⟩
  have checked := checkHasType_complete_of_object typed (by decide +kernel)
  have rejected : checkHasType packetLanguage free bound (.collection .hashSet first none) (.base "Term") = false := rfl
  rw [rejected] at checked
  cases checked

private def permuted : List Pattern := [erase b,erase a,erase a]
private theorem permutes : first.Perm permuted := by decide +kernel

theorem nested_set_permutation_packet_roundtrip :
    getKindWitness (language := packetLanguage) "Term" (.collection .hashSet first none) (.collection .hashSet permuted none)
      (putWitness (.setPerm wrapperRule first permuted wrapper_member receipt permutes)) =
        some ⟨.setPerm wrapperRule first permuted wrapper_member receipt permutes,rfl⟩ :=
  get_putSetPerm wrapper_member receipt permutes

private def innerA : Pattern := .collection .hashSet [erase a] (some "tailA")
private def innerB : Pattern := .collection .hashSet [erase b] (some "tailB")
private def outerReceipt : CollectionTypedReceipt packetLanguage wrapperRule .hashBag [innerA,innerB] where
  parameterIndex := ⟨1,by decide⟩
  path := []
  elementType := .collection .hashSet (.base "Term")
  selected := rfl
  bound := []
  data := SourceReceiptData.ofTerm (dataNode .hashBag [dataNode .hashSet [a],dataNode .hashSet [b]])
  accepted := by decide +kernel

/-- Inner schema tails remain in the raw domain accepted by HasType. -/
theorem nested_bag_open_inner_tail_packet_roundtrip :
    getKindWitness (language := packetLanguage) "Term" (.collection .hashBag [innerA,innerB] none) (.collection .hashBag [innerB,innerA] none)
      (putWitness (.bagPerm wrapperRule _ _ wrapper_member outerReceipt (List.Perm.swap _ _ []))) =
        some ⟨.bagPerm wrapperRule _ _ wrapper_member outerReceipt (List.Perm.swap _ _ []),rfl⟩ :=
  get_putBagPerm wrapper_member outerReceipt (List.Perm.swap _ _ [])

private def substitution : Term (signatureOf packetLanguage) [] (.base "Term") :=
  .op (.subst (.base "Term") (.base "Term")) (.cons (.var .zero) (.cons a .nil))
private def substitutionReceipt : CollectionTypedReceipt packetLanguage wrapperRule .hashSet
    [erase substitution,erase substitution] where
  parameterIndex := ⟨1,by decide⟩
  path := [.element]
  elementType := .base "Term"
  selected := rfl
  bound := []
  data := SourceReceiptData.ofTerm (dataNode .hashSet [substitution,substitution])
  accepted := by decide +kernel

theorem raw_substitution_kind_packet_roundtrip :
    getKindWitness (language := packetLanguage) "Term" (.collection .hashSet [erase substitution,erase substitution] none)
      (.collection .hashSet [erase substitution] none)
      (putWitness (.setDedup wrapperRule (erase substitution) [] wrapper_member substitutionReceipt)) =
        some ⟨.setDedup wrapperRule (erase substitution) [] wrapper_member substitutionReceipt,rfl⟩ :=
  get_putSetDedup wrapper_member substitutionReceipt

private def replaceParameterIndex (index : Nat) : Data → Data
  | .pair tag (.pair row (.pair payload (.pair _ fields))) =>
      .pair tag (.pair row (.pair payload (.pair (.atom index) fields)))
  | data => data

private def replaceTypeRoute (route : List CollectionTypeEdge) : Data → Data
  | .pair tag (.pair row (.pair payload (.pair slot (.pair _ fields)))) =>
      .pair tag (.pair row (.pair payload (.pair slot (.pair ((Codec.list edgeCodec).put route) fields))))
  | data => data

theorem wrong_parameter_packet_refused :
    getKindWitness (language := packetLanguage) "Term" (.collection .hashSet first none) (.collection .hashSet second none)
      (replaceParameterIndex 0 packet) = none := by decide +kernel

theorem out_of_bounds_parameter_packet_refused :
    getKindWitness (language := packetLanguage) "Term" (.collection .hashSet first none) (.collection .hashSet second none)
      (replaceParameterIndex 2 packet) = none := by decide +kernel

theorem wrong_type_route_packet_refused :
    getKindWitness (language := packetLanguage) "Term" (.collection .hashSet first none) (.collection .hashSet second none)
      (replaceTypeRoute [.domain] packet) = none := by decide +kernel


theorem wrong_kind_packet_refused :
    getKindWitness (language := packetLanguage) "Term" (.collection .hashBag first none) (.collection .hashBag first none)
      (.pair (.atom 0) (.pair ((Wire.rowCodec packetLanguage).put ⟨wrapperRule,wrapper_member⟩)
        (.pair (pairPatterns.put (first,first)) ((kindReceiptCodec wrapperRule .hashSet first).put receipt)))) = none := by
  decide +kernel

theorem false_permutation_packet_refused :
    getKindWitness (language := packetLanguage) "Term" (.collection .hashSet first none) (.collection .hashSet second none)
      (.pair (.atom 1) (.pair ((Wire.rowCodec packetLanguage).put ⟨wrapperRule,wrapper_member⟩)
        (.pair (pairPatterns.put (first,second)) ((kindReceiptCodec wrapperRule .hashSet first).put receipt)))) = none := by
  decide +kernel

theorem cross_constructor_packet_refused :
    getKindWitness (language := packetLanguage) "Term" (.collection .hashSet first none) (.collection .hashSet second none)
      (.pair (.atom 2) (.pair ((Wire.rowCodec packetLanguage).put ⟨atomRule "B",by decide +kernel⟩)
        (.pair (dedupCodec.put (erase a,[erase b])) ((kindReceiptCodec wrapperRule .hashSet first).put receipt)))) = none := by
  decide +kernel

theorem wrong_conclusion_packet_refused :
    getKindWitness (language := packetLanguage) "Term" (.collection .hashSet first none) (erase b) packet = none := by decide +kernel

theorem outer_open_tail_packet_refused :
    getKindWitness (language := packetLanguage) "Term" (.collection .hashSet first (some "rest")) (.collection .hashSet second none) packet = none := by
  decide +kernel

theorem old_carrier_only_packet_refused :
    getKindWitness (language := packetLanguage) "Term" (.collection .hashSet first none) (.collection .hashSet second none)
      (.pair (.atom 2) (.pair ((Wire.rowCodec packetLanguage).put ⟨wrapperRule,wrapper_member⟩)
        (dedupCodec.put (erase a,[erase b])))) = none := by decide +kernel

#print axioms language_valid
#print axioms nested_set_packet_roundtrip
#print axioms nested_set_packet_source_law
#print axioms nested_set_data_has_no_base_carrier
#print axioms nested_set_permutation_packet_roundtrip
#print axioms nested_bag_open_inner_tail_packet_roundtrip
#print axioms raw_substitution_kind_packet_roundtrip
#print axioms wrong_parameter_packet_refused
#print axioms out_of_bounds_parameter_packet_refused
#print axioms wrong_type_route_packet_refused
#print axioms wrong_kind_packet_refused
#print axioms false_permutation_packet_refused
#print axioms cross_constructor_packet_refused
#print axioms wrong_conclusion_packet_refused
#print axioms outer_open_tail_packet_refused
#print axioms old_carrier_only_packet_refused
end Controls

#print axioms kindReceiptCodec
#print axioms get_putBagPerm
#print axioms get_putSetPerm
#print axioms get_putSetDedup
#print axioms get_putWitness
#print axioms get_putDeclaration

end Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationWire
