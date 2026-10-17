import Mettapedia.GSLT.LanguageDef.BindingSignatureWire
import Mettapedia.GSLT.LanguageDef.BindingCollectionEquationGenerators
import Mettapedia.GSLT.LanguageDef.CertificateDataEncoding

/-!
# Checked source packets for the original collection equation family

Law packets retain the declaring row and original raw decomposition. Sorted
intrinsic endpoints are read by the existing binding codec. Their independently
proved source typing supplies the sort premise, while the packet reader checks
the exact row shape, permutation, algebra switches, unit inventory and literal
endpoints. No authorization proof is accepted from an external packet.
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

private def carrier? (row : {rule : GrammarRule // rule ∈ language.terms}) (kind : CollType) :
    Option (PLift (CollectionCarrierRule language row.val kind)) :=
  match row.val.params with
  | [.simple parameter (.collection _ element)] =>
      if shape : row.val.params = [.simple parameter (.collection kind element)] then
        some ⟨⟨row.property, ⟨parameter, element, shape⟩⟩⟩
      else none
  | _ => none

private theorem carrier?_complete (row : {rule : GrammarRule // rule ∈ language.terms})
    (kind : CollType) (declaration : CollectionCarrierRule language row.val kind) :
    carrier? row kind = some ⟨declaration⟩ := by
  obtain ⟨parameter, element, shape⟩ := declaration.selfSorted
  simp only [carrier?, shape, dite_true]

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
  | _, _, .bagPerm rule first second carrier _ _ =>
      .pair (.atom 0) (.pair ((Wire.rowCodec language).put ⟨rule, carrier.authored⟩) (pairPatterns.put (first, second)))
  | _, _, .setPerm rule first second carrier _ _ =>
      .pair (.atom 1) (.pair ((Wire.rowCodec language).put ⟨rule, carrier.authored⟩) (pairPatterns.put (first, second)))
  | _, _, .setDedup rule element rest carrier _ =>
      .pair (.atom 2) (.pair ((Wire.rowCodec language).put ⟨rule, carrier.authored⟩) (dedupCodec.put (element, rest)))
  | _, _, .flatten rule kind _ pre inner post algebra _ _ =>
      .pair (.atom 3) (.pair ((Wire.rowCodec language).put ⟨rule, algebra.authored⟩) (flattenCodec.put (kind, pre, inner, post)))
  | _, _, .singleton rule kind _ element algebra _ _ =>
      .pair (.atom 4) (.pair ((Wire.rowCodec language).put ⟨rule, algebra.authored⟩) (singletonCodec.put (kind, element)))
  | _, _, .unitElim rule kind _ unit pre post algebra _ _ =>
      .pair (.atom 5) (.pair ((Wire.rowCodec language).put ⟨rule, algebra.authored⟩) (unitCodec.put (kind, unit, pre, post)))
  | _, _, .emptyUnit rule kind _ unit algebra _ _ =>
      .pair (.atom 6) (.pair ((Wire.rowCodec language).put ⟨rule, algebra.authored⟩) (emptyCodec.put (kind, unit)))

/-- The only proof argument is the independently established source typing
of the submitted left endpoint. All remaining law conditions are checked. -/
def getWitness (category : String) (left right : Pattern) (sorted : SortedAt language left category) :
    Data → Option (WitnessAt language category left right)
  | .pair (.atom 0) (.pair rowData payload) => do
      let row ← (Wire.rowCodec language).get rowData
      if sameCategory : row.val.category = category then
        let (first, second) ← pairPatterns.get payload
        let ⟨carrier⟩ ← carrier? row .hashBag
        if permutation : first.Perm second then
          let ⟨same⟩ ← endpoints? (.collection .hashBag first none) (.collection .hashBag second none) left right
          let sourceSorted : SortedAt language (.collection .hashBag first none) row.val.category := by
            simpa only [same.1, sameCategory] using sorted
          return castWitness ⟨.bagPerm row.val first second carrier sourceSorted permutation, sameCategory⟩ same.1 same.2
        else none
      else none
  | .pair (.atom 1) (.pair rowData payload) => do
      let row ← (Wire.rowCodec language).get rowData
      if sameCategory : row.val.category = category then
        let (first, second) ← pairPatterns.get payload
        let ⟨carrier⟩ ← carrier? row .hashSet
        if permutation : first.Perm second then
          let ⟨same⟩ ← endpoints? (.collection .hashSet first none) (.collection .hashSet second none) left right
          let sourceSorted : SortedAt language (.collection .hashSet first none) row.val.category := by
            simpa only [same.1, sameCategory] using sorted
          return castWitness ⟨.setPerm row.val first second carrier sourceSorted permutation, sameCategory⟩ same.1 same.2
        else none
      else none
  | .pair (.atom 2) (.pair rowData payload) => do
      let row ← (Wire.rowCodec language).get rowData
      if sameCategory : row.val.category = category then
        let (element, rest) ← dedupCodec.get payload
        let ⟨carrier⟩ ← carrier? row .hashSet
        let ⟨same⟩ ← endpoints? (.collection .hashSet (element :: element :: rest) none)
          (.collection .hashSet (element :: rest) none) left right
        let sourceSorted : SortedAt language (.collection .hashSet (element :: element :: rest) none) row.val.category := by
          simpa only [same.1, sameCategory] using sorted
        return castWitness ⟨.setDedup row.val element rest carrier sourceSorted, sameCategory⟩ same.1 same.2
      else none
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

theorem get_putWitness {category : String} {left right : Pattern}
    (sorted : SortedAt language left category) (witness : DerivedGeneratorWitness language left right)
    (sameCategory : (declaringRule witness).category = category) :
    getWitness category left right sorted (putWitness witness) = some ⟨witness, sameCategory⟩ := by
  cases witness with
  | bagPerm rule first second carrier sortedOriginal permutation =>
      simp only [putWitness, getWitness, Codec.get_put, Bind.bind, Option.bind,
        declaringRule] at sameCategory ⊢
      simp only [sameCategory, dite_true, carrier?_complete ⟨rule, carrier.authored⟩ .hashBag carrier, permutation,
        endpoints?, and_self, castWitness]
      rfl
  | setPerm rule first second carrier sortedOriginal permutation =>
      simp only [putWitness, getWitness, Codec.get_put, Bind.bind, Option.bind,
        declaringRule] at sameCategory ⊢
      simp only [sameCategory, dite_true, carrier?_complete ⟨rule, carrier.authored⟩ .hashSet carrier, permutation,
        endpoints?, and_self, castWitness]
      rfl
  | setDedup rule element rest carrier sortedOriginal =>
      simp only [putWitness, getWitness, Codec.get_put, Bind.bind, Option.bind,
        declaringRule] at sameCategory ⊢
      simp only [sameCategory, dite_true, carrier?_complete ⟨rule, carrier.authored⟩ .hashSet carrier,
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

end Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationWire
