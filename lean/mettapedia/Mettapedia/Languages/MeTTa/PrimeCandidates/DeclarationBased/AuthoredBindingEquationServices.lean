import Mettapedia.GSLT.LanguageDef.AuthoredBindingEquationServices
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec
import Mettapedia.GSLT.LanguageDef.CertificateDataEncoding
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions
import Mettapedia.GSLT.LanguageDef.BindingCollectionEquationGenerators
import Mettapedia.GSLT.LanguageDef.BindingCollectionEquationWire
import Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SharedJudgmentServiceRegistry

/-!
# Optional literal declared-calculus attachment of authored binding equations

The independent source service is imported above. This optional attachment
compares its original finite contextual equality with literal declared-calculus
endpoints over the same checked collection-law table. Requests retain the original declaration
inventory, source context and sort, literal native endpoints and canonical
source words. Source words are data in the existing native wire carrier.
Admission compares their decoded source syntax with both literal endpoints;
it never attempts to recover metadata from optimized execution programs.

This service is an explicit certificate boundary. It does not install the
source laws as ambient native conversion. Accepted table profiles compute one
finite declaration package for all retained endpoints. Executed resource
bounds remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Mettapedia.GSLT.LanguageDef
open SemanticService
open KernelAuthority SemanticEvidence
open BindingSyntax CollectionEquationFamily CollectionEquationGenerators
open AuthoredTypeExpressions
open Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission

variable {language : LanguageDef}

/-- The source witness occupies a canonical complete binary word. The native
carrier stores that word as literal string data; it does not evaluate it. -/
def sourceData {context : List TypeExpr} {sort : TypeExpr}
    (source : Term (signatureOf language) context sort) : Tower.Tm context.length :=
  NativeWireData.encode (.string (Binary.Text.render
    (Binary.encodeWith (Wire.termCodec language context sort) source)))

def sourceData? (context : List TypeExpr) (sort : TypeExpr)
    (native : Tower.Tm context.length) : Option (Term (signatureOf language) context sort) := do
  let represented ← NativeWireData.decode native
  let text ← match represented with | .string text => some text | _ => none
  let word ← Binary.Text.parse text
  Binary.canonicalDecodeWith (Wire.termCodec language context sort) word

theorem sourceData?_sourceData {context : List TypeExpr} {sort : TypeExpr}
    (source : Term (signatureOf language) context sort) :
    sourceData? context sort (sourceData source) = some source := by
  simp only [sourceData?, sourceData, NativeWireData.decode_encode,
    Binary.Text.parse_render, Bind.bind, Option.bind, Binary.canonicalDecodeWith_encodeWith]

/-- The native telescope is determined by the retained source context. Each
endpoint additionally carries the complete source syntax used for admission. -/
structure Endpoint (n : Nat) where
  literal : Tower.Tm n
  source : Tower.Tm n

def endpoint (scope : Lean.Name) {context : List TypeExpr} {sort : TypeExpr}
    (source : Term (signatureOf language) context sort) : Endpoint context.length :=
  ⟨Literal.encode scope language source, sourceData source⟩

def EndpointAt (scope : Lean.Name) (context : List TypeExpr) (sort : TypeExpr)
    (native : Endpoint context.length) (source : Term (signatureOf language) context sort) : Prop :=
  native.literal = Literal.encode scope language source ∧ native.source = sourceData source

def admitEndpoint? (scope : Lean.Name) (context : List TypeExpr) (sort : TypeExpr)
    (native : Endpoint context.length) : Option (Term (signatureOf language) context sort) := do
  let source ← sourceData? context sort native.source
  if native.literal = Literal.encode scope language source ∧ native.source = sourceData source then
    some source else none

theorem admitEndpoint?_exact (scope : Lean.Name) (context : List TypeExpr) (sort : TypeExpr)
    (native : Endpoint context.length) (source : Term (signatureOf language) context sort) :
    admitEndpoint? scope context sort native = some source ↔ EndpointAt scope context sort native source := by
  constructor
  · intro accepted
    cases decoded : sourceData? (language := language) context sort native.source with
    | none => simp only [admitEndpoint?, decoded, Bind.bind, Option.bind] at accepted; cases accepted
    | some found =>
        simp only [admitEndpoint?, decoded, Bind.bind, Option.bind] at accepted
        split at accepted
        · rename_i literal
          cases Option.some.inj accepted
          exact literal
        · cases accepted
  · rintro ⟨literal, represented⟩
    simp only [admitEndpoint?, represented, sourceData?_sourceData, Bind.bind, Option.bind]
    simp only [literal, and_self, ite_true]

theorem admitEndpoint?_endpoint (scope : Lean.Name) {context : List TypeExpr} {sort : TypeExpr}
    (source : Term (signatureOf language) context sort) :
    admitEndpoint? scope context sort (endpoint scope source) = some source :=
  (admitEndpoint?_exact scope context sort (endpoint scope source) source).mpr ⟨rfl, rfl⟩

open Mettapedia.GSLT.LanguageDef.AuthoredBindingEquationServices
  (equations selectedTable equations_selectedTable environmentData table_supported supported_table rootWord Role
    requiredRoles requiredRoles_complete)

structure Request (n : Nat) where
  scopeName : Lean.Name
  languageName : String
  types : List TypeDecl
  rows : List GrammarRule
  equations : List Data
  context : List TypeExpr
  sort : TypeExpr
  nativeType : Tower.Tm n
  first : Endpoint n
  second : Endpoint n

def headerMatches (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) (request : Request context.length) : Bool :=
  decide (request.scopeName = scope ∧ request.languageName = language.name ∧
    request.types = language.types ∧ request.rows = language.terms ∧
    request.equations = environmentData selected ∧ request.context = context ∧ request.sort = sort ∧
    request.nativeType = BindingSignatureEmbedding.sortType (Literal.names scope language) sort)

def HeaderAt (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) (request : Request context.length) : Prop :=
  request.scopeName = scope ∧ request.languageName = language.name ∧
    request.types = language.types ∧ request.rows = language.terms ∧
    request.equations = environmentData selected ∧ request.context = context ∧ request.sort = sort ∧
    request.nativeType = BindingSignatureEmbedding.sortType (Literal.names scope language) sort

theorem headerMatches_exact (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) (request : Request context.length) :
    headerMatches scope selected context sort request = true ↔ HeaderAt scope selected context sort request := by
  simp only [headerMatches, HeaderAt, decide_eq_true_eq]

/-- Authority is the independently defined source equality and literal image
metadata. The executable checker does not occur in this specification. -/
def Meaning (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) (request : Request context.length) : Prop :=
  HeaderAt scope selected context sort request ∧
    ∃ first second : Term (signatureOf language) context sort,
      EndpointAt scope context sort request.first first ∧
      EndpointAt scope context sort request.second second ∧
      EqClosure (equations selected) first second

def check (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr)
    (request : Request context.length) (proof : List Binary.Alphabet) : Bool :=
  headerMatches scope selected context sort request &&
    match admitEndpoint? scope context sort request.first, admitEndpoint? scope context sort request.second with
    | some first, some second => Wire.checkEquationBinary language (equations selected) proof first second
    | _, _ => false

theorem check_sound (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr)
    (request : Request context.length) (proof : List Binary.Alphabet)
    (accepted : check scope selected context sort request proof = true) :
    Meaning scope selected context sort request := by
  simp only [check, Bool.and_eq_true] at accepted
  refine ⟨(headerMatches_exact scope selected context sort request).mp accepted.1, ?_⟩
  cases firstRead : admitEndpoint? (language := language) scope context sort request.first with
  | none => simp only [firstRead] at accepted; cases accepted.2
  | some first =>
    cases secondRead : admitEndpoint? (language := language) scope context sort request.second with
    | none => simp only [firstRead, secondRead] at accepted; cases accepted.2
    | some second =>
      simp only [firstRead, secondRead] at accepted
      obtain ⟨certificate, _, checked⟩ :=
        (Wire.checkEquationBinary_exact language (equations selected) proof first second).mp accepted.2
      exact ⟨first, second,
        (admitEndpoint?_exact scope context sort request.first first).mp firstRead,
        (admitEndpoint?_exact scope context sort request.second second).mp secondRead,
        EqualityCertificates.check_sound certificate first second checked⟩

theorem check_complete (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) (request : Request context.length)
    (meaning : Meaning scope selected context sort request) :
    ∃ proof : List Binary.Alphabet, check scope selected context sort request proof = true := by
  obtain ⟨header, first, second, firstAt, secondAt, source⟩ := meaning
  obtain ⟨proof, accepted⟩ := (Wire.checkEquationBinary_complete language (equations selected) first second).mp source
  refine ⟨proof, ?_⟩
  simp only [check, (headerMatches_exact scope selected context sort request).mpr header,
    Bool.true_and, (admitEndpoint?_exact scope context sort request.first first).mpr firstAt,
    (admitEndpoint?_exact scope context sort request.second second).mpr secondAt]
  exact accepted

def target (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) : AdmissionObject where
  Carrier := Request context.length
  Meaning := Meaning scope selected context sort

def checker (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) : Checker (Request context.length) (List Binary.Alphabet) :=
  ⟨check scope selected context sort⟩

theorem authority (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) :
    (checker scope selected context sort).Authority (Meaning scope selected context sort) where
  sound := check_sound scope selected context sort
  complete := check_complete scope selected context sort

def service (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) : SemanticService.Service (target scope selected context sort) :=
  .certificateBoundary (List Binary.Alphabet) (checker scope selected context sort) (authority scope selected context sort)

def invocation (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    {context : List TypeExpr} {sort : TypeExpr} (request : Request context.length) (proof : List Binary.Alphabet) :
    SemanticServiceInvocation.Request (service scope selected context sort) := .certificateBoundary request proof

theorem invocation_exact (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    {context : List TypeExpr} {sort : TypeExpr} (request : Request context.length) (proof : List Binary.Alphabet) :
    (SemanticServiceInvocation.invoke (invocation (sort := sort) scope selected request proof)).acceptedValue = some request ↔
      check scope selected context sort request proof = true := by
  change (if check scope selected context sort request proof then some request else none) = some request ↔ _
  cases check scope selected context sort request proof <;> simp

def sourceRequest (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort) : Request context.length where
  scopeName := scope
  languageName := language.name
  types := language.types
  rows := language.terms
  equations := environmentData selected
  context := context
  sort := sort
  nativeType := BindingSignatureEmbedding.sortType (Literal.names scope language) sort
  first := endpoint scope first
  second := endpoint scope second

theorem sourceRequest_header (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort) :
    HeaderAt scope selected context sort (sourceRequest scope selected first second) := by
  simp only [HeaderAt, sourceRequest, and_self]

theorem check_sourceRequest (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort) (proof : List Binary.Alphabet) :
    check scope selected context sort (sourceRequest scope selected first second) proof =
      Wire.checkEquationBinary language (equations selected) proof first second := by
  have header : headerMatches scope selected context sort (sourceRequest scope selected first second) = true :=
    (headerMatches_exact scope selected _ _ _).mpr (sourceRequest_header scope selected first second)
  simp only [check, header, Bool.true_and]
  simp only [sourceRequest, admitEndpoint?_endpoint]

theorem endpointAt_endpoint_iff (scope : Lean.Name) {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort) :
    EndpointAt scope context sort (endpoint scope first) second ↔ first = second := by
  constructor
  · intro admitted
    exact Literal.encode_injective scope language admitted.1
  · intro same
    cases same
    exact ⟨rfl, rfl⟩

theorem sourceRequest_meaning_iff (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort) :
    Meaning scope selected context sort (sourceRequest scope selected first second) ↔
      EqClosure (equations selected) first second := by
  constructor
  · rintro ⟨_, recoveredFirst, recoveredSecond, firstAt, secondAt, source⟩
    have firstSame := (endpointAt_endpoint_iff scope first recoveredFirst).mp firstAt
    have secondSame := (endpointAt_endpoint_iff scope second recoveredSecond).mp secondAt
    simpa only [firstSame, secondSame] using source
  · intro source
    exact ⟨sourceRequest_header scope selected first second,
      first, second, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, source⟩

theorem source_equation_iff_service (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort) :
    EqClosure (equations selected) first second ↔
      ∃ proof : List Binary.Alphabet,
        (SemanticServiceInvocation.invoke
          (invocation (sort := sort) scope selected (sourceRequest scope selected first second) proof)).acceptedValue =
            some (sourceRequest scope selected first second) := by
  constructor
  · intro source
    obtain ⟨proof, checked⟩ := check_complete scope selected context sort
      (sourceRequest scope selected first second) ((sourceRequest_meaning_iff scope selected first second).mpr source)
    exact ⟨proof, (invocation_exact scope selected _ proof).mpr checked⟩
  · rintro ⟨proof, accepted⟩
    exact (sourceRequest_meaning_iff scope selected first second).mp
      (check_sound scope selected context sort _ proof ((invocation_exact scope selected _ proof).mp accepted))

/-- Full original declaration-family coverage retains alternative intrinsic
elaborations at the same raw law boundary. The source relation is not
restricted to the convenient seven producer functions. -/
theorem full_source_iff_service (scope : Lean.Name)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort) :
    BindingEquationFamilyCongruence.Related (CollectionEquationFamily.family language) first second ↔
      ∃ declarations : List (DeclaredAxiom language), ∃ proof : List Binary.Alphabet,
        (SemanticServiceInvocation.invoke
          (invocation (sort := sort) scope declarations (sourceRequest scope declarations first second) proof)).acceptedValue =
            some (sourceRequest scope declarations first second) := by
  constructor
  · rintro ⟨fragment, supported, derived⟩
    obtain ⟨declarations, rfl⟩ := supported_table fragment supported
    obtain ⟨word, accepted⟩ := (source_equation_iff_service scope declarations first second).mp derived
    exact ⟨declarations, word, accepted⟩
  · rintro ⟨declarations, word, accepted⟩
    exact ⟨equations declarations, table_supported declarations,
      (source_equation_iff_service scope declarations first second).mpr ⟨word, accepted⟩⟩

/-- Every computably selected original law producer is included, without
requiring unique unit labels or identifying distinct declaration rows. -/
theorem selected_source_service_coverage (scope : Lean.Name)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (source : BindingEquationFamilyCongruence.Related (selectedFamily language) first second) :
    ∃ declarations : List (DeclaredAxiom language), ∃ proof : List Binary.Alphabet,
      (SemanticServiceInvocation.invoke
        (invocation (sort := sort) scope declarations (sourceRequest scope declarations first second) proof)).acceptedValue =
          some (sourceRequest scope declarations first second) := by
  obtain ⟨fragment, supported, derivation⟩ := source
  apply (full_source_iff_service scope first second).mp
  exact ⟨fragment, (fun equation member => selected_in_boundary (supported equation member)), derivation⟩

theorem rootWord_checked (scope : Lean.Name) (selected : SelectedGenerator language) :
    check scope [selected.declaration] selected.declaration.context (.base selected.declaration.category)
      (sourceRequest scope [selected.declaration] selected.declaration.left selected.declaration.right) (rootWord selected) = true := by
  rw [check_sourceRequest]
  apply (Wire.checkEquationBinary_exact language [selected.declaration.toAxiom] _ _ _).mpr
  refine ⟨selected.instanceCertificate
    (EqualityCertificates.Substitution.quote (S := signatureOf language)
      selected.declaration.context (fun _ position => .var position)), rfl, ?_⟩
  simpa only [EqualityCertificates.Substitution.read_quote, Binding.bind_id] using
    selected.instanceCertificate_checked
      (EqualityCertificates.Substitution.quote (S := signatureOf language)
        selected.declaration.context (fun _ position => .var position))

theorem rootWord_accepted (scope : Lean.Name) (selected : SelectedGenerator language) :
    (SemanticServiceInvocation.invoke
      (invocation (sort := .base selected.declaration.category) scope [selected.declaration]
        (sourceRequest scope [selected.declaration] selected.declaration.left selected.declaration.right) (rootWord selected))).acceptedValue =
          some (sourceRequest scope [selected.declaration] selected.declaration.left selected.declaration.right) :=
  (invocation_exact scope [selected.declaration] _ _).mpr (rootWord_checked scope selected)

/-! ## Admission and required invocation roles -/

def AdmissionMeaning (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) (request : Request context.length) : Prop :=
  HeaderAt scope selected context sort request ∧
    (∃ first : Term (signatureOf language) context sort, EndpointAt scope context sort request.first first) ∧
    (∃ second : Term (signatureOf language) context sort, EndpointAt scope context sort request.second second)

def checkAdmission (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) (request : Request context.length) : Bool :=
  headerMatches scope selected context sort request &&
    (admitEndpoint? (language := language) scope context sort request.first).isSome &&
    (admitEndpoint? (language := language) scope context sort request.second).isSome

theorem checkAdmission_exact (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) (request : Request context.length) :
    checkAdmission scope selected context sort request = true ↔
      AdmissionMeaning scope selected context sort request := by
  simp only [checkAdmission, Bool.and_eq_true, headerMatches_exact,
    Option.isSome_iff_exists, admitEndpoint?_exact, AdmissionMeaning]
  exact and_assoc

def admissionTarget (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) : AdmissionObject where
  Carrier := Request context.length
  Meaning := AdmissionMeaning scope selected context sort

def admissionKernel (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) :
    Checker.DecisionKernel (Request context.length) (AdmissionMeaning scope selected context sort) :=
  ⟨checkAdmission scope selected context sort, checkAdmission_exact scope selected context sort⟩

/-! ## Submitted source-law tables -/

namespace SubmittedTable

structure Packet where
  tableWord : List Binary.Alphabet
  proofWord : List Binary.Alphabet

def packet (declarations : List (DeclaredAxiom language)) (proof : List Binary.Alphabet) : Packet :=
  ⟨Binary.encodeWith (CollectionEquationWire.tableCodec language) declarations, proof⟩

/-- The meaning retains original law authority and source equality, without
requiring that an implementation has decoded any particular packet. -/
def Meaning (scope : Lean.Name) (language : LanguageDef)
    (context : List TypeExpr) (sort : TypeExpr) (request : Request context.length) : Prop :=
  ∃ declarations : List (DeclaredAxiom language),
    AuthoredBindingEquationServices.Meaning scope declarations context sort request

/-- The table decoder constructs the actual original witnesses before the
existing proof checker runs. Neither component accepts a supplied source
authorization proof from the caller. -/
def check (scope : Lean.Name) (language : LanguageDef)
    (context : List TypeExpr) (sort : TypeExpr)
    (request : Request context.length) (submitted : Packet) : Bool :=
  match Binary.canonicalDecodeWith (CollectionEquationWire.tableCodec language) submitted.tableWord with
  | none => false
  | some declarations => AuthoredBindingEquationServices.check scope declarations context sort request submitted.proofWord

theorem check_packet (scope : Lean.Name) (declarations : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) (request : Request context.length) (proof : List Binary.Alphabet) :
    check scope language context sort request (packet declarations proof) =
      AuthoredBindingEquationServices.check scope declarations context sort request proof := by
  simp only [check, packet, Binary.canonicalDecodeWith_encodeWith]

theorem check_sound (scope : Lean.Name) (language : LanguageDef)
    (context : List TypeExpr) (sort : TypeExpr) (request : Request context.length) (submitted : Packet)
    (accepted : check scope language context sort request submitted = true) :
    Meaning scope language context sort request := by
  cases decoded : Binary.canonicalDecodeWith (CollectionEquationWire.tableCodec language) submitted.tableWord with
  | none => simp only [check, decoded] at accepted; cases accepted
  | some declarations =>
      exact ⟨declarations, AuthoredBindingEquationServices.check_sound scope declarations context sort request submitted.proofWord
        (by simpa only [check, decoded] using accepted)⟩

theorem check_complete (scope : Lean.Name) (language : LanguageDef)
    (context : List TypeExpr) (sort : TypeExpr) (request : Request context.length)
    (meaning : Meaning scope language context sort request) :
    ∃ submitted : Packet, check scope language context sort request submitted = true := by
  obtain ⟨declarations, source⟩ := meaning
  obtain ⟨proof, accepted⟩ := AuthoredBindingEquationServices.check_complete scope declarations context sort request source
  exact ⟨packet declarations proof, (check_packet scope declarations context sort request proof).trans accepted⟩

def target (scope : Lean.Name) (language : LanguageDef) (context : List TypeExpr) (sort : TypeExpr) : AdmissionObject where
  Carrier := Request context.length
  Meaning := Meaning scope language context sort

def checker (scope : Lean.Name) (language : LanguageDef) (context : List TypeExpr) (sort : TypeExpr) :
    Checker (Request context.length) Packet := ⟨check scope language context sort⟩

theorem authority (scope : Lean.Name) (language : LanguageDef) (context : List TypeExpr) (sort : TypeExpr) :
    (checker scope language context sort).Authority (Meaning scope language context sort) where
  sound := check_sound scope language context sort
  complete := check_complete scope language context sort

def service (scope : Lean.Name) (language : LanguageDef) (context : List TypeExpr) (sort : TypeExpr) :
    SemanticService.Service (target scope language context sort) :=
  .certificateBoundary Packet (checker scope language context sort) (authority scope language context sort)

def invocation (scope : Lean.Name) (language : LanguageDef) {context : List TypeExpr} {sort : TypeExpr}
    (request : Request context.length) (submitted : Packet) :
    SemanticServiceInvocation.Request (service scope language context sort) := .certificateBoundary request submitted

theorem invocation_exact (scope : Lean.Name) (language : LanguageDef) {context : List TypeExpr} {sort : TypeExpr}
    (request : Request context.length) (submitted : Packet) :
    (SemanticServiceInvocation.invoke (invocation (sort := sort) scope language request submitted)).acceptedValue = some request ↔
      check scope language context sort request submitted = true := by
  change (if check scope language context sort request submitted then some request else none) = some request ↔ _
  cases check scope language context sort request submitted <;> simp

/-- The table and proof are both finite submitted words. Coverage ranges
over the full original family, including alternative sorted elaborations. -/
theorem full_source_iff_service (scope : Lean.Name)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort) :
    BindingEquationFamilyCongruence.Related (CollectionEquationFamily.family language) first second ↔
      ∃ declarations : List (DeclaredAxiom language), ∃ submitted : Packet,
        (SemanticServiceInvocation.invoke
          (invocation (sort := sort) scope language (sourceRequest scope declarations first second) submitted)).acceptedValue =
            some (sourceRequest scope declarations first second) := by
  constructor
  · intro source
    obtain ⟨declarations, proof, accepted⟩ := (AuthoredBindingEquationServices.full_source_iff_service scope first second).mp source
    refine ⟨declarations, packet declarations proof, (invocation_exact scope language _ _).mpr ?_⟩
    rw [check_packet]
    exact (AuthoredBindingEquationServices.invocation_exact scope declarations _ _).mp accepted
  · rintro ⟨declarations, submitted, accepted⟩
    obtain ⟨checkedTable, _, recoveredFirst, recoveredSecond, firstAt, secondAt, source⟩ :=
      check_sound scope language context sort _ submitted ((invocation_exact scope language _ _).mp accepted)
    have firstSame := (endpointAt_endpoint_iff scope first recoveredFirst).mp firstAt
    have secondSame := (endpointAt_endpoint_iff scope second recoveredSecond).mp secondAt
    refine ⟨equations checkedTable, table_supported checkedTable, ?_⟩
    simpa only [firstSame, secondSame] using source

theorem root_accepted (scope : Lean.Name) (selected : SelectedGenerator language) :
    (SemanticServiceInvocation.invoke
      (invocation (sort := .base selected.declaration.category) scope language
        (sourceRequest scope [selected.declaration] selected.declaration.left selected.declaration.right)
        (packet [selected.declaration] (rootWord selected)))).acceptedValue =
          some (sourceRequest scope [selected.declaration] selected.declaration.left selected.declaration.right) := by
  apply (invocation_exact scope language _ _).mpr
  rw [check_packet]
  exact rootWord_checked scope selected

end SubmittedTable

def serviceTarget (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) : Role → AdmissionObject
  | .sourceAdmission => admissionTarget scope selected context sort
  | .sourceEquation => target scope selected context sort
  | .submittedTableEquation => SubmittedTable.target scope language context sort

def routedService (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) :
    (role : Role) → SemanticService.Service (serviceTarget scope selected context sort role)
  | .sourceAdmission => .directDecision (admissionKernel scope selected context sort)
  | .sourceEquation => service scope selected context sort
  | .submittedTableEquation => SubmittedTable.service scope language context sort

open SemanticService

def requiredInterface (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) :
    (role : Role) → Interface (serviceTarget scope selected context sort role)
  | .sourceAdmission => .directDecision
  | .sourceEquation => .certificateBoundary (List Binary.Alphabet)
  | .submittedTableEquation => .certificateBoundary SubmittedTable.Packet

theorem service_interface_matches (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) (role : Role) :
    InterfaceMatches (RawService.erase (routedService scope selected context sort role))
      (requiredInterface scope selected context sort role) := by
  cases role with
  | sourceAdmission => exact .directDecision _
  | sourceEquation => exact .certificateBoundary _ _
  | submittedTableEquation => exact .certificateBoundary _ _

abbrev RoutedRequest (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) :=
  (role : Role) × SemanticServiceInvocation.Request (routedService scope selected context sort role)

def invokeRouted (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    {context : List TypeExpr} {sort : TypeExpr} (request : RoutedRequest scope selected context sort) :
    SemanticServiceInvocation.Response request.2 := SemanticServiceInvocation.invoke request.2

def routedEquationRequest (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    {context : List TypeExpr} {sort : TypeExpr} (request : Request context.length) (proof : List Binary.Alphabet) :
    RoutedRequest scope selected context sort :=
  ⟨.sourceEquation, invocation (sort := sort) scope selected request proof⟩

theorem routed_equation_exact (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    {context : List TypeExpr} {sort : TypeExpr} (request : Request context.length) (proof : List Binary.Alphabet) :
    (invokeRouted scope selected (routedEquationRequest (sort := sort) scope selected request proof)).acceptedValue = some request ↔
      check scope selected context sort request proof = true :=
  invocation_exact scope selected request proof

def routedSubmittedTableRequest (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    {context : List TypeExpr} {sort : TypeExpr} (request : Request context.length) (submitted : SubmittedTable.Packet) :
    RoutedRequest scope selected context sort :=
  ⟨.submittedTableEquation, SubmittedTable.invocation (sort := sort) scope language request submitted⟩

theorem routed_submitted_table_exact (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    {context : List TypeExpr} {sort : TypeExpr} (request : Request context.length) (submitted : SubmittedTable.Packet) :
    (invokeRouted scope selected (routedSubmittedTableRequest (sort := sort) scope selected request submitted)).acceptedValue = some request ↔
      SubmittedTable.check scope language context sort request submitted = true :=
  SubmittedTable.invocation_exact scope language request submitted

/-- The extensional observer is the already constructed original-family
quotient. This identifies service evidence with equality in that model,
without selecting a new ambient set foundation. -/
theorem quotient_equality_iff_service (scope : Lean.Name)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort) :
    BindingEquationFamilyModel.project (CollectionEquationFamily.family language) first =
        BindingEquationFamilyModel.project (CollectionEquationFamily.family language) second ↔
      ∃ declarations : List (DeclaredAxiom language), ∃ submitted : SubmittedTable.Packet,
        (SemanticServiceInvocation.invoke
          (SubmittedTable.invocation (sort := sort) scope language
            (sourceRequest scope declarations first second) submitted)).acceptedValue =
              some (sourceRequest scope declarations first second) := by
  have modelExact :
      BindingEquationFamilyModel.project (CollectionEquationFamily.family language) first =
          BindingEquationFamilyModel.project (CollectionEquationFamily.family language) second ↔
        BindingEquationFamilyCongruence.Related (CollectionEquationFamily.family language) first second :=
    ⟨fun equal => Quotient.exact equal, fun related => Quotient.sound related⟩
  exact modelExact.trans (SubmittedTable.full_source_iff_service scope first second)

namespace FiniteDeclarations

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations

abbrev Symbol (language : LanguageDef) :=
  BindingSignaturePackage.Symbol (signatureOf language)

/-- The original equation context and both actual sorted endpoints determine
its native constructor requirements. Witness provenance remains in the
source table; no extra computation root is installed by this inventory. -/
def lawInventory (declaration : DeclaredAxiom language) : List (Symbol language) :=
  BindingSignaturePackage.inventory declaration.left ++
    BindingSignaturePackage.inventory declaration.right

def tableInventory : List (DeclaredAxiom language) → List (Symbol language)
  | [] => []
  | declaration :: later => lawInventory declaration ++ tableInventory later

/-- All endpoints share one actual finite environment. In particular, the
source contexts of law instances need not coincide with the request context. -/
def inventory {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (declarations : List (DeclaredAxiom language)) : List (Symbol language) :=
  BindingSignaturePackage.inventory first ++ BindingSignaturePackage.inventory second ++
    tableInventory declarations

theorem first_inventory {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (declarations : List (DeclaredAxiom language)) :
    ∀ symbol ∈ BindingSignaturePackage.inventory first,
      symbol ∈ inventory first second declarations := by
  intro symbol member
  exact List.mem_append_left _ (List.mem_append_left _ member)

theorem second_inventory {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (declarations : List (DeclaredAxiom language)) :
    ∀ symbol ∈ BindingSignaturePackage.inventory second,
      symbol ∈ inventory first second declarations := by
  intro symbol member
  exact List.mem_append_left _ (List.mem_append_right _ member)

theorem law_inventory (declarations : List (DeclaredAxiom language))
    (declaration : DeclaredAxiom language) (present : declaration ∈ declarations) :
    ∀ symbol ∈ lawInventory declaration, symbol ∈ tableInventory declarations := by
  induction declarations with
  | nil => cases present
  | cons first rest inductionHypothesis =>
    intro symbol member
    rcases List.mem_cons.mp present with same | later
    · subst first
      exact List.mem_append_left _ member
    · exact List.mem_append_right _ (inductionHypothesis later symbol member)

theorem table_inventory {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (declarations : List (DeclaredAxiom language))
    (declaration : DeclaredAxiom language) (present : declaration ∈ declarations) :
    ∀ symbol ∈ lawInventory declaration,
      symbol ∈ inventory first second declarations := by
  intro symbol member
  exact List.mem_append_right _ (law_inventory declarations declaration present symbol member)

theorem law_closed (declaration : DeclaredAxiom language) :
    BindingSignaturePackage.Closed (lawInventory declaration) :=
  (BindingSignaturePackage.inventory_closed declaration.left).append
    (BindingSignaturePackage.inventory_closed declaration.right)

theorem table_closed (declarations : List (DeclaredAxiom language)) :
    BindingSignaturePackage.Closed (tableInventory declarations) := by
  induction declarations with
  | nil => intro operator impossible; cases impossible
  | cons declaration later inductionHypothesis =>
    exact (law_closed declaration).append inductionHypothesis

theorem inventory_closed {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (declarations : List (DeclaredAxiom language)) :
    BindingSignaturePackage.Closed (inventory first second declarations) :=
  ((BindingSignaturePackage.inventory_closed first).append
    (BindingSignaturePackage.inventory_closed second)).append (table_closed declarations)

def signature (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (declarations : List (DeclaredAxiom language)) : Declaration.Signature Tower.Head :=
  BindingSignaturePackage.signature (Literal.names scope language) (inventory first second declarations)

def rules (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (declarations : List (DeclaredAxiom language)) : Rules Tower.Head :=
  BindingSignaturePackage.rules (Literal.names scope language) (inventory first second declarations)

theorem wellFormed (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (declarations : List (DeclaredAxiom language)) :
    (signature scope language first second declarations).WellFormed Tower.rules :=
  BindingSignaturePackage.wellFormed (Literal.names scope language)
    (Literal.FiniteDeclarations.declarationName_injective scope language)
    (inventory first second declarations) (inventory_closed first second declarations)

private theorem formed_of_inventory (scope : Lean.Name) (language : LanguageDef)
    {context gamma : List TypeExpr} {sort result : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (declarations : List (DeclaredAxiom language))
    (source : Term (signatureOf language) gamma result)
    (covered : ∀ symbol ∈ BindingSignaturePackage.inventory source,
      symbol ∈ inventory first second declarations) :
    FormationSensitive.Judgment (rules scope language first second declarations)
      (BindingSignatureEmbedding.context (Literal.names scope language) gamma)
      (Literal.encode scope language source)
      (BindingSignatureEmbedding.sortType (Literal.names scope language) result) := by
  apply BindingSignaturePackage.supported_judgment (Literal.names scope language)
    (Literal.FiniteDeclarations.declarationName_injective scope language)
    (inventory first second declarations) source
  · intro operator present
    exact covered _ (List.mem_append_right _ (List.mem_map.mpr ⟨operator, present, rfl⟩))
  · intro sourceSort present
    exact covered _ (List.mem_append_left _ (List.mem_map.mpr ⟨sourceSort, present, rfl⟩))

theorem first_formed (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (declarations : List (DeclaredAxiom language)) :
    FormationSensitive.Judgment (rules scope language first second declarations)
      (BindingSignatureEmbedding.context (Literal.names scope language) context)
      (Literal.encode scope language first)
      (BindingSignatureEmbedding.sortType (Literal.names scope language) sort) :=
  formed_of_inventory scope language first second declarations first
    (first_inventory first second declarations)

theorem second_formed (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (declarations : List (DeclaredAxiom language)) :
    FormationSensitive.Judgment (rules scope language first second declarations)
      (BindingSignatureEmbedding.context (Literal.names scope language) context)
      (Literal.encode scope language second)
      (BindingSignatureEmbedding.sortType (Literal.names scope language) sort) :=
  formed_of_inventory scope language first second declarations second
    (second_inventory first second declarations)

/-- Every retained law endpoint is formed in the same native declaration
package as the request endpoints, at its own original telescope. -/
theorem table_formed (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (declarations : List (DeclaredAxiom language))
    (declaration : DeclaredAxiom language) (present : declaration ∈ declarations) :
    FormationSensitive.Judgment (rules scope language first second declarations)
      (BindingSignatureEmbedding.context (Literal.names scope language) declaration.context)
      (Literal.encode scope language declaration.left)
      (BindingSignatureEmbedding.sortType (Literal.names scope language) (.base declaration.category)) ∧
    FormationSensitive.Judgment (rules scope language first second declarations)
      (BindingSignatureEmbedding.context (Literal.names scope language) declaration.context)
      (Literal.encode scope language declaration.right)
      (BindingSignatureEmbedding.sortType (Literal.names scope language) (.base declaration.category)) := by
  constructor
  · apply formed_of_inventory scope language first second declarations declaration.left
    intro symbol member
    exact table_inventory first second declarations declaration present symbol (List.mem_append_left _ member)
  · apply formed_of_inventory scope language first second declarations declaration.right
    intro symbol member
    exact table_inventory first second declarations declaration present symbol (List.mem_append_right _ member)

@[simp] theorem computation_empty (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (declarations : List (DeclaredAxiom language)) :
    (rules scope language first second declarations).computation = RootComputation.empty :=
  BindingSignaturePackage.computation_empty (Literal.names scope language) (inventory first second declarations)

/-- Installing the finite declarations does not turn source collection laws
into ambient native equations. Native conversion between these literal
images still reflects original source syntax equality. -/
theorem conversion_iff_eq (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (declarations : List (DeclaredAxiom language)) :
    Conv (rules scope language first second declarations).headEq
      (Literal.encode scope language first) (Literal.encode scope language second)
      (rules scope language first second declarations).computation ↔ first = second :=
  Literal.conversion_iff_eq scope language (rules scope language first second declarations)
    (computation_empty scope language first second declarations) LevelTower.headEq_symmetric first second

/-- A decoded submitted request retains original terms and the original
checked law table. Its declaration package is computed below; no semantic
correctness field is accepted from a caller. -/
structure Selected (context : List TypeExpr) (sort : TypeExpr) where
  declarations : List (DeclaredAxiom language)
  first : Term (signatureOf language) context sort
  second : Term (signatureOf language) context sort

def profile? (scope : Lean.Name) (language : LanguageDef)
    (context : List TypeExpr) (sort : TypeExpr)
    (request : Request context.length) (submitted : SubmittedTable.Packet) :
    Option (Selected (language := language) context sort) := do
  let declarations ← Binary.canonicalDecodeWith (CollectionEquationWire.tableCodec language) submitted.tableWord
  let first ← admitEndpoint? scope context sort request.first
  let second ← admitEndpoint? scope context sort request.second
  if SubmittedTable.check scope language context sort request submitted then
    some ⟨declarations, first, second⟩ else none

theorem profile?_exact (scope : Lean.Name) (language : LanguageDef)
    (context : List TypeExpr) (sort : TypeExpr)
    (request : Request context.length) (submitted : SubmittedTable.Packet)
    (selected : Selected (language := language) context sort) :
    profile? scope language context sort request submitted = some selected ↔
      Binary.canonicalDecodeWith (CollectionEquationWire.tableCodec language) submitted.tableWord = some selected.declarations ∧
      admitEndpoint? scope context sort request.first = some selected.first ∧
      admitEndpoint? scope context sort request.second = some selected.second ∧
      SubmittedTable.check scope language context sort request submitted = true := by
  cases selected with
  | mk declarations first second =>
    cases tableRead : Binary.canonicalDecodeWith (CollectionEquationWire.tableCodec language) submitted.tableWord <;>
      cases firstRead : admitEndpoint? (language := language) scope context sort request.first <;>
      cases secondRead : admitEndpoint? (language := language) scope context sort request.second <;>
      cases accepted : SubmittedTable.check scope language context sort request submitted <;>
      simp [profile?, tableRead, firstRead, secondRead, accepted, Selected.mk.injEq]

theorem profile?_complete (scope : Lean.Name) (language : LanguageDef)
    (context : List TypeExpr) (sort : TypeExpr)
    (request : Request context.length) (submitted : SubmittedTable.Packet)
    (accepted : SubmittedTable.check scope language context sort request submitted = true) :
    ∃ selected : Selected (language := language) context sort,
      profile? scope language context sort request submitted = some selected := by
  cases tableRead : Binary.canonicalDecodeWith (CollectionEquationWire.tableCodec language) submitted.tableWord with
  | none => simp only [SubmittedTable.check, tableRead] at accepted; cases accepted
  | some declarations =>
    cases firstRead : admitEndpoint? (language := language) scope context sort request.first with
    | none =>
      simp only [SubmittedTable.check, tableRead, AuthoredBindingEquationServices.check,
        firstRead, Bool.and_false] at accepted
      cases accepted
    | some first =>
      cases secondRead : admitEndpoint? (language := language) scope context sort request.second with
      | none =>
        simp only [SubmittedTable.check, tableRead, AuthoredBindingEquationServices.check,
          firstRead, secondRead, Bool.and_false] at accepted
        cases accepted
      | some second =>
        exact ⟨⟨declarations, first, second⟩,
          (profile?_exact scope language context sort request submitted _).mpr
            ⟨tableRead, firstRead, secondRead, accepted⟩⟩

/-- The returned profile earns the original equality, actual literal request
metadata and its checked table. Signature formation is then derived from
these reconstructed terms, rather than supplied by request data. -/
theorem profile?_sound (scope : Lean.Name) (language : LanguageDef)
    (context : List TypeExpr) (sort : TypeExpr)
    (request : Request context.length) (submitted : SubmittedTable.Packet)
    (selected : Selected (language := language) context sort)
    (read : profile? scope language context sort request submitted = some selected) :
    HeaderAt scope selected.declarations context sort request ∧
      EndpointAt scope context sort request.first selected.first ∧
      EndpointAt scope context sort request.second selected.second ∧
      EqClosure (equations selected.declarations) selected.first selected.second := by
  obtain ⟨tableRead, firstRead, secondRead, accepted⟩ :=
    (profile?_exact scope language context sort request submitted selected).mp read
  have checked : AuthoredBindingEquationServices.check scope selected.declarations context sort request submitted.proofWord = true := by
    simpa only [SubmittedTable.check, tableRead] using accepted
  simp only [AuthoredBindingEquationServices.check, Bool.and_eq_true, firstRead, secondRead] at checked
  obtain ⟨certificate, _, valid⟩ :=
    (Wire.checkEquationBinary_exact language (equations selected.declarations)
      submitted.proofWord selected.first selected.second).mp checked.2
  exact ⟨(headerMatches_exact scope selected.declarations context sort request).mp checked.1,
    (admitEndpoint?_exact scope context sort request.first selected.first).mp firstRead,
    (admitEndpoint?_exact scope context sort request.second selected.second).mp secondRead,
    EqualityCertificates.check_sound certificate selected.first selected.second valid⟩

def Selected.signature (scope : Lean.Name) {context : List TypeExpr} {sort : TypeExpr}
    (selected : Selected (language := language) context sort) : Declaration.Signature Tower.Head :=
  FiniteDeclarations.signature scope language selected.first selected.second selected.declarations

def Selected.rules (scope : Lean.Name) {context : List TypeExpr} {sort : TypeExpr}
    (selected : Selected (language := language) context sort) : Rules Tower.Head :=
  FiniteDeclarations.rules scope language selected.first selected.second selected.declarations

/-- The accepted native endpoints and every retained source-law endpoint have
formed judgments in one computed finite declaration environment. -/
theorem profile?_formed (scope : Lean.Name) (language : LanguageDef)
    (context : List TypeExpr) (sort : TypeExpr)
    (request : Request context.length) (submitted : SubmittedTable.Packet)
    (selected : Selected (language := language) context sort)
    (read : profile? scope language context sort request submitted = some selected) :
    (selected.signature scope).WellFormed Tower.rules ∧
      FormationSensitive.Judgment (selected.rules scope)
        (BindingSignatureEmbedding.context (Literal.names scope language) context)
        request.first.literal request.nativeType ∧
      FormationSensitive.Judgment (selected.rules scope)
        (BindingSignatureEmbedding.context (Literal.names scope language) context)
        request.second.literal request.nativeType ∧
      ∀ declaration ∈ selected.declarations,
        FormationSensitive.Judgment (selected.rules scope)
          (BindingSignatureEmbedding.context (Literal.names scope language) declaration.context)
          (Literal.encode scope language declaration.left)
          (BindingSignatureEmbedding.sortType (Literal.names scope language) (.base declaration.category)) ∧
        FormationSensitive.Judgment (selected.rules scope)
          (BindingSignatureEmbedding.context (Literal.names scope language) declaration.context)
          (Literal.encode scope language declaration.right)
          (BindingSignatureEmbedding.sortType (Literal.names scope language) (.base declaration.category)) := by
  obtain ⟨header, firstAt, secondAt, _source⟩ := profile?_sound scope language context sort request submitted selected read
  refine ⟨wellFormed scope language selected.first selected.second selected.declarations, ?_, ?_, ?_⟩
  · rw [firstAt.1, header.2.2.2.2.2.2.2]
    exact first_formed scope language selected.first selected.second selected.declarations
  · rw [secondAt.1, header.2.2.2.2.2.2.2]
    exact second_formed scope language selected.first selected.second selected.declarations
  · intro declaration present
    exact table_formed scope language selected.first selected.second selected.declarations declaration present

end FiniteDeclarations

/-! ## Whole external requests -/

namespace External

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PatternCodec
private abbrev pattern := CertificateDataEncoding.patternCodec
private abbrev head := WithScalars.towerHeadCodec binaryScalars

def nativeTerm (arity : Nat) : Codec (Tower.Tm arity) := pattern.mapped
  (WithScalars.encodeTm binaryScalars head)
  (WithScalars.decodeTm? binaryScalars head arity)
  (WithScalars.decodeTm?_encodeTm binaryScalars head)

private def data : Codec Data := ⟨id, some, fun _ => rfl⟩
def word : Codec (List Binary.Alphabet) := Codec.string.mapped Binary.Text.render
  Binary.Text.parse Binary.Text.parse_render

def endpointCodec (arity : Nat) : Codec (Endpoint arity) :=
  (Codec.prod (nativeTerm arity) (nativeTerm arity)).mapped
    (fun value => (value.literal, value.source))
    (fun fields => some ⟨fields.1, fields.2⟩) (fun _ => rfl)

/-- Both complete source metadata and proposed native fields are physically
present. Native scope is checked by the original native syntax decoder. -/
def requestCodec (arity : Nat) : Codec (Request arity) :=
  (Codec.prod Codec.name (Codec.prod Wire.Header.codec (Codec.prod (Codec.list data)
    (Codec.prod (Codec.list Wire.typeCodec) (Codec.prod Wire.typeCodec
      (Codec.prod (nativeTerm arity) (Codec.prod (endpointCodec arity) (endpointCodec arity)))))))).mapped
    (fun request => (request.scopeName, (request.languageName, request.types, request.rows),
      request.equations, request.context, request.sort, request.nativeType, request.first, request.second))
    (fun fields => some ⟨fields.1, fields.2.1.1, fields.2.1.2.1, fields.2.1.2.2,
      fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1, fields.2.2.2.2.2.1,
      fields.2.2.2.2.2.2.1, fields.2.2.2.2.2.2.2⟩) (fun _ => rfl)

private def roleNumber : Role → Nat
  | .sourceAdmission => 0 | .sourceEquation => 1 | .submittedTableEquation => 2
private def readRole : Nat → Option Role
  | 0 => some .sourceAdmission | 1 => some .sourceEquation | 2 => some .submittedTableEquation | _ => none

def roles : Codec Role := Codec.nat.mapped roleNumber readRole (fun role => by cases role <;> rfl)

def submittedCodec : Codec SubmittedTable.Packet := (Codec.prod word word).mapped
  (fun packet => (packet.tableWord, packet.proofWord))
  (fun fields => some ⟨fields.1, fields.2⟩) (fun _ => rfl)

def Fields (arity : Nat) : Role → Type
  | .sourceAdmission => Request arity × List Binary.Alphabet
  | .sourceEquation => Request arity × SubmittedTable.Packet
  | .submittedTableEquation => Request arity × SubmittedTable.Packet

abbrev Packet := Σ context : List TypeExpr, Σ _sort : TypeExpr, Σ role : Role, Fields context.length role

private def fieldsCodec (arity : Nat) : (role : Role) → Codec (Fields arity role)
  | .sourceAdmission => Codec.prod (requestCodec arity) word
  | .sourceEquation => Codec.prod (requestCodec arity) submittedCodec
  | .submittedTableEquation => Codec.prod (requestCodec arity) submittedCodec

private def payload : Codec Packet := Codec.sigma (Codec.list Wire.typeCodec)
  (fun context => Codec.sigma Wire.typeCodec (fun _ => Codec.sigma roles (fieldsCodec context.length)))

/-- The versioned envelope distinguishes this proof service from other
native services even when an inner payload happens to have a similar shape. -/
def packetCodec : Codec Packet where
  put value := .pair (.atom 20261015) (payload.put value)
  get
    | .pair (.atom 20261015) body => payload.get body
    | _ => none
  get_put value := payload.get_put value

/-- A client profile fixes the exact authority footprint. Reconstructing it
creates a declaration-only language: arbitrary authored equations and
rewrite rules are not supplied by this profile format. -/
def profileCodec : Codec (Lean.Name × (String × List TypeDecl × List GrammarRule)) :=
  Codec.prod Codec.name Wire.Header.codec

def profileLanguage (header : String × List TypeDecl × List GrammarRule) : LanguageDef :=
  LanguageDef.ofCore header.1 header.2.1 header.2.2 [] []

def encodeRequest (value : Packet) : List Binary.Alphabet := Binary.encodeWith packetCodec value
def decodeRequest (input : List Binary.Alphabet) : Option Packet := Binary.canonicalDecodeWith packetCodec input

theorem decodeRequest_encodeRequest (value : Packet) :
    decodeRequest (encodeRequest value) = some value := Binary.canonicalDecodeWith_encodeWith packetCodec value

theorem decodeRequest_exact (input : List Binary.Alphabet) (value : Packet) :
    decodeRequest input = some value ↔ encodeRequest value = input := Binary.canonicalDecodeWith_exact packetCodec input value

theorem request_trailing_refused (value : Packet) (tail : List Binary.Alphabet)
    (nonempty : tail.isEmpty = false) : decodeRequest (encodeRequest value ++ tail) = none :=
  Binary.canonicalDecodeWith_trailing_refused packetCodec value tail nonempty

/-- Table decoding authorizes each original source law. The selected role
then invokes the corresponding existing service checker. -/
def respond? (scope : Lean.Name) (language : LanguageDef) : Packet → Option Data
  | ⟨context, sort, .sourceAdmission, request, tableWord⟩ => do
      let declarations ← Binary.canonicalDecodeWith (CollectionEquationWire.tableCodec language) tableWord
      if checkAdmission scope declarations context sort request then some (.atom 0) else none
  | ⟨context, sort, .sourceEquation, request, submitted⟩ => do
      let declarations ← Binary.canonicalDecodeWith (CollectionEquationWire.tableCodec language) submitted.tableWord
      if check scope declarations context sort request submitted.proofWord then some (.atom 0) else none
  | ⟨context, sort, .submittedTableEquation, request, submitted⟩ =>
      if SubmittedTable.check scope language context sort request submitted then some (.atom 0) else none

def ReplyMeaning (scope : Lean.Name) (language : LanguageDef) : Packet → Data → Prop
  | ⟨context, sort, .sourceAdmission, request, _⟩, result =>
      result = .atom 0 ∧ ∃ declarations : List (DeclaredAxiom language),
        AdmissionMeaning scope declarations context sort request
  | ⟨context, sort, .sourceEquation, request, _⟩, result =>
      result = .atom 0 ∧ SubmittedTable.Meaning scope language context sort request
  | ⟨context, sort, .submittedTableEquation, request, _⟩, result =>
      result = .atom 0 ∧ SubmittedTable.Meaning scope language context sort request

theorem respond?_sound (scope : Lean.Name) (language : LanguageDef)
    (value : Packet) (result : Data) (accepted : respond? scope language value = some result) :
    ReplyMeaning scope language value result := by
  obtain ⟨context, sort, role, fields⟩ := value
  cases role with
  | sourceAdmission =>
    obtain ⟨request, tableWord⟩ := fields
    cases tableRead : Binary.canonicalDecodeWith (CollectionEquationWire.tableCodec language) tableWord with
    | none => simp only [respond?, tableRead, Bind.bind, Option.bind] at accepted; cases accepted
    | some declarations =>
      simp only [respond?, tableRead, Bind.bind, Option.bind] at accepted
      split at accepted
      · rename_i checked
        exact ⟨(Option.some.inj accepted).symm,
          declarations, (checkAdmission_exact scope declarations context sort request).mp checked⟩
      · cases accepted
  | sourceEquation =>
    obtain ⟨request, submitted⟩ := fields
    cases tableRead : Binary.canonicalDecodeWith (CollectionEquationWire.tableCodec language) submitted.tableWord with
    | none => simp only [respond?, tableRead, Bind.bind, Option.bind] at accepted; cases accepted
    | some declarations =>
      simp only [respond?, tableRead, Bind.bind, Option.bind] at accepted
      split at accepted
      · rename_i checked
        exact ⟨(Option.some.inj accepted).symm,
          declarations, check_sound scope declarations context sort request submitted.proofWord checked⟩
      · cases accepted
  | submittedTableEquation =>
    obtain ⟨request, submitted⟩ := fields
    simp only [respond?] at accepted
    split at accepted
    · rename_i checked
      exact ⟨(Option.some.inj accepted).symm,
        SubmittedTable.check_sound scope language context sort request submitted checked⟩
    · cases accepted

/-- Successful output binds the original complete request as well as its
service result. The same whole-word decoder refuses trailing input. -/
def run (scope : Lean.Name) (language : LanguageDef) (input : List Binary.Alphabet) : Option (List Binary.Alphabet) := do
  let request ← decodeRequest input
  let result ← respond? scope language request
  some (Binary.encodeData (.pair (packetCodec.put request) result))

theorem run_encodeRequest (scope : Lean.Name) (language : LanguageDef) (value : Packet)
    (result : Data) (accepted : respond? scope language value = some result) :
    run scope language (encodeRequest value) =
      some (Binary.encodeData (.pair (packetCodec.put value) result)) := by
  simp only [run, decodeRequest_encodeRequest, accepted, Bind.bind, Option.bind]

theorem run_sound (scope : Lean.Name) (language : LanguageDef) (input output : List Binary.Alphabet)
    (accepted : run scope language input = some output) :
    ∃ value : Packet, ∃ result : Data,
      encodeRequest value = input ∧ output = Binary.encodeData (.pair (packetCodec.put value) result) ∧
      ReplyMeaning scope language value result := by
  cases read : decodeRequest input with
  | none => simp only [run, read, Bind.bind, Option.bind] at accepted; cases accepted
  | some value =>
    cases responded : respond? scope language value with
    | none => simp only [run, read, responded, Bind.bind, Option.bind] at accepted; cases accepted
    | some result =>
      exact ⟨value, result, (decodeRequest_exact input value).mp read,
        (by simpa only [run, read, responded, Bind.bind, Option.bind, Option.some.injEq] using accepted.symm),
        respond?_sound scope language value result responded⟩

theorem run_trailing_refused (scope : Lean.Name) (language : LanguageDef) (value : Packet)
    (tail : List Binary.Alphabet) (nonempty : tail.isEmpty = false) :
    run scope language (encodeRequest value ++ tail) = none := by
  simp only [run, request_trailing_refused value tail nonempty, Bind.bind, Option.bind]

/-- Every original collection-family equation has a complete external
request accepted at its exact literal native endpoints. -/
theorem full_source_external_complete (scope : Lean.Name)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort)
    (source : BindingEquationFamilyCongruence.Related (CollectionEquationFamily.family language) first second) :
    ∃ declarations : List (DeclaredAxiom language), ∃ submitted : SubmittedTable.Packet,
      run scope language (encodeRequest ⟨context, sort, .submittedTableEquation,
        sourceRequest scope declarations first second, submitted⟩) =
          some (Binary.encodeData (.pair (packetCodec.put ⟨context, sort, .submittedTableEquation,
            sourceRequest scope declarations first second, submitted⟩) (.atom 0))) := by
  obtain ⟨declarations, submitted, accepted⟩ := (SubmittedTable.full_source_iff_service scope first second).mp source
  refine ⟨declarations, submitted, run_encodeRequest scope language _ (.atom 0) ?_⟩
  simp only [respond?, (SubmittedTable.invocation_exact scope language _ _).mp accepted, ite_true]

theorem run_submitted_accepted_iff (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (request : Request context.length) (submitted : SubmittedTable.Packet) :
    (∃ output, run scope language (encodeRequest ⟨context, sort, .submittedTableEquation, request, submitted⟩) = some output) ↔
      SubmittedTable.check scope language context sort request submitted = true := by
  cases checked : SubmittedTable.check scope language context sort request submitted <;>
    simp [run, decodeRequest_encodeRequest, respond?, checked]

/-- Both directions retain the original full source equation family and the
literal endpoint comparison, including alternative intrinsic elaborations. -/
theorem full_source_iff_external (scope : Lean.Name)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort) :
    BindingEquationFamilyCongruence.Related (CollectionEquationFamily.family language) first second ↔
      ∃ declarations : List (DeclaredAxiom language), ∃ submitted : SubmittedTable.Packet, ∃ output,
        run scope language (encodeRequest ⟨context, sort, .submittedTableEquation,
          sourceRequest scope declarations first second, submitted⟩) = some output := by
  rw [SubmittedTable.full_source_iff_service scope first second]
  constructor
  · rintro ⟨declarations, submitted, accepted⟩
    exact ⟨declarations, submitted, (run_submitted_accepted_iff scope language _ _).mpr
      ((SubmittedTable.invocation_exact scope language _ _).mp accepted)⟩
  · rintro ⟨declarations, submitted, output, accepted⟩
    exact ⟨declarations, submitted, (SubmittedTable.invocation_exact scope language _ _).mpr
      ((run_submitted_accepted_iff scope language _ _).mp ⟨output, accepted⟩)⟩

/-- The same accepted complete external request computes the finite profile;
its formation theorem applies to the physically submitted native fields. -/
theorem run_submitted_profile (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (request : Request context.length) (submitted : SubmittedTable.Packet) (output : List Binary.Alphabet)
    (accepted : run scope language (encodeRequest ⟨context, sort, .submittedTableEquation, request, submitted⟩) = some output) :
    ∃ selected : FiniteDeclarations.Selected (language := language) context sort,
      FiniteDeclarations.profile? scope language context sort request submitted = some selected :=
  FiniteDeclarations.profile?_complete scope language context sort request submitted
    ((run_submitted_accepted_iff scope language _ _).mp ⟨output, accepted⟩)

end External

/-- The optional target checker agrees with the independent original-source
checker on every literal encoded request; target formation stays separate. -/
theorem source_check_agrees (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Term (signatureOf language) context sort) (proof : List Binary.Alphabet) :
    check scope selected context sort (sourceRequest scope selected first second) proof =
      Mettapedia.GSLT.LanguageDef.AuthoredBindingEquationServices.check scope selected context sort
        (Mettapedia.GSLT.LanguageDef.AuthoredBindingEquationServices.sourceRequest scope selected first second) proof := by
  rw [check_sourceRequest, Mettapedia.GSLT.LanguageDef.AuthoredBindingEquationServices.check_sourceRequest]

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingEquationServices
