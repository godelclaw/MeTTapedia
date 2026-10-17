import Mettapedia.GSLT.LanguageDef.CertificateDataEncoding
import Mettapedia.GSLT.LanguageDef.BindingCollectionEquationGenerators
import Mettapedia.GSLT.LanguageDef.BindingCollectionEquationWire
import Mettapedia.GSLT.LanguageDef.SemanticServiceInvocation

/-!
# Original authored binding-equation services

The selected observation is original finite contextual equality over a checked
collection-law table. Requests retain the complete declaration footprint,
source context and sort, and canonical original term words. Law admission
constructs the existing DeclaredAxiom witnesses before original equality replay.
No target type calculus or literal target image is required by source checking.

Optional typed representations consume this source boundary downstream.
The source wire alone makes no executed resource-bound claim.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.AuthoredBindingEquationServices

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.GSLT.LanguageDef
open SemanticService
open KernelAuthority SemanticEvidence
open BindingSyntax CollectionEquationFamily CollectionEquationGenerators

variable {language : LanguageDef}

/-- Exact original source syntax in its canonical finite word. -/
def sourceData {context : List TypeExpr} {sort : TypeExpr}
    (source : Term (signatureOf language) context sort) : List Binary.Alphabet :=
  Binary.encodeWith (Wire.termCodec language context sort) source

def sourceData? (context : List TypeExpr) (sort : TypeExpr)
    (word : List Binary.Alphabet) : Option (Term (signatureOf language) context sort) :=
  Binary.canonicalDecodeWith (Wire.termCodec language context sort) word

theorem sourceData?_sourceData {context : List TypeExpr} {sort : TypeExpr}
    (source : Term (signatureOf language) context sort) :
    sourceData? context sort (sourceData source) = some source :=
  Binary.canonicalDecodeWith_encodeWith (Wire.termCodec language context sort) source

/-- A canonical original source endpoint; the context and sort are retained
in the enclosing request and used by the existing term decoder. -/
structure Endpoint (n : Nat) where
  source : List Binary.Alphabet

def endpoint (_scope : Lean.Name) {context : List TypeExpr} {sort : TypeExpr}
    (source : Term (signatureOf language) context sort) : Endpoint context.length :=
  ⟨sourceData source⟩

def EndpointAt (_scope : Lean.Name) (context : List TypeExpr) (sort : TypeExpr)
    (native : Endpoint context.length) (source : Term (signatureOf language) context sort) : Prop :=
  native.source = sourceData source

def admitEndpoint? (_scope : Lean.Name) (context : List TypeExpr) (sort : TypeExpr)
    (native : Endpoint context.length) : Option (Term (signatureOf language) context sort) := do
  let source ← sourceData? context sort native.source
  if native.source = sourceData source then
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
  · intro represented
    change native.source = sourceData source at represented
    simp only [admitEndpoint?, represented, sourceData?_sourceData, Bind.bind, Option.bind, ite_true]

theorem admitEndpoint?_endpoint (scope : Lean.Name) {context : List TypeExpr} {sort : TypeExpr}
    (source : Term (signatureOf language) context sort) :
    admitEndpoint? scope context sort (endpoint scope source) = some source :=
  (admitEndpoint?_exact scope context sort (endpoint scope source) source).mpr rfl

private def declarationCodec (context : List TypeExpr) (sort : TypeExpr) :=
  Codec.prod (Wire.termCodec language context sort) (Wire.termCodec language context sort)

/-- The complete retained endpoints, context and source sort identify each
equation in the selected environment, independently of its proof index. -/
def equations (declarations : List (DeclaredAxiom language)) : List (EqAxiom (signatureOf language) []) :=
  declarations.map DeclaredAxiom.toAxiom

def selectedTable (selected : List (SelectedGenerator language)) : List (DeclaredAxiom language) :=
  selected.map SelectedGenerator.declaration

theorem equations_selectedTable (selected : List (SelectedGenerator language)) :
    equations (selectedTable selected) = CollectionEquationGenerators.equations selected := by
  simp only [equations, selectedTable, CollectionEquationGenerators.equations, List.map_map]
  rfl

def environmentData (selected : List (DeclaredAxiom language)) : List Data :=
  selected.map fun declaration =>
    .pair ((Codec.list Wire.typeCodec).put declaration.context)
      (.pair (Wire.typeCodec.put (.base declaration.category))
        ((declarationCodec declaration.context (.base declaration.category)).put
          (declaration.left, declaration.right)))

structure Request (n : Nat) where
  scopeName : Lean.Name
  languageName : String
  types : List TypeDecl
  rows : List GrammarRule
  equations : List Data
  context : List TypeExpr
  sort : TypeExpr
  first : Endpoint n
  second : Endpoint n

def headerMatches (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) (request : Request context.length) : Bool :=
  decide (request.scopeName = scope ∧ request.languageName = language.name ∧
    request.types = language.types ∧ request.rows = language.terms ∧
    request.equations = environmentData selected ∧ request.context = context ∧ request.sort = sort)

def HeaderAt (scope : Lean.Name) (selected : List (DeclaredAxiom language))
    (context : List TypeExpr) (sort : TypeExpr) (request : Request context.length) : Prop :=
  request.scopeName = scope ∧ request.languageName = language.name ∧
    request.types = language.types ∧ request.rows = language.terms ∧
    request.equations = environmentData selected ∧ request.context = context ∧ request.sort = sort

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
    exact Binary.encodeWith_injective (Wire.termCodec language context sort) admitted
  · intro same
    cases same
    exact rfl

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
      first, second, rfl, rfl, source⟩

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

theorem table_supported (declarations : List (DeclaredAxiom language)) :
    BindingEquationFamilyCongruence.Supported (CollectionEquationFamily.family language) (equations declarations) := by
  intro equation member
  obtain ⟨declaration, _, same⟩ := List.mem_map.mp member
  exact ⟨declaration, same⟩

/-- This is an existence proof over the original finite source derivation,
not a program that chooses source declarations from untrusted inputs. -/
theorem supported_table (fragment : List (EqAxiom (signatureOf language) []))
    (supported : BindingEquationFamilyCongruence.Supported (CollectionEquationFamily.family language) fragment) :
    ∃ declarations : List (DeclaredAxiom language), equations declarations = fragment := by
  induction fragment with
  | nil => exact ⟨[], rfl⟩
  | cons equation rest ih =>
      obtain ⟨declaration, same⟩ := supported equation List.mem_cons_self
      obtain ⟨later, laterSame⟩ := ih (fun current member => supported current (List.mem_cons_of_mem _ member))
      exact ⟨declaration :: later, congrArg₂ List.cons same laterSame⟩

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

/-- Construct an actual complete certificate word for each original law
producer, rather than selecting a word from the coverage theorem. -/
def rootWord (selected : SelectedGenerator language) : List Binary.Alphabet :=
  let declaration := selected.declaration
  let proof := selected.instanceCertificate
    (EqualityCertificates.Substitution.quote (S := signatureOf language)
      declaration.context (fun _ position => .var position))
  Binary.encodeWith (Wire.equationCodec language [declaration.toAxiom]
    declaration.context (.base declaration.category)) proof

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

inductive Role where
  | sourceAdmission
  | sourceEquation
  | submittedTableEquation
  deriving DecidableEq

def requiredRoles : List Role := [.sourceAdmission, .sourceEquation, .submittedTableEquation]

theorem requiredRoles_complete (role : Role) : role ∈ requiredRoles := by cases role <;> decide

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



/-! ## Whole external requests -/

namespace External

private def data : Codec Data := ⟨id, some, fun _ => rfl⟩
def word : Codec (List Binary.Alphabet) := Codec.string.mapped Binary.Text.render
  Binary.Text.parse Binary.Text.parse_render

def endpointCodec (arity : Nat) : Codec (Endpoint arity) := word.mapped
  (fun value => value.source) (fun source => some ⟨source⟩) (fun _ => rfl)

/-- Complete source metadata and both canonical original source endpoints. -/
def requestCodec (arity : Nat) : Codec (Request arity) :=
  (Codec.prod Codec.name (Codec.prod Wire.Header.codec (Codec.prod (Codec.list data)
    (Codec.prod (Codec.list Wire.typeCodec) (Codec.prod Wire.typeCodec
      (Codec.prod (endpointCodec arity) (endpointCodec arity))))))).mapped
    (fun request => (request.scopeName, (request.languageName, request.types, request.rows),
      request.equations, request.context, request.sort, request.first, request.second))
    (fun fields => some ⟨fields.1, fields.2.1.1, fields.2.1.2.1, fields.2.1.2.2,
      fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1,
      fields.2.2.2.2.2.1, fields.2.2.2.2.2.2⟩) (fun _ => rfl)

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
def requestTag : String := "GSLT.BindingEquations.Request.v1"

def packetCodec : Codec Packet := (Codec.prod Codec.string payload).mapped
  (fun value => (requestTag, value))
  (fun fields => if fields.1 = requestTag then some fields.2 else none)
  (fun _ => by simp only [ite_true])

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
request accepted at its exact canonical source endpoints. -/
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

end External

end Mettapedia.GSLT.LanguageDef.AuthoredBindingEquationServices
