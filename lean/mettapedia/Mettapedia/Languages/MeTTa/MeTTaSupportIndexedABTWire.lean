import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.GSLT.LanguageDef.ContextSupportTransport
import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.GSLT.LanguageDef.CertificateGSLTWireFormat
import Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval

/-!
# Support-indexed ABT lowering at the MeTTa wire boundary

This module gives the revisioned `match`/`let`/`eval` candidate an explicit,
fail-closed binding boundary.

There are two independent kinds of variables at that boundary.

* MeTTa matcher variables select values and are represented by finite support
  and assignment tables.
* Canonical object binders are de Bruijn indices inside those values.

The support table records the context in which an assigned value was obtained.
Using that value at a different depth performs a checked signed shift.  Moving
outward fails when it would discard or capture a referenced binder.  Moving
inward is ordinary weakening.

The packet codec uses the existing canonical `WireTerm` and `Pattern` codec.
Consequently the wire theorem is about the same rich pattern universe as the
Lean semantics rather than a hand-picked syntax fragment.
-/

namespace Mettapedia.Languages.MeTTa.MeTTaSupportIndexedABTWire

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-! ## Checked signed de Bruijn transport -/

mutual

/-- Remove `amount` ambient binder levels at `cutoff`.  Failure means that a
removed level was actually referenced, so returning a term would capture or
discard an index. -/
def lowerBVars? (cutoff amount : Nat) : Pattern → Option Pattern
  | .bvar index =>
      if index < cutoff then
        some (.bvar index)
      else if index < cutoff + amount then
        none
      else
        some (.bvar (index - amount))
  | .fvar name => some (.fvar name)
  | .apply constructor arguments => do
      let lowered ← lowerBVarList? cutoff amount arguments
      some (.apply constructor lowered)
  | .lambda binder body => do
      let lowered ← lowerBVars? (cutoff + 1) amount body
      some (.lambda binder lowered)
  | .multiLambda arity binders body => do
      let lowered ← lowerBVars? (cutoff + arity) amount body
      some (.multiLambda arity binders lowered)
  | .subst body replacement => do
      let loweredBody ← lowerBVars? (cutoff + 1) amount body
      let loweredReplacement ← lowerBVars? cutoff amount replacement
      some (.subst loweredBody loweredReplacement)
  | .collection collectionType elements rest => do
      let lowered ← lowerBVarList? cutoff amount elements
      some (.collection collectionType lowered rest)
termination_by pattern => sizeOf pattern

def lowerBVarList? (cutoff amount : Nat) :
    List Pattern → Option (List Pattern)
  | [] => some []
  | pattern :: patterns => do
      let lowered ← lowerBVars? cutoff amount pattern
      let rest ← lowerBVarList? cutoff amount patterns
      some (lowered :: rest)
termination_by patterns => sizeOf patterns

end

/-- The failure guard used by the physical signed-shift provider is exact:
an outward transport fails precisely when the removed interval contains the
referenced index.  Under a binder, `cutoff` moves with the binder depth, so
this same interval test is also the capture check. -/
theorem lowerBVars?_bvar_eq_none_iff
    (cutoff amount index : Nat) :
    lowerBVars? cutoff amount (.bvar index) = none ↔
      cutoff ≤ index ∧ index < cutoff + amount := by
  simp only [lowerBVars?]
  by_cases below : index < cutoff
  · simp [below, Nat.not_le_of_lt below]
  · simp [below, Nat.le_of_not_gt below]

/-- An index above the removed interval survives at the uniquely shifted
index. -/
theorem lowerBVars?_bvar_of_above
    (cutoff amount index : Nat) (above : cutoff + amount ≤ index) :
    lowerBVars? cutoff amount (.bvar index) =
      some (.bvar (index - amount)) := by
  simp [lowerBVars?, Nat.not_lt_of_ge above,
    Nat.not_lt_of_ge (Nat.le_trans (Nat.le_add_right cutoff amount) above)]

/-- Transport a canonical ABT from its authored support depth to one use
depth.  Weakening is total; strengthening is checked. -/
def transportBVars? (supportDepth useDepth : Nat)
    (pattern : Pattern) : Option Pattern :=
  if supportDepth ≤ useDepth then
    some (liftBVars 0 (useDepth - supportDepth) pattern)
  else
    lowerBVars? 0 (supportDepth - useDepth) pattern

@[simp] theorem transportBVars?_of_le
    {supportDepth useDepth : Nat} (within : supportDepth ≤ useDepth)
    (pattern : Pattern) :
    transportBVars? supportDepth useDepth pattern =
      some (liftBVars 0 (useDepth - supportDepth) pattern) := by
  simp [transportBVars?, within]

@[simp] theorem transportBVars?_same (depth : Nat) (pattern : Pattern) :
    transportBVars? depth depth pattern = some pattern := by
  simp [transportBVars?, liftBVars_zero]

/-! ## Explicit finite support and assignment packets -/

structure SupportEntry where
  name : String
  context : List TypeExpr
deriving Repr, DecidableEq

structure AssignmentEntry where
  name : String
  value : Pattern
deriving Repr, DecidableEq

structure SupportedSubstitutionPacket where
  support : List SupportEntry
  assignment : List AssignmentEntry
  useDepth : Nat
  body : Pattern
deriving Repr, DecidableEq

def SupportedSubstitutionPacket.WellFormed
    (packet : SupportedSubstitutionPacket) : Prop :=
  (packet.support.map SupportEntry.name).Nodup ∧
    (packet.assignment.map AssignmentEntry.name).Nodup ∧
    ∀ name ∈ packet.assignment.map AssignmentEntry.name,
      name ∈ packet.support.map SupportEntry.name

instance (packet : SupportedSubstitutionPacket) :
    Decidable packet.WellFormed := by
  unfold SupportedSubstitutionPacket.WellFormed
  infer_instance

abbrev CanonicalPacket :=
  { packet : SupportedSubstitutionPacket // packet.WellFormed }

def supportContext (entries : List SupportEntry) (name : String) :
    List TypeExpr :=
  match entries.find? (fun entry => entry.name = name) with
  | some entry => entry.context
  | none => []

def assignmentValue (entries : List AssignmentEntry) (name : String) :
    Pattern :=
  match entries.find? (fun entry => entry.name = name) with
  | some entry => entry.value
  | none => .fvar name

def SupportedSubstitutionPacket.supportFunction
    (packet : SupportedSubstitutionPacket) : ContextSupport.Support :=
  supportContext packet.support

def SupportedSubstitutionPacket.assignmentFunction
    (packet : SupportedSubstitutionPacket) : ContextSupport.Assignment :=
  assignmentValue packet.assignment

mutual

/-- Execute one explicit support packet.  Unlike `ContextSupport.substituteAt`,
this operation also handles checked outward transport. -/
def substituteSupportedAt? (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (depth : Nat) :
    Pattern → Option Pattern
  | .bvar index => some (.bvar index)
  | .fvar name =>
      transportBVars? (support name).length depth (assignment name)
  | .apply constructor arguments => do
      let instantiated ←
        substituteSupportedListAt? support assignment depth arguments
      some (.apply constructor instantiated)
  | .lambda binder body => do
      let instantiated ←
        substituteSupportedAt? support assignment (depth + 1) body
      some (.lambda binder instantiated)
  | .multiLambda arity binders body => do
      let instantiated ←
        substituteSupportedAt? support assignment (depth + arity) body
      some (.multiLambda arity binders instantiated)
  | .subst body replacement => do
      let instantiatedBody ←
        substituteSupportedAt? support assignment (depth + 1) body
      let instantiatedReplacement ←
        substituteSupportedAt? support assignment depth replacement
      some (.subst instantiatedBody instantiatedReplacement)
  | .collection collectionType elements rest => do
      let instantiated ←
        substituteSupportedListAt? support assignment depth elements
      some (.collection collectionType instantiated rest)
termination_by pattern => sizeOf pattern

def substituteSupportedListAt? (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (depth : Nat) :
    List Pattern → Option (List Pattern)
  | [] => some []
  | pattern :: patterns => do
      let instantiated ←
        substituteSupportedAt? support assignment depth pattern
      let rest ←
        substituteSupportedListAt? support assignment depth patterns
      some (instantiated :: rest)
termination_by patterns => sizeOf patterns

end

def executePacket (packet : SupportedSubstitutionPacket) : Option Pattern :=
  substituteSupportedAt? packet.supportFunction packet.assignmentFunction
    packet.useDepth packet.body

/-! ## Canonical versioned wire codec -/

def encodeTypeExpr : TypeExpr → WireTerm
  | .base name => .list [.symbol "TBase", .symbol name]
  | .arrow domain codomain =>
      .list [.symbol "TArrow", encodeTypeExpr domain, encodeTypeExpr codomain]
  | .multiBinder body => .list [.symbol "TMultiBinder", encodeTypeExpr body]
  | .collection collectionType element =>
      .list [.symbol "TCollection", encodeCollType collectionType,
        encodeTypeExpr element]

def decodeTypeExpr : WireTerm → Option TypeExpr
  | .list [.symbol "TBase", .symbol name] => some (.base name)
  | .list [.symbol "TArrow", domain, codomain] => do
      let decodedDomain ← decodeTypeExpr domain
      let decodedCodomain ← decodeTypeExpr codomain
      some (.arrow decodedDomain decodedCodomain)
  | .list [.symbol "TMultiBinder", body] => do
      let decoded ← decodeTypeExpr body
      some (.multiBinder decoded)
  | .list [.symbol "TCollection", collectionType, element] => do
      let decodedCollection ← decodeCollType collectionType
      let decodedElement ← decodeTypeExpr element
      some (.collection decodedCollection decodedElement)
  | _ => none

def encodeTypeExprList : List TypeExpr → List WireTerm
  | [] => []
  | type :: types => encodeTypeExpr type :: encodeTypeExprList types

def decodeTypeExprList : List WireTerm → Option (List TypeExpr)
  | [] => some []
  | type :: types => do
      let decoded ← decodeTypeExpr type
      let rest ← decodeTypeExprList types
      some (decoded :: rest)

@[simp] theorem decodeTypeExpr_encodeTypeExpr (type : TypeExpr) :
    decodeTypeExpr (encodeTypeExpr type) = some type := by
  induction type with
  | base name => rfl
  | arrow domain codomain domainInduction codomainInduction =>
      simp [encodeTypeExpr, decodeTypeExpr, domainInduction, codomainInduction]
  | multiBinder body inductionHypothesis =>
      simp [encodeTypeExpr, decodeTypeExpr, inductionHypothesis]
  | collection collectionType element inductionHypothesis =>
      simp [encodeTypeExpr, decodeTypeExpr, inductionHypothesis]

@[simp] theorem decodeTypeExprList_encodeTypeExprList
    (types : List TypeExpr) :
    decodeTypeExprList (encodeTypeExprList types) = some types := by
  induction types with
  | nil => rfl
  | cons type rest inductionHypothesis =>
      simp [encodeTypeExprList, decodeTypeExprList, inductionHypothesis]

def encodeSupportEntry (entry : SupportEntry) : WireTerm :=
  .list [.symbol "WSupport", .symbol entry.name,
    .list (encodeTypeExprList entry.context)]

def decodeSupportEntry : WireTerm → Option SupportEntry
  | .list [.symbol "WSupport", .symbol name, .list context] => do
      let decoded ← decodeTypeExprList context
      some ⟨name, decoded⟩
  | _ => none

def encodeSupportEntries : List SupportEntry → List WireTerm
  | [] => []
  | entry :: entries => encodeSupportEntry entry :: encodeSupportEntries entries

def decodeSupportEntries : List WireTerm → Option (List SupportEntry)
  | [] => some []
  | entry :: entries => do
      let decoded ← decodeSupportEntry entry
      let rest ← decodeSupportEntries entries
      some (decoded :: rest)

@[simp] theorem decodeSupportEntry_encodeSupportEntry (entry : SupportEntry) :
    decodeSupportEntry (encodeSupportEntry entry) = some entry := by
  simp [encodeSupportEntry, decodeSupportEntry]

@[simp] theorem decodeSupportEntries_encodeSupportEntries
    (entries : List SupportEntry) :
    decodeSupportEntries (encodeSupportEntries entries) = some entries := by
  induction entries with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp [encodeSupportEntries, decodeSupportEntries, inductionHypothesis]

def encodeAssignmentEntry (entry : AssignmentEntry) : WireTerm :=
  .list [.symbol "WAssignment", .symbol entry.name, encodePattern entry.value]

def decodeAssignmentEntry : WireTerm → Option AssignmentEntry
  | .list [.symbol "WAssignment", .symbol name, value] => do
      let decoded ← decodePattern value
      some ⟨name, decoded⟩
  | _ => none

def encodeAssignmentEntries : List AssignmentEntry → List WireTerm
  | [] => []
  | entry :: entries =>
      encodeAssignmentEntry entry :: encodeAssignmentEntries entries

def decodeAssignmentEntries : List WireTerm → Option (List AssignmentEntry)
  | [] => some []
  | entry :: entries => do
      let decoded ← decodeAssignmentEntry entry
      let rest ← decodeAssignmentEntries entries
      some (decoded :: rest)

@[simp] theorem decodeAssignmentEntry_encodeAssignmentEntry
    (entry : AssignmentEntry) :
    decodeAssignmentEntry (encodeAssignmentEntry entry) = some entry := by
  simp [encodeAssignmentEntry, decodeAssignmentEntry]

@[simp] theorem decodeAssignmentEntries_encodeAssignmentEntries
    (entries : List AssignmentEntry) :
    decodeAssignmentEntries (encodeAssignmentEntries entries) = some entries := by
  induction entries with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp [encodeAssignmentEntries, decodeAssignmentEntries,
        inductionHypothesis]

def encodePacket (packet : CanonicalPacket) : WireTerm :=
  .list [.symbol "WSupportedSubstitution", .natural 1,
    .list (encodeSupportEntries packet.1.support),
    .list (encodeAssignmentEntries packet.1.assignment),
    .natural packet.1.useDepth, encodePattern packet.1.body]

def decodePacket : WireTerm → Option CanonicalPacket
  | .list [.symbol "WSupportedSubstitution", .natural 1,
      .list support, .list assignment, .natural useDepth, body] => do
      let decodedSupport ← decodeSupportEntries support
      let decodedAssignment ← decodeAssignmentEntries assignment
      let decodedBody ← decodePattern body
      let packet : SupportedSubstitutionPacket :=
        ⟨decodedSupport, decodedAssignment, useDepth, decodedBody⟩
      if valid : packet.WellFormed then some ⟨packet, valid⟩ else none
  | _ => none

@[simp] theorem decodePacket_encodePacket (packet : CanonicalPacket) :
    decodePacket (encodePacket packet) = some packet := by
  rcases packet with ⟨packet, valid⟩
  simp [encodePacket, decodePacket, valid]

def packetCodec : Checker.PartialCodec CanonicalPacket WireTerm where
  encode := encodePacket
  decode := decodePacket
  decode_encode := decodePacket_encodePacket

theorem encodePacket_injective : Function.Injective encodePacket :=
  packetCodec.encode_injective

/-- Execute only after canonical, versioned decoding. -/
def executeWire (wire : WireTerm) : Option Pattern := do
  let packet ← decodePacket wire
  executePacket packet.1

/-- Canonical wire execution refines the exact Lean support-indexed operation. -/
theorem executeWire_encodePacket (packet : CanonicalPacket) :
    executeWire (encodePacket packet) = executePacket packet.1 := by
  simp [executeWire, decodePacket_encodePacket]

/-! ## Semantic and typed refinement of the support provider -/

open MeTTaRevisionedQueryBindEval

private theorem supportsAvailableIn_iff (support : ContextSupport.Support)
    (depth : Nat) (patterns : List Pattern) :
    supportsAvailableIn support depth patterns = true ↔
      ∀ pattern ∈ patterns, supportsAvailableAt support depth pattern = true := by
  induction patterns with
  | nil => simp [supportsAvailableIn]
  | cons pattern rest ih => simp [supportsAvailableIn, ih]

private theorem substituteSupportedListAt?_of_pointwise
    (support : ContextSupport.Support) (assignment : ContextSupport.Assignment)
    (depth : Nat) (patterns : List Pattern)
    (pointwise : ∀ pattern ∈ patterns,
      substituteSupportedAt? support assignment depth pattern =
        some (ContextSupport.substituteAt support assignment depth pattern)) :
    substituteSupportedListAt? support assignment depth patterns =
      some (patterns.map (ContextSupport.substituteAt support assignment depth)) := by
  induction patterns with
  | nil => simp [substituteSupportedListAt?]
  | cons pattern patterns ih =>
      have head := pointwise pattern (by simp)
      have tail := ih (fun value member => pointwise value (by simp [member]))
      simp [substituteSupportedListAt?, head, tail]

/-- On admitted support depths, the executable partial operation implements
the independently defined semantic support action on every rich Pattern. -/
theorem substituteSupportedAt?_of_available
    (support : ContextSupport.Support) (assignment : ContextSupport.Assignment)
    (depth : Nat) (pattern : Pattern)
    (available : supportsAvailableAt support depth pattern = true) :
    substituteSupportedAt? support assignment depth pattern =
      some (ContextSupport.substituteAt support assignment depth pattern) := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => simp [substituteSupportedAt?, ContextSupport.substituteAt]
  | hfvar name =>
      have within : (support name).length ≤ depth := by
        simpa only [supportsAvailableAt, decide_eq_true_eq] using available
      simp [substituteSupportedAt?, ContextSupport.substituteAt,
        transportBVars?_of_le within]
  | happly label arguments ih =>
      have childAvailable : ∀ value ∈ arguments,
          supportsAvailableAt support depth value = true := by
        simpa only [supportsAvailableAt, supportsAvailableIn_iff] using available
      have children := substituteSupportedListAt?_of_pointwise support assignment depth arguments
        (fun value member => ih value member depth (childAvailable value member))
      simp [substituteSupportedAt?, ContextSupport.substituteAt, children]
  | hlambda binder body ih =>
      have childAvailable : supportsAvailableAt support (depth + 1) body = true := by
        simpa only [supportsAvailableAt] using available
      simp [substituteSupportedAt?, ContextSupport.substituteAt, ih (depth + 1) childAvailable]
  | hmultiLambda arity binders body ih =>
      have childAvailable : supportsAvailableAt support (depth + arity) body = true := by
        simpa only [supportsAvailableAt] using available
      simp [substituteSupportedAt?, ContextSupport.substituteAt, ih (depth + arity) childAvailable]
  | hsubst body replacement ihBody ihReplacement =>
      have children : supportsAvailableAt support (depth + 1) body = true ∧
          supportsAvailableAt support depth replacement = true := by
        simpa only [supportsAvailableAt, Bool.and_eq_true] using available
      simp [substituteSupportedAt?, ContextSupport.substituteAt,
        ihBody (depth + 1) children.1, ihReplacement depth children.2]
  | hcollection kind elements rest ih =>
      have childAvailable : ∀ value ∈ elements,
          supportsAvailableAt support depth value = true := by
        simpa only [supportsAvailableAt, supportsAvailableIn_iff] using available
      have children := substituteSupportedListAt?_of_pointwise support assignment depth elements
        (fun value member => ih value member depth (childAvailable value member))
      simp [substituteSupportedAt?, ContextSupport.substituteAt, children]

open WellSorted

mutual

/-- The independent typed support judgment supplies every local admission
needed by the executable support action. -/
theorem typed_supportsAvailable
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free bound pattern type)
    (supported : typed.RespectsSupport support) :
    supportsAvailableAt support bound.length pattern = true := by
  cases typed with
  | bvar lookup => simp [supportsAvailableAt]
  | @fvar bound name type lookup =>
      obtain ⟨inner, shape⟩ := supported name bound (FreeVariableOccursAt.here (lookup := lookup))
      simp [supportsAvailableAt, shape]
  | @constructor bound rule arguments membership notBare argumentsTyped =>
      have argumentsSupported : ∀ name occurrenceBound,
          ArgumentsFreeVariableOccursAt argumentsTyped name occurrenceBound →
            ∃ inner, occurrenceBound = inner ++ support name := by
        intro name occurrenceBound occurs
        exact supported name occurrenceBound
          (FreeVariableOccursAt.constructor
            (membership := membership) (notBare := notBare) occurs)
      simpa only [supportsAvailableAt] using
        arguments_supportsAvailable argumentsTyped argumentsSupported
  | @lambda bound binder body domain codomain bodyTyped =>
      have bodySupported : bodyTyped.RespectsSupport support := by
        intro name occurrenceBound occurs
        exact supported name occurrenceBound (FreeVariableOccursAt.lambda occurs)
      simpa only [supportsAvailableAt, List.length_cons, Nat.add_comm] using
        typed_supportsAvailable bodyTyped bodySupported
  | @multiLambda bound arity binders body domain codomain bodyTyped =>
      have bodySupported : bodyTyped.RespectsSupport support := by
        intro name occurrenceBound occurs
        exact supported name occurrenceBound (FreeVariableOccursAt.multiLambda occurs)
      simpa only [supportsAvailableAt, List.length_append, List.length_replicate,
        Nat.add_comm] using typed_supportsAvailable bodyTyped bodySupported
  | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
      have bodySupported : bodyTyped.RespectsSupport support := by
        intro name occurrenceBound occurs
        exact supported name occurrenceBound
          (FreeVariableOccursAt.substBody (replacementTyped := replacementTyped) occurs)
      have replacementSupported : replacementTyped.RespectsSupport support := by
        intro name occurrenceBound occurs
        exact supported name occurrenceBound
          (FreeVariableOccursAt.substReplacement (bodyTyped := bodyTyped) occurs)
      simpa only [supportsAvailableAt, Bool.and_eq_true, List.length_cons,
        Nat.add_comm] using And.intro (typed_supportsAvailable bodyTyped bodySupported)
          (typed_supportsAvailable replacementTyped replacementSupported)
  | @collection bound collectionType elements rest elementType elementsTyped =>
      have elementsSupported : ∀ name occurrenceBound,
          ElementsFreeVariableOccursAt elementsTyped name occurrenceBound →
            ∃ inner, occurrenceBound = inner ++ support name := by
        intro name occurrenceBound occurs
        exact supported name occurrenceBound (FreeVariableOccursAt.collection occurs)
      simpa only [supportsAvailableAt] using
        elements_supportsAvailable elementsTyped elementsSupported
  | @collectionConstructor bound rule parameterName collectionType elements rest
      elementType membership parameterShape elementsTyped =>
      have elementsSupported : ∀ name occurrenceBound,
          ElementsFreeVariableOccursAt elementsTyped name occurrenceBound →
            ∃ inner, occurrenceBound = inner ++ support name := by
        intro name occurrenceBound occurs
        exact supported name occurrenceBound
          (FreeVariableOccursAt.collectionConstructor
            (parameterName := parameterName) (membership := membership)
            (parameterShape := parameterShape) occurs)
      simpa only [supportsAvailableAt, supportsAvailableIn, Bool.and_true] using
        elements_supportsAvailable elementsTyped elementsSupported

theorem arguments_supportsAvailable
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {arguments : List Pattern} {parameters : List TermParam}
    (typed : ArgumentsHaveTypes language free bound arguments parameters)
    (supported : ∀ name occurrenceBound,
      ArgumentsFreeVariableOccursAt typed name occurrenceBound →
        ∃ inner, occurrenceBound = inner ++ support name) :
    supportsAvailableIn support bound.length arguments = true := by
  cases typed with
  | nil => simp [supportsAvailableIn]
  | cons representation parameterType argumentTyped argumentsTyped =>
      have headSupported : argumentTyped.RespectsSupport support := by
        intro name occurrenceBound occurs
        exact supported name occurrenceBound
          (ArgumentsFreeVariableOccursAt.head (representation := representation)
            (parameterType := parameterType) (argumentsTyped := argumentsTyped) occurs)
      have tailSupported : ∀ name occurrenceBound,
          ArgumentsFreeVariableOccursAt argumentsTyped name occurrenceBound →
            ∃ inner, occurrenceBound = inner ++ support name := by
        intro name occurrenceBound occurs
        exact supported name occurrenceBound
          (ArgumentsFreeVariableOccursAt.tail (representation := representation)
            (parameterType := parameterType) (argumentTyped := argumentTyped) occurs)
      simp only [supportsAvailableIn, Bool.and_eq_true]
      exact ⟨typed_supportsAvailable argumentTyped headSupported,
        arguments_supportsAvailable (bound := bound) argumentsTyped tailSupported⟩

theorem elements_supportsAvailable
    {language : LanguageDef} {free : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {elements : List Pattern} {elementType : TypeExpr}
    (typed : ElementsHaveType language free bound elements elementType)
    (supported : ∀ name occurrenceBound,
      ElementsFreeVariableOccursAt typed name occurrenceBound →
        ∃ inner, occurrenceBound = inner ++ support name) :
    supportsAvailableIn support bound.length elements = true := by
  cases typed with
  | nil => simp [supportsAvailableIn]
  | cons elementTyped elementsTyped =>
      have headSupported : elementTyped.RespectsSupport support := by
        intro name occurrenceBound occurs
        exact supported name occurrenceBound
          (ElementsFreeVariableOccursAt.head (elementsTyped := elementsTyped) occurs)
      have tailSupported : ∀ name occurrenceBound,
          ElementsFreeVariableOccursAt elementsTyped name occurrenceBound →
            ∃ inner, occurrenceBound = inner ++ support name := by
        intro name occurrenceBound occurs
        exact supported name occurrenceBound
          (ElementsFreeVariableOccursAt.tail (elementTyped := elementTyped) occurs)
      simp only [supportsAvailableIn, Bool.and_eq_true]
      exact ⟨typed_supportsAvailable elementTyped headSupported,
        elements_supportsAvailable (bound := bound) elementsTyped tailSupported⟩

end

/-- An independently typed supported assignment executes successfully through
the partial provider, and its actual result has the required authored type. -/
theorem substituteSupportedAt?_typed
    {language : LanguageDef} {source target : FreeTypeContext}
    {support : ContextSupport.Support} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (assignment : SupportedAssignment language source target support)
    (typed : HasType language source bound pattern type)
    (supported : typed.RespectsSupport support) :
    ∃ result, substituteSupportedAt? support assignment.assignment bound.length pattern =
        some result ∧ HasType language target bound result type := by
  refine ⟨ContextSupport.substituteAt support assignment.assignment bound.length pattern, ?_, ?_⟩
  · exact substituteSupportedAt?_of_available support assignment.assignment bound.length pattern
      (typed_supportsAvailable typed supported)
  · exact typed.substituteSupported assignment supported

/-- The finite support packet implements the same typed support action after
its use depth is matched with the authored ambient context. -/
theorem executePacket_typed
    (packet : SupportedSubstitutionPacket)
    {language : LanguageDef} {source target : FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (depth : packet.useDepth = bound.length)
    (assignmentTyped : ∀ {name type}, source name = some type →
      HasType language target (packet.supportFunction name)
        (packet.assignmentFunction name) type)
    (typed : HasType language source bound packet.body type)
    (supported : typed.RespectsSupport packet.supportFunction) :
    executePacket packet = some (ContextSupport.substituteAt packet.supportFunction
      packet.assignmentFunction bound.length packet.body) ∧
    HasType language target bound
      (ContextSupport.substituteAt packet.supportFunction
        packet.assignmentFunction bound.length packet.body) type := by
  constructor
  · unfold executePacket
    rw [depth]
    exact substituteSupportedAt?_of_available _ _ _ _
      (typed_supportsAvailable typed supported)
  · exact typed.substituteSupported
      ⟨packet.assignmentFunction, assignmentTyped⟩ supported

/-- Canonical versioned wire decoding preserves the executable typed support
action; no function-world equality or untyped name replacement is assumed. -/
theorem executeWire_typed
    (packet : CanonicalPacket)
    {language : LanguageDef} {source target : FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (depth : packet.val.useDepth = bound.length)
    (assignmentTyped : ∀ {name type}, source name = some type →
      HasType language target (packet.val.supportFunction name)
        (packet.val.assignmentFunction name) type)
    (typed : HasType language source bound packet.val.body type)
    (supported : typed.RespectsSupport packet.val.supportFunction) :
    executeWire (encodePacket packet) =
      some (ContextSupport.substituteAt packet.val.supportFunction
        packet.val.assignmentFunction bound.length packet.val.body) ∧
    HasType language target bound
      (ContextSupport.substituteAt packet.val.supportFunction
        packet.val.assignmentFunction bound.length packet.val.body) type := by
  rw [executeWire_encodePacket]
  exact executePacket_typed packet.val depth assignmentTyped typed supported

namespace RefinementControls

def typeA : TypeExpr := .base "A"

def supportX : ContextSupport.Support :=
  fun name => if name = "x" then [typeA] else []

def assignmentX : ContextSupport.Assignment :=
  fun name => if name = "x" then .bvar 0 else .fvar name

theorem typed_lambda_context (language : LanguageDef) :
    HasType language FreeTypeContext.empty [typeA]
      (.lambda none (.bvar 1)) (.arrow typeA typeA) := by
  exact HasType.lambda (HasType.bvar rfl)

theorem lambda_available :
    supportsAvailableAt supportX 0 (.lambda none (.fvar "x")) = true := by
  simp [supportsAvailableAt, supportX]

theorem bare_reference_unavailable :
    supportsAvailableAt supportX 0 (.fvar "x") = false := by
  simp [supportsAvailableAt, supportX]

theorem supported_lambda_executes :
    substituteSupportedAt? supportX assignmentX 1 (.lambda none (.fvar "x")) =
      some (.lambda none (.bvar 1)) := by
  simp [substituteSupportedAt?, supportX, assignmentX, transportBVars?,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

theorem unsupported_bare_capture_refused :
    substituteSupportedAt? supportX assignmentX 0 (.fvar "x") = none := by
  simp [substituteSupportedAt?, supportX, assignmentX, transportBVars?, lowerBVars?]

end RefinementControls


/-! ## Checked contextual matching and continuation operations -/

open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.MeTTa.MeTTaZero

/-- The finite source conditions for transporting one actual matcher filling.
The context assignment is checked against the capture sites, not merely
asserted by a wire support table. -/
def BindingAdmitted (support : ContextSupport.Support) (depth : Nat)
    (pattern body : Pattern) (bindings : Bindings) : Prop :=
  bindings.hasUniqueNames = true ∧ depthAligned pattern 0 pattern = true ∧
    (∀ entry ∈ bindings,
      captureDepth entry.1 depth pattern = some (support entry.1).length ∧
        entry.2.isWellScopedAt (support entry.1).length = true) ∧
    supportsAvailableAt support depth body = true

instance (support : ContextSupport.Support) (depth : Nat)
    (pattern body : Pattern) (bindings : Bindings) :
    Decidable (BindingAdmitted support depth pattern body bindings) := by
  unfold BindingAdmitted
  infer_instance

/-- Execute the actual support provider only after the independently stated
capture, scope, uniqueness and continuation-depth conditions pass. -/
def instantiateBinding? (support : ContextSupport.Support) (depth : Nat)
    (pattern body : Pattern) (bindings : Bindings) : Option Pattern :=
  if BindingAdmitted support depth pattern body bindings then
    substituteSupportedAt? support (bindingAssignment bindings) depth body
  else none

theorem instantiateBinding?_exact (support : ContextSupport.Support) (depth : Nat)
    (pattern body : Pattern) (bindings : Bindings) (instantiated : Pattern) :
    instantiateBinding? support depth pattern body bindings = some instantiated ↔
      BindingAdmitted support depth pattern body bindings ∧
        ContextSupport.substituteAt support (bindingAssignment bindings) depth body = instantiated := by
  by_cases admitted : BindingAdmitted support depth pattern body bindings
  · have physical := substituteSupportedAt?_of_available support
      (bindingAssignment bindings) depth body admitted.2.2.2
    simp [instantiateBinding?, admitted, physical]
  · simp [instantiateBinding?, admitted]

/-- The raw evidence contains its actual matcher occurrence.  The physical
substitution result controls acceptance. -/
def checkSupportedBinding (model : Model) (support : ContextSupport.Support)
    (depth : Nat) (pattern body value instantiated : Pattern)
    (bindings : Bindings) (occurrence : Nat) : Bool :=
  decide (occurrence < Multiset.count bindings (model.matchAtoms pattern value)) &&
    decide (instantiateBinding? support depth pattern body bindings = some instantiated)

theorem checkSupportedBinding_exact (model : Model)
    (support : ContextSupport.Support) (depth : Nat)
    (pattern body value instantiated : Pattern) (bindings : Bindings) (occurrence : Nat) :
    checkSupportedBinding model support depth pattern body value instantiated bindings occurrence = true ↔
      occurrence < Multiset.count bindings (model.matchAtoms pattern value) ∧
        BindingAdmitted support depth pattern body bindings ∧
        ContextSupport.substituteAt support (bindingAssignment bindings) depth body = instantiated := by
  simp only [checkSupportedBinding, Bool.and_eq_true, decide_eq_true_eq,
    instantiateBinding?_exact]

def supportedBindingOfChecked (model : Model)
    {support : ContextSupport.Support} {depth : Nat}
    {pattern body value instantiated : Pattern} {bindings : Bindings} {occurrence : Nat}
    (checked : checkSupportedBinding model support depth pattern body value instantiated
      bindings occurrence = true) :
    SupportedLetBinding model support depth pattern body value instantiated := by
  obtain ⟨matched, admitted, substituted⟩ :=
    (checkSupportedBinding_exact model support depth pattern body value instantiated bindings occurrence).mp checked
  exact {
    bindings := bindings
    occurrence := occurrence
    occurrence_exists := matched
    unique := admitted.1
    capturesAligned := admitted.2.1
    captured := admitted.2.2.1
    available := admitted.2.2.2
    instantiates := substituted }

theorem supportedBinding_iff_checked (model : Model)
    (support : ContextSupport.Support) (depth : Nat)
    (pattern body value instantiated : Pattern) :
    Nonempty (SupportedLetBinding model support depth pattern body value instantiated) ↔
      ∃ bindings occurrence, checkSupportedBinding model support depth pattern body value instantiated
        bindings occurrence = true := by
  constructor
  · rintro ⟨binding⟩
    refine ⟨binding.bindings, binding.occurrence,
      (checkSupportedBinding_exact model support depth pattern body value instantiated
        binding.bindings binding.occurrence).mpr ?_⟩
    exact ⟨binding.occurrence_exists,
      ⟨binding.unique, binding.capturesAligned, binding.captured, binding.available⟩,
      binding.instantiates⟩
  · rintro ⟨bindings, occurrence, checked⟩
    exact ⟨supportedBindingOfChecked model checked⟩

/-- Compute all supported continuation instances, retaining matcher
multiplicity and making no global result-order promise. -/
def supportedBindingResults (model : Model) (support : ContextSupport.Support)
    (depth : Nat) (pattern body value : Pattern) : Multiset Pattern :=
  (model.matchAtoms pattern value).bind fun bindings =>
    match instantiateBinding? support depth pattern body bindings with
    | none => 0
    | some instantiated => {instantiated}

theorem mem_supportedBindingResults (model : Model) (support : ContextSupport.Support)
    (depth : Nat) (pattern body value instantiated : Pattern) :
    instantiated ∈ supportedBindingResults model support depth pattern body value ↔
      Nonempty (SupportedLetBinding model support depth pattern body value instantiated) := by
  simp only [supportedBindingResults, Multiset.mem_bind]
  constructor
  · rintro ⟨bindings, matched, produced⟩
    cases physical : instantiateBinding? support depth pattern body bindings with
    | none => simp [physical] at produced
    | some result =>
        have equal : instantiated = result := by simpa [physical] using produced
        subst equal
        apply (supportedBinding_iff_checked model support depth pattern body value instantiated).mpr
        refine ⟨bindings, 0, ?_⟩
        simp only [checkSupportedBinding, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨Multiset.count_pos.mpr matched, physical⟩
  · rintro ⟨binding⟩
    have matched := Multiset.count_pos.mp (Nat.zero_lt_of_lt binding.occurrence_exists)
    refine ⟨binding.bindings, matched, ?_⟩
    have physical := (instantiateBinding?_exact support depth pattern body binding.bindings instantiated).mpr
      ⟨⟨binding.unique, binding.capturesAligned, binding.captured, binding.available⟩,
        binding.instantiates⟩
    simp [physical]

/-- Actual accepted binding evidence preserves an independently supplied
authored typing contract.  Capture-depth checks alone do not infer types. -/
theorem checkSupportedBinding_preservesTyping (model : Model)
    {support : ContextSupport.Support} {depth : Nat}
    {pattern body value instantiated : Pattern} {bindings : Bindings} {occurrence : Nat}
    {language : LanguageDef} {source target : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    (checked : checkSupportedBinding model support depth pattern body value instantiated
      bindings occurrence = true)
    (depthMatches : depth = bound.length)
    (typed : WellSorted.HasType language source bound body type)
    (supported : typed.RespectsSupport support)
    (assignmentTyped : ∀ {name type}, source name = some type →
      WellSorted.HasType language target (support name) (bindingAssignment bindings name) type) :
    WellSorted.HasType language target bound instantiated type := by
  have substituted :=
    (checkSupportedBinding_exact model support depth pattern body value instantiated bindings occurrence).mp checked
  rw [← substituted.2.2, depthMatches]
  exact typed.substituteSupported ⟨bindingAssignment bindings, assignmentTyped⟩ supported

namespace SupportedBindingControls

def supportX : ContextSupport.Support :=
  fun name => if name = "x" then [(.base "Value" : TypeExpr)] else []

def patternX : Pattern := .lambda none (.fvar "x")
def bodyX : Pattern := .lambda none (.lambda none (.fvar "x"))
def valueX : Pattern := .lambda none (.bvar 0)
def resultX : Pattern := .lambda none (.lambda none (.bvar 1))

theorem contextual_binding_accepted :
    checkSupportedBinding structuralModel supportX 0 patternX bodyX valueX resultX
      [("x", .bvar 0)] 0 = true := by decide +kernel

theorem contextual_source_receipt :
    Nonempty (SupportedLetBinding structuralModel supportX 0 patternX bodyX valueX resultX) :=
  ⟨supportedBindingOfChecked structuralModel contextual_binding_accepted⟩

theorem absent_matcher_occurrence_rejected :
    checkSupportedBinding structuralModel supportX 0 patternX bodyX valueX resultX
      [("x", .bvar 0)] 1 = false := by decide +kernel

theorem forged_support_rejected :
    checkSupportedBinding structuralModel (fun _ => []) 0 patternX bodyX valueX resultX
      [("x", .bvar 0)] 0 = false := by decide +kernel

theorem capture_rejected :
    checkSupportedBinding structuralModel supportX 0 patternX (.fvar "x") valueX (.bvar 0)
      [("x", .bvar 0)] 0 = false := by decide +kernel

theorem wrong_shift_rejected :
    checkSupportedBinding structuralModel supportX 0 patternX bodyX valueX
      (.lambda none (.lambda none (.bvar 0))) [("x", .bvar 0)] 0 = false := by decide +kernel

theorem source_pattern_depth_disagreement_rejected :
    instantiateBinding? supportX 0
      (.apply "Pair" [.fvar "x", .lambda none (.fvar "x")]) bodyX [("x", .bvar 0)] = none := by
  decide +kernel

theorem actual_contextual_results :
    supportedBindingResults structuralModel supportX 0 patternX bodyX valueX = {resultX} := by
  decide +kernel

end SupportedBindingControls

/-! ## Revision-bound candidate rows

The physical provider returns a stable world token, the quoted query pattern,
an occurrence identity, and a candidate value.  The occurrence identity is
not interpreted as a transient array index.  A revision catalog resolves it
to one logical multiset ordinal, and the authored matcher remains downstream.
-/

structure CandidateWireRowV1 where
  worldToken : Pattern
  queryPattern : Pattern
  occurrenceId : Pattern
  candidate : Pattern
deriving Repr, DecidableEq

def encodeCandidateRowV1 (row : CandidateWireRowV1) : WireTerm :=
  .list [.symbol "WZeroCandidate", .natural 1,
    encodePattern row.worldToken, encodePattern row.queryPattern,
    encodePattern row.occurrenceId, encodePattern row.candidate]

def decodeCandidateRowV1 : WireTerm → Option CandidateWireRowV1
  | .list [.symbol "WZeroCandidate", .natural 1,
      worldToken, queryPattern, occurrenceId, candidate] => do
      let decodedWorld ← decodePattern worldToken
      let decodedQuery ← decodePattern queryPattern
      let decodedOccurrence ← decodePattern occurrenceId
      let decodedCandidate ← decodePattern candidate
      some ⟨decodedWorld, decodedQuery, decodedOccurrence, decodedCandidate⟩
  | _ => none

@[simp] theorem decodeCandidateRowV1_encodeCandidateRowV1
    (row : CandidateWireRowV1) :
    decodeCandidateRowV1 (encodeCandidateRowV1 row) = some row := by
  simp [encodeCandidateRowV1, decodeCandidateRowV1]

def candidateRowCodecV1 :
    Checker.PartialCodec CandidateWireRowV1 WireTerm where
  encode := encodeCandidateRowV1
  decode := decodeCandidateRowV1
  decode_encode := decodeCandidateRowV1_encodeCandidateRowV1

theorem encodeCandidateRowV1_injective :
    Function.Injective encodeCandidateRowV1 :=
  candidateRowCodecV1.encode_injective

/-- A content-addressed physical world together with an independently checked
resolution of stable occurrence identities to logical multiset ordinals. -/
structure StableRevisionedWorld where
  token : Pattern
  logical :
    MeTTaRevisionedQueryBindEval.RevisionedSpaces String
  resolveOccurrence :
    String → Pattern → Option (Pattern × Nat)
  resolve_sound :
    ∀ space occurrenceId candidate ordinal,
      resolveOccurrence space occurrenceId = some (candidate, ordinal) →
      ordinal < Multiset.count candidate (logical.contents space)

structure CandidateWireRefinement
    (row : CandidateWireRowV1) (world : StableRevisionedWorld)
    (space : String) (queryPattern : Pattern) : Type where
  token_eq : row.worldToken = world.token
  query_eq : row.queryPattern = queryPattern
  ordinal : Nat
  resolved :
    world.resolveOccurrence space row.occurrenceId =
      some (row.candidate, ordinal)

/-- Executable, fail-closed validation of one physical candidate row. -/
def checkCandidateRowV1 (world : StableRevisionedWorld)
    (space : String) (queryPattern : Pattern)
    (row : CandidateWireRowV1) : Bool :=
  decide (row.worldToken = world.token) &&
    decide (row.queryPattern = queryPattern) &&
    match world.resolveOccurrence space row.occurrenceId with
    | some (candidate, _) => decide (candidate = row.candidate)
    | none => false

theorem checkCandidateRowV1_eq_true_iff
    (world : StableRevisionedWorld) (space : String)
    (queryPattern : Pattern) (row : CandidateWireRowV1) :
    checkCandidateRowV1 world space queryPattern row = true ↔
      Nonempty (CandidateWireRefinement
        row world space queryPattern) := by
  cases resolution :
      world.resolveOccurrence space row.occurrenceId with
  | none =>
      constructor
      · simp [checkCandidateRowV1, resolution]
      · rintro ⟨refinement⟩
        have impossible := refinement.resolved
        rw [resolution] at impossible
        cases impossible
  | some resolved =>
      rcases resolved with ⟨candidate, ordinal⟩
      constructor
      · intro checked
        have conjuncts :
            row.worldToken = world.token ∧
              row.queryPattern = queryPattern ∧
              candidate = row.candidate := by
          simpa [checkCandidateRowV1, resolution, and_assoc] using checked
        exact ⟨{
          token_eq := conjuncts.1
          query_eq := conjuncts.2.1
          ordinal := ordinal
          resolved := by simpa [conjuncts.2.2] using resolution
        }⟩
      · rintro ⟨refinement⟩
        have pairEquality :
            (candidate, ordinal) =
              (row.candidate, refinement.ordinal) :=
          Option.some.inj (resolution.symm.trans refinement.resolved)
        have candidateEquality : candidate = row.candidate :=
          congrArg Prod.fst pairEquality
        simp [checkCandidateRowV1, resolution, refinement.token_eq,
          refinement.query_eq, candidateEquality]

/-- Accepted wire evidence reconstructs one ordinary logical candidate
occurrence.  No provider result can acquire match authority at this step. -/
def CandidateWireRowV1.toCandidate
    {row : CandidateWireRowV1} {world : StableRevisionedWorld}
    {space : String} {queryPattern : Pattern}
    (refinement :
      CandidateWireRefinement row world space queryPattern) :
    MeTTaRevisionedQueryBindEval.CandidateOccurrence world.logical space := by
  exact {
    candidate := row.candidate
    atomOccurrence := refinement.ordinal
    atomOccurrence_exists :=
      world.resolve_sound space row.occurrenceId row.candidate
        refinement.ordinal refinement.resolved
  }

/-- Proof-relevant selection retains the exact row and its refinement proof
even when two rows have equal candidate values. -/
structure CandidateWireSelection
    (world : StableRevisionedWorld) (space : String)
    (queryPattern : Pattern) (rows : List CandidateWireRowV1)
    (candidate :
      MeTTaRevisionedQueryBindEval.CandidateOccurrence world.logical space) :
    Type where
  row : CandidateWireRowV1
  member : row ∈ rows
  refinement : CandidateWireRefinement row world space queryPattern
  identifies : row.toCandidate refinement = candidate

def candidateWireSelector
    (world : StableRevisionedWorld) (space : String)
    (queryPattern : Pattern) (rows : List CandidateWireRowV1) :
    MeTTaRevisionedQueryBindEval.CandidateSelector world.logical space :=
  CandidateWireSelection world space queryPattern rows

/-- Exact coverage is a separate provider obligation.  Soundness of every
selected row is already carried by CandidateWireSelection. -/
def CandidateRowsCover
    (world : StableRevisionedWorld) (space : String)
    (queryPattern : Pattern) (rows : List CandidateWireRowV1) : Type :=
  ∀ candidate :
      MeTTaRevisionedQueryBindEval.CandidateOccurrence world.logical space,
    CandidateWireSelection world space queryPattern rows candidate

def candidateWireSelector_complete
    (model : MeTTaZero.Model) (world : StableRevisionedWorld)
    (space : String) (queryPattern : Pattern)
    (rows : List CandidateWireRowV1)
    (coverage : CandidateRowsCover world space queryPattern rows) :
    MeTTaRevisionedQueryBindEval.CandidateComplete model
      (world := world.logical) (space := space) (pattern := queryPattern)
      (candidateWireSelector world space queryPattern rows) :=
  fun candidate _ _ _ => coverage candidate

/-- Once the revision-bound frontier covers every authored match occurrence,
wire-backed selection preserves exactly the existence of logical match
answers.  False positives remain harmless because MatchViaCandidate
reruns the authored matcher and checked substitution. -/
theorem match_nonempty_iff_wire_candidate_nonempty
    (model : MeTTaZero.Model) (world : StableRevisionedWorld)
    (space : String) (queryPattern template result : Pattern)
    (rows : List CandidateWireRowV1)
    (coverage : CandidateRowsCover world space queryPattern rows) :
    Nonempty
        (MeTTaRevisionedQueryBindEval.MatchArticle
          model space queryPattern template
          world.logical world.logical result) ↔
      Nonempty
        (MeTTaRevisionedQueryBindEval.MatchViaCandidate
          model space queryPattern template
          world.logical world.logical result
          (candidateWireSelector world space queryPattern rows)) := by
  exact MeTTaRevisionedQueryBindEval.match_nonempty_iff_candidate_nonempty
    model
    (candidateWireSelector_complete
      model world space queryPattern rows coverage)

/-! ### The same refinement stated over undecoded wire rows -/

/-- A selection from an actual wire frontier carries decoding, revision
validation, stable occurrence resolution, and identification with one logical
candidate.  Malformed wire terms have no constructor of this type. -/
structure EncodedCandidateWireSelection
    (world : StableRevisionedWorld) (space : String)
    (queryPattern : Pattern) (wireRows : List WireTerm)
    (candidate :
      MeTTaRevisionedQueryBindEval.CandidateOccurrence world.logical space) :
    Type where
  wire : WireTerm
  member : wire ∈ wireRows
  row : CandidateWireRowV1
  decoded : decodeCandidateRowV1 wire = some row
  refinement : CandidateWireRefinement row world space queryPattern
  identifies : row.toCandidate refinement = candidate

def encodedCandidateWireSelector
    (world : StableRevisionedWorld) (space : String)
    (queryPattern : Pattern) (wireRows : List WireTerm) :
    MeTTaRevisionedQueryBindEval.CandidateSelector world.logical space :=
  EncodedCandidateWireSelection world space queryPattern wireRows

/-- Completeness of a serialized physical frontier is explicit and separate
from the checker theorem for each row. -/
def EncodedCandidateRowsCover
    (world : StableRevisionedWorld) (space : String)
    (queryPattern : Pattern) (wireRows : List WireTerm) : Type :=
  ∀ candidate :
      MeTTaRevisionedQueryBindEval.CandidateOccurrence world.logical space,
    EncodedCandidateWireSelection
      world space queryPattern wireRows candidate

def encodedCandidateWireSelector_complete
    (model : MeTTaZero.Model) (world : StableRevisionedWorld)
    (space : String) (queryPattern : Pattern)
    (wireRows : List WireTerm)
    (coverage :
      EncodedCandidateRowsCover world space queryPattern wireRows) :
    MeTTaRevisionedQueryBindEval.CandidateComplete model
      (world := world.logical) (space := space) (pattern := queryPattern)
      (encodedCandidateWireSelector
        world space queryPattern wireRows) :=
  fun candidate _ _ _ => coverage candidate

/-- A complete frontier of canonical, revision-bound wire rows preserves
exactly the existence of authored match answers.  This is the Lean-to-wire
refinement theorem used by generated physical providers; the backend still
owes the separately named coverage obligation. -/
theorem match_nonempty_iff_encoded_wire_candidate_nonempty
    (model : MeTTaZero.Model) (world : StableRevisionedWorld)
    (space : String) (queryPattern template result : Pattern)
    (wireRows : List WireTerm)
    (coverage :
      EncodedCandidateRowsCover world space queryPattern wireRows) :
    Nonempty
        (MeTTaRevisionedQueryBindEval.MatchArticle
          model space queryPattern template
          world.logical world.logical result) ↔
      Nonempty
        (MeTTaRevisionedQueryBindEval.MatchViaCandidate
          model space queryPattern template
          world.logical world.logical result
          (encodedCandidateWireSelector
            world space queryPattern wireRows)) := by
  exact MeTTaRevisionedQueryBindEval.match_nonempty_iff_candidate_nonempty
    model
    (encodedCandidateWireSelector_complete
      model world space queryPattern wireRows coverage)

/-- The generated provider catalog is semantic authority data rather than a
runtime dispatch convention. -/
structure ProviderRequirementV1 where
  relation : String
  arity : Nat
  semanticId : String
deriving Repr, DecidableEq

def zeroInteractProviderCatalogV1 : List ProviderRequirementV1 :=
  [ ⟨"zero-space-open", 3, "zero.revisioned-space.open.v1"⟩
  , ⟨"zero-space-candidate", 4, "zero.revisioned-space.candidate.v1"⟩
  , ⟨"zero-space-emit", 6, "zero.revisioned-space.emit.v1"⟩
  , ⟨"qabt-field-depth", 4, "abt.default-signature.field-depth.v1"⟩
  , ⟨"qabt-transport", 4, "abt.default-signature.transport.v1"⟩ ]

theorem zeroInteractProviderCatalogV1_relations_nodup :
    (zeroInteractProviderCatalogV1.map ProviderRequirementV1.relation).Nodup := by
  decide

theorem zeroInteractProviderCatalogV1_semanticIds_nodup :
    (zeroInteractProviderCatalogV1.map
      ProviderRequirementV1.semanticId).Nodup := by
  decide

/-! ## Positive and negative executable canaries -/

namespace Canary

def valueType : TypeExpr := .base "Value"

def richBody : Pattern :=
  .collection .hashBag
    [ .apply "Pair" [.fvar "x", .lambda none (.fvar "x")]
    , .multiLambda 2 ["a", "b"] (.fvar "x")
    , .subst (.fvar "x") (.fvar "x") ]
    none

def richPacket : CanonicalPacket :=
  ⟨{ support := [⟨"x", [valueType]⟩]
     assignment := [⟨"x", .bvar 0⟩]
     useDepth := 1
     body := richBody }, by simp [SupportedSubstitutionPacket.WellFormed]⟩

/-- Every rich `Pattern` binder constructor uses its own depth law. -/
theorem richPacket_result :
    executeWire (encodePacket richPacket) =
      some (.collection .hashBag
        [ .apply "Pair" [.bvar 0, .lambda none (.bvar 1)]
        , .multiLambda 2 ["a", "b"] (.bvar 2)
        , .subst (.bvar 1) (.bvar 0) ]
        none) := by
  simp [executeWire_encodePacket, executePacket, richPacket, richBody,
    SupportedSubstitutionPacket.supportFunction,
    SupportedSubstitutionPacket.assignmentFunction, supportContext,
    assignmentValue, substituteSupportedAt?, substituteSupportedListAt?,
    transportBVars?, liftBVars]

/-- Weakening one value through an additional binder increments its free
outer index. -/
theorem weakening_canary :
    transportBVars? 1 2 (.bvar 0) = some (.bvar 1) := by
  simp [transportBVars?, liftBVars]

/-- Strengthening refuses to turn a referenced outer binder into a free or
captured index. -/
theorem lowering_rejects_removed_reference :
    transportBVars? 1 0 (.bvar 0) = none := by
  simp [transportBVars?, lowerBVars?]

/-- The same check is required beneath an inner binder: `#1` refers to the
removed outer level and must not be changed to the locally bound `#0`. -/
theorem lowering_rejects_capture_under_lambda :
    transportBVars? 1 0 (.lambda none (.bvar 1)) = none := by
  simp [transportBVars?, lowerBVars?]

/-- Duplicate support names are noncanonical and fail closed on the wire. -/
theorem duplicate_support_rejected :
    decodePacket
      (.list [.symbol "WSupportedSubstitution", .natural 1,
        .list
          [ encodeSupportEntry ⟨"x", []⟩
          , encodeSupportEntry ⟨"x", [valueType]⟩ ],
        .list [], .natural 0, encodePattern (.fvar "x")]) = none := by
  simp [decodePacket, decodeSupportEntries, decodeSupportEntry,
    encodeSupportEntry, encodeTypeExprList, encodeTypeExpr,
    decodeTypeExprList, decodeTypeExpr, decodeAssignmentEntries, valueType,
    SupportedSubstitutionPacket.WellFormed]

/-- Every assignment must cite an explicit support entry.  Treating an absent
entry as closed would silently erase the support-indexed contract. -/
theorem assignment_without_support_rejected :
    decodePacket
      (.list [.symbol "WSupportedSubstitution", .natural 1,
        .list [],
        .list [encodeAssignmentEntry ⟨"x", .bvar 0⟩],
        .natural 1, encodePattern (.fvar "x")]) = none := by
  simp [decodePacket, decodeSupportEntries, decodeAssignmentEntries,
    decodeAssignmentEntry, encodeAssignmentEntry,
    SupportedSubstitutionPacket.WellFormed]

/-- An unknown packet version is not interpreted as the current ABI. -/
theorem unknown_version_rejected :
    decodePacket
      (.list [.symbol "WSupportedSubstitution", .natural 2,
        .list [], .list [], .natural 0, encodePattern (.fvar "x")]) = none := by
  rfl

def candidateValue : Pattern := .apply "fact" [.fvar "a"]
def occurrenceZero : Pattern := .apply "gslt-source-occurrence" [.bvar 0]
def occurrenceOne : Pattern := .apply "gslt-source-occurrence" [.bvar 1]
def worldToken : Pattern := .apply "zero-world-token" [.fvar "digest"]
def queryPattern : Pattern := .apply "fact" [.fvar "x"]

def duplicateLogicalWorld :
    MeTTaRevisionedQueryBindEval.RevisionedSpaces String where
  revision := 0
  contents := fun space =>
    if space = "&self" then
      ({candidateValue, candidateValue} : Multiset Pattern)
    else 0

def duplicateResolve (space : String) (occurrenceId : Pattern) :
    Option (Pattern × Nat) :=
  if space = "&self" ∧ occurrenceId = occurrenceZero then
    some (candidateValue, 0)
  else if space = "&self" ∧ occurrenceId = occurrenceOne then
    some (candidateValue, 1)
  else none

def duplicateStableWorld : StableRevisionedWorld where
  token := worldToken
  logical := duplicateLogicalWorld
  resolveOccurrence := duplicateResolve
  resolve_sound := by
    intro space occurrenceId candidate ordinal resolved
    unfold duplicateResolve at resolved
    split at resolved
    · next selected =>
        obtain ⟨spaceEq, occurrenceEq⟩ := selected
        have pairEq :
            (candidateValue, 0) = (candidate, ordinal) :=
          Option.some.inj resolved
        have candidateEq : candidateValue = candidate := by
          simpa using congrArg Prod.fst pairEq
        have ordinalEq : 0 = ordinal := by
          simpa using congrArg Prod.snd pairEq
        subst space candidate ordinal
        simp [duplicateLogicalWorld]
    · split at resolved
      · next selected =>
          obtain ⟨spaceEq, occurrenceEq⟩ := selected
          have pairEq :
              (candidateValue, 1) = (candidate, ordinal) :=
            Option.some.inj resolved
          have candidateEq : candidateValue = candidate := by
            simpa using congrArg Prod.fst pairEq
          have ordinalEq : 1 = ordinal := by
            simpa using congrArg Prod.snd pairEq
          subst space candidate ordinal
          simp [duplicateLogicalWorld]
      · cases resolved

def candidateRowZero : CandidateWireRowV1 where
  worldToken := worldToken
  queryPattern := queryPattern
  occurrenceId := occurrenceZero
  candidate := candidateValue

def candidateRowOne : CandidateWireRowV1 where
  worldToken := worldToken
  queryPattern := queryPattern
  occurrenceId := occurrenceOne
  candidate := candidateValue

def candidateRefinementZero :
    CandidateWireRefinement candidateRowZero duplicateStableWorld
      "&self" queryPattern where
  token_eq := rfl
  query_eq := rfl
  ordinal := 0
  resolved := by
    simp [duplicateStableWorld, duplicateResolve, candidateRowZero,
      occurrenceZero]

def candidateRefinementOne :
    CandidateWireRefinement candidateRowOne duplicateStableWorld
      "&self" queryPattern where
  token_eq := rfl
  query_eq := rfl
  ordinal := 1
  resolved := by
    simp [duplicateStableWorld, duplicateResolve, candidateRowOne,
      occurrenceOne, occurrenceZero]

/-- Equal candidate values retain distinct authenticated occurrence
coordinates after wire validation. -/
theorem duplicate_candidate_occurrences_remain_distinct :
    (candidateRowZero.toCandidate candidateRefinementZero).atomOccurrence ≠
      (candidateRowOne.toCandidate candidateRefinementOne).atomOccurrence := by
  decide

theorem valid_candidate_row_is_accepted :
    checkCandidateRowV1 duplicateStableWorld "&self" queryPattern
      candidateRowZero = true := by
  exact (checkCandidateRowV1_eq_true_iff
    duplicateStableWorld "&self" queryPattern candidateRowZero).2
      ⟨candidateRefinementZero⟩

/-- A row from another content-addressed world cannot be replayed against the
current revision. -/
theorem stale_world_candidate_is_rejected :
    checkCandidateRowV1 duplicateStableWorld "&self" queryPattern
      { candidateRowZero with worldToken := .fvar "stale" } = false := by
  simp [checkCandidateRowV1, duplicateStableWorld, candidateRowZero,
    worldToken]

end Canary

end Mettapedia.Languages.MeTTa.MeTTaSupportIndexedABTWire


/-! ## Incoming ambient assignments and fresh matcher roles -/

namespace Mettapedia.Languages.MeTTa.MeTTaSupportIndexedABTWire.AmbientBinding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution
open Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval

/-- Only names already present in the incoming assignment become ambient
slots. Other free names retain their matcher role. The original assignment's
first matching entry controls lookup even if an external table repeats a key. -/
def abstraction (incoming : Bindings) (name : String) : Pattern :=
  match incoming.findIdx? (fun entry => entry.1 == name) with
  | none => .fvar name
  | some index => .bvar index

/-- Read an incoming value by its physical table index. Out-of-table indices
remain ambient references; the abstraction never emits such indices. -/
def values (incoming : Bindings) :
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment :=
  fun index => ((incoming[index]?).map Prod.snd).getD (.bvar index)

theorem reopen_abstraction (incoming : Bindings) (name : String) :
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute (values incoming)
      (abstraction incoming name) = bindingAssignment incoming name := by
  have lookup := @List.find?_eq_bind_findIdx?_getElem? _ incoming
    (fun entry => entry.1 == name)
  cases indexFound : incoming.findIdx? (fun entry => entry.1 == name) with
  | none =>
    have absent : incoming.lookup name = none := by
      simp only [Bindings.lookup, lookup, indexFound, Option.bind_none, Option.map_none]
    simp [abstraction, indexFound, bindingAssignment, absent,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute]
  | some index =>
    have inTable : index < incoming.length :=
      (List.findIdx?_eq_some_iff_getElem.mp indexFound).choose
    have found : incoming.lookup name = (incoming[index]?).map Prod.snd := by
      simp only [Bindings.lookup, lookup, indexFound, Option.bind_some]
    simp [abstraction, indexFound, bindingAssignment, found, values,
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
      List.getElem?_eq_getElem inTable]

/-- Prepare the same raw Pattern using existing support-aware binding syntax;
no second program AST or matcher is introduced. -/
def prepare (incoming : Bindings) (depth : Nat) (pattern : Pattern) : Pattern :=
  ContextSupport.substituteAt (fun _ => []) (abstraction incoming) depth pattern

/-- Reopen ambient slots without altering freshly introduced matcher names. -/
def reopen (incoming : Bindings) (depth : Nat) (pattern : Pattern) : Pattern :=
  Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
    (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift depth (values incoming)) pattern

/-- The actual two-pass preparation agrees with the original named support
action. In particular a pre-bound name is not silently treated as fresh. -/
theorem reopen_prepare (incoming : Bindings) (depth : Nat) (pattern : Pattern)
    (wellScoped : pattern.isWellScopedAt depth = true) :
    reopen incoming depth (prepare incoming depth pattern) =
      ContextSupport.substituteAt (fun _ => []) (bindingAssignment incoming) depth pattern := by
  unfold reopen prepare
  rw [ContextSupport.ambient_substitute_named _ _ _ _ wellScoped]
  congr 1
  funext name
  exact reopen_abstraction incoming name

@[simp] theorem fresh_name_remains_matcher (incoming : Bindings) (name : String)
    (absent : incoming.lookup name = none) :
    reopen incoming 0 (prepare incoming 0 (.fvar name)) = .fvar name := by
  rw [reopen_prepare incoming 0 (.fvar name) rfl]
  simp [ContextSupport.substituteAt, bindingAssignment, absent, liftBVars_zero]

@[simp] theorem prebound_name_reopens (incoming : Bindings) (name : String) (value : Pattern)
    (found : incoming.lookup name = some value) :
    reopen incoming 0 (prepare incoming 0 (.fvar name)) = value := by
  rw [reopen_prepare incoming 0 (.fvar name) rfl]
  simp [ContextSupport.substituteAt, bindingAssignment, found, liftBVars_zero]


/-- On the existing constructor/variable fragment the named support action
is the actual original binding applier, including leaving unbound variables
unresolved. Object-binder transport and executable explicit substitution
require their separate support/normalization contracts. -/
theorem named_support_eq_applyBindings (incoming : Bindings) (pattern : Pattern)
    (plain : isMatchCorrectAux pattern = true) :
    ContextSupport.substituteAt (fun _ => []) (bindingAssignment incoming) 0 pattern =
      applyBindings incoming pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp only [ContextSupport.substituteAt, applyBindings]
  | hfvar name =>
    simp only [ContextSupport.substituteAt, List.length_nil, Nat.sub_self,
      liftBVars_zero, bindingAssignment, Bindings.lookup, applyBindings]
    cases incoming.find? (fun entry => entry.1 == name) <;> rfl
  | happly constructor arguments ih =>
    simp only [ContextSupport.substituteAt, applyBindings]
    congr 1
    apply List.map_congr_left
    intro argument member
    exact ih argument member ((Mettapedia.OSLF.MeTTaIL.MatchSpec.isMatchCorrectListAux_iff_forall _).mp plain _ member)
  | hlambda name body _ => simp [isMatchCorrectAux] at plain
  | hmultiLambda arity names body _ => simp [isMatchCorrectAux] at plain
  | hsubst body replacement _ _ => simp [isMatchCorrectAux] at plain
  | hcollection kind elements rest _ => simp [isMatchCorrectAux] at plain

/-- Ambient-slot abstraction and reopening agree with original binding before
native dispatch, while retaining every source occurrence of an unbound name. -/
theorem reopen_prepare_applyBindings (incoming : Bindings) (pattern : Pattern)
    (wellScoped : pattern.isWellScopedAt 0 = true)
    (plain : isMatchCorrectAux pattern = true) :
    reopen incoming 0 (prepare incoming 0 pattern) = applyBindings incoming pattern := by
  rw [reopen_prepare incoming 0 pattern wellScoped,
    named_support_eq_applyBindings incoming pattern plain]


end Mettapedia.Languages.MeTTa.MeTTaSupportIndexedABTWire.AmbientBinding
