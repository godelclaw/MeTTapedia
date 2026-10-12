import Mettapedia.GSLT.LanguageDef.ArithmeticExtension
import Mettapedia.GSLT.LanguageDef.ExtensionComposition
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Value
import Mettapedia.GSLT.Parsing.SourceIntegerProvider
import Mettapedia.Languages.C11.IntegerBits
import Mettapedia.Languages.C11.IntegerStep

/-!
# Integer representation declarations and constructed realizations

An integer representation is attached beside an operation theory and its
surface section. It does not select overflow, quotient, conversion or effect
policies. Authored declarations check precisions and declaration identities;
the existing coGSLT document language retains declaration order and nested
bundles. This is structured authoring, not a textual `.module` parser.

Two realizations share mathematical integers while keeping their representation
observations distinct. The module value carrier stores exact `Int` values. C
profiles store finite words whose independent reading judgments retain traps
and negative zero. Canonical stores choose positive zero. Decimal source atoms
use the existing selected source integer provider, with its exact spelling law.
No compiler, ABI or native arithmetic correspondence is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IntegerRepresentationExtension

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.Languages.C11


/-- Representation choices do not own an arithmetic operation family. -/
inductive Profile where
  | exact
  | bounded (format : IntegerFormat) (negativeZero : IntegerBits.NegativeZero)
  deriving DecidableEq, Repr

/-- Raw profiles retain unchecked precision before elaboration. -/
inductive ProfileData where
  | exact
  | bounded (format : IntegerStep.FormatData) (negativeZero : IntegerBits.NegativeZero)
  deriving DecidableEq, Repr

def encodeProfile : Profile → ProfileData
  | .exact => .exact
  | .bounded format mode => .bounded (IntegerStep.encodeFormat format) mode

def decodeProfile? : ProfileData → Option Profile
  | .exact => some .exact
  | .bounded data mode => (IntegerStep.decodeFormat data).map fun format => .bounded format mode

@[simp] theorem decodeProfile?_encode (profile : Profile) :
    decodeProfile? (encodeProfile profile) = some profile := by
  cases profile <;>
    simp only [encodeProfile, decodeProfile?, IntegerStep.decodeFormat_encode, Option.map_some]

theorem encodeProfile_decode (data : ProfileData) (profile : Profile)
    (decoded : decodeProfile? data = some profile) : encodeProfile profile = data := by
  cases data with
  | exact => cases decoded; rfl
  | bounded wire mode =>
      cases formatEqual : IntegerStep.decodeFormat wire with
      | none => simp [decodeProfile?, formatEqual] at decoded
      | some format =>
          simp only [decodeProfile?, formatEqual, Option.map_some] at decoded
          cases decoded
          exact congrArg (fun data => ProfileData.bounded data mode)
            (IntegerStep.encodeFormat_decode wire format formatEqual)

theorem encodeProfile_injective : Function.Injective encodeProfile := by
  intro first second same
  have decoded := congrArg decodeProfile? same
  simpa only [decodeProfile?_encode, Option.some.injEq] using decoded

structure Declaration where
  name : String
  profile : Profile
  deriving DecidableEq, Repr

inductive DeclarationSyntax where
  | representation (name : String) (profile : ProfileData)
  deriving DecidableEq, Repr

def encodeDeclaration (declaration : Declaration) : DeclarationSyntax :=
  .representation declaration.name (encodeProfile declaration.profile)

def decodeDeclaration? : DeclarationSyntax → Option Declaration
  | .representation name wire =>
      (decodeProfile? wire).map fun profile => ⟨name, profile⟩

@[simp] theorem decodeDeclaration?_encode (declaration : Declaration) :
    decodeDeclaration? (encodeDeclaration declaration) = some declaration := by
  cases declaration
  simp [encodeDeclaration, decodeDeclaration?]

def Admissible (declarations : List Declaration) : Bool :=
  decide (declarations.map Declaration.name).Nodup &&
    declarations.all fun declaration => !declaration.name.isEmpty

abbrev Registry := { declarations : List Declaration // Admissible declarations = true }

def decodeDocument? (source : DeclarationDocument DeclarationSyntax) :
    Option (List Declaration) := source.values.mapM decodeDeclaration?

def elaborate? (source : DeclarationDocument DeclarationSyntax) : Option Registry := do
  let declarations ← decodeDocument? source
  if accepted : Admissible declarations = true then some ⟨declarations, accepted⟩ else none

def quoteRegistry (registry : Registry) : DeclarationDocument DeclarationSyntax :=
  .bundle ((registry.1.map encodeDeclaration).map DeclarationDocument.declaration)

private theorem decode_map_encode (declarations : List Declaration) :
    List.mapM decodeDeclaration? (declarations.map encodeDeclaration) = some declarations := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations inductionHypothesis => simp [inductionHypothesis]

@[simp] theorem decodeDocument?_quote (registry : Registry) :
    decodeDocument? (quoteRegistry registry) = some registry.1 := by
  unfold decodeDocument? quoteRegistry
  rw [DeclarationDocument.values_bundle_map]
  exact decode_map_encode registry.1

@[simp] theorem elaborate?_quote (registry : Registry) :
    elaborate? (quoteRegistry registry) = some registry := by
  rcases registry with ⟨declarations, accepted⟩
  simp [elaborate?, decodeDocument?_quote, accepted]

/-- The existing declaration-document GSLT authors checked representations.
The arithmetic theory remains the unchanged base of this extension. -/
def representationLayer : CoGSLTLayer ArithmeticExtension.ExactInteger.AdmittedTheory where
  Fiber := fun _ => Registry
  sourceGSLT := fun _ => ExactDeclarationCodec.documentGSLT DeclarationSyntax
  elaborate := fun _ => elaborate?
  quote := fun _ => quoteRegistry
  elaborate_quote := fun _ => elaborate?_quote
  elaborate_equation := by
    intro _ source target equivalent
    change source.values = target.values at equivalent
    unfold elaborate? decodeDocument?
    rw [equivalent]
  elaborate_rewrite := by
    intro _ _ _ impossible
    exact False.elim impossible

/-- Independent surface and representation declarations share an admitted
operation theory through the existing fibrewise product. -/
def numericLayer : ExtensionLayer ArithmeticExtension.ExactInteger.AdmittedTheory :=
  representationLayer.toExtensionLayer.product ArithmeticExtension.ExactInteger.surfaceLayer.toExtensionLayer

def attachNumeric (theory : ArithmeticExtension.ExactInteger.AdmittedTheory) (representations : Registry)
    (surface : ArithmeticExtension.ExactInteger.AdmittedSection theory) : numericLayer.Total :=
  numericLayer.attach theory (representations, surface)

theorem attachNumeric_retains_theory (theory : ArithmeticExtension.ExactInteger.AdmittedTheory)
    (representations : Registry) (surface : ArithmeticExtension.ExactInteger.AdmittedSection theory) :
    numericLayer.erase (attachNumeric theory representations surface) = theory :=
  ExtensionLayer.erase_attach numericLayer theory (representations, surface)

def lookupList? : List Declaration → String → Option Profile
  | [], _ => none
  | declaration :: rest, name =>
      if declaration.name = name then some declaration.profile else lookupList? rest name

theorem lookupList?_sound (declarations : List Declaration) (name : String) (profile : Profile)
    (found : lookupList? declarations name = some profile) :
    Declaration.mk name profile ∈ declarations := by
  induction declarations with
  | nil => cases found
  | cons declaration rest inductionHypothesis =>
      rcases declaration with ⟨actualName, actualProfile⟩
      by_cases same : actualName = name
      · subst actualName
        simp only [lookupList?, ↓reduceIte, Option.some.injEq] at found
        subst actualProfile
        exact List.mem_cons_self
      · simp only [lookupList?, if_neg same] at found
        exact List.mem_cons_of_mem _ (inductionHypothesis found)

theorem lookupList?_complete (declarations : List Declaration)
    (unique : (declarations.map Declaration.name).Nodup)
    (name : String) (profile : Profile) (member : Declaration.mk name profile ∈ declarations) :
    lookupList? declarations name = some profile := by
  induction declarations with
  | nil => cases member
  | cons declaration rest inductionHypothesis =>
      have names := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with sameDeclaration | inRest
      · cases sameDeclaration
        simp [lookupList?]
      · by_cases sameName : declaration.name = name
        · have nameMember : name ∈ rest.map Declaration.name := List.mem_map_of_mem inRest
          exact False.elim (names.1 (sameName.symm ▸ nameMember))
        · simp only [lookupList?, if_neg sameName]
          exact inductionHypothesis names.2 inRest

def lookup? (registry : Registry) (name : String) : Option Profile := lookupList? registry.1 name

theorem lookup?_iff (registry : Registry) (name : String) (profile : Profile) :
    lookup? registry name = some profile ↔ Declaration.mk name profile ∈ registry.1 := by
  have unique : (registry.1.map Declaration.name).Nodup := by
    have accepted := registry.2
    simp only [Admissible, Bool.and_eq_true, decide_eq_true_eq] at accepted
    exact accepted.1
  constructor
  · exact lookupList?_sound registry.1 name profile
  · exact lookupList?_complete registry.1 unique name profile

/-- Payloads are already admitted mathematical values, not unchecked casts. -/
abbrev Payload : Profile → Type
  | .exact => Int
  | .bounded format _ => IntegerValue format

def integer : (profile : Profile) → Payload profile → Int
  | .exact, value => value
  | .bounded _ _, value => value.value

/-- Exact values and C words use the same structured module carrier. The
profile determines whether its integer field is a value or an unsigned word. -/
def encodeValue : (profile : Profile) → Payload profile → ModuleFormat.Value
  | .exact, value => .integer value
  | .bounded format _, value => .integer (IntegerBits.canonicalWord format value.value)

def readValue? : Profile → ModuleFormat.Value → Option IntegerBits.Outcome
  | .exact, .integer value => some (.value value false)
  | .bounded format mode, .integer word =>
      if 0 ≤ word then IntegerBits.read format mode word.toNat else none
  | _, _ => none

/-- The relation specifies meanings through independent finite-word reading
rules. An invalid carrier or word is distinct from a permitted trap. -/
inductive ValueReading : Profile → ModuleFormat.Value → IntegerBits.Outcome → Prop where
  | exact (value : Int) : ValueReading .exact (.integer value) (.value value false)
  | bounded (format : IntegerFormat) (mode : IntegerBits.NegativeZero) (word : Nat)
      (outcome : IntegerBits.Outcome) (reading : IntegerBits.Reading format mode word outcome) :
      ValueReading (.bounded format mode) (.integer word) outcome

theorem readValue?_sound (profile : Profile) (wire : ModuleFormat.Value)
    (outcome : IntegerBits.Outcome) (computed : readValue? profile wire = some outcome) :
    ValueReading profile wire outcome := by
  cases profile with
  | exact =>
      cases wire <;> simp [readValue?] at computed
      subst outcome
      exact .exact _
  | bounded format mode =>
      cases wire <;> simp only [readValue?] at computed
      all_goals try contradiction
      rename_i word
      by_cases nonnegative : 0 ≤ word
      · have reading := IntegerBits.read_sound format mode word.toNat outcome
          (by simpa [nonnegative] using computed)
        simpa only [Int.toNat_of_nonneg nonnegative] using
          ValueReading.bounded format mode word.toNat outcome reading
      · simp [nonnegative] at computed

theorem readValue?_complete (profile : Profile) (wire : ModuleFormat.Value)
    (outcome : IntegerBits.Outcome) (reading : ValueReading profile wire outcome) :
    readValue? profile wire = some outcome := by
  cases reading with
  | exact value => rfl
  | bounded format mode word outcome reading =>
      simp only [readValue?, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
      exact IntegerBits.read_complete format mode word outcome reading

theorem readValue?_iff (profile : Profile) (wire : ModuleFormat.Value)
    (outcome : IntegerBits.Outcome) :
    readValue? profile wire = some outcome ↔ ValueReading profile wire outcome :=
  ⟨readValue?_sound profile wire outcome, readValue?_complete profile wire outcome⟩

theorem readValue?_encode (profile : Profile) (value : Payload profile) :
    readValue? profile (encodeValue profile value) = some (.value (integer profile value) false) := by
  cases profile with
  | exact => rfl
  | bounded format mode =>
      simp only [readValue?, encodeValue, Int.natCast_nonneg, ↓reduceIte,
        Int.toNat_natCast, integer]
      exact IntegerBits.read_canonicalWord format mode value.value value.valid

/-- Authored identities select the admitted reader. There is no implicit
change of representation when a name is absent or a document is rejected. -/
def readAuthored? (source : DeclarationDocument DeclarationSyntax) (name : String)
    (wire : ModuleFormat.Value) : Option IntegerBits.Outcome := do
  let registry ← elaborate? source
  let profile ← lookup? registry name
  readValue? profile wire

theorem readAuthored?_sound (source : DeclarationDocument DeclarationSyntax)
    (name : String) (wire : ModuleFormat.Value) (outcome : IntegerBits.Outcome)
    (read : readAuthored? source name wire = some outcome) :
    ∃ registry : Registry, elaborate? source = some registry ∧
      ∃ profile, Declaration.mk name profile ∈ registry.1 ∧ ValueReading profile wire outcome := by
  cases admitted : elaborate? source with
  | none => simp [readAuthored?, admitted] at read
  | some registry =>
      cases selected : lookup? registry name with
      | none => simp [readAuthored?, admitted, selected] at read
      | some profile =>
          exact ⟨registry, rfl, profile, (lookup?_iff registry name profile).1 selected,
            readValue?_sound profile wire outcome (by simpa [readAuthored?, admitted, selected] using read)⟩

theorem readAuthored?_quote (registry : Registry) (name : String) (profile : Profile)
    (member : Declaration.mk name profile ∈ registry.1) (value : Payload profile) :
    readAuthored? (quoteRegistry registry) name (encodeValue profile value) =
      some (.value (integer profile value) false) := by
  simp only [readAuthored?, elaborate?_quote, bind, Option.bind_some,
    (lookup?_iff registry name profile).2 member, readValue?_encode]

/-- Constructed value realization. The bounded compiler changes a signed
mathematical value into its finite bit representation; the reader does not
call that compiler or the source observation. -/
def valueRealization : Mettapedia.GSLT.Realization Payload
    (fun _ => ModuleFormat.Value) (fun _ => Option IntegerBits.Outcome) where
  compile := encodeValue
  observeSource := fun profile value => some (.value (integer profile value) false)
  observeArtifact := readValue?
  adequate := readValue?_encode

theorem encodeValue_injective (profile : Profile) : Function.Injective (encodeValue profile) := by
  intro first second same
  have observed := congrArg (readValue? profile) same
  rw [readValue?_encode, readValue?_encode] at observed
  have integers : integer profile first = integer profile second := by
    exact (IntegerBits.Outcome.value.inj (Option.some.inj observed)).1
  cases profile with
  | exact => exact integers
  | bounded format mode =>
      cases first
      cases second
      simp only [integer] at integers
      cases integers
      rfl

/-- Canonical decimal atoms are another constructed realization of the exact
value fibre. Its reader is the actual selected source-provider algorithm. -/
def decimalRealization : Mettapedia.GSLT.SimpleRealization Int String (Option Int) where
  compile := fun _ value => toString value
  observeSource := fun _ value => some value
  observeArtifact := fun _ token => Mettapedia.GSLT.Parsing.SourceIntegerProvider.integerValue? token
  adequate := fun _ value => Mettapedia.GSLT.Parsing.SourceIntegerProvider.integerValue?_repr value

theorem decimal_value_reading (token : String) (value : Int)
    (parsed : Mettapedia.GSLT.Parsing.SourceIntegerProvider.integerValue? token = some value) :
    token = toString value ∧ ValueReading .exact (.integer value) (.value value false) := by
  have spelling := (Mettapedia.GSLT.Parsing.SourceIntegerProvider.integerValue?_iff token value).1 parsed
  exact ⟨spelling, .exact value⟩

/-- Finite-word aliases may share a mathematical value while retaining
different negative-zero observations. That is not erased by `readValue?`. -/
theorem negativeZero_distinguished (format : IntegerFormat) (mode : IntegerBits.NegativeZero)
    (positiveWord negativeWord : Nat)
    (positiveRead : IntegerBits.Reading format mode positiveWord (.value 0 false))
    (negativeRead : IntegerBits.Reading format mode negativeWord (.value 0 true)) :
    readValue? (.bounded format mode) (.integer positiveWord) ≠
      readValue? (.bounded format mode) (.integer negativeWord) := by
  rw [readValue?_complete _ _ _ (.bounded format mode positiveWord _ positiveRead),
    readValue?_complete _ _ _ (.bounded format mode negativeWord _ negativeRead)]
  decide

end Mettapedia.GSLT.LanguageDef.IntegerRepresentationExtension
