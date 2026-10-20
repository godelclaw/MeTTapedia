import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestTypes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeAbstraction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationAdmissionReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaboration

/-!
# Generated indexed declarations checked in source-prefix order

The family, all constructor occurrences and the dependent eliminator form one
ordered inventory. Explicit parameters are closed using the existing telescope
abstraction. Declaration names also generate the prefixes used inside method
types, so those prefixes cannot be supplied independently of the inventory.

The existing declaration checker admits each type against its preceding
inventory. The evidence producer below has no authority: its output is replayed
by that checker. Generated declarations are opaque and install no iota equations.
Formation, positivity, dependent meaning and computation preservation remain
distinct obligations. In particular an empty constructor inventory still has a
family and an eliminator to check.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Declarations

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Declaration TelescopeAbstraction

universe u
variable {I : Interface.{u}} {Head : Type} {n : Nat}

structure Names where
  family : DeclName
  constructor : String → DeclName
  eliminator : DeclName

/-- All semantic parameters are explicit guest binders. -/
structure Parameters (I : Interface.{u}) (Head : Type) (n : Nat) where
  context : Ctx Head n
  dataType : I.SortCode → Tm Head n
  indexType : Tm Head n
  familyUniverse : Head
  motiveUniverse : Head

def Parameters.types (parameters : Parameters I Head n) (names : Names) :
    Types.TypeSyntax I Head n where
  dataType := parameters.dataType
  indexType := parameters.indexType
  family := applyClosed parameters.context (fun index => .var index) (.const names.family)
  constructor := fun name =>
    applyClosed parameters.context (fun index => .var index) (.const (names.constructor name))
  motiveUniverse := parameters.motiveUniverse

def familyEntry (parameters : Parameters I Head n) : Entry Head :=
  ⟨closeType parameters.context (.pi parameters.indexType (.head parameters.familyUniverse)), none⟩

def constructorEntry (indices : IndexSyntax I Head) (parameters : Parameters I Head n)
    (names : Names) (constructor : NamedConstructor I []) : Entry Head :=
  ⟨closeType parameters.context
    (Types.constructorType indices constructor.body (parameters.types names) PUnit.unit), none⟩

def eliminatorEntry (indices : IndexSyntax I Head) (parameters : Parameters I Head n)
    (names : Names) (admitted : Admitted I []) : Entry Head :=
  ⟨closeType parameters.context (Types.eliminatorType indices admitted (parameters.types names)), none⟩

def entries (indices : IndexSyntax I Head) (parameters : Parameters I Head n)
    (names : Names) (admitted : Admitted I []) : List (DeclName × Entry Head) :=
  (names.family, familyEntry parameters) ::
    (admitted.constructors.map fun constructor =>
      (names.constructor constructor.name, constructorEntry indices parameters names constructor)) ++
    [(names.eliminator, eliminatorEntry indices parameters names admitted)]

theorem entries_length (indices : IndexSyntax I Head) (parameters : Parameters I Head n)
    (names : Names) (admitted : Admitted I []) :
    (entries indices parameters names admitted).length = admitted.constructors.length + 2 := by
  simp only [entries, List.length_append, List.length_cons, List.length_map, List.length_nil]

theorem entries_names (indices : IndexSyntax I Head) (parameters : Parameters I Head n)
    (names : Names) (admitted : Admitted I []) :
    (entries indices parameters names admitted).map Prod.fst =
      names.family :: admitted.constructors.map (fun constructor => names.constructor constructor.name) ++
        [names.eliminator] := by
  simp [entries, List.map_map, Function.comp_def]

theorem entries_opaque (indices : IndexSyntax I Head) (parameters : Parameters I Head n)
    (names : Names) (admitted : Admitted I []) (item : DeclName × Entry Head)
    (member : item ∈ entries indices parameters names admitted) : item.2.value? = none := by
  simp only [entries, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at member
  rcases member with (rfl | ⟨constructor, _, rfl⟩) | rfl <;> rfl

section Checking

variable (base : Rules Head) [DecidableEq Head]
    [DecidableRel base.headTyping] [DecidablePred base.isUniverse]
    [∀ u v w, Decidable (base.join u v w)] [DecidableRel base.cumulative]
    [DecidableRel base.headEq]
variable (decoder : StructuralConversionCode.RootDecoder base.computation)

abbrev Choices := FormationSensitiveElaboration.Choices Head
  (DeclarationConversionCode.RootCode decoder.Code (fun _ => Empty))

/-- Production follows actual declaration prefixes; it may fail on a typable
library. The independent checker, not the choices or inferred types, decides
whether a produced certificate is accepted. -/
def produce (choices : Choices base decoder) (fuel : Nat) :
    List (DeclName × Entry Head) → List (DeclName × Entry Head) →
      Option (List (DeclarationAdmissionReplay.Certificate Head decoder.Code))
  | _, [] => some []
  | prior, item :: later => do
      let rules := extendRules base (Signature.ofList prior)
      let formation ← FormationSensitiveElaboration.synth rules choices fuel .nil item.2.type
      let level ← match formation.type with
        | .head level => some level
        | _ => none
      let value ← match item.2.value? with
        | none => some none
        | some value => do
            let evidence ← FormationSensitiveElaboration.check rules choices fuel .nil value item.2.type
            some (some evidence)
      let rest ← produce choices fuel (prior ++ [item]) later
      pure (⟨level, formation.evidence, value⟩ :: rest)

def elaborate (choices : Choices base decoder) (fuel : Nat)
    (prior source : List (DeclName × Entry Head)) :
    Option (List (DeclarationAdmissionReplay.Certificate Head decoder.Code)) := do
  let certificates ← produce base decoder choices fuel prior source
  if DeclarationAdmissionReplay.check base decoder prior source certificates then
    some certificates
  else none

theorem elaborate_checked (choices : Choices base decoder) (fuel : Nat)
    (prior source : List (DeclName × Entry Head))
    (certificates : List (DeclarationAdmissionReplay.Certificate Head decoder.Code))
    (produced : elaborate base decoder choices fuel prior source = some certificates) :
    DeclarationAdmissionReplay.check base decoder prior source certificates = true := by
  cases result : produce base decoder choices fuel prior source with
  | none => simp [elaborate, result] at produced
  | some found =>
      by_cases checked : DeclarationAdmissionReplay.check base decoder prior source found = true
      · have same : found = certificates := by simpa [elaborate, result, checked] using produced
        simpa [same] using checked
      · simp [elaborate, result, checked] at produced

theorem elaborate_sound (choices : Choices base decoder) (fuel : Nat)
    (prior source : List (DeclName × Entry Head))
    (certificates : List (DeclarationAdmissionReplay.Certificate Head decoder.Code))
    (produced : elaborate base decoder choices fuel prior source = some certificates) :
    DeclarationAdmissionReplay.Admitted base prior source :=
  DeclarationAdmissionReplay.check_sound base decoder
    (elaborate_checked base decoder choices fuel prior source certificates produced)

/-- The caller supplies the authored document, not a replacement guest table.
Structural admission and prefix typing must both succeed before publication. -/
def admitSource (choices : Choices base decoder) (fuel : Nat)
    (prior : List (DeclName × Entry Head)) (indices : IndexSyntax I Head)
    (parameters : Parameters I Head n) (names : Names) (source : Document I []) :
    Option ((_ : Admitted I []) ×
      List (DeclarationAdmissionReplay.Certificate Head decoder.Code)) := do
  let admitted ← IndexedInductive.admit? source
  let certificates ← elaborate base decoder choices fuel prior
    (entries indices parameters names admitted)
  pure ⟨admitted, certificates⟩

theorem admitSource_sound (choices : Choices base decoder) (fuel : Nat)
    (prior : List (DeclName × Entry Head)) (indices : IndexSyntax I Head)
    (parameters : Parameters I Head n) (names : Names) (source : Document I [])
    (admitted : Admitted I [])
    (certificates : List (DeclarationAdmissionReplay.Certificate Head decoder.Code))
    (accepted : admitSource base decoder choices fuel prior indices parameters names source =
      some ⟨admitted, certificates⟩) :
    admitted.constructors.map quoteConstructor = source.values ∧
      DeclarationAdmissionReplay.Admitted base prior (entries indices parameters names admitted) := by
  cases structural : IndexedInductive.admit? source with
  | none => simp [admitSource, structural] at accepted
  | some found =>
      cases typed : elaborate base decoder choices fuel prior (entries indices parameters names found) with
      | none => simp [admitSource, structural, typed] at accepted
      | some evidence =>
          have same : (⟨found, evidence⟩ : (_ : Admitted I []) ×
              List (DeclarationAdmissionReplay.Certificate Head decoder.Code)) =
              ⟨admitted, certificates⟩ := by
            simpa [admitSource, structural, typed] using accepted
          cases same
          exact ⟨source_of_admit source admitted structural,
            elaborate_sound base decoder choices fuel prior _ certificates typed⟩

theorem elaborate_zero_cons (choices : Choices base decoder)
    (prior : List (DeclName × Entry Head)) (item : DeclName × Entry Head)
    (later : List (DeclName × Entry Head)) :
    elaborate base decoder choices 0 prior (item :: later) = none := by
  simp [elaborate, produce, FormationSensitiveElaboration.synth]

theorem generated_zero_budget (choices : Choices base decoder)
    (prior : List (DeclName × Entry Head)) (indices : IndexSyntax I Head)
    (parameters : Parameters I Head n) (names : Names) (admitted : Admitted I []) :
    elaborate base decoder choices 0 prior (entries indices parameters names admitted) = none := by
  exact elaborate_zero_cons base decoder choices prior _ _

end Checking

/-- Prefix admission yields a formed signature for an opaque inventory. This
does not license any root computation or assert inhabitation of opaque types. -/
theorem opaque_formed (base : Rules Head) (source : List (DeclName × Entry Head))
    (admitted : DeclarationAdmissionReplay.Admitted base [] source)
    (opaqueEntries : ∀ item ∈ source, item.2.value? = none) :
    (Signature.ofList source).Formed base where
  fresh := by
    intro name entry lookup
    exact (admitted.member_typed base (Signature.entries_ofList_mem source lookup)).1
  types := by
    intro name type lookup
    cases selected : (Signature.ofList source).entries name with
    | none => simp [Signature.typeOf?, selected] at lookup
    | some entry =>
        have same : entry.type = type := by simpa [Signature.typeOf?, selected] using lookup
        obtain ⟨_, level, isUniverse, typed, _⟩ :=
          admitted.member_typed base (Signature.entries_ofList_mem source selected)
        exact ⟨level, isUniverse, by simpa [same] using typed.toRaw⟩
  values := by
    intro name type value _ lookup
    cases selected : (Signature.ofList source).entries name with
    | none => simp [Signature.valueOf?, selected] at lookup
    | some entry =>
        have empty : entry.value? = none := opaqueEntries (name, entry) (Signature.entries_ofList_mem source selected)
        simp [Signature.valueOf?, selected, empty] at lookup
  noSelfDelta := by
    intro name value lookup
    cases selected : (Signature.ofList source).entries name with
    | none => simp [Signature.valueOf?, selected] at lookup
    | some entry =>
        have empty : entry.value? = none := opaqueEntries (name, entry) (Signature.entries_ofList_mem source selected)
        simp [Signature.valueOf?, selected, empty] at lookup

#print axioms elaborate_sound
#print axioms opaque_formed

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Declarations
