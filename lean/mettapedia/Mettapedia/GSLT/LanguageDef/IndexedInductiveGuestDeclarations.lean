import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestTypes
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestTypes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeAbstraction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms
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

section Production

variable (base : Rules Head) [DecidableEq Head]
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

/-- Production over consecutive source blocks retains the same certificates. -/
theorem produce_append (choices : Choices base decoder) (fuel : Nat)
    (prior first second : List (DeclName × Entry Head)) :
    produce base decoder choices fuel prior (first ++ second) = (do
      let firstCertificates ← produce base decoder choices fuel prior first
      let secondCertificates ← produce base decoder choices fuel (prior ++ first) second
      pure (firstCertificates ++ secondCertificates)) := by
  induction first generalizing prior with
  | nil => simp [produce]
  | cons item later ih =>
      simp only [List.cons_append, produce, ih, List.append_assoc]
      cases formation : FormationSensitiveElaboration.synth
        (extendRules base (Signature.ofList prior)) choices fuel .nil item.2.type with
      | none => simp
      | some result =>
          cases resultType : result.type <;> simp [resultType]
          cases item.2.value? <;> simp [Option.bind_assoc]
theorem produce_length (choices : Choices base decoder) (fuel : Nat)
    (prior source : List (DeclName × Entry Head))
    (certificates : List (DeclarationAdmissionReplay.Certificate Head decoder.Code))
    (produced : produce base decoder choices fuel prior source = some certificates) :
    certificates.length = source.length := by
  induction source generalizing prior certificates with
  | nil =>
      have same : ([] : List (DeclarationAdmissionReplay.Certificate Head decoder.Code)) = certificates := by
        simpa [produce] using produced
      cases same
      rfl
  | cons item later ih =>
      cases formation : FormationSensitiveElaboration.synth
        (extendRules base (Signature.ofList prior)) choices fuel .nil item.2.type with
      | none => simp [produce, formation] at produced
      | some result =>
          cases resultType : result.type <;> simp [produce, formation, resultType] at produced
          cases value : item.2.value? with
          | none =>
              simp only [value, Option.bind_eq_some_iff, Option.some.injEq] at produced
              obtain ⟨rest, restProduced, rfl⟩ := produced
              exact congrArg Nat.succ (ih _ _ restProduced)
          | some term =>
              simp only [value, Option.bind_eq_some_iff, Option.some.injEq] at produced
              obtain ⟨evidence, _, rest, restProduced, rfl⟩ := produced
              exact congrArg Nat.succ (ih _ _ restProduced)


end Production

section Checking

variable (base : Rules Head) [DecidableEq Head]
    [DecidableRel base.headTyping] [DecidablePred base.isUniverse]
    [∀ u v w, Decidable (base.join u v w)] [DecidableRel base.cumulative]
    [DecidableRel base.headEq]
variable (decoder : StructuralConversionCode.RootDecoder base.computation)

def elaborate (choices : Choices base decoder) (fuel : Nat)
    (prior source : List (DeclName × Entry Head)) :
    Option (List (DeclarationAdmissionReplay.Certificate Head decoder.Code)) := do
  let certificates ← produce base decoder choices fuel prior source
  if DeclarationAdmissionReplay.check base decoder prior source certificates then
    some certificates
  else none

/-- Prefix production and independent replay compose on the exact flat
certificate list. The algorithms and their budgets are unchanged. -/
theorem elaborate_append (choices : Choices base decoder) (fuel : Nat)
    (prior first second : List (DeclName × Entry Head)) :
    elaborate base decoder choices fuel prior (first ++ second) = (do
      let firstCertificates ← elaborate base decoder choices fuel prior first
      let secondCertificates ← elaborate base decoder choices fuel (prior ++ first) second
      pure (firstCertificates ++ secondCertificates)) := by
  rw [elaborate, produce_append]
  cases firstProduced : produce base decoder choices fuel prior first with
  | none => simp [elaborate, firstProduced]
  | some firstCertificates =>
      cases secondProduced : produce base decoder choices fuel (prior ++ first) second with
      | none => simp [elaborate, firstProduced, secondProduced]
      | some secondCertificates =>
          have splitCheck := DeclarationAdmissionReplay.check_append base decoder prior first second
            firstCertificates secondCertificates
            (produce_length base decoder choices fuel prior first firstCertificates firstProduced).symm
          cases firstChecked : DeclarationAdmissionReplay.check base decoder prior first firstCertificates
          <;> cases secondChecked : DeclarationAdmissionReplay.check base decoder
            (prior ++ first) second secondCertificates
          <;> simp [elaborate, firstProduced, secondProduced, splitCheck, firstChecked, secondChecked]

theorem elaborate_isSome_append (choices : Choices base decoder) (fuel : Nat)
    (prior first second : List (DeclName × Entry Head)) :
    (elaborate base decoder choices fuel prior (first ++ second)).isSome =
      ((elaborate base decoder choices fuel prior first).isSome &&
        (elaborate base decoder choices fuel (prior ++ first) second).isSome) := by
  rw [elaborate_append]
  cases elaborate base decoder choices fuel prior first <;>
    cases elaborate base decoder choices fuel (prior ++ first) second <;> rfl

/-- Assemble acceptance from one checked declaration and its checked suffix. -/
theorem elaborate_cons_of (choices : Choices base decoder) (fuel : Nat)
    {prior : List (DeclName × Entry Head)} {item : DeclName × Entry Head}
    {later : List (DeclName × Entry Head)}
    (firstAccepted : (elaborate base decoder choices fuel prior [item]).isSome = true)
    (restAccepted : (elaborate base decoder choices fuel (prior ++ [item]) later).isSome = true) :
    (elaborate base decoder choices fuel prior (item :: later)).isSome = true := by
  have same := elaborate_isSome_append base decoder choices fuel prior [item] later
  simpa only [List.singleton_append, firstAccepted, restAccepted, Bool.true_and] using same

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

/-!
## Registered-container declaration inventories

The family, constructors and complete eliminator share one name assignment and
one explicit parameter telescope. The code's uniform parameter count agrees
with that telescope. Prefix admission reuses the producer and independent
replay above; no new checker or computation rule is introduced.

The input is an already resolved registered-container inventory. Textual block
recognition and semantic qualification stay separate. Producer failure does
not establish that a declaration is untypable. The ordinary indexed route is
preserved exactly.
-/

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Declarations.Registered

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Declaration TelescopeAbstraction
open IndexedPositiveContainerGuestTypes (Indexing RegistrySyntax IndexPredicate
  IndicesAdmitted indices_unrestricted constructorType_formedOn)
universe u
variable {I : Interface.{u}} {registry : Registry I} {Head : Type} {n : Nat}

structure Parameters (I : Interface.{u}) (Head : Type) (indexing : Indexing I Head) (n : Nat) where
  context : Ctx Head n
  dataType : I.SortCode → Tm Head n
  indexDomain : indexing.Domain n
  familyUniverse : Head
  motiveUniverse : Head

def Parameters.types {indexing : Indexing I Head}
    (parameters : Parameters I Head indexing n) (names : Names) :
    IndexedPositiveContainerGuestTypes.TypeSyntax I Head n where
  dataType := parameters.dataType
  family := applyClosed parameters.context (fun index => .var index) (.const names.family)
  constructor := fun name =>
    applyClosed parameters.context (fun index => .var index) (.const (names.constructor name))

def familyEntry (indexing : Indexing I Head) (parameters : Parameters I Head indexing n) : Entry Head :=
  ⟨closeType parameters.context (match indexing with
    | .indexed _ => .pi parameters.indexDomain (.head parameters.familyUniverse)
    | .unindexed _ => .head parameters.familyUniverse), none⟩

def constructorEntry (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    (constructor : String × Code I registry n []) : Entry Head :=
  ⟨closeType parameters.context
    (IndexedPositiveContainerGuestTypes.constructorType indexing containers constructor.2
      (parameters.types names) PUnit.unit), none⟩

def eliminatorEntry (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    (constructors : List (String × Code I registry n [])) : Entry Head :=
  ⟨closeType parameters.context
    (IndexedPositiveContainerGuestTypes.eliminatorType indexing containers constructors
      (parameters.types names) parameters.indexDomain parameters.motiveUniverse), none⟩

def entries (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    (constructors : List (String × Code I registry n [])) : List (DeclName × Entry Head) :=
  (names.family, familyEntry indexing parameters) ::
    (constructors.map fun constructor =>
      (names.constructor constructor.1, constructorEntry indexing containers parameters names constructor)) ++
    [(names.eliminator, eliminatorEntry indexing containers parameters names constructors)]

theorem entries_length (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    (constructors : List (String × Code I registry n [])) :
    (entries indexing containers parameters names constructors).length = constructors.length + 2 := by
  simp [entries]

theorem entries_names (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    (constructors : List (String × Code I registry n [])) :
    (entries indexing containers parameters names constructors).map Prod.fst =
      names.family :: constructors.map (fun constructor => names.constructor constructor.1) ++ [names.eliminator] := by
  simp [entries, List.map_map, Function.comp_def]

theorem entries_opaque (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    (constructors : List (String × Code I registry n [])) (item : DeclName × Entry Head)
    (member : item ∈ entries indexing containers parameters names constructors) : item.2.value? = none := by
  simp only [entries, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at member
  rcases member with (rfl | ⟨constructor, _, rfl⟩) | rfl <;> rfl

def Parameters.ofOrdinary (indices : IndexSyntax I Head)
    (parameters : Declarations.Parameters I Head n) : Parameters I Head (.indexed indices) n where
  context := parameters.context
  dataType := parameters.dataType
  indexDomain := parameters.indexType
  familyUniverse := parameters.familyUniverse
  motiveUniverse := parameters.motiveUniverse

theorem familyEntry_ordinary (indices : IndexSyntax I Head)
    (parameters : Declarations.Parameters I Head n) :
    familyEntry (.indexed indices) (Parameters.ofOrdinary indices parameters) =
      Declarations.familyEntry parameters := rfl

theorem constructorEntry_ordinary (indices : IndexSyntax I Head)
    (containers : RegistrySyntax I registry Head) (parameters : Declarations.Parameters I Head n)
    (names : Names) (constructor : NamedConstructor I []) :
    constructorEntry (.indexed indices) containers (Parameters.ofOrdinary indices parameters) names
        (constructor.name, IndexedPositiveContainerGuestTypes.ordinaryCode (parameters := n) constructor.body) =
      Declarations.constructorEntry indices parameters names constructor := by
  exact congrArg (fun term : Tm Head n => (Entry.mk (closeType parameters.context term) none))
    (IndexedPositiveContainerGuestTypes.constructorType_ordinary indices containers
      constructor.body (parameters.types names) PUnit.unit)

theorem eliminatorEntry_ordinary (indices : IndexSyntax I Head)
    (containers : RegistrySyntax I registry Head) (parameters : Declarations.Parameters I Head n)
    (names : Names) (admitted : IndexedInductive.Admitted I []) :
    eliminatorEntry (.indexed indices) containers (Parameters.ofOrdinary indices parameters) names
        (IndexedPositiveContainerGuestTypes.ordinaryInventory (parameters := n) admitted.constructors) =
      Declarations.eliminatorEntry indices parameters names admitted := by
  exact congrArg (fun term : Tm Head n => (Entry.mk (closeType parameters.context term) none))
    (IndexedPositiveContainerGuestTypes.eliminatorType_ordinary indices containers
      admitted (parameters.types names))

theorem entries_ordinary (indices : IndexSyntax I Head)
    (containers : RegistrySyntax I registry Head) (parameters : Declarations.Parameters I Head n)
    (names : Names) (admitted : IndexedInductive.Admitted I []) :
    entries (.indexed indices) containers (Parameters.ofOrdinary indices parameters) names
        (IndexedPositiveContainerGuestTypes.ordinaryInventory (parameters := n) admitted.constructors) =
      Declarations.entries indices parameters names admitted := by
  rw [entries, Declarations.entries, familyEntry_ordinary, eliminatorEntry_ordinary]
  simp only [IndexedPositiveContainerGuestTypes.ordinaryInventory,
    List.map_map, Function.comp_def, constructorEntry_ordinary]

section Admission
variable (base : Rules Head) [DecidableEq Head]
    [DecidableRel base.headTyping] [DecidablePred base.isUniverse]
    [∀ u v w, Decidable (base.join u v w)] [DecidableRel base.cumulative]
    [DecidableRel base.headEq]
variable (decoder : StructuralConversionCode.RootDecoder base.computation)

def admitInventory (choices : Choices base decoder) (fuel : Nat)
    (prior : List (DeclName × Entry Head))
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    (constructors : List (String × Code I registry n [])) :=
  elaborate base decoder choices fuel prior (entries indexing containers parameters names constructors)

theorem admitInventory_sound (choices : Choices base decoder) (fuel : Nat)
    (prior : List (DeclName × Entry Head))
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    (constructors : List (String × Code I registry n []))
    (certificates : List (DeclarationAdmissionReplay.Certificate Head decoder.Code))
    (accepted : admitInventory base decoder choices fuel prior indexing containers parameters names constructors = some certificates) :
    DeclarationAdmissionReplay.Admitted base prior (entries indexing containers parameters names constructors) :=
  elaborate_sound base decoder choices fuel prior _ certificates accepted

/-- An admitted prior inventory and accepted generated suffix form one opaque
library. Formation of dependencies is not inferred from suffix acceptance. -/
theorem admitInventory_formed (choices : Choices base decoder) (fuel : Nat)
    (prior : List (DeclName × Entry Head))
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    (constructors : List (String × Code I registry n []))
    (certificates : List (DeclarationAdmissionReplay.Certificate Head decoder.Code))
    (priorAdmitted : DeclarationAdmissionReplay.Admitted base [] prior)
    (opaquePrior : ∀ item ∈ prior, item.2.value? = none)
    (accepted : admitInventory base decoder choices fuel prior indexing containers parameters names constructors = some certificates) :
    (Signature.ofList (prior ++ entries indexing containers parameters names constructors)).Formed base := by
  apply Declarations.opaque_formed base _
    (priorAdmitted.append base (admitInventory_sound base decoder choices fuel prior
      indexing containers parameters names constructors certificates accepted))
  intro item member
  rcases List.mem_append.mp member with old | generated
  · exact opaquePrior item old
  · exact entries_opaque indexing containers parameters names constructors item generated

/-- The checker evidence also justifies source-name lookup without a separate
name-distinctness assumption on the generated inventory. -/
theorem admitInventory_names (choices : Choices base decoder) (fuel : Nat)
    (prior : List (DeclName × Entry Head))
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    (constructors : List (String × Code I registry n []))
    (certificates : List (DeclarationAdmissionReplay.Certificate Head decoder.Code))
    (priorAdmitted : DeclarationAdmissionReplay.Admitted base [] prior)
    (accepted : admitInventory base decoder choices fuel prior indexing containers parameters names constructors = some certificates) :
    (prior.map Prod.fst ++ (names.family ::
      constructors.map (fun constructor => names.constructor constructor.1) ++ [names.eliminator])).Nodup := by
  have checked := priorAdmitted.append base (admitInventory_sound base decoder choices fuel prior
    indexing containers parameters names constructors certificates accepted)
  simpa only [List.nil_append, List.map_append, entries_names] using
    checked.names_nodup base (by simp)

/-- An eliminator cannot alias the family, at any production budget. This
refusal follows from admission freshness, independently of producer behavior. -/
theorem aliased_endpoints_refused (choices : Choices base decoder) (fuel : Nat)
    (prior : List (DeclName × Entry Head))
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    (constructors : List (String × Code I registry n []))
    (priorAdmitted : DeclarationAdmissionReplay.Admitted base [] prior)
    (sameName : names.eliminator = names.family) :
    (admitInventory base decoder choices fuel prior indexing containers parameters names constructors).isNone = true := by
  cases result : admitInventory base decoder choices fuel prior indexing containers parameters names constructors with
  | none => rfl
  | some certificates =>
      have distinct := (admitInventory_names base decoder choices fuel prior indexing containers
        parameters names constructors certificates priorAdmitted result).of_append_right
      have absent := (List.nodup_cons.mp distinct).1
      exact False.elim (absent (List.mem_append_right _ (by simp [sameName])))

end Admission
/-! ## Constructor admission from primitive formation contracts -/

open IndexedPositiveContainerGuestTypes (ConstructorPrimitives constructorType_formed TypeSyntax)

theorem constructorEntry_formedOn (R : Rules Head)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    {admittedIndices : IndexPredicate I}
    (constructor : String × Code I registry n [])
    (constructorAdmitted : IndicesAdmitted admittedIndices constructor.2)
    (context : FormationSensitive.ContextFormation R parameters.context)
    (primitives : ConstructorPrimitives R parameters.context (parameters.types names)
      indexing containers parameters.indexDomain parameters.familyUniverse admittedIndices) :
    ∃ level, R.isUniverse level ∧ FormationSensitive.Typing R .nil
      (constructorEntry indexing containers parameters names constructor).type (.head level) := by
  have morphism : FormationSensitive.CtxMor R parameters.context parameters.context ids := by
    intro index
    simpa only [subst_ids, ids] using
      FormationSensitive.Typing.var (R := R) (Γ := parameters.context) index
  have openType := constructorType_formedOn primitives constructor.2 constructorAdmitted ids morphism PUnit.unit (by trivial)
  simp only [TypeSyntax.map, subst_ids] at openType
  exact FormationCheckedTelescopePrograms.close_formed joins context openType primitives.isUniverse

theorem constructorEntry_formed (R : Rules Head)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    (constructor : String × Code I registry n [])
    (context : FormationSensitive.ContextFormation R parameters.context)
    (primitives : ConstructorPrimitives R parameters.context (parameters.types names)
      indexing containers parameters.indexDomain parameters.familyUniverse) :
    ∃ level, R.isUniverse level ∧ FormationSensitive.Typing R .nil
      (constructorEntry indexing containers parameters names constructor).type (.head level) :=
  constructorEntry_formedOn R joins indexing containers parameters names constructor
    (indices_unrestricted constructor.2) context primitives

/-- The generated opaque constructor is admitted at the actual prior prefix. -/
theorem constructorEntry_admittedOn (base : Rules Head) (prior : List (DeclName × Entry Head))
    (joins : ∀ {u v}, base.isUniverse u → base.isUniverse v →
      ∃ w, base.isUniverse w ∧ base.join u v w)
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    {admittedIndices : IndexPredicate I}
    (constructor : String × Code I registry n [])
    (constructorAdmitted : IndicesAdmitted admittedIndices constructor.2)
    (context : FormationSensitive.ContextFormation (extendRules base (Signature.ofList prior)) parameters.context)
    (primitives : ConstructorPrimitives (extendRules base (Signature.ofList prior)) parameters.context
      (parameters.types names) indexing containers parameters.indexDomain parameters.familyUniverse admittedIndices)
    (fresh : (extendRules base (Signature.ofList prior)).constantType (names.constructor constructor.1) = none) :
    DeclarationAdmissionReplay.Admitted base prior
      [(names.constructor constructor.1, constructorEntry indexing containers parameters names constructor)] := by
  obtain ⟨level, universeWitness, formed⟩ :=
    constructorEntry_formedOn (extendRules base (Signature.ofList prior)) joins indexing containers
      parameters names constructor constructorAdmitted context primitives
  exact .cons fresh universeWitness formed (fun value impossible => by cases impossible) (.nil _)

theorem constructorEntry_admitted (base : Rules Head) (prior : List (DeclName × Entry Head))
    (joins : ∀ {u v}, base.isUniverse u → base.isUniverse v →
      ∃ w, base.isUniverse w ∧ base.join u v w)
    (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    (parameters : Parameters I Head indexing n) (names : Names)
    (constructor : String × Code I registry n [])
    (context : FormationSensitive.ContextFormation (extendRules base (Signature.ofList prior)) parameters.context)
    (primitives : ConstructorPrimitives (extendRules base (Signature.ofList prior)) parameters.context
      (parameters.types names) indexing containers parameters.indexDomain parameters.familyUniverse)
    (fresh : (extendRules base (Signature.ofList prior)).constantType (names.constructor constructor.1) = none) :
    DeclarationAdmissionReplay.Admitted base prior
      [(names.constructor constructor.1, constructorEntry indexing containers parameters names constructor)] :=
  constructorEntry_admittedOn base prior joins indexing containers parameters names constructor
    (indices_unrestricted constructor.2) context primitives fresh


#print axioms constructorEntry_formedOn
#print axioms constructorEntry_admittedOn
#print axioms constructorEntry_formed
#print axioms constructorEntry_admitted

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Declarations.Registered
