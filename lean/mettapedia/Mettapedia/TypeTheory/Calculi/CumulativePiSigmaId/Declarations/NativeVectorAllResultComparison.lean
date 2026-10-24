import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllCommonRecursorChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllTypedMaps
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeIndexedRootConversionCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeFormationReadback

/-!
# Vector-result comparison in a common identity-bearing profile

The common evidence/result profile is joined with the existing native identity
signature. The retained Vector/identity profile includes into the assembly,
so its typed evidence maps remain available without changing their universe
annotations. Comparison programs use Vector induction and declared identity
elimination. Their checking is a separate finite replay obligation.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration RussellTarski
open NativeNaturalVectorFamilies
open NativeVectorAll.ResultView
open TypedEquality.Normalization

abbrev resultContainerLevel := NativeVectorAllCommonRecursorProfile.resultContainerLevel
abbrev evidenceUpperLevel := NativeVectorAllCommonRecursorProfile.evidenceUpperLevel
abbrev common := NativeVectorAllCommonRecursorProfile.signature
abbrev identitySignature := NativeVectorIdentityComparison.identitySignature

theorem output_identity_disjoint : Signature.Compatible
    NativeVectorAllCommonRecursorProfile.output identitySignature := by
  intro name first second firstFound secondFound
  change (NativeIndexedFamilies.Intrinsic.rawSignature.entries name).map _ = some second at secondFound
  obtain ⟨original, known, _⟩ := Option.map_eq_some_iff.mp secondFound
  have present := Signature.entries_ofList_mem NativeIndexedFamilies.Intrinsic.declarations known
  have names : name ∈ NativeIndexedFamilies.Intrinsic.declarations.map Prod.fst :=
    List.mem_map.mpr ⟨(name, original), present, rfl⟩
  have supported : name = NativeIndexedFamilies.Intrinsic.listName ∨
      name = NativeIndexedFamilies.Intrinsic.nilName ∨
      name = NativeIndexedFamilies.Intrinsic.consName ∨
      name = NativeIndexedFamilies.Intrinsic.eliminateName ∨
      name = NativeIndexedFamilies.Intrinsic.identityEliminateName := by
    simpa only [NativeIndexedFamilies.Intrinsic.declarations, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, Prod.fst] using names
  rcases supported with rfl | rfl | rfl | rfl | rfl
  all_goals change none = some first at firstFound; cases firstFound

theorem compatible : Signature.Compatible common identitySignature := by
  intro name first second firstFound secondFound
  change (Signature.merge NativeVectorAllCommonRecursorProfile.lower
    NativeVectorAllCommonRecursorProfile.output).entries name = some first at firstFound
  rcases Signature.merge_origin NativeVectorAllCommonRecursorProfile.lower
    NativeVectorAllCommonRecursorProfile.output name with lower | output
  · rw [lower] at firstFound
    exact NativeVectorIdentityComparison.compatible name first second firstFound secondFound
  · rw [output] at firstFound
    exact output_identity_disjoint name first second firstFound secondFound

def signature := Signature.merge common identitySignature
abbrev rules := extendRules Tower.rules signature

theorem signature_formed : signature.Formed Tower.rules :=
  NativeVectorAllCommonRecursorProfile.signature_formed.merge
    (NativeIndexedFamilies.IntrinsicMaps.listSignatureAt_formed evidenceUpperLevel) compatible

theorem common_inclusion : common.Extends signature := Signature.merge_left _ _

theorem previous_inclusion : NativeVectorIdentityComparison.signature.Extends signature where
  entries := by
    intro name entry found
    change (Signature.merge NativeVectorIdentityComparison.vectorSignature identitySignature).entries name =
      some entry at found
    rcases Signature.merge_origin NativeVectorIdentityComparison.vectorSignature identitySignature name
      with lower | identity
    · rw [lower] at found
      exact Signature.merge_entries_left _ _
        (Signature.merge_entries_left _ _ found)
    · rw [identity] at found
      exact Signature.merge_entries_right compatible found
  computation := by
    intro n left right step
    rcases step with lower | identity
    · exact Or.inl (Or.inl lower)
    · exact Or.inr identity

theorem previous_morphism : NativeVectorIdentityComparison.rules.Morphism rules (fun head => head) :=
  extensionMorphism Tower.rules previous_inclusion

theorem lower_projection_formed : FormationSensitive.Judgment rules .nil
    OriginalInputUniverses.program OriginalInputUniverses.programType :=
  NativeVectorAllCommonRecursorProfile.Projection.lower_typed.monoSignature common_inclusion

theorem upper_projection_formed : FormationSensitive.Judgment rules .nil
    (NativeVectorAllCommonRecursorProfile.Projection.programme evidenceUpperLevel)
    (NativeVectorAllCommonRecursorProfile.Projection.programmeType evidenceUpperLevel) :=
  NativeVectorAllCommonRecursorProfile.Projection.upper_typed.monoSignature common_inclusion

theorem forward_map_typed : TypedEquality.Typed rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forward
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forwardType :=
  NativeVectorAllTypedMaps.forward_typed.of_morphism previous_morphism

theorem backward_map_typed : TypedEquality.Typed rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.backward
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.backwardType :=
  NativeVectorAllTypedMaps.backward_typed.of_morphism previous_morphism

def identityRootDecoder : StructuralConversionCode.RootDecoder identitySignature.computation where
  Code := NativeIndexedFamilies.Intrinsic.IotaEvidenceCode
  decode := NativeIndexedRootConversionCode.decode
  sound := by
    intro n code left right decoded
    have step := NativeIndexedRootConversionCode.decode_sound code decoded
    cases step with
    | inherited impossible => exact impossible.elim
    | delta unfolding =>
      rw [NativeIndexedFamilies.Intrinsic.rawSignature_valueOf_none] at unfolding
      cases unfolding
    | declared retained => exact retained
  complete step := by
    obtain ⟨evidence⟩ := step
    exact ⟨evidence.code, NativeIndexedRootConversionCode.decode_evidence evidence⟩

def decoder : StructuralConversionCode.RootDecoder rules.computation :=
  DeclarationConversionCode.rootDecoder (base := Tower.rules) (signature := signature)
    (.ofEmpty _ rfl)
    ((Checking.iotaDecoder.union (Checking.iotaDecoder.renameConst OriginalInputUniverses.names)).union
      identityRootDecoder)

def searchRoot {n : Nat} (term : Tower.Tm n) : Option (decoder.Code n) := do
  match ← OriginalInputUniverses.searchRoot term with
  | .inherited impossible => nomatch impossible
  | .delta name => return .delta name
  | .declared code => return .declared (.inl code)

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def choices : FormationSensitiveElaboration.Choices Tower.Head decoder.Code where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (rules.cumulative first second)
  normalize fuel term := match StructuralConversionSearch.normalize decoder searchRoot
      (headEq := rules.headEq) fuel term with
    | none => term
    | some normalized => normalized.term
  conversion fuel left right := StructuralConversionSearch.compare decoder searchRoot
    (headEq := rules.headEq) fuel left right

private theorem steps_monoSignature {first second : Signature Tower.Head}
    (inclusion : first.Extends second) {n : Nat} {left right : Tower.Tm n}
    (path : TypedEquality.Reduces (extendRules Tower.rules first) left right) :
    TypedEquality.Reduces (extendRules Tower.rules second) left right := by
  have morphism := extensionMorphism Tower.rules inclusion
  induction path with
  | refl => exact .refl
  | tail _ step ih =>
      apply Relation.ReflTransGen.tail ih
      simpa only [Tm.mapHead_id] using
        step.mapHead (fun head => head) morphism.headEq morphism.computation

def mapped {n : Nat} (source target : LevelExpr Nat)
    (element result length vector evidence : Tower.Tm n) : Tower.Tm n :=
  .app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map source target
    element (predicate result) length vector) evidence

def goal {n : Nat} (source target : LevelExpr Nat)
    (element result length vector evidence : Tower.Tm n) : Tower.Tm n :=
  .id (OriginalInputUniverses.upperVec result length)
    (NativeVectorAllCommonRecursorProfile.Projection.project target element result length vector
      (mapped source target element result length vector evidence))
    (NativeVectorAllCommonRecursorProfile.Projection.project source element result length vector evidence)

/-- On constructor vectors, both readings reduce to the original ordered
heads. The supplied final tail is retained by the evidence map and omitted
by either result reading. This is a directed-computation statement. -/
theorem constructor_readouts {n : Nat} (source target : LevelExpr Nat)
    (element result : Tower.Tm n) (values : List (Tower.Tm n)) (evidence : Tower.Tm n) :
    TypedEquality.Reduces rules
      (NativeVectorAllCommonRecursorProfile.Projection.project target element result
        (NativeVectorAll.CanonicalAdequacy.numeral values.length)
        (NativeVectorAll.CanonicalAdequacy.encodeVector element values)
        (mapped source target element result (NativeVectorAll.CanonicalAdequacy.numeral values.length)
          (NativeVectorAll.CanonicalAdequacy.encodeVector element values) evidence))
      (OriginalInputUniverses.Computation.encodeResults result (PairSpine.reads values.length evidence)) ∧
    TypedEquality.Reduces rules
      (NativeVectorAllCommonRecursorProfile.Projection.project source element result
        (NativeVectorAll.CanonicalAdequacy.numeral values.length)
        (NativeVectorAll.CanonicalAdequacy.encodeVector element values) evidence)
      (OriginalInputUniverses.Computation.encodeResults result (PairSpine.reads values.length evidence)) := by
  have mappedPath := steps_monoSignature
    ((Signature.merge_left NativeVectorAllCommonRecursorProfile.lower
      NativeVectorAllCommonRecursorProfile.output).trans common_inclusion)
    (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.canonical_steps
      source target element (predicate result) values evidence)
  rw [PairSpine.expand_eq_assemble_reads_tail] at mappedPath
  have readPaths := PairSpine.reads_of_reduces_to_assemble rules
    (PairSpine.reads values.length evidence) (PairSpine.tail values.length evidence)
      (mapped source target element result (NativeVectorAll.CanonicalAdequacy.numeral values.length)
        (NativeVectorAll.CanonicalAdequacy.encodeVector element values) evidence) mappedPath
  simp only [PairSpine.reads_length] at readPaths
  refine ⟨?_, steps_monoSignature common_inclusion
    (NativeVectorAllCommonRecursorProfile.Projection.project_reads source element result values evidence)⟩
  exact (steps_monoSignature common_inclusion
    (NativeVectorAllCommonRecursorProfile.Projection.project_reads target element result values
      (mapped source target element result (NativeVectorAll.CanonicalAdequacy.numeral values.length)
        (NativeVectorAll.CanonicalAdequacy.encodeVector element values) evidence))).trans
    (NativeVectorAll.ResultView.EvidenceElimination.encode_reduces rules
      (OriginalInputUniverses.Computation.resultNil result)
      (OriginalInputUniverses.Computation.resultCons result) readPaths)

theorem constructor_witnesses {n : Nat} (source target : LevelExpr Nat)
    (element result : Tower.Tm n) (values witnesses : List (Tower.Tm n)) (last : Tower.Tm n)
    (lengths : values.length = witnesses.length) :
    TypedEquality.Reduces rules
      (NativeVectorAllCommonRecursorProfile.Projection.project target element result
        (NativeVectorAll.CanonicalAdequacy.numeral values.length)
        (NativeVectorAll.CanonicalAdequacy.encodeVector element values)
        (mapped source target element result (NativeVectorAll.CanonicalAdequacy.numeral values.length)
          (NativeVectorAll.CanonicalAdequacy.encodeVector element values)
            (PairSpine.assemble witnesses last)))
      (OriginalInputUniverses.Computation.encodeResults result witnesses) ∧
    TypedEquality.Reduces rules
      (NativeVectorAllCommonRecursorProfile.Projection.project source element result
        (NativeVectorAll.CanonicalAdequacy.numeral values.length)
        (NativeVectorAll.CanonicalAdequacy.encodeVector element values)
        (PairSpine.assemble witnesses last))
      (OriginalInputUniverses.Computation.encodeResults result witnesses) := by
  have readPaths : List.Forall₂ (TypedEquality.Reduces rules)
      (PairSpine.reads values.length (PairSpine.assemble witnesses last)) witnesses := by
    rw [lengths]
    exact PairSpine.reads_of_reduces_to_assemble rules witnesses last
      (PairSpine.assemble witnesses last) .refl
  have decoded := NativeVectorAll.ResultView.EvidenceElimination.encode_reduces rules
    (OriginalInputUniverses.Computation.resultNil result)
    (OriginalInputUniverses.Computation.resultCons result) readPaths
  have both := constructor_readouts source target element result values (PairSpine.assemble witnesses last)
  exact ⟨both.1.trans decoded, both.2.trans decoded⟩

theorem substitute_mapped {n m : Nat} (sigma : Sub Tower.Head n m)
    (source target : LevelExpr Nat) (element result length vector evidence : Tower.Tm n) :
    subst sigma (mapped source target element result length vector evidence) =
      mapped source target (subst sigma element) (subst sigma result) (subst sigma length)
        (subst sigma vector) (subst sigma evidence) := by
  simp only [mapped, subst, NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.substitute_map,
    predicate, subst_liftSub_wk]

theorem substitute_goal {n m : Nat} (sigma : Sub Tower.Head n m)
    (source target : LevelExpr Nat) (element result length vector evidence : Tower.Tm n) :
    subst sigma (goal source target element result length vector evidence) =
      goal source target (subst sigma element) (subst sigma result) (subst sigma length)
        (subst sigma vector) (subst sigma evidence) := by
  simp only [goal, subst, NativeVectorAllCommonRecursorProfile.Projection.substitute_project,
    substitute_mapped, OriginalInputUniverses.upperVec, appSpine, List.foldl_cons, List.foldl_nil]

def motive {n : Nat} (source target : LevelExpr Nat)
    (element result : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.pi
    (NativeVectorAllCommonRecursorProfile.Projection.inputType source
      (NativeVectorAll.weaken2 element) (NativeVectorAll.weaken2 result) (.var 1) (.var 0))
    (goal source target (rename wk (NativeVectorAll.weaken2 element))
      (rename wk (NativeVectorAll.weaken2 result)) (.var 2) (.var 1) (.var 0))))

def nilCase {n : Nat} (result : Tower.Tm n) : Tower.Tm n :=
  .lam (.refl ((.app (.const `CumulativeTower.VecUpper.nil) (rename wk result))))

def weaken5 {n : Nat} (term : Tower.Tm n) : Tower.Tm (n + 5) :=
  rename wk (rename wk (rename wk (rename wk (rename wk term))))

def consCase {n : Nat} (source target : LevelExpr Nat)
    (element result : Tower.Tm n) : Tower.Tm n :=
  let A := weaken5 element
  let R := weaken5 result
  let first := NativeVectorAllCommonRecursorProfile.Projection.project target A R (.var 4) (.var 2)
    (mapped source target A R (.var 4) (.var 2) (.snd (.var 0)))
  let second := NativeVectorAllCommonRecursorProfile.Projection.project source A R (.var 4) (.var 2)
    (.snd (.var 0))
  let action := .lam (appSpine (.const `CumulativeTower.VecUpper.cons)
    [rename wk R, .var 5, .fst (.var 1), .var 0])
  let targetType := OriginalInputUniverses.upperVec R (succApp (.var 4))
  let firstResult := .app action first
  let equalityMotive := .lam (.lam (.id (NativeVectorAll.weaken2 targetType)
    (NativeVectorAll.weaken2 firstResult)
    (.app (NativeVectorAll.weaken2 action) (.var 1))))
  .lam (.lam (.lam (.lam (.lam
    (NativeIndexedFamilies.Intrinsic.identityEliminateApp
      (OriginalInputUniverses.upperVec R (.var 4)) first equalityMotive (.refl firstResult)
      second (.app (.var 1) (.snd (.var 0))))))))

def programme (source target : LevelExpr Nat) : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (.lam
    (.app (vecEliminateApp (.var 4) (motive source target (.var 4) (.var 3))
      (nilCase (.var 3)) (consCase source target (.var 4) (.var 3))
        (.var 2) (.var 1)) (.var 0))))))

def programmeType (source target : LevelExpr Nat) : Tower.Tm 0 :=
  .pi (sortTm NativeVectorAllCommonRecursorProfile.dataLevel)
    (.pi (sortTm NativeVectorAllCommonRecursorProfile.resultLevel)
      (.pi natTm (.pi (vecApp (.var 2) (.var 0))
        (.pi (NativeVectorAllCommonRecursorProfile.Projection.inputType source
          (.var 3) (.var 2) (.var 1) (.var 0))
          (goal source target (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))))))

def parameterContext : Tower.Ctx 4 :=
  .snoc (.snoc (.snoc (.snoc .nil
    (sortTm NativeVectorAllCommonRecursorProfile.dataLevel))
      (sortTm NativeVectorAllCommonRecursorProfile.resultLevel)) natTm)
        (vecApp (.var 2) (.var 0))

def context (source : LevelExpr Nat) : Tower.Ctx 5 :=
  .snoc parameterContext
    (NativeVectorAllCommonRecursorProfile.Projection.inputType source (.var 3) (.var 2) (.var 1) (.var 0))

theorem projection_type_readback (source : LevelExpr Nat) :
    TelescopeAbstraction.closeType (context source)
      (OriginalInputUniverses.upperVec (.var 3) (.var 2)) =
      NativeVectorAllCommonRecursorProfile.Projection.programmeType source := rfl

private theorem context_from_projection {source : LevelExpr Nat}
    (checked : FormationSensitive.Judgment rules .nil
      (NativeVectorAllCommonRecursorProfile.Projection.programme source)
      (NativeVectorAllCommonRecursorProfile.Projection.programmeType source)) :
    FormationSensitive.ContextFormation rules (context source) := by
  obtain ⟨level, isUniverse, formed⟩ := checked.regularity
    (FormationSensitive.towerUniverseRegularity.includeSignature signature)
  have sourceFormation : FormationSensitive.Typing rules .nil
      (TelescopeAbstraction.closeType (context source)
        (OriginalInputUniverses.upperVec (.var 3) (.var 2))) (.head level) := by
    rw [projection_type_readback]
    exact formed.typing
  exact (TelescopeAbstraction.formation_of_closeType (context source) isUniverse sourceFormation).1

theorem lower_context_formed : FormationSensitive.ContextFormation rules (context resultContainerLevel) := by
  apply context_from_projection
  rw [NativeVectorAllCommonRecursorProfile.Projection.lower_programme_readback,
    NativeVectorAllCommonRecursorProfile.Projection.lower_type_readback]
  exact lower_projection_formed

theorem upper_context_formed : FormationSensitive.ContextFormation rules (context evidenceUpperLevel) :=
  context_from_projection upper_projection_formed

def arguments {n : Nat} (element result length vector evidence : Tower.Tm n) : Sub Tower.Head 5 n :=
  consSub evidence (consSub vector (consSub length (consSub result (consSub element Fin.elim0))))

theorem programme_type_readback (source target : LevelExpr Nat) :
    TelescopeAbstraction.closeType (context source)
      (goal source target (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)) =
        programmeType source target := rfl

theorem goal_at_arguments {n : Nat} (source target : LevelExpr Nat)
    (element result length vector evidence : Tower.Tm n) :
    subst (arguments element result length vector evidence)
      (goal source target (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)) =
      goal source target element result length vector evidence := by
  rw [substitute_goal]
  rfl

def application {n : Nat} (source target : LevelExpr Nat)
    (element result length vector evidence : Tower.Tm n) : Tower.Tm n :=
  TelescopeAbstraction.applyClosed (context source)
    (arguments element result length vector evidence) (liftClosed (programme source target))

theorem arguments_typed {n : Nat} {ambient : Tower.Ctx n}
    (source : LevelExpr Nat) {element result length vector evidence : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing rules ambient element
      (sortTm NativeVectorAllCommonRecursorProfile.dataLevel))
    (resultTyped : FormationSensitive.Typing rules ambient result
      (sortTm NativeVectorAllCommonRecursorProfile.resultLevel))
    (lengthTyped : FormationSensitive.Typing rules ambient length natTm)
    (vectorTyped : FormationSensitive.Typing rules ambient vector (vecApp element length))
    (evidenceTyped : FormationSensitive.Typing rules ambient evidence
      (NativeVectorAllCommonRecursorProfile.Projection.inputType source element result length vector)) :
    FormationSensitive.CtxMor rules (context source) ambient
      (arguments element result length vector evidence) := by
  intro index
  fin_cases index
  · change FormationSensitive.Typing rules ambient evidence
      (subst (arguments element result length vector evidence)
        (rename wk (NativeVectorAllCommonRecursorProfile.Projection.inputType source
          (.var 3) (.var 2) (.var 1) (.var 0))))
    have inputExact : subst (arguments element result length vector evidence)
        (rename wk (NativeVectorAllCommonRecursorProfile.Projection.inputType source
          (.var 3) (.var 2) (.var 1) (.var 0))) =
        NativeVectorAllCommonRecursorProfile.Projection.inputType source element result length vector := by
      rw [arguments, subst_consSub_rename_wk,
        NativeVectorAllCommonRecursorProfile.Projection.substitute_inputType]
      rfl
    rw [inputExact]
    exact evidenceTyped
  · exact vectorTyped
  · exact lengthTyped
  · exact resultTyped
  · exact elementTyped

theorem neutral_inputs (source : LevelExpr Nat) :
    FormationSensitive.CtxMor rules (context source) (context source)
      (arguments (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)) :=
  arguments_typed source (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

/-- Applying a checked closed comparison program uses the actual dependent
argument assignment. The input vector and evidence may both be neutral. -/
theorem application_typed (source target : LevelExpr Nat)
    (checked : FormationSensitive.Typing rules .nil
      (programme source target) (programmeType source target))
    {n : Nat} {ambient : Tower.Ctx n}
    (ambientFormation : FormationSensitive.ContextFormation rules ambient)
    {element result length vector evidence : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing rules ambient element
      (sortTm NativeVectorAllCommonRecursorProfile.dataLevel))
    (resultTyped : FormationSensitive.Typing rules ambient result
      (sortTm NativeVectorAllCommonRecursorProfile.resultLevel))
    (lengthTyped : FormationSensitive.Typing rules ambient length natTm)
    (vectorTyped : FormationSensitive.Typing rules ambient vector (vecApp element length))
    (evidenceTyped : FormationSensitive.Typing rules ambient evidence
      (NativeVectorAllCommonRecursorProfile.Projection.inputType source element result length vector)) :
    FormationSensitive.Judgment rules ambient
      (application source target element result length vector evidence)
      (goal source target element result length vector evidence) := by
  have functionTyping : FormationSensitive.Typing rules ambient (liftClosed (programme source target))
      (liftClosed (TelescopeAbstraction.closeType (context source)
        (goal source target (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)))) := by
    rw [programme_type_readback]
    exact FormationCheckedTelescopePrograms.liftClosed_typing checked ambient
  have applied := FormationCheckedTelescopePrograms.apply_typed
    (arguments_typed source elementTyped resultTyped lengthTyped vectorTyped evidenceTyped) functionTyping
  rw [goal_at_arguments] at applied
  exact ⟨ambientFormation, applied⟩

namespace Controls

theorem lower_inputs : FormationSensitive.CtxMor rules (context resultContainerLevel)
    (context resultContainerLevel) (arguments (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)) :=
  arguments_typed resultContainerLevel (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

theorem upper_inputs : FormationSensitive.CtxMor rules (context evidenceUpperLevel)
    (context evidenceUpperLevel) (arguments (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)) :=
  arguments_typed evidenceUpperLevel (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

def repeatedValues : List (Tower.Tm 0) := [zeroTm, zeroTm]
def orderedWitnesses : List (Tower.Tm 0) := [zeroTm, succApp zeroTm]
def suppliedEvidence : Tower.Tm 0 := PairSpine.assemble orderedWitnesses NativeVectorAll.unitEvidence

def originalRead : Tower.Tm 0 :=
  NativeVectorAllCommonRecursorProfile.Projection.project resultContainerLevel natTm natTm
    (NativeVectorAll.CanonicalAdequacy.numeral repeatedValues.length)
    (NativeVectorAll.CanonicalAdequacy.encodeVector natTm repeatedValues) suppliedEvidence

def mappedRead : Tower.Tm 0 :=
  NativeVectorAllCommonRecursorProfile.Projection.project evidenceUpperLevel natTm natTm
    (NativeVectorAll.CanonicalAdequacy.numeral repeatedValues.length)
    (NativeVectorAll.CanonicalAdequacy.encodeVector natTm repeatedValues)
    (mapped resultContainerLevel evidenceUpperLevel natTm natTm
      (NativeVectorAll.CanonicalAdequacy.numeral repeatedValues.length)
      (NativeVectorAll.CanonicalAdequacy.encodeVector natTm repeatedValues) suppliedEvidence)

def result : Tower.Tm 0 := OriginalInputUniverses.Computation.encodeResults natTm orderedWitnesses

theorem repeated_values_readout :
    TypedEquality.Reduces rules mappedRead result ∧ TypedEquality.Reduces rules originalRead result :=
  constructor_witnesses resultContainerLevel evidenceUpperLevel natTm natTm repeatedValues orderedWitnesses
    NativeVectorAll.unitEvidence rfl

theorem exchanged_witnesses_distinct : result ≠
    OriginalInputUniverses.Computation.encodeResults natTm [succApp zeroTm, zeroTm] := by decide +kernel

end Controls

#print axioms signature_formed
#print axioms previous_inclusion

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllResultComparison
