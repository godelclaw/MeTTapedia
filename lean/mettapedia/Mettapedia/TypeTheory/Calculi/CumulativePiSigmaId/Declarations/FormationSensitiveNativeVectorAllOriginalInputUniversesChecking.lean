import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllOriginalInputUniversesEvidence

/-! Kernel replay of the higher-result program over the original lower-universe input. -/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ResultView.OriginalInputUniverses
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

set_option maxRecDepth 8192 in
theorem replay_checked : FormationSensitiveElaboration.replay rules decoder .nil
    program programType Evidence.submission = true := by decide +kernel

theorem program_formed : FormationSensitive.Judgment rules .nil program programType :=
  FormationSensitiveElaboration.replay_sound rules decoder replay_checked

#print axioms program_formed

open RussellTarski NativeNaturalVectorFamilies TypedEquality.Normalization
theorem unrenamed_signatures_incompatible :
    ¬ Signature.Compatible lower NativeVectorAll.ResultView.Universes.signature := by
  intro compatible
  have low : lower.entries vecName = some
      { type := substLevelsTm NativeVectorAll.Universes.levels vecType } := rfl
  have high : NativeVectorAll.ResultView.Universes.signature.entries vecName = some
      { type := substLevelsTm NativeVectorAll.ResultView.Universes.levels vecType } := rfl
  have identified := congrArg Entry.type (compatible vecName _ _ low high)
  have different : substLevelsTm NativeVectorAll.Universes.levels vecType ≠
      substLevelsTm NativeVectorAll.ResultView.Universes.levels vecType := by decide +kernel
  exact different identified

theorem lower_vector_retained : signature.typeOf? vecName = lower.typeOf? vecName := rfl

theorem upper_vector_retained : signature.typeOf? `CumulativeTower.VecUpper =
    upper.typeOf? `CumulativeTower.VecUpper := rfl


/-- Only the result family is changed in the proposed certificate target. -/
def lowerResultType : Tower.Tm 0 :=
  .pi (sortTm NativeVectorAll.Universes.dataLevel)
    (.pi (sortTm NativeVectorAll.Universes.predicateLevel)
      (.pi natTm
        (.pi (vecApp (.var 2) (.var 0))
          (.pi (NativeVectorAll.Universes.allType (.var 3) (ResultView.predicate (.var 2))
            (.var 1) (.var 0))
            (vecApp (.var 3) (.var 2))))))

set_option maxRecDepth 8192 in
theorem changed_result_certificate_refused : FormationSensitiveElaboration.replay rules decoder
    .nil program lowerResultType Evidence.submission = false := by decide +kernel

theorem qualified_profile : signature.Formed Tower.rules ∧
    FormationSensitive.Judgment rules .nil program programType :=
  ⟨signature_formed, program_formed⟩

def independentRun : Tower.Tm 4 :=
  appSpine (liftClosed program)
    [natTm, .var 3, CanonicalAdequacy.numeral 2,
      CanonicalAdequacy.encodeVector natTm [zeroTm, zeroTm],
      PairSpine.assemble [.var 2, .var 1] (.var 0)]

def independentResult : Tower.Tm 4 :=
  (CanonicalAdequacy.encodeVector (.var 3) [.var 2, .var 1]).mapConst names

def swappedResult : Tower.Tm 4 :=
  (CanonicalAdequacy.encodeVector (.var 3) [.var 1, .var 2]).mapConst names

def independentCode := choices.conversion 96 independentRun independentResult

def codeCheck (target : Tower.Tm 4)
    (code : StructuralConversionCode.Code Tower.Head decoder.Code 4) : Bool :=
  code.check rules.headEq decoder.decode independentRun target

def independentAccepted := independentCode.any (codeCheck independentResult)
def swappedAccepted := independentCode.any (codeCheck swappedResult)

theorem independent_conversion_accepted : independentAccepted = true := by decide +kernel
theorem swapped_conversion_refused : swappedAccepted = false := by decide +kernel

def verdicts : List (String × Bool) :=
  [("original-input Vector results check in their joined universe signature",
      FormationSensitiveElaboration.replay rules decoder .nil program programType Evidence.submission),
   ("the same original-input result certificate refuses a changed result family",
      !(FormationSensitiveElaboration.replay rules decoder .nil program lowerResultType Evidence.submission)),
   ("the original-input result program retains separately supplied position witnesses", independentAccepted),
   ("the same original-input conversion code refuses swapped witnesses", !swappedAccepted)]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp only [verdicts, List.all_cons, List.all_nil, replay_checked,
    changed_result_certificate_refused, independent_conversion_accepted, swapped_conversion_refused]
  rfl

theorem independent_code_controls : independentAccepted = true ∧ swappedAccepted = false :=
  ⟨independent_conversion_accepted, swapped_conversion_refused⟩

#print axioms qualified_profile
#print axioms unrenamed_signatures_incompatible
#print axioms changed_result_certificate_refused
#print axioms independent_conversion_accepted
#print axioms swapped_conversion_refused


open Mettapedia.TypeTheory.UniverseLevel
theorem program_level_transport (theta : Nat → LevelExpr Nat) :
    FormationSensitive.Judgment (resultLevelInstance theta).rules .nil
      (substLevelsTm theta program) (substLevelsTm theta programType) :=
  (resultLevelInstance theta).refinedJudgment program_formed

theorem closed_higher_result_formed :
    FormationSensitive.Judgment (resultLevelInstance closedLevels).rules .nil
      (substLevelsTm closedLevels program) (substLevelsTm closedLevels programType) :=
  program_level_transport closedLevels


#print axioms program_level_transport
#print axioms closed_higher_result_formed

theorem closed_qualified_profile :
    (resultLevelInstance closedLevels).signature.Formed Tower.rules ∧
      FormationSensitive.Judgment (resultLevelInstance closedLevels).rules .nil
        (substLevelsTm closedLevels program) (substLevelsTm closedLevels programType) :=
  ⟨result_signature_level_formed closedLevels, closed_higher_result_formed⟩

/-! ## A checked closed instance returning a vector of types

The source vector has repeated natural-number values. Its independent result
witnesses are Nat and an identity type in U0, collected as data in the upper
Vector. The named definition is installed only after its body has been checked.
-/

namespace ClosedResultDefinition


open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open RussellTarski NativeNaturalVectorFamilies
open TypedEquality.Normalization
open Mettapedia.TypeTheory.UniverseLevel


abbrev instanceClosed := NativeVectorAll.ResultView.OriginalInputUniverses.resultLevelInstance NativeVectorAll.ResultView.OriginalInputUniverses.closedLevels
abbrev base := instanceClosed.rules

def body : Tower.Tm 0 := substLevelsTm NativeVectorAll.ResultView.OriginalInputUniverses.closedLevels NativeVectorAll.ResultView.OriginalInputUniverses.program
def bodyType : Tower.Tm 0 := substLevelsTm NativeVectorAll.ResultView.OriginalInputUniverses.closedLevels NativeVectorAll.ResultView.OriginalInputUniverses.programType
def selfName : DeclName := `CumulativeTower.originalInputResults

def declarations : List (DeclName × Entry Tower.Head) :=
  [(selfName, ⟨bodyType, some body⟩)]

def signature : Signature Tower.Head := Signature.ofList declarations
abbrev rules := extendRules base signature

theorem body_type_formed : ∃ u, base.isUniverse u ∧
    FormationSensitive.Judgment base .nil bodyType (.head u) :=
  NativeVectorAll.ResultView.OriginalInputUniverses.closed_higher_result_formed.regularity
    (FormationSensitive.towerUniverseRegularity.includeSignature instanceClosed.signature)

theorem body_typed : FormationSensitive.Judgment rules .nil body bodyType :=
  NativeVectorAll.ResultView.OriginalInputUniverses.closed_higher_result_formed.includeSignature signature

theorem fresh : base.constantType selfName = none := by decide +kernel

theorem type_lookup (name : DeclName) : signature.typeOf? name =
    if name = selfName then some bodyType else none := by
  by_cases same : name = selfName <;>
    simp [signature, declarations, Signature.ofList, Signature.typeOf?,
      Signature.insert, Signature.empty, same]

theorem value_lookup (name : DeclName) : signature.valueOf? name =
    if name = selfName then some body else none := by
  by_cases same : name = selfName <;>
    simp [signature, declarations, Signature.ofList, Signature.valueOf?,
      Signature.insert, Signature.empty, same]

theorem formed : signature.Formed base where
  fresh := by
    intro name entry known
    by_cases same : name = selfName
    · simpa only [same] using fresh
    · simp [signature, declarations, Signature.ofList, Signature.insert,
        Signature.empty, same] at known
  types := by
    intro name type known
    rw [type_lookup] at known
    split at known
    · cases Option.some.inj known
      obtain ⟨u, universeWitness, typing⟩ := body_type_formed
      exact ⟨u, universeWitness, (typing.includeSignature signature).toRaw⟩
    · cases known
  values := by
    intro name type value known selected
    rw [type_lookup] at known
    rw [value_lookup] at selected
    split at known
    · rename_i same
      simp only [same, ↓reduceIte] at selected
      cases Option.some.inj known
      cases Option.some.inj selected
      exact body_typed.toRaw
    · cases known
  noSelfDelta := by
    intro name value known
    rw [value_lookup] at known
    split at known
    · cases Option.some.inj known
      intro impossible
      cases impossible
    · cases known

theorem constant_known : rules.constantType selfName = some bodyType := by
  apply combinedType_of_signature base signature fresh
  simp [type_lookup]

theorem constant_typed : FormationSensitive.Judgment rules .nil
    (.const selfName) (liftClosed bodyType) := by
  obtain ⟨u, universeWitness, typed⟩ := body_type_formed
  exact ⟨.nil, .const constant_known (typed.typing.includeSignature signature) universeWitness⟩

theorem typed_unfolding {n : Nat} {context : Tower.Ctx n} {displayed : Tower.Tm n}
    (typed : FormationSensitive.Judgment rules context (.const selfName) displayed) :
    StepCore rules.computation rules.headEq (.const selfName : Tower.Tm n) (liftClosed body) ∧
      FormationSensitive.Judgment rules context (liftClosed body) displayed := by
  apply typed.delta (declared := bodyType) (bodyTyped := body_typed.typing)
  · simp [value_lookup]
  · exact constant_known

#print axioms formed
#print axioms constant_typed
#print axioms typed_unfolding

def baseDecoder : StructuralConversionCode.RootDecoder base.computation :=
  DeclarationConversionCode.rootDecoder (base := Tower.rules)
    (signature := instanceClosed.signature) (.ofEmpty _ rfl)
    (Checking.iotaDecoder.union
      (Checking.iotaDecoder.renameConst NativeVectorAll.ResultView.OriginalInputUniverses.names))

def decoder : StructuralConversionCode.RootDecoder rules.computation :=
  DeclarationConversionCode.ofList base baseDecoder declarations

def searchRoot {n : Nat} (term : Tower.Tm n) : Option (decoder.Code n) :=
  ((NativeVectorAll.ResultView.OriginalInputUniverses.searchRoot term).map
    DeclarationConversionCode.RootCode.inherited).orElse (fun _ =>
      match term with
      | .const name => if name = selfName then some (.delta name) else none
      | _ => none)

def choices : FormationSensitiveElaboration.Choices Tower.Head decoder.Code where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (Tower.rules.cumulative first second)
  normalize fuel term :=
    match StructuralConversionSearch.normalize decoder searchRoot
        (headEq := Tower.rules.headEq) fuel term with
    | none => term
    | some candidate => candidate.term
  conversion fuel left right :=
    StructuralConversionSearch.compare decoder searchRoot
      (headEq := Tower.rules.headEq) fuel left right

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

def source : Tower.Tm 0 := NativeVectorAll.CanonicalAdequacy.encodeVector natTm [zeroTm, zeroTm]
def witnesses : Tower.Tm 0 := PairSpine.assemble [natTm, NativeVectorAll.unitType]
  NativeVectorAll.unitEvidence
def application : Tower.Tm 0 := appSpine (.const selfName)
  [natTm, sortTm Tower.zero, NativeVectorAll.CanonicalAdequacy.numeral 2, source, witnesses]
def outputType : Tower.Tm 0 :=
  NativeVectorAll.ResultView.OriginalInputUniverses.upperVec
    (sortTm Tower.zero) (NativeVectorAll.CanonicalAdequacy.numeral 2)
def output : Tower.Tm 0 :=
  (NativeVectorAll.CanonicalAdequacy.encodeVector (sortTm Tower.zero) [natTm, NativeVectorAll.unitType]).mapConst
    NativeVectorAll.ResultView.OriginalInputUniverses.names

def accepted := (FormationSensitiveElaboration.elaborate rules decoder choices 256
  .nil application outputType).isSome

def conversion := choices.conversion 128 application output
def conversionCheck (target : Tower.Tm 0)
    (code : StructuralConversionCode.Code Tower.Head decoder.Code 0) : Bool :=
  code.check rules.headEq decoder.decode application target

def converted := conversion.any (conversionCheck output)

def swapped : Tower.Tm 0 :=
  (NativeVectorAll.CanonicalAdequacy.encodeVector (sortTm Tower.zero)
    [NativeVectorAll.unitType, natTm]).mapConst
    NativeVectorAll.ResultView.OriginalInputUniverses.names

def swappedAccepted := conversion.any (conversionCheck swapped)

set_option maxRecDepth 8192 in
theorem accepted_eq_true : accepted = true := by decide +kernel

theorem application_typed : FormationSensitive.Judgment rules .nil application outputType := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp accepted_eq_true
  exact FormationSensitiveElaboration.elaborate_sound rules decoder choices 256 .nil
    application outputType submission produced

set_option maxRecDepth 8192 in
theorem converted_eq_true : converted = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem swapped_refused : swappedAccepted = false := by decide +kernel

private theorem option_code_sound {n : Nat}
    {left right : Tower.Tm n}
    (candidate : Option (StructuralConversionCode.Code Tower.Head decoder.Code n))
    (check : StructuralConversionCode.Code Tower.Head decoder.Code n → Bool)
    (correct : ∀ code, check code = true →
      code.check rules.headEq decoder.decode left right = true)
    (positive : candidate.any check = true) :
    Conv rules.headEq left right rules.computation := by
  cases candidate with
  | none => simp [Option.any] at positive
  | some code =>
      exact StructuralConversionCode.Code.check_sound decoder
        (correct code (by simpa only [Option.any] using positive))

theorem application_conversion : Conv rules.headEq application output rules.computation :=
  option_code_sound conversion (conversionCheck output) (fun _ checked => checked)
    converted_eq_true

#print axioms application_typed
#print axioms converted_eq_true
#print axioms swapped_refused
#print axioms application_conversion


def outputAccepted := (FormationSensitiveElaboration.elaborate rules decoder choices 256
  .nil output outputType).isSome

set_option maxRecDepth 8192 in
theorem output_accepted : outputAccepted = true := by decide +kernel

theorem output_typed : FormationSensitive.Judgment rules .nil output outputType := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp output_accepted
  exact FormationSensitiveElaboration.elaborate_sound rules decoder choices 256 .nil
    output outputType submission produced

#print axioms output_typed

def verdicts : List (String × Bool) :=
  [("the named original-input result program returns a vector of types", accepted),
   ("the returned vector of types checks independently", outputAccepted),
   ("the vector-of-types application has an independently checked conversion", converted),
   ("the same vector-of-types conversion certificate refuses swapped results", !swappedAccepted)]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp only [verdicts, List.all_cons, List.all_nil, accepted_eq_true,
    converted_eq_true, swapped_refused, output_accepted]
  rfl

end ClosedResultDefinition

namespace ClosedComputationControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open RussellTarski NativeNaturalVectorFamilies TypedEquality.Normalization
open NativeVectorAll.CanonicalAdequacy
open Mettapedia.TypeTheory.IndexedContainer

def values : List (Tower.Tm 0) := [zeroTm, zeroTm]
def heads : List (Tower.Tm 0) := [natTm, NativeVectorAll.unitType]
def evidence : Tower.Tm 0 := PairSpine.assemble heads NativeVectorAll.unitEvidence
def source : Tower.Tm 0 := encodeVector natTm values
def result : Tower.Tm 0 := Computation.encodeResults (sortTm Tower.zero) heads

theorem fold_reads_closed :
    TypedEquality.Reduces rules
      (project natTm (sortTm Tower.zero) (numeral 2) source evidence)
      (Computation.encodeResults (sortTm Tower.zero) (PairSpine.reads 2 evidence)) :=
  EvidenceElimination.fold_reads rules
    (fun witness => RootStep.declared (Or.inl ⟨witness⟩))
    natTm (motive natTm (sortTm Tower.zero)) (nilCase (sortTm Tower.zero))
    (consCase (sortTm Tower.zero)) (Computation.resultNil (sortTm Tower.zero))
    (Computation.resultCons (sortTm Tower.zero))
    (Computation.nil_beta rules (sortTm Tower.zero))
    (Computation.cons_beta rules (sortTm Tower.zero)) values evidence

theorem project_witnesses_closed :
    TypedEquality.Reduces rules
      (project natTm (sortTm Tower.zero) (numeral 2) source evidence) result :=
  Computation.project_witnesses natTm (sortTm Tower.zero) values heads
    NativeVectorAll.unitEvidence rfl

def application : Tower.Tm 0 :=
  appSpine (liftClosed program) [natTm, sortTm Tower.zero, numeral 2, source, evidence]

theorem program_witnesses_closed : TypedEquality.Reduces rules application result :=
  Computation.program_witnesses natTm (sortTm Tower.zero) values heads
    NativeVectorAll.unitEvidence rfl

theorem program_levels_closed :
    TypedEquality.Reduces (resultLevelInstance closedLevels).rules
      (substLevelsTm closedLevels application) (substLevelsTm closedLevels result) :=
  Computation.program_level_witnesses closedLevels natTm (sortTm Tower.zero)
    values heads NativeVectorAll.unitEvidence rfl

noncomputable def registeredEvidence :
    (vectorInductionBundle (fun _ : Tower.Tm 0 => Tower.Tm 0)).Bundle (semanticValue values) := by
  change ListAll (fun _ : Tower.Tm 0 => Tower.Tm 0) [zeroTm, zeroTm]
  exact .cons natTm (.cons NativeVectorAll.unitType .nil)

noncomputable def registeredHeads : List (Tower.Tm 0) :=
  List.ofFn fun position : Fin values.length =>
    ((vectorInductionBundle (fun _ : Tower.Tm 0 => Tower.Tm 0)).exact
      (semanticValue values) registeredEvidence) position

theorem registered_heads_exact : registeredHeads = heads := by rfl

theorem registered_bundle_closed :
    TypedEquality.Reduces rules
      (appSpine (liftClosed program)
        [natTm, sortTm Tower.zero, numeral 2, source, quoteWitnesses registeredHeads])
      (Computation.encodeResults (sortTm Tower.zero) registeredHeads) :=
  Computation.registered_bundle_steps natTm (sortTm Tower.zero)
    (P := fun _ : Tower.Tm 0 => Tower.Tm 0) (fun _ witness => witness) values registeredEvidence

noncomputable def genericHeads : List (Tower.Tm 0) :=
  Mettapedia.TypeTheory.IndexedPositiveContainer.Code.readResults
    Mettapedia.TypeTheory.IndexedPositiveContainer.VectorControl.inductionQualified
    Mettapedia.TypeTheory.IndexedPositiveContainer.VectorControl.orderedFinitary
    (fun _ _ (witness : Tower.Tm 0) => witness)
    (Computation.RegisteredResults.bundle values registeredEvidence)

theorem generic_heads_exact : genericHeads = heads :=
  (Computation.RegisteredResults.readback (fun _ (witness : Tower.Tm 0) => witness)
    values registeredEvidence).trans registered_heads_exact

theorem generic_result_program_closed :
    TypedEquality.Reduces rules
      (appSpine (liftClosed program)
        [natTm, sortTm Tower.zero, numeral 2, source, quoteWitnesses genericHeads])
      (Computation.encodeResults (sortTm Tower.zero) genericHeads) :=
  Computation.RegisteredResults.program_steps natTm (sortTm Tower.zero)
    (P := fun _ : Tower.Tm 0 => Tower.Tm 0) (fun _ witness => witness) values registeredEvidence

#print axioms fold_reads_closed
#print axioms project_witnesses_closed
#print axioms program_witnesses_closed
#print axioms program_levels_closed
#print axioms registered_bundle_closed
#print axioms generic_heads_exact
#print axioms generic_result_program_closed

end ClosedComputationControls

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ResultView.OriginalInputUniverses
