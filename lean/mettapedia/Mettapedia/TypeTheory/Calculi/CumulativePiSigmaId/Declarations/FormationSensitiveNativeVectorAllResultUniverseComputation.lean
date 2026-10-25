import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllResultUniverses
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FormationSensitiveLevelInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralLaws

/-!
# Level-instantiated computation of native Vector results

The enlarged result profile factors through an explicit universe-level
instance of the original native All profile. Its formation-sensitive judgments
and raw source computations transport along this instance. The same result
program therefore computes ordered evidence heads on mapped constructor inputs.
Assembled witnesses may have an arbitrary final evidence tail.

Contexts and inputs follow the level substitution. The comparison retaining
an original lower-universe input with independently higher result evidence
remains separate. These finite paths supply neither inverse equality nor
normalization of arbitrary terms. No conversion rule is added.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ResultView.Universes
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration RussellTarski TypedEquality.Normalization
open NativeNaturalVectorFamilies

private theorem level_composition (level : LevelExpr Nat) :
    LevelExpr.subst programLevels (LevelExpr.subst NativeVectorAll.allLevels level) =
      LevelExpr.subst levels level := by
  induction level with
  | const value => rfl
  | param parameter =>
      by_cases zero : parameter = 0
      · subst parameter; rfl
      · by_cases one : parameter = 1
        · subst parameter; rfl
        · simp [LevelExpr.subst, NativeVectorAll.allLevels, programLevels, levels, zero, one]
  | succ level ih => exact congrArg LevelExpr.succ ih
  | max left right ihLeft ihRight => exact congrArg₂ LevelExpr.max ihLeft ihRight

private theorem head_composition :
    substLevelsHead programLevels ∘ substLevelsHead NativeVectorAll.allLevels =
      substLevelsHead levels := by
  funext head
  cases head with
  | legacyGround => rfl
  | sort level => exact congrArg LevelTower.Head.sort (level_composition level)

private theorem term_composition {n : Nat} (term : Tower.Tm n) :
    substLevelsTm programLevels (substLevelsTm NativeVectorAll.allLevels term) =
      substLevelsTm levels term := by
  simp only [substLevelsTm, Tm.mapHead_comp, head_composition]

private theorem entry_composition (entry : Entry Tower.Head) :
    Entry.instantiateLevels programLevels (Entry.instantiateLevels NativeVectorAll.allLevels entry) =
      Entry.instantiateLevels levels entry := by
  cases entry with
  | mk type value =>
      simp only [Entry.instantiateLevels, term_composition]
      congr 1
      cases value <;> simp [term_composition]

def sourceInstance : LevelInstance NativeVectorAll.signature programLevels where
  computation := NativeNaturalVectorFamilies.iotaComputation
  computationMap step := by
    obtain ⟨evidence⟩ := step
    exact ⟨NativeNaturalVectorFamilies.Programs.mapIota (substLevelsHead programLevels) evidence⟩

theorem sourceInstance_signature : sourceInstance.signature = signature := by
  change (NativeNaturalVectorFamilies.rawSignature.instantiateLevels NativeVectorAll.allLevels
      NativeNaturalVectorFamilies.iotaComputation).instantiateLevels programLevels
      NativeNaturalVectorFamilies.iotaComputation =
    NativeNaturalVectorFamilies.rawSignature.instantiateLevels levels
      NativeNaturalVectorFamilies.iotaComputation
  simp only [Signature.instantiateLevels]
  congr 1
  funext name
  cases found : NativeNaturalVectorFamilies.rawSignature.entries name with
  | none => rfl
  | some entry => simpa only [Option.map_some] using congrArg some (entry_composition entry)


theorem sourceInstance_rules : sourceInstance.rules = rules :=
  congrArg (extendRules Tower.rules) sourceInstance_signature

/-- Transport of an actual source judgment, including its formed context. -/
theorem judgment_map {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : FormationSensitive.Judgment NativeVectorAll.rules context term type) :
    FormationSensitive.Judgment rules (substLevelsCtx programLevels context)
      (substLevelsTm programLevels term) (substLevelsTm programLevels type) := by
  have mapped := sourceInstance.refinedJudgment typed
  rw [sourceInstance_rules] at mapped
  exact mapped

theorem step_map {n : Nat} {left right : Tower.Tm n}
    (step : Step NativeVectorAll.rules.headEq left right NativeVectorAll.rules.computation) :
    Step rules.headEq (substLevelsTm programLevels left)
      (substLevelsTm programLevels right) rules.computation := by
  have mapped := StepCore.mapHead (substLevelsHead programLevels)
    sourceInstance.morphism.headEq sourceInstance.morphism.computation step
  change Step sourceInstance.rules.headEq (substLevelsTm programLevels left)
    (substLevelsTm programLevels right) sourceInstance.rules.computation at mapped
  rw [sourceInstance_rules] at mapped
  exact mapped

theorem steps_map {n : Nat} {left right : Tower.Tm n}
    (path : TypedEquality.Reduces NativeVectorAll.rules left right) :
    TypedEquality.Reduces rules (substLevelsTm programLevels left)
      (substLevelsTm programLevels right) :=
  Relation.ReflTransGen.lift (substLevelsTm programLevels)
    (fun _ _ step => step_map step) _ _ path

open NativeVectorAll.CanonicalAdequacy

theorem program_computes_mapped_inputs {n : Nat}
    (element result : Tower.Tm n) (values : List (Tower.Tm n)) (bundle : Tower.Tm n) :
    TypedEquality.Reduces rules
      (appSpine (liftClosed program)
        [substLevelsTm programLevels element, substLevelsTm programLevels result,
         substLevelsTm programLevels (numeral values.length),
         substLevelsTm programLevels (encodeVector element values),
         substLevelsTm programLevels bundle])
      (substLevelsTm programLevels
        (encodeVector result (PairSpine.reads values.length bundle))) := by
  have source := (ResultView.program_beta NativeVectorAll.rules element result
    (numeral values.length) (encodeVector element values) bundle).trans
      (ResultView.canonical_steps_observe element result values bundle)
  have mapped := steps_map source
  simpa only [substLevelsTm, Tm.mapHead, Tm.mapHead_liftClosed,
    appSpine, List.foldl_cons, List.foldl_nil, program] using mapped

#print axioms step_map
#print axioms steps_map
#print axioms program_computes_mapped_inputs


theorem program_computes_mapped_witnesses {n : Nat}
    (element result : Tower.Tm n) (values witnesses : List (Tower.Tm n))
    (last : Tower.Tm n) (lengths : values.length = witnesses.length) :
    TypedEquality.Reduces rules
      (appSpine (liftClosed program)
        [substLevelsTm programLevels element, substLevelsTm programLevels result,
         substLevelsTm programLevels (numeral values.length),
         substLevelsTm programLevels (encodeVector element values),
         substLevelsTm programLevels (PairSpine.assemble witnesses last)])
      (substLevelsTm programLevels (encodeVector result witnesses)) := by
  have source := (ResultView.program_beta NativeVectorAll.rules element result
    (numeral values.length) (encodeVector element values) (PairSpine.assemble witnesses last)).trans
      (ResultView.canonical_steps_assembled element result values witnesses last lengths)
  have mapped := steps_map source
  simpa only [substLevelsTm, Tm.mapHead, Tm.mapHead_liftClosed,
    appSpine, List.foldl_cons, List.foldl_nil, program] using mapped

theorem program_annotation_changes : program ≠ ResultView.program := by
  decide +kernel

#print axioms program_computes_mapped_witnesses
#print axioms program_annotation_changes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ResultView.Universes
