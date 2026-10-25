import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllOriginalInputUniverses

/-!
# A common recursor capacity for Vector evidence and result profiles

The lower Vector retains its original element-universe bound. The separately
named output Vector retains the common result bound. Both declaration sets
use the larger recursor capacity already required by the evidence-universe
maps. Their four shared Nat declarations therefore agree literally.

Formation of this assembly is distinct from interpreting its declarations,
proving an observer comparison or qualifying a native implementation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllCommonRecursorProfile

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration RussellTarski
open NativeNaturalVectorFamilies
open NativeVectorAll.ResultView

abbrev dataLevel := NativeVectorAll.Universes.dataLevel
abbrev resultLevel := NativeVectorAll.Universes.predicateLevel
abbrev resultContainerLevel := NativeVectorAll.Universes.resultLevel
abbrev evidenceUpperLevel := NativeVectorAll.Universes.CumulativeElimination.upperLevel
def recursorLevel : LevelExpr Nat := .succ evidenceUpperLevel

abbrev lower := NativeVectorAll.Universes.CumulativeElimination.signature

def outputLevels (parameter : Nat) : LevelExpr Nat :=
  if parameter = 0 then resultContainerLevel
  else if parameter = 1 then recursorLevel
  else .param parameter

def outputInstance : LevelInstance rawSignature outputLevels where
  computation := iotaComputation
  computationMap step := by
    obtain ⟨evidence⟩ := step
    exact ⟨Programs.mapIota (substLevelsHead outputLevels) evidence⟩

def output := outputInstance.signature.renameConst OriginalInputUniverses.names

theorem lower_formed : lower.Formed Tower.rules :=
  NativeVectorAll.Universes.CumulativeElimination.levelInstance.formed rawSignature_formed

theorem output_formed : output.Formed Tower.rules :=
  (outputInstance.formed rawSignature_formed).renameConst OriginalInputUniverses.names

theorem compatible : Signature.Compatible lower output := by
  intro name first second firstFound secondFound
  have supported : name = natName ∨ name = zeroName ∨ name = succName ∨ name = natEliminateName ∨
      name = vecName ∨ name = vnilName ∨ name = vconsName ∨ name = vecEliminateName := by
    change (rawSignature.entries name).map _ = some first at firstFound
    obtain ⟨original, known, _⟩ := Option.map_eq_some_iff.mp firstFound
    have present := Signature.entries_ofList_mem declarations known
    have namePresent : name ∈ declarations.map Prod.fst :=
      List.mem_map.mpr ⟨(name, original), present, rfl⟩
    simpa only [declarations, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, Prod.fst] using namePresent
  rcases supported with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have same : output.entries natName = lower.entries natName := by rfl
    rw [same] at secondFound
    exact Option.some.inj (firstFound.symm.trans secondFound)
  · have same : output.entries zeroName = lower.entries zeroName := by rfl
    rw [same] at secondFound
    exact Option.some.inj (firstFound.symm.trans secondFound)
  · have same : output.entries succName = lower.entries succName := by rfl
    rw [same] at secondFound
    exact Option.some.inj (firstFound.symm.trans secondFound)
  · have same : output.entries natEliminateName = lower.entries natEliminateName := by rfl
    rw [same] at secondFound
    exact Option.some.inj (firstFound.symm.trans secondFound)
  · change none = some second at secondFound
    cases secondFound
  · change none = some second at secondFound
    cases secondFound
  · change none = some second at secondFound
    cases secondFound
  · change none = some second at secondFound
    cases secondFound

def signature := Signature.merge lower output
abbrev rules := extendRules Tower.rules signature

theorem signature_formed : signature.Formed Tower.rules :=
  lower_formed.merge output_formed compatible

theorem shared_natural_eliminator : output.entries natEliminateName = lower.entries natEliminateName := rfl

theorem lower_vector_retained : signature.typeOf? vecName = lower.typeOf? vecName := rfl

theorem output_vector_retained : signature.typeOf? `CumulativeTower.VecUpper =
    output.typeOf? `CumulativeTower.VecUpper := rfl

theorem evidence_profile_inclusion :
    NativeVectorAll.Universes.CumulativeElimination.rules.Morphism rules (fun head => head) :=
  extensionMorphism Tower.rules (Signature.merge_left lower output)

theorem recursor_capacity_strict (valuation : Nat → Nat) :
    resultContainerLevel.eval valuation < recursorLevel.eval valuation := by
  exact Nat.lt_succ_of_le (Nat.le_max_left _ _)

def decoder : StructuralConversionCode.RootDecoder rules.computation :=
  DeclarationConversionCode.rootDecoder (base := Tower.rules) (signature := signature)
    (.ofEmpty _ rfl) (Checking.iotaDecoder.union (Checking.iotaDecoder.renameConst OriginalInputUniverses.names))

def choices : FormationSensitiveElaboration.Choices Tower.Head decoder.Code := OriginalInputUniverses.choices

namespace Projection

open TypedEquality.Normalization

def inputType {n : Nat} (evidenceLevel : LevelExpr Nat)
    (element result length vector : Tower.Tm n) : Tower.Tm n :=
  NativeVectorAll.Universes.Canonical.allTypeAtUniverse evidenceLevel element
    (predicate result) length vector

def motive {n : Nat} (evidenceLevel : LevelExpr Nat) (element result : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.pi (inputType evidenceLevel (NativeVectorAll.weaken2 element)
    (NativeVectorAll.weaken2 result) (.var 1) (.var 0))
    (OriginalInputUniverses.upperVec (rename wk (NativeVectorAll.weaken2 result)) (.var 2))))

def project {n : Nat} (evidenceLevel : LevelExpr Nat)
    (element result length vector evidence : Tower.Tm n) : Tower.Tm n :=
  .app (vecEliminateApp element (motive evidenceLevel element result)
    (OriginalInputUniverses.nilCase result) (OriginalInputUniverses.consCase result) length vector) evidence

/-- Constructor-vector execution is independent of the displayed evidence
universe and retains the complete ordered sequence of evidence heads. -/
theorem project_reads {n : Nat} (evidenceLevel : LevelExpr Nat) (element result : Tower.Tm n)
    (values : List (Tower.Tm n)) (evidence : Tower.Tm n) :
    TypedEquality.Reduces rules
      (project evidenceLevel element result (NativeVectorAll.CanonicalAdequacy.numeral values.length)
        (NativeVectorAll.CanonicalAdequacy.encodeVector element values) evidence)
      (OriginalInputUniverses.Computation.encodeResults result (PairSpine.reads values.length evidence)) :=
  NativeVectorAll.ResultView.EvidenceElimination.fold_reads rules
    (fun retained => RootStep.declared (Or.inl ⟨retained⟩))
    element (motive evidenceLevel element result) (OriginalInputUniverses.nilCase result)
    (OriginalInputUniverses.consCase result) (OriginalInputUniverses.Computation.resultNil result)
    (OriginalInputUniverses.Computation.resultCons result)
    (OriginalInputUniverses.Computation.nil_beta rules result)
    (OriginalInputUniverses.Computation.cons_beta rules result) values evidence

theorem substitute_inputType {n m : Nat} (sigma : Sub Tower.Head n m)
    (evidenceLevel : LevelExpr Nat) (element result length vector : Tower.Tm n) :
    subst sigma (inputType evidenceLevel element result length vector) =
      inputType evidenceLevel (subst sigma element) (subst sigma result)
        (subst sigma length) (subst sigma vector) := by
  simp only [inputType, NativeVectorAll.Universes.Canonical.substitute_allTypeAtUniverse,
    predicate, subst, subst_liftSub_wk]

theorem substitute_motive {n m : Nat} (sigma : Sub Tower.Head n m)
    (evidenceLevel : LevelExpr Nat) (element result : Tower.Tm n) :
    subst sigma (motive evidenceLevel element result) =
      motive evidenceLevel (subst sigma element) (subst sigma result) := by
  simp only [motive, subst, substitute_inputType, NativeVectorAll.subst_weaken2,
    OriginalInputUniverses.upperVec, appSpine, List.foldl_cons, List.foldl_nil,
    subst_liftSub_wk]
  rfl

theorem substitute_project {n m : Nat} (sigma : Sub Tower.Head n m)
    (evidenceLevel : LevelExpr Nat) (element result length vector evidence : Tower.Tm n) :
    subst sigma (project evidenceLevel element result length vector evidence) =
      project evidenceLevel (subst sigma element) (subst sigma result)
        (subst sigma length) (subst sigma vector) (subst sigma evidence) := by
  simp only [project, vecEliminateApp, appSpine, List.foldl_cons, List.foldl_nil,
    subst, substitute_motive, OriginalInputUniverses.nilCase,
    OriginalInputUniverses.consCase, NativeVectorAll.subst_weaken4, subst_liftSub_wk]
  rfl

def programme (evidenceLevel : LevelExpr Nat) : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (.lam
    (project evidenceLevel (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))))))

def programmeType (evidenceLevel : LevelExpr Nat) : Tower.Tm 0 :=
  .pi (sortTm dataLevel) (.pi (sortTm resultLevel) (.pi natTm
    (.pi (vecApp (.var 2) (.var 0))
      (.pi (inputType evidenceLevel (.var 3) (.var 2) (.var 1) (.var 0))
        (OriginalInputUniverses.upperVec (.var 3) (.var 2))))))

theorem lower_programme_readback : programme resultContainerLevel = OriginalInputUniverses.program := by
  decide +kernel

theorem lower_type_readback : programmeType resultContainerLevel = OriginalInputUniverses.programType := by
  decide +kernel

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

def accepted (evidenceLevel : LevelExpr Nat) : Bool :=
  (FormationSensitiveElaboration.elaborate rules decoder choices 256 .nil
    (programme evidenceLevel) (programmeType evidenceLevel)).isSome


end Projection

#print axioms compatible
#print axioms signature_formed
#print axioms evidence_profile_inclusion
#print axioms recursor_capacity_strict

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllCommonRecursorProfile
