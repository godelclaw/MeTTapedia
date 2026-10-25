import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.DeclarationConstantTransport
import Mettapedia.TypeTheory.IndexedPositiveContainerInduction
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllResultUniverses
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllUniverses

/-!
# Native Vector results retaining the original input universe

The original Vec at alpha and a separately named Vec at max(alpha,beta)
coexist in one formed signature. Their four shared Nat declarations agree;
the vector type, constructors and eliminator use distinct names. The source
input and its All evidence keep the original lower-universe declarations.
The result program constructs the higher-universe Vec from position evidence.
Its independent finite typing replay is in the checking companion.

The root decoder retains both iota families. Formation and finite replay do
not establish global subject reduction, normalization or native refinement.
-/

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ResultView.OriginalInputUniverses
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies
open TypedEquality.Normalization

def names : DeclName ≃ DeclName :=
  (((Equiv.swap vecName `CumulativeTower.VecUpper).trans
    (Equiv.swap vnilName `CumulativeTower.VecUpper.nil)).trans
    (Equiv.swap vconsName `CumulativeTower.VecUpper.cons)).trans
    (Equiv.swap vecEliminateName `CumulativeTower.VecUpper.eliminate)

abbrev lower := NativeVectorAll.Universes.signature
abbrev upper := NativeVectorAll.ResultView.Universes.signature.renameConst names

theorem lower_formed : lower.Formed Tower.rules :=
  NativeVectorAll.Universes.levelInstance.formed NativeNaturalVectorFamilies.rawSignature_formed

theorem upper_formed : upper.Formed Tower.rules :=
  NativeVectorAll.ResultView.Universes.signature_formed.renameConst names

private theorem lower_support {name : DeclName} {entry : Entry Tower.Head}
    (found : lower.entries name = some entry) :
    name = natName ∨ name = zeroName ∨ name = succName ∨ name = natEliminateName ∨
      name = vecName ∨ name = vnilName ∨ name = vconsName ∨ name = vecEliminateName := by
  change (NativeNaturalVectorFamilies.rawSignature.entries name).map _ = some entry at found
  obtain ⟨original, selected, _⟩ := Option.map_eq_some_iff.mp found
  have member := Signature.entries_ofList_mem NativeNaturalVectorFamilies.declarations selected
  have nameMember : name ∈ NativeNaturalVectorFamilies.declarations.map Prod.fst :=
    List.mem_map.mpr ⟨(name, original), member, rfl⟩
  simpa only [NativeNaturalVectorFamilies.declarations, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false, Prod.fst] using nameMember

theorem compatible : Signature.Compatible lower upper := by
  intro name first second firstFound secondFound
  rcases lower_support firstFound with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have entriesEqual : upper.entries natName = lower.entries natName := by rfl
    rw [entriesEqual] at secondFound
    exact Option.some.inj (firstFound.symm.trans secondFound)
  · have entriesEqual : upper.entries zeroName = lower.entries zeroName := by rfl
    rw [entriesEqual] at secondFound
    exact Option.some.inj (firstFound.symm.trans secondFound)
  · have entriesEqual : upper.entries succName = lower.entries succName := by rfl
    rw [entriesEqual] at secondFound
    exact Option.some.inj (firstFound.symm.trans secondFound)
  · have entriesEqual : upper.entries natEliminateName = lower.entries natEliminateName := by rfl
    rw [entriesEqual] at secondFound
    exact Option.some.inj (firstFound.symm.trans secondFound)
  · change none = some second at secondFound
    cases secondFound
  · change none = some second at secondFound
    cases secondFound
  · change none = some second at secondFound
    cases secondFound
  · change none = some second at secondFound
    cases secondFound

def signature : Signature Tower.Head := Signature.merge lower upper

theorem signature_formed : signature.Formed Tower.rules :=
  lower_formed.merge upper_formed compatible

#print axioms compatible
#print axioms signature_formed

abbrev rules := extendRules Tower.rules signature

def decoder : StructuralConversionCode.RootDecoder rules.computation :=
  DeclarationConversionCode.rootDecoder (base := Tower.rules) (signature := signature)
    (.ofEmpty _ rfl) (Checking.iotaDecoder.union (Checking.iotaDecoder.renameConst names))

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

def searchRoot {n : Nat} (term : Tower.Tm n) : Option (decoder.Code n) :=
  ((NativeVectorAll.searchRows term (List.finRange Checking.table.length)).map
      (fun code => DeclarationConversionCode.RootCode.declared (Sum.inl code))).orElse
    (fun _ => (NativeVectorAll.searchRows (term.mapConst names.symm)
      (List.finRange Checking.table.length)).map
      (fun code => DeclarationConversionCode.RootCode.declared (Sum.inr code)))

def choices : FormationSensitiveElaboration.Choices Tower.Head decoder.Code where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (rules.cumulative first second)
  normalize fuel term :=
    match StructuralConversionSearch.normalize decoder searchRoot
        (headEq := rules.headEq) fuel term with
    | none => term
    | some candidate => candidate.term
  conversion fuel left right :=
    StructuralConversionSearch.compare decoder searchRoot
      (headEq := rules.headEq) fuel left right

def upperVec {n : Nat} (element length : Tower.Tm n) : Tower.Tm n :=
  appSpine (.const `CumulativeTower.VecUpper) [element, length]

def motive {n : Nat} (element result : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.pi
    (NativeVectorAll.Universes.allType (weaken2 element)
      (ResultView.predicate (weaken2 result)) (.var 1) (.var 0))
    (upperVec (rename wk (weaken2 result)) (.var 2))))

def nilCase {n : Nat} (result : Tower.Tm n) : Tower.Tm n :=
  .lam (.app (.const `CumulativeTower.VecUpper.nil) (rename wk result))

def consCase {n : Nat} (result : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.lam (.lam (.lam
    (appSpine (.const `CumulativeTower.VecUpper.cons)
      [rename wk (NativeVectorAll.weaken4 result), .var 4, .fst (.var 0),
        .app (.var 1) (.snd (.var 0))])))))

def project {n : Nat} (element result length vector bundle : Tower.Tm n) : Tower.Tm n :=
  .app (vecEliminateApp element (motive element result) (nilCase result) (consCase result)
    length vector) bundle

def program : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (.lam
    (project (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))))))

def programType : Tower.Tm 0 :=
  .pi (sortTm NativeVectorAll.Universes.dataLevel)
    (.pi (sortTm NativeVectorAll.Universes.predicateLevel)
      (.pi natTm
        (.pi (vecApp (.var 2) (.var 0))
          (.pi (NativeVectorAll.Universes.allType (.var 3) (ResultView.predicate (.var 2))
            (.var 1) (.var 0))
            (upperVec (.var 3) (.var 2))))))

def submitted := FormationSensitiveElaboration.elaborate rules decoder choices 256 .nil program programType


open Mettapedia.TypeTheory.UniverseLevel
open RussellTarski
def resultLevelInstance (theta : Nat → LevelExpr Nat) : LevelInstance signature theta where
  computation := signature.computation
  computationMap := by
    intro n left right step
    change iotaComputation.step left right ∨
      iotaComputation.step (left.mapConst names.symm) (right.mapConst names.symm) at step
    change iotaComputation.step (substLevelsTm theta left) (substLevelsTm theta right) ∨
      iotaComputation.step ((substLevelsTm theta left).mapConst names.symm)
        ((substLevelsTm theta right).mapConst names.symm)
    rcases step with first | second
    · obtain ⟨evidence⟩ := first
      exact Or.inl ⟨NativeNaturalVectorFamilies.Programs.mapIota (substLevelsHead theta) evidence⟩
    · obtain ⟨evidence⟩ := second
      apply Or.inr
      have mapped := NativeNaturalVectorFamilies.Programs.mapIota (substLevelsHead theta) evidence
      simp only [substLevelsTm, Tm.mapConst_mapHead]
      exact ⟨mapped⟩

theorem result_signature_level_formed (theta : Nat → LevelExpr Nat) :
    (resultLevelInstance theta).signature.Formed Tower.rules :=
  (resultLevelInstance theta).formed signature_formed

def closedLevels (parameter : Nat) : LevelExpr Nat :=
  if parameter = 2 then .succ Tower.zero else Tower.zero


/-! ## Computation with the original input representation

Only the destination constructor prefix changes. The actual result-type and
witness arguments are retained, including names belonging to the input profile.
-/

namespace Computation

open Mettapedia.TypeTheory.IndexedContainer
open NativeVectorAll.CanonicalAdequacy
open NativeVectorAll.ResultView.EvidenceElimination


open NativeVectorAll.ResultView.OriginalInputUniverses

def resultNil {n : Nat} (result : Tower.Tm n) : Tower.Tm n :=
  .app (.const `CumulativeTower.VecUpper.nil) result

def resultCons {n : Nat} (result : Tower.Tm n) : Tower.Tm n :=
  .app (.const `CumulativeTower.VecUpper.cons) result

theorem nil_beta (R : Rules Tower.Head) {n : Nat} (result bundle : Tower.Tm n) :
    TypedEquality.Reduces R (.app (nilCase result) bundle) (resultNil result) := by
  change TypedEquality.Reduces R
    (.app (.lam (rename wk (resultNil result))) bundle) (resultNil result)
  have beta := Relation.ReflTransGen.single
    (StepCore.betaPi (root := R.computation) (headEq := R.headEq)
      (rename wk (resultNil result)) bundle)
  have unchanged : inst0 bundle (rename wk (resultNil result)) = resultNil result := by
    unfold inst0
    rw [subst_rename]
    change subst ids (resultNil result) = resultNil result
    exact subst_ids _
  simpa only [unchanged] using beta

theorem cons_beta (R : Rules Tower.Head) {n : Nat}
    (result length head tail recursive bundle : Tower.Tm n) :
    TypedEquality.Reduces R
      (appSpine (consCase result) [length, head, tail, recursive, bundle])
      (appSpine (resultCons result) [length, .fst bundle, .app recursive (.snd bundle)]) := by
  let body : Tower.Tm (n + 5) :=
    appSpine (.const `CumulativeTower.VecUpper.cons)
      [rename wk (NativeVectorAll.weaken4 result), .var 4, .fst (.var 0),
        .app (.var 1) (.snd (.var 0))]
  let sigma : Sub Tower.Head (n + 5) n :=
    consSub bundle (consSub recursive (consSub tail (consSub head (consSub length ids))))
  have beta := lams_beta (R := R) 5 body [length, head, tail, recursive, bundle] rfl
  have assignment : extendSub ids
      (fun j => [length, head, tail, recursive, bundle].getD j defaultTm) 5 = sigma := rfl
  rw [assignment] at beta
  have retained : subst sigma (rename wk (NativeVectorAll.weaken4 result)) = result := by
    unfold NativeVectorAll.weaken4
    rw [subst_rename, subst_rename]
    change subst ids result = result
    exact subst_ids _
  have target : subst sigma body =
      appSpine (resultCons result) [length, .fst bundle, .app recursive (.snd bundle)] := by
    change appSpine (.const `CumulativeTower.VecUpper.cons)
      [subst sigma (rename wk (NativeVectorAll.weaken4 result)), length,
        .fst bundle, .app recursive (.snd bundle)] = _
    rw [retained]
    rfl
  rw [target] at beta
  exact beta

def encodeResults {n : Nat} (result : Tower.Tm n) (values : List (Tower.Tm n)) : Tower.Tm n :=
  encode (resultNil result) (resultCons result) values

theorem project_reads {n : Nat} (element result : Tower.Tm n)
    (values : List (Tower.Tm n)) (bundle : Tower.Tm n) :
    TypedEquality.Reduces NativeVectorAll.ResultView.OriginalInputUniverses.rules
      (project element result (numeral values.length) (encodeVector element values) bundle)
      (encodeResults result (PairSpine.reads values.length bundle)) :=
  fold_reads NativeVectorAll.ResultView.OriginalInputUniverses.rules
    (fun evidence => RootStep.declared (Or.inl ⟨evidence⟩))
    element (motive element result) (nilCase result) (consCase result)
    (resultNil result) (resultCons result)
    (nil_beta NativeVectorAll.ResultView.OriginalInputUniverses.rules result)
    (cons_beta NativeVectorAll.ResultView.OriginalInputUniverses.rules result) values bundle

theorem project_witnesses {n : Nat} (element result : Tower.Tm n)
    (values witnesses : List (Tower.Tm n)) (last : Tower.Tm n)
    (lengths : values.length = witnesses.length) :
    TypedEquality.Reduces NativeVectorAll.ResultView.OriginalInputUniverses.rules
      (project element result (numeral values.length) (encodeVector element values)
        (PairSpine.assemble witnesses last)) (encodeResults result witnesses) := by
  refine (project_reads element result values (PairSpine.assemble witnesses last)).trans ?_
  unfold encodeResults
  rw [lengths]
  exact encode_reduces NativeVectorAll.ResultView.OriginalInputUniverses.rules _ _
    (PairSpine.reads_of_reduces_to_assemble
      NativeVectorAll.ResultView.OriginalInputUniverses.rules witnesses last
      (PairSpine.assemble witnesses last) .refl)

theorem subst_motive {n m : Nat} (sigma : Sub Tower.Head n m)
    (element result : Tower.Tm n) :
    subst sigma (motive element result) = motive (subst sigma element) (subst sigma result) := by
  simp [motive, subst, NativeVectorAll.Universes.substitute_allType,
    NativeVectorAll.ResultView.subst_predicate, upperVec]
  rfl

theorem subst_consCase {n m : Nat} (sigma : Sub Tower.Head n m) (result : Tower.Tm n) :
    subst sigma (consCase result) = consCase (subst sigma result) := by
  simp [consCase, subst]
  rfl

theorem subst_project {n m : Nat} (sigma : Sub Tower.Head n m)
    (element result length vector bundle : Tower.Tm n) :
    subst sigma (project element result length vector bundle) =
      project (subst sigma element) (subst sigma result) (subst sigma length)
        (subst sigma vector) (subst sigma bundle) := by
  simp [project, nilCase, vecEliminateApp, subst, subst_motive, subst_consCase]

theorem program_beta (R : Rules Tower.Head) {n : Nat}
    (element result length vector bundle : Tower.Tm n) :
    TypedEquality.Reduces R
      (appSpine (liftClosed program) [element, result, length, vector, bundle])
      (project element result length vector bundle) := by
  let body : Tower.Tm (n + 5) := project (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)
  let sigma : Sub Tower.Head (n + 5) n :=
    consSub bundle (consSub vector (consSub length (consSub result (consSub element ids))))
  have beta := lams_beta (R := R) 5 body [element, result, length, vector, bundle] rfl
  have assignment : extendSub ids
      (fun j => [element, result, length, vector, bundle].getD j defaultTm) 5 = sigma := rfl
  rw [assignment] at beta
  have target : subst sigma body = project element result length vector bundle := by
    rw [show body = project (.var 4) (.var 3) (.var 2) (.var 1) (.var 0) from rfl, subst_project]
    rfl
  rw [target] at beta
  exact beta

theorem program_witnesses {n : Nat} (element result : Tower.Tm n)
    (values witnesses : List (Tower.Tm n)) (last : Tower.Tm n)
    (lengths : values.length = witnesses.length) :
    TypedEquality.Reduces NativeVectorAll.ResultView.OriginalInputUniverses.rules
      (appSpine (liftClosed program)
        [element, result, numeral values.length, encodeVector element values,
          PairSpine.assemble witnesses last]) (encodeResults result witnesses) :=
  (program_beta NativeVectorAll.ResultView.OriginalInputUniverses.rules element result
    (numeral values.length) (encodeVector element values)
    (PairSpine.assemble witnesses last)).trans
      (project_witnesses element result values witnesses last lengths)

universe uWitness

theorem registered_bundle_steps {n : Nat} (element result : Tower.Tm n)
    {P : Tower.Tm n → Type uWitness} (read : ∀ value, P value → Tower.Tm n)
    (values : List (Tower.Tm n))
    (bundle : (vectorInductionBundle P).Bundle (semanticValue values)) :
    let witnesses := List.ofFn fun position : Fin values.length =>
      read (values.get position) ((vectorInductionBundle P).exact (semanticValue values) bundle position)
    TypedEquality.Reduces NativeVectorAll.ResultView.OriginalInputUniverses.rules
      (appSpine (liftClosed program)
        [element, result, numeral values.length, encodeVector element values,
          quoteWitnesses witnesses]) (encodeResults result witnesses) := by
  dsimp only
  apply program_witnesses
  exact List.length_ofFn.symm

/-! The generic registered-code result view specializes to the same witness
sequence consumed by this original-input Vector program. The semantic bundle
qualification retains its existing Type-valued motive fragment. -/
namespace RegisteredResults

open Mettapedia.TypeTheory.IndexedPositiveContainer

def children {n : Nat} (values : List (Tower.Tm n))
    (position : Code.Position VectorControl.code (VectorControl.shapeAt values.length)) : Tower.Tm n :=
  values.get (VectorControl.positionEquiv values.length position)

noncomputable def bundle {n : Nat} {P : Tower.Tm n → Type} (values : List (Tower.Tm n))
    (evidence : (vectorInductionBundle P).Bundle (semanticValue values)) :
    Code.Bundle VectorControl.inductionQualified (fun _ => P) VectorControl.code
      (VectorControl.shapeAt values.length) (children values) :=
  ⟨evidence, PUnit.unit⟩

theorem witness_at {n : Nat} {P : Tower.Tm n → Type} (values : List (Tower.Tm n))
    (evidence : (vectorInductionBundle P).Bundle (semanticValue values)) (position : Fin values.length) :
    Code.bundleExact VectorControl.inductionQualified (fun _ => P) VectorControl.code
        (VectorControl.shapeAt values.length) (children values) (bundle values evidence)
        ((VectorControl.positionEquiv values.length).symm position) =
      (vectorInductionBundle P).exact (semanticValue values) evidence position := rfl

theorem position_order (length : Nat) :
    Code.orderedPositions VectorControl.orderedFinitary VectorControl.code (VectorControl.shapeAt length) =
      List.ofFn (fun position : Fin length => (VectorControl.positionEquiv length).symm position) := by
  change List.append ((List.ofFn (id : Fin length → Fin length)).map
    (Sum.inl : Fin length → Fin length ⊕ PEmpty)) ([] : List (Fin length ⊕ PEmpty)) =
      List.ofFn (fun position : Fin length => (Sum.inl position : Fin length ⊕ PEmpty))
  exact List.append_eq.trans ((List.append_nil _).trans (by
    simp only [List.map_ofFn, Function.comp_def, id_eq]))

theorem readback {n : Nat} {P : Tower.Tm n → Type} {Result : Type}
    (read : ∀ value, P value → Result) (values : List (Tower.Tm n))
    (evidence : (vectorInductionBundle P).Bundle (semanticValue values)) :
    Code.readResults VectorControl.inductionQualified VectorControl.orderedFinitary
        (fun _ => read) (bundle values evidence) =
      List.ofFn (fun position : Fin values.length =>
        read (values.get position) ((vectorInductionBundle P).exact (semanticValue values) evidence position)) := by
  dsimp only [Code.readResults]
  rw [position_order, List.map_ofFn]
  apply congrArg List.ofFn
  funext position
  rfl

/-- The native result program computes the generic registered-code result
view at every constructor-vector length and arbitrary position witnesses. -/
theorem program_steps {n : Nat} (element result : Tower.Tm n)
    {P : Tower.Tm n → Type} (read : ∀ value, P value → Tower.Tm n)
    (values : List (Tower.Tm n))
    (evidence : (vectorInductionBundle P).Bundle (semanticValue values)) :
    let witnesses := Code.readResults VectorControl.inductionQualified VectorControl.orderedFinitary
      (fun _ => read) (bundle values evidence)
    TypedEquality.Reduces NativeVectorAll.ResultView.OriginalInputUniverses.rules
      (appSpine (liftClosed program)
        [element, result, numeral values.length, encodeVector element values,
          quoteWitnesses witnesses]) (encodeResults result witnesses) := by
  dsimp only
  rw [readback]
  exact registered_bundle_steps element result read values evidence

end RegisteredResults

theorem constructor_prefix_renaming_is_distinct :
    encodeResults (n := 0) (vecApp natTm zeroTm) [] ≠
      (encodeVector (vecApp natTm zeroTm) []).mapConst
        NativeVectorAll.ResultView.OriginalInputUniverses.names := by decide +kernel

theorem program_level_witnesses
    (theta : Nat → Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat)
    {n : Nat} (element result : Tower.Tm n)
    (values witnesses : List (Tower.Tm n)) (last : Tower.Tm n)
    (lengths : values.length = witnesses.length) :
    TypedEquality.Reduces (resultLevelInstance theta).rules
      (substLevelsTm theta
        (appSpine (liftClosed program)
          [element, result, numeral values.length, encodeVector element values,
            PairSpine.assemble witnesses last]))
      (substLevelsTm theta (encodeResults result witnesses)) := by
  apply Relation.ReflTransGen.lift (substLevelsTm theta) ?_ _ _
    (program_witnesses element result values witnesses last lengths)
  intro left right step
  exact StepCore.mapHead (substLevelsHead theta)
    (resultLevelInstance theta).morphism.headEq
    (resultLevelInstance theta).morphism.computation step

#print axioms project_reads
#print axioms program_witnesses
#print axioms registered_bundle_steps
#print axioms RegisteredResults.readback
#print axioms RegisteredResults.program_steps
#print axioms constructor_prefix_renaming_is_distinct
#print axioms program_level_witnesses

end Computation

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ResultView.OriginalInputUniverses
