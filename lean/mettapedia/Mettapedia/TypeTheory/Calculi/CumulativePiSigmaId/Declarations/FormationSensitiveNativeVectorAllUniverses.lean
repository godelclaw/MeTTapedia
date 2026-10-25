import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAll
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FormationSensitiveLevelInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation

/-!
# Independent child and predicate universes for native Vector All

A universe-instantiated copy of the existing four-input All program computes
its type in max(alpha,beta), with children in U_alpha and predicates into
U_beta. Only the template's result-universe annotation changes; the child
universe in the native Vector signature stays alpha. The original source
program supplies the template and the existing checker validates the new
open judgment. No pointwise witness function is needed for type formation.

Typed substitution yields formation in every extended signature. The
construction is a profile of the existing native declarations. It adds no
primitive constant, reduction rule or native implementation guarantee.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Universes
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration RussellTarski
open NativeNaturalVectorFamilies

def dataLevel : LevelExpr Nat := .param 0
def predicateLevel : LevelExpr Nat := .param 2
def resultLevel : LevelExpr Nat := .max dataLevel predicateLevel

def levels (parameter : Nat) : LevelExpr Nat :=
  if parameter = 1 then .succ resultLevel else .param parameter

def levelInstance : LevelInstance NativeNaturalVectorFamilies.rawSignature levels where
  computation := NativeNaturalVectorFamilies.iotaComputation
  computationMap step := by
    obtain ⟨evidence⟩ := step
    exact ⟨NativeNaturalVectorFamilies.Programs.mapIota (substLevelsHead levels) evidence⟩

abbrev signature := levelInstance.signature
abbrev rules := levelInstance.rules

def decoder : StructuralConversionCode.RootDecoder rules.computation :=
  DeclarationConversionCode.rootDecoder (base := Tower.rules) (signature := signature)
    (.ofEmpty _ rfl) NativeNaturalVectorFamilies.Checking.iotaDecoder

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

/-- The existing four-input program has only its result-universe annotation instantiated. -/
def subject : Tower.Tm 4 := substLevelsTm (fun _ => resultLevel) NativeVectorAll.TypeFormation.subject

def contextA : Tower.Ctx 1 := .snoc .nil (sortTm dataLevel)
def contextAP : Tower.Ctx 2 := .snoc contextA (.pi (.var 0) (sortTm predicateLevel))
def contextAPN : Tower.Ctx 3 := .snoc contextAP natTm
def context : Tower.Ctx 4 := .snoc contextAPN (vecApp (.var 2) (.var 0))

def choices : FormationSensitiveElaboration.Choices Tower.Head decoder.Code := NativeVectorAll.choices

def accepted := (FormationSensitiveElaboration.elaborate rules decoder choices 128
  context subject (sortTm resultLevel)).isSome

theorem accepted_eq_true : accepted = true := by decide +kernel

theorem formed : FormationSensitive.Judgment rules context subject (sortTm resultLevel) := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp accepted_eq_true
  exact FormationSensitiveElaboration.elaborate_sound rules decoder choices 128 context subject
    (sortTm resultLevel) submission produced

/-- Substitute the four authored inputs into the universe-instantiated source program. -/
def arguments {n : Nat} (element predicate length vector : Tower.Tm n) : Sub Tower.Head 4 n :=
  consSub vector (consSub length (consSub predicate (consSub element Fin.elim0)))

def allType {n : Nat} (element predicate length vector : Tower.Tm n) : Tower.Tm n :=
  subst (arguments element predicate length vector) subject

theorem inputs_typed (extension : Signature Tower.Head) {n : Nat} {ambient : Tower.Ctx n}
    {element predicate length vector : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient element (sortTm dataLevel))
    (predicateTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient predicate (.pi element (sortTm predicateLevel)))
    (lengthTyped : FormationSensitive.Typing (extendRules rules extension) ambient length natTm)
    (vectorTyped : FormationSensitive.Typing (extendRules rules extension) ambient vector (vecApp element length)) :
    FormationSensitive.CtxMor (extendRules rules extension) context ambient
      (arguments element predicate length vector) := by
  intro index
  fin_cases index
  · exact vectorTyped
  · exact lengthTyped
  · exact predicateTyped
  · exact elementTyped

theorem allType_typed (extension : Signature Tower.Head) {n : Nat} {ambient : Tower.Ctx n}
    {element predicate length vector : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient element (sortTm dataLevel))
    (predicateTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient predicate (.pi element (sortTm predicateLevel)))
    (lengthTyped : FormationSensitive.Typing (extendRules rules extension) ambient length natTm)
    (vectorTyped : FormationSensitive.Typing (extendRules rules extension) ambient vector (vecApp element length)) :
    FormationSensitive.Typing (extendRules rules extension) ambient
      (allType element predicate length vector) (sortTm resultLevel) :=
  (formed.typing.includeSignature extension).substitute
    (inputs_typed extension elementTyped predicateTyped lengthTyped vectorTyped)

theorem substitute_allType {n m : Nat} (sigma : Sub Tower.Head n m)
    (element predicate length vector : Tower.Tm n) :
    subst sigma (allType element predicate length vector) =
      allType (subst sigma element) (subst sigma predicate)
        (subst sigma length) (subst sigma vector) := by
  unfold allType
  rw [subst_comp]
  apply subst_ext
  intro index
  fin_cases index <;> rfl

def insufficientBoundAccepted := (FormationSensitiveElaboration.elaborate rules decoder choices 128
  context subject (sortTm dataLevel)).isSome

theorem insufficient_bound_refused : insufficientBoundAccepted = false := by decide +kernel

def malformedPredicateAccepted := (FormationSensitiveElaboration.elaborate rules decoder choices 128
  context (allType (.var 3) natTm (.var 1) (.var 0)) (sortTm resultLevel)).isSome

theorem malformed_predicate_refused : malformedPredicateAccepted = false := by decide +kernel

def verdicts : List (String × Bool) :=
  [("Vector All forms with independent child and predicate universes", accepted),
   ("Vector All refuses a result bound below the predicate universe", !insufficientBoundAccepted),
   ("Vector All refuses a natural type in place of its predicate", !malformedPredicateAccepted)]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp only [verdicts, accepted_eq_true, insufficient_bound_refused, malformed_predicate_refused,
    Bool.not_false, List.all_cons, List.all_nil, Bool.and_self]

#print axioms insufficient_bound_refused
#print axioms malformed_predicate_refused

#print axioms allType_typed
#print axioms substitute_allType

#print axioms accepted_eq_true
#print axioms formed
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Universes

/-! ## Canonical constructor-vector computation

The same source program at any raw universe annotation reaches the quoted
dependent-pair type spine on every constructor vector. Input elements and
predicate applications remain in their source order. This spine can contain
reducible predicate applications. The result is a canonical-input computation
law, with arbitrary neutral-term typed lift coherence still separate.
-/

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Universes.Canonical
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration RussellTarski TypedEquality.Normalization
open NativeNaturalVectorFamilies
open NativeVectorAll.CanonicalAdequacy

def typeProgramAtUniverse (level : LevelExpr Nat) : Tower.Tm 4 :=
  substLevelsTm (fun _ => level) NativeVectorAll.TypeFormation.subject

def allTypeAtUniverse {n : Nat} (level : LevelExpr Nat) (element predicate length vector : Tower.Tm n) : Tower.Tm n :=
  subst (Universes.arguments element predicate length vector) (typeProgramAtUniverse level)

theorem allTypeAtUniverse_eq_eliminate {n : Nat} (level : LevelExpr Nat)
    (element predicate length vector : Tower.Tm n) :
    allTypeAtUniverse level element predicate length vector =
      vecEliminateApp element (.lam (.lam (sortTm level))) unitType
        (allTypeConsCase predicate) length vector := by
  simp only [allTypeAtUniverse, typeProgramAtUniverse, TypeFormation.subject, NativeVectorAll.allType, allUniverseMotive,
    allTypeConsCase, weaken4, vecEliminateApp, unitType, natTm, zeroTm, sortTm,
    substLevelsTm, substLevelsHead, LevelExpr.subst, NativeVectorAll.motiveLevel, Universes.arguments, consSub,
    Tm.mapHead, subst, liftSub, rename, Fin.cases_zero, Fin.cases_succ]
  dsimp only [Fin.cases]
  congr 1
  rw [rename_comp, rename_comp, rename_comp]
  rfl

abbrev Steps {n : Nat} (left right : Tower.Tm n) : Prop :=
  Relation.ReflTransGen (StepCore Universes.rules.computation Universes.rules.headEq) left right

theorem consType_steps (R : Rules Tower.Head) {n : Nat}
    (predicate length head tail recursive : Tower.Tm n) :
    TypedEquality.Reduces R (.app (.app (.app (.app (allTypeConsCase predicate) length) head) tail) recursive)
      (.sigma (.app predicate head) (rename wk recursive)) := by
  refine Relation.ReflTransGen.head (.congAppFun (.congAppFun (.congAppFun (.betaPi _ _)))) ?_
  refine Relation.ReflTransGen.head (.congAppFun (.congAppFun (.betaPi _ _))) ?_
  refine Relation.ReflTransGen.head (.congAppFun (.betaPi _ _)) ?_
  convert Relation.ReflTransGen.single
    (StepCore.betaPi (root := R.computation) (headEq := R.headEq) _ _) using 1
  all_goals first | rfl | (
    simp only [weaken4, inst0, subst, subst_comp, subst_rename]
    congr 1
    · congr 1
      · symm
        trans subst ids predicate
        · apply subst_ext
          intro index
          rfl
        · exact subst_ids predicate
      · have index : (2 : Fin (n + 4)) = (0 : Fin (n + 2)).succ.succ := by
          apply Fin.ext
          change 2 % (n + 4) = 2
          exact Nat.mod_eq_of_lt (by omega)
        rw [index, ← subst_comp, ← subst_comp]
        have heldSlot : (liftSub (liftSub (liftSub (subst0 length))))
            (0 : Fin (n + 2)).succ.succ =
            (.var (0 : Fin (n + 1)).succ.succ : Tower.Tm (n + 3)) := by
          simp only [liftSub, Fin.cases_succ, Fin.cases_zero, rename, wk]
        rw [heldSlot]
        have selected : (liftSub (liftSub (subst0 head)))
            (0 : Fin (n + 1)).succ.succ = rename wk (rename wk head) := by
          simp only [liftSub, subst0, Fin.cases_succ, Fin.cases_zero]
        change head = subst (subst0 recursive)
          (subst (liftSub (subst0 tail)) ((liftSub (liftSub (subst0 head)))
            (0 : Fin (n + 1)).succ.succ))
        rw [selected]
        rw [subst_liftSub_wk]
        change head = inst0 recursive (rename wk (inst0 tail (rename wk head)))
        rw [inst0_rename_wk, inst0_rename_wk]
        )

def quoteAllType {n : Nat} (predicate : Tower.Tm n) : List (Tower.Tm n) → Tower.Tm n
  | [] => unitType
  | head :: tail => .sigma (.app predicate head) (rename wk (quoteAllType predicate tail))

private theorem steps_sigma_cod {n : Nat} (first : Tower.Tm n)
    {left right : Tower.Tm n} (steps : Steps left right) :
    Steps (.sigma first (rename wk left)) (.sigma first (rename wk right)) := by
  induction steps with
  | refl => exact .refl
  | tail prior step ih => exact .tail ih (.congSigmaCod (StepCore.renameTerms step wk))

theorem allTypeAtUniverse_steps {n : Nat} (level : LevelExpr Nat) (element predicate : Tower.Tm n) :
    ∀ values : List (Tower.Tm n),
      Steps (allTypeAtUniverse level element predicate (numeral values.length) (encodeVector element values))
        (quoteAllType predicate values)
  | [] => by
      rw [allTypeAtUniverse_eq_eliminate]
      apply Relation.ReflTransGen.single
      apply StepCore.root
      exact RootStep.declared ⟨NativeNaturalVectorFamilies.IotaEvidence.vecNil
        element (.lam (.lam (sortTm level))) unitType (allTypeConsCase predicate)⟩
  | head :: tail => by
      rw [allTypeAtUniverse_eq_eliminate]
      apply Relation.ReflTransGen.head
      · apply StepCore.root
        exact RootStep.declared ⟨NativeNaturalVectorFamilies.IotaEvidence.vecCons
          element (.lam (.lam (sortTm level))) unitType (allTypeConsCase predicate)
          (numeral tail.length) head (encodeVector element tail)⟩
      · have branch := consType_steps Universes.rules predicate (numeral tail.length) head (encodeVector element tail)
          (allTypeAtUniverse level element predicate (numeral tail.length) (encodeVector element tail))
        rw [allTypeAtUniverse_eq_eliminate] at branch
        have recursiveSteps := allTypeAtUniverse_steps level element predicate tail
        rw [allTypeAtUniverse_eq_eliminate] at recursiveSteps
        exact branch.trans (steps_sigma_cod (.app predicate head) recursiveSteps)

theorem universe_annotation_common_result {n : Nat}
    (first second : LevelExpr Nat) (element predicate : Tower.Tm n) (values : List (Tower.Tm n)) :
    ∃ result, Steps (allTypeAtUniverse first element predicate (numeral values.length) (encodeVector element values)) result ∧
      Steps (allTypeAtUniverse second element predicate (numeral values.length) (encodeVector element values)) result :=
  ⟨quoteAllType predicate values, allTypeAtUniverse_steps first element predicate values,
    allTypeAtUniverse_steps second element predicate values⟩

/-- The checked universe profile is the selected instance of the same source program. -/
theorem allType_steps {n : Nat} (element predicate : Tower.Tm n) (values : List (Tower.Tm n)) :
    Steps (Universes.allType element predicate (numeral values.length) (encodeVector element values))
      (quoteAllType predicate values) :=
  allTypeAtUniverse_steps Universes.resultLevel element predicate values

/-- The actual native two-element vector supplies a closed, nonconstant predicate instance. -/
theorem two_positions_reduce :
    Steps (Universes.allType (natTm : Tower.Tm 0)
      (.lam (.id natTm (.var 0) (.var 0))) (numeral 2)
      (encodeVector natTm [zeroTm, succApp zeroTm]))
      (quoteAllType (.lam (.id natTm (.var 0) (.var 0))) [zeroTm, succApp zeroTm]) :=
  allType_steps natTm (.lam (.id natTm (.var 0) (.var 0))) [zeroTm, succApp zeroTm]

/-- Two raw annotations retain the same concrete source positions and predicate. -/
theorem two_raw_annotations_share_result :
    ∃ result : Tower.Tm 0,
      Steps (allTypeAtUniverse Universes.resultLevel natTm
        (.lam (.id natTm (.var 0) (.var 0))) (numeral 2)
        (encodeVector natTm [zeroTm, succApp zeroTm])) result ∧
      Steps (allTypeAtUniverse (.succ Universes.resultLevel) natTm
        (.lam (.id natTm (.var 0) (.var 0))) (numeral 2)
        (encodeVector natTm [zeroTm, succApp zeroTm])) result :=
  universe_annotation_common_result _ _ natTm
    (.lam (.id natTm (.var 0) (.var 0))) [zeroTm, succApp zeroTm]

/-- The quoted spine retains two original positions and differs from a one-position spine. -/
theorem two_positions_not_one :
    quoteAllType (.lam (.id (natTm : Tower.Tm 1) (.var 0) (.var 0))) [zeroTm, succApp zeroTm] ≠
      quoteAllType (.lam (.id (natTm : Tower.Tm 1) (.var 0) (.var 0))) [zeroTm] := by
  decide +kernel

/-- Quoted predicate applications may still reduce; the spine is not a full normal-form claim. -/
theorem quoted_predicate_can_reduce :
    ∃ next : Tower.Tm 0, StepCore Universes.rules.computation Universes.rules.headEq
      (quoteAllType (.lam (.id natTm (.var 0) (.var 0))) [zeroTm]) next := by
  exact ⟨_, .congSigmaDom (.betaPi _ _)⟩

#print axioms allType_steps
#print axioms two_positions_reduce
#print axioms two_raw_annotations_share_result
#print axioms two_positions_not_one
#print axioms quoted_predicate_can_reduce

#print axioms universe_annotation_common_result
#print axioms allTypeAtUniverse_steps

#print axioms consType_steps

#print axioms allTypeAtUniverse_eq_eliminate

/-- Term substitution preserves the four authored inputs at every result annotation. -/
theorem substitute_allTypeAtUniverse {n m : Nat} (sigma : Sub Tower.Head n m)
    (level : LevelExpr Nat) (element predicate length vector : Tower.Tm n) :
    subst sigma (allTypeAtUniverse level element predicate length vector) =
      allTypeAtUniverse level (subst sigma element) (subst sigma predicate)
        (subst sigma length) (subst sigma vector) := by
  unfold allTypeAtUniverse
  rw [subst_comp]
  apply subst_ext
  intro index
  fin_cases index <;> rfl

/-- Universe instantiation changes both the program annotation and its actual inputs. -/
theorem substLevels_allTypeAtUniverse {n : Nat} (theta : Nat → LevelExpr Nat)
    (level : LevelExpr Nat) (element predicate length vector : Tower.Tm n) :
    substLevelsTm theta (allTypeAtUniverse level element predicate length vector) =
      allTypeAtUniverse (LevelExpr.subst theta level)
        (substLevelsTm theta element) (substLevelsTm theta predicate)
        (substLevelsTm theta length) (substLevelsTm theta vector) := by
  rw [allTypeAtUniverse_eq_eliminate, allTypeAtUniverse_eq_eliminate]
  simp only [vecEliminateApp, allTypeConsCase, weaken4, unitType, natTm, zeroTm, sortTm,
    substLevelsTm, Tm.mapHead, Tm.mapHead_rename, substLevelsHead]

/-- The concrete All program commutes with level instantiation and capture-avoiding substitution. -/
theorem instantiation_substitution_square {n m : Nat} (theta : Nat → LevelExpr Nat)
    (sigma : Sub Tower.Head n m) (level : LevelExpr Nat)
    (element predicate length vector : Tower.Tm n) :
    substLevelsTm theta (subst sigma (allTypeAtUniverse level element predicate length vector)) =
      allTypeAtUniverse (LevelExpr.subst theta level)
        (subst (fun i => substLevelsTm theta (sigma i)) (substLevelsTm theta element))
        (subst (fun i => substLevelsTm theta (sigma i)) (substLevelsTm theta predicate))
        (subst (fun i => substLevelsTm theta (sigma i)) (substLevelsTm theta length))
        (subst (fun i => substLevelsTm theta (sigma i)) (substLevelsTm theta vector)) := by
  rw [substitute_allTypeAtUniverse, substLevels_allTypeAtUniverse]
  simp only [substLevelsTm, Tm.mapHead_subst]

#print axioms substitute_allTypeAtUniverse
#print axioms substLevels_allTypeAtUniverse
#print axioms instantiation_substitution_square
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Universes.Canonical


/-! ## Cumulative elimination in one shared profile

The native eliminator's result bound is enlarged while its element and
predicate universes stay fixed. The original and enlarged All annotations
both form in this profile, including on a neutral vector. On constructor
vectors their common quoted computation yields conversion and transport of
every inhabitant without changing its term. Arbitrary level instantiation
also transports the formed open judgments; extensions supply their own
computation map and preserve exact declaration lookup.

Neither syntactic inequality of the open programs nor source-checker refusal
is presented as a non-derivability result. Equality of the two All types at
an arbitrary neutral vector remains a separate obligation.
-/

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Universes.CumulativeElimination
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration RussellTarski
open NativeNaturalVectorFamilies

def upperLevel : LevelExpr Nat := .max resultLevel (.param 3)

def levels (parameter : Nat) : LevelExpr Nat :=
  if parameter = 1 then .succ upperLevel else .param parameter

def levelInstance : LevelInstance NativeNaturalVectorFamilies.rawSignature levels where
  computation := NativeNaturalVectorFamilies.iotaComputation
  computationMap step := by
    obtain ⟨evidence⟩ := step
    exact ⟨NativeNaturalVectorFamilies.Programs.mapIota (substLevelsHead levels) evidence⟩

abbrev signature := levelInstance.signature
abbrev rules := levelInstance.rules

def decoder : StructuralConversionCode.RootDecoder rules.computation :=
  DeclarationConversionCode.rootDecoder (base := Tower.rules) (signature := signature)
    (.ofEmpty _ rfl) NativeNaturalVectorFamilies.Checking.iotaDecoder

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

def choices : FormationSensitiveElaboration.Choices Tower.Head decoder.Code := NativeVectorAll.choices

def lowerAccepted := (FormationSensitiveElaboration.elaborate rules decoder choices 128
  Universes.context Universes.subject (sortTm resultLevel)).isSome

def upperAccepted := (FormationSensitiveElaboration.elaborate rules decoder choices 128
  Universes.context (Canonical.typeProgramAtUniverse upperLevel) (sortTm upperLevel)).isSome

theorem lower_accepted : lowerAccepted = true := by decide +kernel
theorem upper_accepted : upperAccepted = true := by decide +kernel

theorem lower_formed : FormationSensitive.Judgment rules Universes.context
    Universes.subject (sortTm resultLevel) := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp lower_accepted
  exact FormationSensitiveElaboration.elaborate_sound rules decoder choices 128 _ _ _ submission produced

theorem upper_formed : FormationSensitive.Judgment rules Universes.context
    (Canonical.typeProgramAtUniverse upperLevel) (sortTm upperLevel) := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp upper_accepted
  exact FormationSensitiveElaboration.elaborate_sound rules decoder choices 128 _ _ _ submission produced

theorem lower_le_upper : rules.cumulative (.sort resultLevel) (.sort upperLevel) := by
  intro valuation
  exact Nat.le_max_left _ _

theorem inputs_typed (extension : Signature Tower.Head) {n : Nat} {ambient : Tower.Ctx n}
    {element predicate length vector : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient element (sortTm dataLevel))
    (predicateTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient predicate (.pi element (sortTm predicateLevel)))
    (lengthTyped : FormationSensitive.Typing (extendRules rules extension) ambient length natTm)
    (vectorTyped : FormationSensitive.Typing (extendRules rules extension) ambient vector (vecApp element length)) :
    FormationSensitive.CtxMor (extendRules rules extension) Universes.context ambient
      (Universes.arguments element predicate length vector) := by
  intro index
  fin_cases index
  · exact vectorTyped
  · exact lengthTyped
  · exact predicateTyped
  · exact elementTyped

/-- Both source annotations form at one common bound, including on neutral inputs. -/
theorem both_typed (extension : Signature Tower.Head) {n : Nat} {ambient : Tower.Ctx n}
    {element predicate length vector : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient element (sortTm dataLevel))
    (predicateTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient predicate (.pi element (sortTm predicateLevel)))
    (lengthTyped : FormationSensitive.Typing (extendRules rules extension) ambient length natTm)
    (vectorTyped : FormationSensitive.Typing (extendRules rules extension) ambient vector (vecApp element length)) :
    FormationSensitive.Typing (extendRules rules extension) ambient
      (Canonical.allTypeAtUniverse resultLevel element predicate length vector) (sortTm upperLevel) ∧
    FormationSensitive.Typing (extendRules rules extension) ambient
      (Canonical.allTypeAtUniverse upperLevel element predicate length vector) (sortTm upperLevel) := by
  have inputs := inputs_typed extension elementTyped predicateTyped lengthTyped vectorTyped
  exact ⟨.cumul ((lower_formed.typing.includeSignature extension).substitute inputs) lower_le_upper,
    (upper_formed.typing.includeSignature extension).substitute inputs⟩

def upperBelowAccepted := (FormationSensitiveElaboration.elaborate rules decoder choices 128
  Universes.context (Canonical.typeProgramAtUniverse upperLevel) (sortTm resultLevel)).isSome

theorem upper_below_refused : upperBelowAccepted = false := by decide +kernel

private theorem root_transport {n : Nat} {left right : Tower.Tm n}
    (step : Universes.rules.computation.step left right) : rules.computation.step left right := by
  cases step with
  | inherited impossible => exact impossible.elim
  | @delta name value known =>
      change Universes.signature.valueOf? name = some value at known
      simp [Universes.signature, LevelInstance.signature] at known
  | declared evidence => exact .declared evidence

theorem step_transport (extension : Signature Tower.Head) {n : Nat} {left right : Tower.Tm n}
    (step : StepCore Universes.rules.computation Universes.rules.headEq left right) :
    StepCore (extendRules rules extension).computation rules.headEq left right := by
  have mapped := step.mapHead (targetRoot := (extendRules rules extension).computation)
    (targetEq := rules.headEq) (fun head : Tower.Head => head) (fun same => same)
    (fun prior => by
      simp only [Tm.mapHead_id]
      exact RootStep.inherited (base := rules) (signature := extension) (root_transport prior))
  simpa only [Tm.mapHead_id] using mapped

theorem steps_transport (extension : Signature Tower.Head) {n : Nat} {left right : Tower.Tm n}
    (steps : Canonical.Steps left right) :
    Relation.ReflTransGen (StepCore (extendRules rules extension).computation rules.headEq) left right := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (step_transport extension step)

theorem canonical_conversion (extension : Signature Tower.Head) {n : Nat}
    (element predicate : Tower.Tm n) (values : List (Tower.Tm n)) :
    Conv rules.headEq
      (Canonical.allTypeAtUniverse resultLevel element predicate
        (NativeVectorAll.CanonicalAdequacy.numeral values.length)
        (NativeVectorAll.CanonicalAdequacy.encodeVector element values))
      (Canonical.allTypeAtUniverse upperLevel element predicate
        (NativeVectorAll.CanonicalAdequacy.numeral values.length)
        (NativeVectorAll.CanonicalAdequacy.encodeVector element values)) (extendRules rules extension).computation := by
  have lower := steps_transport extension (Canonical.allTypeAtUniverse_steps resultLevel element predicate values)
  have upper := steps_transport extension (Canonical.allTypeAtUniverse_steps upperLevel element predicate values)
  have toConv {left right : Tower.Tm n}
      (steps : Relation.ReflTransGen (StepCore (extendRules rules extension).computation rules.headEq) left right) :
      Conv rules.headEq left right (extendRules rules extension).computation := by
    induction steps with
    | refl => exact .refl _
    | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ step)
  exact .trans _ _ _ (toConv lower) (.symm _ _ (toConv upper))

/-- On constructor vectors, changing the result annotation preserves every inhabitant judgment. -/
theorem canonical_typing_iff (extension : Signature Tower.Head) {n : Nat} {ambient : Tower.Ctx n}
    {element predicate term : Tower.Tm n} (values : List (Tower.Tm n))
    (elementTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient element (sortTm dataLevel))
    (predicateTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient predicate (.pi element (sortTm predicateLevel)))
    (lengthTyped : FormationSensitive.Typing (extendRules rules extension) ambient
      (NativeVectorAll.CanonicalAdequacy.numeral values.length) natTm)
    (vectorTyped : FormationSensitive.Typing (extendRules rules extension) ambient
      (NativeVectorAll.CanonicalAdequacy.encodeVector element values)
      (vecApp element (NativeVectorAll.CanonicalAdequacy.numeral values.length))) :
    FormationSensitive.Typing (extendRules rules extension) ambient term
      (Canonical.allTypeAtUniverse resultLevel element predicate
        (NativeVectorAll.CanonicalAdequacy.numeral values.length)
        (NativeVectorAll.CanonicalAdequacy.encodeVector element values)) ↔
    FormationSensitive.Typing (extendRules rules extension) ambient term
      (Canonical.allTypeAtUniverse upperLevel element predicate
        (NativeVectorAll.CanonicalAdequacy.numeral values.length)
        (NativeVectorAll.CanonicalAdequacy.encodeVector element values)) := by
  have both := both_typed extension elementTyped predicateTyped lengthTyped vectorTyped
  have conversion := canonical_conversion extension element predicate values
  constructor
  · intro typed
    exact .conv typed both.2 (.sort upperLevel) conversion
  · intro typed
    exact .conv typed both.1 (.sort upperLevel) (.symm _ _ conversion)

def instantiation (theta : Nat → LevelExpr Nat) : LevelInstance signature theta where
  computation := NativeNaturalVectorFamilies.iotaComputation
  computationMap step := by
    obtain ⟨evidence⟩ := step
    exact ⟨NativeNaturalVectorFamilies.Programs.mapIota (substLevelsHead theta) evidence⟩

theorem instantiated_lookup (theta : Nat → LevelExpr Nat) (name : DeclName) :
    (instantiation theta).rules.constantType name =
      (rules.constantType name).map (substLevelsTm theta) := by
  change (instantiation theta).signature.typeOf? name =
    (signature.typeOf? name).map (substLevelsTm theta)
  exact Signature.typeOf_instantiateLevels theta signature _ name

theorem extended_instantiation (theta : Nat → LevelExpr Nat)
    {extension : Signature Tower.Head} (extensionInstance : LevelInstance extension theta) :
    (extendRules rules extension).Morphism
      (extendRules (instantiation theta).rules extensionInstance.signature) (substLevelsHead theta) :=
  LevelInstance.extendMorphism (instantiation theta).morphism (instantiated_lookup theta) extensionInstance

/-- Explicit signature instantiation preserves both open source formation judgments. -/
theorem instantiated_both_typed (theta : Nat → LevelExpr Nat)
    {extension : Signature Tower.Head} (extensionInstance : LevelInstance extension theta)
    {n : Nat} {ambient : Tower.Ctx n} {element predicate length vector : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient element (sortTm dataLevel))
    (predicateTyped : FormationSensitive.Typing (extendRules rules extension)
      ambient predicate (.pi element (sortTm predicateLevel)))
    (lengthTyped : FormationSensitive.Typing (extendRules rules extension) ambient length natTm)
    (vectorTyped : FormationSensitive.Typing (extendRules rules extension) ambient vector (vecApp element length)) :
    FormationSensitive.Typing (extendRules (instantiation theta).rules extensionInstance.signature)
      (substLevelsCtx theta ambient)
      (Canonical.allTypeAtUniverse (LevelExpr.subst theta resultLevel)
        (substLevelsTm theta element) (substLevelsTm theta predicate)
        (substLevelsTm theta length) (substLevelsTm theta vector))
      (sortTm (LevelExpr.subst theta upperLevel)) ∧
    FormationSensitive.Typing (extendRules (instantiation theta).rules extensionInstance.signature)
      (substLevelsCtx theta ambient)
      (Canonical.allTypeAtUniverse (LevelExpr.subst theta upperLevel)
        (substLevelsTm theta element) (substLevelsTm theta predicate)
        (substLevelsTm theta length) (substLevelsTm theta vector))
      (sortTm (LevelExpr.subst theta upperLevel)) := by
  have both := both_typed extension elementTyped predicateTyped lengthTyped vectorTyped
  have transport := extended_instantiation theta extensionInstance
  constructor
  · have mapped := both.1.mapHead transport
    change FormationSensitive.Typing _ (substLevelsCtx theta ambient)
      (substLevelsTm theta (Canonical.allTypeAtUniverse resultLevel element predicate length vector))
      (sortTm (LevelExpr.subst theta upperLevel)) at mapped
    rw [Canonical.substLevels_allTypeAtUniverse] at mapped
    exact mapped
  · have mapped := both.2.mapHead transport
    change FormationSensitive.Typing _ (substLevelsCtx theta ambient)
      (substLevelsTm theta (Canonical.allTypeAtUniverse upperLevel element predicate length vector))
      (sortTm (LevelExpr.subst theta upperLevel)) at mapped
    rw [Canonical.substLevels_allTypeAtUniverse] at mapped
    exact mapped

def collapseLevels (_ : Nat) : LevelExpr Nat := .const 0

/-- Collapsing level parameters admits this target judgment despite the source checker refusal. -/
theorem collapsed_upper_fits_lower :
    FormationSensitive.Judgment (instantiation collapseLevels).rules
      (substLevelsCtx collapseLevels Universes.context)
      (substLevelsTm collapseLevels (Canonical.typeProgramAtUniverse upperLevel))
      (substLevelsTm collapseLevels (sortTm resultLevel)) := by
  have mapped := (instantiation collapseLevels).refinedJudgment upper_formed
  refine ⟨mapped.context, .conv mapped.typing
    (.headType (.sort (LevelExpr.subst collapseLevels resultLevel)))
    (.sort (.succ (LevelExpr.subst collapseLevels resultLevel))) (.rel _ _ (.head ?_))⟩
  intro valuation
  simp [upperLevel, resultLevel, dataLevel, predicateLevel, collapseLevels, LevelExpr.subst, LevelExpr.eval]

open NativeVectorAll.CanonicalAdequacy

def twoValues : List (Tower.Tm 0) := [zeroTm, succApp zeroTm]
def twoPredicate : Tower.Tm 0 := .lam (.id natTm (.var 0) (.var 0))
def twoEvidence : Tower.Tm 0 := .pair (.refl zeroTm) (.pair (.refl (succApp zeroTm)) unitEvidence)

def checked (term type : Tower.Tm 0) :=
  (FormationSensitiveElaboration.elaborate rules decoder choices 128 .nil term type).isSome

theorem checked_sound {term type : Tower.Tm 0} (accepted : checked term type = true) :
    FormationSensitive.Judgment rules .nil term type := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp accepted
  exact FormationSensitiveElaboration.elaborate_sound rules decoder choices 128 _ _ _ submission produced

theorem two_element_checked : checked natTm (sortTm dataLevel) = true := by decide +kernel
theorem two_predicate_checked : checked twoPredicate (.pi natTm (sortTm predicateLevel)) = true := by decide +kernel
theorem two_length_checked : checked (numeral twoValues.length) natTm = true := by decide +kernel
theorem two_vector_checked : checked (encodeVector natTm twoValues)
    (vecApp natTm (numeral twoValues.length)) = true := by decide +kernel

theorem two_evidence_checked : checked twoEvidence
    (Canonical.allTypeAtUniverse resultLevel natTm twoPredicate
      (numeral twoValues.length) (encodeVector natTm twoValues)) = true := by decide +kernel

theorem two_positions_lift :
    FormationSensitive.Typing (extendRules rules Signature.empty) .nil twoEvidence
      (Canonical.allTypeAtUniverse upperLevel natTm twoPredicate
        (numeral twoValues.length) (encodeVector natTm twoValues)) := by
  apply (canonical_typing_iff Signature.empty twoValues
    ((checked_sound two_element_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_predicate_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_length_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_vector_checked).typing.includeSignature Signature.empty)).mp
  exact (checked_sound two_evidence_checked).typing.includeSignature Signature.empty

def emptyInstantiation (theta : Nat → LevelExpr Nat) : LevelInstance Signature.empty theta where
  computation := RootComputation.empty
  computationMap impossible := impossible.elim

/-- Nonidentity level and term substitutions commute on the actual four-input source. -/
theorem two_program_instantiation_square :
    substLevelsTm collapseLevels
      (subst (Universes.arguments natTm twoPredicate (numeral twoValues.length)
        (encodeVector natTm twoValues)) Universes.subject) =
      Canonical.allTypeAtUniverse (LevelExpr.subst collapseLevels resultLevel)
        (substLevelsTm collapseLevels natTm) (substLevelsTm collapseLevels twoPredicate)
        (substLevelsTm collapseLevels (numeral twoValues.length))
        (substLevelsTm collapseLevels (encodeVector natTm twoValues)) :=
  Canonical.instantiation_substitution_square collapseLevels
    (Universes.arguments natTm twoPredicate (numeral twoValues.length)
      (encodeVector natTm twoValues)) resultLevel (.var 3) (.var 2) (.var 1) (.var 0)

theorem two_positions_instantiated :
    FormationSensitive.Typing
      (extendRules (instantiation collapseLevels).rules (emptyInstantiation collapseLevels).signature)
      (substLevelsCtx collapseLevels (.nil : Tower.Ctx 0))
      (Canonical.allTypeAtUniverse (LevelExpr.subst collapseLevels upperLevel)
        (substLevelsTm collapseLevels natTm) (substLevelsTm collapseLevels twoPredicate)
        (substLevelsTm collapseLevels (numeral twoValues.length))
        (substLevelsTm collapseLevels (encodeVector natTm twoValues)))
      (sortTm (LevelExpr.subst collapseLevels upperLevel)) :=
  (instantiated_both_typed collapseLevels (emptyInstantiation collapseLevels)
    ((checked_sound two_element_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_predicate_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_length_checked).typing.includeSignature Signature.empty)
    ((checked_sound two_vector_checked).typing.includeSignature Signature.empty)).2

/-- The two annotations remain syntactically distinct; this is not a nonconvertibility theorem. -/
theorem neutral_programs_distinct : Universes.subject ≠ Canonical.typeProgramAtUniverse upperLevel := by
  decide +kernel

def verdicts : List (String × Bool) :=
  [("Vector All lower result forms in a shared larger-elimination profile", lowerAccepted),
   ("Vector All upper result forms in the same profile", upperAccepted),
   ("Vector All upper result refuses an insufficient result bound", !upperBelowAccepted),
   ("Vector All concrete two-position evidence checks at the lower result", checked twoEvidence
      (Canonical.allTypeAtUniverse resultLevel natTm twoPredicate
        (numeral twoValues.length) (encodeVector natTm twoValues)))]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp only [verdicts, lower_accepted, upper_accepted, upper_below_refused, two_evidence_checked,
    Bool.not_false, List.all_cons, List.all_nil, Bool.and_self]

#print axioms instantiated_both_typed
#print axioms collapsed_upper_fits_lower

#print axioms both_typed
#print axioms canonical_conversion
#print axioms canonical_typing_iff
#print axioms upper_below_refused
#print axioms two_positions_lift
#print axioms two_positions_instantiated
#print axioms two_program_instantiation_square
#print axioms neutral_programs_distinct

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Universes.CumulativeElimination
