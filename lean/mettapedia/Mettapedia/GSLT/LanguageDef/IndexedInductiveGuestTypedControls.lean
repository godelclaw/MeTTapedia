import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestFormation
import Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaboration

/-!
# Independent typed comparison for generated indexed declarations

The admitted vector telescope generates its constructor, motive, method and
eliminator types over an explicit element-type parameter. The comparison target
is the separately authored cumulative Nat/Vec declaration library. The existing
formation-sensitive checker checks the generated contexts and endpoints.

These controls qualify this vector instance. They do not confer formation or
computation authority on every raw indexed signature.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.TypedControls

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedInductiveNatVec

def lookup {A : Type} {n : Nat} : {context : List Vectors.DataSort} →
    Vectors.LengthVariable context → TermEnv (Vectors.interface A) Tower.Head n context → Tower.Tm n
  | _, .here, environment => environment.1
  | _, .there reference, environment => lookup reference environment.2

theorem lookup_substitute {A : Type} {n m : Nat} (substitution : Sub Tower.Head n m)
    {context : List Vectors.DataSort} (reference : Vectors.LengthVariable context)
    (environment : TermEnv (Vectors.interface A) Tower.Head n context) :
    subst substitution (lookup reference environment) =
      lookup reference (mapEnv (subst substitution) environment) := by
  induction reference with
  | here => rfl
  | there reference ih => exact ih environment.2

/-- Head maps retain the selected source length variable. -/
theorem lookup_mapHead (map : Tower.Head → Tower.Head) {A : Type} {n : Nat}
    {context : List Vectors.DataSort} (reference : Vectors.LengthVariable context)
    (environment : TermEnv (Vectors.interface A) Tower.Head n context) :
    (lookup reference environment).mapHead map =
      lookup reference (mapEnv (Tm.mapHead map) environment) := by
  induction reference with
  | here => rfl
  | there reference ih => exact ih environment.2

/-- Native name interpretation. Addition is deliberately not a declared
operation of the reference library and is not used by its constructor codes. -/
def indexTerm {A : Type} {n : Nat} {context : List Vectors.DataSort} :
    Vectors.IndexExpr context → TermEnv (Vectors.interface A) Tower.Head n context → Tower.Tm n
  | .zero, _ => NativeNaturalVectorFamilies.zeroTm
  | .variable reference, environment => lookup reference environment
  | .successor expression, environment => NativeNaturalVectorFamilies.succApp (indexTerm expression environment)
  | .addition left right, environment =>
      .app (.app (.const `Unadmitted.IndexAdd) (indexTerm left environment))
        (indexTerm right environment)

/-- The source index syntax commutes with head maps, including open variables.
This syntactic law does not admit the deliberately undeclared addition operation. -/
theorem indexTerm_mapHead (map : Tower.Head → Tower.Head) {A : Type} {n : Nat}
    {context : List Vectors.DataSort} (expression : Vectors.IndexExpr context)
    (environment : TermEnv (Vectors.interface A) Tower.Head n context) :
    (indexTerm expression environment).mapHead map =
      indexTerm expression (mapEnv (Tm.mapHead map) environment) := by
  induction expression with
  | zero => rfl
  | «variable» reference => exact lookup_mapHead map reference environment
  | successor expression ih =>
      simp only [indexTerm, NativeNaturalVectorFamilies.succApp, Tm.mapHead, ih]
  | addition left right ihLeft ihRight =>
      simp only [indexTerm, Tm.mapHead, ihLeft, ihRight]

def indexSyntax (A : Type) : IndexSyntax (Vectors.interface A) Tower.Head where
  term := indexTerm
  substitute := by
    intro context n m expression environment substitution
    induction expression with
    | zero => rfl
    | «variable» reference => exact lookup_substitute substitution reference environment
    | successor expression ih => simp only [indexTerm, NativeNaturalVectorFamilies.succApp, subst, ih]
    | addition left right ihLeft ihRight => simp only [indexTerm, subst, ihLeft, ihRight]

/-- The sole ambient variable is the guest element type; host `A` supplies
the source interpretation, not a hidden guest constant. -/
def types (A : Type) : Types.TypeSyntax (Vectors.interface A) Tower.Head 1 where
  dataType := fun sort => match sort with
    | .length => NativeNaturalVectorFamilies.natTm
    | .payload => .var 0
  indexType := NativeNaturalVectorFamilies.natTm
  family := .app (.const NativeNaturalVectorFamilies.vecName) (.var 0)
  constructor := fun name =>
    .app (.const (if name = "Nil" then NativeNaturalVectorFamilies.vnilName else NativeNaturalVectorFamilies.vconsName)) (.var 0)
  motiveUniverse := .sort NativeNaturalVectorFamilies.motiveLevel

def nilOccurrence (A : Type) : Fin (Vectors.admitted A).constructors.length := ⟨0, by change 0 < 2; decide⟩
def consOccurrence (A : Type) : Fin (Vectors.admitted A).constructors.length := ⟨1, by change 1 < 2; decide⟩

theorem generated_nil_type (A : Type) :
    .pi (.head (.sort NativeNaturalVectorFamilies.elementLevel))
      (Types.constructorType (indexSyntax A) (Vectors.nilCode A) (types A) PUnit.unit) =
      NativeNaturalVectorFamilies.vnilType := rfl

theorem generated_cons_type (A : Type) :
    .pi (.head (.sort NativeNaturalVectorFamilies.elementLevel))
      (Types.constructorType (indexSyntax A) (Vectors.consCode A) (types A) PUnit.unit) =
      NativeNaturalVectorFamilies.vconsType := rfl

theorem generated_motive_type (A : Type) :
    Types.motiveType (types A) = NativeNaturalVectorFamilies.vecMotiveType := rfl

theorem generated_nil_method (A : Type) :
    Types.methodType (indexSyntax A)
      ((Vectors.admitted A).constructors.get (nilOccurrence A))
      (types A).weaken (.var 0) = NativeNaturalVectorFamilies.vecNilCaseType := by
  simp [Types.methodType, Types.methodBody, Types.hypotheses, nilOccurrence,
    Vectors.admitted, Vectors.constructors, Vectors.nilCode, types, Types.TypeSyntax.weaken,
    Types.TypeSyntax.map, indexSyntax, indexTerm, Types.motiveAt, NativeNaturalVectorFamilies.vecNilCaseType,
    NativeNaturalVectorFamilies.vnilApp, rename, wk]

theorem generated_cons_method (A : Type) :
    Types.methodType (indexSyntax A)
      ((Vectors.admitted A).constructors.get (consOccurrence A))
      (types A).weaken.weaken (.var 1) = NativeNaturalVectorFamilies.vecConsCaseType := by
  simp [Types.methodType, Types.methodBody, Types.hypotheses, consOccurrence,
    Vectors.admitted, Vectors.constructors, Vectors.consCode, types, Types.TypeSyntax.weaken,
    Types.TypeSyntax.map, indexSyntax, indexTerm, lookup, Types.motiveAt, NativeNaturalVectorFamilies.vecConsCaseType,
    NativeNaturalVectorFamilies.vconsApp, NativeNaturalVectorFamilies.vecApp, rename, wk, Types.weakenEnvironment, mapEnv]

theorem generated_eliminator_type (A : Type) :
    .pi (.head (.sort NativeNaturalVectorFamilies.elementLevel))
      (Types.eliminatorType (indexSyntax A) (Vectors.admitted A) (types A)) =
      NativeNaturalVectorFamilies.vecEliminateType := by
  simp [sortTm, Types.eliminatorType, Types.methodsType, Types.motiveType, Types.methodType,
    Types.methodBody, Types.hypotheses, Types.motiveAt, Types.TypeSyntax.weaken,
    Types.TypeSyntax.map, Types.weakenEnvironment, types, indexSyntax, indexTerm, lookup,
    Vectors.admitted, Vectors.constructors, Vectors.nilCode, Vectors.consCode,
    NativeNaturalVectorFamilies.vecEliminateType, NativeNaturalVectorFamilies.vecMotiveType,
    NativeNaturalVectorFamilies.vecNilCaseType, NativeNaturalVectorFamilies.vecConsCaseType,
    NativeNaturalVectorFamilies.vecEliminateResultType, NativeNaturalVectorFamilies.vecApp,
    NativeNaturalVectorFamilies.vnilApp, NativeNaturalVectorFamilies.vconsApp, rename, wk, mapEnv]

theorem generated_nil_context (A : Type) :
    Types.iotaContext (indexSyntax A) (Vectors.admitted A) (nilOccurrence A)
      (types A) NativeNaturalVectorFamilies.vecContextA = NativeNaturalVectorFamilies.vecContextAPZS := by
  simp [sortTm, Types.motiveType, Types.methodType,
    Types.methodBody, Types.hypotheses, Types.motiveAt, Types.TypeSyntax.weaken,
    Types.TypeSyntax.map, Types.weakenEnvironment, types, indexSyntax, indexTerm, lookup,
    Vectors.admitted, Vectors.constructors, Vectors.nilCode, Vectors.consCode,
    NativeNaturalVectorFamilies.vecMotiveType,
    NativeNaturalVectorFamilies.vecNilCaseType, NativeNaturalVectorFamilies.vecConsCaseType,
    NativeNaturalVectorFamilies.vecApp,
    NativeNaturalVectorFamilies.vnilApp, NativeNaturalVectorFamilies.vconsApp, rename, wk, mapEnv, Types.iotaContext, Types.methodsContext, Types.fieldsContext,
    Types.castContext, Types.parameterShift, nilOccurrence, fieldCount, arity,
    NativeNaturalVectorFamilies.vecContextA, NativeNaturalVectorFamilies.vecContextAP,
    NativeNaturalVectorFamilies.vecContextAPZ, NativeNaturalVectorFamilies.vecContextAPZS]

theorem generated_cons_context (A : Type) :
    Types.iotaContext (indexSyntax A) (Vectors.admitted A) (consOccurrence A)
      (types A) NativeNaturalVectorFamilies.vecContextA = NativeNaturalVectorFamilies.vecContextAPZSNHeadTail := by
  simp [sortTm, Types.motiveType, Types.methodType,
    Types.methodBody, Types.hypotheses, Types.motiveAt, Types.TypeSyntax.weaken,
    Types.TypeSyntax.map, Types.weakenEnvironment, types, indexSyntax, indexTerm, lookup,
    Vectors.admitted, Vectors.constructors, Vectors.nilCode, Vectors.consCode,
    NativeNaturalVectorFamilies.vecMotiveType,
    NativeNaturalVectorFamilies.vecNilCaseType, NativeNaturalVectorFamilies.vecConsCaseType,
    NativeNaturalVectorFamilies.vecApp,
    NativeNaturalVectorFamilies.vnilApp, NativeNaturalVectorFamilies.vconsApp, rename, wk, mapEnv, Types.iotaContext, Types.methodsContext, Types.fieldsContext,
    Types.castContext, Types.parameterShift, consOccurrence, fieldCount, arity,
    NativeNaturalVectorFamilies.vecContextA, NativeNaturalVectorFamilies.vecContextAP,
    NativeNaturalVectorFamilies.vecContextAPZ, NativeNaturalVectorFamilies.vecContextAPZS,
    NativeNaturalVectorFamilies.vecContextAPZSN, NativeNaturalVectorFamilies.vecContextAPZSNHead,
    NativeNaturalVectorFamilies.vecContextAPZSNHeadTail]

def recursorPrefix : Tower.Tm 1 := .app (.const NativeNaturalVectorFamilies.vecEliminateName) (.var 0)

theorem generated_nil_endpoints (A : Type) :
    Types.iotaSchema (indexSyntax A) (Vectors.admitted A) (nilOccurrence A)
      (types A) recursorPrefix = (NativeNaturalVectorFamilies.vecNilIotaLeft, NativeNaturalVectorFamilies.vecNilIotaRight) := rfl

theorem generated_cons_endpoints (A : Type) :
    Types.iotaSchema (indexSyntax A) (Vectors.admitted A) (consOccurrence A)
      (types A) recursorPrefix = (NativeNaturalVectorFamilies.vecConsIotaLeft, NativeNaturalVectorFamilies.vecConsIotaRight) := rfl

theorem generated_nil_result_type (A : Type) :
    Types.iotaType (indexSyntax A) (Vectors.admitted A) (nilOccurrence A) (types A) =
      NativeNaturalVectorFamilies.vecNilIotaType := rfl

theorem generated_cons_result_type (A : Type) :
    Types.iotaType (indexSyntax A) (Vectors.admitted A) (consOccurrence A) (types A) =
      NativeNaturalVectorFamilies.vecConsIotaType := rfl

/-- The fields are generated; the proof comes from the independently authored
reference receipt after the preceding comparisons. This instance does not
assume a generic formation or subject-preservation theorem. -/
noncomputable def nilSchema (A : Type) : Declaration.IndexedFamily.IotaSchema
    Tower.rules NativeNaturalVectorFamilies.rawSignature NativeNaturalVectorFamilies.proofRelevantIotaComputation 4 where
  context := Types.iotaContext (indexSyntax A) (Vectors.admitted A) (nilOccurrence A)
    (types A) NativeNaturalVectorFamilies.vecContextA
  left := (Types.iotaSchema (indexSyntax A) (Vectors.admitted A) (nilOccurrence A)
    (types A) recursorPrefix).1
  right := (Types.iotaSchema (indexSyntax A) (Vectors.admitted A) (nilOccurrence A)
    (types A) recursorPrefix).2
  type := Types.iotaType (indexSyntax A) (Vectors.admitted A) (nilOccurrence A) (types A)
  receipt := by
    rw [generated_nil_context, generated_nil_endpoints, generated_nil_result_type]
    exact NativeNaturalVectorFamilies.vecNilIotaReceipt

noncomputable def consSchema (A : Type) : Declaration.IndexedFamily.IotaSchema
    Tower.rules NativeNaturalVectorFamilies.rawSignature NativeNaturalVectorFamilies.proofRelevantIotaComputation 7 where
  context := Types.iotaContext (indexSyntax A) (Vectors.admitted A) (consOccurrence A)
    (types A) NativeNaturalVectorFamilies.vecContextA
  left := (Types.iotaSchema (indexSyntax A) (Vectors.admitted A) (consOccurrence A)
    (types A) recursorPrefix).1
  right := (Types.iotaSchema (indexSyntax A) (Vectors.admitted A) (consOccurrence A)
    (types A) recursorPrefix).2
  type := Types.iotaType (indexSyntax A) (Vectors.admitted A) (consOccurrence A) (types A)
  receipt := by
    rw [generated_cons_context, generated_cons_endpoints, generated_cons_result_type]
    exact NativeNaturalVectorFamilies.vecConsIotaReceipt

noncomputable def schemas (A : Type) : Declaration.IndexedFamily.Checking.Schemas
    Tower.rules NativeNaturalVectorFamilies.rawSignature NativeNaturalVectorFamilies.proofRelevantIotaComputation :=
  [⟨4, nilSchema A⟩, ⟨7, consSchema A⟩]

theorem generated_table_reference (A : Type) :
    Declaration.IndexedFamily.Checking.table (schemas A) = NativeNaturalVectorFamilies.Checking.table.drop 2 := rfl

local instance : DecidableRel NativeNaturalVectorFamilies.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred NativeNaturalVectorFamilies.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (NativeNaturalVectorFamilies.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel NativeNaturalVectorFamilies.rules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel NativeNaturalVectorFamilies.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

/-- Proof-free hints. The independent replay checks every universe choice,
ambient binding and dependent application before accepting a submission. -/
def choices : FormationSensitiveElaboration.Choices Tower.Head NativeNaturalVectorFamilies.Checking.decoder.Code where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (Tower.rules.cumulative first second)
  normalize := fun _ term => term
  conversion := fun _ left right =>
    if left = right then some (.refl left)
    else match left, right with
      | .head first, .head second => some (.single (.head first second))
      | _, _ => none

def submission {n : Nat} (context : Tower.Ctx n) (term type : Tower.Tm n) :=
  FormationSensitiveElaboration.elaborate NativeNaturalVectorFamilies.rules NativeNaturalVectorFamilies.Checking.decoder
    choices 64 context term type

def accepted {n : Nat} (context : Tower.Ctx n) (term type : Tower.Tm n) : Bool :=
  (submission context term type).isSome

theorem accepted_sound {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (checked : accepted context term type = true) :
    FormationSensitive.Judgment NativeNaturalVectorFamilies.rules context term type := by
  obtain ⟨code, produced⟩ := Option.isSome_iff_exists.mp checked
  exact FormationSensitiveElaboration.elaborate_sound NativeNaturalVectorFamilies.rules NativeNaturalVectorFamilies.Checking.decoder
    choices 64 context term type code produced

def verdictsFor (nilContext : Tower.Ctx 4) (nilLeft nilRight nilType : Tower.Tm 4)
    (consContext : Tower.Ctx 7) (consLeft consRight consType : Tower.Tm 7) : List (String × Bool) := [
  ("generated nil source is formed", accepted nilContext
    nilLeft nilType),
  ("generated nil target is formed", accepted nilContext
    nilRight nilType),
  ("generated cons source is formed", accepted consContext
    consLeft consType),
  ("generated cons target is formed", accepted consContext
    consRight consType),
  ("tail cannot replace payload", !(accepted consContext (.var 0) (.var 6))),
  ("payload cannot replace tail", !(accepted consContext (.var 1)
    (NativeNaturalVectorFamilies.vecApp (.var 6) (.var 2)))),
  ("undeclared index arithmetic has no typing authority", !(accepted NativeNaturalVectorFamilies.vecContextA
    (.app (.app (.const `Unadmitted.IndexAdd) NativeNaturalVectorFamilies.zeroTm) NativeNaturalVectorFamilies.zeroTm) NativeNaturalVectorFamilies.natTm)),
  ("unused malformed ambient binding is rejected", !(accepted
    (.snoc (.snoc .nil (.head (.sort NativeNaturalVectorFamilies.elementLevel))) (.const `Undeclared))
    NativeNaturalVectorFamilies.zeroTm NativeNaturalVectorFamilies.natTm))]



noncomputable def verdicts := verdictsFor
  (nilSchema Bool).context (nilSchema Bool).left (nilSchema Bool).right (nilSchema Bool).type
  (consSchema Bool).context (consSchema Bool).left (consSchema Bool).right (consSchema Bool).type

/-- Executable specialization at the independently represented reference
syntax. The equality below qualifies its inputs against generated source rows;
it does not turn the source's semantic evaluator into a runtime decoder. -/
def runtimeVerdicts := verdictsFor
  NativeNaturalVectorFamilies.vecContextAPZS
  NativeNaturalVectorFamilies.vecNilIotaLeft NativeNaturalVectorFamilies.vecNilIotaRight
  NativeNaturalVectorFamilies.vecNilIotaType
  NativeNaturalVectorFamilies.vecContextAPZSNHeadTail
  NativeNaturalVectorFamilies.vecConsIotaLeft NativeNaturalVectorFamilies.vecConsIotaRight
  NativeNaturalVectorFamilies.vecConsIotaType

theorem verdicts_eq_runtime : verdicts = runtimeVerdicts := by
  simp only [verdicts, runtimeVerdicts, nilSchema, consSchema, generated_nil_context,
    generated_cons_context, generated_nil_endpoints, generated_cons_endpoints,
    generated_nil_result_type, generated_cons_result_type]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem all_verdicts : verdicts.all Prod.snd = true := by
  rw [verdicts_eq_runtime]
  decide +kernel

theorem generated_inventory_checked :
    Formation.check NativeNaturalVectorFamilies.rules NativeNaturalVectorFamilies.Checking.decoder
      choices 64 (indexSyntax Bool) (Vectors.admitted Bool) (types Bool)
      NativeNaturalVectorFamilies.vecContextA recursorPrefix = true := by
  apply (Formation.check_iff _ _ _ _ _ _ _ _ _).mpr
  intro occurrence
  have passed := all_verdicts
  simp only [verdicts, verdictsFor, List.all_cons, List.all_nil,
    Bool.and_eq_true] at passed
  refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index)
    occurrence
  · erw [Formation.rowCheck_eq]
    change (accepted (nilSchema Bool).context (nilSchema Bool).left (nilSchema Bool).type &&
      accepted (nilSchema Bool).context (nilSchema Bool).right (nilSchema Bool).type) = true
    rw [passed.1, passed.2.1]
    rfl
  · erw [Formation.rowCheck_eq]
    change (accepted (consSchema Bool).context (consSchema Bool).left (consSchema Bool).type &&
      accepted (consSchema Bool).context (consSchema Bool).right (consSchema Bool).type) = true
    rw [passed.2.2.1, passed.2.2.2.1]
    rfl

/-- The structured coGSLT source admits the same inventory consumed by the
generic checker. This is not a claim about a textual `.module` parser. -/
theorem admitted_source_checked :
    ((IndexedInductive.admit? (Vectors.source Bool)).map fun admitted =>
      Formation.check NativeNaturalVectorFamilies.rules NativeNaturalVectorFamilies.Checking.decoder
        choices 64 (indexSyntax Bool) admitted (types Bool)
        NativeNaturalVectorFamilies.vecContextA recursorPrefix) = some true := by
  rw [Vectors.source_admitted]
  exact congrArg some generated_inventory_checked

/-- Every actual source constructor has formed endpoints, including all
ambient assumptions. The same generic inventory checker establishes this
fact; the native raw receipts alone are not used to infer formation. -/
theorem generated_rows_formed (occurrence : Fin (Vectors.admitted Bool).constructors.length) :
    FormationSensitive.Judgment NativeNaturalVectorFamilies.rules
        (Types.iotaContext (indexSyntax Bool) (Vectors.admitted Bool) occurrence (types Bool)
          NativeNaturalVectorFamilies.vecContextA)
        (Types.iotaSchema (indexSyntax Bool) (Vectors.admitted Bool) occurrence
          (types Bool) recursorPrefix).1
        (Types.iotaType (indexSyntax Bool) (Vectors.admitted Bool) occurrence (types Bool)) ∧
      FormationSensitive.Judgment NativeNaturalVectorFamilies.rules
        (Types.iotaContext (indexSyntax Bool) (Vectors.admitted Bool) occurrence (types Bool)
          NativeNaturalVectorFamilies.vecContextA)
        (Types.iotaSchema (indexSyntax Bool) (Vectors.admitted Bool) occurrence
          (types Bool) recursorPrefix).2
        (Types.iotaType (indexSyntax Bool) (Vectors.admitted Bool) occurrence (types Bool)) :=
  Formation.check_sound _ _ _ _ _ _ _ _ _ generated_inventory_checked occurrence

/-- This same well-typed inventory is not accepted with no search budget.
Producer failure therefore cannot be interpreted as refutation of typing. -/
theorem formed_inventory_zero_budget :
    Formation.check NativeNaturalVectorFamilies.rules NativeNaturalVectorFamilies.Checking.decoder
      choices 0 (indexSyntax Bool) (Vectors.admitted Bool) (types Bool)
      NativeNaturalVectorFamilies.vecContextA recursorPrefix = false := by
  simp [Formation.check, Formation.inventory, Formation.rowCheck, Formation.elaborateRow_zero,
    List.ofFn_succ, Vectors.admitted, Vectors.constructors]

#eval runtimeVerdicts

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.TypedControls
