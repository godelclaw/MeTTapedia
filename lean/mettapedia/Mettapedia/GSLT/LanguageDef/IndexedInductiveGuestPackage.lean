import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestDeclarations
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedFamilyChecking

/-!
# Generated indexed schemas in the shared typed checking interface

The authored constructor inventory generates the entire parameterized table.
Each canonical endpoint is checked against the opaque declaration library,
before its generated equations are installed. Accepted rows produce the
existing typed schemas, with the original table position and every assignment
retained. Selection of those schemas uses the existing profile checker.

Installing a raw equation table is not computational authorization. Uniform
subject preservation, dependent semantic interpretation and the DTT policy's
authority remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Package

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Declaration Declaration.ComputationAuthority Declaration.IndexedFamily

universe u
variable {I : Interface.{u}} {Head : Type} {n : Nat}

variable (indices : IndexSyntax I Head) (parameters : Declarations.Parameters I Head n)
    (names : Declarations.Names) (admitted : Admitted I [])

private def arguments {m : Nat} : {k : Nat} → Ctx Head k → Sub Head k m → List (Tm Head m)
  | _, .nil, _ => []
  | _, .snoc context _, assignment =>
      arguments context (fun i => assignment i.succ) ++ [assignment 0]

private theorem arguments_length {m k : Nat} (context : Ctx Head k)
    (assignment : Sub Head k m) : (arguments context assignment).length = k := by
  induction context with
  | nil => rfl
  | snoc context domain ih => simp [arguments, ih]

private theorem applyClosed_eq {m k : Nat} (context : Ctx Head k)
    (assignment : Sub Head k m) (function : Tm Head m) :
    TelescopeAbstraction.applyClosed context assignment function =
      applyArgs function (arguments context assignment) := by
  induction context with
  | nil => rfl
  | snoc context domain ih =>
      simp only [TelescopeAbstraction.applyClosed, arguments, Types.applyArgs_append,
        applyArgs_cons, applyArgs_nil, ih]

private theorem arguments_free {m k : Nat} (family : DeclName) (context : Ctx Head k)
    (assignment : Sub Head k m) (free : ∀ i, FreeOf family (assignment i)) :
    ∀ term ∈ arguments context assignment, FreeOf family term := by
  induction context with
  | nil => simp [arguments]
  | snoc context domain ih =>
      intro term member
      rcases List.mem_append.mp member with old | last
      · exact ih _ (fun i => free i.succ) term old
      · exact (List.mem_singleton.mp last) ▸ free 0

/-- Parameter domains may mention earlier parameters but not the family
currently being introduced. -/
def ContextFree (family : DeclName) : {k : Nat} → Ctx Head k → Prop
  | _, .nil => True
  | _, .snoc context domain => ContextFree family context ∧ FreeOf family domain

private noncomputable def closePositive (family : DeclName) (count : Nat) {k : Nat}
    (context : Ctx Head k) (free : ContextFree family context) (type : Tm Head k)
    (positive : ConstructorType family count type) :
    ConstructorType family count (TelescopeAbstraction.closeType context type) := by
  induction context with
  | nil => exact positive
  | snoc context domain ih =>
      exact ih free.1 (.pi domain type) (.field (.free free.2) positive)

/-- Source strict positivity survives closing the explicit parameter
telescope. The generated constructor type itself is not a premise. -/
noncomputable def constructorPositive
    (indexFree : Types.IndexFree indices names.family)
    (contextFree : ContextFree names.family parameters.context)
    (dataFree : ∀ sort, FreeOf names.family (parameters.dataType sort))
    (constructor : NamedConstructor I []) :
    ConstructorType names.family (n + 1)
      (Declarations.constructorEntry indices parameters names constructor).type := by
  apply closePositive names.family (n + 1) parameters.context contextFree
  have positive := Types.constructorPositive indices names.family indexFree constructor.body
    (parameters.types names) PUnit.unit (arguments parameters.context ids)
    (applyClosed_eq parameters.context ids (.const names.family))
    (arguments_free names.family parameters.context ids (fun i => .var i)) dataFree trivial
  simpa only [arguments_length] using positive

private theorem entryLookup (source : List (DeclName × Entry Head))
    (unique : (source.map Prod.fst).Nodup) (item : DeclName × Entry Head) (member : item ∈ source) :
    (Signature.ofList source).entries item.1 = some item.2 := by
  induction source with
  | nil => cases member
  | cons first rest ih =>
      have distinct := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with rfl | later
      · simp [Signature.ofList, Signature.insert]
      · have different : item.1 ≠ first.1 := by
          intro equal
          exact distinct.1 (equal ▸ List.mem_map_of_mem later)
        simpa [Signature.ofList, Signature.insert, different] using ih distinct.2 later

def recursor : Tm Head n :=
  TelescopeAbstraction.applyClosed parameters.context (fun i => .var i)
    (.const names.eliminator)

/-- One row per source occurrence; parameters remain oldest in its telescope. -/
def table : AlgebraicSchema.SchemaTable Head :=
  List.ofFn fun occurrence : Fin admitted.constructors.length =>
    ⟨arity admitted occurrence + n,
      Types.iotaSchema indices admitted occurrence (parameters.types names)
        (recursor parameters names)⟩

@[simp] theorem table_length :
    (table indices parameters names admitted).length = admitted.constructors.length := by
  simp [table]

def position (occurrence : Fin admitted.constructors.length) :
    Fin (table indices parameters names admitted).length :=
  ⟨occurrence.val, by simp⟩

@[simp] theorem table_get (occurrence : Fin admitted.constructors.length) :
    (table indices parameters names admitted).get
        (position indices parameters names admitted occurrence) =
      ⟨arity admitted occurrence + n,
        Types.iotaSchema indices admitted occurrence (parameters.types names)
          (recursor parameters names)⟩ := by
  simp [table, position]

def computation : ProofRelevantRootComputation Head :=
  SchemaTableConversionCode.retained (table indices parameters names admitted) (fun _ => true)

def library (prior : List (DeclName × Entry Head)) : List (DeclName × Entry Head) :=
  prior ++ Declarations.entries indices parameters names admitted

def signature (prior : List (DeclName × Entry Head)) : Signature Head :=
  { Signature.ofList (library indices parameters names admitted prior) with
    computation := (computation indices parameters names admitted).support }

def namesDistinct (prior : List (DeclName × Entry Head)) : Bool :=
  decide (((library indices parameters names admitted prior).map Prod.fst).Nodup)

def constructorNames : List DeclName :=
  admitted.constructors.map fun constructor => names.constructor constructor.name

private theorem generated_names_distinct (prior : List (DeclName × Entry Head))
    (distinct : namesDistinct indices parameters names admitted prior = true) :
    (names.family :: constructorNames names admitted ++ [names.eliminator]).Nodup := by
  have all : ((library indices parameters names admitted prior).map Prod.fst).Nodup := of_decide_eq_true distinct
  rw [library, List.map_append] at all
  simpa only [Declarations.entries_names, constructorNames] using all.of_append_right

private theorem lookupGenerated (prior : List (DeclName × Entry Head))
    (distinct : namesDistinct indices parameters names admitted prior = true)
    (item : DeclName × Entry Head)
    (member : item ∈ Declarations.entries indices parameters names admitted) :
    (signature indices parameters names admitted prior).typeOf? item.1 = some item.2.type := by
  have lookup := entryLookup (library indices parameters names admitted prior)
    (of_decide_eq_true distinct) item (List.mem_append_right _ member)
  exact congrArg (Option.map Entry.type) lookup

noncomputable def constructorSpecs (prior : List (DeclName × Entry Head))
    (distinct : namesDistinct indices parameters names admitted prior = true)
    (indexFree : Types.IndexFree indices names.family)
    (contextFree : ContextFree names.family parameters.context)
    (dataFree : ∀ sort, FreeOf names.family (parameters.dataType sort)) :
    List (ConstructorSpec (signature indices parameters names admitted prior) names.family (n + 1)) :=
  admitted.constructors.attach.map fun marked => {
    name := names.constructor marked.val.name
    type := (Declarations.constructorEntry indices parameters names marked.val).type
    declared := lookupGenerated indices parameters names admitted prior distinct _ (by
      apply List.mem_append_left
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨marked.val, marked.property, rfl⟩)
    positive := constructorPositive indices parameters names indexFree contextFree dataFree marked.val }

@[simp] theorem constructorSpecs_names (prior : List (DeclName × Entry Head))
    (distinct : namesDistinct indices parameters names admitted prior = true)
    (indexFree : Types.IndexFree indices names.family)
    (contextFree : ContextFree names.family parameters.context)
    (dataFree : ∀ sort, FreeOf names.family (parameters.dataType sort)) :
    (constructorSpecs indices parameters names admitted prior distinct indexFree contextFree dataFree).map
      ConstructorSpec.name = constructorNames names admitted := by
  simp [constructorSpecs, constructorNames, List.map_map, Function.comp_def]

theorem extendsOpaque (prior : List (DeclName × Entry Head)) :
    (Signature.ofList (library indices parameters names admitted prior)).Extends
      (signature indices parameters names admitted prior) where
  entries := fun known => known
  computation := by
    intro ambient left right impossible
    rw [Signature.computation_ofList] at impossible
    exact impossible.elim

/-- Declaration formation is transported only after checking the opaque
library. No generated equation participates in that admission. -/
theorem formed (base : Rules Head) (prior : List (DeclName × Entry Head))
    (checked : DeclarationAdmissionReplay.Admitted base []
      (library indices parameters names admitted prior))
    (opaquePrior : ∀ item ∈ prior, item.2.value? = none) :
    (signature indices parameters names admitted prior).Formed base := by
  have original := Declarations.opaque_formed base
    (library indices parameters names admitted prior) checked (by
      intro item member
      rcases List.mem_append.mp member with old | generated
      · exact opaquePrior item old
      · exact Declarations.entries_opaque indices parameters names admitted item generated)
  exact {
    fresh := original.fresh
    types := by
      intro name type found
      obtain ⟨level, levelValid, typed⟩ := original.types found
      exact ⟨level, levelValid, Declaration.HasType.monoSignature base
        (extendsOpaque indices parameters names admitted prior) typed⟩
    values := fun typed value => Declaration.HasType.monoSignature base
      (extendsOpaque indices parameters names admitted prior) (original.values typed value)
    noSelfDelta := original.noSelfDelta }

/-- The row address and full assignment construct evidence of this exact
schema instance, including when another row has equal endpoints. -/
def evidenceAt (occurrence : Fin admitted.constructors.length) {ambient : Nat}
    (assignment : Sub Head (arity admitted occurrence + n) ambient) :
    (computation indices parameters names admitted).Evidence
      (subst assignment (Types.iotaSchema indices admitted occurrence
        (parameters.types names) (recursor parameters names)).1)
      (subst assignment (Types.iotaSchema indices admitted occurrence
        (parameters.types names) (recursor parameters names)).2) := by
  have evidence := SchemaTableConversionCode.Evidence.instantiate
    (table := table indices parameters names admitted) (enabled := fun _ => true)
    (n := ambient) (position indices parameters names admitted occurrence) rfl
  rw [table_get] at evidence
  exact evidence assignment

private noncomputable def appliedHead {k : Nat} (name : DeclName) (function : Tm Head k)
    (head : ApplicationHead name function) (args : List (Tm Head k)) :
    ApplicationHead name (applyArgs function args) := by
  induction args generalizing function with
  | nil => exact head
  | cons argument rest ih => exact ih (.app function argument) (.app head)

private noncomputable def parameterHead {k m : Nat} (context : Ctx Head k)
    (assignment : Sub Head k m) (name : DeclName) :
    ApplicationHead name (TelescopeAbstraction.applyClosed context assignment (.const name)) := by
  rw [applyClosed_eq]
  exact appliedHead name _ .const _

private noncomputable def headOccurrence {k : Nat} {name : DeclName} {term : Tm Head k}
    (head : ApplicationHead name term) : ConstantOccurrence name term := by
  induction head with
  | const => exact .here
  | app head ih => exact .appFunction ih

section Checking

variable (base : Rules Head) [DecidableEq Head]
    [DecidableRel base.headTyping] [DecidablePred base.isUniverse]
    [∀ u v w, Decidable (base.join u v w)] [DecidableRel base.cumulative]
    [DecidableRel base.headEq]
variable (decoder : StructuralConversionCode.RootDecoder base.computation)
    (choices : Declarations.Choices base decoder) (fuel : Nat)
    (prior : List (DeclName × Entry Head))

local instance : DecidableRel
    (extendRules base (Signature.ofList (library indices parameters names admitted prior))).headTyping :=
  fun _ _ => inferInstanceAs (Decidable (base.headTyping _ _))
local instance : DecidablePred
    (extendRules base (Signature.ofList (library indices parameters names admitted prior))).isUniverse :=
  fun _ => inferInstanceAs (Decidable (base.isUniverse _))
local instance : ∀ a b c, Decidable
    ((extendRules base (Signature.ofList (library indices parameters names admitted prior))).join a b c) :=
  fun _ _ _ => inferInstanceAs (Decidable (base.join _ _ _))
local instance : DecidableRel
    (extendRules base (Signature.ofList (library indices parameters names admitted prior))).cumulative :=
  fun _ _ => inferInstanceAs (Decidable (base.cumulative _ _))
local instance : DecidableRel
    (extendRules base (Signature.ofList (library indices parameters names admitted prior))).headEq :=
  fun _ _ => inferInstanceAs (Decidable (base.headEq _ _))

def checkRows : Bool :=
  Formation.check (extendRules base (Signature.ofList (library indices parameters names admitted prior)))
    (DeclarationConversionCode.ofList base decoder (library indices parameters names admitted prior))
    choices fuel indices admitted (parameters.types names) parameters.context (recursor parameters names)

/-- The existing shared schema, derived from accepted checking evidence. -/
def schema
    (accepted : checkRows indices parameters names admitted base decoder choices fuel prior = true)
    (occurrence : Fin admitted.constructors.length) :
    IotaSchema base (signature indices parameters names admitted prior)
      (computation indices parameters names admitted) (arity admitted occurrence + n) where
  context := Types.iotaContext indices admitted occurrence (parameters.types names) parameters.context
  left := (Types.iotaSchema indices admitted occurrence (parameters.types names) (recursor parameters names)).1
  right := (Types.iotaSchema indices admitted occurrence (parameters.types names) (recursor parameters names)).2
  type := Types.iotaType indices admitted occurrence (parameters.types names)
  receipt := {
    sourceTyping := Declaration.HasType.monoSignature base
      (extendsOpaque indices parameters names admitted prior) (Formation.check_sound
      (extendRules base (Signature.ofList (library indices parameters names admitted prior)))
      (DeclarationConversionCode.ofList base decoder (library indices parameters names admitted prior))
      choices fuel indices admitted
      (parameters.types names) parameters.context (recursor parameters names) accepted occurrence).1.toRaw
    targetTyping := Declaration.HasType.monoSignature base
      (extendsOpaque indices parameters names admitted prior) (Formation.check_sound
      (extendRules base (Signature.ofList (library indices parameters names admitted prior)))
      (DeclarationConversionCode.ofList base decoder (library indices parameters names admitted prior))
      choices fuel indices admitted
      (parameters.types names) parameters.context (recursor parameters names) accepted occurrence).2.toRaw
    evidence := by
      simpa only [subst_ids] using
        evidenceAt indices parameters names admitted occurrence ids }

def schemas
    (accepted : checkRows indices parameters names admitted base decoder choices fuel prior = true) :
    Checking.Schemas base (signature indices parameters names admitted prior)
      (computation indices parameters names admitted) :=
  List.ofFn fun occurrence : Fin admitted.constructors.length =>
    ⟨arity admitted occurrence + n,
      schema indices parameters names admitted base decoder choices fuel prior accepted occurrence⟩

/-- The shared checker sees every original generated row, in source order.
There is no filtering or quotienting of equal endpoints at this boundary. -/
theorem schemas_table
    (accepted : checkRows indices parameters names admitted base decoder choices fuel prior = true) :
    Checking.table (schemas indices parameters names admitted base decoder choices fuel prior accepted) =
      table indices parameters names admitted := by
  simp only [Checking.table, schemas, List.map_ofFn, table]
  rfl

theorem schemas_length
    (accepted : checkRows indices parameters names admitted base decoder choices fuel prior = true) :
    (schemas indices parameters names admitted base decoder choices fuel prior accepted).length =
      admitted.constructors.length := by simp [schemas]

noncomputable def rule
    (accepted : checkRows indices parameters names admitted base decoder choices fuel prior = true)
    (occurrence : Fin admitted.constructors.length) :
    IotaRule base (signature indices parameters names admitted prior)
      (computation indices parameters names admitted) (constructorNames names admitted) names.eliminator where
  constructorName := names.constructor (admitted.constructors.get occurrence).name
  constructorDeclared := List.mem_map.mpr ⟨_, List.get_mem _ occurrence, rfl⟩
  arity := arity admitted occurrence + n
  schema := schema indices parameters names admitted base decoder choices fuel prior accepted occurrence
  eliminatorHead := by
    apply appliedHead
    exact (parameterHead parameters.context ids names.eliminator).rename
      (Types.parameterShift (arity admitted occurrence))
  constructorOccurrence := by
    change ConstantOccurrence _ (applyArgs _ (_ :: _ ++ [_, _]))
    rw [Types.applyArgs_append]
    apply ConstantOccurrence.appArgument
    apply headOccurrence
    apply appliedHead
    exact (parameterHead parameters.context ids
      (names.constructor (admitted.constructors.get occurrence).name)).rename
        (Types.parameterShift (arity admitted occurrence))

noncomputable def rules
    (accepted : checkRows indices parameters names admitted base decoder choices fuel prior = true) :=
  List.ofFn (rule indices parameters names admitted base decoder choices fuel prior accepted)

theorem rule_names
    (accepted : checkRows indices parameters names admitted base decoder choices fuel prior = true) :
    (rules indices parameters names admitted base decoder choices fuel prior accepted).map
      IotaRule.constructorName = constructorNames names admitted := by
  unfold rules
  rw [List.map_ofFn]
  change List.ofFn ((fun c => names.constructor c.name) ∘ admitted.constructors.get) = _
  rw [← List.map_ofFn, List.ofFn_get]
  rfl

/-- A complete informative candidate generated from one admitted source.
The index interpretation and parameter context supply their explicit
non-recursion conditions; constructor positivity, lookup, origins and rule
coverage are derived. Computational authority is not a field of this result. -/
noncomputable def candidate
    (checked : DeclarationAdmissionReplay.Admitted base []
      (library indices parameters names admitted prior))
    (opaquePrior : ∀ item ∈ prior, item.2.value? = none)
    (distinct : namesDistinct indices parameters names admitted prior = true)
    (indexFree : Types.IndexFree indices names.family)
    (contextFree : ContextFree names.family parameters.context)
    (dataFree : ∀ sort, FreeOf names.family (parameters.dataType sort))
    (accepted : checkRows indices parameters names admitted base decoder choices fuel prior = true) :
    Candidate base where
  signature := signature indices parameters names admitted prior
  formed := formed indices parameters names admitted base prior checked opaquePrior
  computation := computation indices parameters names admitted
  computationSupport := rfl
  familyName := names.family
  familyParameterCount := n
  familyIndexCount := 1
  familyType := (Declarations.familyEntry parameters).type
  familyDeclared := lookupGenerated indices parameters names admitted prior distinct _ (by
    exact List.mem_append_left _ (List.mem_cons_self))
  constructors := constructorSpecs indices parameters names admitted prior distinct indexFree contextFree dataFree
  constructorNamesNodup := by
    rw [constructorSpecs_names]
    exact (List.nodup_cons.mp (generated_names_distinct indices parameters names admitted prior distinct)).2.of_append_left
  familyNotConstructor := by
    intro constructor member same
    have found : constructor.name ∈ constructorNames names admitted := by
      rw [← constructorSpecs_names indices parameters names admitted prior distinct indexFree contextFree dataFree]
      exact List.mem_map_of_mem member
    exact (List.nodup_cons.mp (generated_names_distinct indices parameters names admitted prior distinct)).1
      (List.mem_append_left _ (same ▸ found))
  eliminator := {
    name := names.eliminator
    type := (Declarations.eliminatorEntry indices parameters names admitted).type
    declared := lookupGenerated indices parameters names admitted prior distinct _ (by
      exact List.mem_append_right _ (List.mem_singleton_self _)) }
  eliminatorNotFamily := by
    intro same
    exact (List.nodup_cons.mp (generated_names_distinct indices parameters names admitted prior distinct)).1
      (List.mem_append_right _ (same ▸ List.mem_singleton_self names.eliminator))
  eliminatorNotConstructor := by
    intro constructor member same
    have found : constructor.name ∈ constructorNames names admitted := by
      rw [← constructorSpecs_names indices parameters names admitted prior distinct indexFree contextFree dataFree]
      exact List.mem_map_of_mem member
    have disjoint := (List.nodup_cons.mp
      (generated_names_distinct indices parameters names admitted prior distinct)).2.disjoint
    change constructor.name = names.eliminator at same
    rw [same] at found
    exact List.disjoint_left.mp disjoint found (List.mem_singleton_self _)
  iotaRules := List.ofFn fun occurrence => {
    constructorName := names.constructor (admitted.constructors.get occurrence).name
    constructorDeclared := by
      rw [constructorSpecs_names]
      exact List.mem_map.mpr ⟨_, List.get_mem _ occurrence, rfl⟩
    arity := arity admitted occurrence + n
    schema := schema indices parameters names admitted base decoder choices fuel prior accepted occurrence
    eliminatorHead := (rule indices parameters names admitted base decoder choices fuel prior accepted occurrence).eliminatorHead
    constructorOccurrence := (rule indices parameters names admitted base decoder choices fuel prior accepted occurrence).constructorOccurrence }
  constructorsComputed := by
    intro name member
    rw [constructorSpecs_names] at member
    obtain ⟨constructor, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨occurrence, rfl⟩ := List.mem_iff_get.mp present
    exact List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨occurrence, rfl⟩, rfl⟩

theorem candidate_table
    (checked : DeclarationAdmissionReplay.Admitted base []
      (library indices parameters names admitted prior))
    (opaquePrior : ∀ item ∈ prior, item.2.value? = none)
    (distinct : namesDistinct indices parameters names admitted prior = true)
    (indexFree : Types.IndexFree indices names.family)
    (contextFree : ContextFree names.family parameters.context)
    (dataFree : ∀ sort, FreeOf names.family (parameters.dataType sort))
    (accepted : checkRows indices parameters names admitted base decoder choices fuel prior = true) :
    Checking.table (Checking.candidateSchemas
      (candidate indices parameters names admitted base decoder choices fuel prior
        checked opaquePrior distinct indexFree contextFree dataFree accepted)) =
      table indices parameters names admitted := by
  unfold Checking.candidateSchemas Checking.table candidate
  rw [List.map_ofFn, List.map_ofFn]
  rfl

/-- Publish a structurally admitted direct family after full prefix formation,
name separation, and every generated row check succeed.  This is the common
producer used by textual and independently admitted direct sources. -/
noncomputable def fromAdmitted
    (opaquePrior : ∀ item ∈ prior, item.2.value? = none)
    (indexFree : Types.IndexFree indices names.family)
    (contextFree : ContextFree names.family parameters.context)
    (dataFree : ∀ sort, FreeOf names.family (parameters.dataType sort))
    (shape : Admitted I []) : Option (Candidate base) :=
  match typed : Declarations.elaborate base decoder choices fuel []
      (library indices parameters names shape prior) with
  | none => none
  | some certificates =>
      if distinct : namesDistinct indices parameters names shape prior = true then
        if rows : checkRows indices parameters names shape base decoder choices fuel prior = true then
          some (candidate indices parameters names shape base decoder choices fuel prior
            (Declarations.elaborate_sound base decoder choices fuel [] _ certificates typed)
            opaquePrior distinct indexFree contextFree dataFree rows)
        else none
      else none

/-- Every published admitted family exposes exactly its complete generated
typed table. -/
theorem fromAdmitted_sound
    (opaquePrior : ∀ item ∈ prior, item.2.value? = none)
    (indexFree : Types.IndexFree indices names.family)
    (contextFree : ContextFree names.family parameters.context)
    (dataFree : ∀ sort, FreeOf names.family (parameters.dataType sort))
    (shape : Admitted I []) (output : Candidate base)
    (published : fromAdmitted indices parameters names base decoder choices fuel prior
      opaquePrior indexFree contextFree dataFree shape = some output) :
    Checking.table (Checking.candidateSchemas output) =
      table indices parameters names shape := by
  unfold fromAdmitted at published
  split at published
  · cases published
  · rename_i certificates typed
    split_ifs at published with distinct rows
    · have same : candidate indices parameters names shape base decoder choices fuel prior
          (Declarations.elaborate_sound base decoder choices fuel [] _ certificates typed)
          opaquePrior distinct indexFree contextFree dataFree rows = output :=
        Option.some.inj published
      cases same
      exact candidate_table indices parameters names shape base decoder choices fuel prior
        _ opaquePrior distinct indexFree contextFree dataFree rows

/-- Publication retains the exact generated declaration signature, not only
the same computation table. -/
theorem fromAdmitted_signature
    (opaquePrior : ∀ item ∈ prior, item.2.value? = none)
    (indexFree : Types.IndexFree indices names.family)
    (contextFree : ContextFree names.family parameters.context)
    (dataFree : ∀ sort, FreeOf names.family (parameters.dataType sort))
    (shape : Admitted I []) (output : Candidate base)
    (published : fromAdmitted indices parameters names base decoder choices fuel prior
      opaquePrior indexFree contextFree dataFree shape = some output) :
    output.signature = signature indices parameters names shape prior := by
  unfold fromAdmitted at published
  split at published
  · cases published
  · rename_i certificates typed
    split_ifs at published with distinct rows
    · have same : candidate indices parameters names shape base decoder choices fuel prior
          (Declarations.elaborate_sound base decoder choices fuel [] _ certificates typed)
          opaquePrior distinct indexFree contextFree dataFree rows = output :=
        Option.some.inj published
      cases same
      rfl

/-- Publication retains the complete generated proof-relevant root
computation. -/
theorem fromAdmitted_computation
    (opaquePrior : ∀ item ∈ prior, item.2.value? = none)
    (indexFree : Types.IndexFree indices names.family)
    (contextFree : ContextFree names.family parameters.context)
    (dataFree : ∀ sort, FreeOf names.family (parameters.dataType sort))
    (shape : Admitted I []) (output : Candidate base)
    (published : fromAdmitted indices parameters names base decoder choices fuel prior
      opaquePrior indexFree contextFree dataFree shape = some output) :
    output.computation = computation indices parameters names shape := by
  unfold fromAdmitted at published
  split at published
  · cases published
  · rename_i certificates typed
    split_ifs at published with distinct rows
    · have same : candidate indices parameters names shape base decoder choices fuel prior
          (Declarations.elaborate_sound base decoder choices fuel [] _ certificates typed)
          opaquePrior distinct indexFree contextFree dataFree rows = output :=
        Option.some.inj published
      cases same
      rfl

/-- Publish from the source document only after structural admission, full
prefix formation, name separation and every generated row check succeed.
Failure means this evidence producer did not produce a checked package. -/
noncomputable def fromSource
    (opaquePrior : ∀ item ∈ prior, item.2.value? = none)
    (indexFree : Types.IndexFree indices names.family)
    (contextFree : ContextFree names.family parameters.context)
    (dataFree : ∀ sort, FreeOf names.family (parameters.dataType sort))
    (source : Document I []) : Option (Admitted I [] × Candidate base) :=
  match IndexedInductive.admit? source with
  | none => none
  | some shape =>
      (fromAdmitted indices parameters names base decoder choices fuel prior
        opaquePrior indexFree contextFree dataFree shape).map fun output =>
          (shape, output)

/-- Publication retains the complete authored inventory and exposes exactly
its generated rows through the shared checker. -/
theorem fromSource_sound
    (opaquePrior : ∀ item ∈ prior, item.2.value? = none)
    (indexFree : Types.IndexFree indices names.family)
    (contextFree : ContextFree names.family parameters.context)
    (dataFree : ∀ sort, FreeOf names.family (parameters.dataType sort))
    (source : Document I []) (shape : Admitted I []) (output : Candidate base)
    (published : fromSource indices parameters names base decoder choices fuel prior
      opaquePrior indexFree contextFree dataFree source = some (shape, output)) :
    shape.constructors.map quoteConstructor = source.values ∧
      Checking.table (Checking.candidateSchemas output) = table indices parameters names shape := by
  unfold fromSource at published
  split at published
  · cases published
  · rename_i found structural
    cases generated : fromAdmitted indices parameters names base decoder choices fuel prior
        opaquePrior indexFree contextFree dataFree found with
    | none => simp [generated] at published
    | some candidate =>
        have mapped : some (found, candidate) = some (shape, output) := by
          simpa [generated] using published
        have same : (found, candidate) = (shape, output) := by
          exact Option.some.inj mapped
        cases same
        exact ⟨source_of_admit source shape structural,
          fromAdmitted_sound indices parameters names base decoder choices fuel prior
            opaquePrior indexFree contextFree dataFree shape output generated⟩

end Checking

#print axioms formed
#print axioms schemas_table
#print axioms candidate
#print axioms fromAdmitted_sound
#print axioms fromAdmitted_signature
#print axioms fromAdmitted_computation
#print axioms fromSource_sound

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Package
