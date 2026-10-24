import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestTypes
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestDeclarations
import Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuestControls
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuestControls
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestDeclarationControls
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestTypedControls

/-!
# Generated open List and VectorTree declaration interfaces

Both instances use the actual admitted source codes and existing native
container operations. The generic generator reproduces independently checked
constructor, method and complete eliminator declarations. Vector length expressions are interpreted
in the current data environment, including data binders before recursive fields.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedInductive.Guest
open IndexedPositiveContainerGuestTypes

local instance entryDecidableEq : DecidableEq (Presentation.Declaration.Entry Tower.Head) :=
  fun first second =>
    if typeSame : first.type = second.type then
      if valueSame : first.value? = second.value? then
        isTrue (by
          cases first
          cases second
          cases typeSame
          cases valueSame
          rfl)
      else isFalse (fun same => valueSame (congrArg Presentation.Declaration.Entry.value? same))
    else isFalse (fun same => typeSame (congrArg Presentation.Declaration.Entry.type same))

namespace Lists

abbrev I := PositiveInductiveScenarios.Search.interface
abbrev registry := Unindexed.liftRegistry PositiveInductiveScenarios.Search.registry I
abbrev indexing : Indexing I Tower.Head := .unindexed (by
  change Subsingleton Unit
  infer_instance)

/-- This registry contains exactly the already admitted native List container.
Its bundle retains the List of child/result pairs and its relation evidence. -/
def containers : RegistrySyntax I registry Tower.Head where
  fieldType _ _ _ _ _ element := NativeIndexedFamilies.Intrinsic.listApp element
  bundleType _ _ _ _ _ element predicate field :=
    PositiveInductiveSearchTreeGuest.bundleType element predicate field
  fieldType_substitute := by
    intros
    rfl
  bundleType_substitute := by
    intros
    simp [PositiveInductiveSearchTreeGuest.bundleType,
      PositiveInductiveSearchTreeGuest.packedType,
      PositiveInductiveSearchTreeGuest.packedRelation,
      NativeIndexedFamilies.Intrinsic.listApp,
      NativeIndexedFamilies.IntrinsicRelator.mapRelApp, subst]

def types {n : Nat} (answer : Tower.Tm n) : TypeSyntax I Tower.Head n where
  dataType _ := answer
  family := PositiveInductiveSearchTreeGuest.treeApp answer
  constructor name := .app (.const (.str PositiveInductiveSearchTreeGuest.treeName name)) answer

abbrev solvedCode := ModuleSource.PositiveInductiveLoweringControls.Search.solved.body.eraseIndexed
abbrev branchCode := ModuleSource.PositiveInductiveLoweringControls.Search.branch.body.eraseIndexed

def solvedType : Tower.Tm 0 :=
  .pi (sortTm PositiveInductiveSearchTreeGuest.level)
    (constructorType indexing containers solvedCode (types (.var 0)) PUnit.unit)

def branchType : Tower.Tm 0 :=
  .pi (sortTm PositiveInductiveSearchTreeGuest.level)
    (constructorType indexing containers branchCode (types (.var 0)) PUnit.unit)

def solvedMethod : Tower.Tm 2 :=
  methodType indexing containers solvedCode (types (.var 1)) (.var 0) "solved"

def branchMethod : Tower.Tm 3 :=
  methodType indexing containers branchCode (types (.var 2)) (.var 1) "branch"

def inventory := ModuleSource.PositiveInductiveLoweringControls.Search.resolvedFamily.constructors.map
  (fun constructor => (constructor.name, constructor.body.eraseIndexed))

def eliminatorOpen {n : Nat} (answer : Tower.Tm n) : Tower.Tm n :=
  IndexedPositiveContainerGuestTypes.eliminatorType indexing containers inventory
    (types answer) PUnit.unit (.sort PositiveInductiveSearchTreeGuest.level)

def eliminator : Tower.Tm 0 :=
  .pi (sortTm PositiveInductiveSearchTreeGuest.level) (eliminatorOpen (.var 0))

theorem eliminator_exact : eliminator = PositiveInductiveSearchTreeGuest.eliminateType := by
  decide +kernel

/-- A different constructor order denotes a different method interface. -/
def reversedEliminator : Tower.Tm 0 :=
  .pi (sortTm PositiveInductiveSearchTreeGuest.level)
    (IndexedPositiveContainerGuestTypes.eliminatorType indexing containers inventory.reverse
      (types (.var 0)) PUnit.unit (.sort PositiveInductiveSearchTreeGuest.level))

theorem reversed_order_not_exact : reversedEliminator ≠ PositiveInductiveSearchTreeGuest.eliminateType := by
  decide +kernel

theorem eliminator_substitution_witness :
    subst (fun index : Fin 1 => .var (wk index)) (eliminatorOpen (.var 0)) =
      eliminatorOpen (.var (wk (0 : Fin 1))) := by
  simpa only [eliminatorOpen, types, TypeSyntax.map, subst, Indexing.mapDomain,
    PositiveInductiveSearchTreeGuest.treeApp] using
    IndexedPositiveContainerGuestTypes.eliminatorType_substitute indexing containers inventory
      (types (.var 0)) PUnit.unit (.sort PositiveInductiveSearchTreeGuest.level)
      (fun index : Fin 1 => .var (wk index))

theorem declarations_exact :
    solvedType = PositiveInductiveSearchTreeGuest.solvedType ∧
      branchType = PositiveInductiveSearchTreeGuest.branchType ∧
      solvedMethod = PositiveInductiveSearchTreeGuest.solvedCaseType ∧
      branchMethod = PositiveInductiveSearchTreeGuest.branchCaseType := by
  decide +kernel

/-- Names determine both published entries and all internal prefixes. -/
def declarationNames : Declarations.Names where
  family := PositiveInductiveSearchTreeGuest.treeName
  constructor name := .str PositiveInductiveSearchTreeGuest.treeName name
  eliminator := PositiveInductiveSearchTreeGuest.eliminateName

def declarationParameters : Declarations.Registered.Parameters I Tower.Head indexing 1 where
  context := .snoc .nil (sortTm PositiveInductiveSearchTreeGuest.level)
  dataType _ := .var 0
  indexDomain := PUnit.unit
  familyUniverse := .sort PositiveInductiveSearchTreeGuest.level
  motiveUniverse := .sort PositiveInductiveSearchTreeGuest.level

def entries : List (DeclName × Presentation.Declaration.Entry Tower.Head) :=
  Declarations.Registered.entries indexing containers declarationParameters declarationNames inventory

theorem entries_exact : entries = PositiveInductiveSearchTreeGuest.entries := by
  decide +kernel

theorem branch_substitution_witness :
    subst (fun index : Fin 1 => .var (wk index))
        (constructorType indexing containers branchCode (types (.var 0)) PUnit.unit) =
      constructorType indexing containers branchCode (types (.var (wk (0 : Fin 1)))) PUnit.unit := by
  simpa only [types, TypeSyntax.map, PositiveInductiveSearchTreeGuest.treeApp, subst,
    mapEnv] using constructorType_substitute indexing containers branchCode
      (types (.var 0)) PUnit.unit (fun index : Fin 1 => .var (wk index))

local instance : DecidableRel PositiveInductiveSearchTreeGuest.baseRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred PositiveInductiveSearchTreeGuest.baseRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (PositiveInductiveSearchTreeGuest.baseRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel PositiveInductiveSearchTreeGuest.baseRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel PositiveInductiveSearchTreeGuest.baseRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def sourceAdmission :=
  Declarations.Registered.admitInventory PositiveInductiveSearchTreeGuest.baseRules
    PositiveInductiveSearchTreeGuest.baseDecoder PositiveInductiveSearchTreeGuest.choices 256 []
    indexing containers declarationParameters declarationNames inventory

theorem sourceAdmission_accepted : sourceAdmission.isSome = true := by
  change (Declarations.elaborate PositiveInductiveSearchTreeGuest.baseRules
    PositiveInductiveSearchTreeGuest.baseDecoder PositiveInductiveSearchTreeGuest.choices 256 [] entries).isSome = true
  rw [entries_exact]
  exact PositiveInductiveSearchTreeGuest.inventoryAccepted_eq_true

def sourceCertificates := sourceAdmission.get sourceAdmission_accepted

theorem sourceAdmission_eq : sourceAdmission = some sourceCertificates :=
  (Option.some_get sourceAdmission_accepted).symm

theorem declarations_admitted :
    DeclarationAdmissionReplay.Admitted PositiveInductiveSearchTreeGuest.baseRules [] entries :=
  Declarations.Registered.admitInventory_sound PositiveInductiveSearchTreeGuest.baseRules
    PositiveInductiveSearchTreeGuest.baseDecoder PositiveInductiveSearchTreeGuest.choices 256 []
    indexing containers declarationParameters declarationNames inventory sourceCertificates sourceAdmission_eq

theorem declarations_formed :
    (Presentation.Declaration.Signature.ofList entries).Formed
      PositiveInductiveSearchTreeGuest.baseRules :=
  Declarations.Registered.admitInventory_formed PositiveInductiveSearchTreeGuest.baseRules
    PositiveInductiveSearchTreeGuest.baseDecoder PositiveInductiveSearchTreeGuest.choices 256 []
    indexing containers declarationParameters declarationNames inventory sourceCertificates
    (.nil []) (by simp) sourceAdmission_eq

def collidingNames : Declarations.Names :=
  { declarationNames with eliminator := declarationNames.family }

def collisionAdmission :=
  Declarations.Registered.admitInventory PositiveInductiveSearchTreeGuest.baseRules
    PositiveInductiveSearchTreeGuest.baseDecoder PositiveInductiveSearchTreeGuest.choices 256 []
    indexing containers declarationParameters collidingNames inventory

theorem collision_refused : collisionAdmission.isNone = true :=
  Declarations.Registered.aliased_endpoints_refused PositiveInductiveSearchTreeGuest.baseRules
    PositiveInductiveSearchTreeGuest.baseDecoder PositiveInductiveSearchTreeGuest.choices 256 []
    indexing containers declarationParameters collidingNames inventory (.nil []) rfl

theorem names_distinct :
    (declarationNames.family :: inventory.map (fun constructor => declarationNames.constructor constructor.1) ++
      [declarationNames.eliminator]).Nodup := by
  have checked := declarations_admitted.names_nodup PositiveInductiveSearchTreeGuest.baseRules (by simp)
  simpa only [List.nil_append, entries, Declarations.Registered.entries_names] using checked

end Lists

namespace Vectors

abbrev I := VectorControl.interface
abbrev registry := VectorControl.registry
abbrev indexing : Indexing I Tower.Head := .unindexed (by
  change Subsingleton Unit
  infer_instance)

/-- Read the actual length variable; a payload binder does not become a Nat. -/
def lengthTerm : {context : List I.SortCode} → {n : Nat} →
    VectorControl.LengthExpr context → TermEnv I Tower.Head n context → Tower.Tm n
  | _, _, .here, environment => environment.1
  | _, _, .there expression, environment => lengthTerm expression environment.2

theorem lengthTerm_substitute {context : List I.SortCode} {n m : Nat}
    (expression : VectorControl.LengthExpr context) (environment : TermEnv I Tower.Head n context)
    (substitution : Sub Tower.Head n m) :
    subst substitution (lengthTerm expression environment) =
      lengthTerm expression (mapEnv (subst substitution) environment) := by
  induction expression with
  | here => rfl
  | there expression ih => exact ih environment.2

theorem registered_entry {name : String} {entry : IndexedPositiveContainer.Entry I}
    (registered : registry.lookup name = some entry) : entry = VectorControl.entry := by
  by_cases same : name = "Vector"
  · simpa [registry, VectorControl.registry, same] using registered.symm
  · simp [registry, VectorControl.registry, same] at registered

def registrySyntax
    (readLength : {context : List I.SortCode} → {n : Nat} →
      VectorControl.LengthExpr context → TermEnv I Tower.Head n context → Tower.Tm n)
    (readLength_substitute : ∀ {context n m}
      (expression : VectorControl.LengthExpr context) (environment : TermEnv I Tower.Head n context)
      (substitution : Sub Tower.Head n m),
      subst substitution (readLength expression environment) =
        readLength expression (mapEnv (subst substitution) environment)) :
    RegistrySyntax I registry Tower.Head where
  fieldType := by
    intro context n name entry registered output environment element
    obtain rfl := registered_entry registered
    exact NativeNaturalVectorFamilies.vecApp element (readLength output environment)
  bundleType := by
    intro context n name entry registered output environment element predicate field
    obtain rfl := registered_entry registered
    exact NativeVectorAll.allType element predicate (readLength output environment) field
  fieldType_substitute := by
    intro context n m name entry registered output environment element substitution
    obtain rfl := registered_entry registered
    change VectorControl.LengthExpr context at output
    change subst substitution (NativeNaturalVectorFamilies.vecApp element (readLength output environment)) =
      NativeNaturalVectorFamilies.vecApp (subst substitution element)
        (readLength output (mapEnv (subst substitution) environment))
    simp only [NativeNaturalVectorFamilies.vecApp, subst]
    congr 1
    exact readLength_substitute output environment substitution
  bundleType_substitute := by
    intro context n m name entry registered output environment element predicate field substitution
    obtain rfl := registered_entry registered
    change VectorControl.LengthExpr context at output
    change subst substitution
        (NativeVectorAll.allType element predicate (readLength output environment) field) =
      NativeVectorAll.allType (subst substitution element) (subst substitution predicate)
        (readLength output (mapEnv (subst substitution) environment)) (subst substitution field)
    rw [NativeVectorAll.subst_allType]
    congr 1
    exact readLength_substitute output environment substitution

def containers : RegistrySyntax I registry Tower.Head :=
  registrySyntax lengthTerm lengthTerm_substitute

def types {n : Nat} : TypeSyntax I Tower.Head n where
  dataType
    | .payload => PositiveInductiveVectorTreeGuest.answerTm
    | .length => NativeNaturalVectorFamilies.natTm
  family := PositiveInductiveVectorTreeGuest.treeTm
  constructor name := .const (.str PositiveInductiveVectorTreeGuest.treeName name)

abbrev solvedCode := ModuleSource.IndexedPositiveVectorLowering.Controls.solved.body.erase
abbrev branchCode := ModuleSource.IndexedPositiveVectorLowering.Controls.branch.body.erase

def solvedType : Tower.Tm 0 := constructorType indexing containers solvedCode types PUnit.unit
def branchType : Tower.Tm 0 := constructorType indexing containers branchCode types PUnit.unit
def solvedMethod : Tower.Tm 1 := methodType indexing containers solvedCode types (.var 0) "solved"
def branchMethod : Tower.Tm 2 := methodType indexing containers branchCode types (.var 1) "branch"

def inventory := ModuleSource.IndexedPositiveVectorLowering.Controls.family.constructors.map
  (fun constructor => (constructor.name, constructor.body.erase))

def eliminator : Tower.Tm 0 :=
  IndexedPositiveContainerGuestTypes.eliminatorType indexing containers inventory types PUnit.unit
    (.sort PositiveInductiveVectorTreeGuest.level)

theorem eliminator_exact : eliminator = PositiveInductiveVectorTreeGuest.eliminateType := by
  decide +kernel

def reversedEliminator : Tower.Tm 0 :=
  IndexedPositiveContainerGuestTypes.eliminatorType indexing containers inventory.reverse types PUnit.unit
    (.sort PositiveInductiveVectorTreeGuest.level)

theorem reversed_order_not_exact : reversedEliminator ≠ PositiveInductiveVectorTreeGuest.eliminateType := by
  decide +kernel

theorem declarations_exact :
    solvedType = PositiveInductiveVectorTreeGuest.solvedType ∧
      branchType = PositiveInductiveVectorTreeGuest.branchType ∧
      solvedMethod = PositiveInductiveVectorTreeGuest.solvedCaseType ∧
      branchMethod = PositiveInductiveVectorTreeGuest.branchCaseType := by
  decide +kernel

def declarationNames : Declarations.Names where
  family := PositiveInductiveVectorTreeGuest.treeName
  constructor name := .str PositiveInductiveVectorTreeGuest.treeName name
  eliminator := PositiveInductiveVectorTreeGuest.eliminateName

def declarationParameters : Declarations.Registered.Parameters I Tower.Head indexing 0 where
  context := .nil
  dataType := types.dataType
  indexDomain := PUnit.unit
  familyUniverse := .sort PositiveInductiveVectorTreeGuest.level
  motiveUniverse := .sort PositiveInductiveVectorTreeGuest.level

def prior : List (DeclName × Presentation.Declaration.Entry Tower.Head) :=
  [(PositiveInductiveVectorTreeGuest.answerName, ⟨PositiveInductiveVectorTreeGuest.answerType, none⟩)]

def generatedEntries :=
  Declarations.Registered.entries indexing containers declarationParameters declarationNames inventory

def entries : List (DeclName × Presentation.Declaration.Entry Tower.Head) := prior ++ generatedEntries

theorem entries_exact : entries = PositiveInductiveVectorTreeGuest.entries := by
  decide +kernel

local instance : DecidableRel PositiveInductiveVectorTreeGuest.baseRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred PositiveInductiveVectorTreeGuest.baseRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (PositiveInductiveVectorTreeGuest.baseRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel PositiveInductiveVectorTreeGuest.baseRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel PositiveInductiveVectorTreeGuest.baseRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def sourceAdmission :=
  Declarations.Registered.admitInventory PositiveInductiveVectorTreeGuest.baseRules
    PositiveInductiveVectorTreeGuest.baseDecoder PositiveInductiveVectorTreeGuest.declarationChoices
    256 prior indexing containers declarationParameters declarationNames inventory

theorem sourceAdmission_accepted : sourceAdmission.isSome = true := by
  decide +kernel

def sourceCertificates := sourceAdmission.get sourceAdmission_accepted

theorem sourceAdmission_eq : sourceAdmission = some sourceCertificates :=
  (Option.some_get sourceAdmission_accepted).symm

theorem generated_admitted :
    DeclarationAdmissionReplay.Admitted PositiveInductiveVectorTreeGuest.baseRules prior generatedEntries :=
  Declarations.Registered.admitInventory_sound PositiveInductiveVectorTreeGuest.baseRules
    PositiveInductiveVectorTreeGuest.baseDecoder PositiveInductiveVectorTreeGuest.declarationChoices
    256 prior indexing containers declarationParameters declarationNames inventory sourceCertificates sourceAdmission_eq

theorem prior_admitted : DeclarationAdmissionReplay.Admitted PositiveInductiveVectorTreeGuest.baseRules [] prior := by
  have all := PositiveInductiveVectorTreeGuest.inventory_admitted
  cases all with
  | cons fresh isUniverse formed body rest =>
      exact .cons fresh isUniverse formed body (.nil _)

theorem declarations_admitted :
    DeclarationAdmissionReplay.Admitted PositiveInductiveVectorTreeGuest.baseRules [] entries :=
  prior_admitted.append PositiveInductiveVectorTreeGuest.baseRules generated_admitted

theorem declarations_formed :
    (Presentation.Declaration.Signature.ofList entries).Formed
      PositiveInductiveVectorTreeGuest.baseRules :=
  Declarations.Registered.admitInventory_formed PositiveInductiveVectorTreeGuest.baseRules
    PositiveInductiveVectorTreeGuest.baseDecoder PositiveInductiveVectorTreeGuest.declarationChoices
    256 prior indexing containers declarationParameters declarationNames inventory sourceCertificates
    prior_admitted (by intro item member; rcases List.mem_singleton.mp member with rfl; rfl)
    sourceAdmission_eq

theorem names_distinct :
    (prior.map Prod.fst ++ (declarationNames.family ::
      inventory.map (fun constructor => declarationNames.constructor constructor.1) ++
        [declarationNames.eliminator])).Nodup :=
  Declarations.Registered.admitInventory_names PositiveInductiveVectorTreeGuest.baseRules
    PositiveInductiveVectorTreeGuest.baseDecoder PositiveInductiveVectorTreeGuest.declarationChoices
    256 prior indexing containers declarationParameters declarationNames inventory sourceCertificates
    prior_admitted sourceAdmission_eq

def wrongDataParameters : Declarations.Registered.Parameters I Tower.Head indexing 0 :=
  { declarationParameters with dataType := fun _ => PositiveInductiveVectorTreeGuest.answerTm }

def wrongDataAdmission :=
  Declarations.Registered.admitInventory PositiveInductiveVectorTreeGuest.baseRules
    PositiveInductiveVectorTreeGuest.baseDecoder PositiveInductiveVectorTreeGuest.declarationChoices
    256 prior indexing containers wrongDataParameters declarationNames inventory

theorem wrong_data_refused : wrongDataAdmission.isNone = true := by
  decide +kernel

namespace Mixed

/-- Actual source syntax with direct children before and after a nested field,
and a payload between the arity binder and its Vector use. -/
def source : ModuleSource.IndexedPositiveVectorLowering.ResolvedConstructor :=
  ⟨"mixed", .data "arity" .length (by simp)
    (.recursive "before"
      (.data "tag" .payload (by simp)
        (.vector "children" (.there .here) (.recursive "after" .result))))⟩

theorem source_roundtrip :
    ModuleSource.IndexedPositiveVectorLowering.lowerConstructor source.quote = some source :=
  ModuleSource.IndexedPositiveVectorLowering.lowerConstructor_quote source

abbrev code := source.body.erase

def constructorType : Tower.Tm 0 :=
  IndexedPositiveContainerGuestTypes.constructorType indexing containers code types PUnit.unit

/-- The comparison target is written in the object calculus independently of
the generator: Nat, child, payload, length-indexed children, child. -/
def expectedConstructorType : Tower.Tm 0 :=
  .pi NativeNaturalVectorFamilies.natTm
    (.pi PositiveInductiveVectorTreeGuest.treeTm
      (.pi PositiveInductiveVectorTreeGuest.answerTm
        (.pi (NativeNaturalVectorFamilies.vecApp PositiveInductiveVectorTreeGuest.treeTm (.var 2))
          (.pi PositiveInductiveVectorTreeGuest.treeTm PositiveInductiveVectorTreeGuest.treeTm))))

theorem constructor_exact : constructorType = expectedConstructorType := by
  decide +kernel

/-- Abstract over the actual constructor interface; no constructor or
eliminator is admitted on the strength of this control. -/
def context : Tower.Ctx 2 :=
  .snoc (.snoc .nil PositiveInductiveVectorTreeGuest.motiveType) (rename wk constructorType)

def methodTypes : TypeSyntax I Tower.Head 2 where
  dataType := types.dataType
  family := types.family
  constructor _ := .var 0

def method : Tower.Tm 2 := methodType indexing containers code methodTypes (.var 1) "mixed"

/-- All five original fields precede IH-before, the full nested bundle, and
IH-after. In particular the bundle arity is the original Nat, not the tag. -/
def expectedMethod : Tower.Tm 2 :=
  .pi NativeNaturalVectorFamilies.natTm
    (.pi PositiveInductiveVectorTreeGuest.treeTm
      (.pi PositiveInductiveVectorTreeGuest.answerTm
        (.pi (NativeNaturalVectorFamilies.vecApp PositiveInductiveVectorTreeGuest.treeTm (.var 2))
          (.pi PositiveInductiveVectorTreeGuest.treeTm
            (.pi (.app (.var 6) (.var 3))
              (.pi (NativeVectorAll.allType PositiveInductiveVectorTreeGuest.treeTm
                (.var 7) (.var 5) (.var 2))
                (.pi (.app (.var 8) (.var 2))
                  (.app (.var 9)
                    (.app (.app (.app (.app (.app (.var 8) (.var 7)) (.var 6))
                      (.var 5)) (.var 4)) (.var 3))))))))))

theorem method_exact : method = expectedMethod := by
  decide +kernel

theorem method_accepted :
    PositiveInductiveVectorTreeGuest.endpointAccepted context method
      (sortTm PositiveInductiveVectorTreeGuest.level) = true := by
  decide +kernel

theorem method_formed :
    FormationSensitive.Judgment PositiveInductiveVectorTreeGuest.inventoryRules context method
      (sortTm PositiveInductiveVectorTreeGuest.level) :=
  PositiveInductiveVectorTreeGuest.endpointAccepted_sound method_accepted

theorem method_substitution_witness :
    subst (fun index : Fin 2 => .var (wk index)) method =
      methodType indexing containers code
        (methodTypes.map (subst (fun index : Fin 2 => .var (wk index))))
        (.var (wk (1 : Fin 2))) "mixed" := by
  simpa only [method, subst] using methodType_substitute indexing containers code methodTypes
    (.var 1) "mixed" (fun index : Fin 2 => .var (wk index))

/-- A deliberately faulty output reader picks the newest data binder even
when the source expression refers to an earlier Nat. It still commutes with
substitution, so that law alone cannot certify its typing. -/
def wrongLength : {context : List I.SortCode} → {n : Nat} →
    VectorControl.LengthExpr context → TermEnv I Tower.Head n context → Tower.Tm n
  | _, _, .here, environment => environment.1
  | _, _, .there _, environment => environment.1

theorem wrongLength_substitute {context : List I.SortCode} {n m : Nat}
    (expression : VectorControl.LengthExpr context) (environment : TermEnv I Tower.Head n context)
    (substitution : Sub Tower.Head n m) :
    subst substitution (wrongLength expression environment) =
      wrongLength expression (mapEnv (subst substitution) environment) := by
  cases expression <;> rfl

def wrongContainers : RegistrySyntax I registry Tower.Head :=
  registrySyntax wrongLength wrongLength_substitute

def wrongMethod : Tower.Tm 2 :=
  methodType indexing wrongContainers code methodTypes (.var 1) "mixed"

/-- The faulty reader is indistinguishable on the earlier one-length-field
branch. The mixed source exposes the dependency that branch cannot test. -/
theorem wrong_simple_branch_agrees :
    methodType indexing wrongContainers branchCode types (.var 1) "branch" = branchMethod := by
  decide +kernel

theorem wrong_length_refused :
    PositiveInductiveVectorTreeGuest.endpointAccepted context wrongMethod
      (sortTm PositiveInductiveVectorTreeGuest.level) = false := by
  decide +kernel

end Mixed

end Vectors

namespace OrdinaryVectors

noncomputable abbrev I := IndexedInductiveNatVec.Vectors.interface Bool

/-- The ordinary grammar registers no nested containers. This instance is
used only to compare the existing Nat-indexed Vec constructor and method. -/
def registry : Registry I where
  lookup _ := none

def containers : RegistrySyntax I registry Tower.Head where
  fieldType _ _ registered := nomatch registered
  bundleType _ _ registered := nomatch registered
  fieldType_substitute _ _ registered := nomatch registered
  bundleType_substitute _ _ registered := nomatch registered

abbrev indexing := IndexedInductive.Guest.TypedControls.indexSyntax Bool
abbrev oldTypes := IndexedInductive.Guest.TypedControls.types Bool

theorem cons_constructor_exact :
    (.pi (sortTm NativeNaturalVectorFamilies.elementLevel)
      (constructorType (.indexed indexing) containers
        (ordinaryCode (parameters := 0) (IndexedInductiveNatVec.Vectors.consCode Bool))
        (TypeSyntax.ofOrdinary oldTypes) PUnit.unit) : Tower.Tm 0) =
      NativeNaturalVectorFamilies.vconsType := by
  have preserved := constructorType_ordinary indexing containers (parameters := 0)
    (IndexedInductiveNatVec.Vectors.consCode Bool) oldTypes PUnit.unit
  exact (congrArg (fun body : Tower.Tm 1 =>
    (Tm.pi (sortTm NativeNaturalVectorFamilies.elementLevel) body : Tower.Tm 0)) preserved).trans
    (IndexedInductive.Guest.TypedControls.generated_cons_type Bool)

theorem cons_method_exact :
    methodType (.indexed indexing) containers
        (ordinaryCode (parameters := 0) (IndexedInductiveNatVec.Vectors.consCode Bool))
        (TypeSyntax.ofOrdinary oldTypes.weaken.weaken) (.var 1) "Cons" =
      NativeNaturalVectorFamilies.vecConsCaseType := by
  have preserved := methodType_ordinary indexing containers (parameters := 0)
    ((IndexedInductiveNatVec.Vectors.admitted Bool).constructors.get
      (IndexedInductive.Guest.TypedControls.consOccurrence Bool)) oldTypes.weaken.weaken (.var 1)
  exact preserved.trans (IndexedInductive.Guest.TypedControls.generated_cons_method Bool)

noncomputable def eliminator : Tower.Tm 0 :=
  .pi (sortTm NativeNaturalVectorFamilies.elementLevel)
    (IndexedPositiveContainerGuestTypes.eliminatorType (.indexed indexing) containers
      (ordinaryInventory (parameters := 0) (IndexedInductiveNatVec.Vectors.admitted Bool).constructors)
      (TypeSyntax.ofOrdinary oldTypes) NativeNaturalVectorFamilies.natTm
      (.sort NativeNaturalVectorFamilies.motiveLevel))

theorem eliminator_exact : eliminator = NativeNaturalVectorFamilies.vecEliminateType := by
  have preserved := IndexedPositiveContainerGuestTypes.eliminatorType_ordinary indexing containers
    (parameters := 0) (IndexedInductiveNatVec.Vectors.admitted Bool) oldTypes
  exact (congrArg (fun term : Tower.Tm 1 =>
    (Tm.pi (sortTm NativeNaturalVectorFamilies.elementLevel) term : Tower.Tm 0)) preserved).trans
      (IndexedInductive.Guest.TypedControls.generated_eliminator_type Bool)

noncomputable def entries : List (DeclName × Presentation.Declaration.Entry Tower.Head) :=
  Declarations.Registered.entries (.indexed indexing) containers
    (Declarations.Registered.Parameters.ofOrdinary indexing
      (IndexedInductive.Guest.DeclarationControls.vectorParameters Bool))
    IndexedInductive.Guest.DeclarationControls.vectorNames
    (ordinaryInventory (parameters := 1) (IndexedInductiveNatVec.Vectors.admitted Bool).constructors)

theorem entries_exact : entries = NativeNaturalVectorFamilies.declarations.drop 4 := by
  have preserved := Declarations.Registered.entries_ordinary indexing containers
    (IndexedInductive.Guest.DeclarationControls.vectorParameters Bool)
    IndexedInductive.Guest.DeclarationControls.vectorNames (IndexedInductiveNatVec.Vectors.admitted Bool)
  exact preserved.trans (IndexedInductive.Guest.DeclarationControls.vector_entries_reference Bool)

end OrdinaryVectors

def verdicts : List (String × Bool) :=
  [("registered List inventory admits", Lists.sourceAdmission.isSome),
   ("registered Vector inventory admits after Answer", Vectors.sourceAdmission.isSome),
   ("registered declaration name collision refuses", Lists.collisionAdmission.isNone),
   ("registered Vector length type mismatch refuses", Vectors.wrongDataAdmission.isNone),
   ("generated List solved constructor", Lists.solvedType == PositiveInductiveSearchTreeGuest.solvedType),
   ("generated List nested constructor", Lists.branchType == PositiveInductiveSearchTreeGuest.branchType),
   ("generated List solved method", Lists.solvedMethod == PositiveInductiveSearchTreeGuest.solvedCaseType),
   ("generated List nested method", Lists.branchMethod == PositiveInductiveSearchTreeGuest.branchCaseType),
   ("generated Vector solved constructor", Vectors.solvedType == PositiveInductiveVectorTreeGuest.solvedType),
   ("generated Vector nested constructor", Vectors.branchType == PositiveInductiveVectorTreeGuest.branchType),
   ("generated Vector solved method", Vectors.solvedMethod == PositiveInductiveVectorTreeGuest.solvedCaseType),
   ("generated Vector nested method", Vectors.branchMethod == PositiveInductiveVectorTreeGuest.branchCaseType),
   ("generated complete List eliminator", Lists.eliminator == PositiveInductiveSearchTreeGuest.eliminateType),
   ("generated complete Vector eliminator", Vectors.eliminator == PositiveInductiveVectorTreeGuest.eliminateType),
   ("List constructor order changes its method interface", Lists.reversedEliminator != PositiveInductiveSearchTreeGuest.eliminateType),
   ("Vector constructor order changes its method interface", Vectors.reversedEliminator != PositiveInductiveVectorTreeGuest.eliminateType),
   ("mixed source retains all fields",
      (ModuleSource.IndexedPositiveVectorLowering.lowerConstructor Vectors.Mixed.source.quote).isSome),
   ("mixed constructor retains earlier length", Vectors.Mixed.constructorType == Vectors.Mixed.expectedConstructorType),
   ("mixed method retains complete ordered IHs", Vectors.Mixed.method == Vectors.Mixed.expectedMethod),
   ("mixed generated method forms", PositiveInductiveVectorTreeGuest.endpointAccepted
      Vectors.Mixed.context Vectors.Mixed.method (sortTm PositiveInductiveVectorTreeGuest.level)),
   ("simple branch cannot expose faulty length reader",
      methodType Vectors.indexing Vectors.Mixed.wrongContainers Vectors.branchCode Vectors.types
        (.var 1) "branch" == Vectors.branchMethod),
   ("mixed generated method refuses faulty length reader",
      !(PositiveInductiveVectorTreeGuest.endpointAccepted Vectors.Mixed.context Vectors.Mixed.wrongMethod
        (sortTm PositiveInductiveVectorTreeGuest.level)))]

theorem verdicts_eq_true : verdicts.all Prod.snd = true := by
  simp only [verdicts, List.all_cons, List.all_nil,
    Lists.sourceAdmission_accepted, Vectors.sourceAdmission_accepted,
    Lists.collision_refused, Vectors.wrong_data_refused,
    Vectors.Mixed.method_accepted, Vectors.Mixed.wrong_length_refused,
    Vectors.Mixed.source_roundtrip, Option.isSome_some]
  simp [Lists.declarations_exact.1, Lists.declarations_exact.2.1,
    Lists.declarations_exact.2.2.1, Lists.declarations_exact.2.2.2,
    Vectors.declarations_exact.1, Vectors.declarations_exact.2.1,
    Vectors.declarations_exact.2.2.1, Vectors.declarations_exact.2.2.2,
    Vectors.Mixed.constructor_exact, Vectors.Mixed.method_exact,
    Vectors.Mixed.wrong_simple_branch_agrees, Lists.eliminator_exact, Vectors.eliminator_exact,
    Lists.reversed_order_not_exact, Vectors.reversed_order_not_exact]

end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls

/-!
## Formation of arbitrary registered-List constructors before their admission

The actual family-only source prefix supplies the primitive family type.
Native List formation validates the container operation. No constructor or
eliminator declaration occurs in this prefix.
-/
namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.Lists.Formation
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration FormationSensitive
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestTypes
open Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuest (treeName familyType treeApp level baseRules)

def familyEntries : List (DeclName × Entry Tower.Head) := [(treeName, ⟨familyType, none⟩)]
def familySignature : Signature Tower.Head := Signature.ofList familyEntries
abbrev rules := extendRules baseRules familySignature

theorem familyType_formed : FormationSensitive.Typing baseRules .nil familyType
    (sortTm (.max (.succ level) (.succ level))) :=
  .piForm (.headType (.sort level)) (.sort _) (.headType (.sort level)) (.sort _) (.sorts _ _)

theorem prefix_admitted : DeclarationAdmissionReplay.Admitted baseRules [] familyEntries := by
  apply DeclarationAdmissionReplay.Admitted.cons (levelHead := .sort (.max (.succ level) (.succ level)))
  · decide +kernel
  · exact .sort _
  · exact familyType_formed.includeSignature (Signature.ofList [])
  · intro value impossible; cases impossible
  · exact .nil _

theorem prefix_formed : familySignature.Formed baseRules :=
  IndexedInductive.Guest.Declarations.opaque_formed baseRules familyEntries prefix_admitted
    (by intro item member; simp only [familyEntries, List.mem_singleton] at member; cases member; rfl)

theorem family_lookup : rules.constantType treeName = some familyType := by
  change combinedType baseRules familySignature treeName = _
  apply combinedType_of_signature baseRules familySignature
  · decide +kernel
  · decide +kernel

theorem family_constant {n : Nat} (ambient : Tower.Ctx n) :
    FormationSensitive.Typing rules ambient (.const treeName) (liftClosed familyType) :=
  .const family_lookup (familyType_formed.includeSignature familySignature) (.sort _)

theorem family_application {n : Nat} {ambient : Tower.Ctx n} {answer : Tower.Tm n}
    (formed : FormationSensitive.Typing rules ambient answer (sortTm level)) :
    FormationSensitive.Typing rules ambient (treeApp answer) (sortTm level) := by
  have application := FormationSensitive.Typing.appElim (family_constant ambient) formed
  simpa only [treeApp, familyType, liftClosed, rename, inst0, subst, sortTm] using application

theorem list_constant {n : Nat} (ambient : Tower.Ctx n) :
    FormationSensitive.Typing rules ambient (.const NativeIndexedFamilies.Intrinsic.listName)
      (liftClosed (NativeIndexedFamilies.IntrinsicMaps.listTypeAt level)) := by
  have typed : FormationSensitive.Typing baseRules ambient
      (.const NativeIndexedFamilies.Intrinsic.listName)
      (liftClosed (NativeIndexedFamilies.IntrinsicMaps.listTypeAt level)) :=
    FormationSensitiveNativeList.Instantiated.listConstant_typed level ambient
  exact typed.includeSignature familySignature

theorem primitives {n : Nat} {ambient : Tower.Ctx n} {answer : Tower.Tm n}
    (formed : FormationSensitive.Typing rules ambient answer (sortTm level)) :
    ConstructorPrimitives rules ambient (types answer) indexing containers PUnit.unit (.sort level) where
  isUniverse := .sort _
  productClosure := ⟨.sort (.max level level), .sorts _ _, .inr (fun _ => le_rfl)⟩
  data := fun _ => formed
  family := family_application formed
  indices := trivial
  container := by
    intro m target sigma morphism context name entry registered output environment environmentTyped element elementTyped
    exact FormationSensitiveNativeList.Instantiated.listApp_of_constant level (list_constant target) elementTyped

/-- Every registered-List constructor code forms in the family-only prefix;
no constructor or eliminator declaration is assumed. -/
theorem every_constructor_formed {parameters n : Nat}
    (code : Code I registry parameters []) {ambient : Tower.Ctx n} {answer : Tower.Tm n}
    (formed : FormationSensitive.Typing rules ambient answer (sortTm level)) :
    FormationSensitive.Typing rules ambient
      (constructorType indexing containers code (types answer) PUnit.unit) (sortTm level) := by
  have morphism : FormationSensitive.CtxMor rules ambient ambient ids := by
    intro i; simpa only [subst_ids, ids] using (FormationSensitive.Typing.var (R := rules) (Γ := ambient) i)
  simpa only [TypeSyntax.map, types, subst_ids, sortTm] using
    constructorType_formed (primitives formed) code ids morphism PUnit.unit (by trivial)

theorem source_solved_formed :
    FormationSensitive.Typing rules PositiveInductiveSearchTreeGuest.contextA
      (constructorType indexing containers solvedCode (types (.var 0)) PUnit.unit) (sortTm level) :=
  every_constructor_formed solvedCode (.var 0)

theorem source_branch_formed :
    FormationSensitive.Typing rules PositiveInductiveSearchTreeGuest.contextA
      (constructorType indexing containers branchCode (types (.var 0)) PUnit.unit) (sortTm level) := by
  simpa only [TypeSyntax.map, types, subst_ids, sortTm] using
    constructorType_formed
      (primitives (ambient := PositiveInductiveSearchTreeGuest.contextA) (answer := .var 0) (.var 0))
      branchCode ids
      (show FormationSensitive.CtxMor rules PositiveInductiveSearchTreeGuest.contextA
        PositiveInductiveSearchTreeGuest.contextA ids from
        fun index => by
          simpa only [subst_ids, ids] using
            FormationSensitive.Typing.var (R := rules) (Γ := PositiveInductiveSearchTreeGuest.contextA) index)
      PUnit.unit True.intro

theorem source_branch_judgment :
    FormationSensitive.Judgment rules PositiveInductiveSearchTreeGuest.contextA
      (constructorType indexing containers branchCode (types (.var 0)) PUnit.unit) (sortTm level) :=
  ⟨.snoc .nil (.headType (.sort level)) (.sort _), source_branch_formed⟩

def missingFamilyTypes {n : Nat} (answer : Tower.Tm n) : TypeSyntax I Tower.Head n :=
  { types answer with family := .const `Unregistered.Family }

theorem missing_family_refused {n : Nat} (ambient : Tower.Ctx n) (answer : Tower.Tm n) :
    ¬ ConstructorPrimitives rules ambient (missingFamilyTypes answer) indexing containers PUnit.unit (.sort level) := by
  intro claimed
  obtain ⟨_, _, known, _, _⟩ := claimed.family.constFormation
  have absent : rules.constantType `Unregistered.Family = none := by decide +kernel
  rw [absent] at known
  cases known

#print axioms primitives
#print axioms every_constructor_formed
#print axioms source_branch_formed
#print axioms source_branch_judgment
#print axioms missing_family_refused
end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.Lists.Formation


namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.Lists.Formation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration FormationSensitive
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedPositiveContainerGuestTypes
open Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuest (treeName branchName familyType level baseRules)

theorem source_closed_branch_formed :
    FormationSensitive.Judgment rules .nil branchType
      (sortTm (.max (.succ level) level)) := by
  exact ⟨.nil, .piForm (.headType (.sort level)) (.sort _)
    source_branch_formed (.sort _) (.sorts _ _)⟩

def branchEntries : List (DeclName × Entry Tower.Head) :=
  [(declarationNames.constructor "branch", IndexedInductive.Guest.Declarations.Registered.constructorEntry
    indexing containers declarationParameters declarationNames ("branch", branchCode))]

theorem branch_admitted : DeclarationAdmissionReplay.Admitted baseRules familyEntries branchEntries := by
  apply IndexedInductive.Guest.Declarations.Registered.constructorEntry_admitted baseRules familyEntries
    (by
      intro u v isU isV
      cases isU with
      | sort u => cases isV with
        | sort v => exact ⟨.sort (.max u v), .sort _, .sorts _ _⟩)
    indexing containers declarationParameters declarationNames ("branch", branchCode)
    (.snoc .nil (.headType (.sort level)) (.sort _))
  · change ConstructorPrimitives rules PositiveInductiveSearchTreeGuest.contextA
      (types (.var 0)) indexing containers PUnit.unit (.sort level)
    exact primitives (.var 0)
  · decide +kernel

theorem family_branch_admitted :
    DeclarationAdmissionReplay.Admitted baseRules [] (familyEntries ++ branchEntries) :=
  prefix_admitted.append baseRules branch_admitted


local instance : DecidableRel baseRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred baseRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (baseRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel baseRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel baseRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def branchChecked : Bool :=
  (IndexedInductive.Guest.Declarations.elaborate baseRules PositiveInductiveSearchTreeGuest.baseDecoder
    PositiveInductiveSearchTreeGuest.choices 256 familyEntries branchEntries).isSome

def missingFamilyChecked : Bool :=
  (IndexedInductive.Guest.Declarations.elaborate baseRules PositiveInductiveSearchTreeGuest.baseDecoder
    PositiveInductiveSearchTreeGuest.choices 256 [] branchEntries).isSome

theorem source_branch_checked : branchChecked = true := by decide +kernel

theorem missing_prefix_refused : missingFamilyChecked = false := by decide +kernel

def verdicts : List (String × Bool) :=
  [("generic constructor source branch checks at its family-only prefix", branchChecked),
   ("generic constructor source branch refuses a missing family prefix", !missingFamilyChecked)]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp [verdicts, source_branch_checked, missing_prefix_refused]

#print axioms source_closed_branch_formed
#print axioms family_branch_admitted
#print axioms source_branch_checked
#print axioms missing_prefix_refused
end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.Lists.Formation

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.Vectors.Formation
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedPositiveContainerGuestTypes
open IndexedInductive.Guest
open Mettapedia.TypeTheory.IndexedPositiveContainer
open NativeNaturalVectorFamilies
open PositiveInductiveVectorTreeGuest (answerName answerTm treeName treeTm level baseRules)

/-- Recover the actual native Vector declaration's refined formation from
an already checked native Vector context. -/
theorem nativeVecType_formed : ∃ universeHead, baseRules.isUniverse universeHead ∧
    FormationSensitive.Typing baseRules .nil
      (.pi (sortTm level) (.pi natTm (sortTm level))) (.head universeHead) := by
  obtain ⟨universeHead, _, vectorFormed⟩ :=
    NativeVectorAll.TypeFormation.formed.context.lookup_formed 0
  change FormationSensitive.Typing baseRules NativeVectorAll.TypeFormation.context
    (.app (.app (.const vecName) (.var 3)) (.var 1)) (.head universeHead) at vectorFormed
  obtain ⟨_, _, appliedHead, _, _, _⟩ := vectorFormed.appGeneration
  obtain ⟨_, _, constant, _, _, _⟩ := appliedHead.appGeneration
  obtain ⟨declaredType, declaredLevel, known, formed, isUniverse⟩ := constant.constFormation
  have actual : baseRules.constantType vecName =
      some (.pi (sortTm level) (.pi natTm (sortTm level))) := by decide +kernel
  have same := Option.some.inj (known.symm.trans actual)
  cases same
  exact ⟨declaredLevel, isUniverse, formed⟩

def familyEntries : List (DeclName × Entry Tower.Head) :=
  PositiveInductiveVectorTreeGuest.entries.take 2

def familySignature : Signature Tower.Head := Signature.ofList familyEntries
abbrev rules := extendRules baseRules familySignature

theorem prefix_admitted : DeclarationAdmissionReplay.Admitted baseRules [] familyEntries := by
  change DeclarationAdmissionReplay.Admitted baseRules []
    [(answerName, ⟨sortTm level, none⟩), (treeName, ⟨sortTm level, none⟩)]
  apply DeclarationAdmissionReplay.Admitted.cons (levelHead := .sort (.succ level))
  · decide +kernel
  · exact .sort _
  · exact .headType (.sort level)
  · intro value impossible; cases impossible
  · apply DeclarationAdmissionReplay.Admitted.cons (levelHead := .sort (.succ level))
    · decide +kernel
    · exact .sort _
    · exact .headType (.sort level)
    · intro value impossible; cases impossible
    · exact .nil _

theorem prefix_formed : familySignature.Formed baseRules :=
  IndexedInductive.Guest.Declarations.opaque_formed baseRules familyEntries prefix_admitted
    (by
      intro item member
      change item ∈ [(answerName, ⟨sortTm level, none⟩), (treeName, ⟨sortTm level, none⟩)] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl)

theorem answer_typed {n : Nat} (ambient : Tower.Ctx n) :
    FormationSensitive.Typing rules ambient answerTm (sortTm level) := by
  apply FormationSensitive.Typing.const (R := rules) (type := sortTm level) (u := .sort (.succ level))
  · decide +kernel
  · exact .headType (.sort level)
  · exact .sort _

theorem tree_typed {n : Nat} (ambient : Tower.Ctx n) :
    FormationSensitive.Typing rules ambient treeTm (sortTm level) := by
  apply FormationSensitive.Typing.const (R := rules) (type := sortTm level) (u := .sort (.succ level))
  · decide +kernel
  · exact .headType (.sort level)
  · exact .sort _

theorem nat_typed {n : Nat} (ambient : Tower.Ctx n) :
    FormationSensitive.Typing rules ambient natTm (sortTm natLevel) := by
  apply FormationSensitive.Typing.const (R := rules) (type := sortTm natLevel) (u := .sort (.succ natLevel))
  · decide +kernel
  · exact .headType (.sort natLevel)
  · exact .sort _

theorem nat_at_level {n : Nat} (ambient : Tower.Ctx n) :
    FormationSensitive.Typing rules ambient natTm (sortTm level) :=
  .cumul (nat_typed ambient) (fun _ => Nat.zero_le _)

theorem vec_constant {n : Nat} (ambient : Tower.Ctx n) :
    FormationSensitive.Typing rules ambient (.const vecName)
      (liftClosed (.pi (sortTm level) (.pi natTm (sortTm level)))) := by
  obtain ⟨universeHead, isUniverse, formed⟩ := nativeVecType_formed
  have known : baseRules.constantType vecName =
      some (.pi (sortTm level) (.pi natTm (sortTm level))) := by decide +kernel
  exact (FormationSensitive.Typing.const (Γ := ambient) known formed isUniverse).includeSignature familySignature

theorem vecApp_typed {n : Nat} {ambient : Tower.Ctx n} {element length : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing rules ambient element (sortTm level))
    (lengthTyped : FormationSensitive.Typing rules ambient length natTm) :
    FormationSensitive.Typing rules ambient (vecApp element length) (sortTm level) := by
  have applied := FormationSensitive.Typing.appElim
    (FormationSensitive.Typing.appElim (vec_constant ambient) elementTyped) lengthTyped
  simpa only [liftClosed, vecApp, rename, sortTm, natTm, inst0, subst] using applied

theorem lengthTerm_typed {R : Rules Tower.Head} {context : List I.SortCode} {n : Nat}
    {ambient : Tower.Ctx n} (expression : VectorControl.LengthExpr context)
    (environment : TermEnv I Tower.Head n context)
    (typed : EnvironmentTyped R ambient types.dataType environment) :
    FormationSensitive.Typing R ambient (lengthTerm expression environment) natTm := by
  induction expression with
  | here => exact typed.1
  | there expression ih => exact ih environment.2 typed.2

theorem primitives : ConstructorPrimitives rules .nil (types : TypeSyntax I Tower.Head 0)
    indexing containers PUnit.unit (.sort level) where
  isUniverse := .sort _
  productClosure := ⟨.sort (.max level level), .sorts _ _, .inr (fun _ => max_le le_rfl le_rfl)⟩
  data := by
    intro sort
    cases sort with
    | payload => exact answer_typed .nil
    | length => exact nat_at_level .nil
  family := tree_typed .nil
  indices := trivial
  container := by
    intro m target sigma morphism context name entry registered output environment environmentTyped element elementTyped
    obtain rfl := registered_entry registered
    change VectorControl.LengthExpr context at output
    apply vecApp_typed elementTyped
    apply lengthTerm_typed output environment
    convert environmentTyped using 1
    funext sort
    cases sort <;> rfl

theorem every_constructor_formed {parameters n : Nat}
    (code : Code I registry parameters []) (ambient : Tower.Ctx n) :
    FormationSensitive.Typing rules ambient
      (constructorType indexing containers code types PUnit.unit) (sortTm level) := by
  let sigma : Sub Tower.Head 0 n := fun i => Fin.elim0 i
  have mapped : (types : TypeSyntax I Tower.Head 0).map (subst sigma) =
      (types : TypeSyntax I Tower.Head n) := by
    dsimp only [TypeSyntax.map, types, answerTm, treeTm, subst]
    congr 1
    funext sort
    cases sort <;> rfl
  have formed := constructorType_formed (target := ambient) primitives code sigma
    (by intro i; exact Fin.elim0 i) PUnit.unit True.intro
  rw [mapped] at formed
  exact formed

theorem source_branch_formed : FormationSensitive.Judgment rules .nil branchType (sortTm level) :=
  ⟨.nil, every_constructor_formed branchCode .nil⟩

theorem source_mixed_formed : FormationSensitive.Judgment rules .nil Mixed.constructorType (sortTm level) :=
  ⟨.nil, every_constructor_formed Mixed.code .nil⟩


/-- The registered bundle operation forms for any typed predicate and actual
field; it requires no pointwise inhabitant of that predicate. -/
theorem bundle_formed {n : Nat} {ambient : Tower.Ctx n} {context : List I.SortCode}
    (name : String) (entry : Entry I) (registered : registry.lookup name = some entry)
    (output : entry.OutputExpr context) (environment : TermEnv I Tower.Head n context)
    (environmentTyped : EnvironmentTyped rules ambient types.dataType environment)
    {element predicate field : Tower.Tm n}
    (elementTyped : FormationSensitive.Typing rules ambient element (sortTm level))
    (predicateTyped : FormationSensitive.Typing rules ambient predicate (.pi element (sortTm level)))
    (fieldTyped : FormationSensitive.Typing rules ambient field
      (containers.fieldType name entry registered output environment element)) :
    FormationSensitive.Typing rules ambient
      (containers.bundleType name entry registered output environment element predicate field)
      (sortTm level) := by
  obtain rfl := registered_entry registered
  change VectorControl.LengthExpr context at output
  change FormationSensitive.Typing rules ambient field (vecApp element (lengthTerm output environment)) at fieldTyped
  exact NativeVectorAll.TypeFormation.allType_typed familySignature elementTyped predicateTyped
    (lengthTerm_typed output environment environmentTyped) fieldTyped

/-- The actual witness-free native context directly instantiates typed
substitution, independently of the registered-bundle specialization. -/
theorem allType_witness : FormationSensitive.Judgment rules NativeVectorAll.TypeFormation.context
    NativeVectorAll.TypeFormation.subject (sortTm level) := by
  refine ⟨(NativeVectorAll.TypeFormation.formed.includeSignature familySignature).context, ?_⟩
  exact NativeVectorAll.TypeFormation.allType_typed familySignature (.var 3) (.var 2) (.var 1) (.var 0)

theorem bundle_witness : FormationSensitive.Judgment rules NativeVectorAll.TypeFormation.context
    (containers.bundleType "Vector" VectorControl.entry (by rfl)
      (.here : VectorControl.LengthExpr [.length]) (.var 1, PUnit.unit)
      (.var 3) (.var 2) (.var 0)) (sortTm level) := by
  refine ⟨(NativeVectorAll.TypeFormation.formed.includeSignature familySignature).context, ?_⟩
  exact bundle_formed (context := [.length]) "Vector" VectorControl.entry (by rfl) .here (.var 1, PUnit.unit)
    ⟨.var 1, True.intro⟩ (.var 3) (.var 2) (.var 0)


def generatedBranchEntries : List (DeclName × Declaration.Entry Tower.Head) :=
  [(declarationNames.constructor "branch", Declarations.Registered.constructorEntry indexing containers
    declarationParameters declarationNames ("branch", branchCode))]

def generatedMixedEntries : List (DeclName × Declaration.Entry Tower.Head) :=
  [(declarationNames.constructor "mixed", Declarations.Registered.constructorEntry indexing containers
    declarationParameters declarationNames ("mixed", Mixed.code))]

def wrongMixedEntries : List (DeclName × Declaration.Entry Tower.Head) :=
  [(declarationNames.constructor "mixed", Declarations.Registered.constructorEntry indexing Mixed.wrongContainers
    declarationParameters declarationNames ("mixed", Mixed.code))]

theorem branch_admitted : DeclarationAdmissionReplay.Admitted baseRules familyEntries generatedBranchEntries := by
  apply Declarations.Registered.constructorEntry_admitted baseRules familyEntries
    (by intro u v hu hv; cases hu with
        | sort u => cases hv with
          | sort v => exact ⟨.sort (.max u v), .sort _, .sorts _ _⟩)
    indexing containers declarationParameters declarationNames ("branch", branchCode) .nil
  · exact primitives
  · decide +kernel

theorem mixed_admitted : DeclarationAdmissionReplay.Admitted baseRules familyEntries generatedMixedEntries := by
  apply Declarations.Registered.constructorEntry_admitted baseRules familyEntries
    (by intro u v hu hv; cases hu with
        | sort u => cases hv with
          | sort v => exact ⟨.sort (.max u v), .sort _, .sorts _ _⟩)
    indexing containers declarationParameters declarationNames ("mixed", Mixed.code) .nil
  · exact primitives
  · decide +kernel

local instance : DecidableRel baseRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred baseRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (baseRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel baseRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel baseRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def checkEntries (items : List (DeclName × Declaration.Entry Tower.Head)) : Bool :=
  (Declarations.elaborate baseRules PositiveInductiveVectorTreeGuest.baseDecoder
    PositiveInductiveVectorTreeGuest.declarationChoices 256 familyEntries items).isSome

theorem branch_checked : checkEntries generatedBranchEntries = true := by decide +kernel

theorem mixed_checked : checkEntries generatedMixedEntries = true := by decide +kernel

theorem wrong_mixed_refused : checkEntries wrongMixedEntries = false := by decide +kernel

def verdicts : List (String × Bool) :=
  [("Vector source branch checks at its family-only prefix", checkEntries generatedBranchEntries),
   ("mixed Vector source constructor checks at its family-only prefix", checkEntries generatedMixedEntries),
   ("Vector source constructor refuses a payload as its length", !(checkEntries wrongMixedEntries))]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp [verdicts, branch_checked, mixed_checked, wrong_mixed_refused]

#print axioms nativeVecType_formed
#print axioms primitives
#print axioms source_branch_formed
#print axioms source_mixed_formed
#print axioms bundle_formed
#print axioms bundle_witness
#print axioms branch_admitted
#print axioms mixed_admitted
#print axioms all_verdicts
end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.Vectors.Formation

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.Vectors.MethodFormation
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration FormationSensitive
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedPositiveContainerGuestTypes
open IndexedInductive.Guest
open Mettapedia.TypeTheory.IndexedPositiveContainer
open NativeNaturalVectorFamilies
open PositiveInductiveVectorTreeGuest (answerName answerTm treeName treeTm level baseRules)

/-- The actual family prefix followed by its generated branch constructor;
the tree eliminator is absent. -/
def prefixEntries := Formation.familyEntries ++ Formation.generatedBranchEntries

def signature : Signature Tower.Head := Signature.ofList prefixEntries
abbrev rules := extendRules baseRules signature

theorem source_type_exact :
    (Declarations.Registered.constructorEntry indexing containers declarationParameters
      declarationNames ("branch", branchCode)).type = PositiveInductiveVectorTreeGuest.branchType := by
  decide +kernel

theorem no_eliminator : rules.constantType PositiveInductiveVectorTreeGuest.eliminateName = none := by
  decide +kernel

theorem family_extension : Formation.familySignature.Extends signature :=
  Signature.ofList_extends_append Formation.familyEntries Formation.generatedBranchEntries

theorem prefix_admitted : DeclarationAdmissionReplay.Admitted baseRules [] prefixEntries :=
  Formation.prefix_admitted.append baseRules Formation.branch_admitted

theorem primitives_for (selected : Signature Tower.Head)
    (extension : Formation.familySignature.Extends selected) :
    MethodPrimitives (extendRules baseRules selected) .nil (types : TypeSyntax I Tower.Head 0)
    indexing containers PUnit.unit (.sort level) where
  resultUniverse := .sort _
  methodUniverse := .sort _
  resultBound := .inl rfl
  fieldClosure := ⟨.sort (.max level level), .sorts _ _, .inr (fun _ => max_le le_rfl le_rfl)⟩
  methodClosure := ⟨.sort (.max level level), .sorts _ _, .inr (fun _ => max_le le_rfl le_rfl)⟩
  isUniverse := .sort _
  productClosure := ⟨.sort (.max level level), .sorts _ _, .inr (fun _ => max_le le_rfl le_rfl)⟩
  data := by
    intro sort
    exact (Formation.primitives.data sort).monoSignature extension
  family := Formation.primitives.family.monoSignature extension
  indices := trivial
  container := by
    intro m target sigma morphism context name entry registered output environment environmentTyped element elementTyped
    obtain rfl := registered_entry registered
    change VectorControl.LengthExpr context at output
    have lengthTyped : Typing (extendRules baseRules selected) target (lengthTerm output environment) natTm := by
      apply Formation.lengthTerm_typed output environment
      convert environmentTyped using 1
      funext sort
      cases sort <;> rfl
    have vector := (Formation.vec_constant target).monoSignature extension
    have applied := Typing.appElim vector elementTyped
    change Typing (extendRules baseRules selected) target (vecApp element (lengthTerm output environment)) (sortTm level)
    simpa only [sortTm, liftClosed, inst0, subst, rename, vecApp] using Typing.appElim applied lengthTyped
  bundle := by
    intro m target sigma morphism context name entry registered output environment environmentTyped
      element predicate field elementTyped predicateTyped fieldTyped
    obtain rfl := registered_entry registered
    change VectorControl.LengthExpr context at output
    change Typing (extendRules baseRules selected) target field (vecApp element (lengthTerm output environment)) at fieldTyped
    apply NativeVectorAll.TypeFormation.allType_typed selected elementTyped predicateTyped
    · apply Formation.lengthTerm_typed output environment
      convert environmentTyped using 1
      funext sort
      cases sort <;> rfl
    · exact fieldTyped

theorem primitives : MethodPrimitives rules .nil (types : TypeSyntax I Tower.Head 0)
    indexing containers PUnit.unit (.sort level) :=
  primitives_for signature family_extension

def motiveContext : Tower.Ctx 1 := .snoc .nil PositiveInductiveVectorTreeGuest.motiveType

theorem motiveType_formed : Typing rules .nil PositiveInductiveVectorTreeGuest.motiveType
    (sortTm (.max level (.succ level))) :=
  Typing.piForm ((Formation.tree_typed .nil).monoSignature family_extension)
    (.sort _) (.headType (.sort level)) (.sort _) (.sorts _ _)

theorem motiveContext_formed : ContextFormation rules motiveContext :=
  .snoc .nil motiveType_formed (.sort _)

theorem branchType_formed : Typing rules .nil branchType (sortTm level) :=
  Formation.source_branch_formed.typing.monoSignature family_extension

theorem branch_constant {n : Nat} (ambient : Tower.Ctx n) :
    Typing rules ambient (.const PositiveInductiveVectorTreeGuest.branchName)
      (liftClosed branchType) := by
  apply Typing.const (R := rules) (type := branchType) (u := .sort level)
  · decide +kernel
  · exact branchType_formed
  · exact .sort _

def sourceMethod : Tower.Tm 1 :=
  methodType indexing containers branchCode types (.var 0) "branch"

def motiveSubstitution : Sub Tower.Head 0 1 := fun index => Fin.elim0 index

theorem mappedTypes_exact : (types : TypeSyntax I Tower.Head 0).map (subst motiveSubstitution) =
    (types : TypeSyntax I Tower.Head 1) := by
  dsimp only [TypeSyntax.map, types, answerTm, treeTm, subst]
  congr 1
  funext sort
  cases sort <;> rfl

theorem source_constructor_typed : Typing rules motiveContext
    (subst motiveSubstitution (types.constructor "branch"))
    (constructorType indexing containers branchCode
      (types.map (subst motiveSubstitution)) PUnit.unit) := by
  have actualType : liftClosed branchType =
      constructorType indexing containers branchCode (types : TypeSyntax I Tower.Head 1) PUnit.unit := by
    decide +kernel
  rw [mappedTypes_exact, ← actualType]
  exact branch_constant motiveContext

theorem source_method_formed : Judgment rules motiveContext sourceMethod (sortTm level) := by
  refine ⟨motiveContext_formed, ?_⟩
  have formed := methodType_formed primitives branchCode "branch" motiveSubstitution
    (by intro index; exact Fin.elim0 index) (.var 0)
    (by exact .var 0) source_constructor_typed
  simpa only [mappedTypes_exact, sourceMethod, sortTm] using formed

def closedMethod : Tower.Tm 0 := .pi PositiveInductiveVectorTreeGuest.motiveType sourceMethod

theorem closed_method_formed : Judgment rules .nil closedMethod
    (sortTm (.max (.max level (.succ level)) level)) :=
  ⟨.nil, .piForm motiveType_formed (.sort _) source_method_formed.typing (.sort _) (.sorts _ _)⟩

def methodEntries : List (DeclName × Declaration.Entry Tower.Head) :=
  [(`Generated.VectorTree.branchMethod, ⟨closedMethod, none⟩)]

theorem method_admitted : DeclarationAdmissionReplay.Admitted baseRules prefixEntries methodEntries := by
  apply DeclarationAdmissionReplay.Admitted.cons
    (levelHead := .sort (.max (.max level (.succ level)) level))
  · decide +kernel
  · exact .sort _
  · exact closed_method_formed.typing
  · intro value impossible; cases impossible
  · exact .nil _

def wrongTypes : TypeSyntax I Tower.Head 1 :=
  { types with constructor := fun _ => .const `Undeclared.VectorTree.branch }

def wrongMethod : Tower.Tm 0 := .pi PositiveInductiveVectorTreeGuest.motiveType
  (methodType indexing containers branchCode wrongTypes (.var 0) "branch")

def wrongEntries : List (DeclName × Declaration.Entry Tower.Head) :=
  [(`Generated.VectorTree.branchMethod, ⟨wrongMethod, none⟩)]

local instance : DecidableRel baseRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred baseRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (baseRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel baseRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel baseRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def checked (prior items : List (DeclName × Declaration.Entry Tower.Head)) : Bool :=
  (Declarations.elaborate baseRules PositiveInductiveVectorTreeGuest.baseDecoder
    PositiveInductiveVectorTreeGuest.declarationChoices 256 prior items).isSome

theorem source_method_checked : checked prefixEntries methodEntries = true := by decide +kernel

theorem missing_constructor_refused : checked Formation.familyEntries methodEntries = false := by decide +kernel

theorem undeclared_constructor_refused : checked prefixEntries wrongEntries = false := by decide +kernel

def verdicts : List (String × Bool) :=
  [("source method prefix contains no tree eliminator",
      (rules.constantType PositiveInductiveVectorTreeGuest.eliminateName).isNone),
   ("generic dependent source method independently checks", checked prefixEntries methodEntries),
   ("dependent source method refuses a missing constructor", !(checked Formation.familyEntries methodEntries)),
   ("dependent source method refuses an undeclared constructor", !(checked prefixEntries wrongEntries))]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp [verdicts, no_eliminator, source_method_checked, missing_constructor_refused,
    undeclared_constructor_refused]

#print axioms source_type_exact
#print axioms no_eliminator
#print axioms prefix_admitted
#print axioms primitives
#print axioms source_method_formed
#print axioms closed_method_formed
#print axioms method_admitted
#print axioms source_method_checked
#print axioms missing_constructor_refused
#print axioms undeclared_constructor_refused
end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.Vectors.MethodFormation

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.Vectors.EliminatorFormation
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration FormationSensitive
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedPositiveContainerGuestTypes
open IndexedInductive.Guest
open Mettapedia.TypeTheory.IndexedPositiveContainer
open NativeNaturalVectorFamilies
open PositiveInductiveVectorTreeGuest (answerName answerTm treeName treeTm level baseRules)
attribute [local instance] IndexedPositiveContainerGuestControls.entryDecidableEq

def solvedEntries : List (DeclName × Declaration.Entry Tower.Head) :=
  [(declarationNames.constructor "solved", Declarations.Registered.constructorEntry indexing containers
    declarationParameters declarationNames ("solved", solvedCode))]

def beforeBranch := Formation.familyEntries ++ solvedEntries

def prefixEntries := beforeBranch ++ Formation.generatedBranchEntries

def signature : Signature Tower.Head := Signature.ofList prefixEntries
abbrev rules := extendRules baseRules signature

theorem prefix_exact : prefixEntries = PositiveInductiveVectorTreeGuest.entries.take 4 := by decide +kernel

theorem no_eliminator : rules.constantType PositiveInductiveVectorTreeGuest.eliminateName = none := by decide +kernel

theorem family_extension : Formation.familySignature.Extends signature :=
  (Signature.ofList_extends_append Formation.familyEntries solvedEntries).trans
    (Signature.ofList_extends_append beforeBranch Formation.generatedBranchEntries)

theorem solved_admitted : DeclarationAdmissionReplay.Admitted baseRules Formation.familyEntries solvedEntries := by
  apply Declarations.Registered.constructorEntry_admitted baseRules Formation.familyEntries
    (by intro u v hu hv; cases hu with
        | sort u => cases hv with
          | sort v => exact ⟨.sort (.max u v), .sort _, .sorts _ _⟩)
    indexing containers declarationParameters declarationNames ("solved", solvedCode) .nil
  · exact Formation.primitives
  · decide +kernel

theorem branch_admitted : DeclarationAdmissionReplay.Admitted baseRules beforeBranch Formation.generatedBranchEntries := by
  apply Declarations.Registered.constructorEntry_admitted baseRules beforeBranch
    (by intro u v hu hv; cases hu with
        | sort u => cases hv with
          | sort v => exact ⟨.sort (.max u v), .sort _, .sorts _ _⟩)
    indexing containers declarationParameters declarationNames ("branch", branchCode) .nil
  · exact (MethodFormation.primitives_for (Signature.ofList beforeBranch)
      (Signature.ofList_extends_append Formation.familyEntries solvedEntries)).toConstructorPrimitives
  · decide +kernel

theorem prefix_admitted : DeclarationAdmissionReplay.Admitted baseRules [] prefixEntries :=
  (Formation.prefix_admitted.append baseRules solved_admitted).append baseRules branch_admitted

theorem primitives : EliminatorPrimitives rules .nil (types : TypeSyntax I Tower.Head 0)
    indexing containers PUnit.unit (.sort level) (.sort (.succ level)) (.sort (.max (.succ level) level)) where
  toMethodPrimitives := MethodFormation.primitives_for signature family_extension
  domainTyped := trivial
  levelTyping := .sort _
  resultSortBound := .inl rfl
  upperUniverse := .sort _
  motiveClosure := ⟨.sort (.max level (.succ level)), .sorts _ _,
    .inr (fun _ => max_le (Nat.le_succ _) le_rfl)⟩
  eliminatorJoin := .sorts _ _
  outputUniverse := .sort _

def closedSubstitution : Sub Tower.Head 0 0 := ids

theorem mappedTypes_exact : (types : TypeSyntax I Tower.Head 0).map (subst closedSubstitution) = types := by
  simp only [TypeSyntax.map, closedSubstitution, subst_ids]

theorem constructors_typed : ∀ item ∈ inventory, Typing rules .nil (types.constructor item.1)
    (constructorType indexing containers item.2 (types : TypeSyntax I Tower.Head 0) PUnit.unit) := by
  intro item member
  have formed := constructorType_formed (target := .nil) primitives.toConstructorPrimitives item.2 closedSubstitution
    (by intro index; exact Fin.elim0 index) PUnit.unit True.intro
  rw [mappedTypes_exact] at formed
  have known : rules.constantType (declarationNames.constructor item.1) =
      some (constructorType indexing containers item.2 (types : TypeSyntax I Tower.Head 0) PUnit.unit) := by
    change item ∈ [("solved", solvedCode), ("branch", branchCode)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  have constant := Typing.const (Γ := .nil) known formed (.sort _)
  have emptyRename : (Fin.elim0 : Ren 0 0) = idRen := funext (fun index => Fin.elim0 index)
  simpa only [liftClosed, emptyRename, rename_id, types, declarationNames] using constant

def motiveContext : Tower.Ctx 1 :=
  .snoc .nil (motiveType indexing treeTm PUnit.unit (.sort level))

theorem motive_context_formed : ContextFormation rules motiveContext := by
  apply ContextFormation.snoc .nil
  · have formed := motiveType_formed (target := .nil) primitives closedSubstitution
      (by intro index; exact Fin.elim0 index)
    simpa only [closedSubstitution, subst_ids, types, Indexing.mapDomain] using formed
  · exact .sort _

def motiveSubstitution : Sub Tower.Head 0 1 := fun index => Fin.elim0 index

theorem source_result_formed : Judgment rules motiveContext
    (resultType indexing treeTm (.var 0) PUnit.unit) (sortTm level) := by
  refine ⟨motive_context_formed, ?_⟩
  have formed := resultType_formed (target := motiveContext) primitives motiveSubstitution
    (by intro index; exact Fin.elim0 index) (.var 0) (by exact .var 0)
  simpa only [types, treeTm, subst, Indexing.mapDomain, sortTm] using formed


theorem source_eliminator_formed : Judgment rules .nil eliminator (sortTm (.max (.succ level) level)) := by
  refine ⟨.nil, ?_⟩
  have formed := eliminatorType_formed (target := .nil) primitives inventory constructors_typed closedSubstitution
    (by intro index; exact Fin.elim0 index)
  simpa only [eliminator, mappedTypes_exact, Indexing.mapDomain, sortTm] using formed

def eliminatorEntries : List (DeclName × Declaration.Entry Tower.Head) :=
  [(PositiveInductiveVectorTreeGuest.eliminateName, ⟨eliminator, none⟩)]

theorem entry_exact : eliminatorEntries = (PositiveInductiveVectorTreeGuest.entries.drop 4) := by decide +kernel

theorem eliminator_admitted : DeclarationAdmissionReplay.Admitted baseRules prefixEntries eliminatorEntries := by
  apply DeclarationAdmissionReplay.Admitted.cons (levelHead := .sort (.max (.succ level) level))
  · decide +kernel
  · exact .sort _
  · exact source_eliminator_formed.typing
  · intro value impossible; cases impossible
  · exact .nil _

theorem full_inventory_admitted :
    DeclarationAdmissionReplay.Admitted baseRules [] PositiveInductiveVectorTreeGuest.entries := by
  have admitted := prefix_admitted.append baseRules eliminator_admitted
  have same : prefixEntries ++ eliminatorEntries = PositiveInductiveVectorTreeGuest.entries := by decide +kernel
  exact same ▸ admitted

def lowerUniverseEntry : List (DeclName × Declaration.Entry Tower.Head) :=
  [(`Generated.VectorTree.LowerUniverseClaim, ⟨sortTm level, some eliminator⟩)]

local instance : DecidableRel baseRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred baseRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (baseRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel baseRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel baseRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def checked (prior items : List (DeclName × Declaration.Entry Tower.Head)) : Bool :=
  (Declarations.elaborate baseRules PositiveInductiveVectorTreeGuest.baseDecoder
    PositiveInductiveVectorTreeGuest.declarationChoices 256 prior items).isSome

theorem source_checked : checked prefixEntries eliminatorEntries = true := by decide +kernel

theorem missing_constructor_refused : checked Formation.familyEntries eliminatorEntries = false := by decide +kernel

theorem lower_universe_refused : checked prefixEntries lowerUniverseEntry = false := by decide +kernel

def verdicts : List (String × Bool) :=
  [("complete source eliminator prefix contains no eliminator",
      (rules.constantType PositiveInductiveVectorTreeGuest.eliminateName).isNone),
   ("complete source eliminator independently checks", checked prefixEntries eliminatorEntries),
   ("complete source eliminator refuses missing constructors", !(checked Formation.familyEntries eliminatorEntries)),
   ("source eliminator type refuses an insufficient universe", !(checked prefixEntries lowerUniverseEntry))]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp [verdicts, no_eliminator, source_checked, missing_constructor_refused, lower_universe_refused]

#print axioms prefix_exact
#print axioms prefix_admitted
#print axioms primitives
#print axioms constructors_typed
#print axioms source_eliminator_formed
#print axioms full_inventory_admitted
#print axioms source_checked
#print axioms missing_constructor_refused
#print axioms lower_universe_refused
end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.Vectors.EliminatorFormation


/-! ## Scoped operations for the original indexed vector source -/

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.OrdinaryVectors.IndexAdmission
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation FormationSensitive
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration
open IndexedPositiveContainerGuestTypes
open IndexedInductive
open IndexedInductiveNatVec

theorem undeclared_addition_prevents_total_indexTyping {n : Nat}
    {R : Rules Tower.Head} (ambient : Tower.Ctx n)
    (types : TypeSyntax (Vectors.interface Bool) Tower.Head n)
    (missing : R.constantType `Unadmitted.IndexAdd = none) :
    ¬ IndexTyping R ambient types (.indexed (Guest.TypedControls.indexSyntax Bool))
      NativeNaturalVectorFamilies.natTm := by
  intro allTyped
  have typed := allTyped (ids : Sub Tower.Head n n)
    (by intro index; simpa only [subst_ids, ids] using (Typing.var (R := R) (Γ := ambient) index))
    (.addition .zero .zero : Vectors.IndexExpr []) PUnit.unit True.intro
  change Typing R ambient
    (.app (.app (.const `Unadmitted.IndexAdd) NativeNaturalVectorFamilies.zeroTm)
      NativeNaturalVectorFamilies.zeroTm) NativeNaturalVectorFamilies.natTm at typed
  obtain ⟨_, _, function, _, _, _⟩ := typed.appGeneration
  obtain ⟨_, _, constant, _, _, _⟩ := function.appGeneration
  obtain ⟨_, _, known, _, _⟩ := constant.constFormation
  rw [missing] at known
  contradiction

inductive SupportedIndex : {context : List Vectors.DataSort} → Vectors.IndexExpr context → Prop where
  | zero {context} : SupportedIndex (.zero : Vectors.IndexExpr context)
  | variable {context} (reference : Vectors.LengthVariable context) : SupportedIndex (.variable reference)
  | successor {context} {expression : Vectors.IndexExpr context} :
      SupportedIndex expression → SupportedIndex (.successor expression)

theorem lookup_typed {n : Nat} {R : Rules Tower.Head} {ambient : Tower.Ctx n}
    {dataTypes : Vectors.DataSort → Tower.Tm n}
    (lengthType : dataTypes .length = NativeNaturalVectorFamilies.natTm)
    {context : List Vectors.DataSort} (reference : Vectors.LengthVariable context)
    (environment : Guest.TermEnv (Vectors.interface Bool) Tower.Head n context)
    (typed : EnvironmentTyped R ambient dataTypes environment) :
    Typing R ambient (Guest.TypedControls.lookup reference environment) NativeNaturalVectorFamilies.natTm := by
  induction reference with
  | here => exact lengthType ▸ typed.1
  | there reference ih => exact ih environment.2 typed.2

theorem supported_index_typed {n : Nat} {R : Rules Tower.Head} {ambient : Tower.Ctx n}
    {dataTypes : Vectors.DataSort → Tower.Tm n}
    (lengthType : dataTypes .length = NativeNaturalVectorFamilies.natTm)
    (zeroTyped : Typing R ambient NativeNaturalVectorFamilies.zeroTm NativeNaturalVectorFamilies.natTm)
    (successorTyped : Typing R ambient (.const NativeNaturalVectorFamilies.succName)
      (.pi NativeNaturalVectorFamilies.natTm NativeNaturalVectorFamilies.natTm))
    {context : List Vectors.DataSort} {expression : Vectors.IndexExpr context}
    (supported : SupportedIndex expression)
    (environment : Guest.TermEnv (Vectors.interface Bool) Tower.Head n context)
    (typed : EnvironmentTyped R ambient dataTypes environment) :
    Typing R ambient (Guest.TypedControls.indexTerm expression environment) NativeNaturalVectorFamilies.natTm := by
  induction supported with
  | zero => exact zeroTyped
  | «variable» reference => exact lookup_typed lengthType reference environment typed
  | successor supported ih =>
      have applied := Typing.appElim successorTyped ih
      simpa only [Guest.TypedControls.indexTerm, NativeNaturalVectorFamilies.succApp,
        NativeNaturalVectorFamilies.natTm, inst0, subst] using applied

def familyPrefix := NativeNaturalVectorFamilies.declarations.take 5
abbrev nativeRules := extendRules Tower.rules (Signature.ofList familyPrefix)

theorem natural_typed {n : Nat} (ambient : Tower.Ctx n) :
    Typing nativeRules ambient NativeNaturalVectorFamilies.natTm
      (sortTm NativeNaturalVectorFamilies.natLevel) := by
  apply Typing.const (R := nativeRules) (type := sortTm NativeNaturalVectorFamilies.natLevel)
    (u := .sort (.succ NativeNaturalVectorFamilies.natLevel))
  · decide +kernel
  · exact .headType (.sort _)
  · exact .sort _

theorem zero_typed {n : Nat} (ambient : Tower.Ctx n) :
    Typing nativeRules ambient NativeNaturalVectorFamilies.zeroTm NativeNaturalVectorFamilies.natTm := by
  apply Typing.const (R := nativeRules) (type := NativeNaturalVectorFamilies.natTm)
    (u := .sort NativeNaturalVectorFamilies.natLevel)
  · decide +kernel
  · exact natural_typed .nil
  · exact .sort _

theorem successor_typed {n : Nat} (ambient : Tower.Ctx n) :
    Typing nativeRules ambient (.const NativeNaturalVectorFamilies.succName)
      (.pi NativeNaturalVectorFamilies.natTm NativeNaturalVectorFamilies.natTm) := by
  apply Typing.const (R := nativeRules)
    (type := .pi NativeNaturalVectorFamilies.natTm NativeNaturalVectorFamilies.natTm)
    (u := .sort (.max NativeNaturalVectorFamilies.natLevel NativeNaturalVectorFamilies.natLevel))
  · decide +kernel
  · exact .piForm (natural_typed .nil) (.sort _)
      (natural_typed (.snoc .nil NativeNaturalVectorFamilies.natTm)) (.sort _) (.sorts _ _)
  · exact .sort _

def nativeContextA : Tower.Ctx 1 := .snoc .nil (sortTm NativeNaturalVectorFamilies.elementLevel)
def nativeIndexContext : Tower.Ctx 2 := .snoc nativeContextA NativeNaturalVectorFamilies.natTm

theorem native_context_formed : ContextFormation nativeRules nativeIndexContext :=
  .snoc (.snoc .nil (.headType (.sort _)) (.sort _)) (natural_typed nativeContextA) (.sort _)

def nativeDataTypes : Vectors.DataSort → Tower.Tm 2
  | .length => NativeNaturalVectorFamilies.natTm
  | .payload => .var 1

theorem native_successor_index_typed : Judgment nativeRules nativeIndexContext
    (Guest.TypedControls.indexTerm (A := Bool)
      (.successor (.variable .here) : Vectors.IndexExpr [.length]) (.var 0, PUnit.unit))
    NativeNaturalVectorFamilies.natTm := by
  refine ⟨native_context_formed, ?_⟩
  exact supported_index_typed (context := [.length])
    (expression := .successor (.variable .here)) (dataTypes := nativeDataTypes) rfl
    (zero_typed nativeIndexContext) (successor_typed nativeIndexContext)
    (.successor (.variable .here)) (.var 0, PUnit.unit) ⟨.var 0, True.intro⟩

theorem native_total_contract_refused :
    ¬ IndexTyping nativeRules nativeContextA
      (TypeSyntax.ofOrdinary (Guest.TypedControls.types Bool))
      (.indexed (Guest.TypedControls.indexSyntax Bool)) NativeNaturalVectorFamilies.natTm :=
  undeclared_addition_prevents_total_indexTyping nativeContextA _ (by decide +kernel)

def element := NativeNaturalVectorFamilies.elementLevel

noncomputable def referenceTypes : TypeSyntax (Vectors.interface Bool) Tower.Head 1 :=
  TypeSyntax.ofOrdinary (Guest.TypedControls.types Bool)

def familyTypeLevel : Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat :=
  .max (.succ element) (.max NativeNaturalVectorFamilies.natLevel (.succ element))

theorem vector_kind_formed : Typing nativeRules .nil NativeNaturalVectorFamilies.vecType
    (sortTm familyTypeLevel) := by
  apply Typing.piForm (R := nativeRules) (.headType (.sort element)) (.sort _)
  · exact .piForm (natural_typed _) (.sort _) (.headType (.sort element)) (.sort _) (.sorts _ _)
  · exact .sort _
  · exact .sorts _ _

theorem vector_family_typed : Typing nativeRules nativeContextA referenceTypes.family
    (.pi NativeNaturalVectorFamilies.natTm (sortTm element)) := by
  have known : nativeRules.constantType NativeNaturalVectorFamilies.vecName =
      some NativeNaturalVectorFamilies.vecType := by decide +kernel
  have constant := Typing.const (Γ := nativeContextA) known vector_kind_formed (show nativeRules.isUniverse (.sort familyTypeLevel) from .sort _)
  have applied := Typing.appElim constant (Typing.var (R := nativeRules) (Γ := nativeContextA) 0)
  simpa only [referenceTypes, TypeSyntax.ofOrdinary, Guest.TypedControls.types,
    NativeNaturalVectorFamilies.vecType, NativeNaturalVectorFamilies.natTm,
    sortTm, element, liftClosed, rename, inst0, subst] using applied

theorem scoped_primitives : ConstructorPrimitives nativeRules nativeContextA referenceTypes
    (.indexed (Guest.TypedControls.indexSyntax Bool)) containers NativeNaturalVectorFamilies.natTm
    (.sort element) SupportedIndex where
  isUniverse := .sort _
  productClosure := ⟨.sort (.max element element), .sorts _ _, .inr (fun _ => max_le le_rfl le_rfl)⟩
  data := by
    intro sort
    cases sort with
    | length => exact .cumul (natural_typed nativeContextA) (fun _ => Nat.zero_le _)
    | payload => exact .var 0
  family := vector_family_typed
  indices := by
    intro m target sigma morphism context expression supported environment environmentTyped
    exact supported_index_typed (dataTypes := fun sort => subst sigma (referenceTypes.dataType sort))
      rfl (zero_typed target) (successor_typed target) supported environment environmentTyped
  container := by
    intro m target sigma morphism context name entry registered
    nomatch registered

theorem cons_indices_admitted : IndicesAdmitted SupportedIndex
    (ordinaryCode (registry := registry) (parameters := 0) (Vectors.consCode Bool)) :=
  ⟨.variable (.there .here), .successor (.variable (.there .here))⟩

theorem nil_indices_admitted : IndicesAdmitted SupportedIndex
    (ordinaryCode (registry := registry) (parameters := 0) (Vectors.nilCode Bool)) := .zero

theorem source_cons_formed : Judgment nativeRules nativeContextA
    (constructorType (.indexed (Guest.TypedControls.indexSyntax Bool)) containers
      (ordinaryCode (parameters := 0) (Vectors.consCode Bool)) referenceTypes PUnit.unit)
    (sortTm element) := by
  refine ⟨by exact .snoc .nil (.headType (.sort _)) (.sort _), ?_⟩
  have formed := constructorType_formedOn scoped_primitives
    (ordinaryCode (parameters := 0) (Vectors.consCode Bool)) cons_indices_admitted ids
    (show FormationSensitive.CtxMor nativeRules nativeContextA nativeContextA ids from
      fun index => by simpa only [subst_ids, ids] using (Typing.var (R := nativeRules) (Γ := nativeContextA) index))
    PUnit.unit True.intro
  simpa only [TypeSyntax.map, referenceTypes, TypeSyntax.ofOrdinary,
    Guest.TypedControls.types, subst_ids, sortTm] using formed

theorem source_vcons_type_formed : Judgment nativeRules .nil NativeNaturalVectorFamilies.vconsType
    (sortTm (.max (.succ element) element)) := by
  have formed := Typing.piForm (R := nativeRules) (.headType (.sort element)) (.sort _) source_cons_formed.2
    (.sort _) (.sorts (.succ element) element)
  dsimp only [referenceTypes] at formed
  have comparison := constructorType_ordinary (Guest.TypedControls.indexSyntax Bool) containers
    (parameters := 0) (Vectors.consCode Bool) (Guest.TypedControls.types Bool) PUnit.unit
  rw [comparison] at formed
  exact ⟨.nil, (Guest.TypedControls.generated_cons_type Bool) ▸ formed⟩

theorem source_prefix_has_no_vector_constructors :
    nativeRules.constantType NativeNaturalVectorFamilies.vnilName = none ∧
    nativeRules.constantType NativeNaturalVectorFamilies.vconsName = none ∧
    nativeRules.constantType NativeNaturalVectorFamilies.vecEliminateName = none := by
  decide +kernel

noncomputable def sourceParameters := IndexedInductive.Guest.Declarations.Registered.Parameters.ofOrdinary
  (Guest.TypedControls.indexSyntax Bool) (Guest.DeclarationControls.vectorParameters Bool)

noncomputable def consEntry := IndexedInductive.Guest.Declarations.Registered.constructorEntry
  (.indexed (Guest.TypedControls.indexSyntax Bool)) containers sourceParameters
  Guest.DeclarationControls.vectorNames
  ("Cons", ordinaryCode (parameters := 1) (Vectors.consCode Bool))

theorem source_cons_admitted : DeclarationAdmissionReplay.Admitted Tower.rules familyPrefix
    [(NativeNaturalVectorFamilies.vconsName, consEntry)] := by
  apply IndexedInductive.Guest.Declarations.Registered.constructorEntry_admittedOn
    (admittedIndices := SupportedIndex) Tower.rules familyPrefix
    (by
      intro first second firstUniverse secondUniverse
      cases firstUniverse with
      | sort first =>
          cases secondUniverse with
          | sort second => exact ⟨.sort (.max first second), .sort _, .sorts _ _⟩)
    (.indexed (Guest.TypedControls.indexSyntax Bool)) containers sourceParameters
    Guest.DeclarationControls.vectorNames
    ("Cons", ordinaryCode (parameters := 1) (Vectors.consCode Bool))
    (show IndicesAdmitted SupportedIndex
      (ordinaryCode (registry := registry) (parameters := 1) (Vectors.consCode Bool)) from
      ⟨.variable (.there .here), .successor (.variable (.there .here))⟩)
  · exact .snoc .nil (.headType (.sort _)) (.sort _)
  · exact scoped_primitives
  · decide +kernel

attribute [local instance] IndexedPositiveContainerGuestControls.entryDecidableEq

theorem cons_entry_reference : consEntry = ⟨NativeNaturalVectorFamilies.vconsType, none⟩ := by
  decide +kernel

def sourceConsChecked := Guest.DeclarationControls.accepted familyPrefix
  [(NativeNaturalVectorFamilies.vconsName, ⟨NativeNaturalVectorFamilies.vconsType, none⟩)]

def sourceMissingNatChecked := Guest.DeclarationControls.accepted
  (NativeNaturalVectorFamilies.declarations.drop 4 |>.take 1)
  [(NativeNaturalVectorFamilies.vconsName, ⟨NativeNaturalVectorFamilies.vconsType, none⟩)]

def sourceAdditionChecked := Guest.DeclarationControls.accepted familyPrefix
  [(`IndexAdmission.Addition, ⟨.app (.app (.const `Unadmitted.IndexAdd)
    NativeNaturalVectorFamilies.zeroTm) NativeNaturalVectorFamilies.zeroTm, none⟩)]

theorem source_cons_checked : sourceConsChecked = true := by decide +kernel

theorem source_generated_cons_checked : Guest.DeclarationControls.accepted familyPrefix
    [(NativeNaturalVectorFamilies.vconsName, consEntry)] = true := by
  rw [cons_entry_reference]
  exact source_cons_checked

theorem source_missing_nat_refused : sourceMissingNatChecked = false := by decide +kernel

theorem source_addition_refused : sourceAdditionChecked = false := by decide +kernel

theorem addition_code_not_admitted :
    ¬ IndicesAdmitted SupportedIndex
      (.result (.addition .zero .zero) : Mettapedia.TypeTheory.IndexedPositiveContainer.Code
        (Vectors.interface Bool) registry 0 []) := by
  intro admitted
  cases admitted

def verdicts : List (String × Bool) :=
  [("scoped original indexed vector constructor admits", sourceConsChecked),
   ("scoped indexed constructor refuses missing Nat", !sourceMissingNatChecked),
   ("scoped indexed source refuses undeclared addition", !sourceAdditionChecked)]

theorem verdicts_eq_true : verdicts.all Prod.snd = true := by
  simp only [verdicts, List.all_cons, List.all_nil, source_cons_checked,
    source_missing_nat_refused, source_addition_refused, Bool.not_false, Bool.and_self]

#print axioms source_cons_admitted
#print axioms scoped_primitives
#print axioms source_cons_formed
#print axioms source_vcons_type_formed
#print axioms native_total_contract_refused
end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.OrdinaryVectors.IndexAdmission


/-! ## Direct source witnesses for structural formation hypotheses -/

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Declaration FormationSensitive
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestTypes
open Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest
namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls
namespace Lists.Formation
open PositiveInductiveSearchTreeGuest (level)
theorem branch_entry_formed : ∃ levelHead, rules.isUniverse levelHead ∧
    Typing rules .nil (Declarations.Registered.constructorEntry
      indexing containers declarationParameters declarationNames ("branch", branchCode)).type (.head levelHead) := by
  apply Declarations.Registered.constructorEntry_formed rules
    (by
      intro first second firstUniverse secondUniverse
      cases firstUniverse with
      | sort first => cases secondUniverse with
        | sort second => exact ⟨.sort (.max first second), .sort _, .sorts _ _⟩)
    indexing containers declarationParameters declarationNames ("branch", branchCode)
    (.snoc .nil (.headType (.sort level)) (.sort _))
  exact primitives (.var 0)
end Lists.Formation
namespace Vectors.MethodFormation
open PositiveInductiveVectorTreeGuest (level treeTm)
theorem source_body_formed : Judgment rules motiveContext sourceMethod (sortTm level) := by
  refine ⟨motiveContext_formed, ?_⟩
  have formed := methodBody_formed primitives branchCode motiveSubstitution
    (by intro index; exact Fin.elim0 index) PUnit.unit True.intro (.var 0)
    (subst motiveSubstitution (types.constructor "branch")) []
    (by exact .var 0) source_constructor_typed (by simp)
  rw [mappedTypes_exact] at formed
  have exactBody : methodBody indexing containers branchCode
      (types : TypeSyntax I Tower.Head 1) PUnit.unit (.var 0)
      (subst motiveSubstitution (types.constructor "branch")) [] = sourceMethod := by
    decide +kernel
  exact exactBody ▸ formed

theorem source_scoped_method_formed : Judgment rules motiveContext sourceMethod (sortTm level) := by
  refine ⟨motiveContext_formed, ?_⟩
  have formed := methodType_formedOn primitives branchCode (indices_unrestricted branchCode)
    "branch" motiveSubstitution (by intro index; exact Fin.elim0 index) (.var 0)
    (by exact .var 0) source_constructor_typed
  simpa only [mappedTypes_exact, sourceMethod, sortTm] using formed
end Vectors.MethodFormation
namespace Vectors.EliminatorFormation
open PositiveInductiveVectorTreeGuest (level treeTm)
theorem source_methods_formed : Judgment rules motiveContext
    (methodsType indexing containers inventory types (.var 0) PUnit.unit) (sortTm level) := by
  refine ⟨motive_context_formed, ?_⟩
  have formed := methodsType_formed (target := motiveContext) primitives inventory constructors_typed
    motiveSubstitution (by intro index; exact Fin.elim0 index) (.var 0) (by exact .var 0)
  have mapped : (types : TypeSyntax I Tower.Head 0).map (subst motiveSubstitution) =
      (types : TypeSyntax I Tower.Head 1) := MethodFormation.mappedTypes_exact
  rw [mapped] at formed
  simpa only [Indexing.mapDomain, sortTm] using formed
end Vectors.EliminatorFormation
namespace OrdinaryVectors.IndexAdmission
open IndexedInductiveNatVec

theorem source_zero_family_formed : Judgment nativeRules nativeContextA
    (NativeNaturalVectorFamilies.vecApp (.var 0) NativeNaturalVectorFamilies.zeroTm)
    (sortTm element) := by
  refine ⟨.snoc .nil (.headType (.sort _)) (.sort _), ?_⟩
  have formed := scoped_primitives.familyAt_formedOn ids
    (show FormationSensitive.CtxMor nativeRules nativeContextA nativeContextA ids from
      fun index => by simpa only [subst_ids, ids] using (Typing.var (R := nativeRules) (Γ := nativeContextA) index))
    (.zero : Vectors.IndexExpr []) SupportedIndex.zero PUnit.unit True.intro
  simpa only [Indexing.familyAt, referenceTypes, TypeSyntax.ofOrdinary, TypedControls.types,
    TypedControls.indexSyntax, TypedControls.indexTerm, subst_ids, NativeNaturalVectorFamilies.vecApp,
    sortTm] using formed

theorem eliminator_primitives : EliminatorPrimitives nativeRules nativeContextA referenceTypes
    (.indexed (TypedControls.indexSyntax Bool)) containers NativeNaturalVectorFamilies.natTm
    (.sort element) (.sort (.succ element)) (.sort (.max (.succ element) element)) SupportedIndex where
  toMethodPrimitives := {
    toConstructorPrimitives := scoped_primitives
    resultUniverse := .sort _
    methodUniverse := .sort _
    resultBound := .inl rfl
    fieldClosure := ⟨.sort (.max element element), .sorts _ _, .inr (fun _ => max_le le_rfl le_rfl)⟩
    methodClosure := ⟨.sort (.max element element), .sorts _ _, .inr (fun _ => max_le le_rfl le_rfl)⟩
    bundle := by
      intro m target sigma morphism context name entry registered
      nomatch registered }
  domainTyped := .cumul (natural_typed nativeContextA) (fun _ => Nat.zero_le _)
  levelTyping := .sort _
  resultSortBound := .inl rfl
  upperUniverse := .sort _
  motiveClosure := ⟨.sort (.max element (.succ element)), .sorts _ _,
    .inr (fun _ => max_le (Nat.le_succ _) le_rfl)⟩
  eliminatorJoin := .sorts _ _
  outputUniverse := .sort _

noncomputable def indexMotive : Tower.Tm 1 := motiveType (.indexed (TypedControls.indexSyntax Bool))
  referenceTypes.family NativeNaturalVectorFamilies.natTm (.sort element)

theorem index_motive_formed : Judgment nativeRules nativeContextA indexMotive (sortTm (.succ element)) := by
  refine ⟨.snoc .nil (.headType (.sort _)) (.sort _), ?_⟩
  have formed := motiveType_formed eliminator_primitives ids
    (show FormationSensitive.CtxMor nativeRules nativeContextA nativeContextA ids from
      fun index => by simpa only [subst_ids, ids] using (Typing.var (R := nativeRules) (Γ := nativeContextA) index))
  simpa only [indexMotive, subst_ids, Indexing.mapDomain, sortTm] using formed

noncomputable def indexedMotiveContext : Tower.Ctx 2 := .snoc nativeContextA indexMotive

def indexMotiveSubstitution : Sub Tower.Head 1 2 := fun index => .var (wk index)

theorem source_zero_predicate_typed : Judgment nativeRules indexedMotiveContext
    (.app (.var 0) NativeNaturalVectorFamilies.zeroTm)
    (.pi (NativeNaturalVectorFamilies.vecApp (.var 1) NativeNaturalVectorFamilies.zeroTm) (sortTm element)) := by
  refine ⟨.snoc index_motive_formed.1 index_motive_formed.2 (.sort _), ?_⟩
  have formed := scoped_primitives.predicateAt_typedOn (resultLevel := .sort element) indexMotiveSubstitution
    (show FormationSensitive.CtxMor nativeRules nativeContextA indexedMotiveContext indexMotiveSubstitution from
      by intro index; fin_cases index; exact .var 1)
    (.zero : Vectors.IndexExpr []) SupportedIndex.zero PUnit.unit True.intro (.var 0)
    (by
      have exactType : rename wk indexMotive =
          motiveType (.indexed (TypedControls.indexSyntax Bool))
            (subst indexMotiveSubstitution referenceTypes.family)
            (subst indexMotiveSubstitution NativeNaturalVectorFamilies.natTm) (.sort element) := by
        decide +kernel
      exact exactType ▸ (show Typing nativeRules indexedMotiveContext (.var 0)
        (rename wk indexMotive) from Typing.var (R := nativeRules) (Γ := indexedMotiveContext) 0))
  simpa [Indexing.predicateAt, Indexing.familyAt, referenceTypes, TypeSyntax.ofOrdinary,
    TypedControls.types, TypedControls.indexSyntax, TypedControls.indexTerm,
    indexMotiveSubstitution, NativeNaturalVectorFamilies.vecApp, subst, wk, sortTm] using formed
end OrdinaryVectors.IndexAdmission
end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls


namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.OrdinaryVectors.IndexAdmission
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

theorem familyPrefix_admitted : DeclarationAdmissionReplay.Admitted Tower.rules [] familyPrefix :=
  IndexedInductive.Guest.DeclarationControls.accepted_sound [] familyPrefix (by decide +kernel)

#print axioms familyPrefix_admitted
end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.OrdinaryVectors.IndexAdmission
