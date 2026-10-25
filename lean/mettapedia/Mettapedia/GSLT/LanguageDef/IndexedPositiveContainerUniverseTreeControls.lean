import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllUniverses

/-!
# Independent universes for the registered VectorTree eliminator

The existing source constructors retain their actual length expressions and
native Vector fields. Their dependent methods use the universe-instantiated
native All template: children live in U_alpha, the motive returns into U_beta,
and complete induction-evidence bundles form at max(alpha,beta).

These primitive capabilities are assembled in one declaration prefix. The
same structural formation theorem then forms the full generated eliminator,
which is ordinarily admitted before its own name is present. An independently
written interface and executable checks retain the source order and distinguish
an original child vector from its required induction evidence. Formation and
opaque admission grant no new computation rule or semantic consistency result.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerUniverseTreeControls
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration FormationSensitive RussellTarski
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedInductive.Guest IndexedPositiveContainerGuestTypes
open NativeNaturalVectorFamilies
open PositiveInductiveVectorTreeGuest (treeName treeTm answerName answerTm)
attribute [local instance] IndexedPositiveContainerGuestControls.entryDecidableEq

abbrev I := IndexedPositiveContainerGuestControls.Vectors.I
abbrev registry := IndexedPositiveContainerGuestControls.Vectors.registry
abbrev indexing := IndexedPositiveContainerGuestControls.Vectors.indexing
abbrev types {n : Nat} : TypeSyntax I Tower.Head n := IndexedPositiveContainerGuestControls.Vectors.types
abbrev baseRules := NativeVectorAll.Universes.rules
abbrev dataLevel := NativeVectorAll.Universes.dataLevel
abbrev resultLevel := NativeVectorAll.Universes.predicateLevel
abbrev methodLevel := NativeVectorAll.Universes.resultLevel

 theorem lengthTerm_mapHead (map : Tower.Head → Tower.Head)
    {context : List I.SortCode} {n : Nat}
    (expression : VectorControl.LengthExpr context)
    (environment : TermEnv I Tower.Head n context) :
    (IndexedPositiveContainerGuestControls.Vectors.lengthTerm expression environment).mapHead map =
      IndexedPositiveContainerGuestControls.Vectors.lengthTerm expression
        (mapEnv (Tm.mapHead map) environment) := by
  induction expression with
  | here => rfl
  | there expression ih => exact ih environment.2

def containersAtUniverse (level : LevelExpr Nat) : RegistrySyntax I registry Tower.Head where
  fieldType := IndexedPositiveContainerGuestControls.Vectors.containers.fieldType
  bundleType := by
    intro context n name entry registered output environment element predicate field
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    exact NativeVectorAll.Universes.Canonical.allTypeAtUniverse level element predicate
      (IndexedPositiveContainerGuestControls.Vectors.lengthTerm output environment) field
  fieldType_substitute := IndexedPositiveContainerGuestControls.Vectors.containers.fieldType_substitute
  bundleType_substitute := by
    intro context n m name entry registered output environment element predicate field sigma
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    change subst sigma (NativeVectorAll.Universes.Canonical.allTypeAtUniverse level element predicate
      (IndexedPositiveContainerGuestControls.Vectors.lengthTerm output environment) field) = _
    rw [NativeVectorAll.Universes.Canonical.substitute_allTypeAtUniverse]
    congr 1
    exact IndexedPositiveContainerGuestControls.Vectors.lengthTerm_substitute output environment sigma

theorem containers_substLevels (theta : Nat → LevelExpr Nat) (level : LevelExpr Nat) :
    (containersAtUniverse level).HeadNatural
      (containersAtUniverse (LevelExpr.subst theta level)) (substLevelsHead theta) where
  field := by
    intro context n name entry registered output environment element
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    change (NativeNaturalVectorFamilies.vecApp element
      (IndexedPositiveContainerGuestControls.Vectors.lengthTerm output environment)).mapHead
        (substLevelsHead theta) = _
    simp only [containersAtUniverse, IndexedPositiveContainerGuestControls.Vectors.containers,
      IndexedPositiveContainerGuestControls.Vectors.registrySyntax,
      NativeNaturalVectorFamilies.vecApp, Tm.mapHead]
    congr 1
    exact lengthTerm_mapHead (substLevelsHead theta) output environment
  bundle := by
    intro context n name entry registered output environment element predicate field
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    change substLevelsTm theta
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse level element predicate
        (IndexedPositiveContainerGuestControls.Vectors.lengthTerm output environment) field) = _
    rw [NativeVectorAll.Universes.Canonical.substLevels_allTypeAtUniverse]
    simp only [containersAtUniverse, substLevelsTm]
    congr 1
    exact lengthTerm_mapHead (substLevelsHead theta) output environment

def containers : RegistrySyntax I registry Tower.Head :=
  containersAtUniverse methodLevel

def constructorPrefix := PositiveInductiveVectorTreeGuest.entries.take 4
abbrev signature := Signature.ofList constructorPrefix
abbrev rules := extendRules baseRules signature

local instance : DecidableRel baseRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred baseRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (baseRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel baseRules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel baseRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

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

def prefixAccepted := (IndexedInductive.Guest.Declarations.elaborate baseRules NativeVectorAll.Universes.decoder
  PositiveInductiveVectorTreeGuest.declarationChoices 256 [] constructorPrefix).isSome

theorem prefix_accepted : prefixAccepted = true := by decide +kernel

theorem prefix_admitted : DeclarationAdmissionReplay.Admitted baseRules [] constructorPrefix := by
  obtain ⟨certificates, produced⟩ := Option.isSome_iff_exists.mp prefix_accepted
  exact IndexedInductive.Guest.Declarations.elaborate_sound baseRules NativeVectorAll.Universes.decoder
    PositiveInductiveVectorTreeGuest.declarationChoices 256 [] constructorPrefix certificates produced

theorem nativeVecType_formed : ∃ universeHead, baseRules.isUniverse universeHead ∧
    Typing baseRules .nil NativeNaturalVectorFamilies.vecType (.head universeHead) := by
  obtain ⟨universeHead, _, vectorFormed⟩ := NativeVectorAll.Universes.formed.context.lookup_formed 0
  change Typing baseRules NativeVectorAll.Universes.context
    (.app (.app (.const vecName) (.var 3)) (.var 1)) (.head universeHead) at vectorFormed
  obtain ⟨_, _, appliedHead, _, _, _⟩ := vectorFormed.appGeneration
  obtain ⟨_, _, constant, _, _, _⟩ := appliedHead.appGeneration
  obtain ⟨declaredType, declaredLevel, known, formed, isUniverse⟩ := constant.constFormation
  have actual : baseRules.constantType vecName = some NativeNaturalVectorFamilies.vecType := by decide +kernel
  have same := Option.some.inj (known.symm.trans actual)
  cases same
  exact ⟨declaredLevel, isUniverse, formed⟩

theorem answer_typed {n : Nat} (ambient : Tower.Ctx n) : Typing rules ambient answerTm (sortTm dataLevel) := by
  apply Typing.const (R := rules) (type := sortTm dataLevel) (u := .sort (.succ dataLevel))
  · decide +kernel
  · exact .headType (.sort _)
  · exact .sort _

theorem tree_typed {n : Nat} (ambient : Tower.Ctx n) : Typing rules ambient treeTm (sortTm dataLevel) := by
  apply Typing.const (R := rules) (type := sortTm dataLevel) (u := .sort (.succ dataLevel))
  · decide +kernel
  · exact .headType (.sort _)
  · exact .sort _

theorem natural_typed {n : Nat} (ambient : Tower.Ctx n) : Typing rules ambient natTm (sortTm natLevel) := by
  apply Typing.const (R := rules) (type := sortTm natLevel) (u := .sort (.succ natLevel))
  · decide +kernel
  · exact .headType (.sort _)
  · exact .sort _

theorem vec_constant {n : Nat} (ambient : Tower.Ctx n) : Typing rules ambient (.const vecName)
    (liftClosed NativeNaturalVectorFamilies.vecType) := by
  obtain ⟨universeHead, isUniverse, formed⟩ := nativeVecType_formed
  have known : baseRules.constantType vecName = some NativeNaturalVectorFamilies.vecType := by decide +kernel
  exact (Typing.const (Γ := ambient) known formed isUniverse).includeSignature signature

theorem constructor_primitives : ConstructorPrimitives rules .nil (types : TypeSyntax I Tower.Head 0)
    indexing containers PUnit.unit (.sort dataLevel) where
  isUniverse := .sort _
  productClosure := ⟨.sort (.max dataLevel dataLevel), .sorts _ _, .inr (fun _ => max_le le_rfl le_rfl)⟩
  data := by
    intro sort
    cases sort with
    | payload => exact answer_typed .nil
    | length => exact .cumul (natural_typed .nil) (fun _ => Nat.zero_le _)
  family := tree_typed .nil
  indices := trivial
  container := by
    intro m target sigma morphism context name entry registered output environment environmentTyped element elementTyped
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    have lengthTyped : Typing rules target (IndexedPositiveContainerGuestControls.Vectors.lengthTerm output environment) natTm := by
      apply IndexedPositiveContainerGuestControls.Vectors.Formation.lengthTerm_typed output environment
      convert environmentTyped using 1
      funext sort
      cases sort <;> rfl
    have applied := Typing.appElim (Typing.appElim (vec_constant target) elementTyped) lengthTyped
    change Typing rules target (vecApp element (IndexedPositiveContainerGuestControls.Vectors.lengthTerm output environment)) (sortTm dataLevel)
    have sameLevel : NativeNaturalVectorFamilies.elementLevel = dataLevel := rfl
    rw [sameLevel] at applied
    simpa only [vecApp, vecType, sortTm, liftClosed, rename, inst0, subst] using applied

def motiveBound : LevelExpr Nat := .max dataLevel (.succ resultLevel)
def outputBound : LevelExpr Nat := .max motiveBound methodLevel

theorem primitives : EliminatorPrimitives rules .nil (types : TypeSyntax I Tower.Head 0)
    indexing containers PUnit.unit (.sort dataLevel) (.sort motiveBound) (.sort outputBound)
    unrestrictedIndices (.sort resultLevel) (.sort methodLevel) (.sort (.succ resultLevel)) where
  toConstructorPrimitives := constructor_primitives
  resultUniverse := .sort _
  methodUniverse := .sort _
  resultBound := .inr (fun _ => le_max_right _ _)
  fieldClosure := ⟨.sort (.max dataLevel methodLevel), .sorts _ _, .inr (fun _ => max_le (le_max_left _ _) le_rfl)⟩
  methodClosure := ⟨.sort (.max methodLevel methodLevel), .sorts _ _, .inr (fun _ => max_le le_rfl le_rfl)⟩
  bundle := by
    intro m target sigma morphism context name entry registered output environment environmentTyped
      element predicate field elementTyped predicateTyped fieldTyped
    obtain rfl := IndexedPositiveContainerGuestControls.Vectors.registered_entry registered
    change Typing rules target field (vecApp element (IndexedPositiveContainerGuestControls.Vectors.lengthTerm output environment)) at fieldTyped
    apply NativeVectorAll.Universes.allType_typed signature elementTyped predicateTyped
    · apply IndexedPositiveContainerGuestControls.Vectors.Formation.lengthTerm_typed output environment
      convert environmentTyped using 1
      funext sort
      cases sort <;> rfl
    · exact fieldTyped
  domainTyped := trivial
  levelTyping := .sort _
  resultSortBound := .inr (fun _ => le_max_right _ _)
  upperUniverse := .sort _
  motiveClosure := ⟨.sort (.max dataLevel motiveBound), .sorts _ _, .inr (fun _ => max_le (le_max_left _ _) le_rfl)⟩
  eliminatorJoin := .sorts _ _
  outputUniverse := .sort _

def inventory := IndexedPositiveContainerGuestControls.Vectors.inventory

theorem constructors_typed : ∀ item ∈ inventory, Typing rules .nil (types.constructor item.1)
    (constructorType indexing containers item.2 types PUnit.unit) := by
  intro item member
  change item ∈ [("solved", IndexedPositiveContainerGuestControls.Vectors.solvedCode),
    ("branch", IndexedPositiveContainerGuestControls.Vectors.branchCode)] at member
  rcases List.mem_cons.mp member with rfl | member
  · have member : (PositiveInductiveVectorTreeGuest.solvedName,
        (⟨PositiveInductiveVectorTreeGuest.solvedType, none⟩ : Declaration.Entry Tower.Head)) ∈ constructorPrefix := by
      decide +kernel
    obtain ⟨_, level, isUniverse, formed, _⟩ :=
      DeclarationAdmissionReplay.Admitted.member_typed baseRules prefix_admitted member
    have known : rules.constantType PositiveInductiveVectorTreeGuest.solvedName =
        some PositiveInductiveVectorTreeGuest.solvedType := by decide +kernel
    have constant := Typing.const (Γ := (.nil : Tower.Ctx 0)) known formed isUniverse
    convert constant using 1 <;> decide +kernel
  · rcases List.mem_singleton.mp member with rfl
    have member : (PositiveInductiveVectorTreeGuest.branchName,
        (⟨PositiveInductiveVectorTreeGuest.branchType, none⟩ : Declaration.Entry Tower.Head)) ∈ constructorPrefix := by
      decide +kernel
    obtain ⟨_, level, isUniverse, formed, _⟩ :=
      DeclarationAdmissionReplay.Admitted.member_typed baseRules prefix_admitted member
    have known : rules.constantType PositiveInductiveVectorTreeGuest.branchName =
        some PositiveInductiveVectorTreeGuest.branchType := by decide +kernel
    have constant := Typing.const (Γ := (.nil : Tower.Ctx 0)) known formed isUniverse
    convert constant using 1 <;> decide +kernel

/-- The original branch directly instantiates the constructor inventory. -/
theorem source_branch_typed : Typing rules .nil
    (.const PositiveInductiveVectorTreeGuest.branchName) PositiveInductiveVectorTreeGuest.branchType := by
  have typed := constructors_typed
    ("branch", IndexedPositiveContainerGuestControls.Vectors.branchCode)
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  convert typed using 1 <;> decide +kernel

def generatedType : Tower.Tm 0 := eliminatorType indexing containers inventory types PUnit.unit (.sort resultLevel)


/-- The complete source eliminator, including its registered bundle, commutes
with arbitrary universe instantiation. The source order is retained. -/
theorem generated_type_substLevels (theta : Nat → LevelExpr Nat) :
    substLevelsTm theta generatedType =
      eliminatorType indexing (containersAtUniverse (LevelExpr.subst theta methodLevel))
        inventory (types.map (substLevelsTm theta)) PUnit.unit
        (.sort (LevelExpr.subst theta resultLevel)) :=
  eliminatorType_mapHead indexing (substLevelsHead theta) (by trivial)
    (containers_substLevels theta methodLevel) inventory types PUnit.unit (.sort resultLevel)

/-- A closed nonidentity instance retains the mapped data syntax explicitly. -/
theorem generated_collapse_naturality :
    substLevelsTm (fun _ => .const 0) generatedType =
      eliminatorType indexing
        (containersAtUniverse (LevelExpr.subst (fun _ => .const 0) methodLevel))
        inventory ((types : TypeSyntax I Tower.Head 0).map
          (substLevelsTm (fun _ => .const 0))) PUnit.unit
        (.sort (LevelExpr.subst (fun _ => .const 0) resultLevel)) :=
  eliminatorType_mapHead indexing (substLevelsHead (fun _ => .const 0)) (by trivial)
    (containers_substLevels (fun _ => .const 0) methodLevel) _ _ _ _

/-- The actual branch method retains its complete nested induction bundle. -/
theorem branch_method_collapse_exact :
    substLevelsTm (fun _ => .const 0)
      (methodType indexing containers IndexedPositiveContainerGuestControls.Vectors.branchCode
        (types : TypeSyntax I Tower.Head 1) (.var 0) "branch") =
      methodType indexing
        (containersAtUniverse (LevelExpr.subst (fun _ => .const 0) methodLevel))
        IndexedPositiveContainerGuestControls.Vectors.branchCode
        (types.map (substLevelsTm (fun _ => .const 0))) (.var 0) "branch" :=
  methodBody_mapHead indexing (substLevelsHead (fun _ => .const 0)) (by trivial)
    (containers_substLevels (fun _ => .const 0) methodLevel)
    IndexedPositiveContainerGuestControls.Vectors.branchCode
    (types : TypeSyntax I Tower.Head 1) PUnit.unit (.var 0)
      (types.constructor "branch") []

/-- The actual nested branch witnesses constructor naturality under a
nonidentity universe instantiation and the same registered container. -/
theorem branch_collapse_exact :
    substLevelsTm (fun _ => .const 0)
      (constructorType indexing containers IndexedPositiveContainerGuestControls.Vectors.branchCode
        (types : TypeSyntax I Tower.Head 0) PUnit.unit) =
      constructorType indexing
        (containersAtUniverse (LevelExpr.subst (fun _ => .const 0) methodLevel))
        IndexedPositiveContainerGuestControls.Vectors.branchCode
        (types.map (substLevelsTm (fun _ => .const 0))) PUnit.unit :=
  constructorType_mapHead indexing (substLevelsHead (fun _ => .const 0)) (by trivial)
    (containers_substLevels (fun _ => .const 0) methodLevel) _ _ _

/-- The concrete source family and data types contain no universe heads. -/
theorem types_substLevels (theta : Nat → LevelExpr Nat) {n : Nat} :
    (types : TypeSyntax I Tower.Head n).map (substLevelsTm theta) = types := by
  dsimp only [types, IndexedPositiveContainerGuestControls.Vectors.types, TypeSyntax.map]
  congr 1
  funext sort
  cases sort <;> rfl

def collapsedType : Tower.Tm 0 :=
  eliminatorType indexing
    (containersAtUniverse (LevelExpr.subst (fun _ => .const 0) methodLevel))
    inventory types PUnit.unit (.sort (.const 0))

/-- A concrete nonidentity instance of the whole source-eliminator law. -/
theorem generated_collapse_exact :
    substLevelsTm (fun _ => .const 0) generatedType = collapsedType := by
  unfold collapsedType
  rw [generated_type_substLevels, types_substLevels]
  rfl

/-- Retaining the original annotation is a different generated program. -/
theorem generated_annotation_changes : generatedType ≠ collapsedType := by
  decide +kernel

def generatedCollapseChecked :=
  decide (substLevelsTm (fun _ => .const 0) generatedType = collapsedType)
def generatedAnnotationChangesChecked := decide (generatedType ≠ collapsedType)

theorem generated_collapse_checked : generatedCollapseChecked = true := by decide +kernel
theorem generated_annotation_changes_checked : generatedAnnotationChangesChecked = true := by decide +kernel

theorem generated_type_formed : Judgment rules .nil generatedType (sortTm outputBound) := by
  refine ⟨.nil, ?_⟩
  have formed := eliminatorType_formedOn (target := (.nil : Tower.Ctx 0)) primitives inventory (by intro item _; exact indices_unrestricted item.2)
    constructors_typed ids (by intro index; exact Fin.elim0 index)
  have exactTypes : (types : TypeSyntax I Tower.Head 0).map (subst ids) = types := by
    simp only [TypeSyntax.map, types, IndexedPositiveContainerGuestControls.Vectors.types, subst_ids]
  rw [exactTypes] at formed
  exact formed

/-- The reference branch is written independently of the registered-code generator. -/
def expectedBranch : Tower.Tm 2 := .pi natTm
  (.pi (vecApp treeTm (.var 0))
    (.pi (NativeVectorAll.Universes.allType treeTm (.var 3) (.var 1) (.var 0))
      (.app (.var 4) (PositiveInductiveVectorTreeGuest.branchApp (.var 2) (.var 1)))))

def expectedType : Tower.Tm 0 := .pi (.pi treeTm (sortTm resultLevel))
  (.pi PositiveInductiveVectorTreeGuest.solvedCaseType
    (.pi expectedBranch PositiveInductiveVectorTreeGuest.eliminateResultType))

theorem source_type_exact : generatedType = expectedType := by decide +kernel

theorem source_eliminator_absent : rules.constantType PositiveInductiveVectorTreeGuest.eliminateName = none := by
  decide +kernel

theorem eliminator_admitted : DeclarationAdmissionReplay.Admitted baseRules constructorPrefix
    [(PositiveInductiveVectorTreeGuest.eliminateName, ⟨generatedType, none⟩)] := by
  apply DeclarationAdmissionReplay.Admitted.cons source_eliminator_absent
    (show baseRules.isUniverse (.sort outputBound) from .sort _) generated_type_formed.typing
  · intro value impossible; cases impossible
  · exact .nil _

def sourceEntries := constructorPrefix ++ [(PositiveInductiveVectorTreeGuest.eliminateName,
  (⟨generatedType, none⟩ : Declaration.Entry Tower.Head))]

theorem source_inventory_admitted : DeclarationAdmissionReplay.Admitted baseRules [] sourceEntries :=
  prefix_admitted.append baseRules eliminator_admitted

def checked (prior entries : List (DeclName × Declaration.Entry Tower.Head)) :=
  (IndexedInductive.Guest.Declarations.elaborate baseRules NativeVectorAll.Universes.decoder
    PositiveInductiveVectorTreeGuest.declarationChoices 256 prior entries).isSome

def checkedEntry : List (DeclName × Declaration.Entry Tower.Head) :=
  [(PositiveInductiveVectorTreeGuest.eliminateName, ⟨expectedType, none⟩)]

theorem source_checked : checked constructorPrefix checkedEntry = true := by decide +kernel

/-- The checked reference interface is the exact generated source entry. -/
theorem source_generated_checked : checked constructorPrefix
    [(PositiveInductiveVectorTreeGuest.eliminateName, ⟨generatedType, none⟩)] = true := by
  rw [source_type_exact]
  exact source_checked

theorem missing_constructor_refused : checked (constructorPrefix.take 2) checkedEntry = false := by decide +kernel

def wrongBundleBranch : Tower.Tm 2 := .pi natTm
  (.pi (vecApp treeTm (.var 0))
    (.pi (vecApp treeTm (.var 1))
      (.app (.var 4) (PositiveInductiveVectorTreeGuest.branchApp (.var 2) (.var 1)))))

theorem bundle_cannot_be_replaced_by_children : expectedBranch ≠ wrongBundleBranch := by decide +kernel

def bundleContextP : Tower.Ctx 1 := .snoc .nil (.pi treeTm (sortTm resultLevel))
def bundleContextPZ : Tower.Ctx 2 := .snoc bundleContextP PositiveInductiveVectorTreeGuest.solvedCaseType
def bundleContextPZN : Tower.Ctx 3 := .snoc bundleContextPZ natTm
def bundleContext : Tower.Ctx 4 := .snoc bundleContextPZN (vecApp treeTm (.var 0))

def endpointDecoder := DeclarationConversionCode.ofList baseRules NativeVectorAll.Universes.decoder constructorPrefix

def endpointAccepted {n : Nat} (ambient : Tower.Ctx n) (term type : Tower.Tm n) :=
  (FormationSensitiveElaboration.elaborate rules endpointDecoder PositiveInductiveVectorTreeGuest.inventoryChoices
    256 ambient term type).isSome

theorem endpointAccepted_sound {n : Nat} {ambient : Tower.Ctx n} {term type : Tower.Tm n}
    (accepted : endpointAccepted ambient term type = true) : Judgment rules ambient term type := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp accepted
  exact FormationSensitiveElaboration.elaborate_sound rules endpointDecoder
    PositiveInductiveVectorTreeGuest.inventoryChoices 256 ambient term type submission produced

def childVectorType : Tower.Tm 4 := vecApp treeTm (.var 1)
def sourceBundleType : Tower.Tm 4 := NativeVectorAll.Universes.allType treeTm (.var 3) (.var 1) (.var 0)

theorem original_children_typed : endpointAccepted bundleContext (.var 0) childVectorType = true := by decide +kernel

theorem original_children_not_bundle : endpointAccepted bundleContext (.var 0) sourceBundleType = false := by decide +kernel

theorem source_bundle_formed : Judgment rules bundleContext sourceBundleType (sortTm methodLevel) := by
  refine ⟨(endpointAccepted_sound original_children_typed).context, ?_⟩
  apply NativeVectorAll.Universes.allType_typed signature (tree_typed bundleContext)
  · convert (Typing.var (R := rules) (Γ := bundleContext) (3 : Fin 4)) using 1
    decide +kernel
  · convert (Typing.var (R := rules) (Γ := bundleContext) (1 : Fin 4)) using 1
    decide +kernel
  · convert (Typing.var (R := rules) (Γ := bundleContext) (0 : Fin 4)) using 1
    decide +kernel

def verdicts : List (String × Bool) :=
  [("nested independent-universe source prefix admits", prefixAccepted),
   ("nested independent-universe eliminator checks", checked constructorPrefix checkedEntry),
   ("nested independent-universe eliminator refuses missing constructors", !(checked (constructorPrefix.take 2) checkedEntry)),
   ("nested source children retain their original vector type", endpointAccepted bundleContext (.var 0) childVectorType),
   ("nested source children cannot replace induction evidence", !(endpointAccepted bundleContext (.var 0) sourceBundleType)),
   ("nested generated eliminator commutes with universe instantiation", generatedCollapseChecked),
   ("nested universe instantiation retains a changed annotation", generatedAnnotationChangesChecked)]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp only [verdicts, prefix_accepted, source_checked, missing_constructor_refused,
    original_children_typed, original_children_not_bundle, generated_collapse_checked,
    generated_annotation_changes_checked, Bool.not_false, List.all_cons,
    List.all_nil, Bool.and_self]

#print axioms original_children_typed
#print axioms original_children_not_bundle
#print axioms source_bundle_formed

#print axioms prefix_admitted
#print axioms constructors_typed
#print axioms source_branch_typed
#print axioms generated_type_formed
#print axioms source_type_exact
#print axioms source_eliminator_absent
#print axioms eliminator_admitted
#print axioms source_inventory_admitted
#print axioms source_checked
#print axioms source_generated_checked
#print axioms missing_constructor_refused
#print axioms bundle_cannot_be_replaced_by_children

#print axioms constructor_primitives
#print axioms primitives
end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerUniverseTreeControls
