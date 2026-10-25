import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FormationSensitiveLevelInstantiation

/-!
# Independent universes for the generated indexed Vector eliminator

The original Nat-indexed Vector source forms its generated eliminator type in
an admitted prefix containing its constructors and no Vector eliminator.
The data universe and motive-result universe remain independent parameters.
Methods use their maximum; quantification over the motive additionally includes
the successor of its result universe. Formation yields ordinary opaque
admission, without granting an iota rule or a semantic consistency theorem.

Both universe orderings have source instances and independent executable
checks. A high-result instance accepts the required successor bound and
refuses its omission. Missing constructor declarations also refuse.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerUniverseControls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration FormationSensitive RussellTarski
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedPositiveContainerGuestTypes IndexedInductive IndexedInductiveNatVec
open IndexedPositiveContainerGuestControls.OrdinaryVectors
open IndexedPositiveContainerGuestControls.OrdinaryVectors.IndexAdmission
attribute [local instance] Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.entryDecidableEq

/-- The actual Nat index interpretation retains every source variable and operation. -/
theorem indexSyntax_headNatural (map : Tower.Head → Tower.Head) :
    (Indexing.indexed (Guest.TypedControls.indexSyntax Bool)).HeadNatural map := by
  intro n context expression environment
  exact Guest.TypedControls.indexTerm_mapHead map expression environment

/-- Ordinary Vec has no registered nested container. Its indexed source syntax
is handled separately by indexSyntax_headNatural. -/
theorem containers_headNatural (map : Tower.Head → Tower.Head) :
    containers.HeadNatural containers map where
  field := by intro context n name entry registered; nomatch registered
  bundle := by intro context n name entry registered; nomatch registered

/-- The existing source prefix contains both vector constructors and no vector eliminator. -/
def constructorPrefix := NativeNaturalVectorFamilies.declarations.take 7
abbrev rules := extendRules Tower.rules (Signature.ofList constructorPrefix)

theorem prefix_admitted : DeclarationAdmissionReplay.Admitted Tower.rules [] constructorPrefix :=
  Guest.DeclarationControls.accepted_sound [] constructorPrefix (by decide +kernel)

theorem family_extension : (Signature.ofList familyPrefix).Extends (Signature.ofList constructorPrefix) := by
  have same : constructorPrefix = familyPrefix ++ (NativeNaturalVectorFamilies.declarations.drop 5).take 2 := by
    decide +kernel
  rw [same]
  exact Signature.ofList_extends_append _ _

def dataLevel := NativeNaturalVectorFamilies.elementLevel
def resultLevel := NativeNaturalVectorFamilies.motiveLevel
def methodLevel : LevelExpr Nat := .max dataLevel resultLevel
def motiveLevel : LevelExpr Nat := .max dataLevel (.succ resultLevel)
def outputLevel : LevelExpr Nat := .max motiveLevel methodLevel

theorem constructor_primitives : ConstructorPrimitives rules nativeContextA referenceTypes
    (.indexed (Guest.TypedControls.indexSyntax Bool)) containers NativeNaturalVectorFamilies.natTm
    (.sort dataLevel) SupportedIndex where
  isUniverse := .sort _
  productClosure := ⟨.sort (.max dataLevel dataLevel), .sorts _ _, .inr (fun _ => max_le le_rfl le_rfl)⟩
  data := fun sort => (scoped_primitives.data sort).monoSignature family_extension
  family := vector_family_typed.monoSignature family_extension
  indices := by
    intro m target sigma morphism context expression supported environment environmentTyped
    exact supported_index_typed (dataTypes := fun sort => subst sigma (referenceTypes.dataType sort))
      rfl ((zero_typed target).monoSignature family_extension)
      ((successor_typed target).monoSignature family_extension) supported environment environmentTyped
  container := by
    intro m target sigma morphism context name entry registered
    nomatch registered

theorem primitives : EliminatorPrimitives rules nativeContextA referenceTypes
    (.indexed (Guest.TypedControls.indexSyntax Bool)) containers NativeNaturalVectorFamilies.natTm
    (.sort dataLevel) (.sort motiveLevel) (.sort outputLevel) SupportedIndex
    (.sort resultLevel) (.sort methodLevel) (.sort (.succ resultLevel)) where
  toConstructorPrimitives := constructor_primitives
  resultUniverse := .sort _
  methodUniverse := .sort _
  resultBound := .inr (fun _ => le_max_right _ _)
  fieldClosure := ⟨.sort (.max dataLevel methodLevel), .sorts _ _,
    .inr (fun _ => max_le (le_max_left _ _) le_rfl)⟩
  methodClosure := ⟨.sort (.max methodLevel methodLevel), .sorts _ _,
    .inr (fun _ => max_le le_rfl le_rfl)⟩
  bundle := by
    intro m target sigma morphism context name entry registered
    nomatch registered
  domainTyped := .cumul ((natural_typed nativeContextA).monoSignature family_extension) (fun _ => Nat.zero_le _)
  levelTyping := .sort _
  resultSortBound := .inr (fun _ => le_max_right _ _)
  upperUniverse := .sort _
  motiveClosure := ⟨.sort (.max dataLevel motiveLevel), .sorts _ _,
    .inr (fun _ => max_le (le_max_left _ _) le_rfl)⟩
  eliminatorJoin := .sorts _ _
  outputUniverse := .sort _

noncomputable def inventory := ordinaryInventory (registry := registry) (parameters := 0) (Vectors.admitted Bool).constructors

theorem indices_admitted : ∀ item ∈ inventory, IndicesAdmitted SupportedIndex item.2 := by
  intro item member
  change item ∈ [("Nil", ordinaryCode (registry := registry) (parameters := 0) (Vectors.nilCode Bool)),
    ("Cons", ordinaryCode (registry := registry) (parameters := 0) (Vectors.consCode Bool))] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact nil_indices_admitted
  · rcases List.mem_singleton.mp member with rfl
    exact cons_indices_admitted

theorem constructors_typed : ∀ item ∈ inventory, Typing rules nativeContextA (referenceTypes.constructor item.1)
    (constructorType (.indexed (Guest.TypedControls.indexSyntax Bool)) containers item.2 referenceTypes PUnit.unit) := by
  intro item member
  change item ∈ [("Nil", ordinaryCode (registry := registry) (parameters := 0) (Vectors.nilCode Bool)),
    ("Cons", ordinaryCode (registry := registry) (parameters := 0) (Vectors.consCode Bool))] at member
  rcases List.mem_cons.mp member with rfl | member
  · have member : (NativeNaturalVectorFamilies.vnilName, (⟨NativeNaturalVectorFamilies.vnilType, none⟩ : Entry Tower.Head)) ∈ constructorPrefix := by decide +kernel
    obtain ⟨_, level, isUniverse, formed, _⟩ := DeclarationAdmissionReplay.Admitted.member_typed Tower.rules prefix_admitted member
    have constant := Typing.const (Γ := nativeContextA)
      (show rules.constantType NativeNaturalVectorFamilies.vnilName = some NativeNaturalVectorFamilies.vnilType from by decide +kernel)
      formed isUniverse
    have applied := Typing.appElim constant (Typing.var (R := rules) (Γ := nativeContextA) 0)
    convert applied using 1 <;> decide +kernel
  · rcases List.mem_singleton.mp member with rfl
    have member : (NativeNaturalVectorFamilies.vconsName, (⟨NativeNaturalVectorFamilies.vconsType, none⟩ : Entry Tower.Head)) ∈ constructorPrefix := by decide +kernel
    obtain ⟨_, level, isUniverse, formed, _⟩ := DeclarationAdmissionReplay.Admitted.member_typed Tower.rules prefix_admitted member
    have constant := Typing.const (Γ := nativeContextA)
      (show rules.constantType NativeNaturalVectorFamilies.vconsName = some NativeNaturalVectorFamilies.vconsType from by decide +kernel)
      formed isUniverse
    have applied := Typing.appElim constant (Typing.var (R := rules) (Γ := nativeContextA) 0)
    convert applied using 1 <;> decide +kernel

/-- The original Cons term directly instantiates its admitted constructor occurrence. -/
theorem source_cons_typed : Typing rules nativeContextA
    (.app (.const NativeNaturalVectorFamilies.vconsName) (.var 0))
    NativeNaturalVectorFamilies.vconsBodyType := by
  have typed := constructors_typed
    ("Cons", ordinaryCode (registry := registry) (parameters := 0) (Vectors.consCode Bool))
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  convert typed using 1 <;> decide +kernel

noncomputable def generatedType : Tower.Tm 0 := .pi (sortTm dataLevel)
  (eliminatorType (.indexed (Guest.TypedControls.indexSyntax Bool)) containers inventory referenceTypes
    NativeNaturalVectorFamilies.natTm (.sort resultLevel))


/-- Universe instantiation commutes with the complete indexed Vec eliminator,
including its original element-type binder and its actual index interpretation. -/
theorem generated_type_substLevels (theta : Nat → LevelExpr Nat) :
    substLevelsTm theta generatedType =
      .pi (sortTm (LevelExpr.subst theta dataLevel))
        (eliminatorType (.indexed (Guest.TypedControls.indexSyntax Bool)) containers inventory
          (referenceTypes.map (substLevelsTm theta)) NativeNaturalVectorFamilies.natTm
          (.sort (LevelExpr.subst theta resultLevel))) := by
  unfold generatedType
  change Tm.pi (sortTm (LevelExpr.subst theta dataLevel)) _ = _
  congr 1
  exact eliminatorType_mapHead (.indexed (Guest.TypedControls.indexSyntax Bool))
    (substLevelsHead theta) (indexSyntax_headNatural _) (containers_headNatural _) _ _ _ _

theorem generated_type_formed : Judgment rules .nil generatedType
    (sortTm (.max (.succ dataLevel) outputLevel)) := by
  refine ⟨.nil, ?_⟩
  unfold generatedType
  apply Typing.piForm (R := rules) (.headType (.sort dataLevel)) (.sort _) ?_ (.sort _) (.sorts _ _)
  have formed := eliminatorType_formedOn primitives inventory indices_admitted constructors_typed ids
    (show FormationSensitive.CtxMor rules nativeContextA nativeContextA ids from
      fun index => by simpa only [subst_ids, ids] using (Typing.var (R := rules) (Γ := nativeContextA) index))
  rw [show referenceTypes.map (subst ids) = referenceTypes from by
    cases referenceTypes
    simp only [TypeSyntax.map, subst_ids]] at formed
  exact formed

theorem generated_type_exact : generatedType = NativeNaturalVectorFamilies.vecEliminateType :=
  Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls.OrdinaryVectors.eliminator_exact

theorem source_eliminator_absent : rules.constantType NativeNaturalVectorFamilies.vecEliminateName = none := by
  decide +kernel

/-- Ordinary opaque admission follows from generated formation, before any iota authority. -/
theorem eliminator_admitted : DeclarationAdmissionReplay.Admitted Tower.rules constructorPrefix
    [(NativeNaturalVectorFamilies.vecEliminateName, ⟨generatedType, none⟩)] := by
  apply DeclarationAdmissionReplay.Admitted.cons source_eliminator_absent
    (show Tower.rules.isUniverse (.sort (.max (.succ dataLevel) outputLevel)) from .sort _)
    generated_type_formed.typing
  · intro value impossible
    cases impossible
  · exact .nil _

/-- Structural admission closes the exact original Nat/Vec declaration inventory. -/
theorem source_inventory_admitted : DeclarationAdmissionReplay.Admitted Tower.rules []
    NativeNaturalVectorFamilies.declarations := by
  have admitted := prefix_admitted.append Tower.rules eliminator_admitted
  have same : constructorPrefix ++
      [(NativeNaturalVectorFamilies.vecEliminateName, (⟨generatedType, none⟩ : Entry Tower.Head))] =
      NativeNaturalVectorFamilies.declarations := by
    rw [generated_type_exact]
    decide +kernel
  exact same ▸ admitted

/-- Independent instantiation of the two original universe parameters. -/
def closedLevels (data result : Nat) (parameter : Nat) : LevelExpr Nat :=
  .const (if parameter = 0 then data else if parameter = 1 then result else 0)

def levelInstance (data result : Nat) : LevelInstance (Signature.ofList constructorPrefix) (closedLevels data result) where
  computation := .empty
  computationMap := by
    intro n left right step
    rw [Signature.computation_ofList] at step
    exact step.elim

theorem instantiated_type_formed (data result : Nat) :
    Judgment (levelInstance data result).rules
      (RussellTarski.substLevelsCtx (closedLevels data result) (.nil : Tower.Ctx 0))
      (RussellTarski.substLevelsTm (closedLevels data result) generatedType)
      (RussellTarski.substLevelsTm (closedLevels data result)
        (sortTm (.max (.succ dataLevel) outputLevel))) :=
  (levelInstance data result).refinedJudgment generated_type_formed

def closedPrefix (data result : Nat) := constructorPrefix.map
  (fun item => (item.1, item.2.instantiateLevels (closedLevels data result)))

def closedEliminator (data result : Nat) : Tower.Tm 0 :=
  RussellTarski.substLevelsTm (closedLevels data result) NativeNaturalVectorFamilies.vecEliminateType

/-- The independently checked concrete type is the same instantiated generated type. -/
theorem closed_type_exact (data result : Nat) :
    RussellTarski.substLevelsTm (closedLevels data result) generatedType =
      closedEliminator data result := by
  rw [generated_type_exact]
  rfl

def closedEntry (data result : Nat) : List (DeclName × Entry Tower.Head) :=
  [(NativeNaturalVectorFamilies.vecEliminateName, ⟨closedEliminator data result, none⟩)]

def boundClaim (data result claimed : Nat) : List (DeclName × Entry Tower.Head) :=
  [(`Generated.Vector.UniverseClaim, ⟨sortTm (.const claimed), some (closedEliminator data result)⟩)]

theorem higher_result_formed : Judgment (levelInstance 0 2).rules
    (RussellTarski.substLevelsCtx (closedLevels 0 2) (.nil : Tower.Ctx 0))
    (RussellTarski.substLevelsTm (closedLevels 0 2) generatedType)
    (RussellTarski.substLevelsTm (closedLevels 0 2)
      (sortTm (.max (.succ dataLevel) outputLevel))) :=
  instantiated_type_formed 0 2

theorem lower_result_formed : Judgment (levelInstance 2 0).rules
    (RussellTarski.substLevelsCtx (closedLevels 2 0) (.nil : Tower.Ctx 0))
    (RussellTarski.substLevelsTm (closedLevels 2 0) generatedType)
    (RussellTarski.substLevelsTm (closedLevels 2 0)
      (sortTm (.max (.succ dataLevel) outputLevel))) :=
  instantiated_type_formed 2 0

theorem higher_result_checked : Guest.DeclarationControls.accepted
    (closedPrefix 0 2) (closedEntry 0 2) = true := by decide +kernel

theorem lower_result_checked : Guest.DeclarationControls.accepted
    (closedPrefix 2 0) (closedEntry 2 0) = true := by decide +kernel

/-- At alpha = 0, beta = 2, the full type needs level 3 because it binds a U2-valued motive. -/
theorem motive_successor_bound_checked : Guest.DeclarationControls.accepted
    (closedPrefix 0 2) (boundClaim 0 2 3) = true := by decide +kernel

theorem missing_motive_successor_refused : Guest.DeclarationControls.accepted
    (closedPrefix 0 2) (boundClaim 0 2 2) = false := by decide +kernel

theorem missing_constructors_refused : Guest.DeclarationControls.accepted familyPrefix
    [(NativeNaturalVectorFamilies.vecEliminateName, ⟨NativeNaturalVectorFamilies.vecEliminateType, none⟩)] = false := by
  decide +kernel

def verdicts : List (String × Bool) :=
  [("indexed elimination accepts a higher result universe", Guest.DeclarationControls.accepted (closedPrefix 0 2) (closedEntry 0 2)),
   ("indexed elimination accepts a lower result universe", Guest.DeclarationControls.accepted (closedPrefix 2 0) (closedEntry 2 0)),
   ("motive-binding universe includes the result-universe successor", Guest.DeclarationControls.accepted (closedPrefix 0 2) (boundClaim 0 2 3)),
   ("motive-binding universe refuses an omitted successor", !(Guest.DeclarationControls.accepted (closedPrefix 0 2) (boundClaim 0 2 2))),
   ("polymorphic indexed eliminator refuses missing constructors", !(Guest.DeclarationControls.accepted familyPrefix
      [(NativeNaturalVectorFamilies.vecEliminateName, ⟨NativeNaturalVectorFamilies.vecEliminateType, none⟩)]))]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp only [verdicts, higher_result_checked, lower_result_checked,
    motive_successor_bound_checked, missing_motive_successor_refused, missing_constructors_refused,
    Bool.not_false, List.all_cons, List.all_nil, Bool.and_self]

#print axioms eliminator_admitted
#print axioms source_cons_typed
#print axioms source_inventory_admitted
#print axioms closed_type_exact
#print axioms instantiated_type_formed
#print axioms higher_result_formed
#print axioms lower_result_formed
#print axioms higher_result_checked
#print axioms lower_result_checked
#print axioms motive_successor_bound_checked
#print axioms missing_motive_successor_refused
#print axioms missing_constructors_refused

#print axioms primitives
#print axioms generated_type_formed
#print axioms generated_type_exact
#print axioms source_eliminator_absent
end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerUniverseControls
