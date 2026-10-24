import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestTypes
import Mettapedia.TypeTheory.IndexedPositiveContainer
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FunctionArgumentAdapters

/-!
# Open declaration types for registered positive containers

Constructor, method and complete eliminator types are generated from the
admitted indexed-positive code. A nested field keeps its container output expression, recursive family
index and complete induction-evidence bundle. Original fields precede induction
hypotheses; both orders are the source orders.

The registry supplies object-language container and bundle types with scoped
substitution laws. Constructor formation follows from explicit primitive
typing contracts for data, admitted source indices, the family and registered containers.
The admission predicate is checked for every index occurrence in the constructor
code. Unrestricted index typing remains a sufficient specialization.
Dependent method formation additionally requires typed motives and constructors
and a typed registered bundle operation. Complete eliminator formation additionally requires typed index domains,
constructor inventories and explicit universe formation/product contracts.
Data/family, motive-result and method/bundle universes are distinct. The
method bound closes products over source fields and induction hypotheses;
the motive-binding bound also contains the universe of the result sort.
Neither ordering of the data and result universes is assumed.
Admission and computation authority remain separate obligations.
An unindexed family omits the index argument only when the semantic index type
is a subsingleton; an indexed family retains the actual index expression.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestTypes

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open IndexedInductive.Guest
open IndexedInductive.Guest.Types (weakenEnvironment weakenEnvironment_substitute)

universe u
variable {I : Interface.{u}} {registry : Registry I} {Head : Type}

/-- Whether the object family exposes an index binder. Omitting it requires a
genuinely unindexed semantic family, rather than silently forgetting an index. -/
inductive Indexing (I : Interface.{u}) (Head : Type) where
  | indexed (indices : IndexSyntax I Head)
  | unindexed (unique : Subsingleton I.Index)

def Indexing.familyAt (indexing : Indexing I Head) {context : List I.SortCode}
    {n : Nat} (family : Tm Head n) (expression : I.IndexExpr context)
    (environment : TermEnv I Head n context) : Tm Head n :=
  match indexing with
  | .indexed indices => .app family (indices.term expression environment)
  | .unindexed _ => family

/-- Fix the recursive child's index while leaving the child argument open. -/
def Indexing.predicateAt (indexing : Indexing I Head) {context : List I.SortCode}
    {n : Nat} (motive : Tm Head n) (expression : I.IndexExpr context)
    (environment : TermEnv I Head n context) : Tm Head n :=
  indexing.familyAt motive expression environment

theorem Indexing.familyAt_substitute (indexing : Indexing I Head)
    {context : List I.SortCode} {n m : Nat} (family : Tm Head n)
    (expression : I.IndexExpr context) (environment : TermEnv I Head n context)
    (substitution : Sub Head n m) :
    subst substitution (indexing.familyAt family expression environment) =
      indexing.familyAt (subst substitution family) expression
        (mapEnv (subst substitution) environment) := by
  cases indexing with
  | indexed indices => simp only [familyAt, subst, indices.substitute]
  | unindexed _ => rfl

theorem Indexing.predicateAt_substitute (indexing : Indexing I Head)
    {context : List I.SortCode} {n m : Nat} (motive : Tm Head n)
    (expression : I.IndexExpr context) (environment : TermEnv I Head n context)
    (substitution : Sub Head n m) :
    subst substitution (indexing.predicateAt motive expression environment) =
      indexing.predicateAt (subst substitution motive) expression
        (mapEnv (subst substitution) environment) :=
  indexing.familyAt_substitute motive expression environment substitution

/-- Object syntax for the actual registered containers. The bundle may depend
on the entire original field, not merely on its shape or its result values. -/
structure RegistrySyntax (I : Interface.{u}) (registry : Registry I) (Head : Type) where
  fieldType : ∀ {context : List I.SortCode} {n : Nat}
    (name : String) (entry : Entry I), registry.lookup name = some entry →
      entry.OutputExpr context → TermEnv I Head n context → Tm Head n → Tm Head n
  bundleType : ∀ {context : List I.SortCode} {n : Nat}
    (name : String) (entry : Entry I), registry.lookup name = some entry →
      entry.OutputExpr context → TermEnv I Head n context →
      Tm Head n → Tm Head n → Tm Head n → Tm Head n
  fieldType_substitute : ∀ {context n m} name entry registered
    (output : entry.OutputExpr context) (environment : TermEnv I Head n context)
    (element : Tm Head n) (substitution : Sub Head n m),
    subst substitution (fieldType name entry registered output environment element) =
      fieldType name entry registered output (mapEnv (subst substitution) environment)
        (subst substitution element)
  bundleType_substitute : ∀ {context n m} name entry registered
    (output : entry.OutputExpr context) (environment : TermEnv I Head n context)
    (element predicate field : Tm Head n) (substitution : Sub Head n m),
    subst substitution
        (bundleType name entry registered output environment element predicate field) =
      bundleType name entry registered output (mapEnv (subst substitution) environment)
        (subst substitution element) (subst substitution predicate) (subst substitution field)

/-- Family and constructor prefixes may already contain authored parameters. -/
structure TypeSyntax (I : Interface.{u}) (Head : Type) (n : Nat) where
  dataType : I.SortCode → Tm Head n
  family : Tm Head n
  constructor : String → Tm Head n

def TypeSyntax.map {n m : Nat} (mapping : Tm Head n → Tm Head m)
    (types : TypeSyntax I Head n) : TypeSyntax I Head m where
  dataType := fun sort => mapping (types.dataType sort)
  family := mapping types.family
  constructor := fun name => mapping (types.constructor name)

def TypeSyntax.weaken {n : Nat} (types : TypeSyntax I Head n) : TypeSyntax I Head (n + 1) :=
  types.map (rename wk)

theorem TypeSyntax.weaken_substitute {n m : Nat} (substitution : Sub Head n m)
    (types : TypeSyntax I Head n) :
    types.weaken.map (subst (liftSub substitution)) =
      (types.map (subst substitution)).weaken := by
  cases types
  simp only [weaken, map, subst_liftSub_wk]

def constructorType (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head) :
    {parameters : Nat} → {context : List I.SortCode} →
      Code I registry parameters context → {n : Nat} → TypeSyntax I Head n →
      TermEnv I Head n context → Tm Head n
  | _, _, .result expression, _, types, environment =>
      indexing.familyAt types.family expression environment
  | _, _, .data sort body, _, types, environment =>
      .pi (types.dataType sort)
        (constructorType indexing containers body types.weaken
          (.var 0, weakenEnvironment environment))
  | _, _, .recursive expression rest, _, types, environment =>
      .pi (indexing.familyAt types.family expression environment)
        (constructorType indexing containers rest types.weaken (weakenEnvironment environment))
  | _, _, .nested name entry registered output childIndex rest, _, types, environment =>
      .pi (containers.fieldType name entry registered output environment
          (indexing.familyAt types.family childIndex environment))
        (constructorType indexing containers rest types.weaken (weakenEnvironment environment))

theorem constructorType_substitute (indexing : Indexing I Head)
    (containers : RegistrySyntax I registry Head) {parameters : Nat}
    {context : List I.SortCode} (code : Code I registry parameters context) {n m : Nat}
    (types : TypeSyntax I Head n) (environment : TermEnv I Head n context)
    (substitution : Sub Head n m) :
    subst substitution (constructorType indexing containers code types environment) =
      constructorType indexing containers code (types.map (subst substitution))
        (mapEnv (subst substitution) environment) := by
  induction code generalizing n m with
  | result expression =>
      simp only [constructorType, indexing.familyAt_substitute, TypeSyntax.map]
  | data sort body ih =>
      simp only [constructorType, subst, TypeSyntax.map]
      congr 1
      simpa only [mapEnv, subst, liftSub, Fin.cases_zero, weakenEnvironment_substitute,
        TypeSyntax.weaken, TypeSyntax.map, subst_liftSub_wk]
        using ih types.weaken (.var 0, weakenEnvironment environment) (liftSub substitution)
  | recursive expression rest ih =>
      simp only [constructorType, subst, indexing.familyAt_substitute, TypeSyntax.map]
      congr 1
      simpa only [weakenEnvironment_substitute, TypeSyntax.weaken, TypeSyntax.map,
        subst_liftSub_wk] using
        ih types.weaken (weakenEnvironment environment) (liftSub substitution)
  | nested name entry registered output childIndex rest ih =>
      simp only [constructorType, subst, containers.fieldType_substitute,
        indexing.familyAt_substitute, TypeSyntax.map]
      congr 1
      simpa only [weakenEnvironment_substitute, TypeSyntax.weaken, TypeSyntax.map,
        subst_liftSub_wk] using
        ih types.weaken (weakenEnvironment environment) (liftSub substitution)

/-- Induction hypotheses are complete types, so a nested field contributes one
whole container bundle. All original fields have already been bound. -/
def hypotheses {n : Nat} (types : List (Tm Head n)) (result : Tm Head n) : Tm Head n :=
  FunctionArgumentAdapters.curriedType types result

theorem hypotheses_substitute {n m : Nat} (types : List (Tm Head n))
    (result : Tm Head n) (substitution : Sub Head n m) :
    subst substitution (hypotheses types result) =
      hypotheses (types.map (subst substitution)) (subst substitution result) :=
  FunctionArgumentAdapters.curriedType_substitute types result substitution

def methodBody (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head) :
    {parameters : Nat} → {context : List I.SortCode} →
      Code I registry parameters context → {n : Nat} → TypeSyntax I Head n →
      TermEnv I Head n context → Tm Head n → Tm Head n → List (Tm Head n) → Tm Head n
  | _, _, .result expression, _, _, environment, motive, constructor, pending =>
      hypotheses pending (.app (indexing.predicateAt motive expression environment) constructor)
  | _, _, .data sort body, _, types, environment, motive, constructor, pending =>
      .pi (types.dataType sort)
        (methodBody indexing containers body types.weaken (.var 0, weakenEnvironment environment)
          (rename wk motive) (.app (rename wk constructor) (.var 0))
          (pending.map (rename wk)))
  | _, _, .recursive expression rest, _, types, environment, motive, constructor, pending =>
      .pi (indexing.familyAt types.family expression environment)
        (methodBody indexing containers rest types.weaken (weakenEnvironment environment)
          (rename wk motive) (.app (rename wk constructor) (.var 0))
          ((pending.map (rename wk)) ++
            [.app (indexing.predicateAt (rename wk motive) expression
              (weakenEnvironment environment)) (.var 0)]))
  | _, _, .nested name entry registered output childIndex rest, _,
      types, environment, motive, constructor, pending =>
      .pi (containers.fieldType name entry registered output environment
          (indexing.familyAt types.family childIndex environment))
        (methodBody indexing containers rest types.weaken (weakenEnvironment environment)
          (rename wk motive) (.app (rename wk constructor) (.var 0))
          ((pending.map (rename wk)) ++
            [containers.bundleType name entry registered output (weakenEnvironment environment)
              (indexing.familyAt (rename wk types.family) childIndex
                (weakenEnvironment environment))
              (indexing.predicateAt (rename wk motive) childIndex (weakenEnvironment environment))
              (.var 0)]))

theorem methodBody_substitute (indexing : Indexing I Head)
    (containers : RegistrySyntax I registry Head) {parameters : Nat}
    {context : List I.SortCode} (code : Code I registry parameters context) {n m : Nat}
    (types : TypeSyntax I Head n) (environment : TermEnv I Head n context)
    (motive constructor : Tm Head n) (pending : List (Tm Head n))
    (substitution : Sub Head n m) :
    subst substitution
        (methodBody indexing containers code types environment motive constructor pending) =
      methodBody indexing containers code (types.map (subst substitution))
        (mapEnv (subst substitution) environment) (subst substitution motive)
        (subst substitution constructor) (pending.map (subst substitution)) := by
  induction code generalizing n m with
  | result expression =>
      simp only [methodBody, hypotheses_substitute, subst, indexing.predicateAt_substitute]
  | data sort body ih =>
      simp only [methodBody, subst, TypeSyntax.map]
      congr 1
      simpa only [mapEnv, subst, liftSub, Fin.cases_zero, weakenEnvironment_substitute,
        TypeSyntax.weaken, TypeSyntax.map, subst_liftSub_wk, List.map_map, Function.comp_def]
        using ih types.weaken (.var 0, weakenEnvironment environment)
          (rename wk motive) (.app (rename wk constructor) (.var 0))
          (pending.map (rename wk)) (liftSub substitution)
  | recursive expression rest ih =>
      simp only [methodBody, subst, indexing.familyAt_substitute, TypeSyntax.map]
      congr 1
      convert ih types.weaken (weakenEnvironment environment) (rename wk motive)
        (.app (rename wk constructor) (.var 0))
        ((pending.map (rename wk)) ++
          [.app (indexing.predicateAt (rename wk motive) expression
            (weakenEnvironment environment)) (.var 0)]) (liftSub substitution) using 1
      simp only [subst, liftSub, Fin.cases_zero, weakenEnvironment_substitute,
        TypeSyntax.weaken, TypeSyntax.map, subst_liftSub_wk, List.map_map, Function.comp_def,
        List.map_append, List.map_cons, List.map_nil, indexing.predicateAt_substitute]
  | nested name entry registered output childIndex rest ih =>
      simp only [methodBody, subst, containers.fieldType_substitute,
        indexing.familyAt_substitute, TypeSyntax.map]
      congr 1
      convert ih types.weaken (weakenEnvironment environment) (rename wk motive)
        (.app (rename wk constructor) (.var 0))
        ((pending.map (rename wk)) ++
          [containers.bundleType name entry registered output (weakenEnvironment environment)
            (indexing.familyAt (rename wk types.family) childIndex (weakenEnvironment environment))
            (indexing.predicateAt (rename wk motive) childIndex (weakenEnvironment environment))
            (.var 0)]) (liftSub substitution) using 1
      simp only [subst, liftSub, Fin.cases_zero, weakenEnvironment_substitute,
        TypeSyntax.weaken, TypeSyntax.map, subst_liftSub_wk, List.map_map, Function.comp_def,
        List.map_append, List.map_cons, List.map_nil, containers.bundleType_substitute,
        indexing.familyAt_substitute, indexing.predicateAt_substitute]

def methodType (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters n : Nat} (code : Code I registry parameters [])
    (types : TypeSyntax I Head n) (motive : Tm Head n) (name : String) : Tm Head n :=
  methodBody indexing containers code types PUnit.unit motive (types.constructor name) []

theorem methodType_substitute (indexing : Indexing I Head)
    (containers : RegistrySyntax I registry Head) {parameters n m : Nat}
    (code : Code I registry parameters []) (types : TypeSyntax I Head n)
    (motive : Tm Head n) (name : String) (substitution : Sub Head n m) :
    subst substitution (methodType indexing containers code types motive name) =
      methodType indexing containers code (types.map (subst substitution))
        (subst substitution motive) name := by
  simpa only [methodType, TypeSyntax.map, mapEnv, List.map_nil] using
    methodBody_substitute indexing containers code types PUnit.unit motive
      (types.constructor name) [] substitution

/-! ## The ordinary indexed fragment is retained -/

/-- Embed the ordinary description syntax without introducing nested fields. -/
def ordinaryCode {parameters : Nat} : {context : List I.SortCode} →
    Mettapedia.TypeTheory.IndexedPolynomial.Description.Code I context →
      Code I registry parameters context
  | _, .result expression => .result expression
  | _, .data sort body => .data sort (ordinaryCode body)
  | _, .recursive expression rest => .recursive expression (ordinaryCode rest)

def TypeSyntax.ofOrdinary {n : Nat} (types : IndexedInductive.Guest.Types.TypeSyntax I Head n) :
    TypeSyntax I Head n where
  dataType := types.dataType
  family := types.family
  constructor := types.constructor

private theorem rename_as_substitution {n m : Nat} (rho : Ren n m) :
    (rename rho : Tm Head n → Tm Head m) = subst (fun index => .var (rho index)) := by
  funext term
  simpa only [subst_ids, ids, rename] using rename_subst rho ids term

private theorem indexTerm_weaken (indices : IndexSyntax I Head)
    {context : List I.SortCode} {n : Nat} (expression : I.IndexExpr context)
    (environment : TermEnv I Head n context) :
    indices.term expression (weakenEnvironment environment) =
      rename wk (indices.term expression environment) := by
  symm
  simpa only [← rename_as_substitution, weakenEnvironment] using
    indices.substitute expression environment (fun index => .var (wk index))

theorem constructorType_ordinary (indices : IndexSyntax I Head)
    (containers : RegistrySyntax I registry Head) {parameters : Nat}
    {context : List I.SortCode}
    (code : Mettapedia.TypeTheory.IndexedPolynomial.Description.Code I context)
    {n : Nat} (types : IndexedInductive.Guest.Types.TypeSyntax I Head n)
    (environment : TermEnv I Head n context) :
    constructorType (.indexed indices) containers (ordinaryCode (parameters := parameters) code)
        (TypeSyntax.ofOrdinary types) environment =
      IndexedInductive.Guest.Types.constructorType indices code types environment := by
  induction code generalizing n with
  | result expression =>
      simp only [ordinaryCode, constructorType, IndexedInductive.Guest.Types.constructorType,
        TypeSyntax.ofOrdinary, Indexing.familyAt]
  | data sort body ih =>
      simp only [ordinaryCode, constructorType, IndexedInductive.Guest.Types.constructorType,
        TypeSyntax.ofOrdinary]
      congr 1
      exact ih types.weaken (.var 0, weakenEnvironment environment)
  | recursive expression rest ih =>
      simp only [ordinaryCode, constructorType, IndexedInductive.Guest.Types.constructorType,
        TypeSyntax.ofOrdinary, Indexing.familyAt]
      congr 1
      exact ih types.weaken (weakenEnvironment environment)

theorem hypotheses_ordinary {n : Nat} (motive : Tm Head n)
    (children : List (Tm Head n × Tm Head n)) (result : Tm Head n) :
    hypotheses (children.map fun pair => .app (.app motive pair.1) pair.2) result =
      IndexedInductive.Guest.Types.hypotheses motive children result := by
  cases children with
  | nil => simp only [List.map_nil, hypotheses, FunctionArgumentAdapters.curriedType,
      IndexedInductive.Guest.Types.hypotheses]
  | cons pair rest =>
      rcases pair with ⟨index, child⟩
      simp only [List.map_cons, hypotheses, FunctionArgumentAdapters.curriedType,
        IndexedInductive.Guest.Types.hypotheses,
        IndexedInductive.Guest.Types.motiveAt]
      congr 1
      simpa only [hypotheses, List.map_map, Function.comp_def, rename] using
        hypotheses_ordinary (rename wk motive)
          (rest.map fun pair => (rename wk pair.1, rename wk pair.2)) (rename wk result)
termination_by children.length
  decreasing_by simp_wf

/-- For every ordinary constructor, the extended generator preserves the
existing field/IH ABI and the complete dependent method type. -/
theorem methodBody_ordinary (indices : IndexSyntax I Head)
    (containers : RegistrySyntax I registry Head) {parameters : Nat}
    {context : List I.SortCode}
    (code : Mettapedia.TypeTheory.IndexedPolynomial.Description.Code I context)
    {n : Nat} (types : IndexedInductive.Guest.Types.TypeSyntax I Head n)
    (environment : TermEnv I Head n context) (motive constructor : Tm Head n)
    (children : List (Tm Head n × Tm Head n)) :
    methodBody (.indexed indices) containers (ordinaryCode (parameters := parameters) code)
        (TypeSyntax.ofOrdinary types) environment motive constructor
        (children.map fun pair => .app (.app motive pair.1) pair.2) =
      IndexedInductive.Guest.Types.methodBody indices code types environment motive constructor children := by
  induction code generalizing n with
  | result expression =>
      simp only [ordinaryCode, methodBody, IndexedInductive.Guest.Types.methodBody,
        Indexing.predicateAt, Indexing.familyAt, IndexedInductive.Guest.Types.motiveAt,
        hypotheses_ordinary]
  | data sort body ih =>
      simp only [ordinaryCode, methodBody, IndexedInductive.Guest.Types.methodBody,
        TypeSyntax.ofOrdinary]
      congr 1
      convert ih types.weaken (.var 0, weakenEnvironment environment) (rename wk motive)
          (.app (rename wk constructor) (.var 0))
          (children.map fun pair => (rename wk pair.1, rename wk pair.2)) using 1
      simp only [List.map_map, Function.comp_def, rename, TypeSyntax.ofOrdinary,
        TypeSyntax.weaken, TypeSyntax.map, IndexedInductive.Guest.Types.TypeSyntax.weaken,
        IndexedInductive.Guest.Types.TypeSyntax.map]
  | recursive expression rest ih =>
      simp only [ordinaryCode, methodBody, IndexedInductive.Guest.Types.methodBody,
        TypeSyntax.ofOrdinary, Indexing.familyAt, Indexing.predicateAt]
      congr 1
      convert ih types.weaken (weakenEnvironment environment) (rename wk motive)
          (.app (rename wk constructor) (.var 0))
          ((children.map fun pair => (rename wk pair.1, rename wk pair.2)) ++
            [(rename wk (indices.term expression environment), .var 0)]) using 1
      simp only [List.map_map, Function.comp_def, List.map_append, List.map_cons,
        List.map_nil, rename, indexTerm_weaken, TypeSyntax.ofOrdinary,
        TypeSyntax.weaken, TypeSyntax.map, IndexedInductive.Guest.Types.TypeSyntax.weaken,
        IndexedInductive.Guest.Types.TypeSyntax.map]

theorem methodType_ordinary (indices : IndexSyntax I Head)
    (containers : RegistrySyntax I registry Head) {parameters n : Nat}
    (constructor : NamedConstructor I [])
    (types : IndexedInductive.Guest.Types.TypeSyntax I Head n) (motive : Tm Head n) :
    methodType (.indexed indices) containers (ordinaryCode (parameters := parameters) constructor.body)
        (TypeSyntax.ofOrdinary types) motive constructor.name =
      IndexedInductive.Guest.Types.methodType indices constructor types motive := by
  simpa only [methodType, IndexedInductive.Guest.Types.methodType, TypeSyntax.ofOrdinary,
    List.map_nil] using
    methodBody_ordinary indices containers constructor.body types PUnit.unit motive
      (types.constructor constructor.name) []

/-! ## Complete dependent eliminator interfaces -/

/-- Only an indexed family supplies an index-domain term. -/
def Indexing.Domain (indexing : Indexing I Head) (n : Nat) : Type :=
  match indexing with
  | .indexed _ => Tm Head n
  | .unindexed _ => PUnit

def Indexing.mapDomain (indexing : Indexing I Head) {n m : Nat}
    (mapping : Tm Head n → Tm Head m) (domain : indexing.Domain n) : indexing.Domain m :=
  match indexing with
  | .indexed _ => mapping domain
  | .unindexed _ => PUnit.unit

theorem Indexing.weakenDomain_substitute (indexing : Indexing I Head) {n m : Nat}
    (substitution : Sub Head n m) (domain : indexing.Domain n) :
    indexing.mapDomain (subst (liftSub substitution)) (indexing.mapDomain (rename wk) domain) =
      indexing.mapDomain (rename wk) (indexing.mapDomain (subst substitution) domain) := by
  cases indexing with
  | indexed _ => exact subst_liftSub_wk substitution domain
  | unindexed _ => rfl

def motiveType (indexing : Indexing I Head) {n : Nat}
    (family : Tm Head n) (domain : indexing.Domain n) (universeHead : Head) : Tm Head n :=
  match indexing with
  | .indexed _ => .pi domain (.pi (.app (rename wk family) (.var 0)) (.head universeHead))
  | .unindexed _ => .pi family (.head universeHead)

def resultType (indexing : Indexing I Head) {n : Nat}
    (family motive : Tm Head n) (domain : indexing.Domain n) : Tm Head n :=
  match indexing with
  | .indexed _ => .pi domain (.pi (.app (rename wk family) (.var 0))
      (.app (.app (rename wk (rename wk motive)) (.var 1)) (.var 0)))
  | .unindexed _ => .pi family (.app (rename wk motive) (.var 0))

def methodsType (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters : Nat} : List (String × Code I registry parameters []) → {n : Nat} →
      TypeSyntax I Head n → Tm Head n → indexing.Domain n → Tm Head n
  | [], _, types, motive, domain => resultType indexing types.family motive domain
  | (name, code) :: rest, _, types, motive, domain =>
      .pi (methodType indexing containers code types motive name)
        (methodsType indexing containers rest types.weaken (rename wk motive)
          (indexing.mapDomain (rename wk) domain))

def eliminatorType (indexing : Indexing I Head) (containers : RegistrySyntax I registry Head)
    {parameters n : Nat} (constructors : List (String × Code I registry parameters []))
    (types : TypeSyntax I Head n) (domain : indexing.Domain n) (universeHead : Head) : Tm Head n :=
  .pi (motiveType indexing types.family domain universeHead)
    (methodsType indexing containers constructors types.weaken (.var 0)
      (indexing.mapDomain (rename wk) domain))

theorem motiveType_substitute (indexing : Indexing I Head) {n m : Nat}
    (family : Tm Head n) (domain : indexing.Domain n) (universeHead : Head)
    (substitution : Sub Head n m) :
    subst substitution (motiveType indexing family domain universeHead) =
      motiveType indexing (subst substitution family)
        (indexing.mapDomain (subst substitution) domain) universeHead := by
  cases indexing <;> simp [motiveType, Indexing.mapDomain, subst, subst_liftSub_wk]

theorem resultType_substitute (indexing : Indexing I Head) {n m : Nat}
    (family motive : Tm Head n) (domain : indexing.Domain n) (substitution : Sub Head n m) :
    subst substitution (resultType indexing family motive domain) =
      resultType indexing (subst substitution family) (subst substitution motive)
        (indexing.mapDomain (subst substitution) domain) := by
  cases indexing <;>
    simp only [resultType, Indexing.mapDomain, subst, subst_liftSub_wk] <;> rfl

theorem methodsType_substitute (indexing : Indexing I Head)
    (containers : RegistrySyntax I registry Head) {parameters : Nat}
    (constructors : List (String × Code I registry parameters [])) {n m : Nat}
    (types : TypeSyntax I Head n) (motive : Tm Head n) (domain : indexing.Domain n)
    (substitution : Sub Head n m) :
    subst substitution (methodsType indexing containers constructors types motive domain) =
      methodsType indexing containers constructors (types.map (subst substitution))
        (subst substitution motive) (indexing.mapDomain (subst substitution) domain) := by
  induction constructors generalizing n m with
  | nil => exact resultType_substitute indexing types.family motive domain substitution
  | cons constructor rest ih =>
      rcases constructor with ⟨name, code⟩
      simp only [methodsType, subst, methodType_substitute]
      congr 1
      simpa only [TypeSyntax.weaken_substitute, subst_liftSub_wk,
        Indexing.weakenDomain_substitute] using
        ih types.weaken (rename wk motive) (indexing.mapDomain (rename wk) domain) (liftSub substitution)

theorem eliminatorType_substitute (indexing : Indexing I Head)
    (containers : RegistrySyntax I registry Head) {parameters n m : Nat}
    (constructors : List (String × Code I registry parameters []))
    (types : TypeSyntax I Head n) (domain : indexing.Domain n) (universeHead : Head)
    (substitution : Sub Head n m) :
    subst substitution (eliminatorType indexing containers constructors types domain universeHead) =
      eliminatorType indexing containers constructors (types.map (subst substitution))
        (indexing.mapDomain (subst substitution) domain) universeHead := by
  simp only [eliminatorType, subst, motiveType_substitute, methodsType_substitute,
    TypeSyntax.weaken_substitute, Indexing.weakenDomain_substitute]
  rfl

def ordinaryInventory {parameters : Nat}
    (constructors : List (NamedConstructor I [])) : List (String × Code I registry parameters []) :=
  constructors.map fun constructor => (constructor.name, ordinaryCode constructor.body)

theorem methodsType_ordinary (indices : IndexedInductive.Guest.IndexSyntax I Head)
    (containers : RegistrySyntax I registry Head) {parameters : Nat}
    (constructors : List (NamedConstructor I [])) {n : Nat}
    (types : IndexedInductive.Guest.Types.TypeSyntax I Head n) (motive : Tm Head n) :
    methodsType (.indexed indices) containers (ordinaryInventory (parameters := parameters) constructors)
        (TypeSyntax.ofOrdinary types) motive types.indexType =
      IndexedInductive.Guest.Types.methodsType indices constructors types motive := by
  induction constructors generalizing n with
  | nil => rfl
  | cons constructor rest ih =>
      simp only [ordinaryInventory, List.map_cons, methodsType,
        IndexedInductive.Guest.Types.methodsType, methodType_ordinary]
      congr 1
      simpa only [ordinaryInventory, TypeSyntax.ofOrdinary, TypeSyntax.weaken, TypeSyntax.map, Indexing.mapDomain,
        IndexedInductive.Guest.Types.TypeSyntax.weaken, IndexedInductive.Guest.Types.TypeSyntax.map] using
        ih types.weaken (rename wk motive)

theorem eliminatorType_ordinary (indices : IndexedInductive.Guest.IndexSyntax I Head)
    (containers : RegistrySyntax I registry Head) {parameters n : Nat}
    (admitted : IndexedInductive.Admitted I []) (types : IndexedInductive.Guest.Types.TypeSyntax I Head n) :
    eliminatorType (.indexed indices) containers
        (ordinaryInventory (parameters := parameters) admitted.constructors)
        (TypeSyntax.ofOrdinary types) types.indexType types.motiveUniverse =
      IndexedInductive.Guest.Types.eliminatorType indices admitted types := by
  unfold eliminatorType IndexedInductive.Guest.Types.eliminatorType
  congr 1
  simpa only [motiveType, TypeSyntax.ofOrdinary, TypeSyntax.weaken, TypeSyntax.map, Indexing.mapDomain,
    IndexedInductive.Guest.Types.TypeSyntax.weaken, IndexedInductive.Guest.Types.TypeSyntax.map] using
    methodsType_ordinary indices containers admitted.constructors types.weaken (.var 0)

/-! ## Constructor formation from primitive syntax contracts -/

open FormationSensitive

def EnvironmentTyped (R : Rules Head) {n : Nat} (ambient : Ctx Head n)
    (dataTypes : I.SortCode → Tm Head n) : {context : List I.SortCode} →
      TermEnv I Head n context → Prop
  | [], _ => True
  | sort :: _, environment =>
      Typing R ambient environment.1 (dataTypes sort) ∧
        EnvironmentTyped R ambient dataTypes environment.2

theorem EnvironmentTyped.weaken {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {dataTypes : I.SortCode → Tm Head n} {context : List I.SortCode}
    {environment : TermEnv I Head n context}
    (typed : EnvironmentTyped R ambient dataTypes environment) (domain : Tm Head n) :
    EnvironmentTyped R (.snoc ambient domain) (fun sort => rename wk (dataTypes sort))
      (weakenEnvironment environment) := by
  induction context with
  | nil => trivial
  | cons sort rest ih => exact ⟨typed.1.weaken, ih typed.2⟩

/-- The family kind uses the actual optional index domain. -/
def Indexing.familyKind (indexing : Indexing I Head) {n : Nat}
    (domain : indexing.Domain n) (level : Head) : Tm Head n :=
  match indexing with
  | .indexed _ => .pi domain (.head level)
  | .unindexed _ => .head level

/-- Admission is a property of source index expressions, independent of the
object context into which their variables are substituted. -/
abbrev IndexPredicate (I : Interface.{u}) :=
  {context : List I.SortCode} → I.IndexExpr context → Prop

def unrestrictedIndices : IndexPredicate I := fun _ => True

/-- Every index expression actually used by a constructor has an admission.
Container output expressions retain their separate registry contract. -/
def IndicesAdmitted (admitted : IndexPredicate I) {parameters : Nat} :
    {context : List I.SortCode} → Code I registry parameters context → Prop
  | _, .result expression => admitted expression
  | _, .data _ body => IndicesAdmitted admitted body
  | _, .recursive expression rest => admitted expression ∧ IndicesAdmitted admitted rest
  | _, .nested _ _ _ _ expression rest => admitted expression ∧ IndicesAdmitted admitted rest

theorem indices_unrestricted {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) : IndicesAdmitted unrestrictedIndices code := by
  induction code with
  | result => trivial
  | data _ _ ih => exact ih
  | recursive _ _ ih => exact ⟨True.intro, ih⟩
  | nested _ _ _ _ _ _ ih => exact ⟨True.intro, ih⟩

def IndexTyping (R : Rules Head) {n : Nat} (ambient : Ctx Head n)
    (types : TypeSyntax I Head n) (indexing : Indexing I Head)
    (domain : indexing.Domain n) : Prop :=
  match indexing with
  | .unindexed _ => True
  | .indexed indices => ∀ {m : Nat} {target : Ctx Head m}
      (sigma : Sub Head n m), FormationSensitive.CtxMor R ambient target sigma →
      ∀ {context : List I.SortCode} (expression : I.IndexExpr context)
        (environment : TermEnv I Head m context),
        EnvironmentTyped R target (fun sort => subst sigma (types.dataType sort)) environment →
          Typing R target (indices.term expression environment) (subst sigma domain)

def IndexTypingOn (admitted : IndexPredicate I) (R : Rules Head) {n : Nat} (ambient : Ctx Head n)
    (types : TypeSyntax I Head n) (indexing : Indexing I Head)
    (domain : indexing.Domain n) : Prop :=
  match indexing with
  | .unindexed _ => True
  | .indexed indices => ∀ {m : Nat} {target : Ctx Head m}
      (sigma : Sub Head n m), FormationSensitive.CtxMor R ambient target sigma →
      ∀ {context : List I.SortCode} (expression : I.IndexExpr context), admitted expression → ∀
        (environment : TermEnv I Head m context),
        EnvironmentTyped R target (fun sort => subst sigma (types.dataType sort)) environment →
          Typing R target (indices.term expression environment) (subst sigma domain)

theorem indexTypingOn_unrestricted_iff {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head} {domain : indexing.Domain n} :
    IndexTypingOn unrestrictedIndices R ambient types indexing domain ↔
      IndexTyping R ambient types indexing domain := by
  cases indexing with
  | unindexed => rfl
  | indexed indices =>
      constructor
      · intro typed m target sigma morphism context expression environment environmentTyped
        exact typed sigma morphism expression True.intro environment environmentTyped
      · intro typed m target sigma morphism context expression _ environment environmentTyped
        exact typed sigma morphism expression environment environmentTyped

/-- These are primitive syntax contracts, not formation of a generated type. -/
structure ConstructorPrimitives (R : Rules Head) {n : Nat} (ambient : Ctx Head n)
    (types : TypeSyntax I Head n) (indexing : Indexing I Head)
    (containers : RegistrySyntax I registry Head) (domain : indexing.Domain n) (level : Head)
    (admittedIndices : IndexPredicate I := unrestrictedIndices) : Prop where
  isUniverse : R.isUniverse level
  productClosure : ∃ result, R.join level level result ∧ (result = level ∨ R.cumulative result level)
  data : ∀ sort, Typing R ambient (types.dataType sort) (.head level)
  family : Typing R ambient types.family (indexing.familyKind domain level)
  indices : IndexTypingOn admittedIndices R ambient types indexing domain
  container : ∀ {m : Nat} {target : Ctx Head m}
    (sigma : Sub Head n m), FormationSensitive.CtxMor R ambient target sigma →
    ∀ {context : List I.SortCode} name entry (registered : registry.lookup name = some entry)
      (output : entry.OutputExpr context) (environment : TermEnv I Head m context),
      EnvironmentTyped R target (fun sort => subst sigma (types.dataType sort)) environment →
      ∀ element, Typing R target element (.head level) →
        Typing R target (containers.fieldType name entry registered output environment element) (.head level)

theorem ConstructorPrimitives.piForm {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level : Head}
    {admittedIndices : IndexPredicate I}
    (primitives : ConstructorPrimitives R ambient types indexing containers domain level admittedIndices)
    {m : Nat} {target : Ctx Head m} {A : Tm Head m} {B : Tm Head (m + 1)}
    (first : Typing R target A (.head level))
    (rest : Typing R (.snoc target A) B (.head level)) :
    Typing R target (.pi A B) (.head level) := by
  obtain ⟨productLevel, productRule, productBound⟩ := primitives.productClosure
  have formed := Typing.piForm first primitives.isUniverse rest primitives.isUniverse productRule
  rcases productBound with same | cumulative
  · exact same ▸ formed
  · exact .cumul formed cumulative

theorem ConstructorPrimitives.familyAt_formedOn {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level : Head}
    {admittedIndices : IndexPredicate I}
    (primitives : ConstructorPrimitives R ambient types indexing containers domain level admittedIndices)
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma)
    {context : List I.SortCode} (expression : I.IndexExpr context) (expressionAdmitted : admittedIndices expression)
    (environment : TermEnv I Head m context)
    (typed : EnvironmentTyped R target (fun sort => subst sigma (types.dataType sort)) environment) :
    Typing R target (indexing.familyAt (subst sigma types.family) expression environment) (.head level) := by
  cases indexing with
  | unindexed unique => exact primitives.family.substitute morphism
  | indexed indices =>
      have family := primitives.family.substitute morphism
      have index := primitives.indices sigma morphism expression expressionAdmitted environment typed
      have application := Typing.appElim family index
      simpa only [Indexing.familyKind, Indexing.familyAt, subst, inst0] using application

private theorem mappedTypes_weaken {n m : Nat} (types : TypeSyntax I Head n)
    (sigma : Sub Head n m) :
    (types.map (subst sigma)).weaken = types.map (subst (fun i => rename wk (sigma i))) := by
  cases types
  simp only [TypeSyntax.weaken, TypeSyntax.map, rename_subst]

theorem constructorType_formedOn {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level : Head}
    {admittedIndices : IndexPredicate I}
    (primitives : ConstructorPrimitives R ambient types indexing containers domain level admittedIndices)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    (codeAdmitted : IndicesAdmitted admittedIndices code)
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma)
    (environment : TermEnv I Head m context)
    (typed : EnvironmentTyped R target (fun sort => subst sigma (types.dataType sort)) environment) :
    Typing R target (constructorType indexing containers code (types.map (subst sigma)) environment)
      (.head level) := by
  induction code generalizing m with
  | result expression =>
      simpa only [constructorType, TypeSyntax.map] using
        primitives.familyAt_formedOn sigma morphism expression codeAdmitted environment typed
  | data sort body ih =>
      have domain := (primitives.data sort).substitute morphism
      rw [constructorType]
      apply primitives.piForm domain
      rw [mappedTypes_weaken]
      apply ih codeAdmitted (fun i => rename wk (sigma i)) (by intro index; simpa only [rename_subst] using (morphism index).weaken) (.var 0, weakenEnvironment environment)
      constructor
      · simpa only [Ctx.lookup_snoc_zero, rename_subst] using (Typing.var (R := R) (Γ := .snoc target (subst sigma (types.dataType sort))) (0 : Fin (m + 1)))
      · simpa only [rename_subst] using typed.weaken (subst sigma (types.dataType sort))
  | recursive expression rest ih =>
      have domain := primitives.familyAt_formedOn sigma morphism expression codeAdmitted.1 environment typed
      rw [constructorType]
      apply primitives.piForm domain
      rw [mappedTypes_weaken]
      apply ih codeAdmitted.2 (fun i => rename wk (sigma i)) (by intro index; simpa only [rename_subst] using (morphism index).weaken) (weakenEnvironment environment)
      simpa only [rename_subst] using typed.weaken (indexing.familyAt (subst sigma types.family) expression environment)
  | nested name entry registered output childIndex rest ih =>
      have element := primitives.familyAt_formedOn sigma morphism childIndex codeAdmitted.1 environment typed
      have domain := primitives.container sigma morphism name entry registered output environment typed _ element
      rw [constructorType]
      apply primitives.piForm domain
      rw [mappedTypes_weaken]
      apply ih codeAdmitted.2 (fun i => rename wk (sigma i)) (by intro index; simpa only [rename_subst] using (morphism index).weaken) (weakenEnvironment environment)
      simpa only [rename_subst] using typed.weaken
        (containers.fieldType name entry registered output environment (indexing.familyAt (subst sigma types.family) childIndex environment))

/-! ## Dependent method formation from typed motives and primitive bundles -/

structure MethodPrimitives (R : Rules Head) {n : Nat} (ambient : Ctx Head n)
    (types : TypeSyntax I Head n) (indexing : Indexing I Head)
    (containers : RegistrySyntax I registry Head) (domain : indexing.Domain n) (level : Head)
    (admittedIndices : IndexPredicate I := unrestrictedIndices)
    (resultLevel : Head := level) (methodLevel : Head := level)
    : Prop extends ConstructorPrimitives R ambient types indexing containers domain level admittedIndices where
  resultUniverse : R.isUniverse resultLevel
  methodUniverse : R.isUniverse methodLevel
  resultBound : resultLevel = methodLevel ∨ R.cumulative resultLevel methodLevel
  fieldClosure : ∃ result, R.join level methodLevel result ∧
    (result = methodLevel ∨ R.cumulative result methodLevel)
  methodClosure : ∃ result, R.join methodLevel methodLevel result ∧
    (result = methodLevel ∨ R.cumulative result methodLevel)
  bundle : ∀ {m : Nat} {target : Ctx Head m}
    (sigma : Sub Head n m), FormationSensitive.CtxMor R ambient target sigma →
    ∀ {context : List I.SortCode} name entry (registered : registry.lookup name = some entry)
      (output : entry.OutputExpr context) (environment : TermEnv I Head m context),
      EnvironmentTyped R target (fun sort => subst sigma (types.dataType sort)) environment →
      ∀ element predicate field, Typing R target element (.head level) →
        Typing R target predicate (.pi element (.head resultLevel)) →
        Typing R target field (containers.fieldType name entry registered output environment element) →
        Typing R target (containers.bundleType name entry registered output environment element predicate field)
          (.head methodLevel)

private theorem indexedPredicate_typed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {domain family motive index : Tm Head n} {level : Head}
    (motiveTyped : Typing R ambient motive
      (.pi domain (.pi (.app (rename wk family) (.var 0)) (.head level))))
    (indexTyped : Typing R ambient index domain) :
    Typing R ambient (.app motive index) (.pi (.app family index) (.head level)) := by
  have application := Typing.appElim motiveTyped indexTyped
  simp only [inst0, subst, subst0, Fin.cases_zero] at application
  rw [show subst (subst0 index) (rename wk family) = family from inst0_rename_wk _ _] at application
  exact application

theorem ConstructorPrimitives.predicateAt_typedOn {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level : Head}
    {admittedIndices : IndexPredicate I} {resultLevel : Head}
    (primitives : ConstructorPrimitives R ambient types indexing containers domain level admittedIndices)
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma)
    {context : List I.SortCode} (expression : I.IndexExpr context) (expressionAdmitted : admittedIndices expression)
    (environment : TermEnv I Head m context)
    (typed : EnvironmentTyped R target (fun sort => subst sigma (types.dataType sort)) environment)
    (motive : Tm Head m)
    (motiveTyped : Typing R target motive
      (motiveType indexing (subst sigma types.family) (indexing.mapDomain (subst sigma) domain) resultLevel)) :
    Typing R target (indexing.predicateAt motive expression environment)
      (.pi (indexing.familyAt (subst sigma types.family) expression environment) (.head resultLevel)) := by
  cases indexing with
  | unindexed unique => exact motiveTyped
  | indexed indices =>
      have index := primitives.indices sigma morphism expression expressionAdmitted environment typed
      exact indexedPredicate_typed motiveTyped index

private theorem boundedPi_formed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {firstLevel restLevel : Head} (firstUniverse : R.isUniverse firstLevel)
    (restUniverse : R.isUniverse restLevel)
    (closure : ∃ result, R.join firstLevel restLevel result ∧
      (result = restLevel ∨ R.cumulative result restLevel))
    {A : Tm Head n} {B : Tm Head (n + 1)}
    (first : Typing R ambient A (.head firstLevel))
    (rest : Typing R (.snoc ambient A) B (.head restLevel)) :
    Typing R ambient (.pi A B) (.head restLevel) := by
  obtain ⟨productLevel, productRule, productBound⟩ := closure
  have formed := Typing.piForm first firstUniverse rest restUniverse productRule
  rcases productBound with same | cumulative
  · exact same ▸ formed
  · exact .cumul formed cumulative

private theorem hypotheses_formedWith {R : Rules Head} {level : Head}
    (isUniverse : R.isUniverse level)
    (closure : ∃ result, R.join level level result ∧
      (result = level ∨ R.cumulative result level))
    {n : Nat} {ambient : Ctx Head n} (pending : List (Tm Head n)) (result : Tm Head n)
    (pendingTyped : ∀ type ∈ pending, Typing R ambient type (.head level))
    (resultTyped : Typing R ambient result (.head level)) :
    Typing R ambient (hypotheses pending result) (.head level) :=
  FunctionArgumentAdapters.curriedType_formed isUniverse closure pending result pendingTyped resultTyped

theorem ConstructorPrimitives.hypotheses_formed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level : Head}
    {admittedIndices : IndexPredicate I}
    (primitives : ConstructorPrimitives R ambient types indexing containers domain level admittedIndices)
    {m : Nat} {target : Ctx Head m} (pending : List (Tm Head m)) (result : Tm Head m)
    (pendingTyped : ∀ type ∈ pending, Typing R target type (.head level))
    (resultTyped : Typing R target result (.head level)) :
    Typing R target (hypotheses pending result) (.head level) :=
  hypotheses_formedWith primitives.isUniverse primitives.productClosure pending result pendingTyped resultTyped

theorem MethodPrimitives.liftResult {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n}
    {level resultLevel methodLevel : Head} {admittedIndices : IndexPredicate I}
    (primitives : MethodPrimitives R ambient types indexing containers domain level admittedIndices resultLevel methodLevel)
    {m : Nat} {target : Ctx Head m} {A : Tm Head m}
    (typed : Typing R target A (.head resultLevel)) : Typing R target A (.head methodLevel) := by
  rcases primitives.resultBound with same | cumulative
  · exact same ▸ typed
  · exact .cumul typed cumulative

theorem MethodPrimitives.fieldPiForm {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n}
    {level resultLevel methodLevel : Head} {admittedIndices : IndexPredicate I}
    (primitives : MethodPrimitives R ambient types indexing containers domain level admittedIndices resultLevel methodLevel)
    {m : Nat} {target : Ctx Head m} {A : Tm Head m} {B : Tm Head (m + 1)}
    (first : Typing R target A (.head level))
    (rest : Typing R (.snoc target A) B (.head methodLevel)) :
    Typing R target (.pi A B) (.head methodLevel) :=
  boundedPi_formed primitives.isUniverse primitives.methodUniverse primitives.fieldClosure first rest

theorem MethodPrimitives.piForm {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n}
    {level resultLevel methodLevel : Head} {admittedIndices : IndexPredicate I}
    (primitives : MethodPrimitives R ambient types indexing containers domain level admittedIndices resultLevel methodLevel)
    {m : Nat} {target : Ctx Head m} {A : Tm Head m} {B : Tm Head (m + 1)}
    (first : Typing R target A (.head methodLevel))
    (rest : Typing R (.snoc target A) B (.head methodLevel)) :
    Typing R target (.pi A B) (.head methodLevel) :=
  boundedPi_formed primitives.methodUniverse primitives.methodUniverse primitives.methodClosure first rest

theorem MethodPrimitives.hypotheses_formed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n}
    {level resultLevel methodLevel : Head} {admittedIndices : IndexPredicate I}
    (primitives : MethodPrimitives R ambient types indexing containers domain level admittedIndices resultLevel methodLevel)
    {m : Nat} {target : Ctx Head m} (pending : List (Tm Head m)) (result : Tm Head m)
    (pendingTyped : ∀ type ∈ pending, Typing R target type (.head methodLevel))
    (resultTyped : Typing R target result (.head methodLevel)) :
    Typing R target (hypotheses pending result) (.head methodLevel) :=
  hypotheses_formedWith primitives.methodUniverse primitives.methodClosure pending result pendingTyped resultTyped

private theorem methodMotive_weaken {n : Nat} (indexing : Indexing I Head)
    (family : Tm Head n) (domain : indexing.Domain n) (level : Head) :
    rename wk (motiveType indexing family domain level) =
      motiveType indexing (rename wk family) (indexing.mapDomain (rename wk) domain) level := by
  cases indexing <;> simp only [motiveType, Indexing.mapDomain, rename, rename_comp, liftRen, wk, Fin.cases_zero]
  rfl

private theorem methodDomain_weaken {n m : Nat} (indexing : Indexing I Head)
    (domain : indexing.Domain n) (sigma : Sub Head n m) :
    indexing.mapDomain (rename wk) (indexing.mapDomain (subst sigma) domain) =
      indexing.mapDomain (subst (fun i => rename wk (sigma i))) domain := by
  cases indexing with
  | indexed _ => exact Presentation.rename_subst wk sigma domain
  | unindexed _ => rfl

private theorem methodConstructor_apply {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {constructor A : Tm Head n} {B : Tm Head (n + 1)}
    (typed : Typing R ambient constructor (.pi A B)) :
    Typing R (.snoc ambient A) (.app (rename wk constructor) (.var 0)) B := by
  have applied := Typing.appElim typed.weaken (Typing.var (R := R) (Γ := .snoc ambient A) 0)
  have opening : inst0 (.var 0) (rename (liftRen wk) B) = B := by
    unfold inst0
    rw [subst_rename]
    conv => rhs; rw [← subst_ids B]
    apply subst_ext
    intro index
    exact Fin.cases rfl (fun _ => rfl) index
  exact opening ▸ applied

theorem Indexing.familyAt_weaken (indexing : Indexing I Head)
    {context : List I.SortCode} {n : Nat} (family : Tm Head n)
    (expression : I.IndexExpr context) (environment : TermEnv I Head n context) :
    rename wk (indexing.familyAt family expression environment) =
      indexing.familyAt (rename wk family) expression (weakenEnvironment environment) := by
  simpa only [← rename_as_substitution, weakenEnvironment] using
    indexing.familyAt_substitute family expression environment (fun index => .var (wk index))

theorem RegistrySyntax.fieldType_weaken (containers : RegistrySyntax I registry Head)
    {context : List I.SortCode} {n : Nat} name entry registered
    (output : entry.OutputExpr context) (environment : TermEnv I Head n context) (element : Tm Head n) :
    rename wk (containers.fieldType name entry registered output environment element) =
      containers.fieldType name entry registered output (weakenEnvironment environment) (rename wk element) := by
  simpa only [← rename_as_substitution, weakenEnvironment] using
    containers.fieldType_substitute name entry registered output environment element (fun index => .var (wk index))

theorem methodBody_formedOn {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level : Head}
    {admittedIndices : IndexPredicate I} {resultLevel methodLevel : Head}
    (primitives : MethodPrimitives R ambient types indexing containers domain level admittedIndices resultLevel methodLevel)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    (codeAdmitted : IndicesAdmitted admittedIndices code)
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma)
    (environment : TermEnv I Head m context)
    (typed : EnvironmentTyped R target (fun sort => subst sigma (types.dataType sort)) environment)
    (motive constructor : Tm Head m) (pending : List (Tm Head m))
    (motiveTyped : Typing R target motive
      (motiveType indexing (subst sigma types.family) (indexing.mapDomain (subst sigma) domain) resultLevel))
    (constructorTyped : Typing R target constructor
      (constructorType indexing containers code (types.map (subst sigma)) environment))
    (pendingTyped : ∀ type ∈ pending, Typing R target type (.head methodLevel)) :
    Typing R target
      (methodBody indexing containers code (types.map (subst sigma)) environment motive constructor pending)
      (.head methodLevel) := by
  induction code generalizing m with
  | result expression =>
      simp only [constructorType, TypeSyntax.map] at constructorTyped
      rw [methodBody]
      apply primitives.hypotheses_formed pending _ pendingTyped
      have predicate := primitives.toConstructorPrimitives.predicateAt_typedOn sigma morphism expression codeAdmitted
        environment typed motive motiveTyped
      apply primitives.liftResult
      simpa only [inst0, subst] using Typing.appElim predicate constructorTyped
  | data sort body ih =>
      have fieldType := (primitives.data sort).substitute morphism
      simp only [constructorType, TypeSyntax.map] at constructorTyped
      have constructorRest := methodConstructor_apply constructorTyped
      rw [methodBody]
      apply primitives.fieldPiForm fieldType
      rw [mappedTypes_weaken]
      apply ih codeAdmitted (fun i => rename wk (sigma i))
        (by intro index; simpa only [Presentation.rename_subst] using (morphism index).weaken)
        (.var 0, weakenEnvironment environment)
      · constructor
        · simpa only [Ctx.lookup_snoc_zero, Presentation.rename_subst] using
            (Typing.var (R := R) (Γ := .snoc target (subst sigma (types.dataType sort))) 0)
        · simpa only [Presentation.rename_subst] using typed.weaken (subst sigma (types.dataType sort))
      · simpa only [methodMotive_weaken, methodDomain_weaken, Presentation.rename_subst] using
          (motiveTyped.weaken (extension := subst sigma (types.dataType sort)))
      · simpa only [TypeSyntax.weaken, TypeSyntax.map, Presentation.rename_subst] using constructorRest
      · intro type member
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        exact (pendingTyped original originalMember).weaken
  | recursive expression rest ih =>
      have fieldType := primitives.toConstructorPrimitives.familyAt_formedOn sigma morphism expression codeAdmitted.1 environment typed
      simp only [constructorType, TypeSyntax.map] at constructorTyped
      have constructorRest := methodConstructor_apply constructorTyped
      rw [methodBody]
      apply primitives.fieldPiForm fieldType
      rw [mappedTypes_weaken]
      apply ih codeAdmitted.2 (fun i => rename wk (sigma i))
        (by intro index; simpa only [Presentation.rename_subst] using (morphism index).weaken)
        (weakenEnvironment environment)
      · simpa only [Presentation.rename_subst] using typed.weaken
          (indexing.familyAt (subst sigma types.family) expression environment)
      · simpa only [methodMotive_weaken, methodDomain_weaken, Presentation.rename_subst] using
          (motiveTyped.weaken (extension := indexing.familyAt (subst sigma types.family) expression environment))
      · simpa only [TypeSyntax.weaken, TypeSyntax.map, Presentation.rename_subst] using constructorRest
      · intro type member
        rcases List.mem_append.mp member with prior | fresh
        · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp prior
          exact (pendingTyped original originalMember).weaken
        · simp only [List.mem_singleton] at fresh
          subst type
          have weakenedEnvironment : EnvironmentTyped R
              (.snoc target (indexing.familyAt (subst sigma types.family) expression environment))
              (fun sort => subst (fun i => rename wk (sigma i)) (types.dataType sort))
              (weakenEnvironment environment) := by
            simpa only [Presentation.rename_subst] using typed.weaken
              (indexing.familyAt (subst sigma types.family) expression environment)
          have predicate := primitives.toConstructorPrimitives.predicateAt_typedOn
            (fun i => rename wk (sigma i))
            (by intro index; simpa only [Presentation.rename_subst] using (morphism index).weaken)
            expression codeAdmitted.1 (weakenEnvironment environment) weakenedEnvironment (rename wk motive)
            (by simpa only [methodMotive_weaken, methodDomain_weaken, Presentation.rename_subst] using
              (motiveTyped.weaken (extension := indexing.familyAt (subst sigma types.family) expression environment)))
          have child : Typing R (.snoc target (indexing.familyAt (subst sigma types.family) expression environment))
              (.var 0) (indexing.familyAt (subst (fun i => rename wk (sigma i)) types.family)
                expression (weakenEnvironment environment)) := by
            simpa only [Ctx.lookup_snoc_zero, Indexing.familyAt_weaken, Presentation.rename_subst] using
              (Typing.var (R := R) (Γ := .snoc target (indexing.familyAt (subst sigma types.family) expression environment)) 0)
          have application := Typing.appElim predicate child
          apply primitives.liftResult
          simpa only [inst0, subst] using application
  | nested name entry registered output childIndex rest ih =>
      have element := primitives.toConstructorPrimitives.familyAt_formedOn sigma morphism childIndex codeAdmitted.1 environment typed
      have fieldType := primitives.container sigma morphism name entry registered output environment typed _ element
      simp only [constructorType, TypeSyntax.map] at constructorTyped
      have constructorRest := methodConstructor_apply constructorTyped
      rw [methodBody]
      apply primitives.fieldPiForm fieldType
      rw [mappedTypes_weaken]
      apply ih codeAdmitted.2 (fun i => rename wk (sigma i))
        (by intro index; simpa only [Presentation.rename_subst] using (morphism index).weaken)
        (weakenEnvironment environment)
      · simpa only [Presentation.rename_subst] using typed.weaken
          (containers.fieldType name entry registered output environment
            (indexing.familyAt (subst sigma types.family) childIndex environment))
      · simpa only [methodMotive_weaken, methodDomain_weaken, Presentation.rename_subst] using
          (motiveTyped.weaken (extension := containers.fieldType name entry registered output environment
            (indexing.familyAt (subst sigma types.family) childIndex environment)))
      · simpa only [TypeSyntax.weaken, TypeSyntax.map, Presentation.rename_subst] using constructorRest
      · intro type member
        rcases List.mem_append.mp member with prior | fresh
        · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp prior
          exact (pendingTyped original originalMember).weaken
        · simp only [List.mem_singleton] at fresh
          subst type
          have weakenedEnvironment : EnvironmentTyped R
              (.snoc target (containers.fieldType name entry registered output environment
                (indexing.familyAt (subst sigma types.family) childIndex environment)))
              (fun sort => subst (fun i => rename wk (sigma i)) (types.dataType sort))
              (weakenEnvironment environment) := by
            simpa only [Presentation.rename_subst] using typed.weaken
              (containers.fieldType name entry registered output environment
                (indexing.familyAt (subst sigma types.family) childIndex environment))
          apply primitives.bundle (fun i => rename wk (sigma i))
            (by intro index; simpa only [Presentation.rename_subst] using (morphism index).weaken)
            name entry registered output (weakenEnvironment environment) weakenedEnvironment
          · simpa only [TypeSyntax.map, Presentation.rename_subst] using primitives.toConstructorPrimitives.familyAt_formedOn
              (fun i => rename wk (sigma i))
              (by intro index; simpa only [Presentation.rename_subst] using (morphism index).weaken)
              childIndex codeAdmitted.1 (weakenEnvironment environment) weakenedEnvironment
          · simpa only [TypeSyntax.map, Presentation.rename_subst] using primitives.toConstructorPrimitives.predicateAt_typedOn
              (fun i => rename wk (sigma i))
              (by intro index; simpa only [Presentation.rename_subst] using (morphism index).weaken)
              childIndex codeAdmitted.1 (weakenEnvironment environment) weakenedEnvironment (rename wk motive)
              (by simpa only [methodMotive_weaken, methodDomain_weaken, Presentation.rename_subst] using
                (motiveTyped.weaken (extension := containers.fieldType name entry registered output environment
                  (indexing.familyAt (subst sigma types.family) childIndex environment))))
          · simpa only [Ctx.lookup_snoc_zero, RegistrySyntax.fieldType_weaken,
              Indexing.familyAt_weaken, TypeSyntax.map, Presentation.rename_subst] using
              (Typing.var (R := R) (Γ := .snoc target (containers.fieldType name entry registered output environment
                (indexing.familyAt (subst sigma types.family) childIndex environment))) 0)

/-- Every generated dependent method forms once its actual constructor and
motive are typed and the registered bundle operation preserves formation. -/
theorem methodType_formedOn {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level : Head}
    {admittedIndices : IndexPredicate I} {resultLevel methodLevel : Head}
    (primitives : MethodPrimitives R ambient types indexing containers domain level admittedIndices resultLevel methodLevel)
    {parameters : Nat} (code : Code I registry parameters []) (codeAdmitted : IndicesAdmitted admittedIndices code)
    (name : String)
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma)
    (motive : Tm Head m)
    (motiveTyped : Typing R target motive
      (motiveType indexing (subst sigma types.family) (indexing.mapDomain (subst sigma) domain) resultLevel))
    (constructorTyped : Typing R target (subst sigma (types.constructor name))
      (constructorType indexing containers code (types.map (subst sigma)) PUnit.unit)) :
    Typing R target (methodType indexing containers code (types.map (subst sigma)) motive name)
      (.head methodLevel) :=
  methodBody_formedOn primitives code codeAdmitted sigma morphism PUnit.unit True.intro motive
    (subst sigma (types.constructor name)) [] motiveTyped constructorTyped (by simp)

/-! ## Complete eliminator formation with explicit universe contracts -/

def Indexing.DomainTyped (R : Rules Head) {n : Nat} (ambient : Ctx Head n)
    (indexing : Indexing I Head) (domain : indexing.Domain n) (level : Head) : Prop :=
  match indexing with
  | .indexed _ => Typing R ambient domain (.head level)
  | .unindexed _ => True

structure EliminatorPrimitives (R : Rules Head) {n : Nat} (ambient : Ctx Head n)
    (types : TypeSyntax I Head n) (indexing : Indexing I Head)
    (containers : RegistrySyntax I registry Head) (domain : indexing.Domain n)
    (level upper output : Head) (admittedIndices : IndexPredicate I := unrestrictedIndices)
    (resultLevel : Head := level) (methodLevel : Head := level) (resultSort : Head := upper) : Prop
    extends MethodPrimitives R ambient types indexing containers domain level admittedIndices resultLevel methodLevel where
  domainTyped : indexing.DomainTyped R ambient domain level
  levelTyping : R.headTyping resultLevel resultSort
  resultSortBound : resultSort = upper ∨ R.cumulative resultSort upper
  upperUniverse : R.isUniverse upper
  motiveClosure : ∃ result, R.join level upper result ∧ (result = upper ∨ R.cumulative result upper)
  eliminatorJoin : R.join upper methodLevel output
  outputUniverse : R.isUniverse output

theorem EliminatorPrimitives.resultHead_formed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n}
    {level upper output resultLevel methodLevel resultSort : Head} {admittedIndices : IndexPredicate I}
    (primitives : EliminatorPrimitives R ambient types indexing containers domain level upper output admittedIndices resultLevel methodLevel resultSort)
    {m : Nat} {target : Ctx Head m} : Typing R target (.head resultLevel) (.head upper) := by
  rcases primitives.resultSortBound with same | cumulative
  · exact same ▸ Typing.headType primitives.levelTyping
  · exact .cumul (.headType primitives.levelTyping) cumulative

theorem EliminatorPrimitives.motivePiForm {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level upper output : Head}
    {admittedIndices : IndexPredicate I} {resultLevel methodLevel resultSort : Head}
    (primitives : EliminatorPrimitives R ambient types indexing containers domain level upper output admittedIndices resultLevel methodLevel resultSort)
    {m : Nat} {target : Ctx Head m} {A : Tm Head m} {B : Tm Head (m + 1)}
    (first : Typing R target A (.head level))
    (rest : Typing R (.snoc target A) B (.head upper)) :
    Typing R target (.pi A B) (.head upper) := by
  obtain ⟨productLevel, productRule, productBound⟩ := primitives.motiveClosure
  have formed := Typing.piForm first primitives.isUniverse rest primitives.upperUniverse productRule
  rcases productBound with same | cumulative
  · exact same ▸ formed
  · exact .cumul formed cumulative

theorem motiveType_formed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level upper output : Head}
    {admittedIndices : IndexPredicate I} {resultLevel methodLevel resultSort : Head}
    (primitives : EliminatorPrimitives R ambient types indexing containers domain level upper output admittedIndices resultLevel methodLevel resultSort)
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma) :
    Typing R target (motiveType indexing (subst sigma types.family)
      (indexing.mapDomain (subst sigma) domain) resultLevel) (.head upper) := by
  cases indexing with
  | unindexed unique =>
      rw [motiveType]
      apply primitives.motivePiForm (primitives.family.substitute morphism)
      exact primitives.resultHead_formed
  | indexed indices =>
      have domainTyped := primitives.domainTyped.substitute morphism
      rw [motiveType]
      apply primitives.motivePiForm domainTyped
      have family := (primitives.family.substitute morphism).weaken (extension := subst sigma domain)
      have argument := Typing.var (R := R) (Γ := .snoc target (subst sigma domain)) 0
      have application := Typing.appElim family argument
      apply primitives.motivePiForm
        (show Typing R (.snoc target (subst sigma domain))
          (.app (rename wk (subst sigma types.family)) (.var 0)) (.head level) from
            by simpa only [inst0, subst, rename] using application)
      exact primitives.resultHead_formed

theorem resultType_formed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level upper output : Head}
    {admittedIndices : IndexPredicate I} {resultLevel methodLevel resultSort : Head}
    (primitives : EliminatorPrimitives R ambient types indexing containers domain level upper output admittedIndices resultLevel methodLevel resultSort)
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma)
    (motive : Tm Head m)
    (motiveTyped : Typing R target motive
      (motiveType indexing (subst sigma types.family) (indexing.mapDomain (subst sigma) domain) resultLevel)) :
    Typing R target (resultType indexing (subst sigma types.family) motive
      (indexing.mapDomain (subst sigma) domain)) (.head methodLevel) := by
  cases indexing with
  | unindexed unique =>
      rw [resultType]
      apply primitives.toMethodPrimitives.fieldPiForm (primitives.family.substitute morphism)
      have application := Typing.appElim
        (motiveTyped.weaken (extension := subst sigma types.family)) (Typing.var (R := R) 0)
      apply primitives.toMethodPrimitives.liftResult
      simpa only [inst0, subst, rename] using application
  | indexed indices =>
      have domainTyped := primitives.domainTyped.substitute morphism
      have family := (primitives.family.substitute morphism).weaken (extension := subst sigma domain)
      have argument := Typing.var (R := R) (Γ := .snoc target (subst sigma domain)) 0
      have familyApplication := Typing.appElim family argument
      have familyTyped : Typing R (.snoc target (subst sigma domain))
          (.app (rename wk (subst sigma types.family)) (.var 0)) (.head level) := by
        simpa only [inst0, subst, rename] using familyApplication
      rw [resultType]
      apply primitives.toMethodPrimitives.fieldPiForm domainTyped
      apply primitives.toMethodPrimitives.fieldPiForm familyTyped
      have weakenedMotive : Typing R (.snoc target (subst sigma domain)) (rename wk motive)
          (motiveType (.indexed indices) (rename wk (subst sigma types.family))
            (rename wk (subst sigma domain)) resultLevel) := by
        have weakened := motiveTyped.weaken (extension := subst sigma domain)
        simp only [Indexing.mapDomain] at weakened
        rw [methodMotive_weaken (.indexed indices) (subst sigma types.family)
          (subst sigma domain) resultLevel] at weakened
        exact weakened
      have predicate := indexedPredicate_typed weakenedMotive argument
      have application := Typing.appElim
        (predicate.weaken (extension := .app (rename wk (subst sigma types.family)) (.var 0)))
        (Typing.var (R := R) 0)
      have successor : Fin.succ (0 : Fin (m + 1)) = (1 : Fin (m + 1 + 1)) := by
        ext
        simp
      apply primitives.toMethodPrimitives.liftResult
      simpa only [rename, inst0, subst, wk, successor] using application

theorem methodsType_formedOn {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level upper output : Head}
    {admittedIndices : IndexPredicate I} {resultLevel methodLevel resultSort : Head}
    (primitives : EliminatorPrimitives R ambient types indexing containers domain level upper output admittedIndices resultLevel methodLevel resultSort)
    {parameters : Nat} (constructors : List (String × Code I registry parameters []))
    (indicesAdmitted : ∀ item ∈ constructors, IndicesAdmitted admittedIndices item.2)
    (constructorsTyped : ∀ item ∈ constructors, Typing R ambient (types.constructor item.1)
      (constructorType indexing containers item.2 types PUnit.unit))
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma)
    (motive : Tm Head m)
    (motiveTyped : Typing R target motive
      (motiveType indexing (subst sigma types.family) (indexing.mapDomain (subst sigma) domain) resultLevel)) :
    Typing R target (methodsType indexing containers constructors (types.map (subst sigma)) motive
      (indexing.mapDomain (subst sigma) domain)) (.head methodLevel) := by
  induction constructors generalizing m with
  | nil => exact resultType_formed primitives sigma morphism motive motiveTyped
  | cons constructor rest ih =>
      rcases constructor with ⟨name, code⟩
      have constructorTyped := (constructorsTyped (name, code) (by simp)).substitute morphism
      have constructorSubstitution : subst sigma (constructorType indexing containers code types PUnit.unit) =
          constructorType indexing containers code (types.map (subst sigma)) PUnit.unit :=
        constructorType_substitute indexing containers code types PUnit.unit sigma
      have methodTyped := methodType_formedOn primitives.toMethodPrimitives code (indicesAdmitted (name, code) (by simp)) name sigma morphism motive
        motiveTyped (constructorSubstitution ▸ constructorTyped)
      rw [methodsType]
      apply primitives.toMethodPrimitives.piForm methodTyped
      rw [mappedTypes_weaken, methodDomain_weaken]
      apply ih (by intro item member; exact indicesAdmitted item (List.mem_cons_of_mem _ member))
        (by intro item member; exact constructorsTyped item (List.mem_cons_of_mem _ member))
        (fun i => rename wk (sigma i))
        (by intro index; simpa only [Presentation.rename_subst] using (morphism index).weaken)
        (rename wk motive)
      simpa only [methodMotive_weaken, methodDomain_weaken, Presentation.rename_subst] using
        (motiveTyped.weaken (extension := methodType indexing containers code (types.map (subst sigma)) motive name))

theorem eliminatorType_formedOn {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level upper output : Head}
    {admittedIndices : IndexPredicate I} {resultLevel methodLevel resultSort : Head}
    (primitives : EliminatorPrimitives R ambient types indexing containers domain level upper output admittedIndices resultLevel methodLevel resultSort)
    {parameters : Nat} (constructors : List (String × Code I registry parameters []))
    (indicesAdmitted : ∀ item ∈ constructors, IndicesAdmitted admittedIndices item.2)
    (constructorsTyped : ∀ item ∈ constructors, Typing R ambient (types.constructor item.1)
      (constructorType indexing containers item.2 types PUnit.unit))
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma) :
    Typing R target (eliminatorType indexing containers constructors (types.map (subst sigma))
      (indexing.mapDomain (subst sigma) domain) resultLevel) (.head output) := by
  rw [eliminatorType]
  apply Typing.piForm (motiveType_formed primitives sigma morphism) primitives.upperUniverse
    ?_ primitives.methodUniverse primitives.eliminatorJoin
  rw [mappedTypes_weaken, methodDomain_weaken]
  apply methodsType_formedOn primitives constructors indicesAdmitted constructorsTyped (fun i => rename wk (sigma i))
    (by intro index; simpa only [Presentation.rename_subst] using (morphism index).weaken) (.var 0)
  simpa only [Ctx.lookup_snoc_zero, methodMotive_weaken, methodDomain_weaken,
    Presentation.rename_subst] using
      (Typing.var (R := R) (Γ := .snoc target (motiveType indexing (subst sigma types.family)
        (indexing.mapDomain (subst sigma) domain) resultLevel)) 0)

/-! ## Unrestricted index typing as a sufficient specialization -/

theorem ConstructorPrimitives.familyAt_formed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level : Head}
    (primitives : ConstructorPrimitives R ambient types indexing containers domain level)
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma)
    {context : List I.SortCode} (expression : I.IndexExpr context)
    (environment : TermEnv I Head m context)
    (typed : EnvironmentTyped R target (fun sort => subst sigma (types.dataType sort)) environment) :
    Typing R target (indexing.familyAt (subst sigma types.family) expression environment) (.head level) :=
  primitives.familyAt_formedOn sigma morphism expression True.intro environment typed

theorem constructorType_formed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level : Head}
    (primitives : ConstructorPrimitives R ambient types indexing containers domain level)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma)
    (environment : TermEnv I Head m context)
    (typed : EnvironmentTyped R target (fun sort => subst sigma (types.dataType sort)) environment) :
    Typing R target (constructorType indexing containers code (types.map (subst sigma)) environment)
      (.head level) :=
  constructorType_formedOn primitives code (indices_unrestricted code) sigma morphism environment typed

theorem ConstructorPrimitives.predicateAt_typed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level : Head}
    (primitives : ConstructorPrimitives R ambient types indexing containers domain level)
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma)
    {context : List I.SortCode} (expression : I.IndexExpr context)
    (environment : TermEnv I Head m context)
    (typed : EnvironmentTyped R target (fun sort => subst sigma (types.dataType sort)) environment)
    (motive : Tm Head m)
    (motiveTyped : Typing R target motive
      (motiveType indexing (subst sigma types.family) (indexing.mapDomain (subst sigma) domain) level)) :
    Typing R target (indexing.predicateAt motive expression environment)
      (.pi (indexing.familyAt (subst sigma types.family) expression environment) (.head level)) :=
  primitives.predicateAt_typedOn sigma morphism expression True.intro environment typed motive motiveTyped

theorem methodBody_formed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level : Head}
    (primitives : MethodPrimitives R ambient types indexing containers domain level)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma)
    (environment : TermEnv I Head m context)
    (typed : EnvironmentTyped R target (fun sort => subst sigma (types.dataType sort)) environment)
    (motive constructor : Tm Head m) (pending : List (Tm Head m))
    (motiveTyped : Typing R target motive
      (motiveType indexing (subst sigma types.family) (indexing.mapDomain (subst sigma) domain) level))
    (constructorTyped : Typing R target constructor
      (constructorType indexing containers code (types.map (subst sigma)) environment))
    (pendingTyped : ∀ type ∈ pending, Typing R target type (.head level)) :
    Typing R target
      (methodBody indexing containers code (types.map (subst sigma)) environment motive constructor pending)
      (.head level) :=
  methodBody_formedOn primitives code (indices_unrestricted code) sigma morphism environment typed motive constructor pending motiveTyped constructorTyped pendingTyped

theorem methodType_formed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level : Head}
    (primitives : MethodPrimitives R ambient types indexing containers domain level)
    {parameters : Nat} (code : Code I registry parameters []) (name : String)
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma)
    (motive : Tm Head m)
    (motiveTyped : Typing R target motive
      (motiveType indexing (subst sigma types.family) (indexing.mapDomain (subst sigma) domain) level))
    (constructorTyped : Typing R target (subst sigma (types.constructor name))
      (constructorType indexing containers code (types.map (subst sigma)) PUnit.unit)) :
    Typing R target (methodType indexing containers code (types.map (subst sigma)) motive name)
      (.head level) :=
  methodType_formedOn primitives code (indices_unrestricted code) name sigma morphism motive motiveTyped constructorTyped

theorem methodsType_formed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level upper output : Head}
    (primitives : EliminatorPrimitives R ambient types indexing containers domain level upper output)
    {parameters : Nat} (constructors : List (String × Code I registry parameters []))
    (constructorsTyped : ∀ item ∈ constructors, Typing R ambient (types.constructor item.1)
      (constructorType indexing containers item.2 types PUnit.unit))
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma)
    (motive : Tm Head m)
    (motiveTyped : Typing R target motive
      (motiveType indexing (subst sigma types.family) (indexing.mapDomain (subst sigma) domain) level)) :
    Typing R target (methodsType indexing containers constructors (types.map (subst sigma)) motive
      (indexing.mapDomain (subst sigma) domain)) (.head level) :=
  methodsType_formedOn primitives constructors (by intro item _; exact indices_unrestricted item.2) constructorsTyped sigma morphism motive motiveTyped

theorem eliminatorType_formed {R : Rules Head} {n : Nat} {ambient : Ctx Head n}
    {types : TypeSyntax I Head n} {indexing : Indexing I Head}
    {containers : RegistrySyntax I registry Head} {domain : indexing.Domain n} {level upper output : Head}
    (primitives : EliminatorPrimitives R ambient types indexing containers domain level upper output)
    {parameters : Nat} (constructors : List (String × Code I registry parameters []))
    (constructorsTyped : ∀ item ∈ constructors, Typing R ambient (types.constructor item.1)
      (constructorType indexing containers item.2 types PUnit.unit))
    {m : Nat} {target : Ctx Head m} (sigma : Sub Head n m)
    (morphism : FormationSensitive.CtxMor R ambient target sigma) :
    Typing R target (eliminatorType indexing containers constructors (types.map (subst sigma))
      (indexing.mapDomain (subst sigma) domain) level) (.head output) :=
  eliminatorType_formedOn primitives constructors (by intro item _; exact indices_unrestricted item.2) constructorsTyped sigma morphism

#print axioms ConstructorPrimitives.familyAt_formed
#print axioms constructorType_formed
#print axioms ConstructorPrimitives.predicateAt_typed
#print axioms methodBody_formed
#print axioms methodType_formed
#print axioms methodsType_formed
#print axioms eliminatorType_formed
#print axioms ConstructorPrimitives.familyAt_formedOn
#print axioms constructorType_formedOn
#print axioms ConstructorPrimitives.predicateAt_typedOn
#print axioms methodBody_formedOn
#print axioms methodType_formedOn
#print axioms methodsType_formedOn
#print axioms eliminatorType_formedOn

end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestTypes


/-! ## Naturality of generated declaration types

A head map acts on the actual index interpretation and registered field and
bundle syntax. These primitive naturality laws extend through source binders,
ordered induction hypotheses and the complete generated eliminator. This is a
syntactic coherence theorem; typing transport needs its own rule interpretation.
-/

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestTypes
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open IndexedInductive.Guest
open IndexedInductive.Guest.Types (weakenEnvironment mapEnv_map)

universe u
variable {I : Interface.{u}} {registry : Registry I} {Head : Type}

def Indexing.HeadNatural (indexing : Indexing I Head) (map : Head → Head) : Prop :=
  match indexing with
  | .indexed indices => ∀ {n : Nat} {context : List I.SortCode}
      (expression : I.IndexExpr context) (environment : TermEnv I Head n context),
      (indices.term expression environment).mapHead map =
        indices.term expression (mapEnv (Tm.mapHead map) environment)
  | .unindexed _ => True

structure RegistrySyntax.HeadNatural (source target : RegistrySyntax I registry Head)
    (map : Head → Head) : Prop where
  field : ∀ {context : List I.SortCode} {n : Nat} name entry registered
    (output : entry.OutputExpr context) (environment : TermEnv I Head n context) (element : Tm Head n),
    (source.fieldType name entry registered output environment element).mapHead map =
      target.fieldType name entry registered output (mapEnv (Tm.mapHead map) environment) (element.mapHead map)
  bundle : ∀ {context : List I.SortCode} {n : Nat} name entry registered
    (output : entry.OutputExpr context) (environment : TermEnv I Head n context)
    (element predicate field : Tm Head n),
    (source.bundleType name entry registered output environment element predicate field).mapHead map =
      target.bundleType name entry registered output (mapEnv (Tm.mapHead map) environment)
        (element.mapHead map) (predicate.mapHead map) (field.mapHead map)

theorem Indexing.familyAt_mapHead (indexing : Indexing I Head) (map : Head → Head)
    (natural : indexing.HeadNatural map) {context : List I.SortCode} {n : Nat}
    (family : Tm Head n) (expression : I.IndexExpr context) (environment : TermEnv I Head n context) :
    (indexing.familyAt family expression environment).mapHead map =
      indexing.familyAt (family.mapHead map) expression (mapEnv (Tm.mapHead map) environment) := by
  cases indexing with
  | unindexed _ => rfl
  | indexed indices => simp only [Indexing.familyAt, Tm.mapHead, natural expression environment]

theorem weakenEnvironment_mapHead (map : Head → Head) {context : List I.SortCode} {n : Nat}
    (environment : TermEnv I Head n context) :
    mapEnv (Tm.mapHead map) (weakenEnvironment environment) =
      weakenEnvironment (mapEnv (Tm.mapHead map) environment) := by
  simp only [weakenEnvironment, mapEnv_map, Tm.mapHead_rename]

theorem TypeSyntax.weaken_mapHead (map : Head → Head) {n : Nat} (types : TypeSyntax I Head n) :
    types.weaken.map (Tm.mapHead map) = (types.map (Tm.mapHead map)).weaken := by
  cases types
  simp only [TypeSyntax.weaken, TypeSyntax.map, Tm.mapHead_rename]

theorem Indexing.mapDomain_weaken_mapHead (indexing : Indexing I Head) (map : Head → Head)
    {n : Nat} (domain : indexing.Domain n) :
    indexing.mapDomain (Tm.mapHead map) (indexing.mapDomain (rename wk) domain) =
      indexing.mapDomain (rename wk) (indexing.mapDomain (Tm.mapHead map) domain) := by
  cases indexing with
  | unindexed _ => rfl
  | indexed _ => exact Tm.mapHead_rename map wk domain

theorem constructorType_mapHead (indexing : Indexing I Head) (map : Head → Head)
    (indexNatural : indexing.HeadNatural map) {source target : RegistrySyntax I registry Head}
    (containerNatural : source.HeadNatural target map)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {n : Nat} (types : TypeSyntax I Head n) (environment : TermEnv I Head n context) :
    (constructorType indexing source code types environment).mapHead map =
      constructorType indexing target code (types.map (Tm.mapHead map))
        (mapEnv (Tm.mapHead map) environment) := by
  induction code generalizing n with
  | result expression =>
      simp only [constructorType, indexing.familyAt_mapHead map indexNatural, TypeSyntax.map]
  | data sort body ih =>
      simp only [constructorType, Tm.mapHead, TypeSyntax.map]
      congr 1
      simpa only [mapEnv, Tm.mapHead, weakenEnvironment_mapHead, TypeSyntax.weaken,
        TypeSyntax.map, Tm.mapHead_rename]
        using ih types.weaken (.var 0, weakenEnvironment environment)
  | recursive expression rest ih =>
      simp only [constructorType, Tm.mapHead, indexing.familyAt_mapHead map indexNatural, TypeSyntax.map]
      congr 1
      simpa only [weakenEnvironment_mapHead, TypeSyntax.weaken, TypeSyntax.map, Tm.mapHead_rename] using
        ih types.weaken (weakenEnvironment environment)
  | nested name entry registered output childIndex rest ih =>
      simp only [constructorType, Tm.mapHead, containerNatural.field,
        indexing.familyAt_mapHead map indexNatural, TypeSyntax.map]
      congr 1
      simpa only [weakenEnvironment_mapHead, TypeSyntax.weaken, TypeSyntax.map, Tm.mapHead_rename] using
        ih types.weaken (weakenEnvironment environment)


theorem Indexing.predicateAt_mapHead (indexing : Indexing I Head) (map : Head → Head)
    (natural : indexing.HeadNatural map) {context : List I.SortCode} {n : Nat}
    (predicate : Tm Head n) (expression : I.IndexExpr context) (environment : TermEnv I Head n context) :
    (indexing.predicateAt predicate expression environment).mapHead map =
      indexing.predicateAt (predicate.mapHead map) expression (mapEnv (Tm.mapHead map) environment) :=
  indexing.familyAt_mapHead map natural predicate expression environment

theorem hypotheses_mapHead (map : Head → Head) {n : Nat}
    (types : List (Tm Head n)) (result : Tm Head n) :
    (hypotheses types result).mapHead map =
      hypotheses (types.map (Tm.mapHead map)) (result.mapHead map) :=
  FunctionArgumentAdapters.curriedType_mapHead types result map

theorem methodBody_mapHead (indexing : Indexing I Head) (map : Head → Head)
    (indexNatural : indexing.HeadNatural map) {source target : RegistrySyntax I registry Head}
    (containerNatural : source.HeadNatural target map)
    {parameters : Nat} {context : List I.SortCode} (code : Code I registry parameters context)
    {n : Nat} (types : TypeSyntax I Head n) (environment : TermEnv I Head n context)
    (motive constructor : Tm Head n) (pending : List (Tm Head n)) :
    (methodBody indexing source code types environment motive constructor pending).mapHead map =
      methodBody indexing target code (types.map (Tm.mapHead map))
        (mapEnv (Tm.mapHead map) environment) (motive.mapHead map) (constructor.mapHead map)
        (pending.map (Tm.mapHead map)) := by
  induction code generalizing n with
  | result expression =>
      simp only [methodBody, hypotheses_mapHead, Tm.mapHead,
        indexing.predicateAt_mapHead map indexNatural]
  | data sort body ih =>
      simp only [methodBody, Tm.mapHead, TypeSyntax.map]
      congr 1
      simpa only [mapEnv, Tm.mapHead, weakenEnvironment_mapHead, TypeSyntax.weaken, TypeSyntax.map,
        Tm.mapHead_rename, List.map_map, Function.comp_def] using
        ih types.weaken (.var 0, weakenEnvironment environment) (rename wk motive)
          (.app (rename wk constructor) (.var 0)) (pending.map (rename wk))
  | recursive expression rest ih =>
      simp only [methodBody, Tm.mapHead, indexing.familyAt_mapHead map indexNatural, TypeSyntax.map]
      congr 1
      convert ih types.weaken (weakenEnvironment environment) (rename wk motive)
          (.app (rename wk constructor) (.var 0))
          ((pending.map (rename wk)) ++
            [.app (indexing.predicateAt (rename wk motive) expression (weakenEnvironment environment)) (.var 0)]) using 1
      all_goals simp only [Tm.mapHead, weakenEnvironment_mapHead, TypeSyntax.weaken, TypeSyntax.map,
        Tm.mapHead_rename, List.map_map, Function.comp_def, List.map_append, List.map_cons, List.map_nil,
        indexing.predicateAt_mapHead map indexNatural]
  | nested name entry registered output childIndex rest ih =>
      simp only [methodBody, Tm.mapHead, containerNatural.field,
        indexing.familyAt_mapHead map indexNatural, TypeSyntax.map]
      congr 1
      simpa only [Tm.mapHead, weakenEnvironment_mapHead, TypeSyntax.weaken, TypeSyntax.map,
        Tm.mapHead_rename, List.map_map, Function.comp_def, List.map_append, List.map_cons, List.map_nil,
        containerNatural.bundle, indexing.familyAt_mapHead map indexNatural,
        indexing.predicateAt_mapHead map indexNatural] using
        ih types.weaken (weakenEnvironment environment) (rename wk motive)
          (.app (rename wk constructor) (.var 0))
          ((pending.map (rename wk)) ++
            [source.bundleType name entry registered output (weakenEnvironment environment)
              (indexing.familyAt (rename wk types.family) childIndex (weakenEnvironment environment))
              (indexing.predicateAt (rename wk motive) childIndex (weakenEnvironment environment)) (.var 0)])

theorem methodType_mapHead (indexing : Indexing I Head) (map : Head → Head)
    (indexNatural : indexing.HeadNatural map) {source target : RegistrySyntax I registry Head}
    (containerNatural : source.HeadNatural target map) {parameters n : Nat}
    (code : Code I registry parameters []) (types : TypeSyntax I Head n) (motive : Tm Head n) (name : String) :
    (methodType indexing source code types motive name).mapHead map =
      methodType indexing target code (types.map (Tm.mapHead map)) (motive.mapHead map) name :=
  methodBody_mapHead indexing map indexNatural containerNatural code types PUnit.unit motive
    (types.constructor name) []

theorem motiveType_mapHead (indexing : Indexing I Head) (map : Head → Head) {n : Nat}
    (family : Tm Head n) (domain : indexing.Domain n) (universeHead : Head) :
    (motiveType indexing family domain universeHead).mapHead map =
      motiveType indexing (family.mapHead map) (indexing.mapDomain (Tm.mapHead map) domain)
        (map universeHead) := by
  cases indexing <;> simp only [motiveType, Indexing.mapDomain, Tm.mapHead, Tm.mapHead_rename]

theorem resultType_mapHead (indexing : Indexing I Head) (map : Head → Head) {n : Nat}
    (family motive : Tm Head n) (domain : indexing.Domain n) :
    (resultType indexing family motive domain).mapHead map =
      resultType indexing (family.mapHead map) (motive.mapHead map)
        (indexing.mapDomain (Tm.mapHead map) domain) := by
  cases indexing <;> simp only [resultType, Indexing.mapDomain, Tm.mapHead, Tm.mapHead_rename]

theorem methodsType_mapHead (indexing : Indexing I Head) (map : Head → Head)
    (indexNatural : indexing.HeadNatural map) {source target : RegistrySyntax I registry Head}
    (containerNatural : source.HeadNatural target map) {parameters : Nat}
    (constructors : List (String × Code I registry parameters [])) {n : Nat}
    (types : TypeSyntax I Head n) (motive : Tm Head n) (domain : indexing.Domain n) :
    (methodsType indexing source constructors types motive domain).mapHead map =
      methodsType indexing target constructors (types.map (Tm.mapHead map)) (motive.mapHead map)
        (indexing.mapDomain (Tm.mapHead map) domain) := by
  induction constructors generalizing n with
  | nil => exact resultType_mapHead indexing map types.family motive domain
  | cons first rest ih =>
      simp only [methodsType, Tm.mapHead, methodType_mapHead indexing map indexNatural containerNatural]
      congr 1
      have recursive := ih types.weaken (rename wk motive) (indexing.mapDomain (rename wk) domain)
      rw [TypeSyntax.weaken_mapHead, Tm.mapHead_rename, indexing.mapDomain_weaken_mapHead] at recursive
      exact recursive

theorem eliminatorType_mapHead (indexing : Indexing I Head) (map : Head → Head)
    (indexNatural : indexing.HeadNatural map) {source target : RegistrySyntax I registry Head}
    (containerNatural : source.HeadNatural target map) {parameters n : Nat}
    (constructors : List (String × Code I registry parameters []))
    (types : TypeSyntax I Head n) (domain : indexing.Domain n) (universeHead : Head) :
    (eliminatorType indexing source constructors types domain universeHead).mapHead map =
      eliminatorType indexing target constructors (types.map (Tm.mapHead map))
        (indexing.mapDomain (Tm.mapHead map) domain) (map universeHead) := by
  simp only [eliminatorType, Tm.mapHead, motiveType_mapHead,
    methodsType_mapHead indexing map indexNatural containerNatural]
  rw [TypeSyntax.weaken_mapHead, indexing.mapDomain_weaken_mapHead]
  rfl

end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestTypes
