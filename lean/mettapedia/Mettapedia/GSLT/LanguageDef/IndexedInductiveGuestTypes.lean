import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuest

/-!
# Dependent declaration types generated from indexed constructor codes

Types and constructor prefixes live in an explicit guest parameter context.
Their substitution is transported through every field, method and induction
hypothesis binder. Thus a parameter such as `A : U` can occur in the data sorts,
family prefix and constructor prefixes of a generated vector declaration.

This module generates intrinsically scoped raw types and proves substitution
coherence and structural strict positivity. Universe formation, declaration
formation and computation authority remain judgments of the selected DTT.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Types

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

universe u
variable {I : Interface.{u}} {Head : Type}

/-- Guest interpretations over explicit parameters. `family` and constructor
prefixes may already be applied to those parameters. Formation is not a field. -/
structure TypeSyntax (I : Interface.{u}) (Head : Type) (n : Nat) where
  dataType : I.SortCode → Tm Head n
  indexType : Tm Head n
  family : Tm Head n
  constructor : String → Tm Head n
  motiveUniverse : Head

def TypeSyntax.map {n m : Nat} (mapping : Tm Head n → Tm Head m)
    (types : TypeSyntax I Head n) : TypeSyntax I Head m where
  dataType := fun sort => mapping (types.dataType sort)
  indexType := mapping types.indexType
  family := mapping types.family
  constructor := fun name => mapping (types.constructor name)
  motiveUniverse := types.motiveUniverse

def TypeSyntax.weaken {n : Nat} (types : TypeSyntax I Head n) : TypeSyntax I Head (n + 1) :=
  types.map (rename wk)

def motiveAt {n : Nat} (motive index value : Tm Head n) : Tm Head n :=
  .app (.app motive index) value

def weakenEnvironment {n : Nat} {context : List I.SortCode}
    (environment : TermEnv I Head n context) : TermEnv I Head (n + 1) context :=
  mapEnv (rename wk) environment

theorem mapEnv_map {a b c : Nat} (f : Tm Head a → Tm Head b)
    (g : Tm Head b → Tm Head c) {context : List I.SortCode}
    (environment : TermEnv I Head a context) :
    mapEnv g (mapEnv f environment) = mapEnv (fun term => g (f term)) environment := by
  induction context with
  | nil => rfl
  | cons sort rest ih => exact congrArg (Prod.mk _) (ih environment.2)

theorem weakenEnvironment_substitute {n m : Nat} (substitution : Sub Head n m)
    {context : List I.SortCode} (environment : TermEnv I Head n context) :
    mapEnv (subst (liftSub substitution)) (weakenEnvironment environment) =
      weakenEnvironment (mapEnv (subst substitution) environment) := by
  simp only [weakenEnvironment, mapEnv_map, subst_liftSub_wk]

theorem TypeSyntax.weaken_substitute {n m : Nat} (substitution : Sub Head n m)
    (types : TypeSyntax I Head n) :
    types.weaken.map (subst (liftSub substitution)) = (types.map (subst substitution)).weaken := by
  cases types
  simp only [weaken, map, subst_liftSub_wk]

def constructorType (indices : IndexSyntax I Head) :
    {context : List I.SortCode} → (code : Code I context) → {n : Nat} →
      TypeSyntax I Head n → TermEnv I Head n context → Tm Head n
  | _, .result expression, _, types, environment =>
      .app types.family (indices.term expression environment)
  | _, .data sort body, _, types, environment =>
      .pi (types.dataType sort)
        (constructorType indices body types.weaken (.var 0, weakenEnvironment environment))
  | _, .recursive expression rest, _, types, environment =>
      .pi (.app types.family (indices.term expression environment))
        (constructorType indices rest types.weaken (weakenEnvironment environment))

theorem constructorType_substitute (indices : IndexSyntax I Head)
    {context : List I.SortCode} (code : Code I context) {n m : Nat}
    (types : TypeSyntax I Head n) (environment : TermEnv I Head n context)
    (substitution : Sub Head n m) :
    subst substitution (constructorType indices code types environment) =
      constructorType indices code (types.map (subst substitution))
        (mapEnv (subst substitution) environment) := by
  induction code generalizing n m with
  | result expression => simp [constructorType, subst, indices.substitute, TypeSyntax.map]
  | data sort body ih =>
      simp only [constructorType, subst, TypeSyntax.map]
      congr 1
      simpa only [mapEnv, subst, liftSub, Fin.cases_zero, weakenEnvironment_substitute,
        TypeSyntax.weaken, TypeSyntax.map, subst_liftSub_wk]
        using ih types.weaken (.var 0, weakenEnvironment environment) (liftSub substitution)
  | recursive expression rest ih =>
      simp only [constructorType, subst, indices.substitute, TypeSyntax.map]
      congr 1
      simpa only [weakenEnvironment_substitute, TypeSyntax.weaken, TypeSyntax.map, subst_liftSub_wk]
        using ih types.weaken (weakenEnvironment environment) (liftSub substitution)

/-- Methods receive all original fields first, then their induction hypotheses
in recursive-field order, exactly as in the computation-schema ABI. -/
def hypotheses {n : Nat} (motive : Tm Head n)
    (children : List (Tm Head n × Tm Head n)) (result : Tm Head n) : Tm Head n :=
  match children with
  | [] => result
  | (index, child) :: rest =>
      .pi (motiveAt motive index child)
        (hypotheses (rename wk motive)
          (rest.map fun pair => (rename wk pair.1, rename wk pair.2))
          (rename wk result))
termination_by children.length
  decreasing_by simp_wf

def methodBody (indices : IndexSyntax I Head) :
    {context : List I.SortCode} → (code : Code I context) → {n : Nat} →
      TypeSyntax I Head n → TermEnv I Head n context → Tm Head n → Tm Head n →
      List (Tm Head n × Tm Head n) → Tm Head n
  | _, .result expression, _, _, environment, motive, constructor, children =>
      hypotheses motive children (motiveAt motive (indices.term expression environment) constructor)
  | _, .data sort body, _, types, environment, motive, constructor, children =>
      .pi (types.dataType sort)
        (methodBody indices body types.weaken (.var 0, weakenEnvironment environment)
          (rename wk motive) (.app (rename wk constructor) (.var 0))
          (children.map fun pair => (rename wk pair.1, rename wk pair.2)))
  | _, .recursive expression rest, _, types, environment, motive, constructor, children =>
      .pi (.app types.family (indices.term expression environment))
        (methodBody indices rest types.weaken (weakenEnvironment environment)
          (rename wk motive) (.app (rename wk constructor) (.var 0))
          ((children.map fun pair => (rename wk pair.1, rename wk pair.2)) ++
            [(rename wk (indices.term expression environment), .var 0)]))

def methodType (indices : IndexSyntax I Head) (constructor : NamedConstructor I [])
    {n : Nat} (types : TypeSyntax I Head n) (motive : Tm Head n) : Tm Head n :=
  methodBody indices constructor.body types PUnit.unit motive
    (types.constructor constructor.name) []

def motiveType {n : Nat} (types : TypeSyntax I Head n) : Tm Head n :=
  .pi types.indexType
    (.pi (.app (rename wk types.family) (.var 0)) (.head types.motiveUniverse))

def methodsType (indices : IndexSyntax I Head) (constructors : List (NamedConstructor I []))
    {n : Nat} (types : TypeSyntax I Head n) (motive : Tm Head n) : Tm Head n :=
  match constructors with
  | [] => .pi types.indexType
      (.pi (.app (rename wk types.family) (.var 0))
        (motiveAt (rename wk (rename wk motive)) (.var 1) (.var 0)))
  | constructor :: rest => .pi (methodType indices constructor types motive)
      (methodsType indices rest types.weaken (rename wk motive))

def eliminatorType (indices : IndexSyntax I Head) (admitted : Admitted I [])
    {n : Nat} (types : TypeSyntax I Head n) : Tm Head n :=
  .pi (motiveType types)
    (methodsType indices admitted.constructors types.weaken (.var 0))

theorem hypotheses_substitute {n m : Nat} (motive : Tm Head n)
    (children : List (Tm Head n × Tm Head n)) (result : Tm Head n)
    (substitution : Sub Head n m) :
    subst substitution (hypotheses motive children result) =
      hypotheses (subst substitution motive)
        (children.map fun pair => (subst substitution pair.1, subst substitution pair.2))
        (subst substitution result) := by
  cases children with
  | nil => simp only [hypotheses, List.map_nil]
  | cons pair rest =>
      rcases pair with ⟨index, child⟩
      simp only [hypotheses, List.map_cons, motiveAt, subst]
      congr 1
      simpa only [List.map_map, Function.comp_def, subst_liftSub_wk] using
        hypotheses_substitute (rename wk motive)
          (rest.map fun pair => (rename wk pair.1, rename wk pair.2))
          (rename wk result) (liftSub substitution)
termination_by children.length
  decreasing_by simp_wf

theorem methodBody_substitute (indices : IndexSyntax I Head)
    {context : List I.SortCode} (code : Code I context) {n m : Nat}
    (types : TypeSyntax I Head n) (environment : TermEnv I Head n context)
    (motive constructor : Tm Head n) (children : List (Tm Head n × Tm Head n))
    (substitution : Sub Head n m) :
    subst substitution (methodBody indices code types environment motive constructor children) =
      methodBody indices code (types.map (subst substitution))
        (mapEnv (subst substitution) environment) (subst substitution motive)
        (subst substitution constructor)
        (children.map fun pair => (subst substitution pair.1, subst substitution pair.2)) := by
  induction code generalizing n m with
  | result expression =>
      simp only [methodBody, hypotheses_substitute, motiveAt, subst, indices.substitute]
  | data sort body ih =>
      simp only [methodBody, subst, TypeSyntax.map]
      congr 1
      simpa only [mapEnv, subst, liftSub, Fin.cases_zero, weakenEnvironment_substitute,
        TypeSyntax.weaken, TypeSyntax.map, subst_liftSub_wk, List.map_map, Function.comp_def]
        using ih types.weaken (.var 0, weakenEnvironment environment)
          (rename wk motive) (.app (rename wk constructor) (.var 0))
          (children.map fun pair => (rename wk pair.1, rename wk pair.2)) (liftSub substitution)
  | recursive expression rest ih =>
      simp only [methodBody, subst, TypeSyntax.map, indices.substitute]
      congr 1
      convert ih types.weaken (weakenEnvironment environment)
          (rename wk motive) (.app (rename wk constructor) (.var 0))
          ((children.map fun pair => (rename wk pair.1, rename wk pair.2)) ++
            [(rename wk (indices.term expression environment), .var 0)]) (liftSub substitution) using 1
      simp only [subst, liftSub, Fin.cases_zero, weakenEnvironment_substitute,
          TypeSyntax.weaken, TypeSyntax.map, subst_liftSub_wk, List.map_map, Function.comp_def,
          List.map_append, List.map_cons, List.map_nil, indices.substitute]

theorem methodType_substitute (indices : IndexSyntax I Head)
    (constructor : NamedConstructor I []) {n m : Nat} (types : TypeSyntax I Head n)
    (motive : Tm Head n) (substitution : Sub Head n m) :
    subst substitution (methodType indices constructor types motive) =
      methodType indices constructor (types.map (subst substitution)) (subst substitution motive) := by
  simpa only [methodType, TypeSyntax.map, mapEnv, List.map_nil] using
    methodBody_substitute indices constructor.body types PUnit.unit motive
      (types.constructor constructor.name) [] substitution

theorem motiveType_substitute {n m : Nat} (types : TypeSyntax I Head n)
    (substitution : Sub Head n m) :
    subst substitution (motiveType types) = motiveType (types.map (subst substitution)) := by
  simp [motiveType, TypeSyntax.map, subst, liftSub, subst_liftSub_wk]

theorem methodsType_substitute (indices : IndexSyntax I Head)
    (constructors : List (NamedConstructor I [])) {n m : Nat}
    (types : TypeSyntax I Head n) (motive : Tm Head n) (substitution : Sub Head n m) :
    subst substitution (methodsType indices constructors types motive) =
      methodsType indices constructors (types.map (subst substitution)) (subst substitution motive) := by
  induction constructors generalizing n m with
  | nil =>
      simp only [methodsType, TypeSyntax.map, motiveAt, subst, subst_liftSub_wk]
      rfl
  | cons constructor rest ih =>
      simp only [methodsType, subst, methodType_substitute]
      congr 1
      simpa only [TypeSyntax.weaken_substitute, subst_liftSub_wk] using
        ih types.weaken (rename wk motive) (liftSub substitution)

/-- Substitution of authored parameters commutes with generating the complete
dependent eliminator, including method induction hypotheses. -/
theorem eliminatorType_substitute (indices : IndexSyntax I Head) (admitted : Admitted I [])
    {n m : Nat} (types : TypeSyntax I Head n) (substitution : Sub Head n m) :
    subst substitution (eliminatorType indices admitted types) =
      eliminatorType indices admitted (types.map (subst substitution)) := by
  simp only [eliminatorType, subst, motiveType_substitute, methodsType_substitute,
    TypeSyntax.weaken_substitute, liftSub, Fin.cases_zero]

/-- Contexts grow in source order. The arithmetic cast changes only the
presentation of the number of binders, never a variable position. -/
def castContext {n m : Nat} (equal : n = m) (context : Ctx Head n) : Ctx Head m :=
  equal ▸ context

def fieldsContext (indices : IndexSyntax I Head) :
    {context : List I.SortCode} → (code : Code I context) → {n : Nat} →
      TypeSyntax I Head n → TermEnv I Head n context → Ctx Head n →
      Ctx Head (fieldCount code + n)
  | _, .result _, _, _, _, context => castContext (Nat.zero_add _).symm context
  | _, .data sort body, _, types, environment, context =>
      castContext (by simp only [fieldCount]; omega)
        (fieldsContext indices body types.weaken (.var 0, weakenEnvironment environment)
          (.snoc context (types.dataType sort)))
  | _, .recursive expression rest, _, types, environment, context =>
      castContext (by simp only [fieldCount]; omega)
        (fieldsContext indices rest types.weaken (weakenEnvironment environment)
          (.snoc context (.app types.family (indices.term expression environment))))

def methodsContext (indices : IndexSyntax I Head)
    (constructors : List (NamedConstructor I [])) {n : Nat}
    (types : TypeSyntax I Head n) (motive : Tm Head n) (context : Ctx Head n) :
    Ctx Head (constructors.length + n) :=
  match constructors with
  | [] => castContext (Nat.zero_add _).symm context
  | constructor :: rest =>
      castContext (by simp only [List.length_cons]; omega)
        (methodsContext indices rest types.weaken (rename wk motive)
          (.snoc context (methodType indices constructor types motive)))

/-- Shift the explicit parameters past newly introduced schema binders. -/
def parameterShift (extra : Nat) {n : Nat} : Ren n (extra + n) :=
  fun index => ⟨extra + index.val, Nat.add_lt_add_left index.isLt extra⟩

/-- Motive, all methods, then constructor fields. Existing outer parameters
are retained as the oldest variables. -/
def iotaContext (indices : IndexSyntax I Head) (admitted : Admitted I [])
    (occurrence : Fin admitted.constructors.length) {n : Nat}
    (types : TypeSyntax I Head n) (context : Ctx Head n) :
    Ctx Head (arity admitted occurrence + n) :=
  let base := methodsContext indices admitted.constructors types.weaken (.var 0)
    (.snoc context (motiveType types))
  let shifted := types.map (rename (parameterShift (admitted.constructors.length + 1)))
  castContext (by unfold arity; omega)
    (fieldsContext indices (admitted.constructors.get occurrence).body
      shifted PUnit.unit
      (castContext (by omega) base))

/-- The displayed type of both iota endpoints. The constructor prefix keeps
the original parameters, while fields and motive use the canonical schema
slots already proved correct in the raw computation generator. -/
def iotaType (indices : IndexSyntax I Head) (admitted : Admitted I [])
    (occurrence : Fin admitted.constructors.length) {n : Nat}
    (types : TypeSyntax I Head n) : Tm Head (arity admitted occurrence + n) :=
  let fields := fun field => Tm.var (Head := Head)
    (Fin.castAdd n (fieldSlot admitted occurrence field))
  let constructor := Declaration.IndexedFamily.applyArgs
    (rename (parameterShift (arity admitted occurrence))
      (types.constructor (admitted.constructors.get occurrence).name)) (List.ofFn fields)
  motiveAt (.var (Fin.castAdd n (motiveSlot admitted occurrence)))
    (resultIndex indices (admitted.constructors.get occurrence).body PUnit.unit fields) constructor

def recursorAt {n : Nat} (recursor motive : Tm Head n)
    (methods : List (Tm Head n)) (index value : Tm Head n) : Tm Head n :=
  Declaration.IndexedFamily.applyArgs recursor (motive :: methods ++ [index, value])

/-- Parameterized endpoints use supplied family constructor and recursor
prefixes, preserving the calling convention of the unparameterized generator. -/
def endpoints (indices : IndexSyntax I Head) (admitted : Admitted I [])
    (occurrence : Fin admitted.constructors.length) {n : Nat}
    (types : TypeSyntax I Head n) (recursor motive : Tm Head n)
    (methods : Fin admitted.constructors.length → Tm Head n)
    (arguments : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head n) :
    Tm Head n × Tm Head n :=
  let code := (admitted.constructors.get occurrence).body
  let constructor := Declaration.IndexedFamily.applyArgs
    (types.constructor (admitted.constructors.get occurrence).name) (List.ofFn arguments)
  let left := recursorAt recursor motive (List.ofFn methods)
    (resultIndex indices code PUnit.unit arguments) constructor
  let recursiveResults := (recursiveArguments indices code PUnit.unit arguments).map
    (fun pair => recursorAt recursor motive (List.ofFn methods) pair.1 pair.2)
  (left, Declaration.IndexedFamily.applyArgs (methods occurrence)
    (List.ofFn arguments ++ recursiveResults))

def iotaSchema (indices : IndexSyntax I Head) (admitted : Admitted I [])
    (occurrence : Fin admitted.constructors.length) {n : Nat}
    (types : TypeSyntax I Head n) (recursor : Tm Head n) :
    Tm Head (arity admitted occurrence + n) × Tm Head (arity admitted occurrence + n) :=
  let shift := parameterShift (arity admitted occurrence)
  endpoints indices admitted occurrence (types.map (rename shift)) (rename shift recursor)
    (.var (Fin.castAdd n (motiveSlot admitted occurrence)))
    (fun method => .var (Fin.castAdd n (methodSlot admitted occurrence method)))
    (fun field => .var (Fin.castAdd n (fieldSlot admitted occurrence field)))

theorem recursorAt_substitute {n m : Nat} (substitution : Sub Head n m)
    (recursor motive : Tm Head n) (methods : List (Tm Head n))
    (index value : Tm Head n) :
    subst substitution (recursorAt recursor motive methods index value) =
      recursorAt (subst substitution recursor) (subst substitution motive)
        (methods.map (subst substitution)) (subst substitution index) (subst substitution value) := by
  simp [recursorAt, Declaration.IndexedFamily.subst_applyArgs, subst]

/-- Every parameter, index and child call is transported by the same scoped
substitution; the parameterized ABI does not erase constructor prefixes. -/
theorem endpoints_substitute (indices : IndexSyntax I Head) (admitted : Admitted I [])
    (occurrence : Fin admitted.constructors.length) {n m : Nat}
    (types : TypeSyntax I Head n) (recursor motive : Tm Head n)
    (methods : Fin admitted.constructors.length → Tm Head n)
    (arguments : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head n)
    (substitution : Sub Head n m) :
    (subst substitution (endpoints indices admitted occurrence types recursor motive methods arguments).1,
      subst substitution (endpoints indices admitted occurrence types recursor motive methods arguments).2) =
      endpoints indices admitted occurrence (types.map (subst substitution))
        (subst substitution recursor) (subst substitution motive)
        (fun i => subst substitution (methods i)) (fun i => subst substitution (arguments i)) := by
  have recursive := recursiveArguments_substitute indices substitution
    (admitted.constructors.get occurrence).body PUnit.unit arguments
  have result := resultIndex_substitute indices substitution
    (admitted.constructors.get occurrence).body PUnit.unit arguments
  have mapped := congrArg (List.map (fun pair => recursorAt (subst substitution recursor)
    (subst substitution motive) (List.ofFn (fun i => subst substitution (methods i)))
      pair.1 pair.2)) recursive
  dsimp only [mapEnv] at mapped result
  simp only [endpoints]
  apply Prod.ext
  · dsimp only
    erw [recursorAt_substitute, result]
    simp only [Declaration.IndexedFamily.subst_applyArgs, List.map_ofFn, TypeSyntax.map, Function.comp_def]
  · dsimp only
    erw [Declaration.IndexedFamily.subst_applyArgs]
    simp only [List.map_append, List.map_ofFn]
    apply congrArg (Declaration.IndexedFamily.applyArgs (subst substitution (methods occurrence)))
    apply congrArg (List.append (List.ofFn (fun i => subst substitution (arguments i))))
    simpa only [List.map_map, Function.comp_def, recursorAt_substitute, List.map_ofFn] using mapped

/-- Exact extension of the previous ABI when there are no applied constructor
or recursor parameters. The data-sort interpretations do not enter endpoints. -/
theorem endpoints_constants (indices : IndexSyntax I Head) (admitted : Admitted I [])
    (occurrence : Fin admitted.constructors.length) {n : Nat}
    (types : TypeSyntax I Head n)
    (constructors : ∀ name, types.constructor name = .const (.str .anonymous name))
    (recursor : DeclName) (motive : Tm Head n)
    (methods : Fin admitted.constructors.length → Tm Head n)
    (arguments : Fin (fieldCount (admitted.constructors.get occurrence).body) → Tm Head n) :
    endpoints indices admitted occurrence types (.const recursor) motive methods arguments =
      Guest.endpoints indices admitted recursor occurrence motive methods arguments := by
  simp only [endpoints, Guest.endpoints, constructors, recursorAt, Guest.recursor]

open Declaration.IndexedFamily

def EnvironmentFree (family : DeclName) {n : Nat} :
    {context : List I.SortCode} → TermEnv I Head n context → Prop
  | [], _ => True
  | _ :: _, environment => FreeOf family environment.1 ∧ EnvironmentFree family environment.2

theorem EnvironmentFree.weaken {family : DeclName} {n : Nat}
    {context : List I.SortCode} (environment : TermEnv I Head n context)
    (free : EnvironmentFree family environment) :
    EnvironmentFree family (weakenEnvironment environment) := by
  induction context with
  | nil => trivial
  | cons sort rest ih => exact ⟨free.1.rename wk, ih environment.2 free.2⟩

/-- Index syntax must not smuggle the family being defined into its index.
This condition is checked independently of constructor-type generation. -/
def IndexFree (indices : IndexSyntax I Head) (family : DeclName) : Prop :=
  ∀ {context n} (expression : I.IndexExpr context) (environment : TermEnv I Head n context),
    EnvironmentFree family environment → FreeOf family (indices.term expression environment)

theorem applyArgs_append {n : Nat} (function : Tm Head n) (first second : List (Tm Head n)) :
    applyArgs function (first ++ second) = applyArgs (applyArgs function first) second := by
  induction first generalizing function with
  | nil => rfl
  | cons argument rest ih => exact ih (.app function argument)

theorem indexedFamilyApplication {n : Nat} (family : DeclName)
    (parameters : List (Tm Head n)) (free : ∀ term ∈ parameters, FreeOf family term)
    (index : Tm Head n) (indexFree : FreeOf family index) :
    FamilyApplication family (parameters.length + 1)
      (.app (applyArgs (.const family) parameters) index) := by
  refine .intro (parameters ++ [index]) (by simp) ?_ ?_
  · intro term member
    rcases List.mem_append.mp member with prior | last
    · exact free term prior
    · have equal := List.mem_singleton.mp last
      exact equal ▸ indexFree
  · rw [applyArgs_append]
    rfl

/-- Every source constructor yields the existing strict-positivity witness,
including explicit family parameters. This result follows from the source
telescope; no positivity witness for the generated type is accepted as input. -/
noncomputable def constructorPositive (indices : IndexSyntax I Head)
    (family : DeclName) (indicesFree : IndexFree indices family)
    {context : List I.SortCode} (code : Code I context) {n : Nat}
    (types : TypeSyntax I Head n) (environment : TermEnv I Head n context)
    (parameters : List (Tm Head n))
    (prefix_eq : types.family = applyArgs (.const family) parameters)
    (parametersFree : ∀ term ∈ parameters, FreeOf family term)
    (dataFree : ∀ sort, FreeOf family (types.dataType sort))
    (environmentFree : EnvironmentFree family environment) :
    ConstructorType family (parameters.length + 1) (constructorType indices code types environment) := by
  induction code generalizing n with
  | result expression =>
      apply ConstructorType.result
      rw [constructorType, prefix_eq]
      exact indexedFamilyApplication family parameters parametersFree _
        (indicesFree expression environment environmentFree)
  | data sort body ih =>
      apply ConstructorType.field (.free (dataFree sort))
      have newFree : ∀ term ∈ parameters.map (rename wk), FreeOf family term := by
        intro term member
        obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
        exact (parametersFree source present).rename wk
      have newPrefix : types.weaken.family =
          applyArgs (.const family) (parameters.map (rename wk)) := by
        simpa only [TypeSyntax.weaken, TypeSyntax.map, rename_applyArgs, rename] using
          congrArg (rename wk) prefix_eq
      simpa only [List.length_map] using ih types.weaken
        (.var 0, weakenEnvironment environment) (parameters.map (rename wk)) newPrefix newFree
        (fun sort => (dataFree sort).rename wk)
        ⟨FreeOf.var 0, EnvironmentFree.weaken environment environmentFree⟩
  | recursive expression rest ih =>
      apply ConstructorType.field
        (.recursive (by
          rw [prefix_eq]
          exact indexedFamilyApplication family parameters parametersFree _
            (indicesFree expression environment environmentFree)))
      have newFree : ∀ term ∈ parameters.map (rename wk), FreeOf family term := by
        intro term member
        obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
        exact (parametersFree source present).rename wk
      have newPrefix : types.weaken.family =
          applyArgs (.const family) (parameters.map (rename wk)) := by
        simpa only [TypeSyntax.weaken, TypeSyntax.map, rename_applyArgs, rename] using
          congrArg (rename wk) prefix_eq
      simpa only [List.length_map] using ih types.weaken (weakenEnvironment environment)
        (parameters.map (rename wk)) newPrefix newFree (fun sort => (dataFree sort).rename wk)
        (EnvironmentFree.weaken environment environmentFree)

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Types
