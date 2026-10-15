import Mettapedia.OSLF.NativeTypes.Generation.NativeModalSignature

/-!
# Formation of native event declarations in the authored signature

The formation trees use the complete common native rules. Operational
projections return the same carriers as authored constructor outputs.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeModalSignature

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open NativeSignature SignatureSum

variable (plan : Plan) (installed : Installation plan.snapshot.language)
    (modal : List (NativeModalHeaders.Header plan))

@[simp] theorem formation_cast_before {first second : Judgment (symbols plan installed modal)}
    (equal : first = second) (tree : Derivation (signature plan installed modal) first) (bound : Nat) :
    (cast (congrArg (Derivation (signature plan installed modal)) equal) tree).before bound ↔
      tree.before bound := by
  cases equal
  rfl

@[simp] theorem inputType_rename (index : Fin modal.length) {n m : Nat} (mapping : Renaming n m) :
    (inputType plan installed modal index n).rename mapping = inputType plan installed modal index m := by
  apply congrArg (TypeExpr.family (S := symbols plan installed modal) (.inr (.input index)))
  funext position
  exact Fin.elim0 position

@[simp] theorem inputType_substitute (index : Fin modal.length) {n m : Nat}
    (substitution : Substitution (symbols plan installed modal) n m) :
    (inputType plan installed modal index n).substitute substitution =
      inputType plan installed modal index m := by
  apply congrArg (TypeExpr.family (S := symbols plan installed modal) (.inr (.input index)))
  funext position
  exact Fin.elim0 position

@[simp] theorem authoredType_rename (carrier : Carrier plan.snapshot.language) {n m : Nat}
    (mapping : Renaming n m) :
    (authoredType plan installed modal carrier n).rename mapping =
      authoredType plan installed modal carrier m := by
  rw [authoredType, ← typeLeft_rename, Carrier.native_rename]
  rfl

@[simp] theorem authoredType_substitute (carrier : Carrier plan.snapshot.language) {n m : Nat}
    (substitution : Substitution (symbols plan installed modal) n m) :
    (authoredType plan installed modal carrier n).substitute substitution =
      authoredType plan installed modal carrier m := by
  induction carrier generalizing n m with
  | sort position =>
      apply congrArg (TypeExpr.family (S := symbols plan installed modal) (.inl position))
      funext impossible
      exact Fin.elim0 impossible
  | function domain codomain domainIH codomainIH =>
      exact congrArg₂ TypeExpr.pi (domainIH substitution) (codomainIH (liftSubstitution substitution))

def emptyFormed : Derivation (signature plan installed modal) (.context .nil) :=
  deriveList .contextNil .nil

@[simp] theorem authoredType_sort (position : Fin plan.snapshot.language.types.length) (n : Nat) :
    authoredType plan installed modal (.sort position) n =
      .family (.inl position) Fin.elim0 := by
  apply congrArg (TypeExpr.family (S := symbols plan installed modal) (.inl position))
  funext impossible
  exact Fin.elim0 impossible

def authoredFormed (carrier : Carrier plan.snapshot.language) {n : Nat}
    (context : ContextExpr (symbols plan installed modal) n)
    (formed : Derivation (signature plan installed modal) (.context context)) :
    Derivation (signature plan installed modal) (.type context (authoredType plan installed modal carrier n)) :=
  match carrier with
  | .sort position =>
      cast (congrArg (Derivation (signature plan installed modal))
        (congrArg (Judgment.type context) (authoredType_sort plan installed modal position n).symm))
        (deriveList (.typeFamily context (.inl position) Fin.elim0)
        (.cons formed (.cons (emptyFormed plan installed modal)
          (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil))))
  | .function domain codomain =>
      let domainTree := authoredFormed domain context formed
      let extended := deriveList (.contextExtend context (authoredType plan installed modal domain n))
        (.cons formed (.cons domainTree .nil))
      deriveList (.piFormation context (authoredType plan installed modal domain n)
        (authoredType plan installed modal codomain (n + 1)))
        (.cons domainTree (.cons (authoredFormed codomain _ extended) .nil))

def inputFormed (index : Fin modal.length) {n : Nat} {context : ContextExpr (symbols plan installed modal) n}
    (formed : Derivation (signature plan installed modal) (.context context)) :
    Derivation (signature plan installed modal) (.type context (inputType plan installed modal index n)) :=
  deriveList (.typeFamily context (.inr (.input index)) Fin.elim0)
    (.cons formed (.cons (emptyFormed plan installed modal)
      (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil)))

def inputContextFormed (index : Fin modal.length) :
    Derivation (signature plan installed modal) (.context (inputContext plan installed modal index)) :=
  deriveList (.contextExtend .nil (inputType plan installed modal index 0))
    (.cons (emptyFormed plan installed modal)
      (.cons (inputFormed plan installed modal index (emptyFormed plan installed modal)) .nil))

theorem inputVariableJudgment (index : Fin modal.length) :
    (.term (inputContext plan installed modal index) (.var 0)
      ((inputContext plan installed modal index).lookup 0) : Judgment (symbols plan installed modal)) =
      .term (inputContext plan installed modal index) (.var 0) (inputType plan installed modal index 1) := by
  simp only [inputContext, ContextExpr.lookup_zero, inputType_rename]

def inputVariableFormed (index : Fin modal.length) :
    Derivation (signature plan installed modal)
      (.term (inputContext plan installed modal index) (.var 0)
    (inputType plan installed modal index 1)) :=
  cast (congrArg (Derivation (signature plan installed modal)) (inputVariableJudgment plan installed modal index))
    (deriveList (.variable (inputContext plan installed modal index) 0)
      (.cons (inputContextFormed plan installed modal index) .nil))

def inputArguments (index : Fin modal.length) {n : Nat}
    {context : ContextExpr (symbols plan installed modal) n}
    {value : TermExpr (symbols plan installed modal) n}
    (formed : Derivation (signature plan installed modal) (.context context))
    (typed : Derivation (signature plan installed modal) (.term context value
      (inputType plan installed modal index n))) :
    Derivation (signature plan installed modal)
      (.substitution context (inputContext plan installed modal index)
        (singletonArgument plan installed modal value)) := by
  have valueTree : Derivation (signature plan installed modal)
      (.term context value ((inputType plan installed modal index 0).substitute Fin.elim0)) := by
    exact cast (congrArg (Derivation (signature plan installed modal))
      (congrArg (Judgment.term context value) (inputType_substitute plan installed modal index Fin.elim0).symm)) typed
  exact deriveList (.substitutionExtend context .nil (inputType plan installed modal index 0) Fin.elim0 value)
    (.cons (deriveList (.substitutionNil context) (.cons formed .nil))
      (.cons (inputFormed plan installed modal index (emptyFormed plan installed modal)) (.cons valueTree .nil)))

def eventFormed (index : Fin modal.length) :
    Derivation (signature plan installed modal)
      (.type (inputContext plan installed modal index) (eventType plan installed modal index (.var 0))) :=
  deriveList (.typeFamily (inputContext plan installed modal index) (.inr (.event index))
    (singletonArgument plan installed modal (.var 0)))
    (.cons (inputContextFormed plan installed modal index)
      (.cons (inputContextFormed plan installed modal index)
        (.cons (inputArguments plan installed modal index
          (inputContextFormed plan installed modal index) (inputVariableFormed plan installed modal index)) .nil)))

def eventContextFormed (index : Fin modal.length) :
    Derivation (signature plan installed modal) (.context (eventContext plan installed modal index)) :=
  deriveList (.contextExtend (inputContext plan installed modal index)
      (eventType plan installed modal index (.var 0)))
    (.cons (inputContextFormed plan installed modal index) (.cons (eventFormed plan installed modal index) .nil))

theorem emptyFormed_before (bound : Nat) :
    (emptyFormed plan installed modal).before bound :=
  deriveList_before .contextNil .nil bound True.intro True.intro

theorem authoredFormed_before (carrier : Carrier plan.snapshot.language) {n : Nat}
    (context : ContextExpr (symbols plan installed modal) n)
    (formed : Derivation (signature plan installed modal) (.context context))
    (bound : Nat) (positive : 0 < bound) (contextBefore : formed.before bound) :
    (authoredFormed plan installed modal carrier context formed).before bound := by
  induction carrier generalizing n with
  | sort position =>
      have treeOrder := deriveList_before (.typeFamily context (.inl position) Fin.elim0)
        (.cons formed (.cons (emptyFormed plan installed modal)
          (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil))) bound
        (show (RuleCode.typeFamily (D := signature plan installed modal) context (.inl position)
          Fin.elim0).conclusion.before (signature plan installed modal) bound from
          ⟨formed.before_judgment contextBefore, positive, fun impossible => Fin.elim0 impossible⟩)
        ⟨contextBefore, emptyFormed_before plan installed modal bound,
          deriveList_before _ _ bound
            ⟨formed.before_judgment contextBefore, True.intro, fun impossible => Fin.elim0 impossible⟩
            ⟨contextBefore, True.intro⟩, True.intro⟩
      unfold authoredFormed
      exact (formation_cast_before plan installed modal
        (congrArg (Judgment.type context) (authoredType_sort plan installed modal position n).symm)
        _ bound).mpr treeOrder
  | function domain codomain domainIH codomainIH =>
      have domainBefore := domainIH context formed contextBefore
      have domainSyntax : (authoredType plan installed modal domain n).before
          (signature plan installed modal).typeRank (signature plan installed modal).termRank
          (signature plan installed modal).predicateRank bound := by
        exact (typeLeft_before (ranks installed.signature) (extraRanks plan modal) _ _).mpr
          (domain.native_before n bound positive)
      have extendedBefore :
          (deriveList (.contextExtend context (authoredType plan installed modal domain n))
            (.cons formed (.cons (authoredFormed plan installed modal domain context formed) .nil))).before bound := by
        apply deriveList_before
        · exact ⟨formed.before_judgment contextBefore, domainSyntax⟩
        · exact ⟨contextBefore, domainBefore, True.intro⟩
      apply deriveList_before
      · exact ⟨formed.before_judgment contextBefore,
          (typeLeft_before (ranks installed.signature) (extraRanks plan modal) _ _).mpr
            ((Carrier.function domain codomain).native_before n bound positive)⟩
      · exact ⟨domainBefore, codomainIH _ _ extendedBefore, True.intro⟩

theorem inputFormed_before (index : Fin modal.length) {n : Nat}
    {context : ContextExpr (symbols plan installed modal) n}
    (formed : Derivation (signature plan installed modal) (.context context))
    (bound : Nat) (ordered : formed.before bound) (positive : 1 < bound) :
    (inputFormed plan installed modal index formed).before bound := by
  apply deriveList_before
  · exact ⟨formed.before_judgment ordered, positive, fun impossible => Fin.elim0 impossible⟩
  · exact ⟨ordered, emptyFormed_before plan installed modal bound,
      deriveList_before _ _ bound
        ⟨formed.before_judgment ordered, True.intro, fun impossible => Fin.elim0 impossible⟩
        ⟨ordered, True.intro⟩, True.intro⟩

theorem inputContextFormed_before (index : Fin modal.length) (bound : Nat) (positive : 1 < bound) :
    (inputContextFormed plan installed modal index).before bound :=
  deriveList_before _ _ bound
    ⟨True.intro, positive, fun impossible => Fin.elim0 impossible⟩
    ⟨emptyFormed_before plan installed modal bound,
      inputFormed_before plan installed modal index _ bound
        (emptyFormed_before plan installed modal bound) positive, True.intro⟩

theorem inputVariableFormed_before (index : Fin modal.length) (bound : Nat) (positive : 1 < bound) :
    (inputVariableFormed plan installed modal index).before bound := by
  have treeOrder := deriveList_before (.variable (inputContext plan installed modal index) 0)
    (.cons (inputContextFormed plan installed modal index) .nil) bound
    (show (RuleCode.variable (D := signature plan installed modal)
      (inputContext plan installed modal index) 0).conclusion.before
      (signature plan installed modal) bound from
      ⟨⟨True.intro, positive, fun impossible => Fin.elim0 impossible⟩,
        True.intro, positive, fun impossible => Fin.elim0 impossible⟩)
    ⟨inputContextFormed_before plan installed modal index bound positive, True.intro⟩
  unfold inputVariableFormed
  exact (formation_cast_before plan installed modal (inputVariableJudgment plan installed modal index)
    _ bound).mpr treeOrder

theorem eventFormed_before (index : Fin modal.length) (bound : Nat) (positive : 2 < bound) :
    (eventFormed plan installed modal index).before bound := by
  have inputPositive : 1 < bound := Nat.lt_trans (by decide : 1 < 2) positive
  have inputOrder := inputContextFormed_before plan installed modal index bound inputPositive
  have emptyOrder := emptyFormed_before plan installed modal bound
  have argumentOrder :
      (inputArguments plan installed modal index
        (inputContextFormed plan installed modal index) (inputVariableFormed plan installed modal index)).before bound := by
    unfold inputArguments
    apply deriveList_before
    · exact ⟨⟨True.intro, inputPositive, fun impossible => Fin.elim0 impossible⟩,
        ⟨True.intro, inputPositive, fun impossible => Fin.elim0 impossible⟩,
        fun position => by
          cases position using Fin.cases with
          | zero => trivial
          | succ impossible => exact Fin.elim0 impossible⟩
    · exact ⟨deriveList_before (.substitutionNil (inputContext plan installed modal index)) _ bound
          ⟨⟨True.intro, inputPositive, fun impossible => Fin.elim0 impossible⟩,
            True.intro, fun impossible => Fin.elim0 impossible⟩ ⟨inputOrder, True.intro⟩,
        inputFormed_before plan installed modal index _ bound emptyOrder inputPositive,
        (formation_cast_before plan installed modal
          (congrArg (Judgment.term (inputContext plan installed modal index) (.var 0))
            (inputType_substitute plan installed modal index Fin.elim0).symm) _ bound).mpr
          (inputVariableFormed_before plan installed modal index bound inputPositive),
        True.intro⟩
  apply deriveList_before
  · exact ⟨⟨True.intro, inputPositive, fun impossible => Fin.elim0 impossible⟩,
      positive, fun position => by
        cases position using Fin.cases with
        | zero => trivial
        | succ impossible => exact Fin.elim0 impossible⟩
  · exact ⟨inputOrder, inputOrder, argumentOrder, True.intro⟩

theorem eventContextFormed_before (index : Fin modal.length) (bound : Nat) (positive : 2 < bound) :
    (eventContextFormed plan installed modal index).before bound :=
  deriveList_before _ _ bound
    ⟨⟨True.intro, Nat.lt_trans (by decide : 1 < 2) positive, fun impossible => Fin.elim0 impossible⟩,
      positive, fun position => by
        cases position using Fin.cases with
        | zero => trivial
        | succ impossible => exact Fin.elim0 impossible⟩
    ⟨inputContextFormed_before plan installed modal index bound (Nat.lt_trans (by decide : 1 < 2) positive),
      eventFormed_before plan installed modal index bound positive, True.intro⟩

def headers : HeaderFormation (signature plan installed modal) where
  typeHeader := fun symbol => match symbol with
    | .inl symbol => constructorDerivation plan installed modal (installed.formation.typeHeader symbol)
    | .inr (.input _) => emptyFormed plan installed modal
    | .inr (.event index) => inputContextFormed plan installed modal index
  typeHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol => exact constructorDerivation_before plan installed modal _ _ (installed.formation.typeHeader_before symbol)
    | inr symbol => cases symbol with
        | input => exact emptyFormed_before plan installed modal 1
        | event index => exact inputContextFormed_before plan installed modal index 2 (by decide)
  termHeader := fun symbol => match symbol with
    | .inl symbol => constructorDerivation plan installed modal (installed.formation.termHeader symbol)
    | .inr projection => eventContextFormed plan installed modal projection.index
  termHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol => exact constructorDerivation_before plan installed modal _ _ (installed.formation.termHeader_before symbol)
    | inr symbol => exact eventContextFormed_before plan installed modal _ 3 (by decide)
  termResult := fun symbol => match symbol with
    | .inl symbol => constructorDerivation plan installed modal (installed.formation.termResult symbol)
    | .inr projection => authoredFormed plan installed modal (projectionCarrier plan modal projection)
        _ (eventContextFormed plan installed modal projection.index)
  termResult_before := by
    intro symbol
    cases symbol with
    | inl symbol => exact constructorDerivation_before plan installed modal _ _ (installed.formation.termResult_before symbol)
    | inr symbol => exact authoredFormed_before plan installed modal _ _ _ 3 (by decide) (eventContextFormed_before plan installed modal _ 3 (by decide))
  predicateHeader := fun symbol => match symbol with
    | .inl symbol => nomatch symbol
    | .inr symbol => nomatch symbol
  predicateHeader_before := fun symbol => match symbol with
    | .inl symbol => nomatch symbol
    | .inr symbol => nomatch symbol

end Mettapedia.OSLF.NativeTypes.Generation.NativeModalSignature
