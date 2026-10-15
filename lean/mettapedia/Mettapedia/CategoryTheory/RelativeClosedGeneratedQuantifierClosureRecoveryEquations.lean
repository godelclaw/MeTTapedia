import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureRecoveryFormation

/-!
# Finite-stage reconstruction of structural equations

Shared endpoints and intermediate arrows are aligned by whole-code equality
reflection. A declared equation is recovered at its actual stage of birth;
both independently supplied admission trees are retained in that local rule.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory
open RelativeClosedSyntax Iteration

universe k
variable {C : Type k} [Category.{k} C] (initial : Stage C) (depth : Nat)

def EquationRecovery.reflexivity {source target : ObjectCode C (symbols initial)}
    {arrow : ArrowCode C (symbols initial)} (typed : ArrowRecovery initial depth source target arrow) :
    EquationRecovery initial depth source target arrow arrow :=
  ⟨typed.source, typed.target, typed.code, typed.code, .reflexivity typed.admitted,
    typed.source_read, typed.target_read, typed.read, typed.read⟩

def EquationRecovery.symmetry {source target : ObjectCode C (symbols initial)}
    {first second : ArrowCode C (symbols initial)}
    (same : EquationRecovery initial depth source target first second) :
    EquationRecovery initial depth source target second first :=
  ⟨same.source, same.target, same.second, same.first, .symmetry same.admitted,
    same.source_read, same.target_read, same.second_read, same.first_read⟩

def EquationRecovery.transitivity {source target : ObjectCode C (symbols initial)}
    {first middle last : ArrowCode C (symbols initial)}
    (before : EquationRecovery initial depth source target first middle)
    (after : EquationRecovery initial depth source target middle last) :
    EquationRecovery initial depth source target first last := by
  rcases before with ⟨beforeSource, beforeTarget, firstCode, beforeMiddle, beforeSame,
    beforeSourceRead, beforeTargetRead, firstRead, beforeMiddleRead⟩
  rcases after with ⟨afterSource, afterTarget, afterMiddle, lastCode, afterSame,
    afterSourceRead, afterTargetRead, afterMiddleRead, lastRead⟩
  have sourceSame := object_align initial afterSourceRead beforeSourceRead
  have targetSame := object_align initial afterTargetRead beforeTargetRead
  have middleSame := arrow_align initial afterMiddleRead beforeMiddleRead
  subst afterSource afterTarget afterMiddle
  exact ⟨beforeSource, beforeTarget, firstCode, lastCode, .transitivity beforeSame afterSame,
    beforeSourceRead, beforeTargetRead, firstRead, lastRead⟩

def EquationRecovery.compositionCongruence {source middle target : ObjectCode C (symbols initial)}
    {before before' after after' : ArrowCode C (symbols initial)}
    (first : EquationRecovery initial depth source middle before before')
    (second : EquationRecovery initial depth middle target after after') :
    EquationRecovery initial depth source target (.compose before after) (.compose before' after') := by
  rcases first with ⟨localSource, beforeMiddle, beforeCode, beforeCode', beforeSame,
    sourceRead, beforeMiddleRead, beforeRead, beforeRead'⟩
  rcases second with ⟨afterMiddle, localTarget, afterCode, afterCode', afterSame,
    afterMiddleRead, targetRead, afterRead, afterRead'⟩
  have middleSame := object_align initial afterMiddleRead beforeMiddleRead
  subst afterMiddle
  exact ⟨localSource, localTarget, .compose beforeCode afterCode, .compose beforeCode' afterCode',
    .compositionCongruence beforeSame afterSame, sourceRead, targetRead,
    congrArg₂ ArrowCode.compose beforeRead afterRead, congrArg₂ ArrowCode.compose beforeRead' afterRead'⟩

def EquationRecovery.pairCongruence {source left right : ObjectCode C (symbols initial)}
    {first first' second second' : ArrowCode C (symbols initial)}
    (before : EquationRecovery initial depth source left first first')
    (after : EquationRecovery initial depth source right second second') :
    EquationRecovery initial depth source (.product left right) (.pair first second) (.pair first' second') := by
  rcases before with ⟨beforeSource, localLeft, beforeCode, beforeCode', beforeSame,
    beforeSourceRead, leftRead, beforeRead, beforeRead'⟩
  rcases after with ⟨afterSource, localRight, afterCode, afterCode', afterSame,
    afterSourceRead, rightRead, afterRead, afterRead'⟩
  have sourceSame := object_align initial afterSourceRead beforeSourceRead
  subst afterSource
  exact ⟨beforeSource, .product localLeft localRight, .pair beforeCode afterCode, .pair beforeCode' afterCode',
    .pairCongruence beforeSame afterSame, beforeSourceRead, congrArg₂ ObjectCode.product leftRead rightRead,
    congrArg₂ ArrowCode.pair beforeRead afterRead, congrArg₂ ArrowCode.pair beforeRead' afterRead'⟩

def EquationRecovery.curryCongruence {context argument result : ObjectCode C (symbols initial)}
    {first second : ArrowCode C (symbols initial)}
    (environment : ObjectRecovery initial depth context)
    (domain : ObjectRecovery initial depth argument) (codomain : ObjectRecovery initial depth result)
    (same : EquationRecovery initial depth (.product context argument) result first second) :
    EquationRecovery initial depth context (.exponential argument result)
      (.curry context argument result first) (.curry context argument result second) := by
  rcases environment with ⟨localContext, contextFormed, contextRead⟩
  rcases domain with ⟨localArgument, argumentFormed, argumentRead⟩
  rcases codomain with ⟨localResult, resultFormed, resultRead⟩
  rcases same with ⟨bodySource, bodyTarget, beforeCode, afterCode, bodySame,
    bodySourceRead, bodyTargetRead, beforeRead, afterRead⟩
  have sourceSame := object_align initial (second := .product localContext localArgument)
    bodySourceRead (congrArg₂ ObjectCode.product contextRead argumentRead)
  have targetSame := object_align initial bodyTargetRead resultRead
  subst bodySource bodyTarget
  refine ⟨localContext, .exponential localArgument localResult,
    .curry localContext localArgument localResult beforeCode, .curry localContext localArgument localResult afterCode,
    .curryCongruence contextFormed argumentFormed resultFormed bodySame,
    contextRead, congrArg₂ ObjectCode.exponential argumentRead resultRead, ?_, ?_⟩
  · change ArrowCode.curry (objectCode initial depth localContext) (objectCode initial depth localArgument)
      (objectCode initial depth localResult) (arrowCode initial depth beforeCode) = _
    rw [contextRead, argumentRead, resultRead, beforeRead]
  · change ArrowCode.curry (objectCode initial depth localContext) (objectCode initial depth localArgument)
      (objectCode initial depth localResult) (arrowCode initial depth afterCode) = _
    rw [contextRead, argumentRead, resultRead, afterRead]

def EquationRecovery.leftIdentity {source target : ObjectCode C (symbols initial)}
    {arrow : ArrowCode C (symbols initial)}
    (formed : ObjectRecovery initial depth source) (typed : ArrowRecovery initial depth source target arrow) :
    EquationRecovery initial depth source target (.compose (.identity source) arrow) arrow := by
  rcases formed with ⟨localSource, sourceFormed, sourceRead⟩
  rcases typed with ⟨beforeSource, localTarget, beforeCode, beforeTyped, beforeSourceRead, targetRead, beforeRead⟩
  have sourceSame := object_align initial beforeSourceRead sourceRead
  subst beforeSource
  exact ⟨localSource, localTarget, .compose (.identity localSource) beforeCode, beforeCode,
    .leftIdentity sourceFormed beforeTyped, sourceRead, targetRead,
    congrArg₂ ArrowCode.compose (congrArg ArrowCode.identity sourceRead) beforeRead, beforeRead⟩

def EquationRecovery.rightIdentity {source target : ObjectCode C (symbols initial)}
    {arrow : ArrowCode C (symbols initial)}
    (formed : ObjectRecovery initial depth target) (typed : ArrowRecovery initial depth source target arrow) :
    EquationRecovery initial depth source target (.compose arrow (.identity target)) arrow := by
  rcases formed with ⟨localTarget, targetFormed, targetRead⟩
  rcases typed with ⟨localSource, beforeTarget, beforeCode, beforeTyped, sourceRead, beforeTargetRead, beforeRead⟩
  have targetSame := object_align initial beforeTargetRead targetRead
  subst beforeTarget
  exact ⟨localSource, localTarget, .compose beforeCode (.identity localTarget), beforeCode,
    .rightIdentity targetFormed beforeTyped, sourceRead, targetRead,
    congrArg₂ ArrowCode.compose beforeRead (congrArg ArrowCode.identity targetRead), beforeRead⟩

def EquationRecovery.associativity {first second third fourth : ObjectCode C (symbols initial)}
    {before middle after : ArrowCode C (symbols initial)}
    (left : ArrowRecovery initial depth first second before)
    (center : ArrowRecovery initial depth second third middle)
    (right : ArrowRecovery initial depth third fourth after) :
    EquationRecovery initial depth first fourth (.compose (.compose before middle) after)
      (.compose before (.compose middle after)) := by
  rcases left with ⟨localFirst, beforeSecond, beforeCode, beforeTyped, firstRead, beforeSecondRead, beforeRead⟩
  rcases center with ⟨middleSecond, middleThird, middleCode, middleTyped, middleSecondRead, middleThirdRead, middleRead⟩
  rcases right with ⟨afterThird, localFourth, afterCode, afterTyped, afterThirdRead, fourthRead, afterRead⟩
  have secondSame := object_align initial middleSecondRead beforeSecondRead
  have thirdSame := object_align initial afterThirdRead middleThirdRead
  subst middleSecond afterThird
  exact ⟨localFirst, localFourth, .compose (.compose beforeCode middleCode) afterCode,
    .compose beforeCode (.compose middleCode afterCode), .associativity beforeTyped middleTyped afterTyped,
    firstRead, fourthRead, congrArg₂ ArrowCode.compose (congrArg₂ ArrowCode.compose beforeRead middleRead) afterRead,
    congrArg₂ ArrowCode.compose beforeRead (congrArg₂ ArrowCode.compose middleRead afterRead)⟩

def EquationRecovery.terminalUniqueness {source : ObjectCode C (symbols initial)}
    {first second : ArrowCode C (symbols initial)}
    (before : ArrowRecovery initial depth source .terminal first)
    (after : ArrowRecovery initial depth source .terminal second) :
    EquationRecovery initial depth source .terminal first second := by
  rcases before with ⟨beforeSource, beforeTarget, beforeCode, beforeTyped, beforeSourceRead, beforeTargetRead, beforeRead⟩
  rcases after with ⟨afterSource, afterTarget, afterCode, afterTyped, afterSourceRead, afterTargetRead, afterRead⟩
  have sourceSame := object_align initial afterSourceRead beforeSourceRead
  have firstTerminal := terminal_shape initial beforeTargetRead
  have secondTerminal := terminal_shape initial afterTargetRead
  subst afterSource beforeTarget afterTarget
  exact ⟨beforeSource, .terminal, beforeCode, afterCode, .terminalUniqueness beforeTyped afterTyped,
    beforeSourceRead, rfl, beforeRead, afterRead⟩

def EquationRecovery.baseIdentity (object : C) :
    EquationRecovery initial depth (.base object) (.base object) (.base (𝟙 object)) (.identity (.base object)) :=
  ⟨.base object, .base object, .base (𝟙 object), .identity (.base object), .baseIdentity object,
    rfl, rfl, rfl, rfl⟩

def EquationRecovery.baseComposition {first middle last : C} (before : first ⟶ middle) (after : middle ⟶ last) :
    EquationRecovery initial depth (.base first) (.base last) (.base (before ≫ after)) (.compose (.base before) (.base after)) :=
  ⟨.base first, .base last, .base (before ≫ after), .compose (.base before) (.base after),
    .baseComposition before after, rfl, rfl, rfl, rfl⟩

def EquationRecovery.baseEquality {source target : C} {first second : source ⟶ target} (same : first = second) :
    EquationRecovery initial depth (.base source) (.base target) (.base first) (.base second) :=
  ⟨.base source, .base target, .base first, .base second, .baseEquality same, rfl, rfl, rfl, rfl⟩

def EquationRecovery.declaredEquation (origin : (symbols initial).EquationName)
    (born : equationBirth initial origin ≤ depth)
    (before : ArrowRecovery initial depth ((signature initial).equationSource origin)
      ((signature initial).equationTarget origin) ((signature initial).left origin))
    (after : ArrowRecovery initial depth ((signature initial).equationSource origin)
      ((signature initial).equationTarget origin) ((signature initial).right origin)) :
    EquationRecovery initial depth ((signature initial).equationSource origin)
      ((signature initial).equationTarget origin) ((signature initial).left origin) ((signature initial).right origin) := by
  classical
  let occurrence := (equations_preimage initial depth origin).mpr born
  let previous := Classical.choose occurrence
  have previousRead := Classical.choose_spec occurrence
  rcases before with ⟨beforeSource, beforeTarget, beforeCode, beforeTyped,
    beforeSourceRead, beforeTargetRead, beforeRead⟩
  rcases after with ⟨afterSource, afterTarget, afterCode, afterTyped,
    afterSourceRead, afterTargetRead, afterRead⟩
  have sourceBefore := object_align initial beforeSourceRead (equationSource_preimage initial previousRead)
  have targetBefore := object_align initial beforeTargetRead (equationTarget_preimage initial previousRead)
  have sourceAfter := object_align initial afterSourceRead (equationSource_preimage initial previousRead)
  have targetAfter := object_align initial afterTargetRead (equationTarget_preimage initial previousRead)
  have firstSame := arrow_align initial beforeRead (left_preimage initial previousRead)
  have secondSame := arrow_align initial afterRead (right_preimage initial previousRead)
  subst beforeSource beforeTarget afterSource afterTarget beforeCode afterCode
  exact ⟨_, _, _, _, .declaredEquation previous beforeTyped afterTyped,
    beforeSourceRead, beforeTargetRead, beforeRead, afterRead⟩

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure
