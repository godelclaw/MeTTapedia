import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureRecoveryEquations

/-!
# Finite-stage reconstruction of universal equations

Product and function beta/eta retain every complete annotation and body.
Equalizer equations reconstruct their actual parallel arrows and candidate;
the uniqueness case decodes the recovered equalizer target and retains its
whole supplied commutativity equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory
open RelativeClosedSyntax Iteration

universe k
variable {C : Type k} [Category.{k} C] (initial : Stage C) (depth : Nat)

def EquationRecovery.firstBeta {source left right : ObjectCode C (symbols initial)}
    {first second : ArrowCode C (symbols initial)}
    (leftFormed : ObjectRecovery initial depth left) (rightFormed : ObjectRecovery initial depth right)
    (before : ArrowRecovery initial depth source left first)
    (after : ArrowRecovery initial depth source right second) :
    EquationRecovery initial depth source left (.compose (.pair first second) (.first left right)) first := by
  rcases leftFormed with ⟨localLeft, leftTree, leftRead⟩
  rcases rightFormed with ⟨localRight, rightTree, rightRead⟩
  rcases before with ⟨beforeSource, beforeTarget, beforeCode, beforeTyped, beforeSourceRead, beforeTargetRead, beforeRead⟩
  rcases after with ⟨afterSource, afterTarget, afterCode, afterTyped, afterSourceRead, afterTargetRead, afterRead⟩
  have sourceSame := object_align initial afterSourceRead beforeSourceRead
  have leftSame := object_align initial beforeTargetRead leftRead
  have rightSame := object_align initial afterTargetRead rightRead
  subst afterSource beforeTarget afterTarget
  exact ⟨beforeSource, localLeft, .compose (.pair beforeCode afterCode) (.first localLeft localRight), beforeCode,
    .firstBeta leftTree rightTree beforeTyped afterTyped, beforeSourceRead, leftRead,
    congrArg₂ ArrowCode.compose (congrArg₂ ArrowCode.pair beforeRead afterRead)
      (congrArg₂ ArrowCode.first leftRead rightRead), beforeRead⟩

def EquationRecovery.secondBeta {source left right : ObjectCode C (symbols initial)}
    {first second : ArrowCode C (symbols initial)}
    (leftFormed : ObjectRecovery initial depth left) (rightFormed : ObjectRecovery initial depth right)
    (before : ArrowRecovery initial depth source left first)
    (after : ArrowRecovery initial depth source right second) :
    EquationRecovery initial depth source right (.compose (.pair first second) (.second left right)) second := by
  rcases leftFormed with ⟨localLeft, leftTree, leftRead⟩
  rcases rightFormed with ⟨localRight, rightTree, rightRead⟩
  rcases before with ⟨beforeSource, beforeTarget, beforeCode, beforeTyped, beforeSourceRead, beforeTargetRead, beforeRead⟩
  rcases after with ⟨afterSource, afterTarget, afterCode, afterTyped, afterSourceRead, afterTargetRead, afterRead⟩
  have sourceSame := object_align initial afterSourceRead beforeSourceRead
  have leftSame := object_align initial beforeTargetRead leftRead
  have rightSame := object_align initial afterTargetRead rightRead
  subst afterSource beforeTarget afterTarget
  exact ⟨beforeSource, localRight, .compose (.pair beforeCode afterCode) (.second localLeft localRight), afterCode,
    .secondBeta leftTree rightTree beforeTyped afterTyped, beforeSourceRead, rightRead,
    congrArg₂ ArrowCode.compose (congrArg₂ ArrowCode.pair beforeRead afterRead)
      (congrArg₂ ArrowCode.second leftRead rightRead), afterRead⟩

def EquationRecovery.productEta {source left right : ObjectCode C (symbols initial)}
    {arrow : ArrowCode C (symbols initial)}
    (leftFormed : ObjectRecovery initial depth left) (rightFormed : ObjectRecovery initial depth right)
    (typed : ArrowRecovery initial depth source (.product left right) arrow) :
    EquationRecovery initial depth source (.product left right)
      (.pair (.compose arrow (.first left right)) (.compose arrow (.second left right))) arrow := by
  rcases leftFormed with ⟨localLeft, leftTree, leftRead⟩
  rcases rightFormed with ⟨localRight, rightTree, rightRead⟩
  rcases typed with ⟨localSource, arrowTarget, arrowCode', arrowTyped, sourceRead, arrowTargetRead, arrowRead⟩
  have targetSame := object_align initial (second := .product localLeft localRight)
    arrowTargetRead (congrArg₂ ObjectCode.product leftRead rightRead)
  subst arrowTarget
  exact ⟨localSource, .product localLeft localRight,
    .pair (.compose arrowCode' (.first localLeft localRight)) (.compose arrowCode' (.second localLeft localRight)), arrowCode',
    .productEta leftTree rightTree arrowTyped, sourceRead, congrArg₂ ObjectCode.product leftRead rightRead,
    congrArg₂ ArrowCode.pair (congrArg₂ ArrowCode.compose arrowRead (congrArg₂ ArrowCode.first leftRead rightRead))
      (congrArg₂ ArrowCode.compose arrowRead (congrArg₂ ArrowCode.second leftRead rightRead)), arrowRead⟩

def EquationRecovery.exponentialBeta {context argument result : ObjectCode C (symbols initial)}
    {body : ArrowCode C (symbols initial)}
    (environment : ObjectRecovery initial depth context)
    (domain : ObjectRecovery initial depth argument) (codomain : ObjectRecovery initial depth result)
    (typed : ArrowRecovery initial depth (.product context argument) result body) :
    EquationRecovery initial depth (.product context argument) result
      (.compose (.pair (.compose (.first context argument) (.curry context argument result body))
        (.second context argument)) (.evaluation argument result)) body := by
  rcases environment with ⟨localContext, contextTree, contextRead⟩
  rcases domain with ⟨localArgument, argumentTree, argumentRead⟩
  rcases codomain with ⟨localResult, resultTree, resultRead⟩
  rcases typed with ⟨bodySource, bodyTarget, bodyCode, bodyTyped, bodySourceRead, bodyTargetRead, bodyRead⟩
  have sourceSame := object_align initial (second := .product localContext localArgument)
    bodySourceRead (congrArg₂ ObjectCode.product contextRead argumentRead)
  have targetSame := object_align initial bodyTargetRead resultRead
  subst bodySource bodyTarget
  have curryRead : arrowCode initial depth (.curry localContext localArgument localResult bodyCode) =
      .curry context argument result body := by
    change ArrowCode.curry (objectCode initial depth localContext) (objectCode initial depth localArgument)
      (objectCode initial depth localResult) (arrowCode initial depth bodyCode) = _
    rw [contextRead, argumentRead, resultRead, bodyRead]
  exact ⟨.product localContext localArgument, localResult,
    .compose (.pair (.compose (.first localContext localArgument)
      (.curry localContext localArgument localResult bodyCode)) (.second localContext localArgument))
      (.evaluation localArgument localResult), bodyCode,
    .exponentialBeta contextTree argumentTree resultTree bodyTyped,
    congrArg₂ ObjectCode.product contextRead argumentRead, resultRead,
    congrArg₂ ArrowCode.compose
      (congrArg₂ ArrowCode.pair
        (congrArg₂ ArrowCode.compose (congrArg₂ ArrowCode.first contextRead argumentRead) curryRead)
        (congrArg₂ ArrowCode.second contextRead argumentRead))
      (congrArg₂ ArrowCode.evaluation argumentRead resultRead), bodyRead⟩

def EquationRecovery.exponentialEta {context argument result : ObjectCode C (symbols initial)}
    {arrow : ArrowCode C (symbols initial)}
    (environment : ObjectRecovery initial depth context)
    (domain : ObjectRecovery initial depth argument) (codomain : ObjectRecovery initial depth result)
    (typed : ArrowRecovery initial depth context (.exponential argument result) arrow) :
    EquationRecovery initial depth context (.exponential argument result)
      (.curry context argument result
        (.compose (.pair (.compose (.first context argument) arrow) (.second context argument))
          (.evaluation argument result))) arrow := by
  rcases environment with ⟨localContext, contextTree, contextRead⟩
  rcases domain with ⟨localArgument, argumentTree, argumentRead⟩
  rcases codomain with ⟨localResult, resultTree, resultRead⟩
  rcases typed with ⟨arrowSource, arrowTarget, localArrow, arrowTyped, arrowSourceRead, arrowTargetRead, arrowRead⟩
  have sourceSame := object_align initial arrowSourceRead contextRead
  have targetSame := object_align initial (second := .exponential localArgument localResult)
    arrowTargetRead (congrArg₂ ObjectCode.exponential argumentRead resultRead)
  subst arrowSource arrowTarget
  refine ⟨localContext, .exponential localArgument localResult,
    .curry localContext localArgument localResult
      (.compose (.pair (.compose (.first localContext localArgument) localArrow) (.second localContext localArgument))
        (.evaluation localArgument localResult)), localArrow,
    .exponentialEta contextTree argumentTree resultTree arrowTyped,
    contextRead, congrArg₂ ObjectCode.exponential argumentRead resultRead, ?_, arrowRead⟩
  change ArrowCode.curry (objectCode initial depth localContext) (objectCode initial depth localArgument)
    (objectCode initial depth localResult)
    (.compose (.pair (.compose (.first (objectCode initial depth localContext)
      (objectCode initial depth localArgument)) (arrowCode initial depth localArrow))
        (.second (objectCode initial depth localContext) (objectCode initial depth localArgument)))
      (.evaluation (objectCode initial depth localArgument) (objectCode initial depth localResult))) = _
  rw [contextRead, argumentRead, resultRead, arrowRead]

def EquationRecovery.equalizerCondition {source target : ObjectCode C (symbols initial)}
    {first second : ArrowCode C (symbols initial)}
    (domain : ObjectRecovery initial depth source) (codomain : ObjectRecovery initial depth target)
    (before : ArrowRecovery initial depth source target first)
    (after : ArrowRecovery initial depth source target second) :
    EquationRecovery initial depth (.equalizer source target first second) target
      (.compose (.equalizerArrow source target first second) first)
      (.compose (.equalizerArrow source target first second) second) := by
  rcases domain with ⟨localSource, sourceTree, sourceRead⟩
  rcases codomain with ⟨localTarget, targetTree, targetRead⟩
  rcases before with ⟨beforeSource, beforeTarget, beforeCode, beforeTyped, beforeSourceRead, beforeTargetRead, beforeRead⟩
  rcases after with ⟨afterSource, afterTarget, afterCode, afterTyped, afterSourceRead, afterTargetRead, afterRead⟩
  have sourceBefore := object_align initial beforeSourceRead sourceRead
  have targetBefore := object_align initial beforeTargetRead targetRead
  have sourceAfter := object_align initial afterSourceRead sourceRead
  have targetAfter := object_align initial afterTargetRead targetRead
  subst beforeSource beforeTarget afterSource afterTarget
  have inclusionRead : arrowCode initial depth (.equalizerArrow localSource localTarget beforeCode afterCode) =
      .equalizerArrow source target first second := by
    change ArrowCode.equalizerArrow (objectCode initial depth localSource) (objectCode initial depth localTarget)
      (arrowCode initial depth beforeCode) (arrowCode initial depth afterCode) = _
    rw [sourceRead, targetRead, beforeRead, afterRead]
  refine ⟨.equalizer localSource localTarget beforeCode afterCode, localTarget,
    .compose (.equalizerArrow localSource localTarget beforeCode afterCode) beforeCode,
    .compose (.equalizerArrow localSource localTarget beforeCode afterCode) afterCode,
    .equalizerCondition sourceTree targetTree beforeTyped afterTyped, ?_, targetRead,
    congrArg₂ ArrowCode.compose inclusionRead beforeRead, congrArg₂ ArrowCode.compose inclusionRead afterRead⟩
  change ObjectCode.equalizer (objectCode initial depth localSource) (objectCode initial depth localTarget)
    (arrowCode initial depth beforeCode) (arrowCode initial depth afterCode) = _
  rw [sourceRead, targetRead, beforeRead, afterRead]

def EquationRecovery.equalizerBeta {source target context : ObjectCode C (symbols initial)}
    {first second candidate : ArrowCode C (symbols initial)}
    (domain : ObjectRecovery initial depth source) (codomain : ObjectRecovery initial depth target)
    (environment : ObjectRecovery initial depth context)
    (before : ArrowRecovery initial depth source target first)
    (after : ArrowRecovery initial depth source target second)
    (supplied : ArrowRecovery initial depth context source candidate)
    (commutes : EquationRecovery initial depth context target (.compose candidate first) (.compose candidate second)) :
    EquationRecovery initial depth context source
      (.compose (.equalizerLift source target first second context candidate)
        (.equalizerArrow source target first second)) candidate := by
  rcases domain with ⟨localSource, sourceTree, sourceRead⟩
  rcases codomain with ⟨localTarget, targetTree, targetRead⟩
  rcases environment with ⟨localContext, contextTree, contextRead⟩
  rcases before with ⟨beforeSource, beforeTarget, beforeCode, beforeTyped, beforeSourceRead, beforeTargetRead, beforeRead⟩
  rcases after with ⟨afterSource, afterTarget, afterCode, afterTyped, afterSourceRead, afterTargetRead, afterRead⟩
  rcases supplied with ⟨candidateSource, candidateTarget, candidateCode, candidateTyped,
    candidateSourceRead, candidateTargetRead, candidateRead⟩
  rcases commutes with ⟨equationSource, equationTarget, equationFirst, equationSecond, equationTyped,
    equationSourceRead, equationTargetRead, equationFirstRead, equationSecondRead⟩
  have sourceBefore := object_align initial beforeSourceRead sourceRead
  have targetBefore := object_align initial beforeTargetRead targetRead
  have sourceAfter := object_align initial afterSourceRead sourceRead
  have targetAfter := object_align initial afterTargetRead targetRead
  have sourceCandidate := object_align initial candidateSourceRead contextRead
  have targetCandidate := object_align initial candidateTargetRead sourceRead
  have sourceEquation := object_align initial equationSourceRead contextRead
  have targetEquation := object_align initial equationTargetRead targetRead
  have firstEquation := arrow_align initial (second := .compose candidateCode beforeCode)
    equationFirstRead (congrArg₂ ArrowCode.compose candidateRead beforeRead)
  have secondEquation := arrow_align initial (second := .compose candidateCode afterCode)
    equationSecondRead (congrArg₂ ArrowCode.compose candidateRead afterRead)
  subst beforeSource beforeTarget afterSource afterTarget candidateSource candidateTarget
    equationSource equationTarget equationFirst equationSecond
  have liftRead : arrowCode initial depth
      (.equalizerLift localSource localTarget beforeCode afterCode localContext candidateCode) =
      .equalizerLift source target first second context candidate := by
    change ArrowCode.equalizerLift (objectCode initial depth localSource) (objectCode initial depth localTarget)
      (arrowCode initial depth beforeCode) (arrowCode initial depth afterCode)
      (objectCode initial depth localContext) (arrowCode initial depth candidateCode) = _
    rw [sourceRead, targetRead, beforeRead, afterRead, contextRead, candidateRead]
  have inclusionRead : arrowCode initial depth (.equalizerArrow localSource localTarget beforeCode afterCode) =
      .equalizerArrow source target first second := by
    change ArrowCode.equalizerArrow (objectCode initial depth localSource) (objectCode initial depth localTarget)
      (arrowCode initial depth beforeCode) (arrowCode initial depth afterCode) = _
    rw [sourceRead, targetRead, beforeRead, afterRead]
  exact ⟨localContext, localSource,
    .compose (.equalizerLift localSource localTarget beforeCode afterCode localContext candidateCode)
      (.equalizerArrow localSource localTarget beforeCode afterCode), candidateCode,
    .equalizerBeta sourceTree targetTree contextTree beforeTyped afterTyped candidateTyped equationTyped,
    contextRead, sourceRead, congrArg₂ ArrowCode.compose liftRead inclusionRead, candidateRead⟩

structure EqualizerParts (code : ObjectCode C (stages initial depth).symbols)
    (wholeSource wholeTarget : ObjectCode C (symbols initial))
    (wholeFirst wholeSecond : ArrowCode C (symbols initial)) where
  source : ObjectCode C (stages initial depth).symbols
  target : ObjectCode C (stages initial depth).symbols
  first : ArrowCode C (stages initial depth).symbols
  second : ArrowCode C (stages initial depth).symbols
  shape : code = .equalizer source target first second
  source_read : objectCode initial depth source = wholeSource
  target_read : objectCode initial depth target = wholeTarget
  first_read : arrowCode initial depth first = wholeFirst
  second_read : arrowCode initial depth second = wholeSecond

def equalizerParts {code : ObjectCode C (stages initial depth).symbols}
    {source target : ObjectCode C (symbols initial)} {first second : ArrowCode C (symbols initial)}
    (read : objectCode initial depth code = .equalizer source target first second) :
    EqualizerParts initial depth code source target first second := by
  cases code <;> simp only [objectCode, ObjectCode.map, ObjectCode.equalizer.injEq, reduceCtorEq] at read
  rename_i localSource localTarget localFirst localSecond
  exact ⟨localSource, localTarget, localFirst, localSecond, rfl, read.1, read.2.1, read.2.2.1, read.2.2.2⟩

def EquationRecovery.equalizerUniqueness {source target context : ObjectCode C (symbols initial)}
    {first second before after : ArrowCode C (symbols initial)}
    (left : ArrowRecovery initial depth context (.equalizer source target first second) before)
    (right : ArrowRecovery initial depth context (.equalizer source target first second) after)
    (same : EquationRecovery initial depth context source
      (.compose before (.equalizerArrow source target first second))
      (.compose after (.equalizerArrow source target first second))) :
    EquationRecovery initial depth context (.equalizer source target first second) before after := by
  rcases left with ⟨beforeSource, beforeTarget, beforeCode, beforeTyped, beforeSourceRead, beforeTargetRead, beforeRead⟩
  rcases right with ⟨afterSource, afterTarget, afterCode, afterTyped, afterSourceRead, afterTargetRead, afterRead⟩
  rcases same with ⟨equationSource, equationTarget, equationFirst, equationSecond, equationTyped,
    equationSourceRead, equationTargetRead, equationFirstRead, equationSecondRead⟩
  rcases equalizerParts initial depth beforeTargetRead with
    ⟨localSource, localTarget, localFirst, localSecond, targetShape, sourceRead, targetRead, firstRead, secondRead⟩
  have sourceAfter := object_align initial afterSourceRead beforeSourceRead
  have targetAfter := object_align initial afterTargetRead beforeTargetRead
  have sourceEquation := object_align initial equationSourceRead beforeSourceRead
  have targetEquation := object_align initial equationTargetRead sourceRead
  have inclusionRead : arrowCode initial depth (.equalizerArrow localSource localTarget localFirst localSecond) =
      .equalizerArrow source target first second := by
    change ArrowCode.equalizerArrow (objectCode initial depth localSource) (objectCode initial depth localTarget)
      (arrowCode initial depth localFirst) (arrowCode initial depth localSecond) = _
    rw [sourceRead, targetRead, firstRead, secondRead]
  have firstEquation := arrow_align initial
    (second := .compose beforeCode (.equalizerArrow localSource localTarget localFirst localSecond))
    equationFirstRead (congrArg₂ ArrowCode.compose beforeRead inclusionRead)
  have secondEquation := arrow_align initial
    (second := .compose afterCode (.equalizerArrow localSource localTarget localFirst localSecond))
    equationSecondRead (congrArg₂ ArrowCode.compose afterRead inclusionRead)
  subst afterSource afterTarget equationSource equationTarget equationFirst equationSecond beforeTarget
  exact ⟨beforeSource, .equalizer localSource localTarget localFirst localSecond, beforeCode, afterCode,
    .equalizerUniqueness beforeTyped afterTyped equationTyped,
    beforeSourceRead, beforeTargetRead, beforeRead, afterRead⟩

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure
