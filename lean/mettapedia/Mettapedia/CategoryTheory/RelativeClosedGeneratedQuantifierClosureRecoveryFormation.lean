import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureRecoveryData

/-!
# Finite-stage reconstruction of formation rules

Every reconstructed rule uses actual finite-stage premises. Complete code
reflection aligns shared annotations, while the primitive case recovers the
independently authored name and its exact source and target declarations.
Equalizer lifts retain the supplied commutativity derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory
open RelativeClosedSyntax Iteration

universe k
variable {C : Type k} [Category.{k} C] (initial : Stage C) (depth : Nat)

def ObjectRecovery.base (object : C) : ObjectRecovery initial depth (.base object) :=
  ⟨.base object, .baseObject object, rfl⟩

def ObjectRecovery.name (origin : (symbols initial).ObjectName) :
    ObjectRecovery initial depth (.name origin) :=
  ⟨.name (initialObject initial depth origin), .objectName _,
    congrArg ObjectCode.name (initialObject_read initial depth origin)⟩

def ObjectRecovery.terminal : ObjectRecovery initial depth .terminal :=
  ⟨.terminal, .terminalObject, rfl⟩

def ObjectRecovery.product {first second : ObjectCode C (symbols initial)}
    (left : ObjectRecovery initial depth first) (right : ObjectRecovery initial depth second) :
    ObjectRecovery initial depth (.product first second) :=
  ⟨.product left.code right.code, .productObject left.formed right.formed,
    congrArg₂ ObjectCode.product left.read right.read⟩

def ObjectRecovery.exponential {argument result : ObjectCode C (symbols initial)}
    (domain : ObjectRecovery initial depth argument) (codomain : ObjectRecovery initial depth result) :
    ObjectRecovery initial depth (.exponential argument result) :=
  ⟨.exponential domain.code codomain.code, .exponentialObject domain.formed codomain.formed,
    congrArg₂ ObjectCode.exponential domain.read codomain.read⟩

def ObjectRecovery.equalizer {source target : ObjectCode C (symbols initial)}
    {first second : ArrowCode C (symbols initial)}
    (domain : ObjectRecovery initial depth source) (codomain : ObjectRecovery initial depth target)
    (before : ArrowRecovery initial depth source target first)
    (after : ArrowRecovery initial depth source target second) :
    ObjectRecovery initial depth (.equalizer source target first second) := by
  rcases domain with ⟨localSource, sourceFormed, sourceRead⟩
  rcases codomain with ⟨localTarget, targetFormed, targetRead⟩
  rcases before with ⟨beforeSource, beforeTarget, beforeCode, beforeTyped, beforeSourceRead, beforeTargetRead, beforeRead⟩
  rcases after with ⟨afterSource, afterTarget, afterCode, afterTyped, afterSourceRead, afterTargetRead, afterRead⟩
  have sourceBefore := object_align initial beforeSourceRead sourceRead
  have targetBefore := object_align initial beforeTargetRead targetRead
  have sourceAfter := object_align initial afterSourceRead sourceRead
  have targetAfter := object_align initial afterTargetRead targetRead
  subst beforeSource beforeTarget afterSource afterTarget
  refine ⟨.equalizer localSource localTarget beforeCode afterCode,
    .equalizerObject sourceFormed targetFormed beforeTyped afterTyped, ?_⟩
  change ObjectCode.equalizer (objectCode initial depth localSource) (objectCode initial depth localTarget)
    (arrowCode initial depth beforeCode) (arrowCode initial depth afterCode) = _
  rw [sourceRead, targetRead, beforeRead, afterRead]

def ArrowRecovery.base {source target : C} (arrow : source ⟶ target) :
    ArrowRecovery initial depth (.base source) (.base target) (.base arrow) :=
  ⟨.base source, .base target, .base arrow, .baseArrow arrow, rfl, rfl, rfl⟩

def ArrowRecovery.name (origin : (symbols initial).ArrowName)
    (born : arrowBirth initial origin ≤ depth)
    (domain : ObjectRecovery initial depth ((signature initial).source origin))
    (codomain : ObjectRecovery initial depth ((signature initial).target origin)) :
    ArrowRecovery initial depth ((signature initial).source origin)
      ((signature initial).target origin) (.name origin) := by
  classical
  let occurrence := (arrows_preimage initial depth origin).mpr born
  let previous := Classical.choose occurrence
  have previousRead := Classical.choose_spec occurrence
  rcases domain with ⟨localSource, sourceFormed, sourceRead⟩
  rcases codomain with ⟨localTarget, targetFormed, targetRead⟩
  have sourceSame := object_align initial sourceRead (source_preimage initial previousRead)
  have targetSame := object_align initial targetRead (target_preimage initial previousRead)
  subst localSource localTarget
  exact ⟨_, _, .name previous, .arrowName previous sourceFormed targetFormed,
    sourceRead, targetRead, congrArg ArrowCode.name previousRead⟩

def ArrowRecovery.identity {object : ObjectCode C (symbols initial)}
    (formed : ObjectRecovery initial depth object) :
    ArrowRecovery initial depth object object (.identity object) :=
  ⟨formed.code, formed.code, .identity formed.code, .identity formed.formed,
    formed.read, formed.read, congrArg ArrowCode.identity formed.read⟩

def ArrowRecovery.compose {first middle last : ObjectCode C (symbols initial)}
    {before after : ArrowCode C (symbols initial)}
    (left : ArrowRecovery initial depth first middle before)
    (right : ArrowRecovery initial depth middle last after) :
    ArrowRecovery initial depth first last (.compose before after) := by
  rcases left with ⟨localFirst, beforeMiddle, beforeCode, beforeTyped, firstRead, beforeMiddleRead, beforeRead⟩
  rcases right with ⟨afterMiddle, localLast, afterCode, afterTyped, afterMiddleRead, lastRead, afterRead⟩
  have middleSame := object_align initial afterMiddleRead beforeMiddleRead
  subst afterMiddle
  exact ⟨localFirst, localLast, .compose beforeCode afterCode, .compose beforeTyped afterTyped,
    firstRead, lastRead, congrArg₂ ArrowCode.compose beforeRead afterRead⟩

def ArrowRecovery.terminal {source : ObjectCode C (symbols initial)}
    (formed : ObjectRecovery initial depth source) :
    ArrowRecovery initial depth source .terminal (.terminal source) :=
  ⟨formed.code, .terminal, .terminal formed.code, .terminalArrow formed.formed,
    formed.read, rfl, congrArg ArrowCode.terminal formed.read⟩

def ArrowRecovery.first {left right : ObjectCode C (symbols initial)}
    (before : ObjectRecovery initial depth left) (after : ObjectRecovery initial depth right) :
    ArrowRecovery initial depth (.product left right) left (.first left right) :=
  ⟨.product before.code after.code, before.code, .first before.code after.code,
    .first before.formed after.formed, congrArg₂ ObjectCode.product before.read after.read,
    before.read, congrArg₂ ArrowCode.first before.read after.read⟩

def ArrowRecovery.second {left right : ObjectCode C (symbols initial)}
    (before : ObjectRecovery initial depth left) (after : ObjectRecovery initial depth right) :
    ArrowRecovery initial depth (.product left right) right (.second left right) :=
  ⟨.product before.code after.code, after.code, .second before.code after.code,
    .second before.formed after.formed, congrArg₂ ObjectCode.product before.read after.read,
    after.read, congrArg₂ ArrowCode.second before.read after.read⟩

def ArrowRecovery.pair {source left right : ObjectCode C (symbols initial)}
    {first second : ArrowCode C (symbols initial)}
    (before : ArrowRecovery initial depth source left first)
    (after : ArrowRecovery initial depth source right second) :
    ArrowRecovery initial depth source (.product left right) (.pair first second) := by
  rcases before with ⟨beforeSource, localLeft, beforeCode, beforeTyped, beforeSourceRead, leftRead, beforeRead⟩
  rcases after with ⟨afterSource, localRight, afterCode, afterTyped, afterSourceRead, rightRead, afterRead⟩
  have sourceSame := object_align initial afterSourceRead beforeSourceRead
  subst afterSource
  exact ⟨beforeSource, .product localLeft localRight, .pair beforeCode afterCode,
    .pair beforeTyped afterTyped, beforeSourceRead, congrArg₂ ObjectCode.product leftRead rightRead,
    congrArg₂ ArrowCode.pair beforeRead afterRead⟩

def ArrowRecovery.evaluation {argument result : ObjectCode C (symbols initial)}
    (domain : ObjectRecovery initial depth argument) (codomain : ObjectRecovery initial depth result) :
    ArrowRecovery initial depth (.product (.exponential argument result) argument) result
      (.evaluation argument result) :=
  ⟨.product (.exponential domain.code codomain.code) domain.code, codomain.code,
    .evaluation domain.code codomain.code, .evaluation domain.formed codomain.formed,
    congrArg₂ ObjectCode.product (congrArg₂ ObjectCode.exponential domain.read codomain.read) domain.read,
    codomain.read, congrArg₂ ArrowCode.evaluation domain.read codomain.read⟩

def ArrowRecovery.curry {context argument result : ObjectCode C (symbols initial)}
    {body : ArrowCode C (symbols initial)}
    (environment : ObjectRecovery initial depth context)
    (domain : ObjectRecovery initial depth argument) (codomain : ObjectRecovery initial depth result)
    (typed : ArrowRecovery initial depth (.product context argument) result body) :
    ArrowRecovery initial depth context (.exponential argument result) (.curry context argument result body) := by
  rcases environment with ⟨localContext, contextFormed, contextRead⟩
  rcases domain with ⟨localArgument, argumentFormed, argumentRead⟩
  rcases codomain with ⟨localResult, resultFormed, resultRead⟩
  rcases typed with ⟨bodySource, bodyTarget, bodyCode, bodyTyped, bodySourceRead, bodyTargetRead, bodyRead⟩
  have sourceSame := object_align initial (second := .product localContext localArgument)
    bodySourceRead (congrArg₂ ObjectCode.product contextRead argumentRead)
  have targetSame := object_align initial bodyTargetRead resultRead
  subst bodySource bodyTarget
  refine ⟨localContext, .exponential localArgument localResult,
    .curry localContext localArgument localResult bodyCode,
    .curry contextFormed argumentFormed resultFormed bodyTyped, contextRead,
    congrArg₂ ObjectCode.exponential argumentRead resultRead, ?_⟩
  change ArrowCode.curry (objectCode initial depth localContext) (objectCode initial depth localArgument)
    (objectCode initial depth localResult) (arrowCode initial depth bodyCode) = _
  rw [contextRead, argumentRead, resultRead, bodyRead]

def ArrowRecovery.equalizerArrow {source target : ObjectCode C (symbols initial)}
    {first second : ArrowCode C (symbols initial)}
    (domain : ObjectRecovery initial depth source) (codomain : ObjectRecovery initial depth target)
    (before : ArrowRecovery initial depth source target first)
    (after : ArrowRecovery initial depth source target second) :
    ArrowRecovery initial depth (.equalizer source target first second) source
      (.equalizerArrow source target first second) := by
  rcases domain with ⟨localSource, sourceFormed, sourceRead⟩
  rcases codomain with ⟨localTarget, targetFormed, targetRead⟩
  rcases before with ⟨beforeSource, beforeTarget, beforeCode, beforeTyped, beforeSourceRead, beforeTargetRead, beforeRead⟩
  rcases after with ⟨afterSource, afterTarget, afterCode, afterTyped, afterSourceRead, afterTargetRead, afterRead⟩
  have sourceBefore := object_align initial beforeSourceRead sourceRead
  have targetBefore := object_align initial beforeTargetRead targetRead
  have sourceAfter := object_align initial afterSourceRead sourceRead
  have targetAfter := object_align initial afterTargetRead targetRead
  subst beforeSource beforeTarget afterSource afterTarget
  refine ⟨.equalizer localSource localTarget beforeCode afterCode, localSource,
    .equalizerArrow localSource localTarget beforeCode afterCode,
    .equalizerArrow sourceFormed targetFormed beforeTyped afterTyped, ?_, sourceRead, ?_⟩
  · change ObjectCode.equalizer (objectCode initial depth localSource) (objectCode initial depth localTarget)
      (arrowCode initial depth beforeCode) (arrowCode initial depth afterCode) = _
    rw [sourceRead, targetRead, beforeRead, afterRead]
  · change ArrowCode.equalizerArrow (objectCode initial depth localSource) (objectCode initial depth localTarget)
      (arrowCode initial depth beforeCode) (arrowCode initial depth afterCode) = _
    rw [sourceRead, targetRead, beforeRead, afterRead]

def ArrowRecovery.equalizerLift {source target context : ObjectCode C (symbols initial)}
    {first second candidate : ArrowCode C (symbols initial)}
    (domain : ObjectRecovery initial depth source) (codomain : ObjectRecovery initial depth target)
    (environment : ObjectRecovery initial depth context)
    (before : ArrowRecovery initial depth source target first)
    (after : ArrowRecovery initial depth source target second)
    (supplied : ArrowRecovery initial depth context source candidate)
    (commutes : EquationRecovery initial depth context target (.compose candidate first) (.compose candidate second)) :
    ArrowRecovery initial depth context (.equalizer source target first second)
      (.equalizerLift source target first second context candidate) := by
  rcases domain with ⟨localSource, sourceFormed, sourceRead⟩
  rcases codomain with ⟨localTarget, targetFormed, targetRead⟩
  rcases environment with ⟨localContext, contextFormed, contextRead⟩
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
  have firstEquation := arrow_align initial (second := .compose candidateCode beforeCode) equationFirstRead
    (congrArg₂ ArrowCode.compose candidateRead beforeRead)
  have secondEquation := arrow_align initial (second := .compose candidateCode afterCode) equationSecondRead
    (congrArg₂ ArrowCode.compose candidateRead afterRead)
  subst beforeSource beforeTarget afterSource afterTarget candidateSource candidateTarget
    equationSource equationTarget equationFirst equationSecond
  refine ⟨localContext, .equalizer localSource localTarget beforeCode afterCode,
    .equalizerLift localSource localTarget beforeCode afterCode localContext candidateCode,
    .equalizerLift sourceFormed targetFormed contextFormed beforeTyped afterTyped candidateTyped equationTyped,
    contextRead, ?_, ?_⟩
  · change ObjectCode.equalizer (objectCode initial depth localSource) (objectCode initial depth localTarget)
      (arrowCode initial depth beforeCode) (arrowCode initial depth afterCode) = _
    rw [sourceRead, targetRead, beforeRead, afterRead]
  · change ArrowCode.equalizerLift (objectCode initial depth localSource) (objectCode initial depth localTarget)
      (arrowCode initial depth beforeCode) (arrowCode initial depth afterCode)
      (objectCode initial depth localContext) (arrowCode initial depth candidateCode) = _
    rw [sourceRead, targetRead, beforeRead, afterRead, contextRead, candidateRead]

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure
