import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureCodeEmbedding

/-!
# Complete finite-stage proof recovery data

The bound follows every actual formation and equation premise, including the
commutativity proof of an equalizer lift and declarations used only inside
equation proofs. Recovery retains raw object and arrow codes, their actual
finite-stage derivation and the complete comparison to the merged language.
It does not identify raw contexts or assume that equation extensions are
faithful.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory
open RelativeClosedSyntax Iteration

universe k
variable {C : Type k} [Category.{k} C] (initial : Stage C)

def proofBound : {judgment : Judgment C (symbols initial)} →
    Derivation (signature initial) judgment → Nat
  | _, .baseObject _ => 0
  | _, .objectName _ => 0
  | _, .terminalObject => 0
  | _, .productObject first second => proofBound first + proofBound second
  | _, .exponentialObject argument result => proofBound argument + proofBound result
  | _, .equalizerObject source target first second =>
      proofBound source + proofBound target + proofBound first + proofBound second
  | _, .baseArrow _ => 0
  | _, .arrowName origin source target =>
      arrowBirth initial origin + proofBound source + proofBound target
  | _, .identity formed => proofBound formed
  | _, .compose first second => proofBound first + proofBound second
  | _, .terminalArrow formed => proofBound formed
  | _, .first left right => proofBound left + proofBound right
  | _, .second left right => proofBound left + proofBound right
  | _, .pair first second => proofBound first + proofBound second
  | _, .evaluation argument result => proofBound argument + proofBound result
  | _, .curry context argument result body =>
      proofBound context + proofBound argument + proofBound result + proofBound body
  | _, .equalizerArrow source target first second =>
      proofBound source + proofBound target + proofBound first + proofBound second
  | _, .equalizerLift source target context first second candidate commutes =>
      proofBound source + proofBound target + proofBound context + proofBound first +
        proofBound second + proofBound candidate + proofBound commutes
  | _, .reflexivity typed => proofBound typed
  | _, .symmetry same => proofBound same
  | _, .transitivity before after => proofBound before + proofBound after
  | _, .compositionCongruence before after => proofBound before + proofBound after
  | _, .pairCongruence first second => proofBound first + proofBound second
  | _, .curryCongruence context argument result same =>
      proofBound context + proofBound argument + proofBound result + proofBound same
  | _, .leftIdentity source typed => proofBound source + proofBound typed
  | _, .rightIdentity target typed => proofBound target + proofBound typed
  | _, .associativity before middle after => proofBound before + proofBound middle + proofBound after
  | _, .terminalUniqueness first second => proofBound first + proofBound second
  | _, .firstBeta left right first second =>
      proofBound left + proofBound right + proofBound first + proofBound second
  | _, .secondBeta left right first second =>
      proofBound left + proofBound right + proofBound first + proofBound second
  | _, .productEta left right typed => proofBound left + proofBound right + proofBound typed
  | _, .exponentialBeta context argument result body =>
      proofBound context + proofBound argument + proofBound result + proofBound body
  | _, .exponentialEta context argument result typed =>
      proofBound context + proofBound argument + proofBound result + proofBound typed
  | _, .equalizerCondition source target first second =>
      proofBound source + proofBound target + proofBound first + proofBound second
  | _, .equalizerBeta source target context first second candidate commutes =>
      proofBound source + proofBound target + proofBound context + proofBound first +
        proofBound second + proofBound candidate + proofBound commutes
  | _, .equalizerUniqueness before after same => proofBound before + proofBound after + proofBound same
  | _, .baseIdentity _ => 0
  | _, .baseComposition _ _ => 0
  | _, .baseEquality _ => 0
  | _, .declaredEquation origin left right =>
      equationBirth initial origin + proofBound left + proofBound right

structure ObjectRecovery (depth : Nat) (whole : ObjectCode C (symbols initial)) where
  code : ObjectCode C (stages initial depth).symbols
  formed : Derivation (stages initial depth).presentation (.object code)
  read : objectCode initial depth code = whole

structure ArrowRecovery (depth : Nat) (wholeSource wholeTarget : ObjectCode C (symbols initial))
    (whole : ArrowCode C (symbols initial)) where
  source : ObjectCode C (stages initial depth).symbols
  target : ObjectCode C (stages initial depth).symbols
  code : ArrowCode C (stages initial depth).symbols
  admitted : Derivation (stages initial depth).presentation (.arrow source target code)
  source_read : objectCode initial depth source = wholeSource
  target_read : objectCode initial depth target = wholeTarget
  read : arrowCode initial depth code = whole

structure EquationRecovery (depth : Nat) (wholeSource wholeTarget : ObjectCode C (symbols initial))
    (wholeFirst wholeSecond : ArrowCode C (symbols initial)) where
  source : ObjectCode C (stages initial depth).symbols
  target : ObjectCode C (stages initial depth).symbols
  first : ArrowCode C (stages initial depth).symbols
  second : ArrowCode C (stages initial depth).symbols
  admitted : Derivation (stages initial depth).presentation (.equation source target first second)
  source_read : objectCode initial depth source = wholeSource
  target_read : objectCode initial depth target = wholeTarget
  first_read : arrowCode initial depth first = wholeFirst
  second_read : arrowCode initial depth second = wholeSecond

def Recovery (depth : Nat) : Judgment C (symbols initial) → Type k
  | .object object => ObjectRecovery initial depth object
  | .arrow source target arrow => ArrowRecovery initial depth source target arrow
  | .equation source target first second => EquationRecovery initial depth source target first second

theorem object_align {depth : Nat} {first second : ObjectCode C (stages initial depth).symbols}
    {whole : ObjectCode C (symbols initial)}
    (firstRead : objectCode initial depth first = whole)
    (secondRead : objectCode initial depth second = whole) : first = second :=
  objectCode_injective initial depth (firstRead.trans secondRead.symm)

theorem arrow_align {depth : Nat} {first second : ArrowCode C (stages initial depth).symbols}
    {whole : ArrowCode C (symbols initial)}
    (firstRead : arrowCode initial depth first = whole)
    (secondRead : arrowCode initial depth second = whole) : first = second :=
  arrowCode_injective initial depth (firstRead.trans secondRead.symm)

theorem terminal_shape {depth : Nat} {code : ObjectCode C (stages initial depth).symbols}
    (read : objectCode initial depth code = .terminal) : code = .terminal :=
  objectCode_injective initial depth read

theorem equalizer_shape {depth : Nat} {code : ObjectCode C (stages initial depth).symbols}
    {source target : ObjectCode C (symbols initial)} {first second : ArrowCode C (symbols initial)}
    (read : objectCode initial depth code = .equalizer source target first second) :
    ∃ localSource localTarget localFirst localSecond,
      code = .equalizer localSource localTarget localFirst localSecond ∧
      objectCode initial depth localSource = source ∧
      objectCode initial depth localTarget = target ∧
      arrowCode initial depth localFirst = first ∧
      arrowCode initial depth localSecond = second := by
  cases code <;> simp only [objectCode, ObjectCode.map, ObjectCode.equalizer.injEq, reduceCtorEq] at read
  rename_i localSource localTarget localFirst localSecond
  exact ⟨localSource, localTarget, localFirst, localSecond, rfl, read⟩

theorem source_preimage {depth : Nat} {origin : (symbols initial).ArrowName}
    {previous : (stages initial depth).symbols.ArrowName}
    (read : arrows initial depth previous = origin) :
    objectCode initial depth ((stages initial depth).presentation.source previous) =
      (signature initial).source origin :=
  (source_read initial depth previous).symm.trans (congrArg (signature initial).source read)

theorem target_preimage {depth : Nat} {origin : (symbols initial).ArrowName}
    {previous : (stages initial depth).symbols.ArrowName}
    (read : arrows initial depth previous = origin) :
    objectCode initial depth ((stages initial depth).presentation.target previous) =
      (signature initial).target origin :=
  (target_read initial depth previous).symm.trans (congrArg (signature initial).target read)

theorem equationSource_preimage {depth : Nat} {origin : (symbols initial).EquationName}
    {previous : (stages initial depth).symbols.EquationName}
    (read : equations initial depth previous = origin) :
    objectCode initial depth ((stages initial depth).presentation.equationSource previous) =
      (signature initial).equationSource origin :=
  (equationSource_read initial depth previous).symm.trans
    (congrArg (signature initial).equationSource read)

theorem equationTarget_preimage {depth : Nat} {origin : (symbols initial).EquationName}
    {previous : (stages initial depth).symbols.EquationName}
    (read : equations initial depth previous = origin) :
    objectCode initial depth ((stages initial depth).presentation.equationTarget previous) =
      (signature initial).equationTarget origin :=
  (equationTarget_read initial depth previous).symm.trans
    (congrArg (signature initial).equationTarget read)

theorem left_preimage {depth : Nat} {origin : (symbols initial).EquationName}
    {previous : (stages initial depth).symbols.EquationName}
    (read : equations initial depth previous = origin) :
    arrowCode initial depth ((stages initial depth).presentation.left previous) =
      (signature initial).left origin :=
  (left_read initial depth previous).symm.trans (congrArg (signature initial).left read)

theorem right_preimage {depth : Nat} {origin : (symbols initial).EquationName}
    {previous : (stages initial depth).symbols.EquationName}
    (read : equations initial depth previous = origin) :
    arrowCode initial depth ((stages initial depth).presentation.right previous) =
      (signature initial).right origin :=
  (right_read initial depth previous).symm.trans (congrArg (signature initial).right read)

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure
