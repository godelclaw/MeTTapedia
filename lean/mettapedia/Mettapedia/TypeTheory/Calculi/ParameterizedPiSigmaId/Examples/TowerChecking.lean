import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveCheckingOSLF

/-!
# Positive and negative controls for common cumulative evidence checking

The fixtures exercise the actual dependent rule premises, explicit conversion,
shared references, context formation and the old structural replay handoff.
No model assumptions are required to execute these controls.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tower.Checking
namespace Controls

open FormationSensitiveRuleSignature FormationSensitiveChecking
open Mettapedia.Logic

abbrev u0 : Tower.Head := .sort (.const 0)
abbrev u1 : Tower.Head := .sort (.succ (.const 0))
abbrev upper : Tower.Head := .sort (.max (.succ (.const 0)) (.succ (.const 0)))
abbrev ground {n : Nat} : Tower.Tm n := .head .legacyGround
abbrev sortTerm {n : Nat} : Tower.Tm n := .head u0
abbrev identity {n : Nat} : Tower.Tm n := .lam (.var 0)
abbrev functionType {n : Nat} : Tower.Tm n := .pi sortTerm sortTerm
abbrev pairType {n : Nat} : Tower.Tm n := .sigma sortTerm sortTerm
abbrev identityType {n : Nat} : Tower.Tm n := .id sortTerm ground ground
abbrev beta {n : Nat} : Tower.Tm n := .app identity ground

abbrev Node := DerivationGraph.Node (Judgment Tower.Head) interface.W Unit

def row (claim : Judgment Tower.Head) (code : FormationSensitiveChecking.Code decoder.Code claim)
    (parents : List Nat := []) : Node := ⟨claim, ⟨claim, code⟩, parents, ()⟩

def rows : List Node := [
  row (judgment .nil ground sortTerm) .headType,
  row (judgment .nil sortTerm (.head u1)) .headType,
  row (judgment (.snoc .nil sortTerm) sortTerm (.head u1)) .headType,
  row (judgment .nil functionType (.head upper)) (.piForm (u := u1) (v := u1)) [1, 2],
  row (judgment (.snoc .nil sortTerm) (.var 0) sortTerm) (.var 0),
  row (judgment .nil identity functionType) (.lamIntro (u := upper)) [3, 4],
  row (judgment .nil beta sortTerm) (.appElim (A := sortTerm) (B := sortTerm)) [5, 0],
  row (judgment .nil pairType (.head upper)) (.sigmaForm (u := u1) (v := u1)) [1, 2],
  row (judgment .nil (.pair ground ground) pairType) (.pairIntro (u := upper)) [7, 0, 0],
  row (judgment .nil (.fst (.pair ground ground)) sortTerm) (.fstElim (B := sortTerm)) [8],
  row (judgment .nil (.snd (.pair ground ground)) sortTerm)
    (.sndElim (A := sortTerm) (B := sortTerm)) [8],
  row (judgment .nil identityType (.head u1)) .idForm [1, 0, 0],
  row (judgment .nil (.refl ground) identityType) .reflIntro [0],
  row (judgment .nil ground (.head u1)) (.cumul (u := u0)) [0],
  row (judgment .nil (.head (.sort (.max (.const 0) (.const 0))))
    (.head (.sort (.succ (.max (.const 0) (.const 0)))))) .headType,
  row (judgment .nil ground (.head (.sort (.max (.const 0) (.const 0)))))
    (.convert (A := sortTerm) (u := .sort (.succ (.max (.const 0) (.const 0))))
      (.single (.head u0 (.sort (.max (.const 0) (.const 0)))))) [0, 14],
  row (judgment .nil (.pi sortTerm (.var 0))
    (.head (.sort (.max (.succ (.const 0)) (.const 0)))))
    (.piForm (u := u1) (v := u0)) [1, 4]]

def request (root : Nat) (term type : Tower.Tm 0) : Request (judgment .nil term type) :=
  ⟨.nil, rows, root⟩

def betaCode : StructuralConversionCode.Code Tower.Head decoder.Code 0 :=
  .single (.betaPi (.var 0) ground)

def oldBeta : StructuralTypingReplay.Code Tower.Head
    (StructuralConversionCode.Code Tower.Head decoder.Code) 0 :=
  .appElim sortTerm sortTerm
    (.lamIntro upper (.piForm u1 u1 .headType .headType) .var) .headType

abbrev rawBeta {n : Nat} : Tower.Tm n := .app identity (.app ground ground)

def rawBetaCode : StructuralConversionCode.Code Tower.Head decoder.Code 0 :=
  .single (.betaPi (.var 0) (.app ground ground))

/-- The declared observation is conversion evidence, so a reverse beta edge
is valid without asserting that reverse beta is evaluator execution. -/
theorem reverse_beta_oslf :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (FormationSensitiveCheckingOSLF.theory Tower.rules 0)).satisfies (S := ()) ground
      (FormationSensitiveCheckingOSLF.conversionNativeType Tower.rules beta).pred := by
  apply (FormationSensitiveCheckingOSLF.satisfies_iff_conversion Tower.rules ground beta).mpr
  exact .symm _ _ (StructuralConversionCode.Code.check_sound decoder (by decide :
    betaCode.check Tower.rules.headEq decoder.decode beta ground = true))

/-- Raw beta reachability does not carry a formed typing premise. -/
theorem raw_beta_oslf :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (FormationSensitiveCheckingOSLF.theory Tower.rules 0)).satisfies (S := ()) rawBeta
      (FormationSensitiveCheckingOSLF.conversionNativeType Tower.rules (.app ground ground)).pred := by
  apply (FormationSensitiveCheckingOSLF.satisfies_iff_conversion Tower.rules rawBeta
    (.app ground ground)).mpr
  exact .rel _ _ (.betaPi (.var 0) (.app ground ground))

abbrev dependentContext : Tower.Ctx 2 := .snoc (.snoc .nil sortTerm) (.var 0)

def dependentContextCode : FormationSensitiveChecking.ContextCode decoder dependentContext :=
  .snoc (.snoc .nil u1 .headType) u0 .var

def dependentRows : List Node :=
  [row (judgment dependentContext (.var 0) (.var 1)) (.var 0)]

def dependentRequest : Request (judgment dependentContext (.var 0) (.var 1)) :=
  ⟨dependentContextCode, dependentRows, 0⟩

def forgedContextRequest : Request (judgment dependentContext (.var 0) (.var 1)) :=
  { dependentRequest with context := .snoc (.snoc .nil u1 .headType) u0 .headType }

abbrev badContext : Tower.Ctx 1 := .snoc .nil (.app ground ground)

def badContextRows : List Node :=
  [row (judgment badContext (.var 0) (.app ground ground)) (.var 0)]

def badContextRequest : Request (judgment badContext (.var 0) (.app ground ground)) :=
  ⟨.snoc .nil u0 .headType, badContextRows, 0⟩

def verdicts : List (String × Bool) := [
  ("DTT conversion observation accepts reverse beta code",
    (StructuralConversionCode.Code.symm betaCode).check Tower.rules.headEq decoder.decode ground beta),
  ("DTT raw beta code retains the untyped argument",
    rawBetaCode.check Tower.rules.headEq decoder.decode rawBeta (.app ground ground)),
  ("DTT raw beta code does not authorize typed request", !(check (request 6 rawBeta sortTerm))),
  ("DTT sortTerm leaf", check (request 1 sortTerm (.head u1))),
  ("DTT dependent Pi formation", check (request 3 functionType (.head upper))),
  ("DTT lambda formation", check (request 5 identity functionType)),
  ("DTT beta application", check (request 6 beta sortTerm)),
  ("DTT dependent Sigma formation", check (request 7 pairType (.head upper))),
  ("DTT pair shared premise", check (request 8 (.pair ground ground) pairType)),
  ("DTT first projection", check (request 9 (.fst (.pair ground ground)) sortTerm)),
  ("DTT dependent second projection", check (request 10 (.snd (.pair ground ground)) sortTerm)),
  ("DTT identity formation", check (request 11 identityType (.head u1))),
  ("DTT identity reflexivity", check (request 12 (.refl ground) identityType)),
  ("DTT semantic cumulativity", check (request 13 ground (.head u1))),
  ("DTT original replay mints", (mintReplay decoder (judgment .nil beta sortTerm) oldBeta).isSome),
  ("DTT wrong original replay refuses", (mintReplay decoder (judgment .nil beta ground) oldBeta).isNone),
  ("DTT nonliteral level conversion", check (request 15 ground
      (.head (.sort (.max (.const 0) (.const 0)))))),
  ("DTT dependent empty-type formation", check (request 16 (.pi sortTerm (.var 0))
      (.head (.sort (.max (.succ (.const 0)) (.const 0)))))),
  ("DTT formed dependent telescope", check dependentRequest),
  ("DTT forged telescope formation", !(check forgedContextRequest)),
  ("DTT raw variable does not imply formed context",
      (DerivationGraph.CheckedJudgment.mint interface badContextRows 0).isSome),
  ("DTT unformed request refuses", !(check badContextRequest)),
  ("DTT explicit beta conversion", betaCode.check Tower.rules.headEq decoder.decode beta ground),
  ("DTT forged beta endpoint", !(betaCode.check Tower.rules.headEq decoder.decode beta sortTerm)),
  ("DTT missing root", !(check (request 99 beta sortTerm))),
  ("DTT changed root claim", !(check (request 0 ground ground))),
  ("DTT unadmitted constant", (DerivationGraph.replay interface
    [row (judgment .nil (.const `missing) sortTerm) (.const (type := sortTerm) (u := u1)) [0]]).isNone),
  ("DTT cyclic graph", (DerivationGraph.replay interface
    [row (judgment .nil beta sortTerm) (.appElim (A := sortTerm) (B := sortTerm)) [0, 0]]).isNone),
  ("DTT unused invalid suffix", !(check { request 6 beta sortTerm with
    nodes := rows ++ [row (judgment .nil sortTerm sortTerm) .headType] })),
  ("DTT rejected sortTerm lowering", !(interface.isInstance
    ⟨judgment .nil ground sortTerm, .cumul (u := u1)⟩
    [judgment .nil ground (.head u1)] (judgment .nil ground sortTerm))),
  ("DTT invalid join", !(interface.isInstance
    ⟨judgment .nil functionType (.head u0), .piForm (u := u1) (v := u1)⟩
    [judgment .nil sortTerm (.head u1), judgment (.snoc .nil sortTerm) sortTerm (.head u1)]
    (judgment .nil functionType (.head u0))))]

theorem all_pass : verdicts.all Prod.snd = true := by decide

theorem beta_accepts : check (request 6 beta sortTerm) = true := by decide

theorem forged_root_refuses : check (request 0 ground ground) = false := by decide

end Controls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tower.Checking
