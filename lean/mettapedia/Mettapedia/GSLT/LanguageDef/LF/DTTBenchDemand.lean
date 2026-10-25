/-
# DTTBench product-rule demand

This module analyzes the frozen Lean-owned DTTBench statements without replaying
any witness.  It models the signature-free lambda-Pi fragment used by those
statements, records every product rule needed during formation, and checks the
result against the source-extracted profiles in `Profiles.lean`.
-/

import Mettapedia.GSLT.LanguageDef.LF.Profiles
import Mettapedia.GSLT.LanguageDef.LF.PureCorrespondence
import Mettapedia.GSLT.Dedukti.PureTypeSystem
import Mettapedia.GSLT.LanguageDef.Pure.BetaEtaConversion
import Mettapedia.GSLT.LanguageDef.Pure.DTTBench31

namespace Mettapedia.GSLT.LanguageDef.LFDTTBenchDemand

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFProfile
open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureDTTBench31

/-- An inferred object type or a PTS universe result. -/
inductive Inferred where
  | term : Pure.Expr → Inferred
  | universe : Srt → Inferred
  deriving DecidableEq, Repr

def productResult? (profile : Profile) (domain codomain : Srt) : Option Srt :=
  (profile.products.find? fun rule =>
    rule.domain = domain && rule.codomain = codomain).map ProductRule.result

def matchesExpected : Inferred → Pure.Expr → Bool
  | .term actual, expected => PureBetaEta.convBool actual expected
  | .universe _, _ => false

mutual
/-- Executable profile-parametric inference for the closed DTTBench statement fragment. -/
def infer : Nat → Profile → Pure.Ctx → Pure.Expr → Option Inferred
  | 0, _, _, _ => none
  | _fuel + 1, _, _, .sort => some (.universe .kind)
  | _fuel + 1, _, context, .bvar index =>
      (Pure.ctxLookup context index).map .term
  | fuel + 1, profile, context, .pi domain body => do
      let domainSort ← inferSort fuel profile context domain
      let bodySort ← inferSort fuel profile (domain :: context) body
      let resultSort ← productResult? profile domainSort bodySort
      pure (.universe resultSort)
  | fuel + 1, profile, context, .lam domain body => do
      let domainSort ← inferSort fuel profile context domain
      let bodyType ← infer fuel profile (domain :: context) body
      match bodyType with
      | .universe _ => none
      | .term bodyType =>
          let bodySort ← inferSort fuel profile (domain :: context) bodyType
          let _ ← productResult? profile domainSort bodySort
          pure (.term (.pi domain bodyType))
  | fuel + 1, profile, context, .app fn argument => do
      let fnType ← infer fuel profile context fn
      match fnType with
      | .universe _ => none
      | .term fnType =>
          match PureBetaEta.normalForm fnType with
          | .pi domain body =>
              let argumentType ← infer fuel profile context argument
              if matchesExpected argumentType domain then
                pure (.term (Pure.Expr.subst0 argument body))
              else none
          | _ => none

/-- Sort synthesized for a type/kind expression. -/
def inferSort : Nat → Profile → Pure.Ctx → Pure.Expr → Option Srt
  | 0, _, _, _ => none
  | fuel + 1, profile, context, expression => do
      match ← infer fuel profile context expression with
      | .universe sort => pure sort
      | .term type =>
          if PureBetaEta.convBool type .sort then pure .type else none
end

mutual
/-- Collect every product rule exercised by explicit products and lambda types. -/
def collect : Nat → Profile → Pure.Ctx → Pure.Expr → Option (List ProductRule)
  | 0, _, _, _ => none
  | _fuel + 1, _, _, .sort => some []
  | _fuel + 1, _, _, .bvar _ => some []
  | fuel + 1, profile, context, .pi domain body => do
      let domainSort ← inferSort fuel profile context domain
      let bodySort ← inferSort fuel profile (domain :: context) body
      let resultSort ← productResult? profile domainSort bodySort
      let domainRules ← collect fuel profile context domain
      let bodyRules ← collect fuel profile (domain :: context) body
      pure (⟨domainSort, bodySort, resultSort⟩ :: domainRules ++ bodyRules)
  | fuel + 1, profile, context, .lam domain body => do
      let domainSort ← inferSort fuel profile context domain
      let bodyInferred ← infer fuel profile (domain :: context) body
      let bodyType ← match bodyInferred with
        | .term type => some type
        | .universe _ => none
      let bodySort ← inferSort fuel profile (domain :: context) bodyType
      let resultSort ← productResult? profile domainSort bodySort
      let domainRules ← collect fuel profile context domain
      let bodyRules ← collect fuel profile (domain :: context) body
      pure (⟨domainSort, bodySort, resultSort⟩ :: domainRules ++ bodyRules)
  | fuel + 1, profile, context, .app fn argument => do
      let fnRules ← collect fuel profile context fn
      let argumentRules ← collect fuel profile context argument
      pure (fnRules ++ argumentRules)
end

def analysisFuel : Nat := 4096

def demand? (profile : Profile) (goal : Pure.Expr) : Option (List ProductRule) := do
  let _ ← inferSort analysisFuel profile [] goal
  collect analysisFuel profile [] goal

def statementWithin (profile : Profile) (statement : Statement) : Bool :=
  (demand? profile statement.goal).isSome

structure DemandRow where
  name : String
  resultSort : Option Srt
  rules : List ProductRule
  deriving DecidableEq, Repr

def demandRow (profile : Profile) (statement : Statement) : DemandRow :=
  { name := statement.name
    resultSort := inferSort analysisFuel profile [] statement.goal
    rules := (demand? profile statement.goal).getD [] }

def prototypeRows : List DemandRow :=
  statements.map (demandRow mettaKernelKindResultPrototype)

def allWithinMettaKernelPrototype : Bool :=
  statements.all (statementWithin mettaKernelKindResultPrototype)

def allWithinStandardLF : Bool := statements.all (statementWithin standardLF)

/-- The two rows selected before the native T1 pilot. -/
def pilotNames : List String := ["Eq_congrFun", "sSup_inter_le"]

def pilotRows : List DemandRow :=
  prototypeRows.filter fun row => row.name ∈ pilotNames

def allDemandRules : List ProductRule :=
  (prototypeRows.flatMap DemandRow.rules).eraseDups

/-! ## Closed-corpus demand theorems

These propositions reduce in the Lean kernel from the 31 frozen statement values.
They concern statement formation only: no proof witness and no `Pure` acceptance
judgment is replayed here.
-/

/-- The analysis visits exactly the 31 frozen DTTBench statements. -/
theorem prototypeRows_length : prototypeRows.length = 31 := by
  simp [prototypeRows, statements_length]

/-- Every frozen statement is formable at the historical four-rule
curriculum profile. -/
theorem allWithinMettaKernelPrototype_eq_true :
    allWithinMettaKernelPrototype = true := by
  rfl

/-- Statement-level form of the prototype coverage result. -/
theorem statementWithin_mettaKernelPrototype_of_mem {statement : Statement}
    (hstatement : statement ∈ statements) :
    statementWithin mettaKernelKindResultPrototype statement = true :=
  (List.all_eq_true.mp allWithinMettaKernelPrototype_eq_true) statement hstatement

/-- Standard LF is too small for the frozen statement collection. -/
theorem allWithinStandardLF_eq_false : allWithinStandardLF = false := by
  rfl

/-- The corpus exercises every product rule of the historical four-rule
prototype, including both additions to standard LF. -/
theorem allDemandRules_eq_mettaKernelPrototype :
    allDemandRules =
      [kindKindKind, typeKindKind, kindTypeKind, typeTypeType] := by
  set_option maxRecDepth 100000 in
    rfl

/-- The `Eq_congrFun` statement requires the Type-parameter product. -/
theorem Eq_congrFun_requires_kindKindKind :
    kindKindKind ∈
      (demand? mettaKernelKindResultPrototype goal_Eq_Eq_congrFun).getD [] := by
  decide

/-- Standard LF cannot form the `Eq_congrFun` statement. -/
theorem Eq_congrFun_not_within_standardLF :
    demand? standardLF goal_Eq_Eq_congrFun = none := by
  rfl

/-- The `sSup_inter_le` statement also requires the Type-parameter product. -/
theorem sSup_inter_le_requires_kindKindKind :
    kindKindKind ∈
      (demand? mettaKernelKindResultPrototype goal_Leq_sSup_inter_le).getD [] := by
  decide

/-- Standard LF cannot form the `sSup_inter_le` statement. -/
theorem sSup_inter_le_not_within_standardLF :
    demand? standardLF goal_Leq_sSup_inter_le = none := by
  rfl

/-- A profile contains the DTTBench point when it contains its sort axiom and
every product rule computed from the frozen statement collection. -/
def ContainsDTTBench (profile : Profile) : Prop :=
  profile.sortAxiom .type = some .kind ∧
    ∀ rule, rule ∈ allDemandRules → rule ∈ profile.products

/-- The source-extracted MettaKernel prototype contains the frozen DTTBench
statement point. -/
theorem mettaKernelPrototype_contains_DTTBench :
    ContainsDTTBench mettaKernelKindResultPrototype := by
  constructor
  · rfl
  · intro rule hrule
    rw [allDemandRules_eq_mettaKernelPrototype] at hrule
    simp [mettaKernelKindResultPrototype] at hrule ⊢
    aesop

/-- Standard LF does not contain the frozen DTTBench point. -/
theorem standardLF_does_not_contain_DTTBench :
    ¬ ContainsDTTBench standardLF := by
  intro hcontains
  have hdemand : kindKindKind ∈ allDemandRules := by
    rw [allDemandRules_eq_mettaKernelPrototype]
    simp
  have hbasic := hcontains.2 kindKindKind hdemand
  simp [standardLF, kindKindKind, typeTypeType, typeKindKind] at hbasic

/-- T2 minimality crown: every profile containing the frozen DTTBench demand
subsumes the historical four-rule prototype. -/
theorem mettaKernelPrototype_minimal_for_DTTBench {profile : Profile}
    (hcontains : ContainsDTTBench profile) :
    mettaKernelKindResultPrototype ⊑ profile := by
  constructor
  · intro source target haxiom
    cases source <;> simp [mettaKernelKindResultPrototype, typeAxiom] at haxiom
    · cases haxiom
      exact hcontains.1
  · intro rule hrule
    apply hcontains.2 rule
    rw [allDemandRules_eq_mettaKernelPrototype]
    simp [mettaKernelKindResultPrototype] at hrule ⊢
    aesop

/-! ## Typability under CoC formation

The demand above is computed while inferring at the historical prototype.
It is not a profile-independent lower bound on the rules needed to type the
same raw statements: changing the result sort changes later premises.  The
independently proved conversion-capable checker gives the relevant typability
test for the CoC profile.
-/

def cocInferenceFuel : Nat := 4096

def cocInferredType? (statement : Statement) : Option LF.Term :=
  LFConversionProfileChecker.infer cocInferenceFuel
    Mettapedia.GSLT.Dedukti.constructions [] []
      (LFPureCorrespondence.encodeExpr statement.goal)

def statementTypableInCoc (statement : Statement) : Bool :=
  cocInferredType? statement == some (.srt .type)

def allStatementsTypableInCoc : Bool :=
  statements.all statementTypableInCoc

/-- Every one of the 31 frozen statement types is inferred at sort `Type` by
the generic checker instantiated with CoC formation. -/
theorem allStatementsTypableInCoc_eq_true :
    allStatementsTypableInCoc = true := by
  rfl

theorem coc_inferredType_of_mem {statement : Statement}
    (member : statement ∈ statements) :
    cocInferredType? statement = some (.srt .type) := by
  have checked :=
    (List.all_eq_true.mp allStatementsTypableInCoc_eq_true) statement member
  simpa [statementTypableInCoc] using checked

/-- Statement formation is not merely a Boolean observation: sound inference
constructs the independently specified declarative CoC typing judgment. -/
theorem coc_typable_of_mem {statement : Statement}
    (member : statement ∈ statements) :
    LFConversionProfileChecker.Deriv Mettapedia.GSLT.Dedukti.constructions
      [] [] (LFPureCorrespondence.encodeExpr statement.goal) (.srt .type) :=
  (LFConversionProfileChecker.infer_check_sound cocInferenceFuel).1
    Mettapedia.GSLT.Dedukti.constructions [] []
      (LFPureCorrespondence.encodeExpr statement.goal) (.srt .type)
      (coc_inferredType_of_mem member)

/-- The prototype-specific demand contains its unusual result rule, while
CoC types the whole raw corpus without that rule.  Thus the computed demand
separates inference profiles, not the statements' typability. -/
theorem prototype_demand_not_necessary_for_coc_typability :
    kindTypeKind ∉ Mettapedia.GSLT.Dedukti.constructions.products ∧
      allStatementsTypableInCoc = true :=
  ⟨by decide, allStatementsTypableInCoc_eq_true⟩

#print axioms allWithinMettaKernelPrototype_eq_true
#print axioms statementWithin_mettaKernelPrototype_of_mem
#print axioms Eq_congrFun_requires_kindKindKind
#print axioms sSup_inter_le_requires_kindKindKind
#print axioms mettaKernelPrototype_minimal_for_DTTBench
#print axioms allStatementsTypableInCoc_eq_true
#print axioms coc_typable_of_mem
#print axioms prototype_demand_not_necessary_for_coc_typability

end Mettapedia.GSLT.LanguageDef.LFDTTBenchDemand
