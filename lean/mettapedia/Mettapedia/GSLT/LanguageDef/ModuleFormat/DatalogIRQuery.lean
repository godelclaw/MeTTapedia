import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRJoin
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProvider

/-! The snapshot realization compiles positive atoms to finite provider
queries. Fact rows are data of the immutable round environment, not repeated
arguments of every inference request. No recursive lookup rules are installed.
Scalar guards retain their separate declared relations. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

namespace DatalogQueryAuthoring
open DatalogAuthoring
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_file "../../../../../../metta/gslt/module/DatalogIRQuery.module"
#module_roundtrip DatalogIRQuery
end DatalogQueryAuthoring

namespace DatalogIR.Query

open Mettapedia.OSLF.MeTTaIL Syntax
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def baseLanguage? : Option LanguageDef := DatalogQueryAuthoring.DatalogIRQuery.language.toOption
def baseLanguage : LanguageDef := module_language_view% baseLanguage?
theorem baseLanguage_exact : baseLanguage? = some baseLanguage := by decide +kernel
def factRelation := "dl-fact"

def lowerPremise : Premise → Premise
  | .congruence (.apply "LookupFact" [_]) target => .relationQuery factRelation [target]
  | premise => premise

def lowerRule (pools : Join.Pools) (rule : RewriteRule) : RewriteRule :=
  {rule with
    typeContext := rule.typeContext.filter (fun entry => entry.1 != "facts")
    left := .apply "InferSnapshot" [Join.poolPattern (Join.relationSlots pools),Join.poolPattern (Join.literalSlots pools)]
    premises := rule.premises.map lowerPremise}

def compileClause? (pools : Join.Pools) (statementIndex : Nat)
    (clause : Mettapedia.Languages.Datalog.Clause) : Option RewriteRule :=
  (Join.compileClause? pools statementIndex clause).map (lowerRule pools)

def language (rules : List RewriteRule) : LanguageDef := {baseLanguage with rewrites := rules}
def call (relations literals : List Pattern) : Pattern :=
  .apply "InferSnapshot" [Join.vector relations,Join.vector literals]

def provider (known : List Pattern) : GeneralPremise.ProviderSnapshot where
  signatures := [⟨factRelation,[.base "DlStatement"],[.output]⟩]
  rows := known.map fun fact => ⟨factRelation,[fact]⟩

theorem provider_row_positions (known : List Pattern) :
    (provider known).rows.map (·.values) = known.map (fun fact => [fact]) := by
  simp [provider,List.map_map,Function.comp_def]

theorem provider_rows_exact (known : List Pattern) (row : GeneralPremise.ProviderRow) :
    row ∈ (provider known).rows ↔ ∃ fact ∈ known, row = ⟨factRelation,[fact]⟩ := by
  simp [provider,eq_comm]

theorem conclusion_unchanged (pools : Join.Pools) (rule : RewriteRule) :
    (lowerRule pools rule).right = rule.right := rfl

theorem comparisons_unchanged (relation : String) (arguments : List Pattern) :
    lowerPremise (.relationQuery relation arguments) = .relationQuery relation arguments := rfl

#guard baseLanguage.rewrites.isEmpty
#guard baseLanguage.validate.isEmpty

#print axioms provider_row_positions
#print axioms provider_rows_exact
#print axioms comparisons_unchanged

end DatalogIR.Query
end Mettapedia.GSLT.LanguageDef.ModuleFormat
