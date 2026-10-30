import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRJoin

/-! Separating clause-compilation controls: shared variables, literal pools,
range refusal, missing names and retained comparison operations. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Join.Controls

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL.Syntax

def pools : Pools := ⟨[["edge"],["path"]],[.symbol "a"]⟩
def transitive : Clause :=
  ⟨⟨["path"],[.var "X",.var "Y"]⟩,
   [.atom ⟨["edge"],[.var "X",.var "Z"]⟩,.atom ⟨["edge"],[.var "Z",.var "Y"]⟩]⟩
def literalClause : Clause :=
  ⟨⟨["path"],[.var "X",.literal (.symbol "a")]⟩,
   [.atom ⟨["edge"],[.var "X",.literal (.symbol "a")]⟩]⟩
def unsafeClause : Clause := ⟨⟨["path"],[.var "X"]⟩,[]⟩
def rule : RewriteRule := (compileClause? pools 7 transitive).get (by decide +kernel)

theorem compiled : compileClause? pools 7 transitive = some rule := by decide +kernel

theorem shared_join_variable : rule.premises =
    [.congruence (.apply "LookupFact" [.fvar "facts"])
       (.apply "GroundFact" [.fvar "pool:relation:0",.apply "GroundTuple"
         [vector [.fvar "variable:X",.fvar "variable:Z"]]]),
     .congruence (.apply "LookupFact" [.fvar "facts"])
       (.apply "GroundFact" [.fvar "pool:relation:0",.apply "GroundTuple"
         [vector [.fvar "variable:Z",.fvar "variable:Y"]]])] := by decide +kernel

theorem literal_is_bound_before_body :
    (compileClause? pools 8 literalClause).map (·.left) = some
      (.apply "Infer" [poolPattern ["pool:relation:0","pool:relation:1"],
        poolPattern ["pool:literal:0"],.fvar "facts"]) := by decide +kernel

theorem missing_relation_refused : compileClause? ⟨[["edge"]],[]⟩ 7 transitive = none := by decide +kernel
theorem missing_literal_refused : compileClause? ⟨pools.relations,[]⟩ 8 literalClause = none := by decide +kernel
theorem unsafe_refused : compileClause? pools 9 unsafeClause = none := by decide +kernel

#guard rule.name == "datalog-clause:7"
#guard rule.typeContext.count ("variable:Z",.base "DlValue") == 1
#guard (language [rule]).validate.isEmpty

#print axioms compiled
#print axioms shared_join_variable
#print axioms literal_is_bound_before_body
#print axioms unsafe_refused

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Join.Controls
