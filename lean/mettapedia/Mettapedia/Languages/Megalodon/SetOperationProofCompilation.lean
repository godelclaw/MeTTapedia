import Mettapedia.Languages.Megalodon.LogicalProofCompilation
import Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation
import Mettapedia.Logic.HOL.ProofSyntaxTypeSubstitution

/-!
# The common material HOL signature in Megalodon proof compilation

Six opaque, typed parameters represent membership, empty set, union,
powerset, separation and replacement. Their mathematical laws remain ordered
proof hypotheses. The typed signature map uses the same retained source
proofs as the HOL Light and maintained MM0 routes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SetOperationProofCompilation

open Mettapedia.Logic.HOL
open Embedding.ZFSetHenkinInterpretation
open MathdataKernel HenkinTermInterpretation

def base (_ : Unit) : Ty Base := .base (.inr 0)
def type (source : Ty Unit) : Ty Base := source.substitute base

def symbolName : {source : Ty Unit} → Symbol source → String
  | _, .member => "SetOperationHOL.member"
  | _, .empty => "SetOperationHOL.empty"
  | _, .union => "SetOperationHOL.union"
  | _, .power => "SetOperationHOL.power"
  | _, .separate => "SetOperationHOL.separate"
  | _, .replace => "SetOperationHOL.replace"

def declaration {source : Ty Unit} (symbol : Symbol source) : TermDecl :=
  ⟨symbolName symbol, reifyType (type source), none⟩

def environment : Environment :=
  { terms := [declaration Symbol.member, declaration Symbol.empty,
      declaration Symbol.union, declaration Symbol.power, declaration Symbol.separate,
      declaration Symbol.replace] }

def symbol {source : Ty Unit} (constant : Symbol source) : Constant environment (type source) :=
  .named (symbolName constant) (declaration constant)
    (by cases constant <;> decide +kernel) rfl

def term {gamma : Ctx Unit} {source : Ty Unit} (value : Term Symbol gamma source) :
    Term (Constant environment) (gamma.map type) (type source) :=
  mapTypes base symbol value

def proof {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)}
    {conclusion : Formula Symbol gamma} (value : ProofSyntax Symbol assumptions conclusion) :
    ProofSyntax (Constant environment) (assumptions.map term) (term conclusion) :=
  ProofSyntax.mapTypes base symbol value

theorem proof_nodeCount {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)}
    {conclusion : Formula Symbol gamma} (value : ProofSyntax Symbol assumptions conclusion) :
    (proof value).nodeCount = value.nodeCount :=
  ProofSyntax.nodeCount_mapTypes base symbol value

theorem term_substitution {gamma delta : Ctx Unit}
    (substitution : Subst Symbol gamma delta)
    (translated : Subst (Constant environment) (gamma.map type) (delta.map type))
    (compatible : ∀ {source} (index : Var gamma source),
      term (substitution index) = translated (index.mapTypes base))
    {source : Ty Unit} (value : Term Symbol gamma source) :
    term (subst substitution value) = subst translated (term value) :=
  mapTypes_subst base symbol substitution translated compatible value

def compileLogical {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)}
    {conclusion : Formula Symbol gamma} (value : ProofSyntax Symbol assumptions conclusion) : Option Pf :=
  LogicalProofCompilation.compile (proof value)

end Mettapedia.Languages.Megalodon.SetOperationProofCompilation
