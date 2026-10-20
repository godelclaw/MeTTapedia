import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
import Mettapedia.OSLF.MeTTaIL.CollectionExecutionAdmission
import Mettapedia.OSLF.MeTTaIL.EquationalScopedMatching
import Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine

/-!
# Authored collection consumers

The Petri presentation observes multiplicity. The graph presentation observes
idempotent membership and preserves its premises when publishing a new edge.
These are source fixtures for compiler qualification; loading their syntax is
distinct from admitting or executing them.
-/

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
set_option autoImplicit false

#module_file "../../../../../metta/gslt/module/CollectionPetri.module"
#module_file "../../../../../metta/gslt/module/CollectionReachability.module"

namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers

open Mettapedia.OSLF.MeTTaIL Syntax

def petri? : Except ModuleSource.Error LanguageDef := CollectionPetri.language
def reachability? : Except ModuleSource.Error LanguageDef := CollectionReachability.language

private def emptyLanguage : LanguageDef :=
  { «name» := "", «types» := [], «terms» := [], «equations» := [], «rewrites» := [] }

def petriSource : LanguageDef := petri?.toOption.getD emptyLanguage
def reachabilitySource : LanguageDef := reachability?.toOption.getD emptyLanguage
def petri : LanguageDef :=
  ((petriSource.toCore.toOption).map (·.language)).getD emptyLanguage
def reachability : LanguageDef :=
  ((reachabilitySource.toCore.toOption).map (·.language)).getD emptyLanguage

theorem petri_loaded : petri? = .ok petriSource := by rfl
theorem reachability_loaded : reachability? = .ok reachabilitySource := by rfl

example : petriSource.toCore.isOk = true := by cbv
example : reachabilitySource.toCore.isOk = true := by cbv

def marking (items : List Pattern) : Pattern := .collection .hashBag items none
def graph (items : List Pattern) : Pattern := .collection .hashSet items none
def token (label : String) : Pattern := .apply label []
def edge (source target : String) : Pattern := .apply "Edge" [token source, token target]

def snapshot (language : LanguageDef) : GeneralExecutionAdmission.Snapshot :=
  ⟨language, [], ⟨[], [], []⟩⟩

/-- Rules transform entire markings/fact sets; they do not reduce inside a
place token or an edge. Collection equality is handled by canonical commits. -/
def permissions : GeneralExecutionAdmission.Permissions :=
  { sites := .rootOnly, includeDerivedEquations := false }

def petriPlan : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile (snapshot petri) permissions

def reachabilityPlan : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile (snapshot reachability) permissions

theorem petri_admitted : petriPlan.complete = true := by cbv

/-- The current compiler must keep refusing this source until the new matcher
and its coherence certificate are connected to the admitted execution path. -/
theorem reachability_requires_set_matching :
    .setDecomposition ∈ reachabilityPlan.obligations := by
  cbv
  exact .head _

def petriCollectionAdmission :=
  CollectionExecutionAdmission.admit? petriPlan

def reachabilityCollectionAdmission :=
  CollectionExecutionAdmission.admit? reachabilityPlan

theorem petri_collection_admitted : petriCollectionAdmission.isSome = true := by cbv
theorem reachability_collection_admitted :
    reachabilityCollectionAdmission.isSome = true := by cbv

def petriCertificate : CollectionExecutionAdmission.Certificate petriPlan :=
  ⟨by cbv⟩

def reachabilityCertificate : CollectionExecutionAdmission.Certificate reachabilityPlan :=
  ⟨by cbv⟩

def petriRequest? (declaration : Nat) (targets : List Pattern) :
    Option ScopedCollectionMachine.Request :=
  CollectionExecutionAdmission.request? petriPlan petriCertificate declaration targets

def reachabilityRequest? (declaration : Nat) (targets : List Pattern) :
    Option ScopedCollectionMachine.Request :=
  CollectionExecutionAdmission.request? reachabilityPlan reachabilityCertificate declaration targets

def queries : List (String × Option ScopedCollectionMachine.Request) :=
  [ ("petri-ab", petriRequest? 0 [token "A", token "B"])
  , ("petri-aab", petriRequest? 0 [token "A", token "A", token "B"])
  , ("petri-missing-b", petriRequest? 0 [token "A"])
  , ("reachability-ab-bc", reachabilityRequest? 0 [edge "A" "B", edge "B" "C"])
  , ("reachability-self-loop", reachabilityRequest? 0 [edge "A" "A"])
  , ("reachability-missing-link", reachabilityRequest? 0 [edge "A" "B", edge "A" "C"]) ]

def planQueries : List (String × Option ScopedCollectionMachine.Request) :=
  let petriSource := .collection .hashBag [token "A", token "B"] none
  let graphSource := .collection .hashSet [edge "A" "B", edge "B" "C"] none
  (CollectionExecutionAdmission.requestsForSource petriPlan petriCertificate petriSource).map
      (fun (ordinal, request) => (s!"petri-plan-ab-{ordinal}", some request)) ++
    (CollectionExecutionAdmission.requestsForSource reachabilityPlan reachabilityCertificate graphSource).map
      (fun (ordinal, request) => (s!"reachability-plan-chain-{ordinal}", some request))

theorem queries_extracted : queries.all (fun row => row.2.isSome) = true := by cbv
theorem plan_queries_extracted : planQueries.length = 3 := by cbv

example : petri.rewrites.length = 2 := by cbv
example : reachability.rewrites.length = 1 := by cbv

example : petri.rewrites[0]?.map (·.left) =
    some (.collection .hashBag [token "A", token "B"] (some "rest")) := by cbv

example : reachability.rewrites[0]?.map (·.left) =
    some (.collection .hashSet
      [.apply "Edge" [.fvar "x", .fvar "y"], .apply "Edge" [.fvar "y", .fvar "z"]]
      (some "rest")) := by cbv

end Mettapedia.GSLT.LanguageDef.CollectionConsumers
