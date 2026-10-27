import Mettapedia.OSLF.Framework.GeneralCanonicalQueryAgreement
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Relations served by dynamic services, at the front door

A provider of relations (`GeneralPremise.ProviderSnapshot`) lists rows, and names the relations that admitted dynamic
services implement (`dynamicRelations`); a service answers a request with the rows it serves (`DynamicProvider`). The
front door reads relations through a relation environment, which answers each request when it is made, so a dynamic
relation is native to it.

- **The relation environment of a provider with services** (`servedRelEnv`): a relation answers with its rows, and a
  dynamic relation also with the rows its service serves for the request.
- **It answers exactly that** (`mem_served_iff`), in the service's own terms (`DynamicProvider.Source`).
- **Controls** (`ServedRelations.Controls`): a rule whose premise queries a served relation fires exactly on what the
  service serves, and not without the service.

The runtime's plan semantics resolves a dynamic request with its output schemas uninstantiated, and the reference
relation instantiates what is bound; their agreement on the driver's admitted terms belongs to the integration of the
normalized driver (`Instances/Normalized`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.ServedRelations

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **The relation environment of a provider with dynamic services**: a relation answers with its rows, and a dynamic
relation also with what its service serves for the request. -/
def servedRelEnv (provider : GeneralPremise.ProviderSnapshot) (dynamic : GeneralPremise.DynamicProvider) :
    Engine.RelationEnv where
  tuples relation request :=
    (Framework.GeneralCanonicalAgreement.providerRelEnv provider).tuples relation request ++
      if relation ∈ provider.dynamicRelations then (dynamic.rows? relation request).getD [] else []

/-- **The served environment answers exactly the rows and what the service serves.** -/
theorem mem_served_iff (provider : GeneralPremise.ProviderSnapshot) (dynamic : GeneralPremise.DynamicProvider)
    (relation : String) (request tuple : List Pattern) :
    tuple ∈ (servedRelEnv provider dynamic).tuples relation request ↔
      (∃ row ∈ provider.rows, row.relation = relation ∧ row.values = tuple) ∨
        (relation ∈ provider.dynamicRelations ∧ ∃ rows, dynamic.Source relation request rows ∧ tuple ∈ rows) := by
  simp only [servedRelEnv, Framework.GeneralCanonicalAgreement.providerRelEnv, List.mem_append, List.mem_filterMap]
  apply or_congr
  · constructor
    · rintro ⟨row, member, selected⟩
      by_cases same : row.relation = relation
      · rw [if_pos same] at selected
        exact ⟨row, member, same, Option.some.inj selected⟩
      · rw [if_neg same] at selected
        cases selected
    · rintro ⟨row, member, same, rfl⟩
      exact ⟨row, member, by rw [if_pos same]⟩
  · by_cases dynamicRelation : relation ∈ provider.dynamicRelations
    · rw [if_pos dynamicRelation]
      constructor
      · intro member
        cases served : dynamic.rows? relation request with
        | none => rw [served] at member; cases member
        | some rows =>
          rw [served] at member
          exact ⟨dynamicRelation, rows, (dynamic.rows_exact relation request rows).mp served, member⟩
      · rintro ⟨-, rows, source, member⟩
        rw [(dynamic.rows_exact relation request rows).mpr source]
        exact member
    · rw [if_neg dynamicRelation]
      simp [dynamicRelation]

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.ServedRelations
