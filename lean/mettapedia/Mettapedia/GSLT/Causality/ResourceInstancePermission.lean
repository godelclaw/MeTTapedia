import Mettapedia.GSLT.Causality.ResourceRuns

/-!
# Permitted resource instances and retained occurrence paths

A permission predicate restricts actual rule instances. Consumption, reads
and production are inherited from the supplied resource system. Forgetting
the permission proof retains the original firing, every intermediate
marking and the complete ordered occurrence path.

This is permission for a fixed firing presentation. It does not infer
permission from a price, a preference or availability of a resource.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open OccurrenceHistory

universe uRes uRule uValue

variable {R : Type uRes} (S : System.{uRes, uRule} R)
  (permitted : ∀ {site : S.Site}, S.Instance site → Prop)

def permittedSystem : System.{uRes, uRule} R where
  Site := S.Site
  Instance site := {firing : S.Instance site // permitted firing}
  consume firing := S.consume firing.val
  read firing := S.read firing.val
  produce firing := S.produce firing.val

theorem permitted_enables_iff (marking : Multiset R) {site : S.Site}
    (firing : (permittedSystem S permitted).Instance site) :
    (permittedSystem S permitted).Enables marking firing ↔ S.Enables marking firing.val :=
  Iff.rfl

theorem permitted_instance_exists_iff (marking : Multiset R) {site : S.Site}
    (firing : S.Instance site) :
    (∃ admitted : (permittedSystem S permitted).Instance site,
      admitted.val = firing ∧ (permittedSystem S permitted).Enables marking admitted) ↔
      permitted firing ∧ S.Enables marking firing := by
  constructor
  · rintro ⟨admitted, rfl, enabled⟩
    exact ⟨admitted.property, enabled⟩
  · rintro ⟨permission, enabled⟩
    exact ⟨⟨firing, permission⟩, rfl, enabled⟩

variable [DecidableEq R]

def forgetPermissionOccurrence {source target : Multiset R}
    (occurrence : Occurrence (permittedSystem S permitted).presentation source target) :
    Occurrence S.presentation source target :=
  ⟨occurrence.site, ⟨occurrence.evidence.val.val, occurrence.evidence.property⟩⟩

def forgetPermissionPath : {source target : Multiset R} →
    OccurrencePath (permittedSystem S permitted).presentation source target →
      OccurrencePath S.presentation source target
  | _, _, .refl source => OccurrencePath.refl (P := S.presentation) source
  | _, _, .cons occurrence rest =>
      .cons (forgetPermissionOccurrence S permitted occurrence) (forgetPermissionPath rest)

def forgetPermissionEntry (entry : (permittedSystem S permitted).Entry) : S.Entry :=
  ⟨entry.1, entry.2.val⟩

theorem forgetPermissionPath_entries : ∀ {source target : Multiset R}
    (path : OccurrencePath (permittedSystem S permitted).presentation source target),
    S.pathEntries (forgetPermissionPath S permitted path) =
      ((permittedSystem S permitted).pathEntries path).map (forgetPermissionEntry S permitted)
  | _, _, .refl _ => rfl
  | _, _, .cons occurrence rest => by
      change forgetPermissionEntry S permitted ⟨occurrence.site, occurrence.evidence.val⟩ ::
        S.pathEntries (forgetPermissionPath S permitted rest) = _
      rw [forgetPermissionPath_entries rest]
      rfl

theorem forgetPermissionPath_append : ∀ {source middle target : Multiset R}
    (first : OccurrencePath (permittedSystem S permitted).presentation source middle)
    (second : OccurrencePath (permittedSystem S permitted).presentation middle target),
    forgetPermissionPath S permitted (first.append second) =
      (forgetPermissionPath S permitted first).append (forgetPermissionPath S permitted second)
  | _, _, _, .refl _, _ => rfl
  | _, _, _, .cons occurrence rest, second => by
      change OccurrencePath.cons (forgetPermissionOccurrence S permitted occurrence)
        (forgetPermissionPath S permitted (rest.append second)) = _
      rw [forgetPermissionPath_append rest second]
      rfl

theorem forgotten_entries_permitted {source target : Multiset R}
    (path : OccurrencePath (permittedSystem S permitted).presentation source target) :
    ∀ entry ∈ S.pathEntries (forgetPermissionPath S permitted path), permitted entry.2 := by
  rw [forgetPermissionPath_entries]
  intro entry member
  obtain ⟨admitted, _, rfl⟩ := List.mem_map.mp member
  exact admitted.2.property

theorem forgetPermissionPath_valuation {Value : Type uValue} [AddCommMonoid Value]
    (value : ∀ {site : S.Site}, S.Instance site → Value)
    {source target : Multiset R}
    (path : OccurrencePath (permittedSystem S permitted).presentation source target) :
    (S.instanceValuation value).onPath (forgetPermissionPath S permitted path) =
      ((permittedSystem S permitted).instanceValuation fun admitted => value admitted.val).onPath path := by
  rw [S.instanceValuation_onPath, forgetPermissionPath_entries,
    (permittedSystem S permitted).instanceValuation_onPath, List.map_map]
  rfl

end Mettapedia.GSLT.Causality.ResourceInteraction
