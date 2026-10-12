import Mettapedia.GSLT.Causality.ResourceRuns

/-!
# Complete resource histories are determined by their firing words

For a fixed resource system and initial marking, an ordered word of actual
instances determines every intermediate marking and the complete occurrence
path. No endpoint-only observation has this property in general.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open OccurrenceHistory

universe uRes uRule

variable {R : Type uRes} (S : System.{uRes, uRule} R) [DecidableEq R]

def occurrenceEntry {source target : Multiset R}
    (occurrence : Occurrence S.presentation source target) : S.Entry :=
  ⟨occurrence.site, occurrence.evidence.val⟩

theorem occurrenceEntry_determines {source target target' : Multiset R}
    (first : Occurrence S.presentation source target)
    (second : Occurrence S.presentation source target')
    (same : occurrenceEntry S first = occurrenceEntry S second) :
    target = target' ∧ HEq first second := by
  rcases first with ⟨site, ⟨firing, enabled, endpoint⟩⟩
  rcases second with ⟨site', ⟨firing', enabled', endpoint'⟩⟩
  obtain ⟨sites, instances⟩ := Sigma.mk.inj_iff.mp same
  change site = site' at sites
  change HEq firing firing' at instances
  subst site'
  have equal : firing = firing' := eq_of_heq instances
  subst firing'
  have targets : target = target' := endpoint.trans endpoint'.symm
  refine ⟨targets, ?_⟩
  cases targets
  rfl

theorem pathEntries_determines : ∀ {source target target' : Multiset R}
    (first : OccurrencePath S.presentation source target)
    (second : OccurrencePath S.presentation source target'),
    S.pathEntries first = S.pathEntries second → target = target' ∧ HEq first second
  | _, _, _, .refl _, .refl _, _ => ⟨rfl, HEq.rfl⟩
  | _, _, _, .refl _, .cons _ _, same => by cases same
  | _, _, _, .cons _ _, .refl _, same => by cases same
  | _, _, _, .cons occurrence rest, .cons occurrence' rest', same => by
      obtain ⟨head, tail⟩ := List.cons.inj same
      obtain ⟨middle, sameOccurrence⟩ := occurrenceEntry_determines S occurrence occurrence' head
      subst middle
      have equalOccurrence : occurrence = occurrence' := eq_of_heq sameOccurrence
      subst occurrence'
      obtain ⟨last, sameRest⟩ := pathEntries_determines rest rest' tail
      subst last
      have equalRest : rest = rest' := eq_of_heq sameRest
      subst rest'
      exact ⟨rfl, HEq.rfl⟩

theorem pathEntries_injective {source target : Multiset R} :
    Function.Injective (S.pathEntries (M := source) (N := target)) := by
  intro first second same
  exact eq_of_heq (pathEntries_determines S first second same).2

theorem pathEntries_determines_from {source source' target target' : Multiset R}
    (sources : source = source')
    (first : OccurrencePath S.presentation source target)
    (second : OccurrencePath S.presentation source' target')
    (same : S.pathEntries first = S.pathEntries second) : target = target' ∧ HEq first second := by
  cases sources
  exact pathEntries_determines S first second same

end Mettapedia.GSLT.Causality.ResourceInteraction
