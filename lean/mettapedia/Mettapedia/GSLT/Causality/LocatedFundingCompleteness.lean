import Mettapedia.GSLT.Causality.LocatedPermittedProjection
import Mettapedia.GSLT.Causality.ResourceHistoryWord

/-!
# Funding a specified history with permitted, located, ordered keys

The purse plan is a run of the independently defined purse system. A joint
word names actual permitted instances and their selected purse tails.
Synchronizing its original firing word with its purse word constructs an
actual paid history. Conversely every paid history supplies both runs.

The complete original history, not only its endpoint or aggregate price,
is recovered. A cell count alone does not furnish the purse plan.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open OccurrenceHistory

universe uRes uRule

variable {R : Type uRes} {Place Cell : Type uRule}
  (S : System.{uRes, uRule} R)
  (permitted : ∀ {site : S.Site}, S.Instance site → Prop)
  (place : ∀ {site : S.Site}, S.Instance site → Place)
  (key : ∀ {site : S.Site}, S.Instance site → Cell)
  [DecidableEq R] [DecidableEq Place] [DecidableEq Cell]

theorem permitted_fires_iff (order : List (permittedSystem S @permitted).Entry)
    (source target : Multiset R) :
    (permittedSystem S @permitted).Fires order source target ↔
      S.Fires (order.map (forgetPermissionEntry S @permitted)) source target := by
  induction order generalizing source with
  | nil => rfl
  | cons entry rest ih =>
      change S.Enables source entry.2.val ∧
        (permittedSystem S @permitted).Fires rest (S.fire source entry.2.val) target ↔
          S.Enables source entry.2.val ∧
            S.Fires (rest.map (forgetPermissionEntry S @permitted)) (S.fire source entry.2.val) target
      exact and_congr_right' (ih (S.fire source entry.2.val))

def locatedPurseEntry (entry : (locatedPermitted S @permitted @place @key).Entry) :
    (pursesMany Place Cell).Entry :=
  ⟨place entry.2.1.val, ({(key entry.2.1.val, entry.2.2)} : Multiset (Cell × List Cell))⟩

theorem located_fires_iff
    (order : List (locatedPermitted S @permitted @place @key).Entry)
    (source target : Multiset R) (purses remaining : Multiset (Place × List Cell)) :
    (locatedPermitted S @permitted @place @key).Fires order
      (marking source purses) (marking target remaining) ↔
      S.Fires (order.map (locatedOriginalEntry S @permitted @place @key)) source target ∧
        (pursesMany Place Cell).Fires
          (order.map (locatedPurseEntry S @permitted @place @key)) purses remaining := by
  have comparison := (permittedSystem S @permitted).product_fires_iff
    (pursesMany Place Cell)
    (fun {site} (firing : (permittedSystem S @permitted).Instance site × List Cell) => ⟨site, firing.1⟩)
    (fun {site} (firing : (permittedSystem S @permitted).Instance site × List Cell) =>
      ⟨place firing.1.val, ({(key firing.1.val, firing.2)} : Multiset (Cell × List Cell))⟩)
    order source purses (marking target remaining)
  constructor
  · intro run
    obtain ⟨target', remaining', endpoints, original, payment⟩ := comparison.mp run
    have targets : target = target' := by
      simpa only [leftPart_marking] using congrArg leftPart endpoints
    have remains : remaining = remaining' := by
      simpa only [rightPart_marking] using congrArg rightPart endpoints
    subst target'
    subst remaining'
    refine ⟨?_, payment⟩
    have erased := (permitted_fires_iff S @permitted _ source target).mp original
    change S.Fires ((order.map (fun entry => (⟨entry.1, entry.2.1⟩ :
      (permittedSystem S @permitted).Entry))).map
        (fun entry => (⟨entry.1, entry.2.val⟩ : S.Entry))) source target at erased
    change S.Fires (order.map fun entry => (⟨entry.1, entry.2.1.val⟩ : S.Entry)) source target
    simpa only [List.map_map, Function.comp_def] using erased
  · rintro ⟨original, payment⟩
    apply comparison.mpr
    refine ⟨target, remaining, rfl, ?_, payment⟩
    apply (permitted_fires_iff S @permitted _ source target).mpr
    change S.Fires ((order.map (fun entry => (⟨entry.1, entry.2.1⟩ :
      (permittedSystem S @permitted).Entry))).map
        (fun entry => (⟨entry.1, entry.2.val⟩ : S.Entry))) source target
    change S.Fires (order.map fun entry => (⟨entry.1, entry.2.1.val⟩ : S.Entry)) source target at original
    simpa only [List.map_map, Function.comp_def] using original

theorem located_history_iff
    (order : List (locatedPermitted S @permitted @place @key).Entry)
    (source target : Multiset R) (purses remaining : Multiset (Place × List Cell)) :
    (∃ paid : OccurrencePath (locatedPermitted S @permitted @place @key).presentation
      (marking source purses) (marking target remaining),
        (locatedPermitted S @permitted @place @key).pathEntries paid = order) ↔
      S.Fires (order.map (locatedOriginalEntry S @permitted @place @key)) source target ∧
        (pursesMany Place Cell).Fires
          (order.map (locatedPurseEntry S @permitted @place @key)) purses remaining :=
  ((locatedPermitted S @permitted @place @key).fires_iff_exists_path order).symm.trans
    (located_fires_iff S @permitted @place @key order source target purses remaining)

theorem specified_history_has_located_funding_iff {source target : Multiset R}
    (original : OccurrencePath S.presentation source target)
    (order : List (locatedPermitted S @permitted @place @key).Entry)
    (reads : order.map (locatedOriginalEntry S @permitted @place @key) = S.pathEntries original)
    (purses remaining : Multiset (Place × List Cell)) :
    (∃ paid : OccurrencePath (locatedPermitted S @permitted @place @key).presentation
      (marking source purses) (marking target remaining),
        (locatedPermitted S @permitted @place @key).pathEntries paid = order ∧
          HEq (locatedOriginalPath S @permitted @place @key paid) original) ↔
      (pursesMany Place Cell).Fires
        (order.map (locatedPurseEntry S @permitted @place @key)) purses remaining := by
  constructor
  · rintro ⟨paid, entries, _⟩
    exact ((located_history_iff S @permitted @place @key order source target purses remaining).mp
      ⟨paid, entries⟩).2
  · intro payment
    have executable : S.Fires (order.map (locatedOriginalEntry S @permitted @place @key))
        source target := reads ▸ S.fires_pathEntries original
    obtain ⟨paid, entries⟩ :=
      (located_history_iff S @permitted @place @key order source target purses remaining).mpr
        ⟨executable, payment⟩
    refine ⟨paid, entries, ?_⟩
    have exactWord := locatedOriginalPath_entries S @permitted @place @key paid
    rw [entries, reads] at exactWord
    exact (pathEntries_determines_from S (leftPart_marking source purses)
      (locatedOriginalPath S @permitted @place @key paid) original exactWord).2

end Mettapedia.GSLT.Causality.ResourceInteraction
