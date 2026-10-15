import Mettapedia.GSLT.Causality.LocatedPermittedHistory
import Mathlib.CategoryTheory.EqToHom

/-!
# Actual path projection of located, permitted funding

Every supplied paid firing projects to its original resource firing. The
projection constructs the complete original path, preserving its sites,
instance order, intermediate resource markings and arbitrary additive
instance valuations. It is a functor on the actual occurrence categories.

Projection forgets the purses. Its existence does not supply funding for an
arbitrary original path or identify paid receipts having the same readout.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open _root_.CategoryTheory OccurrenceHistory

universe uRes uRule uValue

variable {R : Type uRes} {Place Cell : Type uRule}
  (S : System.{uRes, uRule} R)
  (permitted : ∀ {site : S.Site}, S.Instance site → Prop)
  (place : ∀ {site : S.Site}, S.Instance site → Place)
  (key : ∀ {site : S.Site}, S.Instance site → Cell)
  [DecidableEq R] [DecidableEq Place] [DecidableEq Cell]

def locatedOriginalOccurrence {source target : Multiset (R ⊕ (Place × List Cell))}
    (occurrence : Occurrence (locatedPermitted S permitted place key).presentation source target) :
    Occurrence S.presentation (leftPart source) (leftPart target) := by
  refine ⟨occurrence.site, ⟨occurrence.evidence.val.1.val, ?_, ?_⟩⟩
  · have actual : (locatedPermitted S permitted place key).Enables
        (marking (leftPart source) (rightPart source)) occurrence.evidence.val :=
      Eq.mpr (congrArg (fun resources =>
        (locatedPermitted S permitted place key).Enables resources occurrence.evidence.val)
          (marking_leftPart_rightPart source)) occurrence.evidence.property.1
    exact ((locatedPermitted_enables_iff S permitted place key
      (leftPart source) (rightPart source) occurrence.evidence.val.1
        occurrence.evidence.val.2).mp actual).1
  · calc
      leftPart target = leftPart ((locatedPermitted S permitted place key).fire
          source occurrence.evidence.val) := congrArg leftPart occurrence.evidence.property.2
      _ = leftPart ((locatedPermitted S permitted place key).fire
          (marking (leftPart source) (rightPart source)) occurrence.evidence.val) :=
        congrArg (fun resources => leftPart
          ((locatedPermitted S permitted place key).fire resources occurrence.evidence.val))
            (marking_leftPart_rightPart source).symm
      _ = S.fire (leftPart source) occurrence.evidence.val.1.val :=
        (congrArg leftPart (locatedPermitted_fire S permitted place key
          (leftPart source) (rightPart source) occurrence.evidence.val.1
            occurrence.evidence.val.2)).trans (leftPart_marking _ _)

def locatedOriginalPath : {source target : Multiset (R ⊕ (Place × List Cell))} →
    OccurrencePath (locatedPermitted S permitted place key).presentation source target →
      OccurrencePath S.presentation (leftPart source) (leftPart target)
  | _, _, .refl source => OccurrencePath.refl (P := S.presentation) (leftPart source)
  | _, _, .cons occurrence rest =>
      .cons (locatedOriginalOccurrence S permitted place key occurrence) (locatedOriginalPath rest)

theorem locatedOriginalPath_entries : ∀ {source target : Multiset (R ⊕ (Place × List Cell))}
    (path : OccurrencePath (locatedPermitted S permitted place key).presentation source target),
    S.pathEntries (locatedOriginalPath S permitted place key path) =
      ((locatedPermitted S permitted place key).pathEntries path).map
        (locatedOriginalEntry S permitted place key)
  | _, _, .refl _ => rfl
  | _, _, .cons occurrence rest => by
      change locatedOriginalEntry S permitted place key ⟨occurrence.site, occurrence.evidence.val⟩ ::
        S.pathEntries (locatedOriginalPath S permitted place key rest) = _
      rw [locatedOriginalPath_entries rest]
      rfl

theorem locatedOriginalPath_append :
    ∀ {source middle target : Multiset (R ⊕ (Place × List Cell))}
    (first : OccurrencePath (locatedPermitted S permitted place key).presentation source middle)
    (second : OccurrencePath (locatedPermitted S permitted place key).presentation middle target),
    locatedOriginalPath S permitted place key (first.append second) =
      (locatedOriginalPath S permitted place key first).append
        (locatedOriginalPath S permitted place key second)
  | _, _, _, .refl _, _ => rfl
  | _, _, _, .cons occurrence rest, second => by
      change OccurrencePath.cons (locatedOriginalOccurrence S permitted place key occurrence)
        (locatedOriginalPath S permitted place key (rest.append second)) = _
      rw [locatedOriginalPath_append rest second]
      rfl

def locatedProjection :
    OccurrenceCat (locatedPermitted S permitted place key).presentation ⥤
      OccurrenceCat S.presentation where
  obj := leftPart
  map := locatedOriginalPath S permitted place key
  map_id _ := rfl
  map_comp := locatedOriginalPath_append S permitted place key

theorem locatedOriginalPath_permitted {source target : Multiset (R ⊕ (Place × List Cell))}
    (path : OccurrencePath (locatedPermitted S permitted place key).presentation source target) :
    ∀ entry ∈ S.pathEntries (locatedOriginalPath S permitted place key path), permitted entry.2 := by
  rw [locatedOriginalPath_entries]
  exact locatedPermitted_entries_permitted S permitted place key path

theorem locatedOriginalPath_valuation {Value : Type uValue} [AddCommMonoid Value]
    (value : ∀ {site : S.Site}, S.Instance site → Value)
    {source target : Multiset (R ⊕ (Place × List Cell))}
    (path : OccurrencePath (locatedPermitted S permitted place key).presentation source target) :
    (S.instanceValuation value).onPath (locatedOriginalPath S permitted place key path) =
      ((locatedPermitted S permitted place key).instanceValuation
        fun paid => value paid.1.val).onPath path := by
  rw [S.instanceValuation_onPath, locatedOriginalPath_entries,
    (locatedPermitted S permitted place key).instanceValuation_onPath, List.map_map]
  rfl

theorem locatedOriginalPath_valuation_square {Value : Type uValue} [AddCommMonoid Value]
    (value : ∀ {site : S.Site}, S.Instance site → Value) :
    locatedProjection S permitted place key ⋙ (S.instanceValuation value).toFunctor =
      ((locatedPermitted S permitted place key).instanceValuation
        fun paid => value paid.1.val).toFunctor := by
  refine _root_.CategoryTheory.Functor.hext
    (F := locatedProjection S permitted place key ⋙ (S.instanceValuation value).toFunctor)
    (G := ((locatedPermitted S permitted place key).instanceValuation
      fun paid => value paid.1.val).toFunctor) (fun _ => rfl) ?_
  intro source target path
  exact heq_of_eq (locatedOriginalPath_valuation S permitted place key value path)

end Mettapedia.GSLT.Causality.ResourceInteraction
