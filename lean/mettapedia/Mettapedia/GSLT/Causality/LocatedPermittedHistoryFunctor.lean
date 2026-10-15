import Mettapedia.GSLT.Causality.LocatedPermittedProjection

/-!
# Located funding on the category of complete history receipts

The original receipt is computed from the supplied paid path, including
all intermediate resource markings and original instances. Continuing a
paid receipt projects to continuing its original receipt. This gives an
actual functor between the existing categories of history elements, with
a commuting square over their actual occurrence categories.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open _root_.CategoryTheory OccurrenceHistory

universe uRes uRule

variable {R : Type uRes} {Place Cell : Type uRule}
  (S : System.{uRes, uRule} R)
  (permitted : ∀ {site : S.Site}, S.Instance site → Prop)
  (place : ∀ {site : S.Site}, S.Instance site → Place)
  (key : ∀ {site : S.Site}, S.Instance site → Cell)
  [DecidableEq R] [DecidableEq Place] [DecidableEq Cell]

local instance paidHistoryCategory (root : Multiset (R ⊕ (Place × List Cell))) :
    Category.{max uRes uRule}
      (Element (locatedPermitted S permitted place key).presentation root) :=
  Element.instCategory
    (P := (locatedPermitted S permitted place key).presentation) (root := root)

local instance originalHistoryCategory (root : Multiset R) :
    Category.{max uRes uRule} (Element S.presentation root) :=
  Element.instCategory (P := S.presentation) (root := root)

def locatedHistoryReceipt {root : Multiset (R ⊕ (Place × List Cell))}
    (receipt : Element (locatedPermitted S permitted place key).presentation root) :
    Element S.presentation (leftPart root) where
  target := leftPart receipt.target
  path := locatedOriginalPath S permitted place key receipt.path

def locatedHistoryContinuation {root : Multiset (R ⊕ (Place × List Cell))}
    {first second : Element (locatedPermitted S permitted place key).presentation root}
    (continuation : Element.Hom first second) :
    Element.Hom (locatedHistoryReceipt S permitted place key first)
      (locatedHistoryReceipt S permitted place key second) where
  rest := locatedOriginalPath S permitted place key continuation.rest
  factor :=
    (locatedOriginalPath_append S permitted place key first.path continuation.rest).symm.trans
      (congrArg (locatedOriginalPath S permitted place key) continuation.factor)

def locatedHistoryProjection (root : Multiset (R ⊕ (Place × List Cell))) :
    Element (locatedPermitted S permitted place key).presentation root ⥤
      Element S.presentation (leftPart root) where
  obj := locatedHistoryReceipt S permitted place key
  map := locatedHistoryContinuation S permitted place key
  map_id receipt := by
    apply Element.Hom.ext
    rfl
  map_comp first second := by
    apply Element.Hom.ext
    exact locatedOriginalPath_append S permitted place key first.rest second.rest

theorem locatedHistoryProjection_forget (root : Multiset (R ⊕ (Place × List Cell))) :
    locatedHistoryProjection S permitted place key root ⋙ Element.forgetFunctor =
      Element.forgetFunctor ⋙ locatedProjection S permitted place key := by
  refine _root_.CategoryTheory.Functor.hext
    (F := locatedHistoryProjection S permitted place key root ⋙ Element.forgetFunctor)
    (G := Element.forgetFunctor ⋙ locatedProjection S permitted place key) (fun _ => rfl) ?_
  intro source target continuation
  rfl

theorem locatedHistoryReceipt_extend {root target : Multiset (R ⊕ (Place × List Cell))}
    (receipt : Element (locatedPermitted S permitted place key).presentation root)
    (occurrence : Occurrence (locatedPermitted S permitted place key).presentation
      receipt.target target) :
    locatedHistoryReceipt S permitted place key (receipt.extend occurrence) =
      (locatedHistoryReceipt S permitted place key receipt).extend
      (locatedOriginalOccurrence S permitted place key occurrence) := by
  change Element.mk (P := S.presentation) (root := leftPart root) (leftPart target)
    (locatedOriginalPath S permitted place key
      (receipt.path.append (.cons occurrence
        (OccurrencePath.refl (P := (locatedPermitted S permitted place key).presentation) target)))) = _
  exact congrArg (Element.mk (P := S.presentation) (root := leftPart root) (leftPart target))
    (locatedOriginalPath_append S permitted place key receipt.path
      (.cons occurrence (OccurrencePath.refl
        (P := (locatedPermitted S permitted place key).presentation) target)))

theorem locatedHistoryReceipt_entries {root : Multiset (R ⊕ (Place × List Cell))}
    (receipt : Element (locatedPermitted S permitted place key).presentation root) :
    S.pathEntries (locatedHistoryReceipt S permitted place key receipt).path =
      ((locatedPermitted S permitted place key).pathEntries receipt.path).map
        (locatedOriginalEntry S permitted place key) :=
  locatedOriginalPath_entries S permitted place key receipt.path

end Mettapedia.GSLT.Causality.ResourceInteraction
