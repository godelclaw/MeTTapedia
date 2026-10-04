import MettapediaFourColor.StripListTransport
import Mettapedia.GraphTheory.Kempe.BoundaryEndpointTransport

/-!
# One endpoint colour suffices for the two strip updates

Every source vertex adjacent to port six sees a proper boundary arc of
length two or three, with port six at an endpoint. Its original allowed
list and the old endpoint colour therefore determine the new list. This
law quantifies over arbitrary proper boundaries and replacement colours
on both decoded sources; it stores no boundary assignment table.
-/

namespace FourColor.StripEndpointTransport

open SimpleGraph Color StripListTransport

def change (s : Bool) (new : Color) (b : Boundary s) (i : Fin (ring s)) : Color :=
  if i.val = 6 then new else b i

def forbidden (s : Bool) (b : Boundary s) (v : Fin (TriangleStripAnchors.size (source s))) :=
  (ports s v).image b

/-- The source geometry, the old endpoint colour, and the old forbidden
sets suffice. No other boundary colour is consulted by this operation. -/
def predict (s : Bool) (old new : Color)
    (F : Fin (TriangleStripAnchors.size (source s)) → Finset Color)
    (v : Fin (TriangleStripAnchors.size (source s))) : Finset Color :=
  if (⟨6,by cases s <;> decide⟩ : Fin (ring s)) ∈ ports s v then
    BoundaryEndpointTransport.change (decide ((ports s v).card = 3)) old new (F v)
  else F v

theorem arc_proper (s : Bool) (b : Boundary s) (h : Proper s b) :
    b 4 ≠ b 5 ∧ b 5 ≠ b 6 ∧ b 6 ≠ b 7 ∧ b 7 ≠ b 8 := by
  cases s <;> exact ⟨h 4 5 (by decide), h 5 6 (by decide),
    h 6 7 (by decide), h 7 8 (by decide)⟩

theorem forbidden_change (s : Bool) (b : Boundary s) (new : Color)
    (h : Proper s b) :
    forbidden s (change s new b) = predict s (b 6) new (forbidden s b) := by
  obtain ⟨h45,h56,h67,h78⟩ := arc_proper s b h
  funext v
  cases s <;> fin_cases v <;> try rfl
  · change Finset.image (change false new b) {4,5,6} =
      BoundaryEndpointTransport.change true (b 6) new (Finset.image b {4,5,6})
    simp only [Finset.image_insert, Finset.image_singleton]
    change {b 4,b 5,new} = BoundaryEndpointTransport.change true (b 6) new {b 4,b 5,b 6}
    exact (BoundaryEndpointTransport.three (b 4) (b 5) (b 6) new h45 h56).symm
  · change Finset.image (change false new b) {6,7} =
      BoundaryEndpointTransport.change false (b 6) new (Finset.image b {6,7})
    simp only [Finset.image_insert, Finset.image_singleton]
    change {new,b 7} = BoundaryEndpointTransport.change false (b 6) new {b 6,b 7}
    have pair (a c : Color) : ({a,c} : Finset Color) = {c,a} := by
      ext z; simp [or_comm]
    rw [pair new (b 7), pair (b 6) (b 7)]
    exact (BoundaryEndpointTransport.two (b 7) (b 6) new h67.symm).symm
  · change Finset.image (change true new b) {6,7,8} =
      BoundaryEndpointTransport.change true (b 6) new (Finset.image b {6,7,8})
    simp only [Finset.image_insert, Finset.image_singleton]
    change {new,b 7,b 8} = BoundaryEndpointTransport.change true (b 6) new {b 6,b 7,b 8}
    have reverse (a c d : Color) : ({a,c,d} : Finset Color) = {d,c,a} := by
      ext z; simp [or_comm, or_left_comm, or_assoc]
    rw [reverse new (b 7) (b 8), reverse (b 6) (b 7) (b 8)]
    exact (BoundaryEndpointTransport.three (b 8) (b 7) (b 6) new h78.symm h67.symm).symm
  · change Finset.image (change true new b) {4,5,6} =
      BoundaryEndpointTransport.change true (b 6) new (Finset.image b {4,5,6})
    simp only [Finset.image_insert, Finset.image_singleton]
    change {b 4,b 5,new} = BoundaryEndpointTransport.change true (b 6) new {b 4,b 5,b 6}
    exact (BoundaryEndpointTransport.three (b 4) (b 5) (b 6) new h45 h56).symm

theorem lists_complement (s : Bool) (b : Boundary s) (v) :
    lists s b v = Finset.univ \ forbidden s b v := by
  ext a
  simp [lists, BoundaryListTransport.allowed, forbidden, ne_comm]

/-- A compact update on the complete old list assignment. -/
def advance (s : Bool) (old new : Color) (L : Lists s) : Lists s :=
  fun v => Finset.univ \ predict s old new (fun u => Finset.univ \ L u) v

theorem lists_change (s : Bool) (b : Boundary s) (new : Color) (h : Proper s b) :
    lists s (change s new b) = advance s (b 6) new (lists s b) := by
  have restore : (fun v => Finset.univ \ lists s b v) = forbidden s b := by
    funext v
    rw [lists_complement]
    simp
  funext v
  rw [lists_complement, forbidden_change s b new h]
  simp only [advance, restore]

/-- Retaining just the endpoint colour repairs the list-only congruence
for these operations on arbitrary proper source boundaries. -/
theorem congruence (s : Bool) (b c : Boundary s) (new : Color)
    (hb : Proper s b) (hc : Proper s c) (same : lists s b = lists s c)
    (endpoint : b 6 = c 6) :
    lists s (change s new b) = lists s (change s new c) := by
  rw [lists_change s b new hb, lists_change s c new hc, same, endpoint]

/-- A successful guard on the compact updated lists reconstructs all source
vertices and preserves the updated ordered boundary. -/
theorem guard_full_change (s : Bool) (b : Boundary s) (new : Color)
    (before : Proper s b) (after : Proper s (change s new b))
    (choice : Fin 2 → Color) (n : ℕ)
    (guard : TriangleStripLists.Guard (source s) (advance s (b 6) new (lists s b))
      choice n) : Full s (change s new b) := by
  apply (full_iff s _ after).mpr
  obtain ⟨C,fit,_⟩ := TriangleStripLists.guard_colouring (source s) _ choice n guard
  refine ⟨C,?_⟩
  rw [lists_change s b new before]
  exact fit

end FourColor.StripEndpointTransport
