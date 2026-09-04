import Mettapedia.Combinatorics.Matching.Pairing

/-!
# Edge-labelled perfect matchings

A `Pairing` presents an undirected perfect matching by naming the partner of
each vertex.  Data attached to a matching edge can therefore be represented by
a vertex labelling which is constant on partners.  `LabeledPairing` packages
exactly this invariant.

The construction is graph-free.  It supports change of labels and transport
across an equivalence of vertex types, so graph-backed applications can keep
their computational coordinates separate from their mathematical carrier.
-/

namespace MatchingParity

universe u v w

/-- A perfect matching together with one label for each undirected matching
edge.  The field `label_partner` says that the two endpoint presentations of an
edge carry the same label. -/
structure LabeledPairing (V : Type u) (A : Type v) extends Pairing V where
  label : V → A
  label_partner : ∀ vertex, label (toPairing.partner vertex) = label vertex

namespace LabeledPairing

variable {V : Type u} {W : Type w} {A : Type v}

@[simp]
theorem label_partner_apply (pairing : LabeledPairing V A) (vertex : V) :
    pairing.label (pairing.toPairing.partner vertex) = pairing.label vertex :=
  pairing.label_partner vertex

/-- Apply a function to every edge label. -/
def mapLabel {B : Type*} (f : A → B) (pairing : LabeledPairing V A) :
    LabeledPairing V B where
  toPairing := pairing.toPairing
  label vertex := f (pairing.label vertex)
  label_partner vertex := by rw [pairing.label_partner]

@[simp]
theorem mapLabel_toPairing {B : Type*} (f : A → B)
    (pairing : LabeledPairing V A) :
    (pairing.mapLabel f).toPairing = pairing.toPairing :=
  rfl

@[simp]
theorem mapLabel_label {B : Type*} (f : A → B)
    (pairing : LabeledPairing V A) (vertex : V) :
    (pairing.mapLabel f).label vertex = f (pairing.label vertex) :=
  rfl

/-- Transport an edge-labelled matching through an equivalence of its vertex
carrier. -/
def reindex (coordinate : W ≃ V) (pairing : LabeledPairing V A) :
    LabeledPairing W A where
  toPairing :=
    { partner := fun point =>
        coordinate.symm (pairing.toPairing.partner (coordinate point))
      partner_partner := by
        intro point
        apply coordinate.injective
        simp only [Equiv.apply_symm_apply]
        exact pairing.partner_partner (coordinate point)
      partner_ne := by
        intro point hfixed
        apply pairing.toPairing.partner_ne (coordinate point)
        have := congrArg coordinate hfixed
        simpa using this }
  label point := pairing.label (coordinate point)
  label_partner point := by
    simp only [Equiv.apply_symm_apply]
    exact pairing.label_partner (coordinate point)

@[simp]
theorem reindex_partner (coordinate : W ≃ V)
    (pairing : LabeledPairing V A) (point : W) :
    (pairing.reindex coordinate).toPairing.partner point =
      coordinate.symm (pairing.toPairing.partner (coordinate point)) :=
  by simp [reindex]

@[simp]
theorem reindex_label (coordinate : W ≃ V)
    (pairing : LabeledPairing V A) (point : W) :
    (pairing.reindex coordinate).label point = pairing.label (coordinate point) :=
  by simp [reindex]

/-- A parity-labelled perfect matching. -/
abbrev ParityPairing (V : Type u) := LabeledPairing V (ZMod 2)

end LabeledPairing

end MatchingParity
