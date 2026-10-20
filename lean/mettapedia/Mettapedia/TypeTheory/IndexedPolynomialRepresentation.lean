import Mettapedia.TypeTheory.IndexedPolynomialInduction

/-!
# Structured representations of indexed inductive families

Algebra comparisons retain constructor shape, payload, recursive position and
result index. A representation is an algebra isomorphism from the polynomial
fixed family. Initiality makes every constructor-preserving comparison between
two such representations agree with the canonical change of representation.

These are semantic representation maps. Machine storage invariants, executable
decoding and an object theory's judgmental computation remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial

universe uB uI uS uP u v w uF

variable {Base : Type uB} {Index : Base → Type uI}
variable {P : IndexedPolynomial.{uB, uI, uS, uP} Base Index}
variable {X : ∀ b, Index b → Type u} {Y : ∀ b, Index b → Type v}
variable {Z : ∀ b, Index b → Type w}

namespace Algebra

namespace Hom

def identity (A : Algebra P X) : Hom A A where
  toFun := fun _ _ x => x
  commutes := by intro b i layer; rw [Extension.map_id]

def compose {A : Algebra P X} {B : Algebra P Y} {C : Algebra P Z}
    (g : Hom B C) (f : Hom A B) : Hom A C where
  toFun := fun b i x => g.toFun b i (f.toFun b i x)
  commutes := by
    intro b i layer
    rw [f.commutes, g.commutes]
    cases layer
    rfl

end Hom

/-- An equivalence in each fibre that preserves the specified constructors. -/
structure Iso (A : Algebra P X) (B : Algebra P Y) where
  toEquiv : ∀ b i, X b i ≃ Y b i
  commutes : ∀ b i (layer : P.Extension X b i),
    toEquiv b i (A.act b i layer) =
      B.act b i (Extension.map P (fun b i => toEquiv b i) layer)

namespace Iso

variable {A : Algebra P X} {B : Algebra P Y} {C : Algebra P Z}

def toHom (e : Iso A B) : Hom A B where
  toFun := fun b i => e.toEquiv b i
  commutes := e.commutes

def refl (A : Algebra P X) : Iso A A where
  toEquiv := fun _ _ => Equiv.refl _
  commutes := by intro b i layer; cases layer; rfl

def trans (e : Iso A B) (f : Iso B C) : Iso A C where
  toEquiv := fun b i => (e.toEquiv b i).trans (f.toEquiv b i)
  commutes := (Hom.compose f.toHom e.toHom).commutes

def symm (e : Iso A B) : Iso B A where
  toEquiv := fun b i => (e.toEquiv b i).symm
  commutes := by
    intro b i layer
    apply (e.toEquiv b i).injective
    rw [Equiv.apply_symm_apply, e.commutes]
    congr 1
    cases layer with
    | mk shape children =>
      change (⟨shape, children⟩ : P.Extension Y b i) =
        ⟨shape, fun pos => e.toEquiv b _ ((e.toEquiv b _).symm (children pos))⟩
      simp only [Equiv.apply_symm_apply]

end Iso

namespace Displayed

private theorem transport_section {α : Sort u} (E : α → Sort v)
    (chosen : ∀ x, E x) {x y : α} (h : x = y) :
    h ▸ chosen x = chosen y := by cases h; rfl

private theorem transport_reindexed {α : Sort u} {β : Sort v}
    (E : β → Sort w) (f : α → β) (chosen : ∀ x, E (f x))
    {x y : α} (h : x = y) :
    congrArg f h ▸ chosen x = chosen y := by cases h; rfl

private theorem transport_cancel {α : Sort u} (E : α → Sort v)
    {x y : α} (h : x = y) (value : E y) :
    h ▸ h.symm ▸ value = value := by cases h; rfl

variable {A : Algebra P X} {B : Algebra P Y}
variable {E : ∀ b i, Y b i → Sort uF}

/-- Pull dependent constructor methods back along an algebra homomorphism. -/
def pullback (D : Displayed B E) (f : Hom A B) :
    Displayed A (fun b i x => E b i (f.toFun b i x)) where
  act := fun b i shape children hypotheses =>
    (f.commutes b i ⟨shape, children⟩).symm ▸
      D.act b i shape (fun pos => f.toFun b _ (children pos)) hypotheses

/-- A target section restricts along any constructor-preserving map. -/
def Section.pullback {D : Displayed B E} (chosen : D.Section) (f : Hom A B) :
    (D.pullback f).Section where
  toFun := fun b i x => chosen.toFun b i (f.toFun b i x)
  commutes := by
    intro b i shape children
    have transported := transport_section (E b i) (chosen.toFun b i)
      (f.commutes b i ⟨shape, children⟩).symm
    simp only [Extension.map] at transported
    rw [chosen.commutes] at transported
    exact transported.symm

/-- Transport the entire dependent value, including its index in the motive. -/
def transportedValues (D : Displayed B E) (e : Iso A B)
    (chosen : (D.pullback e.toHom).Section) : ∀ b i y, E b i y :=
  fun b i y => (e.toEquiv b i).apply_symm_apply y ▸
    chosen.toFun b i ((e.toEquiv b i).symm y)

@[simp] theorem transportedValues_encode (D : Displayed B E) (e : Iso A B)
    (chosen : (D.pullback e.toHom).Section) (b : Base) (i : Index b) (x : X b i) :
    transportedValues D e chosen b i (e.toEquiv b i x) = chosen.toFun b i x := by
  exact transport_reindexed (E b i) (e.toEquiv b i) (chosen.toFun b i)
    ((e.toEquiv b i).symm_apply_apply x)

/-- An algebra equivalence transports dependent elimination and its computation
laws. Equality transports remain internal to this semantic construction. -/
def transport (D : Displayed B E) (e : Iso A B)
    (chosen : (D.pullback e.toHom).Section) : D.Section where
  toFun := transportedValues D e chosen
  commutes := by
    intro b i shape children
    obtain ⟨children, rfl⟩ : ∃ original : ∀ pos, X b (P.next shape pos),
        (fun pos => e.toEquiv b _ (original pos)) = children :=
      ⟨fun pos => (e.toEquiv b _).symm (children pos),
        funext fun pos => (e.toEquiv b _).apply_symm_apply (children pos)⟩
    have transported := transport_section (E b i) (transportedValues D e chosen b i)
      (e.commutes b i ⟨shape, children⟩)
    rw [transportedValues_encode, chosen.commutes] at transported
    change (e.commutes b i ⟨shape, children⟩) ▸
      (e.commutes b i ⟨shape, children⟩).symm ▸
        D.act b i shape (fun pos => e.toEquiv b _ (children pos))
          (fun pos => chosen.toFun b _ (children pos)) = _ at transported
    have clean := (transport_cancel (E b i) (e.commutes b i ⟨shape, children⟩)
      (D.act b i shape (fun pos => e.toEquiv b _ (children pos))
        (fun pos => chosen.toFun b _ (children pos)))).symm.trans transported
    refine clean.symm.trans ?_
    exact congrArg (D.act b i shape (fun pos => e.toEquiv b _ (children pos)))
      (funext fun pos => (transportedValues_encode D e chosen b _ (children pos)).symm)

end Displayed

/-- A semantic realization of the complete indexed inductive family. -/
abbrev Representation (P : IndexedPolynomial Base Index)
    {X : ∀ b, Index b → Type u} (A : Algebra P X) := Iso (initial P) A

namespace Representation

variable {A : Algebra P X} {B : Algebra P Y} {C : Algebra P Z}

/-- Every structured representation inherits dependent elimination, with no
additional eliminator supplied by the representation provider. -/
noncomputable def induction (a : Representation P A)
    {E : ∀ b i, X b i → Sort uF} (D : Displayed A E) : D.Section :=
  D.transport a (D.pullback a.toHom).initialSection

@[simp] theorem induction_encode (a : Representation P A)
    {E : ∀ b i, X b i → Sort uF} (D : Displayed A E)
    (b : Base) (i : Index b) (tree : Fix P b i) :
    (a.induction D).toFun b i (a.toEquiv b i tree) =
      (D.pullback a.toHom).initialSection.toFun b i tree :=
  Displayed.transportedValues_encode D a _ b i tree

/-- The inherited dependent eliminator is determined by the constructor laws. -/
theorem induction_unique (a : Representation P A)
    {E : ∀ b i, X b i → Sort uF} (D : Displayed A E) (other : D.Section)
    (b : Base) (i : Index b) (value : X b i) :
    other.toFun b i value = (a.induction D).toFun b i value := by
  obtain ⟨tree, rfl⟩ := (a.toEquiv b i).surjective value
  rw [induction_encode]
  exact (D.pullback a.toHom).initialSection_unique (other.pullback a.toHom) b i tree

/-- Dependent programs commute with every structured representation route.
The pullback includes the constructor equations needed to transport motives. -/
theorem induction_route (a : Representation P A) (b : Representation P B)
    (route : Hom A B) {E : ∀ base index, Y base index → Sort uF}
    (D : Displayed B E) (base : Base) (index : Index base) (value : X base index) :
    (a.induction (D.pullback route)).toFun base index value =
      (b.induction D).toFun base index (route.toFun base index value) :=
  (induction_unique a (D.pullback route) ((b.induction D).pullback route)
    base index value).symm

/-- Initiality, rather than an arbitrary chosen bijection, determines every
constructor-preserving route on represented values. -/
theorem route_unique (a : Representation P A) (b : Representation P B)
    (route : Hom A B) (base : Base) (index : Index base)
    (tree : Fix P base index) :
    route.toFun base index (a.toEquiv base index tree) =
      b.toEquiv base index tree :=
  (hom_eq_fold B (Hom.compose route a.toHom) base index tree).trans
    (hom_eq_fold B b.toHom base index tree).symm

def change (a : Representation P A) (b : Representation P B) : Iso A B :=
  a.symm.trans b

@[simp] theorem change_encode (a : Representation P A) (b : Representation P B)
    (base : Base) (index : Index base) (tree : Fix P base index) :
    (change a b).toEquiv base index (a.toEquiv base index tree) =
      b.toEquiv base index tree := by
  exact congrArg (b.toEquiv base index) ((a.toEquiv base index).symm_apply_apply tree)

theorem route_eq_change (a : Representation P A) (b : Representation P B)
    (route : Hom A B) (base : Base) (index : Index base) (value : X base index) :
    route.toFun base index value = (change a b).toEquiv base index value := by
  obtain ⟨tree, rfl⟩ := (a.toEquiv base index).surjective value
  rw [change_encode]
  exact route_unique a b route base index tree

@[simp] theorem change_identity (a : Representation P A)
    (base : Base) (index : Index base) (value : X base index) :
    (change a a).toEquiv base index value = value :=
  (a.toEquiv base index).apply_symm_apply value

@[simp] theorem change_composition
    (a : Representation P A) (b : Representation P B) (c : Representation P C)
    (base : Base) (index : Index base) (value : X base index) :
    (change b c).toEquiv base index ((change a b).toEquiv base index value) =
      (change a c).toEquiv base index value := by
  change c.toEquiv base index ((b.toEquiv base index).symm
    (b.toEquiv base index ((a.toEquiv base index).symm value))) = _
  rw [Equiv.symm_apply_apply]
  rfl

end Representation
end Algebra
end Mettapedia.TypeTheory.IndexedPolynomial
