import Mettapedia.TypeTheory.NaturalAlgebra
import Mettapedia.TypeTheory.RouteTransportDiscriminator

/-!
# Coherent transport over natural-number presentations

Successor-algebra isomorphisms form a route groupoid using the existing
transport-family interface. Its value action retains the selected comparison.
For faithful natural presentations, initiality proves that parallel structured
comparisons agree. Route independence is derived on this interface; it is not
imposed on arbitrary equivalences or on proof receipts.

An arbitrary natural-indexed family is transported together with its index.
The implementation factors through the initial natural algebra, and the index
theorem proves that this action agrees with the supplied structured route.
The semantic inverse need not be an executable decoder.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NaturalRepresentationInterface

open NaturalAlgebra ScopedIdentity IdentityRouteCapabilities RouteTransportDiscriminator

universe i u v

variable {Index : Type i} {Carrier : Index → Type u}

def identity {α : Type u} (A : Algebra α) : Iso A A where
  toEquiv := Equiv.refl _
  map_zero := rfl
  map_succ := fun _ => rfl

/-- Routes preserve the declared constructors, rather than just the carrier. -/
def layer (algebra : ∀ index, Algebra (Carrier index)) : Layer Index where
  Route source target := Iso (algebra source) (algebra target)
  refl index := identity (algebra index)
  Support source target := Nonempty (Iso (algebra source) (algebra target))
  forget route := ⟨route⟩

def groupoid (algebra : ∀ index, Algebra (Carrier index)) : RouteGroupoid (layer algebra) where
  comp := Iso.trans
  inv := Iso.symm
  refl_comp route := by apply Iso.ext; intro value; rfl
  comp_refl route := by apply Iso.ext; intro value; rfl
  assoc first second third := by apply Iso.ext; intro value; rfl
  inv_comp route := by
    apply Iso.ext
    exact route.toEquiv.apply_symm_apply
  comp_inv route := by
    apply Iso.ext
    exact route.toEquiv.symm_apply_apply

def values (algebra : ∀ index, Algebra (Carrier index)) :
    TransportFamily (layer algebra) (groupoid algebra) where
  Fibre := Carrier
  transport route := route.toEquiv
  transport_refl _ _ := rfl
  transport_comp _ _ _ := rfl

variable (algebra : ∀ index, Algebra (Carrier index))
  (representation : ∀ index, Representation (algebra index))

/-- This comparison is selected by universal recursion, not by choosing a
path in an implementation's conversion graph. -/
noncomputable def comparison (source target : Index) :
    Iso (algebra source) (algebra target) :=
  isoOfInitial (representation source).initial (representation target).initial
    (representation source).initial (representation target).initial

theorem comparison_unique {source target : Index}
    (route : Iso (algebra source) (algebra target)) :
    route = comparison algebra representation source target :=
  isoOfInitial_unique (representation source).initial (representation target).initial
    (representation source).initial (representation target).initial route

include representation in
theorem routes_unique {source target : Index}
    (first second : Iso (algebra source) (algebra target)) : first = second :=
  (comparison_unique algebra representation first).trans
    (comparison_unique algebra representation second).symm

include representation in
/-- Thinness is confined to the initial successor-algebra interface. -/
theorem structured_routeUIP : RouteUIP (layer algebra) :=
  fun _ _ => ⟨routes_unique algebra representation⟩

theorem comparison_refl (index : Index) :
    comparison algebra representation index index = identity (algebra index) :=
  (comparison_unique algebra representation _).symm

theorem comparison_trans (first middle last : Index) :
    (comparison algebra representation first middle).trans
      (comparison algebra representation middle last) =
    comparison algebra representation first last :=
  comparison_unique algebra representation _

include representation in
/-- Any lawful consumer of this structured groupoid is independent of the
chosen comparison route. This does not identify routes in other interfaces. -/
theorem transport_route_independent
    (family : TransportFamily.{i, u, v} (layer algebra) (groupoid algebra))
    {source target : Index} (first second : Iso (algebra source) (algebra target))
    (value : family.Fibre source) :
    family.transport first value = family.transport second value :=
  congrArg (fun route => family.transport route value)
    (routes_unique algebra representation first second)

theorem route_encode {source target : Index}
    (route : Iso (algebra source) (algebra target)) (number : Nat) :
    route.toEquiv ((representation source).encode number) =
      (representation target).encode number := by
  have same := (initialHom_unique nat_initial (algebra target)
    (Hom.comp route.toHom (representation source).encodeHom)).trans
    (initialHom_unique nat_initial (algebra target) (representation target).encodeHom).symm
  exact congrArg (fun f : Hom natAlgebra (algebra target) => f number) same

/-- Natural fibres reindexed by the canonical structured comparison. -/
abbrev Indexed (family : Nat → Type v) (index : Index) :=
  Σ value : Carrier index, family ((representation index).canonicalIso.toEquiv.symm value)

noncomputable def indexedEquiv (family : Nat → Type v) (index : Index) :
    (Σ number, family number) ≃ Indexed algebra representation family index :=
  Equiv.sigmaCongrLeft' (representation index).canonicalIso.toEquiv

noncomputable def indexedFamily (family : Nat → Type v) :
    TransportFamily (layer algebra) (groupoid algebra) where
  Fibre := Indexed algebra representation family
  transport {source target} _ value :=
    indexedEquiv algebra representation family target
      ((indexedEquiv algebra representation family source).symm value)
  transport_refl index value :=
    (indexedEquiv algebra representation family index).apply_symm_apply value
  transport_comp {source middle target} _ _ value := by
    change _ = indexedEquiv algebra representation family target
      ((indexedEquiv algebra representation family middle).symm
        (indexedEquiv algebra representation family middle _))
    rw [Equiv.symm_apply_apply]

theorem indexed_transport_index (family : Nat → Type v) {source target : Index}
    (route : Iso (algebra source) (algebra target))
    (value : Indexed algebra representation family source) :
    ((indexedFamily algebra representation family).transport route value).1 =
      route.toEquiv value.1 := by
  obtain ⟨⟨number, payload⟩, rfl⟩ :=
    (indexedEquiv algebra representation family source).surjective value
  change (indexedEquiv algebra representation family target
    ((indexedEquiv algebra representation family source).symm
      (indexedEquiv algebra representation family source ⟨number, payload⟩))).1 = _
  rw [Equiv.symm_apply_apply]
  change (representation target).canonicalIso.toEquiv number =
    route.toEquiv ((representation source).canonicalIso.toEquiv number)
  rw [Representation.canonicalIso_encode, Representation.canonicalIso_encode,
    route_encode]

/-- A dependent observation is evaluated on the retained natural index and
payload. Both survive transport together. -/
noncomputable def observe {Result : Type v} (family : Nat → Type v)
    (observation : (Σ number, family number) → Result) (index : Index)
    (value : Indexed algebra representation family index) : Result :=
  observation ((indexedEquiv algebra representation family index).symm value)

theorem observe_transport {Result : Type v} (family : Nat → Type v)
    (observation : (Σ number, family number) → Result) {source target : Index}
    (route : Iso (algebra source) (algebra target))
    (value : Indexed algebra representation family source) :
    observe algebra representation family observation target
      ((indexedFamily algebra representation family).transport route value) =
    observe algebra representation family observation source value := by
  unfold observe indexedFamily
  rw [Equiv.symm_apply_apply]

/-- A route-sensitive interface still exists outside the initial-algebra
contract; it cannot inherit the preceding route-independence theorem. -/
theorem arbitrary_equivalences_can_change_values :
    RouteTransportDiscriminator.Canary.booleanAutomorphismTransport.transport
      (source := ()) (target := ()) false false ≠
    RouteTransportDiscriminator.Canary.booleanAutomorphismTransport.transport
      (source := ()) (target := ()) true false := Bool.false_ne_true

end Mettapedia.TypeTheory.NaturalRepresentationInterface
