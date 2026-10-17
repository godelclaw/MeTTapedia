import Mettapedia.GSLT.Contracts.AuthorityControls
import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Fin.Basic

/-!
# Authority indexed by worlds

Worlds form a category: an arrow is a change of world (an execution step, a
capture, a translation to another representation).  **Indexed authority**
(`IndexedAuthority`) assigns a separation algebra of authority to every world
and a resource homomorphism to every arrow, functorially, such that every
transport preserves frame-preserving updates.

## The total category is an opfibration

A point of the total category (`Point`) is a world with authority at it.  An
arrow from `(w, a)` to `(w', b)` is a change of world `f` such that the
transported authority updates to `b` without breaking any frame.  The total
category is thin over each arrow of worlds, and composition needs exactly that
transports preserve updates.

* Every change of world has a **strongly co-Cartesian lift** in the sense of
  Mathlib's fibred categories (`pushArrow_isStronglyCocartesian`): carry the
  authority along and do nothing else.  So the projection to worlds is an
  opfibration whose fibres are the update orders of separation algebras: a
  fibred family of resource theories.
* **Cartesian lifts are weakest authority before a change.**  Along one arrow
  every point has one exactly when transport along the arrow has a right
  adjoint for updates (`forall_weakestBefore_iff_rightAdjoint`), and such a lift
  is Cartesian in Mathlib's sense (`isCartesian_of_rightAdjoint`).  When every
  transport has a right adjoint, the projection is a pre-fibration
  (`isPreFibered_of_rightAdjoints`); identity transports have one
  (`stillWorlds_isPreFibered`).
* **Revocation has no Cartesian lift.**  Over two worlds where the second
  revokes all access (`revocationWorlds`), no authority before the change
  updates to the consume right after it (`no_arrow_into_consume`), so the
  projection is not a pre-fibration (`revocationWorlds_not_isPreFibered`).
  Forward transport along a revocation is lawful; what fails is pulling
  exclusive authority back across it.

## Transport keeps the read/consume distinction

Along every change of world, self-separate authority (a duplicable read right)
never becomes exclusive (`transport_not_exclusive_of_selfSeparate`), and shared
authority stays shared when the transport erases nothing
(`transport_shared`).

## Plain indexed records

A plain record of labels indexed by worlds proves none of this.

* `upgradeRelabel` is functorial (`upgradeRelabel_comp`), so its labels form an
  ordinary indexed family, yet it relabels a read capability as consume along
  the crossing (`upgradeRelabel_read`), which no transport of authority does.
* `staleRelabel`, a relabelling cached per arrow, violates the reindexing law
  (`staleRelabel_not_functorial`): it is not even a functor of worlds.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts

open CategoryTheory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.SeparationTransport
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u v w

/-- **Authority indexed by worlds.** -/
structure IndexedAuthority (W : Type u) [Category.{v} W] where
  /-- The authority available at each world. -/
  Fibre : W → Type w
  [zero : ∀ x, Zero (Fibre x)]
  [add : ∀ x, Add (Fibre x)]
  [sep : ∀ x, SepAlgebra (Fibre x)]
  /-- Authority carried along a change of world. -/
  transport : ∀ {x y : W}, (x ⟶ y) → Hom (Fibre x) (Fibre y)
  transport_id : ∀ (x : W) (a : Fibre x), transport (𝟙 x) a = a
  transport_comp : ∀ {x y z : W} (f : x ⟶ y) (g : y ⟶ z) (a : Fibre x),
    transport (f ≫ g) a = transport g (transport f a)
  /-- Transport is monotone for frame-preserving updates. -/
  preservesUpdates : ∀ {x y : W} (f : x ⟶ y), PreservesUpdates (transport f)

attribute [instance] IndexedAuthority.zero IndexedAuthority.add IndexedAuthority.sep

namespace IndexedAuthority

variable {W : Type u} [Category.{v} W] (A : IndexedAuthority.{u, v, w} W)

/-- **Duplicable read authority never becomes exclusive along a change of
world.** -/
theorem transport_not_exclusive_of_selfSeparate {x y : W} (f : x ⟶ y) {a : A.Fibre x}
    (self : a ## a) : ¬ Exclusive (A.transport f a) :=
  not_exclusive_map_of_selfSeparate (A.transport f) self

/-- Shared authority stays shared along a change of world that erases nothing. -/
theorem transport_shared {x y : W} (f : x ⟶ y) (reflects : (A.transport f).ReflectsZero)
    {a : A.Fibre x} (shared : Shared a) : Shared (A.transport f a) :=
  shared_map (A.transport f) reflects shared

/-! ## The total category -/

/-- A world with authority at it. -/
@[ext]
structure Point where
  world : W
  authority : A.Fibre world

variable {A}

instance totalCategory : Category.{v} (Point A) where
  Hom x y := {f : x.world ⟶ y.world // FrameUpdate (A.transport f x.authority) y.authority}
  id x := ⟨𝟙 x.world, by rw [A.transport_id]; exact FrameUpdate.refl _⟩
  comp φ ψ := ⟨φ.1 ≫ ψ.1, by
    rw [A.transport_comp]
    exact (A.preservesUpdates ψ.1 _ _ φ.2).trans ψ.2⟩
  id_comp φ := Subtype.ext (Category.id_comp φ.1)
  comp_id φ := Subtype.ext (Category.comp_id φ.1)
  assoc φ ψ χ := Subtype.ext (Category.assoc φ.1 ψ.1 χ.1)

@[simp] theorem id_val (x : Point A) : (𝟙 x : x ⟶ x).1 = 𝟙 x.world := rfl

@[simp] theorem comp_val {x y z : Point A} (φ : x ⟶ y) (ψ : y ⟶ z) :
    (φ ≫ ψ).1 = φ.1 ≫ ψ.1 := rfl

theorem hom_ext {x y : Point A} {φ ψ : x ⟶ y} (same : φ.1 = ψ.1) : φ = ψ := Subtype.ext same

/-- An arrow of the total category from a change of world and an update. -/
def homOf {x y : Point A} (f : x.world ⟶ y.world)
    (update : FrameUpdate (A.transport f x.authority) y.authority) : x ⟶ y :=
  ⟨f, update⟩

@[simp] theorem homOf_val {x y : Point A} (f : x.world ⟶ y.world)
    (update : FrameUpdate (A.transport f x.authority) y.authority) : (homOf f update).1 = f :=
  rfl

variable (A)

/-- The projection from the total category to worlds. -/
abbrev projection : Point A ⥤ W where
  obj := Point.world
  map φ := φ.1

variable {A}

/-! ## Pushing authority forward -/

/-- Carry the authority of a point along a change of world. -/
abbrev push (x : Point A) {y : W} (f : x.world ⟶ y) : Point A :=
  ⟨y, A.transport f x.authority⟩

/-- The arrow that carries authority and does nothing else. -/
def pushArrow (x : Point A) {y : W} (f : x.world ⟶ y) : x ⟶ push x f :=
  ⟨f, FrameUpdate.refl _⟩

instance pushArrow_isHomLift (x : Point A) {y : W} (f : x.world ⟶ y) :
    (projection A).IsHomLift f (pushArrow x f) :=
  IsHomLift.map (projection A) (pushArrow x f)

/-- **Every change of world has a strongly co-Cartesian lift.** -/
theorem pushArrow_isStronglyCocartesian (x : Point A) {y : W} (f : x.world ⟶ y) :
    (projection A).IsStronglyCocartesian f (pushArrow x f) where
  universal_property' := by
    intro target g φ' _
    have base : f ≫ g = φ'.1 :=
      IsHomLift.eq_of_isHomLift (projection A) (a := x) (b := target) (f ≫ g) φ'
    have carried : A.transport φ'.1 x.authority = A.transport g (A.transport f x.authority) := by
      rw [← base]
      exact A.transport_comp f g x.authority
    have update : FrameUpdate (A.transport g (A.transport f x.authority)) target.authority :=
      carried ▸ φ'.2
    refine ⟨homOf (x := push x f) (y := target) g update, ⟨?_, hom_ext base⟩, ?_⟩
    · exact IsHomLift.map (projection A) (homOf (x := push x f) (y := target) g update)
    · rintro χ ⟨_, -⟩
      exact hom_ext
        (IsHomLift.eq_of_isHomLift (projection A) (a := push x f) (b := target) g χ).symm

/-! ## Pulling authority back -/

variable (A) in
/-- `a` is the **weakest authority before** `f` that updates to `b` after it. -/
def WeakestBefore {x y : W} (f : x ⟶ y) (b : A.Fibre y) (a : A.Fibre x) : Prop :=
  FrameUpdate (A.transport f a) b ∧ ∀ a', FrameUpdate (A.transport f a') b → FrameUpdate a' a

variable (A) in
/-- A right adjoint to transport for frame-preserving updates. -/
def RightAdjoint {x y : W} (f : x ⟶ y) (back : A.Fibre y → A.Fibre x) : Prop :=
  ∀ a b, FrameUpdate (A.transport f a) b ↔ FrameUpdate a (back b)

/-- **Weakest authority exists for every target exactly when transport has a
right adjoint.** -/
theorem forall_weakestBefore_iff_rightAdjoint (A : IndexedAuthority.{u, v, w} W) {x y : W}
    (f : x ⟶ y) : (∀ b, ∃ a, WeakestBefore A f b a) ↔ ∃ back, RightAdjoint A f back := by
  constructor
  · intro weakest
    choose back holds using weakest
    refine ⟨back, fun a b => ⟨fun update => (holds b).2 a update, fun update => ?_⟩⟩
    exact (A.preservesUpdates f _ _ update).trans (holds b).1
  · rintro ⟨back, adjoint⟩ b
    exact ⟨back b, (adjoint _ b).mpr (FrameUpdate.refl _), fun a' update => (adjoint a' b).mp update⟩

/-- **A right adjoint gives a Cartesian lift** in Mathlib's sense. -/
theorem isCartesian_of_rightAdjoint {x y : W} (f : x ⟶ y) {back : A.Fibre y → A.Fibre x}
    (adjoint : RightAdjoint A f back) (b : A.Fibre y) :
    (projection A).IsCartesian f
      (⟨f, (adjoint (back b) b).mpr (FrameUpdate.refl _)⟩ :
        (⟨x, back b⟩ : Point A) ⟶ ⟨y, b⟩) where
  toIsHomLift := IsHomLift.map (projection A)
    (homOf (x := ⟨x, back b⟩) (y := ⟨y, b⟩) f ((adjoint (back b) b).mpr (FrameUpdate.refl _)))
  universal_property := by
    rintro ⟨sourceWorld, sourceAuthority⟩ φ' _
    have sameWorld : sourceWorld = x := IsHomLift.domain_eq (projection A) f φ'
    subst sameWorld
    have base : f = φ'.1 :=
      IsHomLift.eq_of_isHomLift (projection A) (a := ⟨sourceWorld, sourceAuthority⟩)
        (b := ⟨y, b⟩) f φ'
    have update : FrameUpdate (A.transport (𝟙 sourceWorld) sourceAuthority) (back b) := by
      rw [A.transport_id]
      have given : FrameUpdate (A.transport φ'.1 sourceAuthority) b := φ'.2
      rw [← base] at given
      exact (adjoint sourceAuthority b).mp given
    refine ⟨homOf (x := ⟨sourceWorld, sourceAuthority⟩) (y := ⟨sourceWorld, back b⟩)
      (𝟙 sourceWorld) update, ⟨?_, hom_ext (by simp [base])⟩, ?_⟩
    · exact IsHomLift.map (projection A)
        (homOf (x := ⟨sourceWorld, sourceAuthority⟩) (y := ⟨sourceWorld, back b⟩)
          (𝟙 sourceWorld) update)
    · rintro χ ⟨_, -⟩
      exact hom_ext (IsHomLift.eq_of_isHomLift (projection A)
        (a := ⟨sourceWorld, sourceAuthority⟩) (b := ⟨sourceWorld, back b⟩)
        (𝟙 sourceWorld) χ).symm

/-- When every transport has a right adjoint, the projection is a
pre-fibration. -/
theorem isPreFibered_of_rightAdjoints
    (adjoints : ∀ {x y : W} (f : x ⟶ y), ∃ back, RightAdjoint A f back) :
    (projection A).IsPreFibered where
  exists_isCartesian' := by
    rintro ⟨y, b⟩ x f
    obtain ⟨back, adjoint⟩ := adjoints f
    exact ⟨_, _, isCartesian_of_rightAdjoint f adjoint b⟩

end IndexedAuthority

/-! ## Constant authority with chosen transports -/

namespace IndexedAuthority

variable {W : Type u} [Category.{v} W]

/-- One separation algebra at every world, with a functorial choice of
update-preserving transports. -/
def ofConstant (α : Type w) [Zero α] [Add α] [SepAlgebra α]
    (transport : ∀ {x y : W}, (x ⟶ y) → Hom α α)
    (transport_id : ∀ (x : W) (a : α), transport (𝟙 x) a = a)
    (transport_comp : ∀ {x y z : W} (f : x ⟶ y) (g : y ⟶ z) (a : α),
      transport (f ≫ g) a = transport g (transport f a))
    (preservesUpdates : ∀ {x y : W} (f : x ⟶ y), PreservesUpdates (transport f)) :
    IndexedAuthority.{u, v, w} W where
  Fibre _ := α
  transport := transport
  transport_id := transport_id
  transport_comp := transport_comp
  preservesUpdates := preservesUpdates

/-- **Still worlds**: the same authority everywhere, carried unchanged. -/
def still (W : Type u) [Category.{v} W] (α : Type w) [Zero α] [Add α] [SepAlgebra α] :
    IndexedAuthority.{u, v, w} W :=
  ofConstant α (fun _ => Hom.id α) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ => id_preservesUpdates)

/-- **Positive control**: without revocation every point has Cartesian lifts. -/
theorem stillWorlds_isPreFibered (W : Type u) [Category.{v} W] (α : Type w) [Zero α] [Add α]
    [SepAlgebra α] : (projection (still W α)).IsPreFibered :=
  isPreFibered_of_rightAdjoints fun _ => ⟨id, fun _ _ => Iff.rfl⟩

end IndexedAuthority

/-! ## Revocation -/

/-- Revoke all access. -/
def revokeAll : Hom Access Access where
  toFun _ := .none
  map_zero := rfl
  map_add _ := rfl
  map_separate _ := rfl

theorem revokeAll_preservesUpdates : PreservesUpdates revokeAll :=
  fun _ _ _ => FrameUpdate.refl _

/-- Transport between Boolean worlds: crossing from `false` to `true` revokes
all access; staying put changes nothing. -/
def crossingTransport {x y : Bool} (_ : x ⟶ y) : Hom Access Access :=
  if x = false ∧ y = true then revokeAll else Hom.id Access

theorem crossingTransport_comp {x y z : Bool} (f : x ⟶ y) (g : y ⟶ z) (a : Access) :
    crossingTransport (f ≫ g) a = crossingTransport g (crossingTransport f a) := by
  have xy : x ≤ y := leOfHom f
  have yz : y ≤ z := leOfHom g
  cases x <;> cases y <;> cases z
  all_goals first
    | exact absurd xy (by decide)
    | exact absurd yz (by decide)
    | simp [crossingTransport, revokeAll, Hom.id]

/-- **Two worlds; the second revokes all access.** -/
def revocationWorlds : IndexedAuthority.{0, 0, 0} Bool :=
  IndexedAuthority.ofConstant Access crossingTransport
    (fun x a => by cases x <;> simp [crossingTransport, Hom.id])
    crossingTransport_comp
    (fun {x y} _ => by
      unfold crossingTransport
      split
      · exact revokeAll_preservesUpdates
      · exact id_preservesUpdates)

namespace revocationWorlds

open IndexedAuthority

/-- **No authority before the revocation updates to consuming after it.** -/
theorem no_arrow_into_consume (a : Access) :
    ¬ Nonempty ((⟨false, a⟩ : Point revocationWorlds) ⟶ ⟨true, .consume⟩) := by
  rintro ⟨φ⟩
  have update := φ.2
  change FrameUpdate (crossingTransport φ.1 a) Access.consume at update
  simp only [crossingTransport, and_self, if_true] at update
  exact Access.not_frameUpdate_read_consume (fun c separate => update c rfl)

/-- **Revocation breaks the Cartesian property**: the projection of revoking
worlds is not a pre-fibration. -/
theorem revocationWorlds_not_isPreFibered :
    ¬ (projection revocationWorlds).IsPreFibered := by
  intro prefibered
  let crossing : false ⟶ true := homOfLE (by decide)
  obtain ⟨⟨world, a⟩, φ, cartesian⟩ := prefibered.exists_isCartesian'
    (a := (⟨true, .consume⟩ : Point revocationWorlds)) (R := false) crossing
  have sameWorld : world = false :=
    IsHomLift.domain_eq (projection revocationWorlds) crossing φ
  subst sameWorld
  exact no_arrow_into_consume a ⟨φ⟩

/-- Forward transport across the revocation is lawful: the pushed point
exists and holds no access. -/
theorem push_across (a : Access) :
    push (⟨false, a⟩ : Point revocationWorlds) (homOfLE (by decide) : false ⟶ true) =
      ⟨true, .none⟩ := by
  simp [push, revocationWorlds, IndexedAuthority.ofConstant, crossingTransport, revokeAll]

end revocationWorlds

/-! ## Plain indexed records -/

/-- A relabelling of capability records along changes of Boolean world:
crossing upgrades every right to consume. -/
def upgradeRelabel {x y : Bool} (_ : x ⟶ y) :
    CapabilityRecord Unit → CapabilityRecord Unit :=
  if x = false ∧ y = true then CapabilityRecord.upgrade else id

/-- The relabelling is functorial. -/
theorem upgradeRelabel_comp {x y z : Bool} (f : x ⟶ y) (g : y ⟶ z) :
    upgradeRelabel (f ≫ g) = upgradeRelabel g ∘ upgradeRelabel f := by
  have xy : x ≤ y := leOfHom f
  have yz : y ≤ z := leOfHom g
  funext record
  cases x <;> cases y <;> cases z
  all_goals first
    | exact absurd xy (by decide)
    | exact absurd yz (by decide)
    | simp [upgradeRelabel, CapabilityRecord.upgrade]

/-- **Yet it relabels read as consume**, which no transport of authority does
(`Access.no_hom_read_to_consume`, `transport_not_exclusive_of_selfSeparate`). -/
theorem upgradeRelabel_read :
    (upgradeRelabel (homOfLE (by decide) : false ⟶ true) ⟨(), .read⟩).right = .consume := by
  simp [upgradeRelabel, CapabilityRecord.upgrade]

/-- A relabelling cached per arrow of three worlds: only the first step
upgrades, and the composite arrow was cached before the upgrade. -/
def staleRelabel {x y : Fin 3} (_ : x ⟶ y) : CapabilityRecord Unit → CapabilityRecord Unit :=
  if x = 0 ∧ y = 1 then CapabilityRecord.upgrade else id

/-- **The reindexing law fails**: the stale record is not a functor of
worlds. -/
theorem staleRelabel_not_functorial :
    ¬ ∀ {x y z : Fin 3} (f : x ⟶ y) (g : y ⟶ z),
      staleRelabel (f ≫ g) = staleRelabel g ∘ staleRelabel f := by
  intro functorial
  have composite := congrFun
    (functorial (homOfLE (by decide) : (0 : Fin 3) ⟶ 1) (homOfLE (by decide) : (1 : Fin 3) ⟶ 2))
    ⟨(), .read⟩
  have rights := congrArg CapabilityRecord.right composite
  simp [staleRelabel, CapabilityRecord.upgrade] at rights

/-! ## Axiom audit -/

#print axioms IndexedAuthority.pushArrow_isStronglyCocartesian
#print axioms IndexedAuthority.forall_weakestBefore_iff_rightAdjoint
#print axioms IndexedAuthority.isCartesian_of_rightAdjoint
#print axioms IndexedAuthority.isPreFibered_of_rightAdjoints
#print axioms IndexedAuthority.stillWorlds_isPreFibered
#print axioms IndexedAuthority.transport_not_exclusive_of_selfSeparate
#print axioms revocationWorlds.no_arrow_into_consume
#print axioms revocationWorlds.revocationWorlds_not_isPreFibered
#print axioms upgradeRelabel_comp
#print axioms upgradeRelabel_read
#print axioms staleRelabel_not_functorial

end Mettapedia.GSLT.Contracts
