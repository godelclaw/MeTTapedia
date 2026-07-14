import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareProfile

namespace Mettapedia.GraphTheory.FourColor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The common interface for gluing a square profile to an exterior profile:
four square portals and an arbitrary finite exterior boundary. -/
abbrev SquareInterfaceNode (B : Type*) := Sum (Fin 4) B

/-- A finite Boolean connectivity profile on the common interface. -/
abbrev SquareInterfaceProfile (B : Type*) :=
  SquareInterfaceNode B → SquareInterfaceNode B → Bool

/-- Computed symmetry predicate for an interface profile. -/
def SquareInterfaceProfile.Symmetric {B : Type*}
    (profile : SquareInterfaceProfile B) : Prop :=
  ∀ u v, profile u v = profile v u

theorem squareTrackedProfile_symmetric
    (w : SquareBoundaryWord) (x : SquareInternalColoring)
    (a b : Color) (i j : Fin 4) :
    squareTrackedProfile w x a b i j = squareTrackedProfile w x a b j i := by
  rw [Bool.eq_iff_iff]
  rw [squareTrackedProfile_eq_true_iff, squareTrackedProfile_eq_true_iff]
  constructor
  · rintro ⟨hi, hj, hij⟩
    exact ⟨hj, hi, hij.symm⟩
  · rintro ⟨hj, hi, hji⟩
    exact ⟨hi, hj, hji.symm⟩

theorem squareReductionTrackedProfile_symmetric
    (side : SquareReductionSide) (w : SquareBoundaryWord)
    (a b : Color) (i j : Fin 4) :
    squareReductionTrackedProfile side w a b i j =
      squareReductionTrackedProfile side w a b j i := by
  rw [Bool.eq_iff_iff]
  rw [squareReductionTrackedProfile_eq_true_iff,
    squareReductionTrackedProfile_eq_true_iff]
  constructor
  · rintro ⟨hi, hj, hij⟩
    exact ⟨hj, hi, hij.symm⟩
  · rintro ⟨hj, hi, hji⟩
    exact ⟨hi, hj, hji.symm⟩

/-- Embed a four-portal local profile into the common interface, with no
relations involving exterior boundary nodes. -/
def squareProfileOnInterface {B : Type*} (localProfile : SquareTrackedProfile) :
    SquareInterfaceProfile B :=
  fun u v => match u, v with
  | .inl i, .inl j => localProfile i j
  | _, _ => false

/-- Union of the exterior component relation and the embedded local square
component relation. -/
def squareInterfaceLinked {B : Type*}
    (external : SquareInterfaceProfile B) (localProfile : SquareTrackedProfile)
    (u v : SquareInterfaceNode B) : Bool :=
  external u v || squareProfileOnInterface (B := B) localProfile u v

/-- Loopless adjacency used to compute the transitive closure of the union
of exterior and local component relations. -/
def squareInterfaceAdj {B : Type*} [DecidableEq B]
    (external : SquareInterfaceProfile B) (localProfile : SquareTrackedProfile)
    (u v : SquareInterfaceNode B) : Bool :=
  decide (u ≠ v) && squareInterfaceLinked external localProfile u v

theorem squareInterfaceLinked_symm {B : Type*}
    (external : SquareInterfaceProfile B) (localProfile : SquareTrackedProfile)
    (hext : external.Symmetric)
    (hloc : ∀ i j, localProfile i j = localProfile j i)
    (u v : SquareInterfaceNode B) :
    squareInterfaceLinked external localProfile u v =
      squareInterfaceLinked external localProfile v u := by
  unfold squareInterfaceLinked
  rw [hext u v]
  cases u <;> cases v <;> simp [squareProfileOnInterface, hloc]

theorem squareInterfaceAdj_symm {B : Type*} [DecidableEq B]
    (external : SquareInterfaceProfile B) (localProfile : SquareTrackedProfile)
    (hext : external.Symmetric)
    (hloc : ∀ i j, localProfile i j = localProfile j i)
    (u v : SquareInterfaceNode B) :
    squareInterfaceAdj external localProfile u v =
      squareInterfaceAdj external localProfile v u := by
  unfold squareInterfaceAdj
  rw [squareInterfaceLinked_symm external localProfile hext hloc u v]
  congr 1
  simp [ne_comm]

theorem squareInterfaceAdj_self {B : Type*} [DecidableEq B]
    (external : SquareInterfaceProfile B) (localProfile : SquareTrackedProfile)
    (u : SquareInterfaceNode B) :
    squareInterfaceAdj external localProfile u u = false := by
  simp [squareInterfaceAdj]

/-- The graph whose reachability computes composition of a symmetric
exterior profile with a symmetric local square profile. -/
def squareInterfaceGraph {B : Type*} [DecidableEq B]
    (external : SquareInterfaceProfile B) (localProfile : SquareTrackedProfile)
    (hext : external.Symmetric)
    (hloc : ∀ i j, localProfile i j = localProfile j i) :
    SimpleGraph (SquareInterfaceNode B) where
  Adj u v := squareInterfaceAdj external localProfile u v = true
  symm := ⟨by
    intro u v huv
    rw [squareInterfaceAdj_symm external localProfile hext hloc u v] at huv
    exact huv⟩
  loopless := ⟨by
    intro u huu
    rw [squareInterfaceAdj_self external localProfile u] at huu
    contradiction⟩

/-- Compose an exterior connectivity profile with a local square profile.
The diagonal records which interface nodes are active; connectivity is the
finite transitive closure of the union relation. -/
def composeSquareInterfaceProfile {B : Type*} [Fintype B] [DecidableEq B]
    (external : SquareInterfaceProfile B) (localProfile : SquareTrackedProfile) :
    SquareInterfaceProfile B :=
  let local' := squareProfileOnInterface (B := B) localProfile
  let linked := fun u v => external u v || local' u v
  let adj := squareInterfaceAdj external localProfile
  fun u v => linked u u && linked v v &&
    decide (v ∈ finsetReachWithin adj u (Fintype.card (SquareInterfaceNode B)))

/-- The computed composition is ordinary graph reachability in the union
of the exterior and local component relations. -/
theorem composeSquareInterfaceProfile_eq_true_iff
    {B : Type*} [Fintype B] [DecidableEq B]
    (external : SquareInterfaceProfile B) (localProfile : SquareTrackedProfile)
    (hext : external.Symmetric)
    (hloc : ∀ i j, localProfile i j = localProfile j i)
    (u v : SquareInterfaceNode B) :
    composeSquareInterfaceProfile external localProfile u v = true ↔
      squareInterfaceLinked external localProfile u u = true ∧
      squareInterfaceLinked external localProfile v v = true ∧
      (squareInterfaceGraph external localProfile hext hloc).Reachable u v := by
  unfold composeSquareInterfaceProfile
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hreach :
      v ∈ finsetReachWithin (squareInterfaceAdj external localProfile) u
          (Fintype.card (SquareInterfaceNode B)) ↔
        (squareInterfaceGraph external localProfile hext hloc).Reachable u v := by
    simpa using mem_finsetReachWithin_card_iff_reachable
      (squareInterfaceGraph external localProfile hext hloc)
      (squareInterfaceAdj external localProfile) (by intros; rfl) u v
  rw [hreach]
  simp only [squareInterfaceLinked, and_assoc]

/-- Profiles obtained by composing one fixed exterior profile with every
proper local square extension. -/
def squareComposedExtensionProfileMultiset
    {B : Type*} [Fintype B] [DecidableEq B]
    (external : SquareInterfaceProfile B)
    (w : SquareBoundaryWord) (a b : Color) :
    Multiset (SquareInterfaceProfile B) :=
  (squareExtensionProfileMultiset w a b).map
    (composeSquareInterfaceProfile external)

/-- Profiles obtained by composing one fixed exterior profile with every
compatible planar square reduction. -/
def squareComposedReductionProfileMultiset
    {B : Type*} [Fintype B] [DecidableEq B]
    (external : SquareInterfaceProfile B)
    (w : SquareBoundaryWord) (a b : Color) :
    Multiset (SquareInterfaceProfile B) :=
  (squareReductionProfileMultiset w a b).map
    (composeSquareInterfaceProfile external)

/-- Local profile equality is preserved after composition with an arbitrary
finite exterior profile. -/
theorem squareComposedProfileMultisetIdentity
    {B : Type*} [Fintype B] [DecidableEq B]
    (external : SquareInterfaceProfile B)
    (w : SquareBoundaryWord) (a b : Color)
    (hw : w.Nonzero) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    squareComposedExtensionProfileMultiset external w a b =
      squareComposedReductionProfileMultiset external w a b := by
  unfold squareComposedExtensionProfileMultiset
    squareComposedReductionProfileMultiset
  rw [squareLocalProfileIdentity w a b hw ha hb hab]

/-- Per-profile count form of `squareComposedProfileMultisetIdentity`. -/
theorem squareComposedProfileCountIdentity
    {B : Type*} [Fintype B] [DecidableEq B]
    (external target : SquareInterfaceProfile B)
    (w : SquareBoundaryWord) (a b : Color)
    (hw : w.Nonzero) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (squareComposedExtensionProfileMultiset external w a b).count target =
      (squareComposedReductionProfileMultiset external w a b).count target := by
  rw [squareComposedProfileMultisetIdentity external w a b hw ha hb hab]

/-- The singleton profile contribution from one planar square reduction,
present exactly when its boundary equalities are compatible. -/
def squareReductionSideProfileMultiset
    (side : SquareReductionSide) (w : SquareBoundaryWord) (a b : Color) :
    Multiset SquareTrackedProfile :=
  if side.Compatible w then {squareReductionTrackedProfile side w a b} else 0

/-- The combined reduction profile multiset is the sum of its two named
planar sides. -/
theorem squareReductionProfileMultiset_eq_side_sum
    (w : SquareBoundaryWord) (a b : Color) :
    squareReductionProfileMultiset w a b =
      squareReductionSideProfileMultiset .join01_23 w a b +
        squareReductionSideProfileMultiset .join12_30 w a b := by
  unfold squareReductionProfileMultiset squareReductionSideProfileMultiset
  rw [show (Finset.univ : Finset SquareReductionSide) =
      {.join01_23, .join12_30} by
    ext side
    fin_cases side <;> simp [SquareReductionSide.join01_23,
      SquareReductionSide.join12_30]]
  by_cases h0 : (0 : SquareReductionSide).Compatible w <;>
    by_cases h1 : (1 : SquareReductionSide).Compatible w <;>
    simp [h0, h1, SquareReductionSide.join01_23,
      SquareReductionSide.join12_30, Multiset.filter_singleton]

def squareComposedReductionSideProfileMultiset
    {B : Type*} [Fintype B] [DecidableEq B]
    (external : SquareInterfaceProfile B) (side : SquareReductionSide)
    (w : SquareBoundaryWord) (a b : Color) :
    Multiset (SquareInterfaceProfile B) :=
  (squareReductionSideProfileMultiset side w a b).map
    (composeSquareInterfaceProfile external)

/-- Fixed-exterior additive form of the square profile identity. -/
theorem squareProfileAdditiveCountIdentity
    {B : Type*} [Fintype B] [DecidableEq B]
    (external target : SquareInterfaceProfile B)
    (w : SquareBoundaryWord) (a b : Color)
    (hw : w.Nonzero) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (squareComposedExtensionProfileMultiset external w a b).count target =
      (squareComposedReductionSideProfileMultiset
        external .join01_23 w a b).count target +
      (squareComposedReductionSideProfileMultiset
        external .join12_30 w a b).count target := by
  rw [squareComposedProfileCountIdentity external target w a b hw ha hb hab]
  unfold squareComposedReductionProfileMultiset
    squareComposedReductionSideProfileMultiset
  rw [squareReductionProfileMultiset_eq_side_sum]
  simp

theorem squareComposedReductionProfileMultiset_eq_side_sum
    {B : Type*} [Fintype B] [DecidableEq B]
    (external : SquareInterfaceProfile B)
    (w : SquareBoundaryWord) (a b : Color) :
    squareComposedReductionProfileMultiset external w a b =
      squareComposedReductionSideProfileMultiset
        external .join01_23 w a b +
      squareComposedReductionSideProfileMultiset
        external .join12_30 w a b := by
  unfold squareComposedReductionProfileMultiset
    squareComposedReductionSideProfileMultiset
  rw [squareReductionProfileMultiset_eq_side_sum]
  simp

/-- Compose every exterior coloring profile, preserving multiplicity, with
all local square extensions. -/
def squareGluedExtensionProfileMultiset
    {B : Type*} [Fintype B] [DecidableEq B]
    (exteriorStates : Multiset (SquareInterfaceProfile B))
    (w : SquareBoundaryWord) (a b : Color) :
    Multiset (SquareInterfaceProfile B) :=
  exteriorStates.bind fun external =>
    squareComposedExtensionProfileMultiset external w a b

/-- Compose every exterior coloring profile, preserving multiplicity, with
one named planar reduction side. -/
def squareGluedReductionSideProfileMultiset
    {B : Type*} [Fintype B] [DecidableEq B]
    (exteriorStates : Multiset (SquareInterfaceProfile B))
    (side : SquareReductionSide)
    (w : SquareBoundaryWord) (a b : Color) :
    Multiset (SquareInterfaceProfile B) :=
  exteriorStates.bind fun external =>
    squareComposedReductionSideProfileMultiset external side w a b

/-- Multiset form of the compositional square profile identity for an
arbitrary multiset of exterior coloring profiles. -/
theorem squareGluedAdditiveProfileMultisetIdentity
    {B : Type*} [Fintype B] [DecidableEq B]
    (exteriorStates : Multiset (SquareInterfaceProfile B))
    (w : SquareBoundaryWord) (a b : Color)
    (hw : w.Nonzero) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    squareGluedExtensionProfileMultiset exteriorStates w a b =
      squareGluedReductionSideProfileMultiset
        exteriorStates .join01_23 w a b +
      squareGluedReductionSideProfileMultiset
        exteriorStates .join12_30 w a b := by
  unfold squareGluedExtensionProfileMultiset
    squareGluedReductionSideProfileMultiset
  calc
    exteriorStates.bind (fun external =>
        squareComposedExtensionProfileMultiset external w a b) =
        exteriorStates.bind (fun external =>
          squareComposedReductionProfileMultiset external w a b) := by
      apply Multiset.bind_congr
      intro external _hext
      exact squareComposedProfileMultisetIdentity external w a b hw ha hb hab
    _ = exteriorStates.bind (fun external =>
          squareComposedReductionSideProfileMultiset
            external .join01_23 w a b +
          squareComposedReductionSideProfileMultiset
            external .join12_30 w a b) := by
      apply Multiset.bind_congr
      intro external _hext
      exact squareComposedReductionProfileMultiset_eq_side_sum external w a b
    _ = _ := Multiset.bind_add _ _ _

/-- Profile-resolved square count identity at the finite interface layer.
For any multiset of exterior coloring profiles and target routing profile,
the square-extension count is the sum of the counts from the two planar
reductions:
`countG[π] = countG0[π] + countG00[π]`.

Instantiation with a facial square in a rotation system additionally needs
the graph-level extraction of its exterior coloring-profile multiset. -/
theorem squareGluedAdditiveProfileCountIdentity
    {B : Type*} [Fintype B] [DecidableEq B]
    (exteriorStates : Multiset (SquareInterfaceProfile B))
    (target : SquareInterfaceProfile B)
    (w : SquareBoundaryWord) (a b : Color)
    (hw : w.Nonzero) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (squareGluedExtensionProfileMultiset exteriorStates w a b).count target =
      (squareGluedReductionSideProfileMultiset
        exteriorStates .join01_23 w a b).count target +
      (squareGluedReductionSideProfileMultiset
        exteriorStates .join12_30 w a b).count target := by
  rw [squareGluedAdditiveProfileMultisetIdentity
    exteriorStates w a b hw ha hb hab]
  simp

end Mettapedia.GraphTheory.FourColor
