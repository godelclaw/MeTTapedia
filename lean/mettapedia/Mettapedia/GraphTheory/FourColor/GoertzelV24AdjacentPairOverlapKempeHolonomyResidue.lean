import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairOverlapKempeHolonomy

/-!
# Exact residue of adjacent-pair relational holonomy

The fixed-point-free relational obstruction has two genuinely different
forms.  Its fourfold composite may be empty, so that the four inhabited side
relations do not even concatenate around the cell.  Otherwise the composite
is inhabited and every completed return changes its starting witness.

This distinction is needed before any permutation-sign or monodromy argument:
an empty relation is not a permutation.  No geometric or wall-exclusion
consequence is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

/-- The fourfold composite is empty.  In the obstruction theorem below the
four side relations are separately inhabited, so this says that their local
witnesses fail to concatenate into even one clockwise path. -/
def HasRelationalBreak
    {Northwest Northeast Southeast Southwest : Type*}
    (north : Northwest → Northeast → Prop)
    (east : Northeast → Southeast → Prop)
    (south : Southeast → Southwest → Prop)
    (west : Southwest → Northwest → Prop) : Prop :=
  ¬ RelationNonempty
    (fourStepRelationalHolonomy north east south west)

/-- The proper holonomy residue: at least one clockwise path completes, but
every completed path changes its north-west witness. -/
def HasNonemptyFixedPointFreeRelationalHolonomy
    {Northwest Northeast Southeast Southwest : Type*}
    (north : Northwest → Northeast → Prop)
    (east : Northeast → Southeast → Prop)
    (south : Southeast → Southwest → Prop)
    (west : Southwest → Northwest → Prop) : Prop :=
  RelationNonempty
      (fourStepRelationalHolonomy north east south west) ∧
    ∀ start finish,
      fourStepRelationalHolonomy north east south west start finish →
        start ≠ finish

/-- A fixed-point-free relational obstruction is exactly either an empty
fourfold composite or an inhabited composite all of whose returns move their
starting witness.  The side-inhabitation hypotheses are retained literally
in both branches. -/
theorem hasFixedPointFreeRelationalHolonomy_iff_break_or_nonempty
    {Northwest Northeast Southeast Southwest : Type*}
    (north : Northwest → Northeast → Prop)
    (east : Northeast → Southeast → Prop)
    (south : Southeast → Southwest → Prop)
    (west : Southwest → Northwest → Prop) :
    HasFixedPointFreeRelationalHolonomy north east south west ↔
      RelationNonempty north ∧
        RelationNonempty east ∧
        RelationNonempty south ∧
        RelationNonempty west ∧
        (HasRelationalBreak north east south west ∨
          HasNonemptyFixedPointFreeRelationalHolonomy
            north east south west) := by
  constructor
  · rintro ⟨hnorth, heast, hsouth, hwest, hnoSection⟩
    refine ⟨hnorth, heast, hsouth, hwest, ?_⟩
    by_cases hcomposite : RelationNonempty
        (fourStepRelationalHolonomy north east south west)
    · right
      refine ⟨hcomposite, ?_⟩
      intro start finish hpath heq
      subst finish
      exact hnoSection ⟨start, hpath⟩
    · exact Or.inl hcomposite
  · rintro ⟨hnorth, heast, hsouth, hwest, hbreak | hproper⟩
    · refine ⟨hnorth, heast, hsouth, hwest, ?_⟩
      rintro ⟨start, hpath⟩
      exact hbreak ⟨start, start, hpath⟩
    · refine ⟨hnorth, heast, hsouth, hwest, ?_⟩
      rintro ⟨start, hpath⟩
      exact hproper.2 start start hpath rfl

/-- The active source support of a relation. -/
def RelationDomain {A B : Type*} (relation : A → B → Prop) : Set A :=
  {source | ∃ target, relation source target}

/-- The active target support of a relation. -/
def RelationRange {A B : Type*} (relation : A → B → Prop) : Set B :=
  {target | ∃ source, relation source target}

/-- A relation has at most one target at each source. -/
def RelationRightUnique {A B : Type*} (relation : A → B → Prop) : Prop :=
  ∀ ⦃source first second⦄,
    relation source first → relation source second → first = second

/-- A relation has at most one source at each target. -/
def RelationLeftUnique {A B : Type*} (relation : A → B → Prop) : Prop :=
  ∀ ⦃first second target⦄,
    relation first target → relation second target → first = second

/-- The source and target supports of an endorelation differ. -/
def HasRelationSupportDrift {A : Type*} (relation : A → A → Prop) : Prop :=
  RelationDomain relation ≠ RelationRange relation

/-- The relation branches forward or backward. -/
def HasRelationBranching {A : Type*} (relation : A → A → Prop) : Prop :=
  ¬ RelationRightUnique relation ∨ ¬ RelationLeftUnique relation

/-- A relation whose source and target supports agree and which is unique in
both directions.  It therefore induces a genuine permutation of its active
support. -/
structure StableRelationalTransport {A : Type*}
    (relation : A → A → Prop) : Prop where
  support_eq : RelationDomain relation = RelationRange relation
  rightUnique : RelationRightUnique relation
  leftUnique : RelationLeftUnique relation

namespace StableRelationalTransport

/-- The unique relation successor on the active support. -/
noncomputable def next {A : Type*} {relation : A → A → Prop}
    (transport : StableRelationalTransport relation)
    (source : RelationDomain relation) : RelationDomain relation :=
  let target := Classical.choose source.property
  ⟨target, by
    rw [transport.support_eq]
    exact ⟨source, Classical.choose_spec source.property⟩⟩

/-- The chosen successor is related to its source. -/
theorem next_spec {A : Type*} {relation : A → A → Prop}
    (transport : StableRelationalTransport relation)
    (source : RelationDomain relation) :
    relation source (transport.next source) := by
  exact Classical.choose_spec source.property

theorem next_injective {A : Type*} {relation : A → A → Prop}
    (transport : StableRelationalTransport relation) :
    Function.Injective transport.next := by
  intro first second heq
  have hfirst := transport.next_spec first
  have hsecond := transport.next_spec second
  have hvalue := congrArg Subtype.val heq
  rw [← hvalue] at hsecond
  exact Subtype.ext (transport.leftUnique hfirst hsecond)

theorem next_surjective {A : Type*} {relation : A → A → Prop}
    (transport : StableRelationalTransport relation) :
    Function.Surjective transport.next := by
  intro target
  have htargetRange : target.1 ∈ RelationRange relation := by
    rw [← transport.support_eq]
    exact target.property
  rcases htargetRange with ⟨source, hsource⟩
  let activeSource : RelationDomain relation :=
    ⟨source, ⟨target, hsource⟩⟩
  refine ⟨activeSource, Subtype.ext ?_⟩
  exact transport.rightUnique (transport.next_spec activeSource) hsource

/-- The permutation induced on the stable active support. -/
noncomputable def equivalence {A : Type*} {relation : A → A → Prop}
    (transport : StableRelationalTransport relation) :
    RelationDomain relation ≃ RelationDomain relation :=
  Equiv.ofBijective transport.next
    ⟨transport.next_injective, transport.next_surjective⟩

/-- The induced permutation follows the original relation on the active
support. -/
theorem equivalence_spec {A : Type*} {relation : A → A → Prop}
    (transport : StableRelationalTransport relation)
    (source : RelationDomain relation) :
    relation source (transport.equivalence source) := by
  exact transport.next_spec source

/-- On active sources and targets, the original relation is exactly the graph
of the induced permutation. -/
theorem relation_iff_equivalence_eq {A : Type*}
    {relation : A → A → Prop}
    (transport : StableRelationalTransport relation)
    (source target : RelationDomain relation) :
    relation source target ↔ transport.equivalence source = target := by
  constructor
  · intro hrelation
    exact Subtype.ext
      (transport.rightUnique (transport.equivalence_spec source) hrelation)
  · rintro rfl
    exact transport.equivalence_spec source

/-- On a two-element active support, a fixed-point-free stable transport is
the unique transposition and therefore has negative sign. -/
theorem equivalence_sign_eq_neg_one_of_card_eq_two
    {A : Type*} {relation : A → A → Prop}
    [Fintype (RelationDomain relation)]
    [DecidableEq (RelationDomain relation)]
    (transport : StableRelationalTransport relation)
    (hcard : Fintype.card (RelationDomain relation) = 2)
    (hfixed : ∀ source, transport.equivalence source ≠ source) :
    Equiv.Perm.sign transport.equivalence = -1 := by
  apply Equiv.Perm.IsSwap.sign_eq
  rw [← Equiv.Perm.card_support_eq_two]
  have hsupport : Equiv.Perm.support transport.equivalence = Finset.univ := by
    ext source
    simp [hfixed source]
  rw [hsupport, Finset.card_univ, hcard]

end StableRelationalTransport

/-- Every nonempty fixed-point-free endorelation has one of three exact
residues: its active support drifts, it branches, or it induces a genuine
fixed-point-free permutation on a stable nonempty support. -/
theorem nonemptyFixedPointFreeRelation_residue
    {A : Type*} (relation : A → A → Prop)
    (hnonempty : RelationNonempty relation)
    (hmove : ∀ source target, relation source target → source ≠ target) :
    HasRelationSupportDrift relation ∨
      HasRelationBranching relation ∨
      ∃ transport : StableRelationalTransport relation,
        Nonempty (RelationDomain relation) ∧
          ∀ source, transport.equivalence source ≠ source := by
  by_cases hsupport : RelationDomain relation = RelationRange relation
  · by_cases hright : RelationRightUnique relation
    · by_cases hleft : RelationLeftUnique relation
      · right
        right
        let transport : StableRelationalTransport relation := {
          support_eq := hsupport
          rightUnique := hright
          leftUnique := hleft }
        refine ⟨transport, ?_, ?_⟩
        · rcases hnonempty with ⟨source, target, hrelation⟩
          exact ⟨⟨source, target, hrelation⟩⟩
        · intro source heq
          have hne := hmove source.1 (transport.equivalence source).1
            (transport.equivalence_spec source)
          exact hne (congrArg Subtype.val heq).symm
      · exact Or.inr (Or.inl (Or.inr hleft))
    · exact Or.inr (Or.inl (Or.inl hright))
  · exact Or.inl hsupport

/-- Applied to the fourfold composite, proper relational holonomy therefore
has support drift, branching, or a genuine fixed-point-free permutation
residue. -/
theorem nonemptyFixedPointFreeRelationalHolonomy_residue
    {Northwest Northeast Southeast Southwest : Type*}
    (north : Northwest → Northeast → Prop)
    (east : Northeast → Southeast → Prop)
    (south : Southeast → Southwest → Prop)
    (west : Southwest → Northwest → Prop)
    (hproper : HasNonemptyFixedPointFreeRelationalHolonomy
      north east south west) :
    let composite := fourStepRelationalHolonomy north east south west
    HasRelationSupportDrift composite ∨
      HasRelationBranching composite ∨
      ∃ transport : StableRelationalTransport composite,
        Nonempty (RelationDomain composite) ∧
          ∀ source, transport.equivalence source ≠ source := by
  exact nonemptyFixedPointFreeRelation_residue _ hproper.1 hproper.2

/-- The concrete adjacent-pair lifting obstruction splits into a relational
break and a proper nonempty holonomy residue. -/
theorem hasSharedWitnessObstruction_iff_exists_break_or_nonemptyHolonomy
    (northwest northeast southeast southwest : AdjacentPairData G)
    (northwestBase : DeletionColoring northwest)
    (northeastBase : DeletionColoring northeast)
    (southeastBase : DeletionColoring southeast)
    (southwestBase : DeletionColoring southwest) :
    HasSharedWitnessObstruction
        (overlapKempeCellStateSupport
          northwest northeast southeast southwest
          northwestBase northeastBase southeastBase southwestBase)
        (compatibleOverlapKempeCycleSupport
          northwest northeast southeast southwest
          northwestBase northeastBase southeastBase southwestBase) ↔
      ∃ state : OverlapKempeCellState, state.IsCornerCoherent ∧
        RelationNonempty
          (overlapStateWitnessRelation northwest northeast
            northwestBase northeastBase state.north) ∧
        RelationNonempty
          (overlapStateWitnessRelation northeast southeast
            northeastBase southeastBase state.east) ∧
        RelationNonempty
          (overlapStateWitnessRelation southeast southwest
            southeastBase southwestBase state.south) ∧
        RelationNonempty
          (overlapStateWitnessRelation southwest northwest
            southwestBase northwestBase state.west) ∧
        (HasRelationalBreak
            (overlapStateWitnessRelation northwest northeast
              northwestBase northeastBase state.north)
            (overlapStateWitnessRelation northeast southeast
              northeastBase southeastBase state.east)
            (overlapStateWitnessRelation southeast southwest
              southeastBase southwestBase state.south)
            (overlapStateWitnessRelation southwest northwest
              southwestBase northwestBase state.west) ∨
          HasNonemptyFixedPointFreeRelationalHolonomy
            (overlapStateWitnessRelation northwest northeast
              northwestBase northeastBase state.north)
            (overlapStateWitnessRelation northeast southeast
              northeastBase southeastBase state.east)
            (overlapStateWitnessRelation southeast southwest
              southeastBase southwestBase state.south)
            (overlapStateWitnessRelation southwest northwest
              southwestBase northwestBase state.west)) := by
  rw [hasSharedWitnessObstruction_iff_exists_fixedPointFreeHolonomy]
  constructor
  · rintro ⟨state, hcoherent, hholonomy⟩
    exact ⟨state, hcoherent,
      (hasFixedPointFreeRelationalHolonomy_iff_break_or_nonempty
        _ _ _ _).1 hholonomy⟩
  · rintro ⟨state, hcoherent, hresidue⟩
    exact ⟨state, hcoherent,
      (hasFixedPointFreeRelationalHolonomy_iff_break_or_nonempty
        _ _ _ _).2 hresidue⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

/-! Publication-facing aliases for the refined relational residue. -/

alias GoertzelV24AdjacentPairOverlapKempeHolonomyResidue.hasFixedPointFreeRelationalHolonomy_iff_break_or_nonempty :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.hasFixedPointFreeRelationalHolonomy_iff_break_or_nonempty

alias GoertzelV24AdjacentPairOverlapKempeHolonomyResidue.hasSharedWitnessObstruction_iff_exists_break_or_nonemptyHolonomy :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.hasSharedWitnessObstruction_iff_exists_break_or_nonemptyHolonomy

alias GoertzelV24AdjacentPairOverlapKempeHolonomyResidue.nonemptyFixedPointFreeRelationalHolonomy_residue :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.nonemptyFixedPointFreeRelationalHolonomy_residue

alias GoertzelV24AdjacentPairOverlapKempeHolonomyResidue.equivalence_sign_eq_neg_one_of_card_eq_two :=
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.StableRelationalTransport.equivalence_sign_eq_neg_one_of_card_eq_two

end Mettapedia.GraphTheory.FourColor
