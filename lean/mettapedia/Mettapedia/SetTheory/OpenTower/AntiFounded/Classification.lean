import Mettapedia.SetTheory.OpenTower.AntiFounded.Branching
import Mettapedia.SetTheory.OpenTower.Potentialism.Modal

/-!
# The closed stages of the hypersets: between `V_κ` and `B_κ`

The closed sets of `ZFSet` are `∅`, `V_ω` and the `V_κ` for inaccessible `κ`, and they form one
chain (`InaccessibleLevels.closed_iff`, `ClosedLevels.closed_subset_total`). For the closed
stages of the hypersets (`HClosed`):

**Classification.** A closed stage `U` is empty, or it has a *height* `κ`, which is `ℵ₀` or an
inaccessible cardinal, and then (`hclosed_classification`):
* its well-founded part is `V_κ`;
* it includes the hyperset of `V_κ`, which is itself a closed stage (`hclosed_ofZFSet_iff`);
* it is included in `B_κ`, the hyperset of the hereditarily small hypersets, which is a closed
  stage (`hclosed_branching_iff`).

So `V_κ` is the least and `B_κ` the greatest closed stage of height `κ`. The member bound is
replacement: a member with at least `κ` members would map onto the ordinals below `κ`, and the
ordinal `κ` would be a member of the well-founded part (`HClosed.smallMembers_of_mem`).

**Not one chain.** Two closed stages of the same height `ω` can be incomparable, without any
large-cardinal hypothesis (`exists_incomparable_hclosed`): the hereditarily finitely branching
hypersets that are well-founded over `Ω`, and those well-founded over `J = {J, ∅}`
(`selfAndEmpty`). `Ω` lies in the first and not the second, `J` in the second and not the
first.

**Still directed, still well-founded under membership.** Any two closed stages lie in a
common one (`hclosed_directed`), the `B_κ` of the larger height. Membership among closed
stages raises the rank of the well-founded part (`HClosed.rank_lt_of_mem`), so it is
well-founded (`hclosed_mem_wellFounded`) although membership of hypersets is not.

**Cyclic data inside the stage.** Every node of a graph with fewer than `κ` nodes is decorated
by a member of `B_κ` (`decorate_mem_branching`); in particular the decorations of finite
graphs lie in `B_ℵ₀`.

**The universe law and the universe operator.** Every hyperset lies in a closed stage exactly
when there are cofinally many inaccessibles (`cofinalInaccessibles_iff_forall_exists_hclosed`):
the same hypothesis as for `ZFSet`. Under it every hyperset has a least closed stage around it
(`exists_isLeastStage`), and around a well-founded set that least stage is the hyperset of the
least closed set of `ZFSet` (`isLeastStage_ofZFSet_univOf`): the universe operator of the type
universes is unchanged. Around `Ω` the least stage has well-founded part `V_ω`
(`IsLeastStage.toZFSet_quineAtom`).

**What fails from the well-founded laws.**
* A closed stage need not be the hyperset of a set (`branching_aleph0_ne_ofZFSet`), and two
  closed stages can have one well-founded part (`ofZFSet_vonNeumann_omega_ne_branching`).
* Inclusion of closed stages is not linear (`exists_incomparable_hclosed`).
* Proper inclusion of closed stages is not membership (`exists_hclosed_ssubset_notMem`): the
  hyperset of `V_ω` is properly included in `B_ℵ₀` and is not a member of it.

**Modal reading.** With access by inclusion the closed stages validate the directedness schema
`.2` (`valid_dot2_hclosed`) and refute the linearity schema `.3` (`not_valid_dot3_hclosed`),
whereas on the closed sets of `ZFSet` `.3` is valid (`Potentialism.valid_dot3_closed`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.AntiFounded

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation
open Mettapedia.SetTheory.OpenTower.Strength
open Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels
open Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels
open Mettapedia.SetTheory.OpenTower.Potentialism
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Cardinal
open scoped ZFSet

universe u

/-! ## Small members, counted without repetition -/

/-- The members of a hyperset, presented without repetition by a type of the lower level:
the children of the point of a graph, identified when they picture one hyperset. -/
theorem exists_injective_members (x : HSet.{u}) :
    ∃ (ι : Type u) (g : ι → HSet.{u}), Function.Injective g ∧ ∀ y, y ∈ x ↔ ∃ i, g i = y := by
  obtain ⟨G, rfl⟩ := HSet.exists_mk x
  let s : Setoid {c : G.Node // G.edge G.point c} :=
    Setoid.ker fun c => HSet.decorate G.edge c.1
  refine ⟨Quotient s, Quotient.lift (fun c => HSet.decorate G.edge c.1) (fun _ _ h => h),
    ?_, fun y => ?_⟩
  · intro a b equal
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    exact Quotient.sound equal
  · rw [HSet.mem_mk]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨Quotient.mk s ⟨c, hc⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      induction q using Quotient.inductionOn with
      | h c => exact ⟨c.1, c.2, rfl⟩

/-- Given a presentation of the members without repetition, a hyperset has fewer than `κ`
members exactly when the presentation has fewer than `κ` indices. -/
theorem smallMembers_iff_of_injective {κ : Cardinal.{u}} {x : HSet.{u}} {ι : Type u}
    {g : ι → HSet.{u}} (hg : Function.Injective g) (hx : ∀ y, y ∈ x ↔ ∃ i, g i = y) :
    SmallMembers κ x ↔ #ι < κ := by
  constructor
  · rintro ⟨ι', g', hι', hg'⟩
    have hit : ∀ i, ∃ j, g' j = g i := fun i => (hg' _).mp ((hx _).mpr ⟨i, rfl⟩)
    choose φ hφ using hit
    have injective : Function.Injective φ := fun i i' e =>
      hg ((hφ i).symm.trans ((congrArg g' e).trans (hφ i')))
    exact (mk_le_of_injective injective).trans_lt hι'
  · exact fun h => ⟨ι, g, h, hx⟩

/-! ## The member bound -/

/-- **A member of a closed stage of height `κ` has fewer than `κ` members.** Otherwise a
function on its members would take every ordinal below `κ` as a value, and replacement would
put the ordinal `κ` into the well-founded part `V_κ`. -/
theorem HClosed.smallMembers_of_mem {U : HSet.{u}} (hU : HClosed U) {κ : Cardinal.{u}}
    (hW : HSet.toZFSet U = V_ κ.ord) (hκ : κ ≠ 0) {z : HSet.{u}} (hz : z ∈ U) :
    SmallMembers κ z := by
  classical
  obtain ⟨ι, g, hg, hzg⟩ := exists_injective_members z
  rw [smallMembers_iff_of_injective hg hzg]
  by_contra large
  have size : #κ.ord.ToType ≤ #ι := by
    rw [mk_ord_toType]
    exact not_lt.mp large
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp size
  have positive : (0 : Ordinal.{u}) < κ.ord := by
    rw [Cardinal.lt_ord, Ordinal.card_zero]
    exact pos_iff_ne_zero.mpr hκ
  let ordOf : HSet.{u} → Ordinal.{u} := fun y =>
    if h : ∃ t, g (e t) = y then
      (Ordinal.typein (α := κ.ord.ToType) (· < ·)).toRelEmbedding h.choose
    else 0
  have ordOf_lt : ∀ y, ordOf y < κ.ord := by
    intro y
    by_cases h : ∃ t, g (e t) = y
    · simp only [ordOf, dif_pos h]
      exact Ordinal.typein_lt_self _
    · simp only [ordOf, dif_neg h]
      exact positive
  have member : HSet.ofZFSet κ.ord.toZFSet ∈ U := by
    refine hU.image_mem hz (fun y hy => ?_)
      ⟨fun y => HSet.ofZFSet (ordOf y).toZFSet, fun y => ?_⟩
    · obtain ⟨w, hw, rfl⟩ := HSet.mem_ofZFSet_iff.mp hy
      obtain ⟨β, hβ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hw
      rw [← mem_toZFSet_iff, hW, ZFSet.mem_vonNeumann, Ordinal.rank_toZFSet]
      exact hβ
    · rw [HSet.mem_ofZFSet_iff]
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨β, hβ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hw
        obtain ⟨t, ht⟩ := Ordinal.typein_surj (α := κ.ord.ToType) (· < ·)
          (by rw [Ordinal.type_toType]; exact hβ)
        refine ⟨g (e t), (hzg _).mpr ⟨e t, rfl⟩, ?_⟩
        have h : ∃ t', g (e t') = g (e t) := ⟨t, rfl⟩
        have chosen : h.choose = t := e.injective (hg h.choose_spec)
        simp only [ordOf, dif_pos h, chosen, ht]
      · rintro ⟨x, _, rfl⟩
        exact ⟨(ordOf x).toZFSet, Ordinal.mem_toZFSet_iff.mpr ⟨ordOf x, ordOf_lt x, rfl⟩, rfl⟩
  have below := mem_toZFSet_iff.mpr member
  rw [hW, ZFSet.mem_vonNeumann, Ordinal.rank_toZFSet] at below
  exact lt_irrefl _ below

/-! ## The classification -/

/-- **The closed stages of the hypersets.** A closed stage is empty, or it has a height `κ`,
`ℵ₀` or inaccessible, with well-founded part `V_κ`, and it lies between the hyperset of `V_κ`
and `B_κ`. -/
theorem hclosed_classification {U : HSet.{u}} (hU : HClosed U) :
    U = ∅ ∨ ∃ κ : Cardinal.{u}, (κ = ℵ₀ ∨ κ.IsInaccessible) ∧
      HSet.toZFSet U = V_ κ.ord ∧ HSet.ofZFSet (V_ κ.ord) ⊆ U ∧ U ⊆ branching κ := by
  by_cases empty : U = ∅
  · exact Or.inl empty
  right
  obtain ⟨x, hx⟩ : ∃ x, x ∈ U := by
    by_contra none
    exact empty (HSet.eq_empty_iff.mpr fun z hz => none ⟨z, hz⟩)
  have hW := hU.closed_toZFSet
  have hEmpty : (∅ : ZFSet.{u}) ∈ HSet.toZFSet U := by
    rw [mem_toZFSet_iff, HSet.ofZFSet_empty]
    exact hU.empty_mem hx
  have height : (HSet.toZFSet U).rank.card = ℵ₀ ∨ (HSet.toZFSet U).rank.card.IsInaccessible := by
    rcases (omega_le_rank hW hEmpty).eq_or_lt with same | above
    · left
      rw [← same, Ordinal.card_omega0]
    · right
      exact isInaccessible_card_rank hW above
  have equal : HSet.toZFSet U = V_ (HSet.toZFSet U).rank.card.ord := by
    rw [ord_card_rank hW]
    exact closed_eq_vonNeumann hW
  have ne : (HSet.toZFSet U).rank.card ≠ 0 := by
    rcases height with h | h
    · rw [h]
      exact aleph0_ne_zero
    · exact h.ne_zero
  refine ⟨_, height, equal, ?_, ?_⟩
  · rw [← equal]
    exact ofZFSet_toZFSet_subset U
  · refine HSet.subset_iff.mpr fun y hy => mem_branching.mpr fun z hz => ?_
    exact hU.smallMembers_of_mem equal ne (hU.mem_of_reflTransGen hy hz)

/-- The well-founded part is monotone. -/
theorem toZFSet_mono {U V : HSet.{u}} (h : U ⊆ V) : HSet.toZFSet U ⊆ HSet.toZFSet V :=
  fun _ hw => mem_toZFSet_iff.mpr (HSet.subset_iff.mp h (mem_toZFSet_iff.mp hw))

theorem ofZFSet_subset_ofZFSet {a b : ZFSet.{u}} (h : a ⊆ b) :
    HSet.ofZFSet a ⊆ HSet.ofZFSet b := by
  refine HSet.subset_iff.mpr fun y hy => ?_
  obtain ⟨w, hw, rfl⟩ := HSet.mem_ofZFSet_iff.mp hy
  exact HSet.ofZFSet_mem_ofZFSet_iff.mpr (h hw)

theorem hset_empty_subset (U : HSet.{u}) : (∅ : HSet.{u}) ⊆ U :=
  HSet.subset_iff.mpr fun z hz => absurd hz (HSet.notMem_empty z)

theorem hset_subset_trans {U V W : HSet.{u}} (hUV : U ⊆ V) (hVW : V ⊆ W) : U ⊆ W :=
  HSet.subset_iff.mpr fun _ hz => HSet.subset_iff.mp hVW (HSet.subset_iff.mp hUV hz)

/-! ## Directed, and well-founded under membership -/

/-- **Any two closed stages lie in a common closed stage.** -/
theorem hclosed_directed {U V : HSet.{u}} (hU : HClosed U) (hV : HClosed V) :
    ∃ W : HSet.{u}, HClosed W ∧ U ⊆ W ∧ V ⊆ W := by
  rcases hclosed_classification hU with rfl | ⟨κ, hκ, _, _, hUκ⟩
  · exact ⟨V, hV, hset_empty_subset V, HSet.subset_iff.mpr fun _ h => h⟩
  rcases hclosed_classification hV with rfl | ⟨μ, hμ, _, _, hVμ⟩
  · exact ⟨U, hU, HSet.subset_iff.mpr fun _ h => h, hset_empty_subset U⟩
  rcases le_total κ μ with h | h
  · exact ⟨branching μ, hclosed_branching_iff.mpr (Or.inr hμ),
      hset_subset_trans hUκ (branching_mono h), hVμ⟩
  · exact ⟨branching κ, hclosed_branching_iff.mpr (Or.inr hκ), hUκ,
      hset_subset_trans hVμ (branching_mono h)⟩

/-- **Membership in a closed stage raises the rank of the well-founded part.** -/
theorem HClosed.rank_lt_of_mem {U V : HSet.{u}} (hV : HClosed V) (h : U ∈ V) :
    (HSet.toZFSet U).rank < (HSet.toZFSet V).rank := by
  apply ZFSet.rank_lt_of_mem
  rw [mem_toZFSet_iff, ← sep_wf_eq_ofZFSet_toZFSet]
  exact hV.sep_mem h _

/-- **Membership among closed stages is well-founded.** -/
theorem hclosed_mem_wellFounded :
    WellFounded fun U V : {U : HSet.{u} // HClosed U} => U.1 ∈ V.1 :=
  Subrelation.wf (fun {_ V} h => V.2.rank_lt_of_mem h)
    (InvImage.wf (fun U : {U : HSet.{u} // HClosed U} => (HSet.toZFSet U.1).rank) Ordinal.lt_wf)

/-- No closed stage is a member of itself. -/
theorem HClosed.notMem_self {U : HSet.{u}} (hU : HClosed U) : U ∉ U :=
  fun h => lt_irrefl _ (hU.rank_lt_of_mem h)

/-! ## The universe law -/

theorem below_mk {G : AccessiblePointedGraph.{u}} {z : HSet.{u}} (h : Below (HSet.mk G) z) :
    ∃ n, HSet.decorate G.edge n = z := by
  induction h with
  | refl => exact ⟨G.point, (HSet.mk_eq_decorate G).symm⟩
  | tail _ hmem ih =>
    obtain ⟨n, rfl⟩ := ih
    obtain ⟨m, _, rfl⟩ := HSet.mem_decorate.mp hmem
    exact ⟨m, rfl⟩

/-- A hyperset pictured by a graph with fewer than `κ` nodes is hereditarily small. -/
theorem herSmall_mk {κ : Cardinal.{u}} (G : AccessiblePointedGraph.{u}) (h : #G.Node < κ) :
    HerSmall κ (HSet.mk G) := by
  intro z hz
  obtain ⟨n, rfl⟩ := below_mk hz
  exact ⟨{m // G.edge n m}, fun m => HSet.decorate G.edge m.1, (mk_subtype_le _).trans_lt h,
    fun y => by
      rw [HSet.mem_decorate]
      exact ⟨fun ⟨m, hm, e⟩ => ⟨⟨m, hm⟩, e⟩, fun ⟨m, e⟩ => ⟨m.1, m.2, e⟩⟩⟩

/-- **Anti-foundation inside `B_κ`.** Every node of a graph with fewer than `κ` nodes is
decorated by a member of `B_κ`: the cyclic data of small graphs lies in the stage. -/
theorem decorate_mem_branching {κ : Cardinal.{u}} {α : Type u} (r : α → α → Prop)
    (h : #α < κ) (a : α) : HSet.decorate r a ∈ branching κ :=
  mem_branching.mpr (herSmall_mk _ ((mk_subtype_le _).trans_lt h))

/-- The decorations of a finite graph lie in `B_ℵ₀`. -/
example {α : Type u} [Finite α] (r : α → α → Prop) (a : α) :
    HSet.decorate r a ∈ branching ℵ₀ :=
  decorate_mem_branching r (lt_aleph0_of_finite α) a

/-- **Every hyperset lies in a closed stage exactly when there are cofinally many
inaccessibles**: the same hypothesis as for the sets. -/
theorem cofinalInaccessibles_iff_forall_exists_hclosed :
    CofinalInaccessibles.{u} ↔ ∀ x : HSet.{u}, ∃ U, HClosed U ∧ x ∈ U := by
  constructor
  · intro h x
    obtain ⟨G, rfl⟩ := HSet.exists_mk x
    obtain ⟨κ, hκ, above⟩ := h (#G.Node).ord
    exact ⟨branching κ, hclosed_branching_iff.mpr (Or.inr (Or.inr hκ)),
      mem_branching.mpr (herSmall_mk G (ord_lt_ord.mp above))⟩
  · intro h
    refine cofinalInaccessibles_iff_cofinal.mpr fun w => ?_
    obtain ⟨U, hU, hw⟩ := h (HSet.ofZFSet w)
    exact ⟨HSet.toZFSet U, hU.closed_toZFSet, mem_toZFSet_iff.mpr hw⟩

/-! ## The least closed stage around a hyperset -/

/-- `U` is the least closed stage that has `N` as a member. -/
def IsLeastStage (N U : HSet.{u}) : Prop :=
  N ∈ U ∧ HClosed U ∧ ∀ V : HSet.{u}, N ∈ V → HClosed V → U ⊆ V

/-- The members of `B` that lie in every closed stage around `N`. -/
noncomputable def hhull (N B : HSet.{u}) : HSet.{u} :=
  HSet.sep (fun x => ∀ V : HSet.{u}, N ∈ V → HClosed V → x ∈ V) B

theorem mem_hhull {N B x : HSet.{u}} :
    x ∈ hhull N B ↔ x ∈ B ∧ ∀ V : HSet.{u}, N ∈ V → HClosed V → x ∈ V :=
  HSet.mem_sep

/-- Inside a closed stage around `N`, the least closed stage around `N` is cut out by
separation. -/
theorem isLeastStage_hhull {N B : HSet.{u}} (hB : HClosed B) (hN : N ∈ B) :
    IsLeastStage N (hhull N B) := by
  refine ⟨mem_hhull.mpr ⟨hN, fun _ h _ => h⟩, ⟨?_, ?_, ?_, ?_⟩, fun V hNV hV => ?_⟩
  · intro x hx y hy
    obtain ⟨hxB, hxall⟩ := mem_hhull.mp hx
    exact mem_hhull.mpr ⟨hB.transitive hxB hy, fun V hNV hV => hV.transitive (hxall V hNV hV) hy⟩
  · intro x hx
    obtain ⟨hxB, hxall⟩ := mem_hhull.mp hx
    exact mem_hhull.mpr ⟨hB.union_mem hxB, fun V hNV hV => hV.union_mem (hxall V hNV hV)⟩
  · intro x hx
    obtain ⟨hxB, hxall⟩ := mem_hhull.mp hx
    exact mem_hhull.mpr ⟨hB.power_mem hxB, fun V hNV hV => hV.power_mem (hxall V hNV hV)⟩
  · intro a b ha hb himage
    obtain ⟨haB, haall⟩ := mem_hhull.mp ha
    exact mem_hhull.mpr ⟨hB.image_mem haB (fun y hy => (mem_hhull.mp (hb hy)).1) himage,
      fun V hNV hV => hV.image_mem (haall V hNV hV)
        (fun y hy => (mem_hhull.mp (hb hy)).2 V hNV hV) himage⟩
  · exact HSet.subset_iff.mpr fun x hx => (mem_hhull.mp hx).2 V hNV hV

/-- The least closed stage around `N` is unique. -/
theorem IsLeastStage.unique {N U U' : HSet.{u}} (h : IsLeastStage N U)
    (h' : IsLeastStage N U') : U = U' :=
  HSet.ext fun _ =>
    ⟨fun hz => HSet.subset_iff.mp (h.2.2 U' h'.1 h'.2.1) hz,
      fun hz => HSet.subset_iff.mp (h'.2.2 U h.1 h.2.1) hz⟩

/-- **Under cofinally many inaccessibles, every hyperset has a least closed stage around
it.** -/
theorem exists_isLeastStage (h : CofinalInaccessibles.{u}) (N : HSet.{u}) :
    ∃ U, IsLeastStage N U := by
  obtain ⟨B, hB, hN⟩ := cofinalInaccessibles_iff_forall_exists_hclosed.mp h N
  exact ⟨hhull N B, isLeastStage_hhull hB hN⟩

/-- **The universe operator is unchanged.** Around a well-founded set, the least closed stage
of the hypersets is the hyperset of the least closed set of `ZFSet`. -/
theorem isLeastStage_ofZFSet_univOf (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    IsLeastStage (HSet.ofZFSet N) (HSet.ofZFSet (univOf h N)) := by
  refine ⟨HSet.ofZFSet_mem_ofZFSet_iff.mpr (mem_univOf h N),
    hclosed_ofZFSet_iff.mpr (univOf_closed h N), fun V hNV hV => ?_⟩
  have least : univOf h N ⊆ HSet.toZFSet V :=
    univOf_minimal h (mem_toZFSet_iff.mpr hNV) hV.closed_toZFSet
  exact hset_subset_trans (ofZFSet_subset_ofZFSet least) (ofZFSet_toZFSet_subset V)

/-- The least closed stage around a well-founded set is well-founded. -/
theorem IsLeastStage.eq_ofZFSet_univOf (h : CofinalInaccessibles.{u}) {N : ZFSet.{u}}
    {U : HSet.{u}} (hU : IsLeastStage (HSet.ofZFSet N) U) :
    U = HSet.ofZFSet (univOf h N) :=
  hU.unique (isLeastStage_ofZFSet_univOf h N)

/-! ## Two closed stages of height `ω` that are not comparable -/

/-- The graph of `J = {J, ∅}`: the node `true` has both nodes as children, `false` has none. -/
def selfAndEmptyEdge : ULift.{u} Bool → ULift.{u} Bool → Prop :=
  fun p _ => p.down = true

/-- `J = {J, ∅}`, a self-member other than `Ω`. -/
noncomputable def selfAndEmpty : HSet.{u} :=
  HSet.decorate selfAndEmptyEdge ⟨true⟩

theorem decorate_selfAndEmptyEdge_false :
    HSet.decorate selfAndEmptyEdge.{u} ⟨false⟩ = ∅ :=
  HSet.eq_empty_iff.mpr fun y hy => by
    obtain ⟨_, hb, _⟩ := HSet.mem_decorate.mp hy
    exact Bool.false_ne_true hb

theorem mem_selfAndEmpty {y : HSet.{u}} : y ∈ selfAndEmpty.{u} ↔ y = selfAndEmpty ∨ y = ∅ := by
  change y ∈ HSet.decorate selfAndEmptyEdge ⟨true⟩ ↔ _
  rw [HSet.mem_decorate]
  constructor
  · rintro ⟨⟨b⟩, _, rfl⟩
    cases b
    · exact Or.inr decorate_selfAndEmptyEdge_false
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨true⟩, rfl, rfl⟩
    · exact ⟨⟨false⟩, rfl, decorate_selfAndEmptyEdge_false⟩

theorem selfAndEmpty_mem_self : selfAndEmpty.{u} ∈ selfAndEmpty :=
  mem_selfAndEmpty.mpr (Or.inl rfl)

theorem selfAndEmpty_ne_quineAtom : selfAndEmpty.{u} ≠ HSet.quineAtom := by
  intro equal
  have member : (∅ : HSet.{u}) ∈ selfAndEmpty := mem_selfAndEmpty.mpr (Or.inr rfl)
  rw [equal] at member
  exact HSet.empty_ne_quineAtom (HSet.mem_quineAtom.mp member)

theorem below_selfAndEmpty {z : HSet.{u}} (h : Below selfAndEmpty z) :
    z = selfAndEmpty ∨ z = ∅ := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hmem ih =>
    rcases ih with rfl | rfl
    · exact mem_selfAndEmpty.mp hmem
    · exact absurd hmem (HSet.notMem_empty _)

theorem selfAndEmpty_mem_branching : selfAndEmpty.{u} ∈ branching ℵ₀ := by
  refine mem_branching.mpr fun z hz => ?_
  rcases below_selfAndEmpty hz with rfl | rfl
  · refine ⟨ULift.{u} Bool, fun b => HSet.decorate selfAndEmptyEdge b, lt_aleph0_of_finite _,
      fun y => ?_⟩
    change y ∈ HSet.decorate selfAndEmptyEdge ⟨true⟩ ↔ _
    rw [HSet.mem_decorate]
    exact ⟨fun ⟨b, _, e⟩ => ⟨b, e⟩, fun ⟨b, e⟩ => ⟨b, rfl, e⟩⟩
  · exact smallMembers_empty aleph0_ne_zero

/-- Separating by a predicate that holds of every well-founded hyperset keeps the
well-founded part. -/
theorem toZFSet_sep_of_wf {P : HSet.{u} → Prop} (hP : ∀ x : HSet.{u}, x.WF → P x)
    (B : HSet.{u}) : HSet.toZFSet (HSet.sep P B) = HSet.toZFSet B := by
  ext w
  rw [mem_toZFSet_iff, mem_toZFSet_iff, HSet.mem_sep]
  exact ⟨fun h => h.1, fun h => ⟨h, hP _ (HSet.wf_ofZFSet w)⟩⟩

/-- The closed stage of height `ω` around `Ω`: hereditarily finitely branching, and
well-founded over `Ω`. -/
noncomputable def quineStage : HSet.{u} :=
  HSet.sep (WFOver HSet.quineAtom) (branching ℵ₀)

/-- The closed stage of height `ω` around `J = {J, ∅}`. -/
noncomputable def selfAndEmptyStage : HSet.{u} :=
  HSet.sep (WFOver selfAndEmpty) (branching ℵ₀)

theorem hclosed_branching_aleph0 : HClosed (branching (ℵ₀ : Cardinal.{u})) :=
  hclosed_branching_iff.mpr (Or.inr (Or.inl rfl))

theorem toZFSet_branching_aleph0 :
    HSet.toZFSet (branching (ℵ₀ : Cardinal.{u})) = V_ Ordinal.omega0 := by
  rw [toZFSet_branching hclosed_branching_aleph0, ord_aleph0]

theorem hclosed_quineStage : HClosed quineStage.{u} :=
  hclosed_branching_aleph0.sep_stable (stable_wfOver fun z hz => by
    rw [HSet.mem_quineAtom.mp hz]
    exact wfOver_self _)

theorem hclosed_selfAndEmptyStage : HClosed selfAndEmptyStage.{u} :=
  hclosed_branching_aleph0.sep_stable (stable_wfOver fun z hz => by
    rcases mem_selfAndEmpty.mp hz with rfl | rfl
    · exact wfOver_self _
    · exact wfOver_of_wf HSet.wf_empty _)

theorem quineAtom_mem_quineStage : HSet.quineAtom.{u} ∈ quineStage :=
  HSet.mem_sep.mpr ⟨quineAtom_mem_branching, wfOver_self _⟩

theorem quineAtom_notMem_selfAndEmptyStage : HSet.quineAtom.{u} ∉ selfAndEmptyStage :=
  fun h => not_wfOver_of_mem_self HSet.quineAtom_mem_self selfAndEmpty_ne_quineAtom.symm
    (HSet.mem_sep.mp h).2

theorem selfAndEmpty_mem_selfAndEmptyStage : selfAndEmpty.{u} ∈ selfAndEmptyStage :=
  HSet.mem_sep.mpr ⟨selfAndEmpty_mem_branching, wfOver_self _⟩

theorem selfAndEmpty_notMem_quineStage : selfAndEmpty.{u} ∉ quineStage :=
  fun h => not_wfOver_of_mem_self selfAndEmpty_mem_self selfAndEmpty_ne_quineAtom
    (HSet.mem_sep.mp h).2

/-- **Two closed stages of height `ω`, neither included in the other.** No large-cardinal
hypothesis is used. -/
theorem exists_incomparable_hclosed :
    ∃ U V : HSet.{u}, HClosed U ∧ HClosed V ∧
      HSet.toZFSet U = V_ Ordinal.omega0 ∧ HSet.toZFSet V = V_ Ordinal.omega0 ∧
      ¬ U ⊆ V ∧ ¬ V ⊆ U := by
  refine ⟨quineStage, selfAndEmptyStage, hclosed_quineStage, hclosed_selfAndEmptyStage,
    ?_, ?_, fun h => ?_, fun h => ?_⟩
  · rw [quineStage, toZFSet_sep_of_wf (fun x hx => wfOver_of_wf hx _), toZFSet_branching_aleph0]
  · rw [selfAndEmptyStage, toZFSet_sep_of_wf (fun x hx => wfOver_of_wf hx _),
      toZFSet_branching_aleph0]
  · exact quineAtom_notMem_selfAndEmptyStage (HSet.subset_iff.mp h quineAtom_mem_quineStage)
  · exact selfAndEmpty_notMem_quineStage
      (HSet.subset_iff.mp h selfAndEmpty_mem_selfAndEmptyStage)

/-! ## Laws of the well-founded closed sets that fail -/

/-- Two closed stages with one well-founded part, `V_ω`. -/
theorem ofZFSet_vonNeumann_omega_ne_branching :
    HSet.ofZFSet (V_ Ordinal.omega0 : ZFSet.{u}) ≠ branching ℵ₀ :=
  fun h => branching_aleph0_ne_ofZFSet _ h.symm

/-- **Proper inclusion of closed stages is not membership.** -/
theorem exists_hclosed_ssubset_notMem :
    ∃ U V : HSet.{u}, HClosed U ∧ HClosed V ∧ U ⊆ V ∧ U ≠ V ∧ U ∉ V :=
  ⟨_, _, hclosed_ofZFSet_iff.mpr ((closed_iff _).mpr (Or.inr (Or.inl rfl))),
    hclosed_branching_aleph0, ofZFSet_vonNeumann_omega_subset_branching,
    ofZFSet_vonNeumann_omega_ne_branching, ofZFSet_vonNeumann_omega_notMem_branching⟩

/-- The least closed stage around `Ω` has the hereditarily finite sets as its well-founded
part. -/
theorem IsLeastStage.toZFSet_quineAtom {U : HSet.{u}} (h : IsLeastStage HSet.quineAtom U) :
    HSet.toZFSet U = V_ Ordinal.omega0 := by
  have hW := h.2.1.closed_toZFSet
  have inside : HSet.toZFSet U ⊆ V_ Ordinal.omega0 := by
    rw [← toZFSet_branching_aleph0]
    exact toZFSet_mono (h.2.2 _ quineAtom_mem_branching hclosed_branching_aleph0)
  have hEmpty : (∅ : ZFSet.{u}) ∈ HSet.toZFSet U := by
    rw [mem_toZFSet_iff, HSet.ofZFSet_empty]
    exact h.2.1.empty_mem h.1
  have rankEq : (HSet.toZFSet U).rank = Ordinal.omega0 :=
    le_antisymm (ZFSet.subset_vonNeumann.mp inside) (omega_le_rank hW hEmpty)
  rw [closed_eq_vonNeumann hW, rankEq]

/-! ## The modal reading -/

/-- The closed stages, with access by inclusion, validate the directedness schema. -/
theorem valid_dot2_hclosed (φ : Formula) :
    Valid (fun A B : {U : HSet.{u} // HClosed U} => A.1 ⊆ B.1) (Formula.axiomDot2 φ) :=
  valid_dot2_of_directed (fun A B => by
    obtain ⟨W, hW, hA, hB⟩ := hclosed_directed A.2 B.2
    exact ⟨⟨W, hW⟩, hA, hB⟩) φ

/-- **The closed stages refute the linearity schema** at the empty stage, for the valuation
naming two incomparable stages of height `ω`. -/
theorem not_valid_dot3_hclosed :
    ¬ Valid (fun A B : {U : HSet.{u} // HClosed U} => A.1 ⊆ B.1)
      (Formula.axiomDot3 (.atom 0) (.atom 1)) := by
  obtain ⟨U, V, hU, hV, _, _, hUV, hVU⟩ := exists_incomparable_hclosed.{u}
  intro hvalid
  let val : ℕ → {U : HSet.{u} // HClosed U} → Prop := fun n W => if n = 0 then W.1 = U else W.1 = V
  have forced := hvalid val ⟨∅, hclosed_empty⟩
  simp only [Formula.axiomDot3, forces_impl, forces_conj, forces_diamond, forces_disj,
    forces_atom] at forced
  obtain ⟨W, _, hW⟩ := forced ⟨⟨⟨U, hU⟩, hset_empty_subset U, by simp [val]⟩,
    ⟨⟨V, hV⟩, hset_empty_subset V, by simp [val]⟩⟩
  rcases hW with ⟨h0, W', hWW', h1⟩ | ⟨h1, W', hWW', h0⟩
  · simp only [val, if_pos rfl] at h0
    simp only [val, one_ne_zero, if_false] at h1
    exact hUV (h0 ▸ h1 ▸ hWW')
  · simp only [val, one_ne_zero, if_false] at h1
    simp only [val, if_pos rfl] at h0
    exact hVU (h1 ▸ h0 ▸ hWW')

#print axioms hclosed_classification
#print axioms hclosed_directed
#print axioms hclosed_mem_wellFounded
#print axioms cofinalInaccessibles_iff_forall_exists_hclosed
#print axioms decorate_mem_branching
#print axioms isLeastStage_ofZFSet_univOf
#print axioms exists_incomparable_hclosed
#print axioms exists_hclosed_ssubset_notMem
#print axioms IsLeastStage.toZFSet_quineAtom
#print axioms valid_dot2_hclosed
#print axioms not_valid_dot3_hclosed

end Mettapedia.SetTheory.OpenTower.AntiFounded
