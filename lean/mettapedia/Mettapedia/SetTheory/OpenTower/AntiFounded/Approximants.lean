import Mettapedia.SetTheory.OpenTower.AntiFounded.Classification

/-!
# Well-founded sets build up, hypersets are identified from above, and they meet

**Initial algebra and final coalgebra.** A map `f` from sets to hypersets *keeps membership* when
the members of `f x` are the values of `f` on the members of `x` (`IsMembershipMap`). The map
`HSet.ofZFSet` keeps membership, and it is the only such map, by two different arguments:

* bottom-up, by induction on membership of sets, the universal property of the well-founded sets
  as an initial algebra (`IsMembershipMap.eq_ofZFSet_of_induction`);
* top-down, because the pairs `(f z, ofZFSet z)` form a bisimulation of hyperset membership, the
  universal property of the hypersets as a final coalgebra
  (`IsMembershipMap.eq_ofZFSet_of_coinduction`).

The map is injective (existing `HSet.ofZFSet_injective`) and its values are exactly the
well-founded hypersets (`exists_ofZFSet_iff_wf`). Stage by stage it sends `V_κ` onto the
well-founded part of `B_κ` (`ofZFSet_mem_branching_iff`, `sep_wf_branching`).

**Approximants.** `Approx α x y` says that `x` and `y` agree to depth `α`: for every `β < α`
each member of one agrees to depth `β` with a member of the other. It is reflexive, symmetric,
and weaker at smaller depths. A well-founded set records the agreement: the *truncation*
`trunc α x`, a set of `ZFSet`, is the set of pairs `⟨β, trunc β x'⟩` for `β < α` and `x' ∈ x`, and
`trunc α x = trunc α y ↔ Approx α x y` (`trunc_eq_trunc_iff`).

**A hyperset is determined by its well-founded approximants.** If `x` and `y` have fewer than
`κ` members hereditarily, `κ` regular, and agree to every depth below `κ`, they are equal
(`eq_of_forall_approx`): the agreements at the depths below `κ` choose, by regularity, one
partner that works at every depth, and these partners form a bisimulation. For every pair of
hypersets some regular `κ` works, so `x = y` exactly when they agree to every depth
(`eq_iff_forall_approx`), exactly when all their truncations agree (`eq_iff_forall_trunc`).

**Transport into the closed bubble.** For `x ∈ B_κ` and `α < κ` the truncation lies in `V_κ`
(`trunc_mem_vonNeumann`), and the truncations below `κ` determine the members of `B_κ`
(`eq_of_trunc_eq`). So questions about `B_κ` become questions about sequences in `V_κ`.

**Controls.** The truncations of `Ω` are pairwise distinct well-founded sets
(`trunc_quineAtom_injective`), yet `Ω` is not well-founded. Without a bound on branching the
finite depths do not suffice: `{s_n : n ∈ ℕ}`, with `s_n` the `n`-fold singleton of `∅`, and the
same set with `Ω` added agree to every finite depth and are different
(`chains_agree_to_finite_depth`, `chains_ne_chains_with_quineAtom`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.AntiFounded

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Cardinal
open scoped ZFSet

universe u

/-! ## The canonical map from sets to hypersets -/

/-- `f` keeps membership: the members of `f x` are the values of `f` on the members of `x`. -/
def IsMembershipMap (f : ZFSet.{u} → HSet.{u}) : Prop :=
  ∀ x y, y ∈ f x ↔ ∃ z ∈ x, f z = y

theorem isMembershipMap_ofZFSet : IsMembershipMap HSet.ofZFSet.{u} :=
  fun _ _ => HSet.mem_ofZFSet_iff

/-- **Bottom-up**: a map keeping membership is `ofZFSet`, by induction on membership of
sets. -/
theorem IsMembershipMap.eq_ofZFSet_of_induction {f : ZFSet.{u} → HSet.{u}}
    (hf : IsMembershipMap f) : f = HSet.ofZFSet := by
  funext x
  induction x using ZFSet.inductionOn with
  | h x ih =>
    apply HSet.ext
    intro y
    rw [hf, HSet.mem_ofZFSet_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, (ih z hz).symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, ih z hz⟩

/-- **Top-down**: a map keeping membership is `ofZFSet`, because the pairs of their values form a
bisimulation of hyperset membership. -/
theorem IsMembershipMap.eq_ofZFSet_of_coinduction {f : ZFSet.{u} → HSet.{u}}
    (hf : IsMembershipMap f) : f = HSet.ofZFSet := by
  funext x
  refine HSet.eq_of_isBisimulation (R := fun a b => ∃ z, f z = a ∧ HSet.ofZFSet z = b) ?_
    ⟨x, rfl, rfl⟩
  rintro _ _ ⟨z, rfl, rfl⟩
  refine ⟨fun a' ha' => ?_, fun b' hb' => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := (hf z a').mp ha'
    exact ⟨HSet.ofZFSet w, HSet.ofZFSet_mem_ofZFSet_iff.mpr hw, w, rfl, rfl⟩
  · obtain ⟨w, hw, rfl⟩ := HSet.mem_ofZFSet_iff.mp hb'
    exact ⟨f w, (hf z _).mpr ⟨w, hw, rfl⟩, w, rfl, rfl⟩

/-- The values of `ofZFSet` are exactly the well-founded hypersets. -/
theorem exists_ofZFSet_iff_wf {y : HSet.{u}} : (∃ x, HSet.ofZFSet x = y) ↔ y.WF :=
  ⟨fun ⟨x, hx⟩ => hx ▸ HSet.wf_ofZFSet x,
    fun hy => ⟨HSet.toZFSet y, HSet.ofZFSet_toZFSet_of_wf hy⟩⟩

/-- Stage by stage: a set is in `V_κ` exactly when its hyperset is in a closed `B_κ`. -/
theorem ofZFSet_mem_branching_iff {κ : Cardinal.{u}} (h : HClosed (branching κ))
    {x : ZFSet.{u}} : HSet.ofZFSet x ∈ branching κ ↔ x ∈ V_ κ.ord := by
  rw [← mem_toZFSet_iff, toZFSet_branching h]

/-- The well-founded part of a closed `B_κ` is the image of `V_κ`. -/
theorem sep_wf_branching {κ : Cardinal.{u}} (h : HClosed (branching κ)) :
    HSet.sep HSet.WF (branching κ) = HSet.ofZFSet (V_ κ.ord) := by
  rw [sep_wf_eq_ofZFSet_toZFSet, toZFSet_branching h]

/-! ## Agreement to a depth -/

/-- `Approx α x y`: for every `β < α`, each member of either agrees to depth `β` with a member
of the other. -/
noncomputable def Approx : Ordinal.{u} → HSet.{u} → HSet.{u} → Prop :=
  Ordinal.lt_wf.fix (C := fun _ => HSet.{u} → HSet.{u} → Prop) fun α ih x y =>
    ∀ β (hβ : β < α), (∀ x' ∈ x, ∃ y' ∈ y, ih β hβ x' y') ∧ (∀ y' ∈ y, ∃ x' ∈ x, ih β hβ x' y')

theorem approx_iff {α : Ordinal.{u}} {x y : HSet.{u}} :
    Approx α x y ↔ ∀ β < α,
      (∀ x' ∈ x, ∃ y' ∈ y, Approx β x' y') ∧ (∀ y' ∈ y, ∃ x' ∈ x, Approx β x' y') := by
  unfold Approx
  rw [WellFounded.fix_eq]

theorem approx_zero (x y : HSet.{u}) : Approx 0 x y :=
  approx_iff.mpr fun _ h => absurd h (not_lt_of_ge zero_le)

theorem Approx.mono {α β : Ordinal.{u}} {x y : HSet.{u}} (h : β ≤ α) (hα : Approx α x y) :
    Approx β x y :=
  approx_iff.mpr fun γ hγ => approx_iff.mp hα γ (hγ.trans_le h)

theorem approx_refl (α : Ordinal.{u}) : ∀ x : HSet.{u}, Approx α x x := by
  refine WellFoundedLT.induction (motive := fun α => ∀ x : HSet.{u}, Approx α x x) α ?_
  intro α ih x
  exact approx_iff.mpr fun β hβ =>
    ⟨fun x' hx' => ⟨x', hx', ih β hβ x'⟩, fun y' hy' => ⟨y', hy', ih β hβ y'⟩⟩

theorem Approx.symm {α : Ordinal.{u}} : ∀ {x y : HSet.{u}}, Approx α x y → Approx α y x := by
  refine WellFoundedLT.induction (motive := fun α => ∀ {x y : HSet.{u}}, Approx α x y → Approx α y x) α ?_
  intro α ih x y h
  refine approx_iff.mpr fun β hβ => ⟨fun y' hy' => ?_, fun x' hx' => ?_⟩
  · obtain ⟨x', hx', a⟩ := (approx_iff.mp h β hβ).2 y' hy'
    exact ⟨x', hx', ih β hβ a⟩
  · obtain ⟨y', hy', a⟩ := (approx_iff.mp h β hβ).1 x' hx'
    exact ⟨y', hy', ih β hβ a⟩

/-- Equal hypersets agree to every depth. -/
theorem approx_of_eq {x y : HSet.{u}} (h : x = y) (α : Ordinal.{u}) : Approx α x y :=
  h ▸ approx_refl α x

/-! ## Agreement to every depth below a regular bound is equality -/

/-- For `b` with fewer than `κ` members, `κ` regular: if `a` agrees with `b` to every depth below
`κ`, each member of `a` has one partner in `b` that agrees with it to every depth below `κ`. -/
theorem exists_partner {κ : Cardinal.{u}} (hreg : κ.IsRegular) {a b : HSet.{u}}
    (hb : SmallMembers κ b) (hab : ∀ α < κ.ord, Approx α a b) {a' : HSet.{u}} (ha' : a' ∈ a) :
    ∃ b' ∈ b, ∀ α < κ.ord, Approx α a' b' := by
  classical
  obtain ⟨ι, g, hι, hg⟩ := hb
  by_contra none
  have bad : ∀ i, ∃ α < κ.ord, ¬ Approx α a' (g i) := by
    intro i
    by_contra hi
    apply none
    refine ⟨g i, (hg _).mpr ⟨i, rfl⟩, fun α hα => ?_⟩
    by_contra hα'
    exact hi ⟨α, hα, hα'⟩
  choose β hβ hbad using bad
  have sup : (⨆ i, β i) < κ.ord :=
    Ordinal.iSup_lt_of_lt_cof (by rw [hreg.cof_ord]; exact hι) hβ
  have limit := Cardinal.isSuccLimit_ord hreg.aleph0_le
  obtain ⟨b', hb', happrox⟩ :=
    (approx_iff.mp (hab _ (limit.succ_lt sup)) _ (Order.lt_succ _)).1 a' ha'
  obtain ⟨i, rfl⟩ := (hg b').mp hb'
  exact hbad i (happrox.mono (Ordinal.le_iSup β i))

/-- **Agreement to every depth below a regular `κ` is equality**, for hereditarily small
hypersets. -/
theorem eq_of_forall_approx {κ : Cardinal.{u}} (hreg : κ.IsRegular) {x y : HSet.{u}}
    (hx : HerSmall κ x) (hy : HerSmall κ y) (h : ∀ α < κ.ord, Approx α x y) : x = y := by
  refine HSet.eq_of_isBisimulation
    (R := fun a b => HerSmall κ a ∧ HerSmall κ b ∧ ∀ α < κ.ord, Approx α a b) ?_ ⟨hx, hy, h⟩
  rintro a b ⟨ha, hb, hab⟩
  refine ⟨fun a' ha' => ?_, fun b' hb' => ?_⟩
  · obtain ⟨b', hb', h'⟩ := exists_partner hreg hb.smallMembers hab ha'
    exact ⟨b', hb', ha.mem ha', hb.mem hb', h'⟩
  · obtain ⟨a', ha', h'⟩ := exists_partner hreg ha.smallMembers
      (fun α hα => (hab α hα).symm) hb'
    exact ⟨a', ha', ha.mem ha', hb.mem hb', fun α hα => (h' α hα).symm⟩

/-- **Two hypersets are equal exactly when they agree to every depth.** -/
theorem eq_iff_forall_approx {x y : HSet.{u}} : x = y ↔ ∀ α, Approx α x y := by
  refine ⟨fun h α => approx_of_eq h α, fun h => ?_⟩
  obtain ⟨G, rfl⟩ := HSet.exists_mk x
  obtain ⟨H, rfl⟩ := HSet.exists_mk y
  set κ := Order.succ (max ℵ₀ (#G.Node + #H.Node))
  have hreg : κ.IsRegular := isRegular_succ (le_max_left _ _)
  have big : #G.Node + #H.Node < κ := (le_max_right _ _).trans_lt (Order.lt_succ _)
  exact eq_of_forall_approx hreg
    (herSmall_mk G ((self_le_add_right _ _).trans_lt big))
    (herSmall_mk H ((self_le_add_left _ _).trans_lt big)) fun α _ => h α

/-! ## Truncations: the agreement recorded by a well-founded set -/

/-- A presentation of the members of each hyperset without repetition, chosen once. -/
noncomputable def memberIndex (x : HSet.{u}) : Type u :=
  Classical.choose (exists_injective_members x)

noncomputable def memberValue (x : HSet.{u}) : memberIndex x → HSet.{u} :=
  Classical.choose (Classical.choose_spec (exists_injective_members x))

theorem memberValue_injective (x : HSet.{u}) : Function.Injective (memberValue x) :=
  (Classical.choose_spec (Classical.choose_spec (exists_injective_members x))).1

theorem mem_iff_memberValue {x y : HSet.{u}} : y ∈ x ↔ ∃ i, memberValue x i = y :=
  (Classical.choose_spec (Classical.choose_spec (exists_injective_members x))).2 y

/-- The truncation of `x` at depth `α`: the set of pairs `⟨β, trunc β x'⟩` for `β < α` and
`x' ∈ x`. It is a set of `ZFSet`, so it is well-founded. -/
noncomputable def trunc : Ordinal.{u} → HSet.{u} → ZFSet.{u} :=
  Ordinal.lt_wf.fix (C := fun _ => HSet.{u} → ZFSet.{u}) fun α ih x =>
    ZFSet.range fun p : α.ToType × memberIndex x =>
      ZFSet.pair ((Ordinal.typein (α := α.ToType) (· < ·)).toRelEmbedding p.1).toZFSet
        (ih _ (Ordinal.typein_lt_self p.1) (memberValue x p.2))

theorem trunc_eq (α : Ordinal.{u}) (x : HSet.{u}) :
    trunc α x = ZFSet.range fun p : α.ToType × memberIndex x =>
      ZFSet.pair ((Ordinal.typein (α := α.ToType) (· < ·)).toRelEmbedding p.1).toZFSet
        (trunc ((Ordinal.typein (α := α.ToType) (· < ·)).toRelEmbedding p.1)
          (memberValue x p.2)) := by
  unfold trunc
  rw [WellFounded.fix_eq]

theorem mem_trunc {α : Ordinal.{u}} {x : HSet.{u}} {w : ZFSet.{u}} :
    w ∈ trunc α x ↔ ∃ β < α, ∃ x' ∈ x, ZFSet.pair β.toZFSet (trunc β x') = w := by
  rw [trunc_eq, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨t, i⟩, rfl⟩
    exact ⟨_, Ordinal.typein_lt_self t, memberValue x i, mem_iff_memberValue.mpr ⟨i, rfl⟩, rfl⟩
  · rintro ⟨β, hβ, x', hx', rfl⟩
    obtain ⟨t, ht⟩ := Ordinal.typein_surj (α := α.ToType) (· < ·)
      (by rw [Ordinal.type_toType]; exact hβ)
    obtain ⟨i, rfl⟩ := mem_iff_memberValue.mp hx'
    exact ⟨⟨t, i⟩, by simp only [ht]⟩

/-- **The truncation records agreement**: `trunc α x = trunc α y ↔ Approx α x y`. -/
theorem trunc_eq_trunc_iff (α : Ordinal.{u}) :
    ∀ x y : HSet.{u}, trunc α x = trunc α y ↔ Approx α x y := by
  refine WellFoundedLT.induction (motive := fun α => ∀ x y : HSet.{u}, trunc α x = trunc α y ↔ Approx α x y) α ?_
  intro α ih x y
  rw [approx_iff]
  constructor
  · intro h β hβ
    have partner : ∀ {x y : HSet.{u}}, trunc α x = trunc α y → ∀ x' ∈ x,
        ∃ y' ∈ y, Approx β x' y' := by
      intro x y h x' hx'
      have member : ZFSet.pair β.toZFSet (trunc β x') ∈ trunc α y :=
        h ▸ mem_trunc.mpr ⟨β, hβ, x', hx', rfl⟩
      obtain ⟨γ, _, y', hy', e⟩ := mem_trunc.mp member
      obtain ⟨e₁, e₂⟩ := ZFSet.pair_inj.mp e
      obtain rfl := Ordinal.toZFSet_injective e₁
      exact ⟨y', hy', (ih γ hβ x' y').mp e₂.symm⟩
    refine ⟨partner h, fun y' hy' => ?_⟩
    obtain ⟨x', hx', a⟩ := partner h.symm y' hy'
    exact ⟨x', hx', a.symm⟩
  · intro h
    ext w
    constructor
    · intro hw
      obtain ⟨β, hβ, x', hx', rfl⟩ := mem_trunc.mp hw
      obtain ⟨y', hy', a⟩ := (h β hβ).1 x' hx'
      exact mem_trunc.mpr ⟨β, hβ, y', hy', by rw [(ih β hβ x' y').mpr a]⟩
    · intro hw
      obtain ⟨β, hβ, y', hy', rfl⟩ := mem_trunc.mp hw
      obtain ⟨x', hx', a⟩ := (h β hβ).2 y' hy'
      exact mem_trunc.mpr ⟨β, hβ, x', hx', by rw [(ih β hβ x' y').mpr a]⟩

/-- **A hyperset is determined by its well-founded truncations.** -/
theorem eq_iff_forall_trunc {x y : HSet.{u}} : x = y ↔ ∀ α, trunc α x = trunc α y := by
  rw [eq_iff_forall_approx]
  exact forall_congr' fun α => (trunc_eq_trunc_iff α x y).symm

/-! ## Transport into `V_κ` -/

theorem rank_pair_lt {a b : ZFSet.{u}} {o : Ordinal.{u}} (ho : Order.IsSuccLimit o)
    (ha : a.rank < o) (hb : b.rank < o) : (ZFSet.pair a b).rank < o := by
  rw [ZFSet.pair, ZFSet.rank_pair, ZFSet.rank_singleton, ZFSet.rank_pair]
  exact max_lt (ho.succ_lt (ho.succ_lt ha))
    (ho.succ_lt (max_lt (ho.succ_lt ha) (ho.succ_lt hb)))

/-- **The truncations below `κ` of a hereditarily small hyperset lie in `V_κ`**, `κ`
regular. -/
theorem rank_trunc_lt {κ : Cardinal.{u}} (hreg : κ.IsRegular) (α : Ordinal.{u}) :
    α < κ.ord → ∀ x : HSet.{u}, HerSmall κ x → (trunc α x).rank < κ.ord := by
  refine WellFoundedLT.induction (motive := fun α => α < κ.ord → ∀ x : HSet.{u}, HerSmall κ x → (trunc α x).rank < κ.ord) α ?_
  intro α ih hα x hx
  have limit := Cardinal.isSuccLimit_ord hreg.aleph0_le
  have small : #(memberIndex x) < κ :=
    (smallMembers_iff_of_injective (memberValue_injective x)
      (fun _ => mem_iff_memberValue)).mp hx.smallMembers
  rw [trunc_eq, ZFSet.rank_range]
  apply Ordinal.iSup_lt_of_lt_cof
  · rw [hreg.cof_ord, mk_prod, lift_id, lift_id, Cardinal.mk_toType]
    exact mul_lt_of_lt hreg.aleph0_le (Cardinal.lt_ord.mp hα) small
  · rintro ⟨t, i⟩
    have hβ := Ordinal.typein_lt_self t
    refine limit.succ_lt (rank_pair_lt limit ?_ ?_)
    · rw [Ordinal.rank_toZFSet]
      exact hβ.trans hα
    · exact ih _ hβ (hβ.trans hα) _ (hx.mem (mem_iff_memberValue.mpr ⟨i, rfl⟩))

theorem trunc_mem_vonNeumann {κ : Cardinal.{u}} (hreg : κ.IsRegular) {α : Ordinal.{u}}
    (hα : α < κ.ord) {x : HSet.{u}} (hx : x ∈ branching κ) : trunc α x ∈ V_ κ.ord :=
  ZFSet.mem_vonNeumann.mpr (rank_trunc_lt hreg α hα x (mem_branching.mp hx))

/-- **The truncations below `κ` determine the members of `B_κ`**, `κ` regular. -/
theorem eq_of_trunc_eq {κ : Cardinal.{u}} (hreg : κ.IsRegular) {x y : HSet.{u}}
    (hx : x ∈ branching κ) (hy : y ∈ branching κ) (h : ∀ α < κ.ord, trunc α x = trunc α y) :
    x = y :=
  eq_of_forall_approx hreg (mem_branching.mp hx) (mem_branching.mp hy)
    fun α hα => (trunc_eq_trunc_iff α x y).mp (h α hα)

/-- `B_κ` embeds into the sequences of `V_κ` indexed by the ordinals below `κ`. -/
theorem trunc_sequence_injective {κ : Cardinal.{u}} (hreg : κ.IsRegular) :
    Function.Injective fun x : {x : HSet.{u} // x ∈ branching κ} =>
      fun α : Set.Iio κ.ord => (⟨trunc α.1 x.1, trunc_mem_vonNeumann hreg α.2 x.2⟩ :
        {w : ZFSet.{u} // w ∈ V_ κ.ord}) :=
  fun x y h => Subtype.ext (eq_of_trunc_eq hreg x.2 y.2 fun α hα =>
    congrArg Subtype.val (congrFun h ⟨α, hα⟩))

/-! ## Controls -/

theorem mem_trunc_quineAtom {α : Ordinal.{u}} {w : ZFSet.{u}} :
    w ∈ trunc α HSet.quineAtom ↔ ∃ β < α, ZFSet.pair β.toZFSet (trunc β HSet.quineAtom) = w := by
  rw [mem_trunc]
  constructor
  · rintro ⟨β, hβ, x', hx', rfl⟩
    rw [HSet.mem_quineAtom.mp hx']
    exact ⟨β, hβ, rfl⟩
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨β, hβ, _, HSet.quineAtom_mem_self, rfl⟩

/-- **The truncations of `Ω` are pairwise distinct** well-founded sets; `Ω` is not
well-founded (`HSet.not_wf_quineAtom`). -/
theorem trunc_quineAtom_injective :
    Function.Injective fun α : Ordinal.{u} => trunc α HSet.quineAtom := by
  have strict : ∀ α α' : Ordinal.{u}, α < α' → trunc α HSet.quineAtom ≠ trunc α' HSet.quineAtom := by
    intro α α' hlt equal
    have member : ZFSet.pair α.toZFSet (trunc α HSet.quineAtom) ∈ trunc α' HSet.quineAtom :=
      mem_trunc_quineAtom.mpr ⟨α, hlt, rfl⟩
    rw [← equal] at member
    obtain ⟨β, hβ, e⟩ := mem_trunc_quineAtom.mp member
    obtain ⟨e₁, _⟩ := ZFSet.pair_inj.mp e
    exact (Ordinal.toZFSet_injective e₁ ▸ hβ).false
  intro α α' equal
  rcases lt_trichotomy α α' with h | h | h
  · exact absurd equal (strict α α' h)
  · exact h
  · exact absurd equal.symm (strict α' α h)

/-- The `n`-fold singleton of `∅`. -/
def chain : ℕ → HSet.{u}
  | 0 => ∅
  | n + 1 => {chain n}

/-- The chains, without `Ω`. -/
noncomputable def chains : HSet.{u} :=
  HSet.range fun n : ULift.{u} ℕ => HSet.Presentation.choice.graph (chain n.down)

theorem mem_chains {y : HSet.{u}} : y ∈ chains ↔ ∃ n, chain n = y := by
  simp only [chains, HSet.mem_range, HSet.Presentation.choice.mk_graph]
  exact ⟨fun ⟨n, h⟩ => ⟨n.down, h⟩, fun ⟨n, h⟩ => ⟨⟨n⟩, h⟩⟩

theorem chain_wf : ∀ n, (chain.{u} n).WF
  | 0 => HSet.wf_empty
  | n + 1 => (chain_wf n).singleton

/-- The `n`-fold singleton agrees with `Ω` to depth `n`. -/
theorem approx_chain_quineAtom : ∀ n : ℕ, Approx (n : Ordinal.{u}) (chain.{u} n) HSet.quineAtom
  | 0 => approx_zero _ _
  | n + 1 => by
    refine approx_iff.mpr fun β hβ => ⟨fun x' hx' => ?_, fun y' hy' => ?_⟩
    · have hx : x' = chain n := HSet.mem_singleton.mp hx'
      refine ⟨HSet.quineAtom, HSet.quineAtom_mem_self, ?_⟩
      rw [hx]
      exact (approx_chain_quineAtom n).mono (Order.lt_succ_iff.mp (by simpa using hβ))
    · have hy : y' = HSet.quineAtom := HSet.mem_quineAtom.mp hy'
      refine ⟨chain n, HSet.mem_singleton_self _, ?_⟩
      rw [hy]
      exact (approx_chain_quineAtom n).mono (Order.lt_succ_iff.mp (by simpa using hβ))

/-- **Without a bound on branching, the finite depths do not suffice**: the chains and the
chains with `Ω` agree to every finite depth. -/
theorem chains_agree_to_finite_depth (n : ℕ) :
    Approx (n : Ordinal.{u}) chains (insert HSet.quineAtom chains) := by
  refine approx_iff.mpr fun β hβ => ⟨fun x' hx' => ?_, fun y' hy' => ?_⟩
  · exact ⟨x', HSet.mem_insert_iff.mpr (Or.inr hx'), approx_refl β x'⟩
  · rcases HSet.mem_insert_iff.mp hy' with rfl | hy'
    · refine ⟨chain n, mem_chains.mpr ⟨n, rfl⟩, ?_⟩
      exact (approx_chain_quineAtom n).mono hβ.le
    · exact ⟨y', hy', approx_refl β y'⟩

/-- The chains and the chains with `Ω` are different: `Ω` is not a chain. -/
theorem chains_ne_chains_with_quineAtom :
    chains.{u} ≠ insert HSet.quineAtom chains := by
  intro equal
  have member : HSet.quineAtom.{u} ∈ chains := equal ▸ HSet.mem_insert_iff.mpr (Or.inl rfl)
  obtain ⟨n, hn⟩ := mem_chains.mp member
  exact HSet.not_wf_quineAtom (hn ▸ chain_wf n)

#print axioms IsMembershipMap.eq_ofZFSet_of_induction
#print axioms IsMembershipMap.eq_ofZFSet_of_coinduction
#print axioms exists_ofZFSet_iff_wf
#print axioms eq_of_forall_approx
#print axioms eq_iff_forall_approx
#print axioms trunc_eq_trunc_iff
#print axioms eq_iff_forall_trunc
#print axioms trunc_mem_vonNeumann
#print axioms eq_of_trunc_eq
#print axioms trunc_quineAtom_injective
#print axioms chains_agree_to_finite_depth

end Mettapedia.SetTheory.OpenTower.AntiFounded
