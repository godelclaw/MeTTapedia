import Mettapedia.TypeTheory.MahloUniverses.VonNeumannUniverse

/-!
# A model of Mahlo reflection: the universe of `V_κ` at a Mahlo cardinal

For an inaccessible `κ`, with the inaccessible levels `V_μ` (`μ < κ` inaccessible) as the ordinary
subuniverses of the Tarski universe of `V_κ`:

* `IsMahlo.mahloReflection`: if `κ` is Mahlo, every internal family operator has an
  inaccessible level closed on its families under the operator. The proof bounds the operator on
  the families lying below each `α < κ`; the resulting ordinal function has a club of closure
  points, which meets the stationary set of inaccessibles.
* `isMahlo_of_mahloReflection`: conversely, reflection forces `κ` to be Mahlo. The
  separating operator (`boundOperator`) depends only on the cardinality of the index type of a
  family, so it respects equivalence of families.
* `mahloReflection_iff_isMahlo`: the two together.

Controls.
* `IsLeastInaccessible.not_mahloReflection`: at the least inaccessible reflection
  fails; with the ordinary subuniverses relaxed to the code families of all nonempty closed
  members, it still fails for the stated operator `omegaOperator`
  (`IsLeastInaccessible.not_reflects_omegaOperator`).
* `IsLeastInaccessibleLimit.not_mahloReflection`: at the least inaccessible limit of
  inaccessibles, inaccessible levels exist below every ordinal of the level, and reflection still
  fails.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MahloUniverses

open Mettapedia.TypeTheory.UniverseClosureProfiles
open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
open Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels
open Cardinal
open scoped ZFSet Ordinal

universe u

noncomputable section

variable {κ : Cardinal.{u}}

/-! ## Families lying below an ordinal -/

/-- A family of `V_κ` lies below `β` when its index set and all its fibre sets have rank below
`β`. -/
def LiesBelow (F : (vonNeumannUniverse κ).InternalFamily) (β : Ordinal.{u}) : Prop :=
  F.1.1.rank < β ∧ ∀ index, (F.2 index).1.rank < β

/-- Negative example: no family lies below `0`. -/
theorem not_liesBelow_zero (F : (vonNeumannUniverse κ).InternalFamily) : ¬ LiesBelow F 0 :=
  fun h => not_lt_of_ge zero_le h.1

theorem LiesBelow.mono {F : (vonNeumannUniverse κ).InternalFamily} {β γ : Ordinal.{u}}
    (h : LiesBelow F β) (hβγ : β ≤ γ) : LiesBelow F γ :=
  ⟨h.1.trans_le hβγ, fun index => (h.2 index).trans_le hβγ⟩

/-- A strong limit cardinal is closed under cardinal exponentiation. -/
theorem power_lt_of_isStrongLimit {c a b : Cardinal.{u}} (hc : c.IsStrongLimit) (ha : a < c)
    (hb : b < c) : a ^ b < c :=
  calc a ^ b ≤ (2 ^ a) ^ b := Cardinal.power_le_power_right (Cardinal.cantor a).le
    _ = 2 ^ (a * b) := Cardinal.power_mul.symm
    _ < c := hc.isStrongPrelimit (Cardinal.mul_lt_of_lt hc.aleph0_le ha hb)

/-- A family whose index set and fibre sets lie in `V_μ`, for an inaccessible `μ`, lies below some
ordinal below `μ`. -/
theorem exists_liesBelow_of_mem {μ : Cardinal.{u}} (hμ : μ.IsInaccessible)
    (F : (vonNeumannUniverse κ).InternalFamily) (hbase : F.1.1 ∈ V_ μ.ord)
    (hfibre : ∀ index, (F.2 index).1 ∈ V_ μ.ord) : ∃ α < μ.ord, LiesBelow F α := by
  have limit := Cardinal.isSuccLimit_ord hμ.aleph0_lt.le
  obtain ⟨β, hβ, fibres⟩ := exists_bound_lt_ord (ι := (vonNeumannUniverse κ).El F.1)
    hμ.isRegular (by rw [Cardinal.lift_lt]; exact card_lt_of_mem_inaccessible hμ hbase)
    (fun index => (F.2 index).1.rank) (fun index => ZFSet.mem_vonNeumann.mp (hfibre index))
  refine ⟨max β (Order.succ F.1.1.rank),
    max_lt hβ (limit.succ_lt (ZFSet.mem_vonNeumann.mp hbase)), ?_, ?_⟩
  · exact (Order.lt_succ _).trans_le (le_max_right _ _)
  · exact fun index => (fibres index).trans_le (le_max_left _ _)

/-- Every family of `V_κ` lies below some ordinal below an inaccessible `κ`. -/
theorem exists_liesBelow (hκ : κ.IsInaccessible) (F : (vonNeumannUniverse κ).InternalFamily) :
    ∃ β < κ.ord, LiesBelow F β :=
  exists_liesBelow_of_mem hκ F F.1.2 (fun index => (F.2 index).2)

/-- The families lying below `α`, as a type: an index set of rank below `α`, and for each of its
members a set of rank below `α`. -/
abbrev LevelFamilyIndex (α : Ordinal.{u}) : Type (u + 1) :=
  Σ a : {x : ZFSet.{u} // x ∈ V_ α}, (Shrink.{u} a.1 → {x : ZFSet.{u} // x ∈ V_ α})

theorem mem_of_mem_vonNeumann_lt {α : Ordinal.{u}} (hα : α < κ.ord) {x : ZFSet.{u}}
    (hx : x ∈ V_ α) : x ∈ V_ κ.ord :=
  ZFSet.mem_vonNeumann.mpr ((ZFSet.mem_vonNeumann.mp hx).trans hα)

/-- The family of `V_κ` named by an element of `LevelFamilyIndex α`. -/
def LevelFamilyIndex.family {α : Ordinal.{u}} (hα : α < κ.ord) (t : LevelFamilyIndex α) :
    (vonNeumannUniverse κ).InternalFamily :=
  ⟨⟨t.1.1, mem_of_mem_vonNeumann_lt hα t.1.2⟩,
    fun index => ⟨(t.2 index).1, mem_of_mem_vonNeumann_lt hα (t.2 index).2⟩⟩

/-- Every family lying below `α` is named by an element of `LevelFamilyIndex α`. -/
theorem LiesBelow.exists_family_eq {α : Ordinal.{u}} (hα : α < κ.ord)
    {F : (vonNeumannUniverse κ).InternalFamily} (h : LiesBelow F α) :
    ∃ t : LevelFamilyIndex α, LevelFamilyIndex.family hα t = F :=
  ⟨⟨⟨F.1.1, ZFSet.mem_vonNeumann.mpr h.1⟩,
    fun index => ⟨(F.2 index).1, ZFSet.mem_vonNeumann.mpr (h.2 index)⟩⟩, rfl⟩

/-- **Fewer than `κ` families lie below each `α < κ`.** -/
theorem card_levelFamilyIndex_lt (hκ : κ.IsInaccessible) {α : Ordinal.{u}} (hα : α < κ.ord) :
    #(LevelFamilyIndex α) < Cardinal.lift.{u + 1} κ := by
  have levelSmall : (V_ α).card < κ := by
    rw [ZFSet.card_vonNeumann, ← hκ.preBeth_ord]
    exact Cardinal.preBeth_strictMono hα
  rw [Cardinal.mk_sigma]
  apply Cardinal.sum_lt_lift_of_isRegular.{u + 1, u + 1} hκ.isRegular.lift
  · rw [ZFSet.cardinalMk_coe_sort, Cardinal.lift_lift, Cardinal.lift_lt]
    exact levelSmall
  · intro a
    have memberSmall : a.1.card < κ :=
      card_lt_of_mem_inaccessible hκ (mem_of_mem_vonNeumann_lt hα a.2)
    rw [Cardinal.mk_arrow, ZFSet.cardinalMk_coe_sort, Cardinal.lift_lift]
    change Cardinal.lift.{u + 1} (V_ α).card ^ Cardinal.lift.{u + 1} a.1.card <
      Cardinal.lift.{u + 1} κ
    rw [← Cardinal.lift_power, Cardinal.lift_lt]
    exact power_lt_of_isStrongLimit hκ.isStrongLimit levelSmall memberSmall

/-- **The operator is bounded on the families below each `α < κ`.** -/
theorem exists_bound_levelFamilies (hκ : κ.IsInaccessible)
    (operator : (vonNeumannUniverse κ).FamilyOperator) {α : Ordinal.{u}} (hα : α < κ.ord) :
    ∃ β < κ.ord, ∀ F, LiesBelow F α → LiesBelow (operator F) β := by
  choose b hbκ hb using
    fun t : LevelFamilyIndex α => exists_liesBelow hκ (operator (LevelFamilyIndex.family hα t))
  obtain ⟨β, hβ, above⟩ := exists_bound_lt_ord hκ.isRegular
    (by simpa using card_levelFamilyIndex_lt hκ hα) b hbκ
  refine ⟨β, hβ, fun F hF => ?_⟩
  obtain ⟨t, rfl⟩ := hF.exists_family_eq hα
  exact (hb t).mono (above t).le

/-- A family lying below `μ` is equivalent to the decoding of a family drawn from the code
family of `V_μ`. -/
theorem exists_subuniverseFamily_equiv {μ : Cardinal.{u}} (hμκ : μ < κ)
    {G : (vonNeumannUniverse κ).InternalFamily} (hG : LiesBelow G μ.ord) :
    ∃ image : (vonNeumannUniverse κ).SubuniverseFamily (levelFamily μ hμκ),
      Nonempty ((vonNeumannUniverse κ).InternalFamilyEquiv G image.decode) := by
  let a : (vonNeumannUniverse κ).El (levelCode μ hμκ) :=
    equivShrink _ ⟨G.1.1, ZFSet.mem_vonNeumann.mpr hG.1⟩
  have ha : G.1 = member (levelCode μ hμκ) a := Subtype.ext (by simp [member, a])
  let e := elCongr ha
  refine ⟨⟨a, fun j => equivShrink _
    ⟨(G.2 (e.symm j)).1, ZFSet.mem_vonNeumann.mpr (hG.2 _)⟩⟩, ⟨⟨e, fun index => elCongr ?_⟩⟩⟩
  apply Subtype.ext
  show (G.2 index).1 = ((equivShrink (V_ μ.ord : ZFSet.{u})).symm
    (equivShrink (V_ μ.ord : ZFSet.{u})
      ⟨(G.2 (e.symm (e index))).1, ZFSet.mem_vonNeumann.mpr (hG.2 _)⟩)).1
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-! ## Mahlo cardinals give reflection -/

/-- **A model of Mahlo reflection.** If `κ` is Mahlo, then in the Tarski universe of `V_κ` every
internal family operator has an inaccessible level `V_μ`, `μ < κ`, closed on its families under
the operator. -/
theorem IsMahlo.mahloReflection (hκ : IsMahlo κ) :
    MahloReflection (vonNeumannUniverse κ) (IsInaccessibleLevel κ) := by
  refine ⟨fun operator => ?_⟩
  have inaccessible := hκ.isInaccessible
  choose! g hgκ hg using
    fun α (hα : α < κ.ord) => exists_bound_levelFamilies inaccessible operator hα
  obtain ⟨μ, hμ, hμκ, closure⟩ := hκ.exists_inaccessible_closurePoint hgκ
  refine ⟨levelFamily μ hμκ, levelFamily_isInaccessibleLevel hμ hμκ, fun family => ?_⟩
  obtain ⟨α, hαμ, below⟩ := exists_liesBelow_of_mem hμ family.decode
    (member_mem (levelCode μ hμκ) family.1)
    (fun index => member_mem (levelCode μ hμκ) (family.2 index))
  have hακ : α < κ.ord := hαμ.trans (Cardinal.ord_lt_ord.mpr hμκ)
  exact exists_subuniverseFamily_equiv hμκ
    ((hg α hακ family.decode below).mono (closure α hαμ).le)

/-! ## Reflection forces Mahlo -/

/-- Below an inaccessible `κ`, the values of a bounded ordinal function on the ordinals of
cardinality at most `c < κ` have a common bound below `κ`. -/
theorem exists_bound_card_le (hκ : κ.IsInaccessible) {f : Ordinal.{u} → Ordinal.{u}}
    (hf : ∀ α < κ.ord, f α < κ.ord) {c : Cardinal.{u}} (hc : c < κ) :
    ∃ β < κ.ord, ∀ α < (Order.succ c).ord, f α < β := by
  have succBelow : Order.succ c < κ := hκ.isSuccLimit.succ_lt hc
  obtain ⟨β, hβ, above⟩ := exists_bound_lt_ord (ι := Set.Iio (Order.succ c).ord) hκ.isRegular
    (by
      rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift, Cardinal.lift_lt, Cardinal.card_ord]
      exact succBelow)
    (fun α => f α.1) (fun α => hf α.1 (α.2.trans (Cardinal.ord_lt_ord.mpr succBelow)))
  exact ⟨β, hβ, fun α hα => above ⟨α, hα⟩⟩

/-- The bound of `exists_bound_card_le`, as a function of the cardinal. -/
def cardinalBound (hκ : κ.IsInaccessible) (f : Ordinal.{u} → Ordinal.{u})
    (hf : ∀ α < κ.ord, f α < κ.ord) (c : Cardinal.{u}) : Ordinal.{u} :=
  if hc : c < κ then Classical.choose (exists_bound_card_le hκ hf hc) else 0

theorem cardinalBound_lt (hκ : κ.IsInaccessible) {f : Ordinal.{u} → Ordinal.{u}}
    (hf : ∀ α < κ.ord, f α < κ.ord) (c : Cardinal.{u}) : cardinalBound hκ f hf c < κ.ord := by
  unfold cardinalBound
  split_ifs with hc
  · exact (Classical.choose_spec (exists_bound_card_le hκ hf hc)).1
  · exact Cardinal.ord_pos.mpr hκ.pos

theorem lt_cardinalBound (hκ : κ.IsInaccessible) {f : Ordinal.{u} → Ordinal.{u}}
    (hf : ∀ α < κ.ord, f α < κ.ord) {c : Cardinal.{u}} (hc : c < κ) {α : Ordinal.{u}}
    (hα : α < (Order.succ c).ord) : f α < cardinalBound hκ f hf c := by
  unfold cardinalBound
  rw [dif_pos hc]
  exact (Classical.choose_spec (exists_bound_card_le hκ hf hc)).2 α hα

/-- **The separating operator.** It sends a family whose index type has cardinality `c` to a
family whose index set is an ordinal bounding `f` on the ordinals of cardinality at most `c`. It
depends only on the cardinality of the index type. -/
def boundOperator (hκ : κ.IsInaccessible) (f : Ordinal.{u} → Ordinal.{u})
    (hf : ∀ α < κ.ord, f α < κ.ord) : (vonNeumannUniverse κ).FamilyOperator :=
  fun F => ⟨⟨(cardinalBound hκ f hf #((vonNeumannUniverse κ).El F.1)).toZFSet,
    ZFSet.mem_vonNeumann.mpr (by rw [Ordinal.rank_toZFSet]; exact cardinalBound_lt hκ hf _)⟩,
    fun _ => F.1⟩

/-- An inaccessible level closed on its families under `boundOperator f` is a closure point of
`f`. -/
theorem closurePoint_of_closed_boundOperator (hκ : κ.IsInaccessible)
    {f : Ordinal.{u} → Ordinal.{u}} (hf : ∀ α < κ.ord, f α < κ.ord) {μ : Cardinal.{u}}
    (hμ : μ.IsInaccessible) (hμκ : μ < κ)
    (closed : (vonNeumannUniverse κ).ClosedOnSubuniverseFamilies (boundOperator hκ f hf)
      (levelFamily μ hμκ)) :
    ∀ α < μ.ord, f α < μ.ord := by
  intro α hα
  have hx : α.toZFSet ∈ V_ μ.ord :=
    ZFSet.mem_vonNeumann.mpr (by rw [Ordinal.rank_toZFSet]; exact hα)
  let a : (vonNeumannUniverse κ).El (levelCode μ hμκ) := equivShrink _ ⟨α.toZFSet, hx⟩
  obtain ⟨image, ⟨e⟩⟩ := closed ⟨a, fun _ => a⟩
  have indexSize : #((vonNeumannUniverse κ).El (member (levelCode μ hμκ) a)) = α.card := by
    rw [card_el]
    simp [member, a, Ordinal.card_toZFSet]
  have hακ : α.card < κ :=
    Cardinal.lt_ord.mp (hα.trans (Cardinal.ord_lt_ord.mpr hμκ))
  have bound : f α < cardinalBound hκ f hf α.card :=
    lt_cardinalBound hκ hf hακ (Cardinal.lt_ord.mpr (Order.lt_succ_of_le le_rfl))
  have sizes : (cardinalBound hκ f hf α.card).toZFSet.card =
      (member (levelCode μ hμκ) image.1).1.card := by
    rw [← indexSize]
    exact Cardinal.mk_congr e.onBase
  rw [Ordinal.card_toZFSet] at sizes
  have small : (member (levelCode μ hμκ) image.1).1.card < μ :=
    card_lt_of_mem_inaccessible hμ (member_mem (levelCode μ hμκ) image.1)
  exact bound.trans (Cardinal.lt_ord.mpr (sizes ▸ small))

/-- **Reflection forces Mahlo.** If every internal family operator of the universe of `V_κ` has
an inaccessible level closed on its families under it, then the inaccessible `κ` is Mahlo. -/
theorem isMahlo_of_mahloReflection (hκ : κ.IsInaccessible)
    (h : MahloReflection (vonNeumannUniverse κ) (IsInaccessibleLevel κ)) :
    IsMahlo κ := by
  refine isMahlo_of_forall_closurePoint hκ fun f hf => ?_
  obtain ⟨_, ⟨μ, hμ, hμκ, rfl⟩, closed⟩ := h.reflect (boundOperator hκ f hf)
  exact ⟨μ, hμ, hμκ, closurePoint_of_closed_boundOperator hκ hf hμ hμκ closed⟩

/-- **Characterization.** For inaccessible `κ`, the universe of `V_κ` has Mahlo reflection into
its inaccessible levels exactly when `κ` is Mahlo. -/
theorem mahloReflection_iff_isMahlo (hκ : κ.IsInaccessible) :
    MahloReflection (vonNeumannUniverse κ) (IsInaccessibleLevel κ) ↔ IsMahlo κ :=
  ⟨isMahlo_of_mahloReflection hκ, IsMahlo.mahloReflection⟩

/-! ## Controls -/

/-- **The separating operator at a non-Mahlo cardinal.** At an inaccessible cardinal that is not
Mahlo, some bounded ordinal function `f` has no inaccessible closure point, and `boundOperator f`
has no reflecting inaccessible level. -/
theorem exists_not_reflected_of_not_isMahlo (hκ : κ.IsInaccessible) (hnot : ¬ IsMahlo κ) :
    ∃ (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ α < κ.ord, f α < κ.ord),
      ¬ ReflectsOperator (vonNeumannUniverse κ) (IsInaccessibleLevel κ)
        (boundOperator hκ f hf) := by
  by_contra hall
  refine hnot (isMahlo_of_forall_closurePoint hκ fun f hf => ?_)
  by_contra hnone
  refine hall ⟨f, hf, ?_⟩
  rintro ⟨_, ⟨μ, hμ, hμκ, rfl⟩, closed⟩
  exact hnone ⟨μ, hμ, hμκ, closurePoint_of_closed_boundOperator hκ hf hμ hμκ closed⟩

/-- At the least inaccessible cardinal, reflection into inaccessible levels fails. -/
theorem IsLeastInaccessible.not_mahloReflection (hκ : IsLeastInaccessible κ) :
    ¬ MahloReflection (vonNeumannUniverse κ) (IsInaccessibleLevel κ) :=
  fun h => hκ.not_isMahlo (isMahlo_of_mahloReflection hκ.1 h)

/-- Unconditionally, one universe level up, some inaccessible level fails reflection into its
inaccessible levels: the least inaccessible cardinal there. -/
theorem exists_inaccessible_not_mahloReflection :
    ∃ κ : Cardinal.{u + 1}, κ.IsInaccessible ∧
      ¬ MahloReflection (vonNeumannUniverse κ) (IsInaccessibleLevel κ) := by
  obtain ⟨κ, hκ⟩ := exists_isLeastInaccessible.{u}
  exact ⟨κ, hκ.1, hκ.not_mahloReflection⟩

/-- The relaxed ordinary subuniverses: code families of nonempty closed members of `V_κ`. -/
def IsClosedLevel (κ : Cardinal.{u}) (F : (vonNeumannUniverse κ).InternalFamily) : Prop :=
  ∃ W : (vonNeumannUniverse κ).Code, Closed W.1 ∧ W.1.Nonempty ∧ F = memberFamily W

/-- Negative example: the code family of the empty set is not a closed level. -/
theorem not_isClosedLevel_empty (hκ : 0 < κ) :
    ¬ IsClosedLevel κ (memberFamily (emptyCode hκ)) := by
  rintro ⟨W, _, ⟨x, hx⟩, hW⟩
  have same : W = emptyCode hκ := (congrArg Sigma.fst hW).symm
  rw [same] at hx
  exact ZFSet.notMem_empty x hx

/-- Every inaccessible level is a closed level. -/
theorem IsInaccessibleLevel.isClosedLevel {F : (vonNeumannUniverse κ).InternalFamily}
    (hF : IsInaccessibleLevel κ F) : IsClosedLevel κ F := by
  obtain ⟨μ, hμ, hμκ, rfl⟩ := hF
  refine ⟨levelCode μ hμκ, inaccessible_closed hμ, ⟨∅, ?_⟩, rfl⟩
  change (∅ : ZFSet.{u}) ∈ V_ μ.ord
  rw [ZFSet.mem_vonNeumann, ZFSet.rank_empty]
  exact Cardinal.ord_pos.mpr hμ.pos

/-- At a Mahlo cardinal, reflection also holds into the relaxed closed levels. -/
theorem IsMahlo.mahloReflection_closedLevel (hκ : IsMahlo κ) :
    MahloReflection (vonNeumannUniverse κ) (IsClosedLevel κ) :=
  hκ.mahloReflection.mono fun _ hF => hF.isClosedLevel

/-- The operator sending every family to a family indexed by `ω`. -/
def omegaOperator (hκ : ℵ₀ < κ) : (vonNeumannUniverse κ).FamilyOperator :=
  fun F => ⟨⟨(ω : Ordinal.{u}).toZFSet, ZFSet.mem_vonNeumann.mpr (by
    rw [Ordinal.rank_toZFSet, ← Cardinal.ord_aleph0]
    exact Cardinal.ord_lt_ord.mpr hκ)⟩, fun _ => F.1⟩

/-- **The least inaccessible against a stated operator.** At the least inaccessible cardinal, even
the relaxed closed levels admit no level closed on its families under `omegaOperator`: the only
nonempty closed member is `V_ω`, whose members are finite. -/
theorem IsLeastInaccessible.not_reflects_omegaOperator (hκ : IsLeastInaccessible κ) :
    ¬ ReflectsOperator (vonNeumannUniverse κ) (IsClosedLevel κ)
      (omegaOperator hκ.1.aleph0_lt) := by
  rintro ⟨_, ⟨W, hW, ⟨x, hx⟩, rfl⟩, closed⟩
  have rankW : W.1.rank = ω := by
    rcases (closed_iff W.1).mp hW with hempty | homega | ⟨μ, hμ, hμW⟩
    · rw [hempty] at hx
      exact absurd hx (ZFSet.notMem_empty x)
    · rw [homega, ZFSet.rank_vonNeumann]
    · have hμκ : μ < κ := by
        have member := W.2
        rw [hμW] at member
        exact Cardinal.ord_lt_ord.mp (ZFSet.vonNeumann_mem_vonNeumann_iff.mp member)
      exact absurd (hκ.2 μ hμ) (not_le.mpr hμκ)
  let a : (vonNeumannUniverse κ).El W := equivShrink _ ⟨x, hx⟩
  obtain ⟨image, ⟨e⟩⟩ := closed ⟨a, fun _ => a⟩
  have sizes : (ω : Ordinal.{u}).toZFSet.card = (member W image.1).1.card :=
    Cardinal.mk_congr e.onBase
  rw [Ordinal.card_toZFSet, Ordinal.card_omega0] at sizes
  have finite := card_lt_card_rank hW (member_mem W image.1)
  rw [rankW, Ordinal.card_omega0, ← sizes] at finite
  exact lt_irrefl _ finite

/-- At the least inaccessible limit of inaccessibles, inaccessible levels lie above every ordinal
of the level. -/
theorem IsLeastInaccessibleLimit.exists_isInaccessibleLevel (hκ : IsLeastInaccessibleLimit κ)
    {α : Ordinal.{u}} (hα : α < κ.ord) :
    ∃ μ : Cardinal.{u}, ∃ hμκ : μ < κ, α < μ.ord ∧ IsInaccessibleLevel κ (levelFamily μ hμκ) := by
  obtain ⟨μ, hμ, above, hμκ⟩ := hκ.2.1 α hα
  exact ⟨μ, hμκ, above, levelFamily_isInaccessibleLevel hμ hμκ⟩

/-- **Reflection fails with plenty of levels.** At the least inaccessible limit of inaccessibles,
inaccessible levels are unbounded, and reflection into them still fails. -/
theorem IsLeastInaccessibleLimit.not_mahloReflection
    (hκ : IsLeastInaccessibleLimit κ) :
    ¬ MahloReflection (vonNeumannUniverse κ) (IsInaccessibleLevel κ) :=
  fun h => hκ.not_isMahlo (isMahlo_of_mahloReflection hκ.1 h)

end

#print axioms card_levelFamilyIndex_lt
#print axioms exists_bound_levelFamilies
#print axioms exists_subuniverseFamily_equiv
#print axioms IsMahlo.mahloReflection
#print axioms closurePoint_of_closed_boundOperator
#print axioms isMahlo_of_mahloReflection
#print axioms mahloReflection_iff_isMahlo
#print axioms exists_not_reflected_of_not_isMahlo
#print axioms IsLeastInaccessible.not_mahloReflection
#print axioms exists_inaccessible_not_mahloReflection
#print axioms IsMahlo.mahloReflection_closedLevel
#print axioms IsLeastInaccessible.not_reflects_omegaOperator
#print axioms IsLeastInaccessibleLimit.exists_isInaccessibleLevel
#print axioms IsLeastInaccessibleLimit.not_mahloReflection

end Mettapedia.TypeTheory.MahloUniverses
