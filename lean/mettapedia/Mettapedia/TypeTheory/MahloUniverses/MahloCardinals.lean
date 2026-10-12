import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels

/-!
# Mahlo cardinals

A cardinal `κ` is **Mahlo** when it is inaccessible and the inaccessible cardinals below it form a
stationary set of ordinals below `κ`. Clubs and stationary sets are Mathlib's `IsClub` and
`IsStationary`, read on the well-ordered type `Set.Iio κ.ord` of ordinals below `κ`.

* `exists_bound_lt_ord`: fewer than `κ` ordinals below a regular `κ` are bounded below `κ`; the
  index type may live in any universe.
* `isClub_closurePoints`: below a regular uncountable `κ`, the closure points of an ordinal
  function that maps ordinals below `κ` below `κ` form a club.
* `isMahlo_iff_forall_closurePoint`: `κ` is Mahlo iff it is inaccessible and every such function
  has an inaccessible closure point below `κ`. This is the form used to build Mahlo universes.
* `IsMahlo.isLimitOfInaccessibles`, `IsMahlo.universeLawInside`: a Mahlo cardinal is a limit of
  inaccessibles, so inside `V_κ` every set lies in a closed set (the local form of
  `CofinalInaccessibles`, read through `universeLawInside_vonNeumann_iff`).

Controls. `ℵ₀` is not Mahlo; the least inaccessible cardinal is not Mahlo, and one exists one
universe level up (`exists_inaccessible_not_isMahlo`); the least inaccessible limit of
inaccessibles is not Mahlo although the law "every set lies in a closed set" holds inside its
level (`IsLeastInaccessibleLimit.not_isMahlo`, `IsLeastInaccessibleLimit.universeLawInside`).
No positive instance of `IsMahlo` is constructed: a Mahlo cardinal exceeds the consistency
strength of the foundations used here, so every positive statement takes it as a hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MahloUniverses

open Cardinal Order Set
open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
open Mettapedia.SetTheory.OpenTower.Strength.StageFamilies
open Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels
open scoped Ordinal ZFSet

universe u v

/-! ## Bounds below a regular cardinal -/

/-- **Regularity bounds a small family of ordinals.** Fewer than `κ` ordinals below a regular
cardinal `κ` have a common strict bound below `κ`. The index type may live in any universe. -/
theorem exists_bound_lt_ord {ι : Type v} {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (hι : Cardinal.lift.{u} #ι < Cardinal.lift.{v} κ) (f : ι → Ordinal.{u})
    (hf : ∀ i, f i < κ.ord) : ∃ β < κ.ord, ∀ i, f i < β := by
  have bounded : BddAbove (Set.range f) := ⟨κ.ord, by rintro _ ⟨i, rfl⟩; exact (hf i).le⟩
  have supBelow : ⨆ i, f i < κ.ord := by
    apply Ordinal.lift_iSup_lt_of_lt_cof _ hf
    rw [← Ordinal.lift_cof, hκ.cof_ord]
    exact hι
  exact ⟨Order.succ (⨆ i, f i), (Cardinal.isSuccLimit_ord hκ.aleph0_le).succ_lt supBelow,
    fun i => Order.lt_succ_of_le (le_ciSup bounded i)⟩

/-! ## Closure points -/

/-- The closure points of an ordinal function below `o`: the ordinals `μ < o` such that the
function sends every ordinal below `μ` to an ordinal below `μ`. -/
def closurePoints (o : Ordinal.{u}) (f : Ordinal.{u} → Ordinal.{u}) : Set (Iio o) :=
  {μ | ∀ α < μ.1, f α < μ.1}

/-- **The closure points form a club.** Below a regular uncountable cardinal `κ`, the closure
points of a function mapping ordinals below `κ` below `κ` are closed and unbounded. -/
theorem isClub_closurePoints {κ : Cardinal.{u}} (hκ : κ.IsRegular) (hω : ℵ₀ < κ)
    {f : Ordinal.{u} → Ordinal.{u}} (hf : ∀ α < κ.ord, f α < κ.ord) :
    IsClub (closurePoints κ.ord f) where
  dirSupClosed := by
    intro d hd _ _ a ha
    show ∀ α < a.1, f α < a.1
    intro α hα
    obtain ⟨c, hc, hlt⟩ :=
      (lt_isLUB_iff ha).mp (show (⟨α, hα.trans a.2⟩ : Iio κ.ord) < a from hα)
    exact (hd hc α hlt).trans_le (Subtype.coe_le_coe.mpr (ha.1 hc))
  isCofinal := by
    intro a
    have bound : ∀ γ < κ.ord, ∃ β < κ.ord, ∀ α : Iio γ, f α.1 < β := by
      intro γ hγ
      refine exists_bound_lt_ord (ι := Iio γ) hκ ?_ (fun α => f α.1) (fun α => hf α.1 (α.2.trans hγ))
      rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_lift, Cardinal.lift_lt]
      exact Cardinal.lt_ord.mp hγ
    choose! g hgκ hg using bound
    let step : Ordinal.{u} → Ordinal.{u} := fun γ => max γ (g γ)
    have stepBelow : ∀ γ < κ.ord, step γ < κ.ord := fun γ hγ => max_lt hγ (hgκ γ hγ)
    have cofinality : ℵ₀ < κ.ord.cof := by rw [hκ.cof_ord]; exact hω
    have pointBelow : Ordinal.nfp step a.1 < κ.ord :=
      Ordinal.nfp_lt_ord cofinality stepBelow a.2
    refine ⟨⟨Ordinal.nfp step a.1, pointBelow⟩, ?_, Ordinal.le_nfp step a.1⟩
    intro α hα
    obtain ⟨n, hn⟩ := Ordinal.lt_nfp_iff.mp hα
    have iterBelow : step^[n] a.1 < κ.ord :=
      (Ordinal.iterate_le_nfp step a.1 n).trans_lt pointBelow
    calc f α < g (step^[n] a.1) := hg _ iterBelow ⟨α, hn⟩
      _ ≤ step (step^[n] a.1) := le_max_right _ _
      _ = step^[n + 1] a.1 := (Function.iterate_succ_apply' step n a.1).symm
      _ ≤ Ordinal.nfp step a.1 := Ordinal.iterate_le_nfp step a.1 (n + 1)

/-- Negative example for closure points: `1` is not a closure point of the successor function,
since the successor of `0` is not below `1`. -/
theorem one_not_mem_closurePoints_succ {o : Ordinal.{u}} (ho : 1 < o) :
    (⟨1, ho⟩ : Iio o) ∉ closurePoints o Order.succ := by
  intro h
  have := h 0 zero_lt_one
  rw [Order.succ_eq_add_one, zero_add] at this
  exact lt_irrefl _ this

/-! ## Examples of clubs and stationary sets below an ordinal -/

/-- Positive example of a club: the ordinals at or above a fixed `β` below `o`. -/
theorem isClub_tail {o β : Ordinal.{u}} (hβ : β < o) : IsClub {x : Iio o | β ≤ x.1} where
  dirSupClosed := by
    intro d hd hne _ a ha
    obtain ⟨c, hc⟩ := hne
    exact le_trans (hd hc) (Subtype.coe_le_coe.mpr (ha.1 hc))
  isCofinal := fun x => ⟨max x ⟨β, hβ⟩, le_max_right x ⟨β, hβ⟩, le_max_left _ _⟩

/-- **Negative example of a club.** Below an ordinal above `ω`, the ordinals other than `ω` are
not closed: `ω` is the supremum of the finite ordinals. -/
theorem not_isClub_ne_omega0 {o : Ordinal.{u}} (ho : ω < o) :
    ¬ IsClub {x : Iio o | x.1 ≠ ω} := by
  intro hC
  let d : Set (Iio o) := {x | x.1 < ω}
  have dC : d ⊆ {x : Iio o | x.1 ≠ ω} := fun x hx => hx.ne
  have dne : d.Nonempty := ⟨⟨0, Ordinal.omega0_pos.trans ho⟩, Ordinal.omega0_pos⟩
  have lub : IsLUB d ⟨ω, ho⟩ := by
    refine ⟨fun x hx => le_of_lt hx, fun b hb => ?_⟩
    by_contra notLe
    have bBelow : b.1 < ω := lt_of_not_ge notLe
    have succBelow : Order.succ b.1 < ω := Ordinal.isSuccLimit_omega0.succ_lt bBelow
    have mem : (⟨Order.succ b.1, succBelow.trans ho⟩ : Iio o) ∈ d := succBelow
    exact (Order.lt_succ b.1).not_ge (hb mem)
  exact (hC.isLUB_mem dC dne lub) rfl

/-- The same set is cofinal below a limit ordinal above `ω`: the failure in
`not_isClub_ne_omega0` is a failure of closure, not of unboundedness. -/
theorem isCofinal_ne_omega0 {o : Ordinal.{u}} (ho : ω < o) (hlimit : IsSuccLimit o) :
    IsCofinal {x : Iio o | x.1 ≠ ω} := by
  intro x
  by_cases hx : x.1 = ω
  · refine ⟨⟨Order.succ ω, hlimit.succ_lt ho⟩, (Order.lt_succ ω).ne', ?_⟩
    show x.1 ≤ Order.succ ω
    rw [hx]
    exact Order.le_succ ω
  · exact ⟨x, hx, le_rfl⟩

/-- Positive example of a stationary set: below a regular uncountable cardinal, the closure
points of any function bounded below the cardinal are stationary. -/
theorem isStationary_closurePoints {κ : Cardinal.{u}} (hκ : κ.IsRegular) (hω : ℵ₀ < κ)
    {f : Ordinal.{u} → Ordinal.{u}} (hf : ∀ α < κ.ord, f α < κ.ord) :
    IsStationary (closurePoints κ.ord f) := by
  have : Nonempty (Iio κ.ord) := ⟨⟨0, Cardinal.ord_pos.mpr (aleph0_pos.trans hω)⟩⟩
  refine (isClub_closurePoints hκ hω hf).isStationary ?_
  rw [Ordinal.cof_Iio, ← Ordinal.lift_cof, hκ.cof_ord]
  intro equal
  exact (lt_irrefl ℵ₀) (Cardinal.lift_eq_aleph0.mp equal ▸ hω)

/-- **Negative example of a stationary set.** A set bounded below `o` is not stationary: it misses
the club of ordinals at or above its bound. -/
theorem not_isStationary_bounded {o β : Ordinal.{u}} (hβ : β < o) :
    ¬ IsStationary {x : Iio o | x.1 < β} := by
  intro h
  obtain ⟨x, below, above⟩ := h (isClub_tail hβ)
  exact (lt_irrefl _) ((show x.1 < β from below).trans_le (show β ≤ x.1 from above))

/-! ## Mahlo cardinals -/

/-- The ordinals below `o` that are initial ordinals of inaccessible cardinals. -/
def inaccessiblesBelow (o : Ordinal.{u}) : Set (Iio o) :=
  {α | ∃ μ : Cardinal.{u}, μ.IsInaccessible ∧ μ.ord = α.1}

/-- Positive example: an inaccessible cardinal below `κ` gives a member of the set. -/
theorem ord_mem_inaccessiblesBelow {κ μ : Cardinal.{u}} (hμ : μ.IsInaccessible) (hμκ : μ < κ) :
    (⟨μ.ord, Cardinal.ord_lt_ord.mpr hμκ⟩ : Iio κ.ord) ∈ inaccessiblesBelow κ.ord :=
  ⟨μ, hμ, rfl⟩

/-- Negative example: `ω` is not the initial ordinal of an inaccessible cardinal. -/
theorem omega0_not_mem_inaccessiblesBelow {o : Ordinal.{u}} (ho : ω < o) :
    (⟨ω, ho⟩ : Iio o) ∉ inaccessiblesBelow o := by
  rintro ⟨μ, hμ, hμω⟩
  change μ.ord = ω at hμω
  rw [← Cardinal.ord_aleph0, Cardinal.ord_inj] at hμω
  exact (lt_irrefl _) (hμω ▸ hμ.aleph0_lt)

/-- **Mahlo cardinals.** `κ` is inaccessible and the inaccessible cardinals below `κ` form a
stationary subset of the ordinals below `κ`. -/
structure IsMahlo (κ : Cardinal.{u}) : Prop where
  isInaccessible : κ.IsInaccessible
  isStationary_inaccessiblesBelow : IsStationary (inaccessiblesBelow κ.ord)

/-- **Mahlo cardinals reflect closure.** Every ordinal function mapping ordinals below a Mahlo
cardinal below it has an inaccessible closure point below the cardinal. -/
theorem IsMahlo.exists_inaccessible_closurePoint {κ : Cardinal.{u}} (hκ : IsMahlo κ)
    {f : Ordinal.{u} → Ordinal.{u}} (hf : ∀ α < κ.ord, f α < κ.ord) :
    ∃ μ : Cardinal.{u}, μ.IsInaccessible ∧ μ < κ ∧ ∀ α < μ.ord, f α < μ.ord := by
  obtain ⟨x, ⟨μ, hμ, hx⟩, closure⟩ := hκ.isStationary_inaccessiblesBelow
    (isClub_closurePoints hκ.isInaccessible.isRegular hκ.isInaccessible.aleph0_lt hf)
  refine ⟨μ, hμ, Cardinal.ord_lt_ord.mp (hx ▸ x.2), fun α hα => ?_⟩
  rw [hx] at hα ⊢
  exact closure α hα

/-- Conversely, an inaccessible cardinal at which every bounded ordinal function has an
inaccessible closure point is Mahlo: every club contains the limit point it is forced to have at
such a closure point. -/
theorem isMahlo_of_forall_closurePoint {κ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    (h : ∀ f : Ordinal.{u} → Ordinal.{u}, (∀ α < κ.ord, f α < κ.ord) →
      ∃ μ : Cardinal.{u}, μ.IsInaccessible ∧ μ < κ ∧ ∀ α < μ.ord, f α < μ.ord) :
    IsMahlo κ := by
  refine ⟨hκ, fun C hC => ?_⟩
  have limit := Cardinal.isSuccLimit_ord hκ.aleph0_lt.le
  have : Nonempty (Iio κ.ord) := ⟨⟨0, Cardinal.ord_pos.mpr hκ.pos⟩⟩
  have next : ∀ α < κ.ord, ∃ c ∈ C, α < c.1 := by
    intro α hα
    obtain ⟨c, hc, above⟩ := hC.isCofinal ⟨Order.succ α, limit.succ_lt hα⟩
    exact ⟨c, hc, (Order.lt_succ α).trans_le above⟩
  choose! g hgC hg using next
  obtain ⟨μ, hμ, hμκ, closure⟩ := h (fun α => (g α).1) (fun α _ => (g α).2)
  have μBelow : μ.ord < κ.ord := Cardinal.ord_lt_ord.mpr hμκ
  have μpos : 0 < μ.ord := Cardinal.ord_pos.mpr hμ.pos
  let t : Set (Iio κ.ord) := {c | c ∈ C ∧ c.1 < μ.ord}
  have tC : t ⊆ C := fun c hc => hc.1
  have tne : t.Nonempty := ⟨g 0, hgC 0 (μpos.trans μBelow), closure 0 μpos⟩
  have lub : IsLUB t ⟨μ.ord, μBelow⟩ := by
    refine ⟨fun c hc => le_of_lt hc.2, fun b hb => ?_⟩
    by_contra notLe
    have bBelow : b.1 < μ.ord := lt_of_not_ge notLe
    have mem : g b.1 ∈ t := ⟨hgC b.1 b.2, closure b.1 bBelow⟩
    exact (hg b.1 b.2).not_ge (hb mem)
  exact ⟨⟨μ.ord, μBelow⟩, ⟨μ, hμ, rfl⟩, hC.isLUB_mem tC tne lub⟩

/-- **Characterization of Mahlo cardinals by closure points.** -/
theorem isMahlo_iff_forall_closurePoint {κ : Cardinal.{u}} :
    IsMahlo κ ↔ κ.IsInaccessible ∧ ∀ f : Ordinal.{u} → Ordinal.{u},
      (∀ α < κ.ord, f α < κ.ord) →
        ∃ μ : Cardinal.{u}, μ.IsInaccessible ∧ μ < κ ∧ ∀ α < μ.ord, f α < μ.ord :=
  ⟨fun hκ => ⟨hκ.isInaccessible, fun _ hf => hκ.exists_inaccessible_closurePoint hf⟩,
    fun ⟨hκ, h⟩ => isMahlo_of_forall_closurePoint hκ h⟩

/-! ## Limits of inaccessibles and the law inside `V_κ` -/

/-- The inaccessible cardinals below `κ` are unbounded below `κ`. This is the bounded form of
`CofinalInaccessibles`, which asks the same of all ordinals of the level. -/
def IsLimitOfInaccessibles (κ : Cardinal.{u}) : Prop :=
  ∀ α < κ.ord, ∃ μ : Cardinal.{u}, μ.IsInaccessible ∧ α < μ.ord ∧ μ < κ

/-- A Mahlo cardinal is a limit of inaccessible cardinals. -/
theorem IsMahlo.isLimitOfInaccessibles {κ : Cardinal.{u}} (hκ : IsMahlo κ) :
    IsLimitOfInaccessibles κ := by
  intro β hβ
  obtain ⟨μ, hμ, hμκ, closure⟩ :=
    hκ.exists_inaccessible_closurePoint (f := fun _ => β) (fun _ _ => hβ)
  exact ⟨μ, hμ, closure 0 (Cardinal.ord_pos.mpr hμ.pos), hμκ⟩

/-- Inside the level at a Mahlo cardinal, every set lies in a closed set. -/
theorem IsMahlo.universeLawInside {κ : Cardinal.{u}} (hκ : IsMahlo κ) :
    UniverseLawInside (V_ κ.ord) :=
  (universeLawInside_vonNeumann_iff hκ.isInaccessible).mpr hκ.isLimitOfInaccessibles

/-! ## Controls -/

/-- `ℵ₀` is not Mahlo: it is not even inaccessible. -/
theorem not_isMahlo_aleph0 : ¬ IsMahlo.{u} ℵ₀ :=
  fun h => (lt_irrefl _) h.isInaccessible.aleph0_lt

/-- `κ` is the least inaccessible cardinal of its level. -/
def IsLeastInaccessible (κ : Cardinal.{u}) : Prop :=
  κ.IsInaccessible ∧ ∀ μ : Cardinal.{u}, μ.IsInaccessible → κ ≤ μ

/-- Positive example: one universe level up, a least inaccessible cardinal exists, since the
cardinal of the lower level is inaccessible there. -/
theorem exists_isLeastInaccessible : ∃ κ : Cardinal.{u + 1}, IsLeastInaccessible κ := by
  have nonempty : {μ : Cardinal.{u + 1} | μ.IsInaccessible}.Nonempty :=
    ⟨_, Cardinal.IsInaccessible.univ.{u, u + 1}⟩
  exact ⟨sInf _, csInf_mem nonempty, fun μ hμ => csInf_le' hμ⟩

/-- Negative example: `ℵ₀` is not the least inaccessible cardinal. -/
theorem not_isLeastInaccessible_aleph0 : ¬ IsLeastInaccessible.{u} ℵ₀ :=
  fun h => (lt_irrefl _) h.1.aleph0_lt

/-- Below the least inaccessible cardinal there are no inaccessible cardinals. -/
theorem IsLeastInaccessible.inaccessiblesBelow_eq_empty {κ : Cardinal.{u}}
    (hκ : IsLeastInaccessible κ) : inaccessiblesBelow κ.ord = ∅ := by
  ext x
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨μ, hμ, hx⟩
  exact (hκ.2 μ hμ).not_gt (Cardinal.ord_lt_ord.mp (hx ▸ x.2))

/-- **The least inaccessible cardinal is not Mahlo.** -/
theorem IsLeastInaccessible.not_isMahlo {κ : Cardinal.{u}} (hκ : IsLeastInaccessible κ) :
    ¬ IsMahlo κ := fun h =>
  not_isStationary_empty (hκ.inaccessiblesBelow_eq_empty ▸ h.isStationary_inaccessiblesBelow)

/-- The least inaccessible cardinal is not a limit of inaccessibles. -/
theorem IsLeastInaccessible.not_isLimitOfInaccessibles {κ : Cardinal.{u}}
    (hκ : IsLeastInaccessible κ) : ¬ IsLimitOfInaccessibles κ := by
  intro h
  obtain ⟨μ, hμ, _, hμκ⟩ := h 0 (Cardinal.ord_pos.mpr hκ.1.pos)
  exact (hκ.2 μ hμ).not_gt hμκ

/-- Unconditionally, some inaccessible cardinal is not Mahlo. -/
theorem exists_inaccessible_not_isMahlo :
    ∃ κ : Cardinal.{u + 1}, κ.IsInaccessible ∧ ¬ IsMahlo κ := by
  obtain ⟨κ, hκ⟩ := exists_isLeastInaccessible.{u}
  exact ⟨κ, hκ.1, hκ.not_isMahlo⟩

/-- `κ` is the least inaccessible cardinal that is a limit of inaccessible cardinals. -/
def IsLeastInaccessibleLimit (κ : Cardinal.{u}) : Prop :=
  κ.IsInaccessible ∧ IsLimitOfInaccessibles κ ∧
    ∀ μ : Cardinal.{u}, μ.IsInaccessible → IsLimitOfInaccessibles μ → κ ≤ μ

/-- Negative example: the least inaccessible cardinal is not the least inaccessible limit of
inaccessibles. -/
theorem IsLeastInaccessible.not_isLeastInaccessibleLimit {κ : Cardinal.{u}}
    (hκ : IsLeastInaccessible κ) : ¬ IsLeastInaccessibleLimit κ :=
  fun h => hκ.not_isLimitOfInaccessibles h.2.1

/-- The ordinals below `κ` that are nonzero limits of inaccessible cardinals. -/
def inaccessibleLimitPoints (o : Ordinal.{u}) : Set (Iio o) :=
  {x | 0 < x.1 ∧ ∀ α < x.1, ∃ ν : Cardinal.{u}, ν.IsInaccessible ∧ α < ν.ord ∧ ν.ord < x.1}

/-- Negative example: `0` is not a limit point of inaccessibles. -/
theorem zero_not_mem_inaccessibleLimitPoints {o : Ordinal.{u}} (ho : 0 < o) :
    (⟨0, ho⟩ : Iio o) ∉ inaccessibleLimitPoints o :=
  fun h => (lt_irrefl _) h.1

/-- Below an inaccessible limit of inaccessibles, the limit points of the inaccessibles form a
club. -/
theorem isClub_inaccessibleLimitPoints {κ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    (hlim : IsLimitOfInaccessibles κ) : IsClub (inaccessibleLimitPoints κ.ord) where
  dirSupClosed := by
    intro d hd hne _ a ha
    obtain ⟨c₀, hc₀⟩ := hne
    refine ⟨(hd hc₀).1.trans_le (ha.1 hc₀), fun α hα => ?_⟩
    obtain ⟨c, hc, hlt⟩ :=
      (lt_isLUB_iff ha).mp (show (⟨α, hα.trans a.2⟩ : Iio κ.ord) < a from hα)
    obtain ⟨ν, hν, above, below⟩ := (hd hc).2 α hlt
    exact ⟨ν, hν, above, below.trans_le (ha.1 hc)⟩
  isCofinal := by
    intro a
    choose! g hg above below using hlim
    let step : Ordinal.{u} → Ordinal.{u} := fun β => (g β).ord
    have stepBelow : ∀ β < κ.ord, step β < κ.ord :=
      fun β hβ => Cardinal.ord_lt_ord.mpr (below β hβ)
    have limit := Cardinal.isSuccLimit_ord hκ.aleph0_lt.le
    have cofinality : ℵ₀ < κ.ord.cof := by
      rw [hκ.isRegular.cof_ord]; exact hκ.aleph0_lt
    let start := Order.succ a.1
    have startBelow : start < κ.ord := limit.succ_lt a.2
    have pointBelow : Ordinal.nfp step start < κ.ord :=
      Ordinal.nfp_lt_ord cofinality stepBelow startBelow
    have iterBelow : ∀ n, step^[n] start < κ.ord :=
      fun n => (Ordinal.iterate_le_nfp step start n).trans_lt pointBelow
    refine ⟨⟨Ordinal.nfp step start, pointBelow⟩, ⟨?_, fun α hα => ?_⟩,
      (Order.le_succ a.1).trans (Ordinal.le_nfp step start)⟩
    · exact (Order.bot_lt_succ a.1).trans_le (Ordinal.le_nfp step start)
    · obtain ⟨n, hn⟩ := Ordinal.lt_nfp_iff.mp hα
      refine ⟨g (step^[n] start), hg _ (iterBelow n), hn.trans (above _ (iterBelow n)), ?_⟩
      calc (g (step^[n] start)).ord = step^[n + 1] start :=
            (Function.iterate_succ_apply' step n start).symm
        _ < step (step^[n + 1] start) := above _ (iterBelow (n + 1))
        _ = step^[n + 2] start := (Function.iterate_succ_apply' step (n + 1) start).symm
        _ ≤ Ordinal.nfp step start := Ordinal.iterate_le_nfp step start (n + 2)

/-- **The least inaccessible limit of inaccessibles is not Mahlo.** The limit points of the
inaccessibles form a club; an inaccessible in that club is an inaccessible limit of inaccessibles
below `κ`, which leastness excludes. -/
theorem IsLeastInaccessibleLimit.not_isMahlo {κ : Cardinal.{u}}
    (hκ : IsLeastInaccessibleLimit κ) : ¬ IsMahlo κ := by
  intro h
  obtain ⟨x, ⟨ν, hν, hx⟩, _, limitPoint⟩ :=
    h.isStationary_inaccessiblesBelow (isClub_inaccessibleLimitPoints hκ.1 hκ.2.1)
  have νκ : ν < κ := Cardinal.ord_lt_ord.mp (hx ▸ x.2)
  have νlimit : IsLimitOfInaccessibles ν := by
    intro α hα
    obtain ⟨ν', hν', above, below⟩ := limitPoint α (hx ▸ hα)
    exact ⟨ν', hν', above, Cardinal.ord_lt_ord.mp (hx ▸ below)⟩
  exact (hκ.2.2 ν hν νlimit).not_gt νκ

/-- At the least inaccessible limit of inaccessibles, the law "every set lies in a closed set"
holds inside the level, although the cardinal is not Mahlo: Mahlo is strictly stronger than the
law inside `V_κ`. -/
theorem IsLeastInaccessibleLimit.universeLawInside {κ : Cardinal.{u}}
    (hκ : IsLeastInaccessibleLimit κ) : UniverseLawInside (V_ κ.ord) :=
  (universeLawInside_vonNeumann_iff hκ.1).mpr hκ.2.1

#print axioms exists_bound_lt_ord
#print axioms isClub_closurePoints
#print axioms not_isClub_ne_omega0
#print axioms isCofinal_ne_omega0
#print axioms isStationary_closurePoints
#print axioms not_isStationary_bounded
#print axioms isMahlo_iff_forall_closurePoint
#print axioms IsMahlo.isLimitOfInaccessibles
#print axioms IsMahlo.universeLawInside
#print axioms not_isMahlo_aleph0
#print axioms exists_isLeastInaccessible
#print axioms IsLeastInaccessible.not_isMahlo
#print axioms exists_inaccessible_not_isMahlo
#print axioms isClub_inaccessibleLimitPoints
#print axioms IsLeastInaccessibleLimit.not_isMahlo
#print axioms IsLeastInaccessibleLimit.universeLawInside

end Mettapedia.TypeTheory.MahloUniverses
