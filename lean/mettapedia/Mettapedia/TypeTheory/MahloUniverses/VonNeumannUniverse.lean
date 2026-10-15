import Mettapedia.TypeTheory.MahloUniverses.MahloCardinals
import Mettapedia.TypeTheory.MahloUniverses.SubuniverseReflection

/-!
# The Tarski universe of `V_κ`

Codes are the members of `V_κ`; a code decodes to the type of its members, shrunk to the size
level of the sets, so that `vonNeumannUniverse κ` has the same shape as the ambient host
`ambientUniverse` (codes one level up, decoded types at the level of the families).

The ordinary subuniverses are the **inaccessible levels**: the code family of `V_μ` for an
inaccessible `μ < κ`, whose indices are the members of `V_μ`, each decoding to itself
(`IsInaccessibleLevel`). Through the classification of closed sets these are exactly the code
families of the closed members of `V_κ` above `V_ω` (`isInaccessibleLevel_iff_closed`).

Two controls on the interface of `UniverseClosureProfiles`:
* `not_wholeSubuniverseClosure`: whole-subuniverse closure fails on `V_κ` for every infinite `κ`
  and every predicate, Mahlo or not: the powerset operator has no closed family.
* `mahloReflection_trivial`: the predicate admitting every family gives Mahlo reflection at every
  `κ > 0`, through the empty code.
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

/-- **The Tarski universe of `V_κ`.** Codes are the members of `V_κ`; a code decodes to the type
of its members, shrunk to the size level of the sets. -/
def vonNeumannUniverse (κ : Cardinal.{u}) : SemanticTarskiUniverse.{u + 1, u} where
  Code := {x : ZFSet.{u} // x ∈ V_ κ.ord}
  El x := Shrink.{u} x.1

variable {κ : Cardinal.{u}}

/-- A decoded type has the cardinality of its code. -/
theorem card_el (x : (vonNeumannUniverse κ).Code) :
    #((vonNeumannUniverse κ).El x) = x.1.card :=
  rfl

/-- Members of codes are codes. -/
theorem mem_of_mem_code (x : (vonNeumannUniverse κ).Code) {y : ZFSet.{u}} (hy : y ∈ x.1) :
    y ∈ V_ κ.ord :=
  ZFSet.mem_vonNeumann.mpr ((ZFSet.rank_lt_of_mem hy).trans (ZFSet.mem_vonNeumann.mp x.2))

/-- The member of a code named by an element of its decoded type, as a code. -/
def member (x : (vonNeumannUniverse κ).Code) (y : (vonNeumannUniverse κ).El x) :
    (vonNeumannUniverse κ).Code :=
  ⟨((equivShrink x.1).symm y).1, mem_of_mem_code x ((equivShrink x.1).symm y).2⟩

theorem member_mem (x : (vonNeumannUniverse κ).Code) (y : (vonNeumannUniverse κ).El x) :
    (member x y).1 ∈ x.1 :=
  ((equivShrink x.1).symm y).2

/-- Equal codes decode to equivalent types. -/
def elCongr {x y : (vonNeumannUniverse κ).Code} (h : x = y) :
    (vonNeumannUniverse κ).El x ≃ (vonNeumannUniverse κ).El y :=
  Equiv.cast (congrArg (vonNeumannUniverse κ).El h)

/-- The code family of a member `W` of `V_κ`: its indices decode `W`, and each index decodes to
the member of `W` it names. -/
def memberFamily (W : (vonNeumannUniverse κ).Code) : (vonNeumannUniverse κ).InternalFamily :=
  ⟨W, member W⟩

/-- The code of `V_μ` for `μ < κ`. -/
def levelCode (μ : Cardinal.{u}) (hμκ : μ < κ) : (vonNeumannUniverse κ).Code :=
  ⟨V_ μ.ord, ZFSet.vonNeumann_mem_vonNeumann_iff.mpr (Cardinal.ord_lt_ord.mpr hμκ)⟩

/-- The code family of `V_μ` for `μ < κ`. -/
def levelFamily (μ : Cardinal.{u}) (hμκ : μ < κ) : (vonNeumannUniverse κ).InternalFamily :=
  memberFamily (levelCode μ hμκ)

/-- **The ordinary subuniverses of `V_κ`**: the code families of `V_μ` for inaccessible `μ < κ`. -/
def IsInaccessibleLevel (κ : Cardinal.{u}) (F : (vonNeumannUniverse κ).InternalFamily) : Prop :=
  ∃ μ : Cardinal.{u}, μ.IsInaccessible ∧ ∃ hμκ : μ < κ, F = levelFamily μ hμκ

/-- Positive example: the code family of `V_μ` at an inaccessible `μ < κ`. -/
theorem levelFamily_isInaccessibleLevel {μ : Cardinal.{u}} (hμ : μ.IsInaccessible)
    (hμκ : μ < κ) : IsInaccessibleLevel κ (levelFamily μ hμκ) :=
  ⟨μ, hμ, hμκ, rfl⟩

/-- The index set of an inaccessible level is `V_μ` at an inaccessible `μ`. -/
theorem IsInaccessibleLevel.exists_base_eq {F : (vonNeumannUniverse κ).InternalFamily}
    (hF : IsInaccessibleLevel κ F) : ∃ μ : Cardinal.{u}, μ.IsInaccessible ∧ F.1.1 = V_ μ.ord := by
  obtain ⟨μ, hμ, hμκ, rfl⟩ := hF
  exact ⟨μ, hμ, rfl⟩

/-- Negative example: the code family of the empty set is not an inaccessible level. -/
theorem not_isInaccessibleLevel_empty (hκ : 0 < κ) :
    ¬ IsInaccessibleLevel κ
      (memberFamily ⟨∅, ZFSet.mem_vonNeumann.mpr (by
        rw [ZFSet.rank_empty]; exact Cardinal.ord_pos.mpr hκ)⟩) := by
  intro h
  obtain ⟨μ, hμ, hbase⟩ := h.exists_base_eq
  have ranks := congrArg ZFSet.rank hbase
  change (∅ : ZFSet.{u}).rank = (V_ μ.ord).rank at ranks
  rw [ZFSet.rank_empty, ZFSet.rank_vonNeumann] at ranks
  exact (Cardinal.ord_pos.mpr hμ.pos).ne ranks

/-- Negative example: the code family of `V_ω` is not an inaccessible level. -/
theorem not_isInaccessibleLevel_omega0 (hκ : ℵ₀ < κ) :
    ¬ IsInaccessibleLevel κ
      (memberFamily ⟨V_ ω, ZFSet.vonNeumann_mem_vonNeumann_iff.mpr (by
        rw [← Cardinal.ord_aleph0]; exact Cardinal.ord_lt_ord.mpr hκ)⟩) := by
  intro h
  obtain ⟨μ, hμ, hbase⟩ := h.exists_base_eq
  have ranks := congrArg ZFSet.rank hbase
  change (V_ ω : ZFSet.{u}).rank = (V_ μ.ord).rank at ranks
  rw [ZFSet.rank_vonNeumann, ZFSet.rank_vonNeumann, ← Cardinal.ord_aleph0,
    Cardinal.ord_inj] at ranks
  exact (lt_irrefl _) (ranks ▸ hμ.aleph0_lt)

/-- **The ordinary subuniverses are the closed members above `V_ω`.** Read through the
classification of closed sets, an inaccessible level is the code family of a closed member of
`V_κ` of rank above `ω`. -/
theorem isInaccessibleLevel_iff_closed (F : (vonNeumannUniverse κ).InternalFamily) :
    IsInaccessibleLevel κ F ↔
      ∃ W : (vonNeumannUniverse κ).Code, Closed W.1 ∧ ω < W.1.rank ∧ F = memberFamily W := by
  constructor
  · rintro ⟨μ, hμ, hμκ, rfl⟩
    refine ⟨levelCode μ hμκ, inaccessible_closed hμ, ?_, rfl⟩
    change ω < (V_ μ.ord).rank
    rw [ZFSet.rank_vonNeumann, ← Cardinal.ord_aleph0]
    exact Cardinal.ord_lt_ord.mpr hμ.aleph0_lt
  · rintro ⟨⟨W, hWκ⟩, hW, above, rfl⟩
    rcases (closed_iff W).mp hW with rfl | rfl | ⟨μ, hμ, rfl⟩
    · rw [ZFSet.rank_empty] at above
      exact absurd above (not_lt_of_ge zero_le)
    · rw [ZFSet.rank_vonNeumann] at above
      exact absurd above (lt_irrefl _)
    · have hμκ : μ < κ :=
        Cardinal.ord_lt_ord.mp (ZFSet.vonNeumann_mem_vonNeumann_iff.mp hWκ)
      exact ⟨μ, hμ, hμκ, rfl⟩

/-! ## Control: whole-subuniverse closure fails on `V_κ` -/

/-- Powersets of codes are codes when `κ` is infinite. -/
def powersetCode (hκ : ℵ₀ ≤ κ) (x : (vonNeumannUniverse κ).Code) : (vonNeumannUniverse κ).Code :=
  ⟨ZFSet.powerset x.1, ZFSet.mem_vonNeumann.mpr (by
    rw [ZFSet.rank_powerset]
    exact (Cardinal.isSuccLimit_ord hκ).succ_lt (ZFSet.mem_vonNeumann.mp x.2))⟩

/-- **Whole-subuniverse closure fails on `V_κ`.** For infinite `κ` and every predicate selecting
ordinary subuniverses, no family is closed, as one family, under the operator taking the powerset
of its index set. In particular it fails at Mahlo cardinals. -/
theorem not_wholeSubuniverseClosure (hκ : ℵ₀ ≤ κ)
    (IsOrdinary : (vonNeumannUniverse κ).InternalFamily → Prop) :
    ¬ WholeSubuniverseClosure (vonNeumannUniverse κ) IsOrdinary := by
  refine not_wholeSubuniverseClosure_of_strictGrowth (powersetCode hκ) (fun x => ⟨fun e => ?_⟩) _
  have sizes := Cardinal.mk_le_of_injective e.injective
  rw [card_el, card_el] at sizes
  change (ZFSet.powerset x.1).card ≤ x.1.card at sizes
  rw [ZFSet.card_powerset] at sizes
  exact (Cardinal.cantor x.1.card).not_ge sizes

/-- At a Mahlo cardinal whole-subuniverse closure fails, with the inaccessible levels as with any
other predicate, while Mahlo reflection holds (`IsMahlo.mahloReflection`). -/
theorem IsMahlo.not_wholeSubuniverseClosure (hκ : IsMahlo κ) :
    ¬ WholeSubuniverseClosure (vonNeumannUniverse κ) (IsInaccessibleLevel κ) :=
  MahloUniverses.not_wholeSubuniverseClosure hκ.isInaccessible.aleph0_lt.le _

/-! ## Control: the predicate admitting every family -/

/-- The empty set is a code when `κ > 0`. -/
def emptyCode (hκ : 0 < κ) : (vonNeumannUniverse κ).Code :=
  ⟨∅, ZFSet.mem_vonNeumann.mpr (by rw [ZFSet.rank_empty]; exact Cardinal.ord_pos.mpr hκ)⟩

theorem isEmpty_el_emptyCode (hκ : 0 < κ) :
    IsEmpty ((vonNeumannUniverse κ).El (emptyCode hκ)) := by
  rw [← Cardinal.mk_eq_zero_iff, card_el]
  exact ZFSet.card_empty

/-- **Vacuous reflection.** With the predicate admitting every family, Mahlo reflection holds on
`V_κ` for every `κ > 0`, Mahlo or not, through the empty subuniverse. -/
theorem mahloReflection_trivial (hκ : 0 < κ) :
    MahloReflection (vonNeumannUniverse κ) (fun _ => True) :=
  mahloReflection_of_emptyCode (emptyCode hκ) (isEmpty_el_emptyCode hκ)

end

#print axioms card_el
#print axioms levelFamily_isInaccessibleLevel
#print axioms not_isInaccessibleLevel_empty
#print axioms not_isInaccessibleLevel_omega0
#print axioms isInaccessibleLevel_iff_closed
#print axioms not_wholeSubuniverseClosure
#print axioms IsMahlo.not_wholeSubuniverseClosure
#print axioms mahloReflection_trivial

end Mettapedia.TypeTheory.MahloUniverses
