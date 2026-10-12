import Mettapedia.TypeTheory.MahloUniverses.Superuniverse

/-!
# Small family-enclosing operators exist exactly under cofinal inaccessibles

A closed Tarski universe over a family, with codes and decoded types at the level of the family
(`ClosedTarskiUniverseOver.{u, u}`), has an inaccessible **height**: the supremum of the sizes of
its decoded types (`isInaccessible_envelopeHeight`), and the index type of the family is smaller
than the height (`card_lt_envelopeHeight`). Closure under dependent products over a two-element
type makes the height a strong limit that is not attained; closure under dependent sums makes it
regular; the natural numbers make it uncountable.

Hence a `SmallFamilyEnclosingUniverseOperator` exists exactly when the inaccessible cardinals of
the level are unbounded (`nonempty_smallFamilyEnclosingUniverseOperator_iff`): the hypothesis
`CofinalInaccessibles` of `leastEnvelopeOperator` is not a convenience but the exact condition for
the superuniverse interface to have any small operator at all.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MahloUniverses

open Mettapedia.TypeTheory.FamilyEnclosingUniverse
open Mettapedia.TypeTheory.UniverseClosureProfiles
open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
open Cardinal

universe u

noncomputable section

variable {A : Type u} {B : A → Type u} (env : ClosedTarskiUniverseOver.{u, u} A B)

/-- The height of a closed universe: the supremum of the sizes of its decoded types. -/
def envelopeHeight : Cardinal.{u} :=
  ⨆ code, #(env.El code)

theorem bddAbove_card_el : BddAbove (Set.range fun code => #(env.El code)) :=
  Cardinal.bddAbove_of_small

theorem card_el_le_envelopeHeight (code : env.Code) : #(env.El code) ≤ envelopeHeight env :=
  le_ciSup (bddAbove_card_el env) code

/-- The two-element type inside a closed universe: the sum of two unit types. -/
def boolCode : env.Code :=
  env.sumCode env.unitCode env.unitCode

theorem card_el_unitCode : #(env.El env.unitCode) = 1 := by
  have : Unique (env.El env.unitCode) := env.elUnit.unique
  exact Cardinal.mk_eq_one _

theorem card_el_boolCode : #(env.El (boolCode env)) = 2 := by
  rw [boolCode, Cardinal.mk_congr (env.elSum _ _), ← Cardinal.add_def, card_el_unitCode,
    one_add_one_eq_two]

/-- The code of the two-valued functions on a decoded type. -/
def predicateCode (code : env.Code) : env.Code :=
  env.piCode code fun _ => boolCode env

theorem card_el_predicateCode (code : env.Code) :
    #(env.El (predicateCode env code)) = 2 ^ #(env.El code) :=
  calc #(env.El (predicateCode env code)) = #(env.El code → env.El (boolCode env)) :=
        Cardinal.mk_congr (env.elPi code fun _ => boolCode env)
    _ = #(env.El (boolCode env)) ^ #(env.El code) := (Cardinal.power_def _ _).symm
    _ = 2 ^ #(env.El code) := by rw [card_el_boolCode]

/-- **The height is not attained.** Every decoded type is smaller than the height. -/
theorem card_el_lt_envelopeHeight (code : env.Code) : #(env.El code) < envelopeHeight env :=
  calc #(env.El code) < 2 ^ #(env.El code) := Cardinal.cantor _
    _ = #(env.El (predicateCode env code)) := (card_el_predicateCode env code).symm
    _ ≤ envelopeHeight env := card_el_le_envelopeHeight env _

/-- The index type of the enclosed family is smaller than the height. -/
theorem card_lt_envelopeHeight : #A < envelopeHeight env := by
  rw [← Cardinal.mk_congr env.elBase]
  exact card_el_lt_envelopeHeight env _

/-- **The height of a closed universe is inaccessible.** -/
theorem isInaccessible_envelopeHeight : (envelopeHeight env).IsInaccessible := by
  have : Nonempty env.Code := ⟨env.baseCode⟩
  refine ⟨?_, ?_, ?_⟩
  · have nat : #(env.El env.natCode) = ℵ₀ := by
      have sizes := Cardinal.lift_mk_eq'.mpr ⟨env.elNat⟩
      simpa using sizes
    exact nat ▸ card_el_lt_envelopeHeight env env.natCode
  · rw [← Ordinal.cof_toType]
    refine Order.le_cof_iff.mpr fun cofinalSet cofinal => ?_
    by_contra hnot
    obtain ⟨code₀, hcode₀⟩ := (lt_ciSup_iff (bddAbove_card_el env)).mp (not_le.mp hnot)
    obtain ⟨g⟩ := (Cardinal.le_def _ _).mp hcode₀.le
    let ordOf : cofinalSet → Ordinal.{u} := fun x => (Ordinal.ToType.mk.symm x.1).1
    have each : ∀ x : cofinalSet, ∃ code, (ordOf x).card < #(env.El code) := fun x =>
      (lt_ciSup_iff (bddAbove_card_el env)).mp
        (Cardinal.lt_ord.mp (Ordinal.ToType.mk.symm x.1).2)
    choose c hc using each
    classical
    let d : env.El code₀ → env.Code := fun y =>
      if h : ∃ x, g x = y then c (Classical.choose h) else env.emptyCode
    have dg : ∀ x, d (g x) = c x := by
      intro x
      have h : ∃ x', g x' = g x := ⟨x, rfl⟩
      simp only [d, dif_pos h]
      rw [g.injective (Classical.choose_spec h)]
    let total := env.sigmaCode code₀ d
    have sizes : ∀ x, #(env.El (c x)) ≤ #(env.El total) := by
      intro x
      rw [Cardinal.mk_congr (env.elSigma code₀ d), ← dg x]
      exact Cardinal.mk_le_of_injective
        (f := @Sigma.mk (env.El code₀) (fun y => env.El (d y)) (g x)) sigma_mk_injective
    have attained : envelopeHeight env ≤ #(env.El total) := by
      by_contra hbelow
      have below : (#(env.El total)).ord < (envelopeHeight env).ord :=
        Cardinal.ord_lt_ord.mpr (not_le.mp hbelow)
      obtain ⟨x, hx, above⟩ := cofinal (Ordinal.ToType.mk ⟨_, below⟩)
      have mono := Ordinal.ToType.mk.symm.monotone above
      rw [OrderIso.symm_apply_apply] at mono
      have atMost : (#(env.El total)).ord ≤ ordOf ⟨x, hx⟩ := Subtype.coe_le_coe.mpr mono
      exact ((Cardinal.ord_le.mp atMost).trans_lt (hc _)).not_ge (sizes _)
    exact (card_el_lt_envelopeHeight env total).not_ge attained
  · intro x hx
    obtain ⟨code, hcode⟩ := (lt_ciSup_iff (bddAbove_card_el env)).mp hx
    calc 2 ^ x ≤ 2 ^ #(env.El code) := Cardinal.power_le_power_left two_ne_zero hcode.le
      _ = #(env.El (predicateCode env code)) := (card_el_predicateCode env code).symm
      _ < envelopeHeight env := card_el_lt_envelopeHeight env _

/-- A closed universe over a family lies below an inaccessible cardinal above the family. -/
theorem exists_inaccessible_above_envelope :
    ∃ μ : Cardinal.{u}, μ.IsInaccessible ∧ #A < μ ∧ ∀ code, #(env.El code) < μ :=
  ⟨envelopeHeight env, isInaccessible_envelopeHeight env, card_lt_envelopeHeight env,
    card_el_lt_envelopeHeight env⟩

/-- **A small family-enclosing operator forces cofinal inaccessibles.** -/
theorem cofinalInaccessibles_of_smallFamilyEnclosingUniverseOperator
    (operator : SmallFamilyEnclosingUniverseOperator.{u}) : CofinalInaccessibles.{u} := by
  intro α
  let env := operator.enclose α.ToType fun _ => α.ToType
  refine ⟨envelopeHeight env, isInaccessible_envelopeHeight env, Cardinal.lt_ord.mpr ?_⟩
  have below := card_lt_envelopeHeight env
  rwa [Cardinal.mk_toType] at below

/-- **Small family-enclosing operators exist exactly under cofinal inaccessibles.** -/
theorem nonempty_smallFamilyEnclosingUniverseOperator_iff :
    Nonempty SmallFamilyEnclosingUniverseOperator.{u} ↔ CofinalInaccessibles.{u} :=
  ⟨fun ⟨operator⟩ => cofinalInaccessibles_of_smallFamilyEnclosingUniverseOperator operator,
    fun h => ⟨leastEnvelopeOperator h⟩⟩

/-- Negative example: if no inaccessible cardinal lies above the size of a type, no closed
universe at its level encloses a family indexed by it. -/
theorem isEmpty_closedTarskiUniverseOver_of_no_inaccessible_above
    (none : ∀ μ : Cardinal.{u}, μ.IsInaccessible → μ ≤ #A) :
    IsEmpty (ClosedTarskiUniverseOver.{u, u} A B) :=
  ⟨fun env => (none _ (isInaccessible_envelopeHeight env)).not_gt (card_lt_envelopeHeight env)⟩

end

#print axioms card_el_lt_envelopeHeight
#print axioms isInaccessible_envelopeHeight
#print axioms exists_inaccessible_above_envelope
#print axioms cofinalInaccessibles_of_smallFamilyEnclosingUniverseOperator
#print axioms nonempty_smallFamilyEnclosingUniverseOperator_iff
#print axioms isEmpty_closedTarskiUniverseOver_of_no_inaccessible_above

end Mettapedia.TypeTheory.MahloUniverses
