import Mettapedia.GSLT.Topos.NativeFixedPointEncodings
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Separating controls for native fixed-point encodings

An inhabited Boolean presheaf makes least/greatest identity fixed points
different. A seeded operator gives a proper, nonconstant least fixed point.
An actual nonidentity map tests fixed-point substitution. The literal source
encodings are tested against independent fixed-point semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.NativeFixedPointEncodingsControls

open _root_.CategoryTheory NativeFixedPointEncodings

abbrev World := Discrete PUnit.{1}
abbrev values : World ⥤ Type := (Functor.const _).obj Bool
abbrev spot : World := Discrete.mk PUnit.unit

def trueOnly : Subfunctor values where
  obj _ := {value | value = true}
  map _ _ member := member

def constantTrue : values ⟶ values where
  app _ := TypeCat.ofHom fun _ => true
  naturality := by intros; rfl

def seeded : Subfunctor values →o Subfunctor values where
  toFun candidate := trueOnly ⊔ candidate
  monotone' _ _ below := sup_le_sup_left below trueOnly

theorem least_identity_empty :
    leastEncoding (OrderHom.id : Subfunctor values →o Subfunctor values) = ⊥ := by
  apply le_antisymm
  · exact least_induction _ ⊥ le_rfl
  · exact bot_le

theorem greatest_identity_full :
    greatestEncoding (OrderHom.id : Subfunctor values →o Subfunctor values) = ⊤ := by
  apply le_antisymm le_top
  exact greatest_coinduction _ ⊤ le_rfl

theorem printed_mu_refuted :
    printedMu (OrderHom.id : Subfunctor values →o Subfunctor values) ≠
      leastMeaning OrderHom.id := by
  intro equal
  rw [printedMu_eq_top, ← leastEncoding_eq_meaning, least_identity_empty] at equal
  have impossible : false ∈ (⊥ : Subfunctor values).obj spot := equal ▸ trivial
  exact impossible

theorem printed_nu_refuted :
    printedNu (OrderHom.id : Subfunctor values →o Subfunctor values) ≠
      greatestMeaning OrderHom.id := by
  intro equal
  rw [printedNu_eq_least, ← leastEncoding_eq_meaning, least_identity_empty,
    ← greatestEncoding_eq_meaning, greatest_identity_full] at equal
  have impossible : false ∈ (⊥ : Subfunctor values).obj spot := equal.symm ▸ trivial
  exact impossible

theorem corrected_mu_inhabits_exact_seed : leastEncoding seeded = trueOnly := by
  apply le_antisymm
  · exact least_induction seeded trueOnly (sup_le le_rfl le_rfl)
  · have unfolds := least_unfold seeded
    exact unfolds ▸ (le_sup_left : trueOnly ≤ trueOnly ⊔ leastEncoding seeded)

theorem corrected_nu_full : greatestEncoding seeded = ⊤ := by
  apply le_antisymm le_top
  exact greatest_coinduction seeded ⊤ le_sup_right

theorem seeded_least_excludes_false :
    false ∉ (leastEncoding seeded).obj spot := by
  rw [corrected_mu_inhabits_exact_seed]
  exact Bool.false_ne_true

theorem seed_survives : true ∈ (leastEncoding seeded).obj spot := by
  rw [corrected_mu_inhabits_exact_seed]
  rfl

theorem nonidentity_context_map : constantTrue ≠ 𝟙 values := by
  intro equal
  have impossible := congrArg (fun σ : values ⟶ values => σ.app spot false) equal
  exact Bool.false_ne_true impossible.symm

/-- Substituting the constant true input makes the proper seed true.
This is a concrete nonidentity fixed-point comparison, not an identity-only
specialization of the general transport law. -/
theorem nonidentity_least_transport :
    (leastEncoding seeded).preimage constantTrue =
      leastEncoding (OrderHom.const (Subfunctor values) (⊤ : Subfunctor values)) := by
  apply least_preimage
  intro candidate
  ext world argument
  constructor
  · intro _
    trivial
  · intro _
    exact Or.inl rfl

theorem nonidentity_greatest_transport :
    (greatestEncoding seeded).preimage constantTrue =
      greatestEncoding (OrderHom.const (Subfunctor values) (⊤ : Subfunctor values)) := by
  apply greatest_preimage
  intro candidate
  ext world argument
  constructor
  · intro _
    trivial
  · intro _
    exact Or.inl rfl

end Mettapedia.GSLT.Topos.NativeFixedPointEncodingsControls
