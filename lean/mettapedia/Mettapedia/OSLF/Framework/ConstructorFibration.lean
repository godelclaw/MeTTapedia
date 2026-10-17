import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.GSLT.Core.LambdaTheoryCategory
import Mettapedia.GSLT.Core.ChangeOfBase

/-!
# Constructor Fibration + Change-of-Base

Given a `LanguageDef`, this file builds a `SubobjectFibration` and `ChangeOfBase`
over the constructor category from `ConstructorCategory.lean`.

## Construction

1. **SubobjectFibration**: Each sort `s` is assigned the fiber `Pattern → Prop`,
   which is a `Frame` (complete Heyting algebra) via Mathlib's `Pi.instFrame`.

2. **ChangeOfBase**: For each morphism `f : s ⟶ t` (a `SortPath`), the
   semantic function `pathSem lang f : Pattern → Pattern` induces:
   - `f* = pb (pathSem f)` — pullback (inverse image)
   - `∃f = di (pathSem f)` — direct image (existential)
   - `∀f = ui (pathSem f)` — universal image

   The adjunctions `∃f ⊣ f* ⊣ ∀f` are direct instances of the generic
   `di_pb_adj` and `pb_ui_adj` from `DerivedModalities.lean`.

## Key Properties

- **Pullback is functorial**: `f*(g*(φ)) = (f ≫ g)*(φ)` and `(𝟙)*(φ) = φ`
- **Pullback preserves meet**: `f*(φ ⊓ ψ) = f*(φ) ⊓ f*(ψ)` (by `rfl`)
- **Adjunctions are unconditional**: follow from DerivedModalities

## References

- Meredith & Stay, "Operational Semantics in Logical Form" §4, §5
- Williams & Stay, "Native Type Theory" (ACT 2021) §3
- Jacobs, "Categorical Logic and Type Theory" Ch. 1
-/

namespace Mettapedia.OSLF.Framework.ConstructorFibration

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.Core
open _root_.Mettapedia.CategoryTheory

/-! ## SubobjectFibration over Constructor Category -/

/-- The predicate fibration over the constructor category.

    Each sort is assigned the fiber `Pattern → Prop`, which is a Frame
    (complete Heyting algebra). Since the Pattern AST is untyped, all
    fibers are the same type — the sort distinction is structural. -/
noncomputable def constructorFibration (lang : LanguageDef) :
    SubobjectFibration (ConstructorObj lang) where
  Sub := fun _ => Pattern → Prop
  frame := fun _ => Pi.instFrame

/-! ## Change-of-Base Operations

Each constructor path `f : s ⟶ t` has a semantic function
`pathSem lang f : Pattern → Pattern` (from ConstructorCategory.lean).
This induces the adjoint triple `∃f ⊣ f* ⊣ ∀f` via the generic
Set-level operations from DerivedModalities.lean. -/

variable (lang : LanguageDef)

/-- Pullback along a constructor path: `f*(φ) = φ ∘ pathSem f`.

    If `f : s ⟶ t` maps patterns at sort s to patterns at sort t,
    then `f*(φ)(p) ↔ φ(pathSem f p)`: a pattern at sort s satisfies
    the pullback iff its constructor-image satisfies `φ`. -/
def constructorPullback {s t : ConstructorObj lang}
    (f : s ⟶ t) (φ : Pattern → Prop) : Pattern → Prop :=
  pb (pathSem lang f) φ

/-- Direct image along a constructor path: `∃f(ψ)(q) = ∃ p, pathSem f p = q ∧ ψ p`.

    Pushes a predicate at sort s forward to sort t existentially:
    `q` satisfies the result iff some preimage under the constructor satisfies `ψ`. -/
def constructorDirectImage {s t : ConstructorObj lang}
    (f : s ⟶ t) (ψ : Pattern → Prop) : Pattern → Prop :=
  di (pathSem lang f) ψ

/-- Universal image along a constructor path: `∀f(ψ)(q) = ∀ p, pathSem f p = q → ψ p`.

    Pushes a predicate at sort s forward to sort t universally:
    `q` satisfies the result iff ALL preimages under the constructor satisfy `ψ`. -/
def constructorUniversalImage {s t : ConstructorObj lang}
    (f : s ⟶ t) (ψ : Pattern → Prop) : Pattern → Prop :=
  ui (pathSem lang f) ψ

/-! ## Adjunctions

The adjoint triple `∃f ⊣ f* ⊣ ∀f` follows directly from the generic
`di_pb_adj` and `pb_ui_adj` in DerivedModalities.lean. -/

/-- `∃f ⊣ f*` for constructor paths. -/
theorem constructorDiPbAdj {s t : ConstructorObj lang} (f : s ⟶ t) :
    GaloisConnection (constructorDirectImage lang f) (constructorPullback lang f) :=
  di_pb_adj (pathSem lang f)

/-- `f* ⊣ ∀f` for constructor paths. -/
theorem constructorPbUiAdj {s t : ConstructorObj lang} (f : s ⟶ t) :
    GaloisConnection (constructorPullback lang f) (constructorUniversalImage lang f) :=
  pb_ui_adj (pathSem lang f)

/-! ## Monotonicity (from adjunctions) -/

theorem constructorPullback_mono {s t : ConstructorObj lang} (f : s ⟶ t) :
    Monotone (constructorPullback lang f) :=
  (constructorDiPbAdj lang f).monotone_u

theorem constructorDirectImage_mono {s t : ConstructorObj lang} (f : s ⟶ t) :
    Monotone (constructorDirectImage lang f) :=
  (constructorDiPbAdj lang f).monotone_l

theorem constructorUniversalImage_mono {s t : ConstructorObj lang} (f : s ⟶ t) :
    Monotone (constructorUniversalImage lang f) :=
  (constructorPbUiAdj lang f).monotone_u

/-! ## Functoriality of Pullback

Pullback is a contravariant functor from the constructor category to the
category of Frames: it respects identity, composition, and meets. -/

/-- Pullback of identity is identity (definitional).

    `𝟙 s = .nil` in our category, `pathSem .nil = id`, `pb id = id`. -/
theorem constructorPullback_id (s : ConstructorObj lang) (φ : Pattern → Prop) :
    constructorPullback lang (SortPath.nil : s ⟶ s) φ = φ := rfl

/-- Pullback is contravariantly functorial: `(f ≫ g)* = f* ∘ g*`. -/
theorem constructorPullback_comp {s t u : ConstructorObj lang}
    (f : s ⟶ t) (g : t ⟶ u) (φ : Pattern → Prop) :
    constructorPullback lang (f.comp g) φ =
    constructorPullback lang f (constructorPullback lang g φ) := by
  funext p
  exact congrArg φ (congrFun (pathSem_comp lang f g) p)

/-- Pullback preserves meet (definitional). -/
theorem constructorPullback_inf {s t : ConstructorObj lang}
    (f : s ⟶ t) (φ ψ : Pattern → Prop) :
    constructorPullback lang f (φ ⊓ ψ) =
    constructorPullback lang f φ ⊓ constructorPullback lang f ψ := rfl

/-- Pullback preserves top (definitional). -/
theorem constructorPullback_top {s t : ConstructorObj lang}
    (f : s ⟶ t) :
    constructorPullback lang f ⊤ = ⊤ := rfl

/-! ## GSLT ChangeOfBase Instance -/

/-- The full change-of-base structure for the constructor fibration.

    This instantiates the GSLT `ChangeOfBase` structure, connecting the
    OSLF Set-level infrastructure to the categorical framework.

    The adjunctions are **proven**, not axiomatized — they follow from
    the generic `di_pb_adj` / `pb_ui_adj` in DerivedModalities.lean. -/
def constructorChangeOfBase (lang : LanguageDef) :
    ChangeOfBase (constructorFibration lang) where
  pullback f := constructorPullback lang f
  directImage f := constructorDirectImage lang f
  universalImage f := constructorUniversalImage lang f
  pullback_mono f := constructorPullback_mono lang f
  directImage_mono f := constructorDirectImage_mono lang f
  universalImage_mono f := constructorUniversalImage_mono lang f
  direct_pullback_adj f := constructorDiPbAdj lang f
  pullback_universal_adj f := constructorPbUiAdj lang f

/-! ## ρ-Calculus Instantiation -/

section RhoCalc

open ConstructorCategory (rhoProcObj rhoNameObj nquoteMor pdropMor)

-- NQuote pullback: pull Name predicates back to Proc
-- NQuote*(φ)(p) = φ(.apply "NQuote" [p])
example (φ : Pattern → Prop) (p : Pattern) :
    constructorPullback rhoCalc nquoteMor φ p =
    φ (.apply "NQuote" [p]) := rfl

-- PDrop pullback: pull Proc predicates back to Name
-- PDrop*(φ)(n) = φ(.apply "PDrop" [n])
example (φ : Pattern → Prop) (n : Pattern) :
    constructorPullback rhoCalc pdropMor φ n =
    φ (.apply "PDrop" [n]) := rfl

-- NQuote direct image: push Proc predicates forward to Name
-- ∃NQuote(ψ)(q) = ∃ p, .apply "NQuote" [p] = q ∧ ψ p
example (ψ : Pattern → Prop) (q : Pattern) :
    constructorDirectImage rhoCalc nquoteMor ψ q =
    (∃ p, Pattern.apply "NQuote" [p] = q ∧ ψ p) := rfl

-- PDrop direct image: push Name predicates forward to Proc
-- ∃PDrop(ψ)(q) = ∃ n, .apply "PDrop" [n] = q ∧ ψ n
example (ψ : Pattern → Prop) (q : Pattern) :
    constructorDirectImage rhoCalc pdropMor ψ q =
    (∃ n, Pattern.apply "PDrop" [n] = q ∧ ψ n) := rfl

-- NQuote universal image: push Proc predicates forward to Name
-- ∀NQuote(ψ)(q) = ∀ p, .apply "NQuote" [p] = q → ψ p
example (ψ : Pattern → Prop) (q : Pattern) :
    constructorUniversalImage rhoCalc nquoteMor ψ q =
    (∀ p, Pattern.apply "NQuote" [p] = q → ψ p) := rfl

-- Verify the full ChangeOfBase instance
#check constructorChangeOfBase rhoCalc

-- Verify the SubobjectFibration instance
#check constructorFibration rhoCalc

end RhoCalc

/-! ## Summary

**0 sorries. 0 axioms.**

### Definitions
- `constructorFibration lang`: SubobjectFibration with fiber `Pattern → Prop`
- `constructorPullback lang f`: `f*(φ) = φ ∘ pathSem f`
- `constructorDirectImage lang f`: `∃f(ψ)(q) = ∃ p, pathSem f p = q ∧ ψ p`
- `constructorUniversalImage lang f`: `∀f(ψ)(q) = ∀ p, pathSem f p = q → ψ p`
- `constructorChangeOfBase lang`: GSLT `ChangeOfBase` instance

### Proven Properties
- `constructorDiPbAdj`: `∃f ⊣ f*` (from `di_pb_adj`)
- `constructorPbUiAdj`: `f* ⊣ ∀f` (from `pb_ui_adj`)
- `constructorPullback_id`: `(𝟙)*(φ) = φ` (by `rfl`)
- `constructorPullback_comp`: `(f ≫ g)* = f* ∘ g*` (from `pathSem_comp`)
- `constructorPullback_inf`: `f*(φ ⊓ ψ) = f*(φ) ⊓ f*(ψ)` (by `rfl`)
- `constructorPullback_top`: `f*(⊤) = ⊤` (by `rfl`)
- Monotonicity of all three operations (from adjunctions)

### Connection to OSLF Architecture
- The constructor change-of-base moves predicates **between sort fibers**
  (e.g., NQuote* pulls Name predicates back to Proc)
- The OSLF modalities ◇/□ operate **within a single fiber** via the
  reduction span (from DerivedModalities/TypeSynthesis)
- Phase C (ModalEquivalence) will connect the two: typing rules combine
  constructor change-of-base with reduction modalities

### For rhoCalc
- `NQuote*(φ)(p) = φ(@(p))` — does `@(p)` satisfy `φ`?
- `∃NQuote(ψ)(q) = ∃ p, @(p) = q ∧ ψ(p)` — is `q` a quotation of some `p` satisfying `ψ`?
- `∀NQuote(ψ)(q) = ∀ p, @(p) = q → ψ(p)` — do all `p` whose quotation is `q` satisfy `ψ`?
- Symmetric results for PDrop
-/

end Mettapedia.OSLF.Framework.ConstructorFibration
