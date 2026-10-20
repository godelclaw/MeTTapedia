import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReading
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeAbstraction

/-!
# The HOL fiber of the impredicative code package

A reading `ρ` of a HOL signature in a package of proposition codes
(`HOLReading`) carves a region out of the package's selected typed judgment
(`TypedEquality.Derivable`). Its types are

* the **carriers** of simple types: `prop ↦` the type of codes, a base sort to
  its closed sort, `σ ⇒ τ ↦ Π (_ : σ). τ` (`IsCarrier`);
* the **proof types** `holds c`, decodings of codes (`IsProofType`).

The region is the `FiberType`. Its data are the read HOL terms (`HOLReading.term`,
typed at their carriers by `Laws.term_typed`), its proofs are terms at the proof
types, and its definitional equality is the package's typed equality, which on
codes is the decoding of `imp`, `all@A` and, under the identity reading, `eq@A`
(`Laws.equal_holds_imp`, `Laws.equal_holds_all`, `Laws.equal_holds_eq`).
Proofs of HOL theorems compile into the region (`Laws.compileP_typedO`).

This module proves two generic facts that isolate the region inside a package,
while the concrete `DeclarationBased.SetProfile` instantiation lives in
`Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.HOLFiberPeano`:

* **Non-dependence.** A carrier is invariant under every substitution
  (`IsCarrier.subst`), so a type with two different substitution instances is
  not a carrier (`not_isCarrier_of_subst_ne`).
* **Inhabited sorts.** A lawful reading that interprets a choice constant
  `ε : (b ⇒ prop) ⇒ b` gives the carrier of `b` a closed inhabitant
  (`choice_inhabits_sort`). If the carrier of `b` is the decoding of a code,
  that inhabitant is a closed proof of the code (`choice_proves_sort_code`), so
  in a package that does not prove the code no lawful reading interprets
  choice at that sort. A type of the package that may be empty therefore
  enters the fiber as a predicate on a carrier, not as a sort.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HOLFiber

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Impredicative
open Mettapedia.Logic

universe u v

/-! ## The region -/

section Region

variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
variable (ρ : HOLReading Head Base Const)

/-- A type of the fiber's data: the carrier of a simple type. -/
def IsCarrier {n : Nat} (T : Tm Head n) : Prop := ∃ τ : HOL.Ty Base, T = ρ.carrierAt n τ

/-- A type of the fiber's proofs: the decoding of a code. -/
def IsProofType {n : Nat} (T : Tm Head n) : Prop := ∃ c : Tm Head n, T = ρ.holdsOf c

/-- The fiber's types. -/
def FiberType {n : Nat} (T : Tm Head n) : Prop := IsCarrier ρ T ∨ IsProofType ρ T

variable {ρ}

/-- **Carriers do not depend on terms**: every substitution fixes them. -/
theorem IsCarrier.subst {n m : Nat} {T : Tm Head n} (carrier : IsCarrier ρ T)
    (σ : Sub Head n m) : IsCarrier ρ (Presentation.subst σ T) ∧
      ∀ σ' : Sub Head n m, Presentation.subst σ T = Presentation.subst σ' T := by
  obtain ⟨τ, rfl⟩ := carrier
  refine ⟨⟨τ, ρ.subst_carrierAt σ τ⟩, fun σ' => ?_⟩
  rw [ρ.subst_carrierAt σ τ, ρ.subst_carrierAt σ' τ]

/-- A type with two different substitution instances is not a carrier. -/
theorem not_isCarrier_of_subst_ne {n m : Nat} {T : Tm Head n} {σ σ' : Sub Head n m}
    (differ : Presentation.subst σ T ≠ Presentation.subst σ' T) : ¬ IsCarrier ρ T :=
  fun carrier => differ ((carrier.subst σ).2 σ')

/-- Every read term of a lawful reading is typed at a carrier. -/
theorem read_typed_at_carrier (L : ρ.Laws) {Γ : HOL.Ctx Base} {τ : HOL.Ty Base}
    {t : HOL.Term Const Γ τ} {out : Tm Head Γ.length} (read : ρ.term t = some out) :
    ∃ T, IsCarrier ρ T ∧ Typed ρ.rules (ρ.objCtx Γ) out T :=
  ⟨_, ⟨τ, rfl⟩, L.term_typed read⟩

end Region

/-! ## Choice inhabits the sorts -/

section Choice

variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
variable {ρ : HOLReading Head Base Const}

/-- **Choice gives every sort a closed inhabitant.** If a lawful reading
interprets a choice constant at the sort `b`, applying it to any closed
predicate on `b` is a closed term of the sort's carrier. -/
theorem choice_inhabits_sort (L : ρ.Laws) {b : Base}
    (eps : Const (.arr (.arr (.base b) .prop) (.base b))) {t : Tm Head 0}
    (interpreted : ρ.constant eps = some t) {k : Tm Head 0}
    (predicate : Typed ρ.rules .nil k (ρ.carrier (.arr (.base b) .prop))) :
    Typed ρ.rules .nil (.app t k) (ρ.sort b) := by
  have typed := L.const_typed eps interpreted
  have applied := Derivable.appElim typed predicate
  have atSort : ρ.carrierAt 0 (.base b) = ρ.sort b := TelescopeAbstraction.liftClosed_zero _
  rw [inst0, ρ.subst_carrierAt, atSort] at applied
  exact applied

/-- If the sort is read as the decoding of a code, choice proves the code. -/
theorem choice_proves_sort_code (L : ρ.Laws) {b : Base}
    (eps : Const (.arr (.arr (.base b) .prop) (.base b))) {t : Tm Head 0}
    (interpreted : ρ.constant eps = some t) {c : Tm Head 0} (sortIsProof : ρ.sort b = ρ.holdsOf c)
    {k : Tm Head 0}
    (predicate : Typed ρ.rules .nil k (ρ.carrier (.arr (.base b) .prop))) :
    Typed ρ.rules .nil (.app t k) (ρ.holdsOf c) := by
  rw [← sortIsProof]
  exact choice_inhabits_sort L eps interpreted predicate

end Choice

/-! ## Axiom audit -/

#print axioms IsCarrier.subst
#print axioms not_isCarrier_of_subst_ne
#print axioms choice_inhabits_sort
#print axioms choice_proves_sort_code

end Mettapedia.TypeTheory.HOLFiber
