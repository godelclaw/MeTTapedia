import Mettapedia.TypeTheory.MahloUniverses.MahloReflectionModel
import Mathlib.Data.W.Cardinal

/-!
# Superuniverse closure of the universe of `V_κ`

`SuperuniverseFor outer operator` asks that `outer` embed the universe that a small
family-enclosing operator builds around each family represented in `outer`.

* `nonempty_universeEmbedding_iff`: for inaccessible `κ`, a small Tarski universe embeds into the
  universe of `V_κ` exactly when it has fewer than `κ` codes and each decoded type has fewer than
  `κ` elements. Hence `superuniverseFor_iff`.
* `levelEnvelope`: for inaccessible `μ`, the universe of `V_μ` at the level of the decoded types,
  enclosing any family of fewer than `μ` types of size below `μ`, is closed under the empty, unit
  and natural-number types, binary sums, dependent products and sums, identity types and
  well-founded trees.
* `leastEnvelopeOperator`: under `CofinalInaccessibles`, enclosing each family in the level of the
  least inaccessible above it is a small family-enclosing operator.
* `superuniverseFor_leastEnvelope_iff`: for inaccessible `κ`, the universe of `V_κ` is a
  superuniverse for that operator exactly when `κ` is a limit of inaccessibles. So Mahlo
  reflection gives superuniverse closure (`superuniverseFor_of_mahloReflection`), and the
  least inaccessible limit of inaccessibles separates the two: it is a superuniverse without Mahlo
  reflection (`IsLeastInaccessibleLimit.superuniverse_without_reflection`). At the least
  inaccessible, superuniverse closure fails (`IsLeastInaccessible.not_superuniverseFor`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MahloUniverses

open Mettapedia.TypeTheory.FamilyEnclosingUniverse
open Mettapedia.TypeTheory.UniverseClosureProfiles
open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
open Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels
open Cardinal
open scoped ZFSet Ordinal

universe u

noncomputable section

variable {κ : Cardinal.{u}}

/-! ## Embeddings into the universe of `V_κ` -/

/-- The code in `V_κ` of a type with fewer than `κ` elements: the initial ordinal of its
cardinality. -/
def typeCode (T : Type u) (hT : #T < κ) : (vonNeumannUniverse κ).Code :=
  ⟨(#T).ord.toZFSet, ZFSet.mem_vonNeumann.mpr (by
    rw [Ordinal.rank_toZFSet]; exact Cardinal.ord_lt_ord.mpr hT)⟩

theorem card_el_typeCode (T : Type u) (hT : #T < κ) :
    #((vonNeumannUniverse κ).El (typeCode T hT)) = #T := by
  rw [card_el]
  change (#T).ord.toZFSet.card = #T
  rw [Ordinal.card_toZFSet, Cardinal.card_ord]

/-- The code of a type decodes to a type equivalent to it. -/
def typeCodeEquiv (T : Type u) (hT : #T < κ) : (vonNeumannUniverse κ).El (typeCode T hT) ≃ T :=
  Classical.choice (Cardinal.eq.mp (card_el_typeCode T hT))

/-- A small universe with fewer than `κ` codes and decoded types of fewer than `κ` elements
embeds into the universe of `V_κ`. -/
def universeEmbeddingOfSmall (inner : SemanticTarskiUniverse.{u, u}) (hcode : #inner.Code < κ)
    (hel : ∀ code, #(inner.El code) < κ) : UniverseEmbedding (vonNeumannUniverse κ) inner where
  codeCarrier := typeCode inner.Code hcode
  decodeCodeCarrier := typeCodeEquiv inner.Code hcode
  decodedType code := typeCode (inner.El code) (hel code)
  decodeDecodedType code := typeCodeEquiv (inner.El code) (hel code)

/-- **Embeddings into `V_κ` are exactly the small universes.** -/
theorem nonempty_universeEmbedding_iff (hκ : κ.IsInaccessible)
    (inner : SemanticTarskiUniverse.{u, u}) :
    Nonempty (UniverseEmbedding (vonNeumannUniverse κ) inner) ↔
      #inner.Code < κ ∧ ∀ code, #(inner.El code) < κ := by
  constructor
  · rintro ⟨e⟩
    refine ⟨?_, fun code => ?_⟩
    · rw [← Cardinal.mk_congr e.decodeCodeCarrier, card_el]
      exact card_lt_of_mem_inaccessible hκ e.codeCarrier.2
    · rw [← Cardinal.mk_congr (e.decodeDecodedType code), card_el]
      exact card_lt_of_mem_inaccessible hκ (e.decodedType code).2
  · rintro ⟨hcode, hel⟩
    exact ⟨universeEmbeddingOfSmall inner hcode hel⟩

/-- **Superuniverse closure of `V_κ`, characterized.** -/
theorem superuniverseFor_iff (hκ : κ.IsInaccessible)
    (operator : SmallFamilyEnclosingUniverseOperator.{u}) :
    SuperuniverseFor (vonNeumannUniverse κ) operator ↔
      ∀ family : (vonNeumannUniverse κ).InternalFamily,
        #(operator.enclose ((vonNeumannUniverse κ).El family.1)
          (fun index => (vonNeumannUniverse κ).El (family.2 index))).Code < κ ∧
        ∀ code, #((operator.enclose ((vonNeumannUniverse κ).El family.1)
          (fun index => (vonNeumannUniverse κ).El (family.2 index))).El code) < κ :=
  forall_congr' fun _ => nonempty_universeEmbedding_iff hκ _

/-! ## Cardinal bounds for the type formers -/

/-- Well-founded trees as Mathlib W-types. -/
def wTreeToWType {S : Type u} {P : S → Type u} : WTree S P → WType P
  | .sup shape children => WType.mk shape fun position => wTreeToWType (children position)

/-- Mathlib W-types as well-founded trees. -/
def wTypeToWTree {S : Type u} {P : S → Type u} : WType P → WTree S P
  | WType.mk shape children => .sup shape fun position => wTypeToWTree (children position)

theorem wTypeToWTree_wTreeToWType {S : Type u} {P : S → Type u} :
    ∀ tree : WTree S P, wTypeToWTree (wTreeToWType tree) = tree
  | .sup shape children => by
      simp only [wTreeToWType, wTypeToWTree]
      congr 1
      funext position
      exact wTypeToWTree_wTreeToWType (children position)

variable {μ : Cardinal.{u}}

theorem card_sigma_lt (hμ : μ.IsInaccessible) {D : Type u} {C : D → Type u} (hD : #D < μ)
    (hC : ∀ x, #(C x) < μ) : #(Σ x, C x) < μ := by
  rw [Cardinal.mk_sigma]
  exact Cardinal.sum_lt_of_isRegular hμ.isRegular hD hC

theorem card_pi_lt (hμ : μ.IsInaccessible) {D : Type u} {C : D → Type u} (hD : #D < μ)
    (hC : ∀ x, #(C x) < μ) : #((x : D) → C x) < μ :=
  calc #((x : D) → C x) ≤ #(D → Σ x, C x) :=
        Cardinal.mk_le_of_injective (f := fun g x => ⟨x, g x⟩)
          (fun _ _ h => funext fun x => sigma_mk_injective (congrFun h x))
    _ = #(Σ x, C x) ^ #D := (Cardinal.power_def _ _).symm
    _ < μ := power_lt_of_isStrongLimit hμ.isStrongLimit (card_sigma_lt hμ hD hC) hD

theorem card_sum_lt (hμ : μ.IsInaccessible) {L R : Type u} (hL : #L < μ) (hR : #R < μ) :
    #(L ⊕ R) < μ := by
  rw [← Cardinal.add_def]
  exact Cardinal.add_lt_of_lt hμ.aleph0_lt.le hL hR

theorem card_wTree_lt (hμ : μ.IsInaccessible) {S : Type u} {P : S → Type u} (hS : #S < μ)
    (hP : ∀ s, #(P s) < μ) : #(WTree S P) < μ := by
  have hsigma := card_sigma_lt hμ hS hP
  let θ : Cardinal.{u} := #S + #(Σ s, P s) + ℵ₀
  have θμ : θ < μ := Cardinal.add_lt_of_lt hμ.aleph0_lt.le
    (Cardinal.add_lt_of_lt hμ.aleph0_lt.le hS hsigma) hμ.aleph0_lt
  have θω : ℵ₀ ≤ θ := le_add_self
  have lamω : ℵ₀ ≤ 2 ^ θ := θω.trans (Cardinal.cantor θ).le
  have Sθ : #S ≤ θ := le_self_add.trans le_self_add
  have Pθ : ∀ s, #(P s) ≤ θ := fun s =>
    (Cardinal.mk_le_of_injective (sigma_mk_injective (i := s))).trans
      ((le_add_self).trans le_self_add)
  have bound : (Cardinal.sum fun s : S => (2 ^ θ) ^ #(P s)) ≤ 2 ^ θ :=
    calc (Cardinal.sum fun s : S => (2 ^ θ) ^ #(P s))
        ≤ Cardinal.sum fun _ : S => (2 ^ θ : Cardinal.{u}) := by
          refine Cardinal.sum_le_sum _ _ fun s => ?_
          calc (2 ^ θ) ^ #(P s) ≤ (2 ^ θ) ^ θ :=
                Cardinal.power_le_power_left (Cardinal.power_ne_zero _ two_ne_zero) (Pθ s)
            _ = 2 ^ θ := by rw [← Cardinal.power_mul, Cardinal.mul_eq_self θω]
      _ = #S * 2 ^ θ := Cardinal.sum_const' S _
      _ ≤ 2 ^ θ * 2 ^ θ := mul_le_mul_left (Sθ.trans (Cardinal.cantor θ).le) _
      _ = 2 ^ θ := Cardinal.mul_eq_self lamω
  calc #(WTree S P) ≤ #(WType P) :=
        Cardinal.mk_le_of_injective (f := wTreeToWType)
          (Function.LeftInverse.injective wTypeToWTree_wTreeToWType)
    _ ≤ 2 ^ θ := WType.cardinalMk_le_of_le bound
    _ < μ := hμ.isStrongPrelimit θμ

/-! ## The universe of `V_μ` as an enclosing universe -/

/-- Decoding for the universe of `V_μ` with codes at the level of the sets. -/
def levelEl (μ : Cardinal.{u}) (code : Shrink.{u} (V_ μ.ord : ZFSet.{u})) : Type u :=
  Shrink.{u} ((equivShrink (V_ μ.ord : ZFSet.{u})).symm code).1

theorem card_levelEl_lt (hμ : μ.IsInaccessible) (code : Shrink.{u} (V_ μ.ord : ZFSet.{u})) :
    #(levelEl μ code) < μ :=
  card_lt_of_mem_inaccessible hμ ((equivShrink (V_ μ.ord : ZFSet.{u})).symm code).2

theorem card_levelCodes (hμ : μ.IsInaccessible) :
    #(Shrink.{u} (V_ μ.ord : ZFSet.{u})) = μ := by
  change (V_ μ.ord).card = μ
  rw [ZFSet.card_vonNeumann, hμ.preBeth_ord]

/-- The code in `V_μ` of a type with fewer than `μ` elements. -/
def smallCode (μ : Cardinal.{u}) (T : Type u) (hT : #T < μ) :
    Shrink.{u} (V_ μ.ord : ZFSet.{u}) :=
  equivShrink (V_ μ.ord : ZFSet.{u}) ⟨(#T).ord.toZFSet, ZFSet.mem_vonNeumann.mpr (by
    rw [Ordinal.rank_toZFSet]; exact Cardinal.ord_lt_ord.mpr hT)⟩

theorem card_levelEl_smallCode (T : Type u) (hT : #T < μ) :
    #(levelEl μ (smallCode μ T hT)) = #T := by
  change (((equivShrink (V_ μ.ord : ZFSet.{u})).symm (smallCode μ T hT)).1).card = #T
  rw [smallCode, Equiv.symm_apply_apply]
  change (#T).ord.toZFSet.card = #T
  rw [Ordinal.card_toZFSet, Cardinal.card_ord]

/-- The small code of a type decodes to a type equivalent to it. -/
def smallCodeEquiv (T : Type u) (hT : #T < μ) : levelEl μ (smallCode μ T hT) ≃ T :=
  Classical.choice (Cardinal.eq.mp (card_levelEl_smallCode T hT))

/-- **The universe of `V_μ` around a family.** For inaccessible `μ` and a family of fewer than
`μ` types with fewer than `μ` elements each, the universe of `V_μ` contains the family and is
closed under the selected type formers. Every type former is coded by the initial ordinal of the
cardinality of the type it forms. -/
def levelEnvelope (hμ : μ.IsInaccessible) (A : Type u) (B : A → Type u) (hA : #A < μ)
    (hB : ∀ index, #(B index) < μ) : ClosedTarskiUniverseOver.{u, u} A B where
  Code := Shrink.{u} (V_ μ.ord : ZFSet.{u})
  El := levelEl μ
  baseCode := smallCode μ A hA
  elBase := smallCodeEquiv A hA
  fibreCode index := smallCode μ (B index) (hB index)
  elFibre index := smallCodeEquiv (B index) (hB index)
  emptyCode := smallCode μ (ULift.{u} Empty) (by simpa using hμ.pos)
  elEmpty := (smallCodeEquiv _ _).trans Equiv.ulift
  unitCode := smallCode μ (ULift.{u} PUnit.{1}) (by simpa using hμ.nat_lt 1)
  elUnit := (smallCodeEquiv _ _).trans Equiv.ulift
  natCode := smallCode μ (ULift.{u} Nat) (by simpa using hμ.aleph0_lt)
  elNat := (smallCodeEquiv _ _).trans Equiv.ulift
  sumCode left right := smallCode μ (levelEl μ left ⊕ levelEl μ right)
    (card_sum_lt hμ (card_levelEl_lt hμ left) (card_levelEl_lt hμ right))
  elSum _ _ := smallCodeEquiv _ _
  piCode domain codomain := smallCode μ ((argument : levelEl μ domain) →
      levelEl μ (codomain argument))
    (card_pi_lt hμ (card_levelEl_lt hμ domain) fun argument =>
      card_levelEl_lt hμ (codomain argument))
  elPi _ _ := smallCodeEquiv _ _
  sigmaCode domain codomain := smallCode μ (Σ argument : levelEl μ domain,
      levelEl μ (codomain argument))
    (card_sigma_lt hμ (card_levelEl_lt hμ domain) fun argument =>
      card_levelEl_lt hμ (codomain argument))
  elSigma _ _ := smallCodeEquiv _ _
  identityCode _ left right := smallCode μ (ULift.{u} (PLift (left = right)))
    (lt_of_le_of_lt (Cardinal.le_one_iff_subsingleton.mpr inferInstance)
      (by simpa using hμ.nat_lt 1))
  elIdentity _ _ _ := (smallCodeEquiv _ _).trans (Equiv.ulift.trans Equiv.plift)
  wCode shape position := smallCode μ (WTree (levelEl μ shape) fun value =>
      levelEl μ (position value))
    (card_wTree_lt hμ (card_levelEl_lt hμ shape) fun value =>
      card_levelEl_lt hμ (position value))
  elW _ _ := smallCodeEquiv _ _

/-! ## The least inaccessible envelope -/

/-- The inaccessible cardinals above a family: above the size of its index type and of each of
its types. -/
def envelopeCardinals (A : Type u) (B : A → Type u) : Set Cardinal.{u} :=
  {μ | μ.IsInaccessible ∧ #A < μ ∧ ∀ index, #(B index) < μ}

/-- Negative example: `ℵ₀` is never an envelope cardinal. -/
theorem aleph0_not_mem_envelopeCardinals (A : Type u) (B : A → Type u) :
    ℵ₀ ∉ envelopeCardinals A B :=
  fun h => (lt_irrefl _) h.1.aleph0_lt

/-- Positive example: under `CofinalInaccessibles`, every family has envelope cardinals. -/
theorem envelopeCardinals_nonempty (h : CofinalInaccessibles.{u}) (A : Type u)
    (B : A → Type u) : (envelopeCardinals A B).Nonempty := by
  obtain ⟨μ, hμ, above⟩ := h (#A + #(Σ index, B index)).ord
  have below : #A + #(Σ index, B index) < μ := Cardinal.ord_lt_ord.mp above
  refine ⟨μ, hμ, le_self_add.trans_lt below, fun index => ?_⟩
  exact ((Cardinal.mk_le_of_injective (sigma_mk_injective (i := index))).trans
    le_add_self).trans_lt below

/-- The least inaccessible cardinal above a family. -/
def leastEnvelopeCardinal (A : Type u) (B : A → Type u) : Cardinal.{u} :=
  sInf (envelopeCardinals A B)

theorem leastEnvelopeCardinal_mem (h : CofinalInaccessibles.{u}) (A : Type u)
    (B : A → Type u) : leastEnvelopeCardinal A B ∈ envelopeCardinals A B :=
  csInf_mem (envelopeCardinals_nonempty h A B)

theorem leastEnvelopeCardinal_le {A : Type u} {B : A → Type u}
    {μ : Cardinal.{u}} (hμ : μ ∈ envelopeCardinals A B) : leastEnvelopeCardinal A B ≤ μ :=
  csInf_le' hμ

/-- **The least inaccessible envelope.** Under `CofinalInaccessibles`, each family is enclosed in
the universe of `V_μ` for the least inaccessible `μ` above it. -/
def leastEnvelopeOperator (h : CofinalInaccessibles.{u}) :
    SmallFamilyEnclosingUniverseOperator.{u} where
  enclose A B := levelEnvelope (leastEnvelopeCardinal_mem h A B).1 A B
    (leastEnvelopeCardinal_mem h A B).2.1 (leastEnvelopeCardinal_mem h A B).2.2

/-- The envelope of a family has as many codes as the least inaccessible above the family. -/
theorem card_leastEnvelope_code (h : CofinalInaccessibles.{u}) (A : Type u) (B : A → Type u) :
    #((leastEnvelopeOperator h).enclose A B).Code = leastEnvelopeCardinal A B :=
  card_levelCodes (leastEnvelopeCardinal_mem h A B).1

/-! ## Superuniverse closure is the limit of inaccessibles -/

/-- **Superuniverse closure of `V_κ`.** For inaccessible `κ`, the universe of `V_κ` embeds the
least inaccessible envelope of each of its families exactly when `κ` is a limit of
inaccessibles. -/
theorem superuniverseFor_leastEnvelope_iff (h : CofinalInaccessibles.{u})
    (hκ : κ.IsInaccessible) :
    SuperuniverseFor (vonNeumannUniverse κ) (leastEnvelopeOperator h) ↔
      IsLimitOfInaccessibles κ := by
  rw [superuniverseFor_iff hκ]
  constructor
  · intro hsuper α hα
    let x : (vonNeumannUniverse κ).Code :=
      ⟨α.toZFSet, ZFSet.mem_vonNeumann.mpr (by rw [Ordinal.rank_toZFSet]; exact hα)⟩
    have hcode := (hsuper ⟨x, fun _ => x⟩).1
    have mem := leastEnvelopeCardinal_mem h ((vonNeumannUniverse κ).El x)
      (fun _ => (vonNeumannUniverse κ).El x)
    rw [card_leastEnvelope_code] at hcode
    refine ⟨_, mem.1, Cardinal.lt_ord.mpr ?_, hcode⟩
    have size := mem.2.1
    rw [card_el] at size
    change α.toZFSet.card < _ at size
    rwa [Ordinal.card_toZFSet] at size
  · intro hlim F
    obtain ⟨β, hβ, below⟩ := exists_liesBelow hκ F
    obtain ⟨ν, hν, βν, νκ⟩ := hlim β hβ
    have inLevel : ∀ {y : ZFSet.{u}}, y.rank < β → y ∈ V_ ν.ord :=
      fun hy => ZFSet.mem_vonNeumann.mpr (hy.trans βν)
    have hνmem : ν ∈ envelopeCardinals ((vonNeumannUniverse κ).El F.1)
        (fun index => (vonNeumannUniverse κ).El (F.2 index)) :=
      ⟨hν, card_lt_of_mem_inaccessible hν (inLevel below.1),
        fun index => card_lt_of_mem_inaccessible hν (inLevel (below.2 index))⟩
    have μν := leastEnvelopeCardinal_le hνmem
    have mem := leastEnvelopeCardinal_mem h ((vonNeumannUniverse κ).El F.1)
      (fun index => (vonNeumannUniverse κ).El (F.2 index))
    refine ⟨?_, fun code => ?_⟩
    · rw [card_leastEnvelope_code]
      exact μν.trans_lt νκ
    · exact ((card_levelEl_lt mem.1 code).trans_le μν).trans νκ

/-- A Mahlo cardinal is a superuniverse for the least inaccessible envelope. -/
theorem IsMahlo.superuniverseFor (h : CofinalInaccessibles.{u}) (hκ : IsMahlo κ) :
    SuperuniverseFor (vonNeumannUniverse κ) (leastEnvelopeOperator h) :=
  (superuniverseFor_leastEnvelope_iff h hκ.isInaccessible).mpr hκ.isLimitOfInaccessibles

/-- **Mahlo reflection gives superuniverse closure.** -/
theorem superuniverseFor_of_mahloReflection (h : CofinalInaccessibles.{u})
    (hκ : κ.IsInaccessible)
    (hreflect : MahloReflection (vonNeumannUniverse κ) (IsInaccessibleLevel κ)) :
    SuperuniverseFor (vonNeumannUniverse κ) (leastEnvelopeOperator h) :=
  (isMahlo_of_mahloReflection hκ hreflect).superuniverseFor h

/-- At the least inaccessible cardinal, superuniverse closure fails. -/
theorem IsLeastInaccessible.not_superuniverseFor (h : CofinalInaccessibles.{u})
    (hκ : IsLeastInaccessible κ) :
    ¬ SuperuniverseFor (vonNeumannUniverse κ) (leastEnvelopeOperator h) :=
  fun hsuper => hκ.not_isLimitOfInaccessibles
    ((superuniverseFor_leastEnvelope_iff h hκ.1).mp hsuper)

/-- **Superuniverse closure is strictly weaker than Mahlo reflection.** At the least inaccessible
limit of inaccessibles the universe of `V_κ` is a superuniverse and has no Mahlo reflection. -/
theorem IsLeastInaccessibleLimit.superuniverse_without_reflection
    (h : CofinalInaccessibles.{u}) (hκ : IsLeastInaccessibleLimit κ) :
    SuperuniverseFor (vonNeumannUniverse κ) (leastEnvelopeOperator h) ∧
      ¬ MahloReflection (vonNeumannUniverse κ) (IsInaccessibleLevel κ) :=
  ⟨(superuniverseFor_leastEnvelope_iff h hκ.1).mpr hκ.2.1,
    hκ.not_mahloReflection⟩

end

#print axioms nonempty_universeEmbedding_iff
#print axioms superuniverseFor_iff
#print axioms card_pi_lt
#print axioms card_wTree_lt
#print axioms envelopeCardinals_nonempty
#print axioms card_leastEnvelope_code
#print axioms superuniverseFor_leastEnvelope_iff
#print axioms IsMahlo.superuniverseFor
#print axioms superuniverseFor_of_mahloReflection
#print axioms IsLeastInaccessible.not_superuniverseFor
#print axioms IsLeastInaccessibleLimit.superuniverse_without_reflection

end Mettapedia.TypeTheory.MahloUniverses
