import Mettapedia.OSLF.Framework.PaidInterventionalNativeEvidence

/-!
# Coherent transport of complete paid witnesses

An admitted witness map must supply its actual action on complete receipts
and an exact initial-charge comparison. It induces a natural map of native
families and their comprehension spaces. The dependent sum retains the
original witness even when the public index map is not injective; its
universal elimination computes the supplied mapped receipt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.PaidInterventionalEvidenceTransport

open _root_.CategoryTheory
open PaidInterventionalNativeEvidence
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafEvidenceTransport
open Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal

variable {I J K : Type}
variable {E : I → Type} {F : J → Type} {G : K → Type}
variable {sourceCharge : ∀ i, E i → Nat} {targetCharge : ∀ j, F j → Nat}
variable {lastCharge : ∀ k, G k → Nat}

structure WitnessMap (E : I → Type) (F : J → Type)
    (sourceCharge : ∀ i, E i → Nat) (targetCharge : ∀ j, F j → Nat) where
  index : I → J
  witness : ∀ i, E i → F (index i)
  charge : ∀ i evidence, targetCharge (index i) (witness i evidence) = sourceCharge i evidence

namespace WitnessMap

def id (E : I → Type) (charge : ∀ i, E i → Nat) : WitnessMap E E charge charge where
  index := _root_.id
  witness _ := _root_.id
  charge _ _ := rfl

def comp (first : WitnessMap E F sourceCharge targetCharge)
    (second : WitnessMap F G targetCharge lastCharge) : WitnessMap E G sourceCharge lastCharge where
  index := second.index ∘ first.index
  witness i evidence := second.witness (first.index i) (first.witness i evidence)
  charge i evidence := (second.charge _ _).trans (first.charge i evidence)

def indices (map : WitnessMap E F sourceCharge targetCharge) :
    (Functor.const BudgetWorldᵒᵖ).obj I ⟶ (Functor.const BudgetWorldᵒᵖ).obj J where
  app _ := TypeCat.ofHom map.index
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro index
    rfl

/-- Mapping a retained witness preserves its actual funding admission. -/
def body (map : WitnessMap E F sourceCharge targetCharge) :
    fundedFamily E sourceCharge ⟶
      reindexDisplayed map.indices (fundedFamily F targetCharge) where
  app point := TypeCat.ofHom fun receipt =>
    ⟨⟨⟨map.index receipt.val.val.1,
        map.witness receipt.val.val.1 receipt.val.val.2⟩,
      by rw [map.charge]; exact receipt.val.property⟩,
      congrArg map.index receipt.property⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem body_introduce (map : WitnessMap E F sourceCharge targetCharge)
    (allowance : Nat) (index : I) (evidence : E index)
    (affordable : sourceCharge index evidence ≤ allowance) :
    map.body.app ⟨Opposite.op allowance, index⟩
      (introduce E sourceCharge allowance index evidence affordable) =
      introduce F targetCharge allowance (map.index index) (map.witness index evidence)
        (by rw [map.charge]; exact affordable) := rfl

def total (map : WitnessMap E F sourceCharge targetCharge) :
    fundedComprehension E sourceCharge ⟶ fundedComprehension F targetCharge :=
  evidenceTotalMap map.indices map.body

theorem total_readout (map : WitnessMap E F sourceCharge targetCharge)
    (allowance : Nat) (index : I) (evidence : E index)
    (affordable : sourceCharge index evidence ≤ allowance) :
    map.total.app (Opposite.op allowance)
      ⟨index, introduce E sourceCharge allowance index evidence affordable⟩ =
      ⟨map.index index,
        introduce F targetCharge allowance (map.index index) (map.witness index evidence)
          (by rw [map.charge]; exact affordable)⟩ := rfl

theorem total_identity : (id E sourceCharge).total = 𝟙 (fundedComprehension E sourceCharge) := by
  ext context receipt
  rcases receipt with ⟨index, ⟨⟨⟨original, evidence⟩, funded⟩, same⟩⟩
  change original = index at same
  subst index
  rfl

theorem total_composition (first : WitnessMap E F sourceCharge targetCharge)
    (second : WitnessMap F G targetCharge lastCharge) :
    (first.comp second).total = first.total ≫ second.total := by
  ext context receipt
  rfl

/-- Native substitution and the actual witness map commute on the entire
comprehension, including its dependent receipt coordinate. -/
theorem total_substitution (map : WitnessMap E F sourceCharge targetCharge)
    {first second : BudgetWorldᵒᵖ} (change : first ⟶ second)
    (receipt : (fundedComprehension E sourceCharge).obj first) :
    (fundedComprehension F targetCharge).map change (map.total.app first receipt) =
      map.total.app second ((fundedComprehension E sourceCharge).map change receipt) :=
  ConcreteCategory.congr_hom (map.total.naturality change).symm receipt

def receipts (map : WitnessMap E F sourceCharge targetCharge) :
    DisplayedFamily ((Functor.const BudgetWorldᵒᵖ).obj J) :=
  transport map.indices (fundedFamily E sourceCharge)

/-- Insert a source receipt without choosing an inverse of its public
index. Its source origin remains available to dependent eliminators. -/
def retain (map : WitnessMap E F sourceCharge targetCharge)
    (allowance : Nat) (index : I) (evidence : E index)
    (affordable : sourceCharge index evidence ≤ allowance) :
    map.receipts.obj ⟨Opposite.op allowance, map.index index⟩ :=
  (unit map.indices (fundedFamily E sourceCharge)).app _
    (introduce E sourceCharge allowance index evidence affordable)

theorem retain_origin (map : WitnessMap E F sourceCharge targetCharge)
    (allowance : Nat) (index : I) (evidence : E index)
    (affordable : sourceCharge index evidence ≤ allowance) :
    (map.retain allowance index evidence affordable).val.2.val.val =
      (⟨index, evidence⟩ : Sigma E) := rfl

theorem retain_injective (map : WitnessMap E F sourceCharge targetCharge)
    (allowance : Nat) (index : I) (first second : E index)
    (firstFunded : sourceCharge index first ≤ allowance)
    (secondFunded : sourceCharge index second ≤ allowance)
    (same : map.retain allowance index first firstFunded =
      map.retain allowance index second secondFunded) : first = second := by
  have original : (⟨index, first⟩ : Sigma E) = ⟨index, second⟩ :=
    congrArg (fun receipt => receipt.val.2.val.val) same
  exact eq_of_heq (Sigma.mk.inj original).2

/-- Reassociate two origin-retaining sums without discarding either
receipt layer. This is the canonical comparison for composed index maps. -/
def receiptComposition (first : WitnessMap E F sourceCharge targetCharge)
    (second : WitnessMap F G targetCharge lastCharge) :
    transport second.indices first.receipts ≅ (first.comp second).receipts :=
  compositionIso first.indices second.indices (fundedFamily E sourceCharge)

theorem retained_composition (first : WitnessMap E F sourceCharge targetCharge)
    (second : WitnessMap F G targetCharge lastCharge)
    (allowance : Nat) (index : I) (evidence : E index)
    (affordable : sourceCharge index evidence ≤ allowance) :
    (receiptComposition first second).hom.app
      ⟨Opposite.op allowance, second.index (first.index index)⟩
      ((unit second.indices first.receipts).app
        ⟨Opposite.op allowance, first.index index⟩
        (first.retain allowance index evidence affordable)) =
      (first.comp second).retain allowance index evidence affordable :=
  composition_unit first.indices second.indices (fundedFamily E sourceCharge) _ _

def eliminate (map : WitnessMap E F sourceCharge targetCharge) :
    map.receipts ⟶ fundedFamily F targetCharge := descend map.indices map.body

theorem eliminate_retained (map : WitnessMap E F sourceCharge targetCharge)
    (allowance : Nat) (index : I) (evidence : E index)
    (affordable : sourceCharge index evidence ≤ allowance) :
    map.eliminate.app ⟨Opposite.op allowance, map.index index⟩
      (map.retain allowance index evidence affordable) =
      introduce F targetCharge allowance (map.index index) (map.witness index evidence)
        (by rw [map.charge]; exact affordable) :=
  (descend_unit map.indices map.body _ _).trans (map.body_introduce _ _ _ _)

theorem eliminate_unique (map : WitnessMap E F sourceCharge targetCharge)
    (other : map.receipts ⟶ fundedFamily F targetCharge)
    (computes : restrict map.indices other = map.body) : other = map.eliminate :=
  descend_unique map.indices map.body other computes

end WitnessMap

end Mettapedia.OSLF.Framework.PaidInterventionalEvidenceTransport
