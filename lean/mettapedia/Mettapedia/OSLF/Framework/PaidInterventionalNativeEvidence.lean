import Mettapedia.OSLF.Framework.PaidInterventionalDescriptions
import Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Native families of complete paid experimental receipts

The base records the snapshot, intervention, request and observed answer.
A fibre retains its original experimental witness and actual paid assay,
not just the truth of the answer. Budget inclusions retain this origin and
admit the actual replay with the extra purse. Semantic comprehension and
dependent sums use the shared native presheaf constructions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.PaidInterventionalNativeEvidence

open _root_.CategoryTheory
open Mettapedia.GSLT.Causality.ProbeCampaign
open Mettapedia.OSLF.Framework.PaidInterventionalDescriptions
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafEvidenceTransport

variable {Snapshot Intervention Questions X Providers Clients : Type}
variable [DecidableEq X] [DecidableEq Providers] [DecidableEq Clients]

structure Key (Snapshot Intervention Questions X Providers Clients : Type) where
  snapshot : Snapshot
  intervention : Intervention
  request : Request Questions X Providers Clients
  answer : Bool


/-- `Origin` is the dependent operational/certificate witness supplied by
an experiment. `priorCost` computes its already paid charge; the remaining
assay has its own independently retained occurrence path and exact ledger. -/
structure Receipt (protocol : Protocol Questions X) (Origin : (Key Snapshot Intervention Questions X Providers Clients) → Type)
    (priorCost : ∀ key, Origin key → Nat) (key : Key Snapshot Intervention Questions X Providers Clients) where
  origin : Origin key
  assayBudget : Nat
  assay : CompletedReceipt protocol key.request assayBudget key.answer

namespace Receipt

variable {protocol : Protocol Questions X} {Origin : (Key Snapshot Intervention Questions X Providers Clients) → Type}
variable {priorCost : ∀ key, Origin key → Nat} {key : Key Snapshot Intervention Questions X Providers Clients}

def initial (receipt : Receipt protocol Origin priorCost key) : Nat :=
  match receipt with
  | .mk origin budget _ => priorCost key origin + budget

def spent (receipt : Receipt protocol Origin priorCost key) : Nat :=
  match receipt with
  | .mk origin _ assay => priorCost key origin + assay.round.spent

theorem ledger (receipt : Receipt protocol Origin priorCost key) :
    receipt.initial = receipt.assay.round.remaining + receipt.spent := by
  have conserved := receipt.assay.round.ledger
  dsimp [initial, spent]
  omega

end Receipt

structure Within (protocol : Protocol Questions X) (Origin : (Key Snapshot Intervention Questions X Providers Clients) → Type)
    (priorCost : ∀ key, Origin key → Nat) (allowance : Nat) (key : Key Snapshot Intervention Questions X Providers Clients) where
  receipt : Receipt protocol Origin priorCost key
  funded : receipt.initial ≤ allowance

namespace Within

variable {protocol : Protocol Questions X} {Origin : (Key Snapshot Intervention Questions X Providers Clients) → Type}
variable {priorCost : ∀ key, Origin key → Nat} {key : Key Snapshot Intervention Questions X Providers Clients} {first second third : Nat}

def widen (included : first ≤ second) (evidence : Within protocol Origin priorCost first key) :
    Within protocol Origin priorCost second key :=
  match evidence with
  | .mk receipt funded => ⟨receipt, funded.trans included⟩

theorem widen_origin (included : first ≤ second)
    (evidence : Within protocol Origin priorCost first key) :
    (evidence.widen included).receipt.origin = evidence.receipt.origin := rfl

theorem widen_identity (evidence : Within protocol Origin priorCost first key) :
    evidence.widen le_rfl = evidence := by cases evidence; rfl

theorem widen_composition (earlier : first ≤ second) (later : second ≤ third)
    (evidence : Within protocol Origin priorCost first key) :
    (evidence.widen earlier).widen later = evidence.widen (earlier.trans later) := rfl

/-- Replay the retained assay path. This never reruns a scheduling policy. -/
def actualReplay (evidence : Within protocol Origin priorCost first key) :
    CompletedReceipt protocol key.request
      (evidence.receipt.assayBudget + (first - evidence.receipt.initial)) key.answer :=
  evidence.receipt.assay.replay (first - evidence.receipt.initial)

theorem replay_answer (evidence : Within protocol Origin priorCost first key) :
    PaidInterventionalDescriptions.Round.answer evidence.actualReplay.round = some key.answer :=
  evidence.actualReplay.actual_answer

theorem replay_ledger (evidence : Within protocol Origin priorCost first key) :
    first = evidence.actualReplay.round.remaining + evidence.receipt.spent := by
  have conserved := evidence.receipt.ledger
  have replayed := evidence.receipt.assay.replay_balance (first - evidence.receipt.initial)
  change (evidence.actualReplay.round).remaining = _ at replayed
  have funded := evidence.funded
  omega

end Within

/-- Morphisms increase an available purse. The opposite indexing makes
native substitution follow these budget inclusions. -/
abbrev BudgetWorld := OrderDual Nat

/-- Complete witnesses admitted at an allowance. The witness may be a
modal-machine receipt or a resource-system path; its representation is not
replaced by another executor. -/
def fundedFace {Index : Type} (Evidence : Index → Type)
    (initial : ∀ key, Evidence key → Nat) : BudgetWorldᵒᵖ ⥤ Type where
  obj context := {receipt : Sigma Evidence // initial receipt.1 receipt.2 ≤ context.unop}
  map arrow := TypeCat.ofHom fun receipt =>
    ⟨receipt.val, receipt.property.trans (leOfHom arrow.unop)⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    apply Subtype.ext
    rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    apply Subtype.ext
    rfl

def witnessIndex {Index : Type} (Evidence : Index → Type)
    (initial : ∀ key, Evidence key → Nat) :
    fundedFace Evidence initial ⟶ (Functor.const BudgetWorldᵒᵖ).obj Index where
  app _ := TypeCat.ofHom fun receipt => receipt.val.1
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    rfl

/-- The native fibre retains the complete witness and its initial purse,
including the equality authenticating its declared public index. -/
def fundedFamily {Index : Type} (Evidence : Index → Type)
    (initial : ∀ key, Evidence key → Nat) :
    DisplayedFamily ((Functor.const BudgetWorldᵒᵖ).obj Index) :=
  observationFibreFamily (witnessIndex Evidence initial)

def introduce {Index : Type} (Evidence : Index → Type)
    (initial : ∀ key, Evidence key → Nat) (allowance : Nat) (key : Index)
    (evidence : Evidence key) (affordable : initial key evidence ≤ allowance) :
    (fundedFamily Evidence initial).obj ⟨Opposite.op allowance, key⟩ :=
  ⟨⟨⟨key, evidence⟩, affordable⟩, rfl⟩

theorem introduce_injective {Index : Type} (Evidence : Index → Type)
    (initial : ∀ key, Evidence key → Nat) (allowance : Nat) (key : Index)
    (first second : Evidence key) (firstFunded : initial key first ≤ allowance)
    (secondFunded : initial key second ≤ allowance)
    (same : introduce Evidence initial allowance key first firstFunded =
      introduce Evidence initial allowance key second secondFunded) : first = second := by
  have pairs : (⟨key, first⟩ : Sigma Evidence) = ⟨key, second⟩ :=
    congrArg (fun receipt => receipt.val.val) same
  exact eq_of_heq (Sigma.mk.inj pairs).2

theorem introduced_substitution {Index : Type} (Evidence : Index → Type)
    (initial : ∀ key, Evidence key → Nat) (first second : Nat) (included : first ≤ second)
    (key : Index) (evidence : Evidence key) (affordable : initial key evidence ≤ first) :
    (fundedFamily Evidence initial).map
      (CategoryOfElements.homMk (F := (Functor.const BudgetWorldᵒᵖ).obj Index)
        ⟨Opposite.op first, key⟩ ⟨Opposite.op second, key⟩
        (homOfLE (X := BudgetWorld) included).op rfl)
      (introduce Evidence initial first key evidence affordable) =
      introduce Evidence initial second key evidence (affordable.trans included) := rfl

def fundedComprehension {Index : Type} (Evidence : Index → Type)
    (initial : ∀ key, Evidence key → Nat) : BudgetWorldᵒᵖ ⥤ Type :=
  totalSpace (fundedFamily Evidence initial)

def answerBase : BudgetWorldᵒᵖ ⥤ Type := (Functor.const _).obj Bool

/-- A public answer forgets the receipt index; the dependent sum below
retains every preimage instead of choosing one. -/
def answerMap {Index : Type} (answer : Index → Bool) :
    (Functor.const BudgetWorldᵒᵖ).obj Index ⟶ answerBase where
  app _ := TypeCat.ofHom answer
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro key
    rfl

def answerReceipts {Index : Type} (Evidence : Index → Type)
    (initial : ∀ key, Evidence key → Nat) (answer : Index → Bool) :
    DisplayedFamily answerBase :=
  transport (answerMap answer) (fundedFamily Evidence initial)

def retainAnswer {Index : Type} (Evidence : Index → Type)
    (initial : ∀ key, Evidence key → Nat) (answer : Index → Bool)
    (allowance : Nat) (key : Index) (evidence : Evidence key)
    (affordable : initial key evidence ≤ allowance) :
    (answerReceipts Evidence initial answer).obj ⟨Opposite.op allowance, answer key⟩ :=
  (unit (answerMap answer) (fundedFamily Evidence initial)).app _
    (introduce Evidence initial allowance key evidence affordable)

theorem answer_retains_index {Index : Type} (Evidence : Index → Type)
    (initial : ∀ key, Evidence key → Nat) (answer : Index → Bool)
    (allowance : Nat) (key : Index) (evidence : Evidence key)
    (affordable : initial key evidence ≤ allowance) :
    (retainAnswer Evidence initial answer allowance key evidence affordable).val.1 = key := rfl

theorem answer_retains_witness {Index : Type} (Evidence : Index → Type)
    (initial : ∀ key, Evidence key → Nat) (answer : Index → Bool)
    (allowance : Nat) (key : Index) (evidence : Evidence key)
    (affordable : initial key evidence ≤ allowance) :
    (retainAnswer Evidence initial answer allowance key evidence affordable).val.2.val.val =
      (⟨key, evidence⟩ : Sigma Evidence) := rfl

def base (Snapshot Intervention Questions X Providers Clients : Type) :
    BudgetWorldᵒᵖ ⥤ Type :=
  (Functor.const _).obj (Key Snapshot Intervention Questions X Providers Clients)

def family (protocol : Protocol Questions X) (Origin : (Key Snapshot Intervention Questions X Providers Clients) → Type)
    (priorCost : ∀ key, Origin key → Nat) :
    DisplayedFamily (base Snapshot Intervention Questions X Providers Clients) where
  obj point := Within protocol Origin priorCost point.1.unop point.2
  map {first second} arrow := TypeCat.ofHom fun evidence => by
    rcases first with ⟨firstContext, firstKey⟩
    rcases second with ⟨secondContext, secondKey⟩
    have same : firstKey = secondKey := arrow.property
    cases same
    exact evidence.widen (leOfHom arrow.val.unop)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro evidence
    cases point with
    | mk context key =>
      exact Within.widen_identity evidence
  map_comp {first middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro evidence
    rcases first with ⟨firstContext, firstKey⟩
    rcases middle with ⟨middleContext, middleKey⟩
    rcases last with ⟨lastContext, lastKey⟩
    rcases earlier with ⟨earlier, sameEarlier⟩
    rcases later with ⟨later, sameLater⟩
    change firstKey = middleKey at sameEarlier
    change middleKey = lastKey at sameLater
    cases sameEarlier
    cases sameLater
    rfl

def comprehension (protocol : Protocol Questions X) (Origin : (Key Snapshot Intervention Questions X Providers Clients) → Type)
    (priorCost : ∀ key, Origin key → Nat) : BudgetWorldᵒᵖ ⥤ Type :=
  totalSpace (family protocol Origin priorCost)

def projection (protocol : Protocol Questions X) (Origin : (Key Snapshot Intervention Questions X Providers Clients) → Type)
    (priorCost : ∀ key, Origin key → Nat) :
    comprehension protocol Origin priorCost ⟶ base Snapshot Intervention Questions X Providers Clients :=
  totalProjection (family protocol Origin priorCost)

theorem comprehension_readout (protocol : Protocol Questions X) (Origin : (Key Snapshot Intervention Questions X Providers Clients) → Type)
    (priorCost : ∀ key, Origin key → Nat) (allowance : Nat)
    (key : Key Snapshot Intervention Questions X Providers Clients) (evidence : Within protocol Origin priorCost allowance key) :
    (projection protocol Origin priorCost).app (Opposite.op allowance) ⟨key, evidence⟩ = key := rfl

theorem comprehension_retains_origin (protocol : Protocol Questions X) (Origin : (Key Snapshot Intervention Questions X Providers Clients) → Type)
    (priorCost : ∀ key, Origin key → Nat) (allowance : Nat)
    (key : Key Snapshot Intervention Questions X Providers Clients) (first second : Within protocol Origin priorCost allowance key)
    (different : first.receipt.origin ≠ second.receipt.origin) :
    (⟨key, first⟩ : (comprehension protocol Origin priorCost).obj (Opposite.op allowance)) ≠
      ⟨key, second⟩ := by
  intro same
  have evidence : first = second := eq_of_heq (Sigma.mk.inj same).2
  exact different (congrArg (fun value => value.receipt.origin) evidence)

end Mettapedia.OSLF.Framework.PaidInterventionalNativeEvidence
