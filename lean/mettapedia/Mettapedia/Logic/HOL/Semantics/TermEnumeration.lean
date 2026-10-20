import Mettapedia.Logic.HOL.Semantics.BethTree
import Mathlib.Tactic.DeriveEncodable

/-!
# Computable enumerations of HOL obligations

The fair services of `HenkinWitnessService` and `BethTree` are computable from
enumerations of existential bodies and disjunction pairs.  This file supplies
those enumerations for every signature with encodable base types and
encodable constants, so the schedules run on a concrete signature.

* `RawTerm`: untyped terms with explicit binder and argument types, and
  constants paired with their types; `Encodable` by deriving.
* `erase` forgets the typing of a term; `check Γ τ` type-checks a raw term in
  context `Γ` at type `τ`; `check_erase`: checking an erased term returns it.
* `decodeBody`, `decodePair`: total decoders `ℕ → Body Const` and
  `ℕ → ClosedFormulaPair Const`, surjective (`decodeBody_surjective`,
  `decodePair_surjective`).
* `encodableWitnessServices`, `encodablePairService`, `encodableBodyService`:
  the services built from them, for the varying-domain Kripke route and for
  the tree Beth route.  Their schedules use no axioms.
* `provable_iff_treeBethConsequence_of_encodable`: tree Beth completeness with
  these computable services.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v

deriving instance Encodable for Ty

namespace TermEnumeration

/-- Untyped terms: variables are de Bruijn indices, constants come with their
types, and applications and binders carry the types needed to re-check them. -/
inductive RawTerm (Base : Type u) (C : Type v) : Type (max u v)
  | var : ℕ → RawTerm Base C
  | const : C → RawTerm Base C
  | app : Ty Base → RawTerm Base C → RawTerm Base C → RawTerm Base C
  | lam : Ty Base → RawTerm Base C → RawTerm Base C
  | top : RawTerm Base C
  | bot : RawTerm Base C
  | and : RawTerm Base C → RawTerm Base C → RawTerm Base C
  | or : RawTerm Base C → RawTerm Base C → RawTerm Base C
  | imp : RawTerm Base C → RawTerm Base C → RawTerm Base C
  | not : RawTerm Base C → RawTerm Base C
  | eq : Ty Base → RawTerm Base C → RawTerm Base C → RawTerm Base C
  | all : Ty Base → RawTerm Base C → RawTerm Base C
  | ex : Ty Base → RawTerm Base C → RawTerm Base C
  deriving Encodable

variable {Base : Type u} {K : Ty Base → Type v}

/-- The index of a variable. -/
def varIndex : {Γ : Ctx Base} → {τ : Ty Base} → Var Γ τ → ℕ
  | _, _, .vz => 0
  | _, _, .vs v => varIndex v + 1

/-- Forget the typing of a term. -/
def erase : {Γ : Ctx Base} → {τ : Ty Base} → Term K Γ τ → RawTerm Base (Σ τ : Ty Base, K τ)
  | _, _, .var v => .var (varIndex v)
  | _, τ, .const c => .const ⟨τ, c⟩
  | _, _, .app (σ := σ) f t => .app σ (erase f) (erase t)
  | _, _, .lam (σ := σ) t => .lam σ (erase t)
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, _, .and a b => .and (erase a) (erase b)
  | _, _, .or a b => .or (erase a) (erase b)
  | _, _, .imp a b => .imp (erase a) (erase b)
  | _, _, .not a => .not (erase a)
  | _, _, .eq (τ := τ) a b => .eq τ (erase a) (erase b)
  | _, _, .all (σ := σ) a => .all σ (erase a)
  | _, _, .ex (σ := σ) a => .ex σ (erase a)

variable [DecidableEq Base]

/-- Look up a de Bruijn index at a type. -/
def lookupVar : (Γ : Ctx Base) → ℕ → (τ : Ty Base) → Option (Var Γ τ)
  | [], _, _ => none
  | σ :: _, 0, τ => if h : σ = τ then some (h ▸ Var.vz) else none
  | _ :: Γ, n + 1, τ => (lookupVar Γ n τ).map Var.vs

theorem lookupVar_varIndex : ∀ {Γ : Ctx Base} {τ : Ty Base} (v : Var Γ τ),
    lookupVar Γ (varIndex v) τ = some v
  | _, _, .vz => by simp [lookupVar, varIndex]
  | _, _, .vs v => by simp [lookupVar, varIndex, lookupVar_varIndex v]

/-- Type-check a raw term in a context at a type. -/
def check : (Γ : Ctx Base) → (τ : Ty Base) → RawTerm Base (Σ τ : Ty Base, K τ) →
    Option (Term K Γ τ)
  | Γ, τ, .var n => (lookupVar Γ n τ).map .var
  | _, τ, .const ⟨τ', c⟩ => if h : τ' = τ then some (h ▸ .const c) else none
  | Γ, τ, .app σ f t =>
      match check Γ (σ ⇒ τ) f, check Γ σ t with
      | some f', some t' => some (.app f' t')
      | _, _ => none
  | Γ, .arr σ τ, .lam σ' t =>
      if σ' = σ then (check (σ :: Γ) τ t).map .lam else none
  | _, .prop, .top => some .top
  | _, .prop, .bot => some .bot
  | Γ, .prop, .and a b =>
      match check Γ .prop a, check Γ .prop b with
      | some a', some b' => some (.and a' b')
      | _, _ => none
  | Γ, .prop, .or a b =>
      match check Γ .prop a, check Γ .prop b with
      | some a', some b' => some (.or a' b')
      | _, _ => none
  | Γ, .prop, .imp a b =>
      match check Γ .prop a, check Γ .prop b with
      | some a', some b' => some (.imp a' b')
      | _, _ => none
  | Γ, .prop, .not a => (check Γ .prop a).map .not
  | Γ, .prop, .eq τ a b =>
      match check Γ τ a, check Γ τ b with
      | some a', some b' => some (.eq a' b')
      | _, _ => none
  | Γ, .prop, .all σ a => (check (σ :: Γ) .prop a).map .all
  | Γ, .prop, .ex σ a => (check (σ :: Γ) .prop a).map .ex
  | _, _, _ => none

/-- **Checking an erased term returns it.** -/
theorem check_erase : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term K Γ τ),
    check Γ τ (erase t) = some t
  | _, _, .var v => by simp [erase, check, lookupVar_varIndex]
  | _, _, .const c => by simp [erase, check]
  | _, _, .app f t => by simp [erase, check, check_erase f, check_erase t]
  | _, _, .lam t => by simp [erase, check, check_erase t]
  | _, _, .top => by simp [erase, check]
  | _, _, .bot => by simp [erase, check]
  | _, _, .and a b => by simp [erase, check, check_erase a, check_erase b]
  | _, _, .or a b => by simp [erase, check, check_erase a, check_erase b]
  | _, _, .imp a b => by simp [erase, check, check_erase a, check_erase b]
  | _, _, .not a => by simp [erase, check, check_erase a]
  | _, _, .eq a b => by simp [erase, check, check_erase a, check_erase b]
  | _, _, .all a => by simp [erase, check, check_erase a]
  | _, _, .ex a => by simp [erase, check, check_erase a]

end TermEnumeration

/-! ## Enumerations of bodies and pairs -/

namespace TermEnumeration

variable {Base : Type u} {Const : Ty Base → Type v}
variable [Encodable Base] [∀ τ, Encodable (Const τ)]

open Mettapedia.Logic.HOL.WithParams ClosedTheorySet

instance : DecidableEq Base := Encodable.decidableEqOfEncodable Base

/-- Raw terms over the parameter signature. -/
abbrev Raw (Base : Type u) (Const : Ty Base → Type v) :=
  RawTerm Base (Σ τ : Ty Base, WithParams Const τ)

instance : Encodable (Σ τ : Ty Base, WithParams Const τ) := inferInstance

/-- Decode an existential body: a binder type and a raw body checked in the
one-variable context. -/
def decodeBody (n : ℕ) : Body Const :=
  match (Encodable.decode n : Option (Ty Base × Raw Base Const)) with
  | some (σ, r) =>
      match check [σ] .prop r with
      | some φ => ⟨σ, φ⟩
      | none => ⟨.prop, .top⟩
  | none => ⟨.prop, .top⟩

/-- Decode a disjunction pair: two raw closed formulas. -/
def decodePair (n : ℕ) : ClosedFormulaPair Const :=
  match (Encodable.decode n : Option (Raw Base Const × Raw Base Const)) with
  | some (r₁, r₂) =>
      match check [] .prop r₁, check [] .prop r₂ with
      | some φ, some ψ => (φ, ψ)
      | _, _ => (.top, .top)
  | none => (.top, .top)

theorem decodeBody_encode (b : Body Const) :
    decodeBody (Encodable.encode ((b.1, erase b.2) : Ty Base × Raw Base Const)) = b := by
  obtain ⟨σ, φ⟩ := b
  simp [decodeBody, Encodable.encodek, check_erase]

theorem decodePair_encode (p : ClosedFormulaPair Const) :
    decodePair (Encodable.encode ((erase p.1, erase p.2) : Raw Base Const × Raw Base Const)) =
      p := by
  obtain ⟨φ, ψ⟩ := p
  simp [decodePair, Encodable.encodek, check_erase]

theorem decodeBody_surjective : Function.Surjective (decodeBody (Base := Base) (Const := Const)) :=
  fun b => ⟨_, decodeBody_encode b⟩

theorem decodePair_surjective :
    Function.Surjective (decodePair (Base := Base) (Const := Const)) :=
  fun p => ⟨_, decodePair_encode p⟩

/-! ## Computable services -/

/-- The fair services of Henkin witness obligations at every layer, computed
from the decoders (the varying-domain Kripke route). -/
def encodableWitnessServices (ℓ : ℕ) :
    KripkeHenkin.SupportedCanonicalFrame.WitnessService (Base := Base) (Const := Const) ℓ :=
  KripkeHenkin.SupportedCanonicalFrame.witnessServiceOfEnumerations decodeBody
    decodeBody_surjective decodePair decodePair_surjective ℓ

/-- The fair pair service of the tree Beth route. -/
def encodablePairService : EligibleService (fun _ (_ : ClosedFormulaPair Const) => True) :=
  BethTree.serviceOfEnumeration decodePair decodePair_surjective (.top, .top)

/-- The fair body service of the tree Beth route. -/
def encodableBodyService : EligibleService (fun _ (_ : Body Const) => True) :=
  BethTree.serviceOfEnumeration decodeBody decodeBody_surjective ⟨.prop, .top⟩

/-- **Tree Beth completeness with computable services**, for signatures with
encodable base types and constants. -/
theorem provable_iff_treeBethConsequence_of_encodable {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)} (hT : BethTree.ParamFree T) :
    Provable (Const := WithParams Const) T θ ↔ TreeBethConsequence T θ :=
  BethTree.provable_iff_treeBethConsequence_of_services hT encodablePairService
    encodableBodyService

/-- **Varying-domain Kripke completeness with computable services**, for
signatures with encodable base types and constants and a closed term at every
base type. -/
theorem provable_of_consequence_of_encodable (inhBase : ∀ b : Base, ClosedTerm Const (.base b))
    {T : ClosedTheorySet Const} {θ : ClosedFormula Const}
    (h : KripkeVarying.Consequence.{u, v, max u v} T θ) :
    Provable (Const := Const) T θ :=
  KripkeHenkin.SupportedCanonicalFrame.provable_of_consequence_of_services
    encodableWitnessServices inhBase h

/-- The pair schedule of `encodablePairService`. -/
def encodablePairSchedule : ℕ → ClosedFormulaPair Const :=
  EligibleService.enumSchedule (fun _ _ => true) decodePair (.top, .top)

/-- The body schedule of `encodableBodyService`. -/
def encodableBodySchedule : ℕ → Body Const :=
  EligibleService.enumSchedule (fun _ _ => true) decodeBody ⟨.prop, .top⟩

theorem encodablePairService_serve :
    (encodablePairService (Base := Base) (Const := Const)).serve = encodablePairSchedule := rfl

theorem encodableBodyService_serve :
    (encodableBodyService (Base := Base) (Const := Const)).serve = encodableBodySchedule := rfl

end TermEnumeration

/-! ## Controls over the one-point signature -/

namespace TermEnumeration

open KripkeVarying.Canonical BethTree ClosedTheorySet

instance (τ : Ty Unit) : Encodable (PointConst τ) :=
  Encodable.ofLeftInjection (fun _ => ())
    (fun _ => match τ with
      | .base () => some .o
      | _ => none)
    (by intro c; cases c; rfl)

/-- Positive control: tree Beth completeness with the computable services of
the one-point signature returns a derivation of `∃ x, x = o`. -/
theorem pointExistsEqO_provable_of_encodable_treeBeth :
    Provable (Const := WithParams PointConst) ∅ pointExistsEqOParam :=
  (provable_iff_treeBethConsequence_of_encodable (Base := Unit) (Const := PointConst)
    paramFree_empty).mpr pointExistsEqO_treeBethConsequence

/-- Positive control: varying-domain Kripke completeness with the computable
witness services of the one-point signature. -/
theorem pointExistsEqO_provable_of_encodable_kripke :
    Provable (Const := PointConst) ∅ pointExistsEqO :=
  provable_of_consequence_of_encodable pointInhabitant pointExistsEqO_consequence

/-- Negative control: the checker rejects an ill-typed raw term, a lambda read
at type `prop`. -/
theorem check_rejects_lam_at_prop :
    check (K := WithParams PointConst) [] .prop (.lam .prop .top) = none := rfl

/-- Negative control: the checker rejects a variable outside the context. -/
theorem check_rejects_free_var :
    check (K := WithParams PointConst) [] .prop (.var 0) = none := rfl

end TermEnumeration

end Mettapedia.Logic.HOL
