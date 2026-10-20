import Mettapedia.Logic.HOL.TermModel.HenkinCompleteness
import Mettapedia.Logic.HOL.ProofSyntaxConstantSubstitution
import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics
import Mettapedia.Logic.HOL.PropositionalSlice
import Mathlib.Tactic.DeriveCountable
import Mathlib.Logic.Equiv.List

/-!
# Virtue 5: the proof system is sound and complete for general models

The proof system is the extensional natural-deduction calculus `ExtDerivation`
with one extra closed axiom, excluded middle stated once by quantifying over
`prop` (`excludedMiddle`). Its semantics is the class of extensional Henkin
models: Henkin models whose admissible functions respect extensional equality
(`HenkinModel.FunctionsRespectEqv`).

* `soundness`: every consequence is true in every extensional Henkin model of
  the theory, at every universe level, including models with empty base types.
* `exists_model_of_consistent`: a consistent theory has an extensional Henkin
  model (Henkin 1950), for a countable signature in which every base type has a
  closed term.
* `provable_iff_valid` and `consistent_iff_satisfiable`: the two directions
  together.

The construction reuses the witnessed term model of `TermModel/`. Two facts
are new here and make the classical corollary usable:

* the parameter calculus over `WithParams Const` assumes that every type is
  inhabited, since every parameter is a closed term
  (`EmptyBase.image_inconsistent`); so a closed inhabitant at every base type is
  needed to return to the original signature (`provable_of_provable_image`);
* excluded middle enters as one parameter-free axiom from which the whole
  `EMSchema` is derivable (`provable_emSchema_of_mem`).

No theory over the parameter signature is both parameter-free and contains
`EMSchema`, because `EMSchema` contains instances with parameters
(`classical_corollary_hypotheses_unsatisfiable`). The parameter-signature
corollary `ClosedTheorySet.henkin_model_exists_of_consistent_classical` therefore
asks that the theory prove the schema, as the single axiom does
(`provable_emSchema_of_mem`).

Without the excluded-middle axiom the calculus is not complete for these
models: `p ∨ ¬ p` for a propositional constant `p` is true in every Henkin model
and not derivable (`incomplete_without_excludedMiddle`, from
`PropositionalSlice.excludedMiddle_not_provable`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v w

deriving instance Countable for Ty
deriving instance Countable for Var

namespace SevenVirtues

open ClosedTheorySet WithParams

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Countability of the syntax -/

/-- The untyped skeleton of an intrinsically typed term. It records every type
that the typed term leaves implicit, so the skeleton determines the term. -/
inductive TermCode (B : Type u) (K : Type v) : Type (max u v) where
  | var : Nat → TermCode B K
  | const : K → TermCode B K
  | app : Ty B → TermCode B K → TermCode B K → TermCode B K
  | lam : Ty B → TermCode B K → TermCode B K
  | top : TermCode B K
  | bot : TermCode B K
  | and : TermCode B K → TermCode B K → TermCode B K
  | or : TermCode B K → TermCode B K → TermCode B K
  | imp : TermCode B K → TermCode B K → TermCode B K
  | not : TermCode B K → TermCode B K
  | eq : Ty B → TermCode B K → TermCode B K → TermCode B K
  | all : Ty B → TermCode B K → TermCode B K
  | ex : Ty B → TermCode B K → TermCode B K
  deriving Countable

/-- The de Bruijn index of a typed variable. -/
def varIndex : {Γ : Ctx Base} → {τ : Ty Base} → Var Γ τ → Nat
  | _, _, .vz => 0
  | _, _, .vs v => varIndex v + 1

theorem varIndex_injective :
    ∀ {Γ : Ctx Base} {τ : Ty Base} {x y : Var Γ τ}, varIndex x = varIndex y → x = y
  | _, _, .vz, .vz, _ => rfl
  | _, _, .vz, .vs _, h => by simp [varIndex] at h
  | _, _, .vs _, .vz, h => by simp [varIndex] at h
  | _, _, .vs x, .vs y, h => by
      have : varIndex x = varIndex y := by simpa [varIndex] using h
      rw [varIndex_injective this]

/-- Encode a term by its skeleton. -/
def termCode : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ →
    TermCode Base (Σ τ : Ty Base, Const τ)
  | _, _, .var v => .var (varIndex v)
  | _, τ, .const c => .const ⟨τ, c⟩
  | _, _, .app (σ := σ) f a => .app σ (termCode f) (termCode a)
  | _, _, .lam (σ := σ) b => .lam σ (termCode b)
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, _, .and p q => .and (termCode p) (termCode q)
  | _, _, .or p q => .or (termCode p) (termCode q)
  | _, _, .imp p q => .imp (termCode p) (termCode q)
  | _, _, .not p => .not (termCode p)
  | _, _, .eq (τ := τ) t s => .eq τ (termCode t) (termCode s)
  | _, _, .all (σ := σ) b => .all σ (termCode b)
  | _, _, .ex (σ := σ) b => .ex σ (termCode b)

theorem termCode_injective {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    ∀ {t' : Term Const Γ τ}, termCode t = termCode t' → t = t' := by
  induction t with
  | var v =>
      intro t' h
      cases t' <;> simp [termCode] at h
      rw [varIndex_injective h]
  | const c =>
      intro t' h
      cases t' <;> simp [termCode] at h
      rw [h]
  | app f a ihf iha =>
      intro t' h
      cases t' <;> simp [termCode] at h
      obtain ⟨rfl, hf, ha⟩ := h
      rw [ihf hf, iha ha]
  | lam b ih =>
      intro t' h
      cases t' <;> simp [termCode] at h
      rw [ih h]
  | top => intro t' h; cases t' <;> simp [termCode] at h ⊢
  | bot => intro t' h; cases t' <;> simp [termCode] at h ⊢
  | and p q ihp ihq =>
      intro t' h
      cases t' <;> simp [termCode] at h
      rw [ihp h.1, ihq h.2]
  | or p q ihp ihq =>
      intro t' h
      cases t' <;> simp [termCode] at h
      rw [ihp h.1, ihq h.2]
  | imp p q ihp ihq =>
      intro t' h
      cases t' <;> simp [termCode] at h
      rw [ihp h.1, ihq h.2]
  | not p ih =>
      intro t' h
      cases t' <;> simp [termCode] at h
      rw [ih h]
  | eq t s iht ihs =>
      intro t' h
      cases t' <;> simp [termCode] at h
      obtain ⟨rfl, ht, hs⟩ := h
      rw [iht ht, ihs hs]
  | all b ih =>
      intro t' h
      cases t' <;> simp [termCode] at h
      obtain ⟨rfl, hb⟩ := h
      rw [ih hb]
  | ex b ih =>
      intro t' h
      cases t' <;> simp [termCode] at h
      obtain ⟨rfl, hb⟩ := h
      rw [ih hb]

instance termCountable [Countable Base] [∀ τ, Countable (Const τ)]
    (Γ : Ctx Base) (τ : Ty Base) : Countable (Term Const Γ τ) :=
  Function.Injective.countable (fun _ _ h => termCode_injective _ h)

/-- A countable signature has a surjective enumeration of the one-variable
bodies that the witnessing construction must witness. -/
theorem exists_body_enumeration [Countable Base] [∀ τ, Countable (Const τ)] :
    ∃ enum : Nat → Body Const, ∀ b : Body Const, ∃ n, enum n = b := by
  have : Nonempty (Body Const) := ⟨⟨.prop, .top⟩⟩
  obtain ⟨enum, surjective⟩ := exists_surjective_nat (Body Const)
  exact ⟨enum, surjective⟩

/-! ## Excluded middle as one axiom -/

/-- Excluded middle, stated once: `∀ p : prop, p ∨ ¬ p`. -/
def excludedMiddle : ClosedFormula Const :=
  .all (.or (.var (.vz : Var [propTy] propTy)) (.not (.var .vz)))

/-- Every Henkin model satisfies excluded middle, because truth values are the
ambient propositions. -/
theorem models_excludedMiddle (M : HenkinModel.{u, v, w} Base Const) :
    M.models excludedMiddle := by
  classical
  intro p _
  exact Classical.em _

theorem mapConst_excludedMiddle {Const' : Ty Base → Type w}
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ) :
    mapConst f (excludedMiddle : ClosedFormula Const) = excludedMiddle := rfl

/-- Excluded middle at an arbitrary formula in context, from the single axiom
weakened into that context. -/
theorem extDerivation_em_of_lem {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    (lem : ExtDerivation Const Δ (.all (.or (.var (.vz : Var (propTy :: Γ) propTy))
      (.not (.var .vz)))))
    (φ : Formula Const Γ) :
    ExtDerivation Const Δ (.or φ (.not φ)) := by
  have h := ExtDerivation.allE φ lem
  simpa [instantiate, subst, Subst.single] using h

/-- The weakened single axiom is again the single axiom. -/
theorem weaken_lemBody {Γ : Ctx Base} {σ : Ty Base} :
    (weaken (σ := σ)
      (.all (.or (.var (.vz : Var (propTy :: Γ) propTy)) (.not (.var .vz))) :
        Formula Const Γ)) =
      .all (.or (.var (.vz : Var (propTy :: σ :: Γ) propTy)) (.not (.var .vz))) := rfl

/-- Every member of the excluded-middle schema is derivable from the single
axiom, over the parameter signature. -/
theorem extDerivation_emSchema (ψ : ClosedFormula (WithParams Const))
    (hψ : ψ ∈ EMSchema Const) :
    ExtDerivation (WithParams Const) [excludedMiddle] ψ := by
  rcases hψ with ⟨χ, rfl⟩ | ⟨σ, φ, rfl⟩
  · exact extDerivation_em_of_lem (.hyp (by simp [excludedMiddle])) χ
  · refine .allI ?_
    refine extDerivation_em_of_lem (.hyp ?_) φ
    simp [weakenHyps, excludedMiddle, weaken_lemBody]

/-- A theory containing the single axiom proves the whole schema. -/
theorem provable_emSchema_of_mem {T : ClosedTheorySet (WithParams Const)}
    (hLem : (excludedMiddle : ClosedFormula (WithParams Const)) ∈ T) :
    ∀ ψ ∈ EMSchema Const, Provable (Const := WithParams Const) T ψ := by
  intro ψ hψ
  refine ⟨[excludedMiddle], ?_, extDerivation_emSchema ψ hψ⟩
  intro ξ hξ
  simp only [List.mem_singleton] at hξ
  subst hξ
  exact hLem

/-- Adding the schema to a theory that contains the single axiom preserves
consistency. -/
theorem consistent_union_emSchema {T : ClosedTheorySet (WithParams Const)}
    (hLem : (excludedMiddle : ClosedFormula (WithParams Const)) ∈ T)
    (hCons : Consistent (Const := WithParams Const) T) :
    Consistent (Const := WithParams Const) (T ∪ EMSchema Const) := by
  rintro ⟨Γ, hΓ, d⟩
  apply hCons
  refine provable_of_closedTheory_provable_hyps (Const := WithParams Const) ?_ d
  intro ψ hψ
  rcases hΓ ψ hψ with hT | hEM
  · exact provable_of_mem (Const := WithParams Const) hT
  · exact provable_emSchema_of_mem hLem ψ hEM

/-! ## Parameters and closed inhabitants -/

/-- A closed term at every simple type, from closed terms at the base types. -/
def closedInhabitant (inh : ∀ b : Base, ClosedTerm Const (.base b)) :
    (τ : Ty Base) → ClosedTerm Const τ
  | .prop => .top
  | .base b => inh b
  | .arr σ τ => .lam (weaken (σ := σ) (closedInhabitant inh τ))

/-- Keep the original constants and send every parameter to the chosen
closed inhabitant of its type. -/
def eraseParams (inh : ∀ b : Base, ClosedTerm Const (.base b)) :
    ∀ {τ : Ty Base}, WithParams Const τ → ClosedTerm Const τ
  | _, .inl c => .const c
  | τ, .inr _ => closedInhabitant inh τ

theorem substConst_eraseParams_mapConst (inh : ∀ b : Base, ClosedTerm Const (.base b))
    {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    substConst (eraseParams inh) (mapConst (fun {_} c => inj c) t) = t := by
  rw [substConst_mapConst]
  calc substConst (fun {τ} (c : Const τ) => eraseParams inh (inj c)) t
      = substConst (fun {τ} (c : Const τ) => (.const c : ClosedTerm Const τ)) t := rfl
    _ = mapConst (fun {_} c => c) t := substConst_constant_images (fun {_} c => c) t
    _ = t := mapConst_id t

/-- The image of a theory in the parameter signature. -/
def paramImage (T : ClosedTheorySet Const) : ClosedTheorySet (WithParams Const) :=
  (fun φ => mapConst (fun {_} c => inj c) φ) '' T

theorem paramImage_paramFree (T : ClosedTheorySet Const) :
    ∀ ψ ∈ paramImage T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ := by
  rintro _ ⟨φ, _, rfl⟩ σ k
  exact noConstOccurrence_param_of_inj k φ

/-- With a closed inhabitant at every base type, derivations over the
parameter signature return to the original signature. -/
theorem provable_of_provable_image (inh : ∀ b : Base, ClosedTerm Const (.base b))
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (h : Provable (Const := WithParams Const) (paramImage T)
      (mapConst (fun {_} c => inj c) φ)) :
    Provable (Const := Const) T φ := by
  obtain ⟨Γ, hΓ, d⟩ := h
  obtain ⟨proof⟩ := ProofSyntax.nonempty_iff.mpr d
  have back := ProofSyntax.nonempty_iff.mp ⟨ProofSyntax.substConst (eraseParams inh) proof⟩
  rw [substConst_eraseParams_mapConst] at back
  refine ⟨Γ.map (substConst (eraseParams inh)), ?_, back⟩
  intro ψ hψ
  obtain ⟨ψ', hψ', rfl⟩ := List.mem_map.mp hψ
  obtain ⟨χ, hχ, rfl⟩ := hΓ ψ' hψ'
  rw [substConst_eraseParams_mapConst]
  exact hχ

theorem consistent_image_of_consistent (inh : ∀ b : Base, ClosedTerm Const (.base b))
    {T : ClosedTheorySet Const} (hCons : Consistent (Const := Const) T) :
    Consistent (Const := WithParams Const) (paramImage T) := by
  intro h
  exact hCons (provable_of_provable_image inh (φ := .bot) h)

/-! ## Soundness -/

/-- **Soundness.** Whatever the theory proves together with excluded middle
is true in each of its extensional Henkin models, at every universe level. -/
theorem soundness {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (h : Provable (Const := Const) (insert excludedMiddle T) φ)
    (M : HenkinModel.{u, v, w} Base Const) (hExt : M.FunctionsRespectEqv)
    (hT : ∀ ψ ∈ T, M.models ψ) : M.models φ := by
  obtain ⟨Γ, hΓ, d⟩ := h
  refine Soundness.extDerivation_sound d (M := M) (ρ := fun v => nomatch v) hExt
    (by intro _ v; nomatch v) ?_
  intro ψ hψ
  rcases hΓ ψ hψ with rfl | hψT
  · exact models_excludedMiddle M
  · exact hT ψ hψT

/-! ## Completeness -/

/-- **Henkin's model existence theorem.** A theory over a countable signature
with a closed term at every base type, consistent together with excluded
middle, has an extensional Henkin model. -/
theorem exists_model_of_consistent [Countable Base] [∀ τ, Countable (Const τ)]
    (inh : ∀ b : Base, ClosedTerm Const (.base b)) {T : ClosedTheorySet Const}
    (hCons : Consistent (Const := Const) (insert excludedMiddle T)) :
    ∃ M : HenkinModel.{u, v, v} Base Const, M.FunctionsRespectEqv ∧ ∀ ψ ∈ T, M.models ψ := by
  obtain ⟨enum, henum⟩ := exists_body_enumeration (Const := Const)
  have hImage := consistent_image_of_consistent inh hCons
  have hWitness := witnessLimit_consistent (paramImage (insert excludedMiddle T)) enum hImage
    (paramImage_paramFree _)
  have hLem : (excludedMiddle : ClosedFormula (WithParams Const)) ∈
      witnessLimit (paramImage (insert excludedMiddle T)) enum :=
    subset_witnessLimit _ enum ⟨excludedMiddle, Set.mem_insert _ _, rfl⟩
  obtain ⟨N, hN, _, hExt⟩ := henkin_extensional_model_exists enum henum
    (consistent_union_emSchema hLem hWitness)
  refine ⟨HenkinModel.constantSubstitutionReduct (fun {_} c => .const (inj c)) N,
    (HenkinModel.constantSubstitutionReduct_functionsRespectEqv_iff _ N).mpr hExt, ?_⟩
  intro ψ hψ
  rw [← HenkinModel.models_substConst, substConst_constant_images]
  exact hN _ ⟨ψ, Set.mem_insert_of_mem _ hψ, rfl⟩

/-- A theory that does not prove `φ` together with excluded middle is still
consistent after adding `¬ φ`. -/
theorem consistent_insert_not {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (h : ¬ Provable (Const := Const) (insert excludedMiddle T) φ) :
    Consistent (Const := Const) (insert excludedMiddle (insert (.not φ) T)) := by
  intro hBot
  apply h
  have hSwap : insert excludedMiddle (insert (.not φ) T) =
      insert (.not φ) (insert excludedMiddle T) := Set.insert_comm _ _ _
  rw [hSwap] at hBot
  have hNotNot : Provable (Const := Const) (insert excludedMiddle T) (.not (.not φ)) :=
    provable_not_of_imp_bot (provable_imp_of_insert hBot)
  have hEM : Provable (Const := Const) (insert excludedMiddle T) (.or φ (.not φ)) := by
    refine ⟨[excludedMiddle], ?_, ?_⟩
    · intro ξ hξ
      simp only [List.mem_singleton] at hξ
      subst hξ
      exact Set.mem_insert _ _
    · exact extDerivation_em_of_lem (.hyp (by simp [excludedMiddle])) φ
  rcases hEM with ⟨Γ₁, hΓ₁, d₁⟩
  rcases hNotNot with ⟨Γ₂, hΓ₂, d₂⟩
  refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
  · intro ξ hξ
    rcases List.mem_append.mp hξ with hξ | hξ
    · exact hΓ₁ ξ hξ
    · exact hΓ₂ ξ hξ
  · refine .orE (ExtDerivation.mono (fun hξ => List.mem_append_left _ hξ) d₁)
      (.hyp (by simp)) ?_
    refine .botE (.notE (ExtDerivation.mono ?_ d₂) (.hyp (by simp)))
    intro ξ hξ
    exact List.mem_cons_of_mem _ (List.mem_append_right _ hξ)

/-- **Completeness.** A sentence true in every extensional Henkin model of the
theory is provable from the theory together with excluded middle. -/
theorem completeness [Countable Base] [∀ τ, Countable (Const τ)]
    (inh : ∀ b : Base, ClosedTerm Const (.base b))
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (hValid : ∀ M : HenkinModel.{u, v, v} Base Const, M.FunctionsRespectEqv →
      (∀ ψ ∈ T, M.models ψ) → M.models φ) :
    Provable (Const := Const) (insert excludedMiddle T) φ := by
  by_contra hNot
  obtain ⟨M, hExt, hM⟩ := exists_model_of_consistent inh (consistent_insert_not hNot)
  have hNotφ : M.models (.not φ) := hM _ (Set.mem_insert _ _)
  exact (HenkinModel.models_not M).mp hNotφ
    (hValid M hExt (fun ψ hψ => hM ψ (Set.mem_insert_of_mem _ hψ)))

/-- **Soundness and completeness for general models** (Henkin 1950; Andrews'
`Q0`, Farmer's Theorems 8 and 11). -/
theorem provable_iff_valid [Countable Base] [∀ τ, Countable (Const τ)]
    (inh : ∀ b : Base, ClosedTerm Const (.base b))
    (T : ClosedTheorySet Const) (φ : ClosedFormula Const) :
    Provable (Const := Const) (insert excludedMiddle T) φ ↔
      ∀ M : HenkinModel.{u, v, v} Base Const, M.FunctionsRespectEqv →
        (∀ ψ ∈ T, M.models ψ) → M.models φ :=
  ⟨fun h M hExt hT => soundness h M hExt hT, completeness inh⟩

/-- Consistency is satisfiability in an extensional Henkin model. -/
theorem consistent_iff_satisfiable [Countable Base] [∀ τ, Countable (Const τ)]
    (inh : ∀ b : Base, ClosedTerm Const (.base b)) (T : ClosedTheorySet Const) :
    Consistent (Const := Const) (insert excludedMiddle T) ↔
      ∃ M : HenkinModel.{u, v, v} Base Const, M.FunctionsRespectEqv ∧ ∀ ψ ∈ T, M.models ψ := by
  constructor
  · exact exists_model_of_consistent inh
  · rintro ⟨M, hExt, hM⟩ hBot
    exact HenkinModel.models_bot M (soundness hBot M hExt hM)

/-! ## Negative control: parameter-freeness excludes containing the schema -/

/-- No theory over the parameter signature is both parameter-free and contains
`EMSchema`: the schema contains `p ∨ ¬ p` for the parameter `p` at `prop`.
A parameter-free classical theory proves the schema instead of containing it. -/
theorem classical_corollary_hypotheses_unsatisfiable :
    ¬ ∃ T : ClosedTheorySet (WithParams Const),
      (∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ) ∧
        (∀ ψ ∈ EMSchema Const, ψ ∈ T) := by
  rintro ⟨T, hFree, hEM⟩
  have hMem : (.or (.const (param .prop 0)) (.not (.const (param .prop 0))) :
      ClosedFormula (WithParams Const)) ∈ T :=
    hEM _ (emClosed_mem (.const (param .prop 0)))
  have hOcc := hFree _ hMem .prop 0
  cases hOcc with
  | or hp _ =>
      cases hp with
      | const_diff_type hne => exact hne rfl
      | const_same_ne _ hne => exact hne rfl

/-! ## Negative example: parameters force inhabited types -/

namespace EmptyBase

/-- One base type and no constants. -/
abbrev NoConstants : Ty Unit → Type := fun _ => Empty

/-- `ι` is empty. -/
def emptiness : ClosedFormula NoConstants :=
  .not (.ex (.top : Formula NoConstants [.base ()]))

/-- The standard model with an empty base carrier. -/
def emptyModel : HenkinModel.{0, 0, 0} Unit NoConstants :=
  HenkinModel.standard (fun _ => ULift.{1, 0} Empty) (fun {_} c => nomatch c)

theorem emptyModel_models : emptyModel.models emptiness := by
  rintro ⟨x, _, _⟩
  exact nomatch x.down

theorem emptyModel_extensional : emptyModel.FunctionsRespectEqv :=
  HenkinModel.functionsRespectEqv_of_fullDomains _ (HenkinModel.fullDomains_standard _ _)

/-- Over the original signature, "`ι` is empty" is consistent with excluded
middle: the empty model satisfies both. -/
theorem consistent : Consistent (Const := NoConstants)
    (insert excludedMiddle {emptiness}) := by
  intro hBot
  exact HenkinModel.models_bot emptyModel
    (soundness hBot emptyModel emptyModel_extensional (by
      intro ψ hψ
      rw [Set.mem_singleton_iff] at hψ
      subst hψ
      exact emptyModel_models))

/-- Over the parameter signature, the same theory is inconsistent: a parameter
of type `ι` is a closed inhabitant. -/
theorem image_inconsistent :
    ¬ Consistent (Const := WithParams NoConstants) (paramImage {emptiness}) := by
  intro hCons
  apply hCons
  refine ⟨[mapConst (fun {_} c => inj c) emptiness], ?_, ?_⟩
  · intro ψ hψ
    simp only [List.mem_singleton] at hψ
    subst hψ
    exact ⟨emptiness, rfl, rfl⟩
  · refine .notE (φ := .ex (.top : Formula (WithParams NoConstants) [.base ()]))
      (.hyp (List.mem_singleton.mpr rfl)) ?_
    exact .exI (.const (param (.base ()) 0)) .topI

end EmptyBase

/-! ## Negative example: excluded middle is needed -/

open PropositionalSlice in
/-- **The calculus without excluded middle is incomplete.** Over one
propositional constant `p`, the sentence `p ∨ ¬ p` holds in every Henkin model
and is not derivable from no hypotheses. -/
theorem incomplete_without_excludedMiddle :
    (∀ M : HenkinModel.{0, 0, 0} AtomBase Atom,
      M.models (embed (.atom 0 ⋎ ∼(.atom 0)))) ∧
    ¬ Provable (Const := Atom) ∅ (embed (.atom 0 ⋎ ∼(.atom 0))) := by
  refine ⟨fun M => ?_, excludedMiddle_not_provable⟩
  classical
  exact Classical.em _

#print axioms incomplete_without_excludedMiddle
#print axioms soundness
#print axioms exists_model_of_consistent
#print axioms provable_iff_valid
#print axioms consistent_iff_satisfiable
#print axioms classical_corollary_hypotheses_unsatisfiable
#print axioms EmptyBase.consistent
#print axioms EmptyBase.image_inconsistent

end SevenVirtues

end Mettapedia.Logic.HOL
