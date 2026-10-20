import Mettapedia.Logic.HOL.ProofSyntax

/-!
# Structural transport of retained HOL derivations

Assumption transport uses explicit occurrence maps, not a choice of a member
of the target assumption list. Renaming traverses every rule of the retained
calculus, including the lifted environments under object binders. Neither
operation reconstructs a proof from proposition-valued derivability.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ProofSyntax

universe u v w

/-- Explicit transport of each assumption occurrence. Repeated formulas do
not choose their target occurrence implicitly. Injectivity is not required. -/
structure OccurrenceMap {α : Type u} (source target : List α) where
  index : Fin source.length → Fin target.length
  get_eq : ∀ i, target.get (index i) = source.get i

namespace OccurrenceMap

variable {α : Type u} {β : Type v} {source target : List α}

def prepend (head : α) : OccurrenceMap source (head :: source) where
  index := Fin.succ
  get_eq _ := rfl

def lift (transport : OccurrenceMap source target) (head : α) :
    OccurrenceMap (head :: source) (head :: target) where
  index := Fin.cases 0 (fun i => (transport.index i).succ)
  get_eq i := by
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · exact transport.get_eq i

def map (transport : OccurrenceMap source target) (f : α → β) :
    OccurrenceMap (source.map f) (target.map f) where
  index i := (transport.index (i.cast (by simp))).cast (by simp)
  get_eq i := by
    simpa using congrArg f (transport.get_eq (i.cast (by simp)))

end OccurrenceMap

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}

/-- Rule-by-rule assumption transport. Only hypothesis occurrences change;
every other rule and all of its ordered subproofs are retained. -/
def mono {Γ : Ctx Base} {Δ Δ' : List (Formula Const Γ)} {φ : Formula Const Γ}
    (transport : OccurrenceMap Δ Δ') (proof : ProofSyntax Const Δ φ) :
    ProofSyntax Const Δ' φ :=
  match proof with
  | .hyp occurrence => (transport.get_eq occurrence) ▸ .hyp (transport.index occurrence)
  | .topI => .topI
  | .botE proof => .botE (mono transport proof)
  | .andI left right => .andI (mono transport left) (mono transport right)
  | .andEL proof => .andEL (mono transport proof)
  | .andER proof => .andER (mono transport proof)
  | .orIL proof => .orIL (mono transport proof)
  | .orIR proof => .orIR (mono transport proof)
  | .orE cases left right =>
      .orE (mono transport cases) (mono (transport.lift _) left) (mono (transport.lift _) right)
  | .impI proof => .impI (mono (transport.lift _) proof)
  | .impE function argument => .impE (mono transport function) (mono transport argument)
  | .notI proof => .notI (mono (transport.lift _) proof)
  | .notE negative positive => .notE (mono transport negative) (mono transport positive)
  | .allI proof => .allI (mono (transport.map (weaken (σ := _))) proof)
  | .allE term proof => .allE term (mono transport proof)
  | .exI term proof => .exI term (mono transport proof)
  | .exE existsProof body =>
      .exE (mono transport existsProof) (mono ((transport.map (weaken (σ := _))).lift _) body)
  | .eqRefl term => .eqRefl term
  | .eqSymm proof => .eqSymm (mono transport proof)
  | .eqTrans left right => .eqTrans (mono transport left) (mono transport right)
  | .eqPropI forward backward => .eqPropI (mono transport forward) (mono transport backward)
  | .eqPropEL proof => .eqPropEL (mono transport proof)
  | .eqPropER proof => .eqPropER (mono transport proof)
  | .eqApp term proof => .eqApp term (mono transport proof)
  | .eqAppArg function proof => .eqAppArg function (mono transport proof)
  | .eqLam proof => .eqLam (mono (transport.map (weaken (σ := _))) proof)
  | .funExt proof => .funExt (mono transport proof)
  | .beta term body => .beta term body
  | .eta function => .eta function

def prepend (head : Formula Const Γ) (proof : ProofSyntax Const Δ φ) :
    ProofSyntax Const (head :: Δ) φ := mono (OccurrenceMap.prepend head) proof

/-- Change only equal sequent indices of a retained proof. -/
def castIndices {Δ' : List (Formula Const Γ)} {ψ : Formula Const Γ}
    (assumptions : Δ = Δ') (conclusion : φ = ψ)
    (proof : ProofSyntax Const Δ φ) : ProofSyntax Const Δ' ψ :=
  assumptions ▸ conclusion ▸ proof

/-- Capture-safe term-variable renaming over the entire retained calculus. -/
def rename {Γ Γ' : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (ρ : Rename Base Γ Γ') (proof : ProofSyntax Const Δ φ) :
    ProofSyntax Const (Δ.map (HOL.rename ρ)) (HOL.rename ρ φ) :=
  match proof with
  | .hyp occurrence => by
      exact castIndices rfl (by simp)
        (ProofSyntax.hyp (Const := Const) (Δ := Δ.map (HOL.rename ρ))
          (occurrence.cast (by simp)))
  | .topI => .topI
  | .botE proof => .botE (rename ρ proof)
  | .andI left right => .andI (rename ρ left) (rename ρ right)
  | .andEL proof => .andEL (rename ρ proof)
  | .andER proof => .andER (rename ρ proof)
  | .orIL proof => .orIL (rename ρ proof)
  | .orIR proof => .orIR (rename ρ proof)
  | .orE cases left right => .orE (rename ρ cases) (rename ρ left) (rename ρ right)
  | .impI proof => .impI (rename ρ proof)
  | .impE function argument => .impE (rename ρ function) (rename ρ argument)
  | .notI proof => .notI (rename ρ proof)
  | .notE negative positive => .notE (rename ρ negative) (rename ρ positive)
  | .allI proof => .allI (castIndices
      (ExtDerivation.rename_weakenHyps ρ _).symm rfl (rename (Rename.lift ρ) proof))
  | .allE term proof => by
      exact castIndices rfl (ExtDerivation.rename_instantiate ρ term _).symm
        (ProofSyntax.allE (HOL.rename ρ term) (rename ρ proof))
  | .exI term proof => .exI (HOL.rename ρ term)
      (castIndices rfl (ExtDerivation.rename_instantiate ρ term _) (rename ρ proof))
  | .exE existsProof body => .exE (rename ρ existsProof)
      (castIndices (by simp [List.map, ExtDerivation.rename_weakenHyps])
        (ExtDerivation.rename_weaken ρ _) (rename (Rename.lift ρ) body))
  | .eqRefl term => .eqRefl (HOL.rename ρ term)
  | .eqSymm proof => .eqSymm (rename ρ proof)
  | .eqTrans left right => .eqTrans (rename ρ left) (rename ρ right)
  | .eqPropI forward backward => .eqPropI (rename ρ forward) (rename ρ backward)
  | .eqPropEL proof => .eqPropEL (rename ρ proof)
  | .eqPropER proof => .eqPropER (rename ρ proof)
  | .eqApp term proof => .eqApp (HOL.rename ρ term) (rename ρ proof)
  | .eqAppArg function proof => .eqAppArg (HOL.rename ρ function) (rename ρ proof)
  | .eqLam proof => .eqLam (castIndices
      (ExtDerivation.rename_weakenHyps ρ _).symm rfl (rename (Rename.lift ρ) proof))
  | .funExt proof => .funExt (castIndices rfl
      (by simp [HOL.rename, Rename.lift, ExtDerivation.rename_weaken]) (rename ρ proof))
  | .beta term body => by
      exact castIndices rfl
        (by simp [HOL.rename, ExtDerivation.rename_instantiate])
        (ProofSyntax.beta (Δ := Δ.map (HOL.rename ρ)) (HOL.rename ρ term)
          (HOL.rename (Rename.lift ρ) body))
  | .eta function => by
      exact castIndices rfl (by simp [HOL.rename, Rename.lift, ExtDerivation.rename_weaken])
        (ProofSyntax.eta (Δ := Δ.map (HOL.rename ρ)) (HOL.rename ρ function))

theorem mono_erasure {Δ' : List (Formula Const Γ)}
    (transport : OccurrenceMap Δ Δ') (proof : ProofSyntax Const Δ φ) :
    ExtDerivation Const Δ' φ := (mono transport proof).erase

theorem rename_erasure {Γ' : Ctx Base} (ρ : Rename Base Γ Γ')
    (proof : ProofSyntax Const Δ φ) :
    ExtDerivation Const (Δ.map (HOL.rename ρ)) (HOL.rename ρ φ) :=
  (rename ρ proof).erase

@[simp] theorem nodeCount_cast_conclusion {ψ : Formula Const Γ}
    (equal : φ = ψ) (proof : ProofSyntax Const Δ φ) :
    (equal ▸ proof : ProofSyntax Const Δ ψ).nodeCount = proof.nodeCount := by
  cases equal
  rfl

@[simp] theorem nodeCount_castIndices {Δ' : List (Formula Const Γ)} {ψ : Formula Const Γ}
    (assumptions : Δ = Δ') (conclusion : φ = ψ)
    (proof : ProofSyntax Const Δ φ) :
    (castIndices assumptions conclusion proof).nodeCount = proof.nodeCount := by
  cases assumptions
  cases conclusion
  rfl

@[simp] theorem rootObservation_castIndices {Δ' : List (Formula Const Γ)} {ψ : Formula Const Γ}
    (assumptions : Δ = Δ') (conclusion : φ = ψ)
    (proof : ProofSyntax Const Δ φ) :
    (castIndices assumptions conclusion proof).rootObservation = proof.rootObservation := by
  cases assumptions
  cases conclusion
  rfl

/-- Explicit occurrence transport preserves the number of rule nodes through
all rules, including the changed assumption lists under object binders. -/
theorem mono_nodeCount {Δ' : List (Formula Const Γ)}
    (transport : OccurrenceMap Δ Δ') (proof : ProofSyntax Const Δ φ) :
    (mono transport proof).nodeCount = proof.nodeCount := by
  induction proof with
  | hyp occurrence =>
      simp only [mono, nodeCount_cast_conclusion]
      rfl
  | _ =>
      simp only [mono]
      change 1 + _ = 1 + _
      simp_all [nodeCount, weakenHyps]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Renaming traverses the proof without adding or removing rule nodes. -/
theorem rename_nodeCount {Ξ : Ctx Base} (ρ : Rename Base Γ Ξ)
    (proof : ProofSyntax Const Δ φ) : (rename ρ proof).nodeCount = proof.nodeCount := by
  have count_cast {Γ : Ctx Base} {Δ Δ' : List (Formula Const Γ)}
      {φ ψ : Formula Const Γ} (assumptions : Δ = Δ') (conclusion : φ = ψ)
      (proof : ProofSyntax Const Δ φ) :
      (castIndices assumptions conclusion proof).observe.nodeCount = proof.observe.nodeCount :=
    nodeCount_castIndices assumptions conclusion proof
  induction proof generalizing Ξ with
  | hyp occurrence => simp only [rename, nodeCount_castIndices]; rfl
  | _ =>
      simp only [rename, nodeCount_castIndices]
      change 1 + _ = 1 + _
      simp_all [nodeCount, weakenHyps]

/-! ## Simultaneous substitution of object terms -/

/-- Substitution commutes with instantiating a bound object variable. -/
theorem subst_instantiate {Γ Γ' : Ctx Base} {A B : Ty Base}
    (θ : Subst Const Γ Γ') (term : Term Const Γ A)
    (body : Term Const (A :: Γ) B) :
    HOL.subst θ (instantiate term body) =
      instantiate (HOL.subst θ term) (HOL.subst (Subst.lift θ) body) := by
  unfold instantiate
  rw [HOL.subst_comp, HOL.subst_comp]
  apply HOL.subst_ext
  intro T index
  cases index with
  | vz => rfl
  | vs index =>
      exact (instantiate_weaken (HOL.subst θ term) (θ index)).symm

theorem subst_weakenHyps {Γ Γ' : Ctx Base} {A : Ty Base}
    (θ : Subst Const Γ Γ') (hypotheses : List (Formula Const Γ)) :
    (weakenHyps (σ := A) hypotheses).map (HOL.subst (Subst.lift θ)) =
      weakenHyps (σ := A) (hypotheses.map (HOL.subst θ)) := by
  simp [weakenHyps, List.map_map, Function.comp_def]

/-- Capture-safe simultaneous substitution traverses all retained proof
constructors. It substitutes terms, not propositions standing in for proofs. -/
def subst {Γ Γ' : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (θ : Subst Const Γ Γ') (proof : ProofSyntax Const Δ φ) :
    ProofSyntax Const (Δ.map (HOL.subst θ)) (HOL.subst θ φ) :=
  match proof with
  | .hyp occurrence => by
      simpa using (ProofSyntax.hyp (Const := Const) (Δ := Δ.map (HOL.subst θ))
        (occurrence.cast (by simp)))
  | .topI => .topI
  | .botE proof => .botE (subst θ proof)
  | .andI left right => .andI (subst θ left) (subst θ right)
  | .andEL proof => .andEL (subst θ proof)
  | .andER proof => .andER (subst θ proof)
  | .orIL proof => .orIL (subst θ proof)
  | .orIR proof => .orIR (subst θ proof)
  | .orE cases left right => .orE (subst θ cases) (subst θ left) (subst θ right)
  | .impI proof => .impI (subst θ proof)
  | .impE function argument => .impE (subst θ function) (subst θ argument)
  | .notI proof => .notI (subst θ proof)
  | .notE negative positive => .notE (subst θ negative) (subst θ positive)
  | .allI proof => .allI (by
      simpa [subst_weakenHyps] using subst (Subst.lift θ) proof)
  | .allE term proof => by
      simpa [subst_instantiate] using
        ProofSyntax.allE (HOL.subst θ term) (subst θ proof)
  | .exI term proof => .exI (HOL.subst θ term) (by
      simpa [subst_instantiate] using subst θ proof)
  | .exE existsProof body => .exE (subst θ existsProof) (by
      simpa [List.map, subst_weakenHyps] using subst (Subst.lift θ) body)
  | .eqRefl term => .eqRefl (HOL.subst θ term)
  | .eqSymm proof => .eqSymm (subst θ proof)
  | .eqTrans left right => .eqTrans (subst θ left) (subst θ right)
  | .eqPropI forward backward => .eqPropI (subst θ forward) (subst θ backward)
  | .eqPropEL proof => .eqPropEL (subst θ proof)
  | .eqPropER proof => .eqPropER (subst θ proof)
  | .eqApp term proof => .eqApp (HOL.subst θ term) (subst θ proof)
  | .eqAppArg function proof => .eqAppArg (HOL.subst θ function) (subst θ proof)
  | .eqLam proof => .eqLam (by
      simpa [HOL.subst, subst_weakenHyps] using subst (Subst.lift θ) proof)
  | .funExt proof => .funExt (by
      simpa [HOL.subst, Subst.lift] using subst θ proof)
  | .beta term body => by
      simpa [HOL.subst, Subst.lift, subst_instantiate] using
        ProofSyntax.beta (Δ := Δ.map (HOL.subst θ)) (HOL.subst θ term)
          (HOL.subst (Subst.lift θ) body)
  | .eta function => by
      simpa [HOL.subst, Subst.lift] using
        ProofSyntax.eta (Δ := Δ.map (HOL.subst θ)) (HOL.subst θ function)

theorem subst_erasure {Γ' : Ctx Base} (θ : Subst Const Γ Γ')
    (proof : ProofSyntax Const Δ φ) :
    ExtDerivation Const (Δ.map (HOL.subst θ)) (HOL.subst θ φ) :=
  (subst θ proof).erase

/-! ## Functoriality of proof substitution

Substitution acts on retained proofs exactly as it acts on terms: the identity
substitution fixes every proof, and substituting along a composite is
substituting twice. The proof indices change only propositionally, so both laws
are heterogeneous equalities of proof trees. Every rule, every hypothesis
occurrence and every retained term argument is compared; no proof is replaced by
mere derivability. -/

section Functoriality

theorem mpr_heq {α β : Sort w} (same : α = β) (value : β) : HEq (same.mpr value) value := by
  subst same
  rfl

theorem mp_heq {α β : Sort w} (same : α = β) (value : α) : HEq (same.mp value) value := by
  subst same
  rfl

theorem id_mp_heq {α β : Sort w} (same : α = β) (value : α) :
    HEq (id (same.mp value)) value := by
  subst same
  rfl

theorem fin_cast_heq {m n : Nat} (same : m = n) (index : Fin m) :
    HEq (Fin.cast same index) index := by
  subst same
  rfl

/-- A substitution which sends every variable to itself fixes every term. -/
theorem term_subst_of_identity {Γ : Ctx Base} {θ : Subst Const Γ Γ}
    (identity : ∀ {τ : Ty Base} (index : Var Γ τ), θ index = .var index)
    {τ : Ty Base} (term : Term Const Γ τ) : HOL.subst θ term = term := by
  rw [subst_ext (σs := θ) (τs := Subst.id) (fun index => identity index) term, subst_id]

theorem terms_subst_of_identity {Γ : Ctx Base} {θ : Subst Const Γ Γ}
    (identity : ∀ {τ : Ty Base} (index : Var Γ τ), θ index = .var index)
    {τ : Ty Base} (terms : List (Term Const Γ τ)) : terms.map (HOL.subst θ) = terms :=
  (List.map_congr_left (fun term _ => term_subst_of_identity identity term)).trans
    (List.map_id _)

theorem lift_of_identity {Γ : Ctx Base} {σ : Ty Base} {θ : Subst Const Γ Γ}
    (identity : ∀ {τ : Ty Base} (index : Var Γ τ), θ index = .var index) :
    ∀ {τ : Ty Base} (index : Var (σ :: Γ) τ), Subst.lift (σ := σ) θ index = .var index := by
  intro τ index
  cases index with
  | vz => rfl
  | vs index =>
      simp only [Subst.lift, identity index]
      rfl

theorem lift_of_composite {Γ Γ' Γ'' : Ctx Base} {σ : Ty Base}
    {θ : Subst Const Γ Γ''} {f : Subst Const Γ' Γ''} {g : Subst Const Γ Γ'}
    (composite : ∀ {τ : Ty Base} (index : Var Γ τ), θ index = HOL.subst f (g index)) :
    ∀ {τ : Ty Base} (index : Var (σ :: Γ) τ),
      Subst.lift (σ := σ) θ index = HOL.subst (Subst.lift f) (Subst.lift g index) := by
  intro τ index
  rw [show Subst.lift (σ := σ) θ index = Subst.lift (σ := σ) (Subst.comp f g) index by
    cases index with
    | vz => rfl
    | vs index => simp [Subst.lift, composite index]]
  exact Subst.lift_comp_apply f g index

theorem term_subst_of_composite {Γ Γ' Γ'' : Ctx Base}
    {θ : Subst Const Γ Γ''} {f : Subst Const Γ' Γ''} {g : Subst Const Γ Γ'}
    (composite : ∀ {τ : Ty Base} (index : Var Γ τ), θ index = HOL.subst f (g index))
    {τ : Ty Base} (term : Term Const Γ τ) :
    HOL.subst θ term = HOL.subst f (HOL.subst g term) := by
  rw [subst_comp, subst_ext (σs := θ) (τs := Subst.comp f g) (fun index => composite index)]

theorem terms_subst_of_composite {Γ Γ' Γ'' : Ctx Base}
    {θ : Subst Const Γ Γ''} {f : Subst Const Γ' Γ''} {g : Subst Const Γ Γ'}
    (composite : ∀ {τ : Ty Base} (index : Var Γ τ), θ index = HOL.subst f (g index))
    {τ : Ty Base} (terms : List (Term Const Γ τ)) :
    terms.map (HOL.subst θ) = (terms.map (HOL.subst g)).map (HOL.subst f) := by
  rw [List.map_map]
  exact List.map_congr_left (fun term _ => term_subst_of_composite composite term)

/-- Substitution respects heterogeneous equality of proofs with equal indices. -/
theorem subst_heq_of_heq {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ')
    {Δ₁ Δ₂ : List (Formula Const Γ)} {φ₁ φ₂ : Formula Const Γ}
    (hypotheses : Δ₁ = Δ₂) (conclusion : φ₁ = φ₂)
    {first : ProofSyntax Const Δ₁ φ₁} {second : ProofSyntax Const Δ₂ φ₂}
    (same : HEq first second) : HEq (subst θ first) (subst θ second) := by
  subst hypotheses conclusion
  cases same
  rfl

/-- **Identity law.** A pointwise identity substitution fixes every retained
proof, including its hypothesis occurrences and binder bodies. -/
theorem subst_heq_self {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) (θ : Subst Const Γ Γ)
    (identity : ∀ {τ : Ty Base} (index : Var Γ τ), θ index = .var index) :
    HEq (subst θ proof) proof := by
  induction proof with
  | _ =>
      simp only [subst]
      try refine (mpr_heq _ _).trans ?_
      try refine (mp_heq _ _).trans ?_
      congr 1
      all_goals first
        | exact term_subst_of_identity identity _
        | exact term_subst_of_identity (lift_of_identity identity) _
        | exact terms_subst_of_identity identity _
        | exact terms_subst_of_identity (lift_of_identity identity) _
        | exact fin_cast_heq _ _
        | solve_by_elim (maxDepth := 4) [lift_of_identity]
        | (refine (id_mp_heq _ _).trans ?_
           solve_by_elim (maxDepth := 4) [lift_of_identity])

theorem subst_id_heq {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) :
    HEq (subst (Subst.id (Base := Base) (Const := Const) (Γ := Γ)) proof) proof :=
  subst_heq_self proof _ (fun _ => rfl)

set_option linter.unusedSimpArgs false in
/-- **Composition law.** Substituting along a pointwise composite is
substituting twice, rule by rule. -/
theorem subst_subst_heq {Γ Γ' Γ'' : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (proof : ProofSyntax Const Δ φ) (θ : Subst Const Γ Γ'')
    (f : Subst Const Γ' Γ'') (g : Subst Const Γ Γ')
    (composite : ∀ {τ : Ty Base} (index : Var Γ τ), θ index = HOL.subst f (g index)) :
    HEq (subst θ proof) (subst f (subst g proof)) := by
  induction proof generalizing Γ' Γ'' with
  | _ =>
      simp only [subst]
      try refine (mpr_heq _ _).trans ?_
      try refine (mp_heq _ _).trans ?_
      try refine HEq.trans ?_ (subst_heq_of_heq f ?_ ?_ (mpr_heq _ _)).symm
      try refine HEq.trans ?_ (subst_heq_of_heq f ?_ ?_ (mp_heq _ _)).symm
      all_goals try (first
        | rfl
        | (simp [subst_instantiate, subst_weakenHyps, HOL.subst, Subst.lift]; done))
      all_goals try simp only [subst]
      all_goals try refine HEq.trans ?_ (mpr_heq _ _).symm
      all_goals try refine HEq.trans ?_ (mp_heq _ _).symm
      all_goals try congr 1
      all_goals first
        | exact term_subst_of_composite composite _
        | exact term_subst_of_composite (lift_of_composite composite) _
        | exact terms_subst_of_composite composite _
        | exact terms_subst_of_composite (lift_of_composite composite) _
        | exact (fin_cast_heq _ _).trans ((fin_cast_heq _ _).trans (fin_cast_heq _ _)).symm
        | solve_by_elim (maxDepth := 6) [lift_of_composite]
        | (refine (id_mp_heq _ _).trans ?_
           refine HEq.trans ?_ (id_mp_heq _ _).symm
           refine HEq.trans ?_ (subst_heq_of_heq _ ?_ ?_ (id_mp_heq _ _)).symm
           · solve_by_elim (maxDepth := 6) [lift_of_composite]
           all_goals simp [subst_instantiate, subst_weakenHyps, HOL.subst, Subst.lift])

theorem subst_comp_heq {Γ Γ' Γ'' : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (proof : ProofSyntax Const Δ φ)
    (f : Subst Const Γ' Γ'') (g : Subst Const Γ Γ') :
    HEq (subst (Subst.comp f g) proof) (subst f (subst g proof)) :=
  subst_subst_heq proof _ f g (fun _ => rfl)

end Functoriality

/-! ## The root rule survives substitution -/

theorem rootObservation_of_heq {Γ : Ctx Base} {Δ₁ Δ₂ : List (Formula Const Γ)}
    {φ₁ φ₂ : Formula Const Γ} (hypotheses : Δ₁ = Δ₂) (conclusion : φ₁ = φ₂)
    {first : ProofSyntax Const Δ₁ φ₁} {second : ProofSyntax Const Δ₂ φ₂}
    (same : HEq first second) : first.rootObservation = second.rootObservation := by
  subst hypotheses conclusion
  cases same
  rfl

set_option linter.unusedSimpArgs false in
/-- Substitution keeps the root rule and its hypothesis position. -/
theorem rootObservation_subst {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ')
    {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} (proof : ProofSyntax Const Δ φ) :
    (subst θ proof).rootObservation = proof.rootObservation := by
  cases proof <;> dsimp only [subst]
  all_goals try (refine (rootObservation_of_heq ?_ ?_ (mpr_heq _ _)).trans ?_; rotate_left 2)
  all_goals try (refine (rootObservation_of_heq ?_ ?_ (mp_heq _ _)).trans ?_; rotate_left 2)
  all_goals first
    | rfl
    | simp [subst_instantiate, subst_weakenHyps, HOL.subst, Subst.lift]

end Mettapedia.Logic.HOL.ProofSyntax
