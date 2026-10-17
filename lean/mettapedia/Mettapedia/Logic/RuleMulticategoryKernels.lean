import Mettapedia.Logic.RuleMulticategoryGraphs
import Mettapedia.Logic.DerivationGraph.TheoryRevalidation
import Mettapedia.Logic.PropositionalExtension
import Mettapedia.Logic.IntuitionisticDecision
import Mettapedia.Logic.ProofSharingBounds
import Mathlib.Tactic.FinCases

/-!
# Translations between native propositional kernels as multifunctors

The intuitionistic and classical Hilbert kernels and the extended kernel with
fresh definitions are each presented by a rule-instance interface, hence by a
free cartesian multicategory. Their inclusions are renamings of rule
instances, so they induce multifunctors.

* **Intuitionistic into classical** (`Hilbert.inclusion_faithful`,
  `Hilbert.inclusion_not_reflecting`): faithful and derivability preserving, but
  not derivability reflecting; excluded middle is the witness.
* **Substitution** (`Hilbert.substFunctor`, `Hilbert.source_subst`,
  `Hilbert.substFunctor_comp_heq`): each substitution of formulas for atoms acts
  on the free Hilbert multicategory by a multifunctor, coherently with composition
  of substitutions, so derivability is closed under substitution as a consequence
  of freeness.
* **Classical into extended** (`Extension.inclusion_faithful`,
  `Extension.inclusion_conservative`, `Extension.inclusion_not_full`): faithful,
  and conservative for admitted fresh definitions over claims in the old
  vocabulary, but not full on proofs: a derivation citing a definition is not the
  image of any classical derivation. This is EXTEND: the multicategory changes,
  and literal expansion can be exponential (`PropositionalExtension.literal_expansion_gap`).
* **Contraction in a rule image** (`Contraction.image_size`): translating the
  chain calculus into the duplication calculus of `ProofSharingBounds` by a rule
  image that cites its one premise twice sends a derivation with `k + 1` nodes
  to a tree with `2 ^ (k + 1) - 1` nodes. The same derivations have shared
  graphs with `k + 1` rows (`ProofSharingBounds.dag_checked`). This is SHARE: the
  multicategory is unchanged and only the representation size differs. Affine
  rule images cannot do this (`RuleSignature.lift_size_le`).
* **Admission and revalidation** (`Revalidation`): retained graph evidence moves
  from the intuitionistic to the classical profile and from admitted definitions
  to admitted extensions of them; classical evidence citing excluded middle, and
  evidence citing a changed definition, are refused on revalidation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic

open RuleSignature CartesianMulticategory

namespace Hilbert

open PropositionalHilbertChecking

/-- An intuitionistic rule instance is a classical rule instance. -/
theorem checkRule_classical {code : Code} {premises : List Formula} {conclusion : Formula}
    (accepted : checkRule .intuitionistic code premises conclusion = true) :
    checkRule .classical code premises conclusion = true := by
  cases code <;> simp_all [checkRule, Code.allowed]

/-- The inclusion of rule instances. -/
def toClassical : ∀ premises conclusion,
    (interface .intuitionistic).signature premises conclusion →
      (interface .classical).signature premises conclusion :=
  fun _ _ rule => ⟨rule.1, checkRule_classical rule.2⟩

theorem toClassical_injective (premises : List Formula) (conclusion : Formula) :
    Function.Injective (toClassical premises conclusion) := by
  intro first second same
  have values := congrArg Subtype.val same
  exact Subtype.ext values

/-- The inclusion multifunctor. -/
def inclusion : (free (interface .intuitionistic).signature).Functor
    (free (interface .classical).signature) _root_.id :=
  liftFunctor (rename toClassical)

/-- **Faithful**: distinct intuitionistic derivations remain distinct. -/
theorem inclusion_faithful {n : ℕ} {Γ : Fin n → Formula} {b : Formula}
    {t t' : Term (interface .intuitionistic).signature Γ b}
    (same : inclusion.map t = inclusion.map t') : t = t' :=
  lift_rename_injective toClassical toClassical_injective same

theorem derivable_iff_source (profile : Profile) (formula : Formula) :
    Derivable (interface profile).signature formula ↔ Source profile formula :=
  (RuleWitness.derivable_iff_derives (interface profile) formula).trans
    (source_iff_derives profile formula).symm

/-- **Not reflecting**: excluded middle is classically derivable and not
intuitionistically derivable. -/
theorem inclusion_not_reflecting :
    Derivable (interface .classical).signature Controls.em ∧
      ¬ Derivable (interface .intuitionistic).signature Controls.em := by
  constructor
  · apply (RuleWitness.derivable_iff_derives (interface .classical) _).mpr
    have accepted := Controls.classical_em_accepted
    simp only [checker, Bool.and_eq_true, decide_eq_true_eq] at accepted
    exact accepted.1 ▸ Derivation.valid_sound (interface .classical) _ accepted.2
  · intro derivable
    exact IntuitionisticDecision.Controls.excluded_middle_unprovable
      ((derivable_iff_source .intuitionistic _).mp derivable)

/-! ### Substitution acts on the Hilbert multicategories -/

/-- Substitute into the formulas of a rule code. -/
def substCode (σ : LO.Propositional.Substitution Nat) : Code → Code
  | .truth => .truth
  | .k a b => .k (a.subst σ) (b.subst σ)
  | .s a b c => .s (a.subst σ) (b.subst σ) (c.subst σ)
  | .andLeft a b => .andLeft (a.subst σ) (b.subst σ)
  | .andRight a b => .andRight (a.subst σ) (b.subst σ)
  | .andIntro a b => .andIntro (a.subst σ) (b.subst σ)
  | .orLeft a b => .orLeft (a.subst σ) (b.subst σ)
  | .orRight a b => .orRight (a.subst σ) (b.subst σ)
  | .orElim a b c => .orElim (a.subst σ) (b.subst σ) (c.subst σ)
  | .explosion a => .explosion (a.subst σ)
  | .excludedMiddle a => .excludedMiddle (a.subst σ)
  | .mp a b => .mp (a.subst σ) (b.subst σ)

/-- Rule instances are stable under substitution, in both profiles. -/
theorem checkRule_subst (profile : Profile) (σ : LO.Propositional.Substitution Nat) {code : Code}
    {premises : List Formula} {conclusion : Formula}
    (accepted : checkRule profile code premises conclusion = true) :
    checkRule profile (substCode σ code) (premises.map (LO.Propositional.Formula.subst σ))
      (conclusion.subst σ) = true := by
  simp only [checkRule, Bool.and_eq_true, decide_eq_true_eq] at accepted ⊢
  obtain ⟨⟨allowed, rfl⟩, rfl⟩ := accepted
  cases code <;> simp_all [substCode, Code.allowed, Code.premises, Code.conclusion,
    LO.Propositional.Formula.subst] <;> rfl

/-- Substitution as an action on rule instances. -/
def substAction (profile : Profile) (σ : LO.Propositional.Substitution Nat) :
    InstanceAction (interface profile).signature (LO.Propositional.Formula.subst σ) :=
  fun _ _ rule => ⟨substCode σ rule.1, checkRule_subst profile σ rule.2⟩

/-- **The schematic level.** Every substitution acts on the free Hilbert
multicategory by a multifunctor. -/
def substFunctor (profile : Profile) (σ : LO.Propositional.Substitution Nat) :
    (free (interface profile).signature).Functor (free (interface profile).signature)
      (LO.Propositional.Formula.subst σ) :=
  actFunctor _ (substAction profile σ)

/-- Hence Hilbert derivability is closed under substitution, a consequence of
the action rather than an added rule. -/
theorem source_subst (profile : Profile) (σ : LO.Propositional.Substitution Nat) {formula : Formula}
    (source : Source profile formula) : Source profile (formula.subst σ) :=
  (derivable_iff_source profile _).mp
    (Derivable.act _ (substAction profile σ) ((derivable_iff_source profile formula).mpr source))

theorem substCode_comp (σ τ : LO.Propositional.Substitution Nat) (code : Code) :
    substCode σ (substCode τ code) = substCode (LO.Propositional.Substitution.comp τ σ) code := by
  cases code <;> simp [substCode, LO.Propositional.Formula.subst_comp]

/-- Rule instances over transported premise lists are heterogeneously equal when
their codes agree. -/
theorem instance_heq (profile : Profile) {L L' : List Formula} {c c' : Formula} (lists : L = L')
    (conclusions : c = c') (x : (interface profile).signature L c) (y : (interface profile).signature L' c')
    (codes : x.1 = y.1) : HEq x y := by
  subst lists
  subst conclusions
  exact heq_of_eq (Subtype.ext codes)

/-- **Coherence of the schematic level.** Substituting by `τ` and then by `σ`
agrees with substituting by their composite, on every derivation, up to the
identification of the substituted formulas. -/
theorem substFunctor_comp_heq (profile : Profile) (σ τ : LO.Propositional.Substitution Nat)
    {n : ℕ} {Γ : Fin n → Formula} {b : Formula} (t : Term (interface profile).signature Γ b) :
    HEq ((substFunctor profile σ).map ((substFunctor profile τ).map t))
      ((substFunctor profile (LO.Propositional.Substitution.comp τ σ)).map t) := by
  apply act_comp_heq _ _ _ (substAction profile σ) (substAction profile τ)
    (substAction profile (LO.Propositional.Substitution.comp τ σ))
    (fun formula => LO.Propositional.Formula.subst_comp.symm)
  intro premises conclusion rule
  apply instance_heq profile
  · rw [List.map_map]
    exact List.map_congr_left fun formula _ => LO.Propositional.Formula.subst_comp.symm
  · exact LO.Propositional.Formula.subst_comp.symm
  · exact substCode_comp σ τ rule.1

end Hilbert

namespace Extension

open PropositionalHilbertChecking
open PropositionalExtension (Definition declarations Admitted atoms ExtensionCode)

/-- Classical rule instances are rule instances of every extension. -/
def toExtended (hypotheses : List Formula) : ∀ premises conclusion,
    (interface .classical).signature premises conclusion →
      (PropositionalExtension.interface hypotheses).signature premises conclusion :=
  fun _ _ rule => ⟨.core rule.1, rule.2⟩

theorem toExtended_injective (hypotheses : List Formula) (premises : List Formula)
    (conclusion : Formula) : Function.Injective (toExtended hypotheses premises conclusion) := by
  intro first second same
  apply Subtype.ext
  have := congrArg Subtype.val same
  simp only [toExtended] at this
  injection this

/-- The inclusion multifunctor. -/
def inclusion (hypotheses : List Formula) : (free (interface .classical).signature).Functor
    (free (PropositionalExtension.interface hypotheses).signature) _root_.id :=
  liftFunctor (rename (toExtended hypotheses))

/-- **Faithful.** -/
theorem inclusion_faithful (hypotheses : List Formula) {n : ℕ} {Γ : Fin n → Formula}
    {b : Formula} {t t' : Term (interface .classical).signature Γ b}
    (same : (inclusion hypotheses).map t = (inclusion hypotheses).map t') : t = t' :=
  lift_rename_injective (toExtended hypotheses) (toExtended_injective hypotheses) same

/-- **Conservative.** Over admitted fresh definitions, every claim in the old
vocabulary derivable with the definitions is derivable classically. -/
theorem inclusion_conservative (definitions : List Definition) (claim : Formula)
    (admitted : Admitted (atoms claim) definitions)
    (derivable : Derivable (PropositionalExtension.interface (declarations definitions)).signature claim) :
    Derivable (interface .classical).signature claim := by
  apply (Hilbert.derivable_iff_source .classical claim).mpr
  apply PropositionalExtension.valid_source claim definitions
  exact ⟨admitted,
    (RuleWitness.derivable_iff_derives (PropositionalExtension.interface _) claim).mp derivable⟩

/-- The root rule instance of a derivation, when it has one. -/
def rootCode {hypotheses : List Formula} {n : ℕ} {Γ : Fin n → Formula} {b : Formula} :
    Term (PropositionalExtension.interface hypotheses).signature Γ b → Option ExtensionCode
  | .var _ => none
  | .node rule _ => some rule.1

theorem rootCode_inclusion (hypotheses : List Formula) {n : ℕ} {Γ : Fin n → Formula} {b : Formula}
    (t : Term (interface .classical).signature Γ b) :
    ∀ code, rootCode ((inclusion hypotheses).map t) = some code → ∃ core, code = .core core := by
  intro code found
  cases t with
  | var i => cases found
  | node rule children =>
      simp only [inclusion, liftFunctor_map] at found
      change rootCode (Term.node (toExtended hypotheses _ _ rule) _) = some code at found
      simp only [rootCode, toExtended, Option.some.injEq] at found
      exact ⟨rule.1, found.symm⟩

/-- **Not full.** Citing a definition is a derivation of the extended kernel that is
the image of no classical derivation. -/
theorem inclusion_not_full (formula : Formula) :
    ∃ t : Term (PropositionalExtension.interface [formula]).signature closedContext formula,
      ∀ t' : Term (interface .classical).signature closedContext formula,
        (inclusion [formula]).map t' ≠ t := by
  refine ⟨.node (premises := []) ⟨.hypothesis 0, by
      show PropositionalExtension.checkRule [formula] (.hypothesis 0) [] formula = true
      simp [PropositionalExtension.checkRule]⟩
    (fun p => p.elim0), ?_⟩
  intro t' same
  obtain ⟨core, impossible⟩ := rootCode_inclusion [formula] t' (.hypothesis 0) (by rw [same]; rfl)
  cases impossible

end Extension

namespace Contraction

open OSLF.NativeTypes.Certificates

/-- The rule instances of a finite presentation. -/
def presentationSignature (P : Presentation.{0}) : RuleSignature.{0, 0} P.Judgment :=
  fun premises conclusion => {rule : P.Rule // P.premises rule = premises ∧ P.conclusion rule = conclusion}

/-- The chain calculus: one premise per step. -/
inductive ChainRule : List ℕ → ℕ → Type
  | base : ChainRule [] 0
  | step (k : ℕ) : ChainRule [k] (k + 1)

/-- The duplication calculus of `ProofSharingBounds`. -/
abbrev Duplication := presentationSignature ProofSharingBounds.presentation

/-- Rule images: each step becomes one duplication citing its premise twice. -/
def image : Interpretation ChainRule (free Duplication) _root_.id
  | _, _, .base => .node (premises := []) ⟨.base, rfl, rfl⟩ (fun p => p.elim0)
  | _, _, .step k => .node (premises := [k, k]) ⟨.duplicate k, rfl, rfl⟩
      (Fin.cases (motive := fun p : Fin 2 =>
          Term Duplication (_root_.id ∘ [k].get) ([k, k].get p))
        (Term.var 0)
        (Fin.cases (motive := fun q : Fin 1 =>
            Term Duplication (_root_.id ∘ [k].get) ([k, k].get q.succ))
          (Term.var 0) (fun r => r.elim0)))

/-- The chain derivation of level `k`. -/
def chain : (k : ℕ) → Term ChainRule closedContext k
  | 0 => .node .base (fun p => p.elim0)
  | k + 1 => .node (.step k)
      (Fin.cases (motive := fun p : Fin 1 => Term ChainRule closedContext ([k].get p))
        (chain k) (fun r => r.elim0))

theorem chain_size (k : ℕ) : (chain k).size = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [chain, Term.size, List.ofFn_succ, List.ofFn_zero, Fin.cases_zero,
        List.sum_cons, List.sum_nil, ih]
      omega

/-- **Contraction makes the tree translation exponential.** -/
theorem image_size (k : ℕ) : ((chain k).lift image).size + 1 = 2 ^ (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have unfolded : ((chain (k + 1)).lift image).size =
          2 * ((chain k).lift image).size + 1 := by
        change Term.size (Term.node (S := Duplication) (premises := [k, k])
            ⟨.duplicate k, rfl, rfl⟩ _) = _
        simp only [Term.size, List.ofFn_succ, List.ofFn_zero, List.sum_cons, List.sum_nil,
          Fin.succ_zero_eq_one]
        change ((chain k).lift image).size + (((chain k).lift image).size + 0) + 1 = _
        omega
      rw [unfolded, pow_succ]
      omega

/-- The source derivations grow linearly while their translations grow
exponentially. -/
theorem contraction_gap (k : ℕ) :
    (chain k).size = k + 1 ∧ ((chain k).lift image).size + 1 = 2 ^ (k + 1) ∧
      Shared.checkJudgments (ProofSharingBounds.certificate k) k = true ∧
      (ProofSharingBounds.rows k).length = k + 1 :=
  ⟨chain_size k, image_size k, ProofSharingBounds.dag_checked k, ProofSharingBounds.rows_length k⟩

/-- The duplication rule image is not affine: it cites its premise twice. -/
theorem image_not_affine (k : ℕ) : ¬ Term.Affine (image [k] (k + 1) (.step k)) := by
  have occurrences : (image [k] (k + 1) (.step k)).occurrences = [0, 0] := rfl
  unfold Term.Affine
  rw [occurrences]
  simp

end Contraction

namespace Revalidation

open PropositionalHilbertChecking DerivationGraph
open PropositionalExtension (Definition declarations validate atoms ExtensionCode DAGCertificate checkDAG)

/-- **Profile extension.** Every accepted intuitionistic graph is accepted by the
classical kernel with the same cache. -/
theorem intuitionistic_to_classical {Origin : Type} {nodes : List (Node Formula Code Origin)}
    {cache : Array Formula} (accepted : replay (interface .intuitionistic) nodes = some cache) :
    replay (interface .classical) nodes = some cache := by
  have moved := replay_extend (interface .intuitionistic) (interface .classical) id
    (fun _ _ _ old => Hilbert.checkRule_classical old) accepted
  have same : ∀ l : List (Node Formula Code Origin), l.map (Node.map id id id) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, ih]; rfl
  convert moved using 2
  exact congrArg _ (same nodes).symm

/-- Instances admitted under some definitions stay admitted when further
definitions are appended. -/
theorem checkRule_append (definitions more : List Definition) (code : ExtensionCode)
    (premises : List Formula) (conclusion : Formula)
    (accepted : PropositionalExtension.checkRule (declarations definitions) code premises conclusion = true) :
    PropositionalExtension.checkRule (declarations (definitions ++ more)) code premises conclusion = true := by
  cases code with
  | core code => exact accepted
  | hypothesis index =>
      simp only [PropositionalExtension.checkRule, decide_eq_true_eq] at accepted ⊢
      obtain ⟨empty, found⟩ := accepted
      refine ⟨empty, ?_⟩
      have inside : index < (declarations definitions).length :=
        (List.getElem?_eq_some_iff.mp found).1
      simp only [declarations, List.map_append]
      rw [List.getElem?_append_left (by simpa [declarations] using inside)]
      exact found

/-- **Admission joined to retained evidence.** An accepted extension graph remains
accepted when further admitted definitions are appended: admission is rechecked
and the retained graph is revalidated against the extended declarations. -/
theorem checkDAG_append (claim : Formula) (definitions more : List Definition)
    (nodes : List (Node Formula ExtensionCode Unit)) (root : Nat)
    (accepted : checkDAG claim ⟨definitions, nodes, root⟩ = true)
    (admitted : validate (atoms claim) (definitions ++ more) = true) :
    checkDAG claim ⟨definitions ++ more, nodes, root⟩ = true := by
  simp only [checkDAG, Bool.and_eq_true, decide_eq_true_eq] at accepted ⊢
  refine ⟨admitted, ?_⟩
  obtain ⟨-, rooted⟩ := accepted
  cases replayed : replay (PropositionalExtension.interface (declarations definitions)) nodes with
  | none => rw [replayed] at rooted; cases rooted
  | some cache =>
      rw [replayed] at rooted
      have moved := replay_extend (PropositionalExtension.interface (declarations definitions))
        (PropositionalExtension.interface (declarations (definitions ++ more))) id
        (fun code premises conclusion old => checkRule_append definitions more code premises conclusion old)
        replayed
      have same : ∀ l : List (Node Formula ExtensionCode Unit), l.map (Node.map id id id) = l := by
        intro l
        induction l with
        | nil => rfl
        | cons x xs ih => simp only [List.map_cons, ih]; rfl
      have moved' : replay (PropositionalExtension.interface (declarations (definitions ++ more))) nodes =
          some cache := by
        convert moved using 2
        exact congrArg _ (same nodes).symm
      rw [moved']
      exact rooted

namespace Controls

open PropositionalExtension.Controls

/-- The classical excluded-middle graph. -/
def emNodes : List (Node Formula Code Unit) := [⟨PropositionalHilbertChecking.Controls.em, .excludedMiddle (.atom 0), [], ()⟩]

theorem em_classical : replay (interface .classical) emNodes = some #[PropositionalHilbertChecking.Controls.em] := by
  decide

/-- Negative control: excluded middle does not revalidate intuitionistically. -/
theorem em_refused_intuitionistically :
    revalidate (interface .intuitionistic) id #[PropositionalHilbertChecking.Controls.em] emNodes = false := by
  decide

/-- Positive control: the worked extension graph survives an admitted further
definition. -/
theorem worked_extended :
    checkDAG oldClaim { worked with definitions := [fresh, ⟨2, .atom 1⟩] } = true :=
  checkDAG_append oldClaim [fresh] [⟨2, .atom 1⟩] worked.nodes worked.root (by decide) (by decide)

/-- Negative control: an admitted but different definition of the same symbol
refuses the retained graph. -/
theorem worked_changed_refused :
    validate (atoms oldClaim) [⟨1, .imp (.atom 0) (.atom 0)⟩] = true ∧
      checkDAG oldClaim { worked with definitions := [⟨1, .imp (.atom 0) (.atom 0)⟩] } = false := by
  constructor <;> decide

end Controls

end Revalidation

end Mettapedia.Logic
