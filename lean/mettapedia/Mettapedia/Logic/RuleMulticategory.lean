import Mettapedia.Logic.Derivation
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Free cartesian multicategories on rule signatures

A finitary inference rule has an ordered list of premises and one conclusion.
A *rule signature* assigns to each premise list and conclusion the type of its
proof-relevant rule instances. Open derivations are trees of rule instances
whose leaves are premise holes; plugging derivations into holes is
simultaneous substitution. This module proves that open derivations form the
free cartesian multicategory on the signature (`RuleSignature.universal`):
multifunctors out of it correspond exactly to interpretations of the rule
instances.

Contexts are finite sort assignments `Fin n → Sorts`. Holes are positions and
may be used any number of times, so exchange, weakening and contraction are
substitutions along position maps rather than equations between proofs.
Reindexing a context along a map of sorts is function composition. Hence
translations between rule systems with different judgments compose without
transport along list equations (`CartesianMulticategory.Functor.comp`).

Closed derivations are derivations in the empty context. They do not see the
structural rules: every closed derivation is linear (`Term.closed_linear`).
Open derivations do, and the identity of premise occurrences is retained
(`Term.var_injective`).

Logical work is counted by rule nodes. It is additive under substitution, with
each occurrence of a hole charged separately (`Term.size_subst`). A
translation whose rule images are affine is linear on trees
(`RuleSignature.lift_size_le`). Contraction in a rule image is exactly what
can make tree translations exponential; that example is in
`RuleMulticategoryCost`.

The single-sorted untyped case is the abstract clone; the List-indexed
presentation `MultiSortedClone` is the restriction of this structure to
contexts of the form `List.get`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic

universe u u' u'' v v' w w' w''

/-- A many-sorted cartesian multicategory in its clone presentation: a
multimorphism goes from a finite context of sorts to one sort, variables select
context positions, and composition is simultaneous substitution. -/
structure CartesianMulticategory (Sorts : Type u) where
  Hom : {n : ℕ} → (Fin n → Sorts) → Sorts → Type w
  var : {n : ℕ} → {Γ : Fin n → Sorts} → (i : Fin n) → Hom Γ (Γ i)
  subst : {m n : ℕ} → {Γ : Fin m → Sorts} → {Δ : Fin n → Sorts} → {b : Sorts} →
    Hom Γ b → ((i : Fin m) → Hom Δ (Γ i)) → Hom Δ b
  subst_var : ∀ {m n : ℕ} {Γ : Fin m → Sorts} {Δ : Fin n → Sorts}
    (σ : (i : Fin m) → Hom Δ (Γ i)) (i : Fin m), subst (var i) σ = σ i
  subst_vars : ∀ {n : ℕ} {Γ : Fin n → Sorts} {b : Sorts} (t : Hom Γ b),
    subst t (fun i => var i) = t
  subst_subst : ∀ {k m n : ℕ} {Γ : Fin k → Sorts} {Δ : Fin m → Sorts}
    {Θ : Fin n → Sorts} {b : Sorts} (t : Hom Γ b) (σ : (i : Fin k) → Hom Δ (Γ i))
    (τ : (j : Fin m) → Hom Θ (Δ j)),
    subst (subst t σ) τ = subst t (fun i => subst (σ i) τ)

namespace CartesianMulticategory

variable {Sorts : Type u} {Sorts' : Type u'} {Sorts'' : Type u''}

/-- A multifunctor over a map of sorts: it preserves variables and substitution.
Contexts are reindexed by composition, so no transport is involved. -/
structure Functor (M : CartesianMulticategory.{u, w} Sorts)
    (N : CartesianMulticategory.{u', w'} Sorts') (obj : Sorts → Sorts') where
  map : {n : ℕ} → {Γ : Fin n → Sorts} → {b : Sorts} → M.Hom Γ b → N.Hom (obj ∘ Γ) (obj b)
  map_var : ∀ {n : ℕ} {Γ : Fin n → Sorts} (i : Fin n),
    map (M.var (Γ := Γ) i) = N.var (Γ := obj ∘ Γ) i
  map_subst : ∀ {m n : ℕ} {Γ : Fin m → Sorts} {Δ : Fin n → Sorts} {b : Sorts}
    (t : M.Hom Γ b) (σ : (i : Fin m) → M.Hom Δ (Γ i)),
    map (M.subst t σ) = N.subst (map t) (fun i => map (σ i))

namespace Functor

variable {M : CartesianMulticategory.{u, w} Sorts}
  {N : CartesianMulticategory.{u', w'} Sorts'}
  {P : CartesianMulticategory.{u'', w''} Sorts''}

/-- Multifunctors are determined by their action on multimorphisms. -/
@[ext] theorem ext {obj : Sorts → Sorts'} {F G : M.Functor N obj}
    (same : ∀ {n : ℕ} {Γ : Fin n → Sorts} {b : Sorts} (t : M.Hom Γ b), F.map t = G.map t) :
    F = G := by
  cases F with
  | mk mapF varF substF =>
    cases G with
    | mk mapG varG substG =>
      have maps : @mapF = @mapG := by
        funext n Γ b t
        exact same t
      cases maps
      rfl

/-- The identity multifunctor. -/
def id (M : CartesianMulticategory.{u, w} Sorts) : M.Functor M _root_.id where
  map t := t
  map_var _ := rfl
  map_subst _ _ := rfl

/-- Multifunctors compose over the composite map of sorts. -/
def comp {f : Sorts → Sorts'} {g : Sorts' → Sorts''} (F : M.Functor N f) (G : N.Functor P g) :
    M.Functor P (g ∘ f) where
  map t := G.map (F.map t)
  map_var i := (congrArg G.map (F.map_var i)).trans (G.map_var i)
  map_subst t σ := (congrArg G.map (F.map_subst t σ)).trans (G.map_subst _ _)

@[simp] theorem comp_map {f : Sorts → Sorts'} {g : Sorts' → Sorts''} (F : M.Functor N f)
    (G : N.Functor P g) {n : ℕ} {Γ : Fin n → Sorts} {b : Sorts} (t : M.Hom Γ b) :
    (F.comp G).map t = G.map (F.map t) := rfl

theorem id_comp {f : Sorts → Sorts'} (F : M.Functor N f) : (Functor.id M).comp F = F :=
  ext fun _ => rfl

theorem comp_id {f : Sorts → Sorts'} (F : M.Functor N f) : F.comp (Functor.id N) = F :=
  ext fun _ => rfl

theorem comp_assoc {Sorts''' : Type u} {Q : CartesianMulticategory.{u, w} Sorts'''}
    {f : Sorts → Sorts'} {g : Sorts' → Sorts''} {h : Sorts'' → Sorts'''}
    (F : M.Functor N f) (G : N.Functor P g) (H : P.Functor Q h) :
    (F.comp G).comp H = F.comp (G.comp H) :=
  ext fun _ => rfl

end Functor

/-- The empty context. -/
def closedContext : Fin 0 → Sorts := Fin.elim0

/-- A sort is inhabited by a closed multimorphism. -/
def Inhabited (M : CartesianMulticategory.{u, w} Sorts) (b : Sorts) : Prop :=
  Nonempty (M.Hom closedContext b)

/-- Closed multimorphisms move between the (unique up to equality) empty contexts. -/
def reclose (M : CartesianMulticategory.{u, w} Sorts) {Γ Γ' : Fin 0 → Sorts} {b : Sorts}
    (t : M.Hom Γ b) : M.Hom Γ' b :=
  M.subst t (fun i => i.elim0)

/-- A multifunctor carries closed multimorphisms to closed multimorphisms. -/
theorem Functor.inhabited {M : CartesianMulticategory.{u, w} Sorts}
    {N : CartesianMulticategory.{u', w'} Sorts'} {obj : Sorts → Sorts'}
    (F : M.Functor N obj) {b : Sorts} (inhabited : M.Inhabited b) : N.Inhabited (obj b) := by
  obtain ⟨t⟩ := inhabited
  exact ⟨N.reclose (F.map t)⟩

end CartesianMulticategory

/-- A proof-relevant finitary rule signature: for each ordered premise list and
conclusion, the type of rule instances. -/
abbrev RuleSignature (Sorts : Type u) := List Sorts → Sorts → Type v

namespace RuleSignature

variable {Sorts : Type u} {Sorts' : Type u'}

/-- Open derivations: a premise hole, or a rule instance applied to one open
derivation per ordered premise. -/
inductive Term (S : RuleSignature.{u, v} Sorts) {n : ℕ} (Γ : Fin n → Sorts) :
    Sorts → Type (max u v)
  | var (i : Fin n) : Term S Γ (Γ i)
  | node {premises : List Sorts} {conclusion : Sorts} (rule : S premises conclusion)
      (children : (p : Fin premises.length) → Term S Γ (premises.get p)) :
      Term S Γ conclusion

namespace Term

variable {S : RuleSignature.{u, v} Sorts}

/-- Simultaneous substitution: plug one derivation into every hole. -/
def subst {m n : ℕ} {Γ : Fin m → Sorts} {Δ : Fin n → Sorts} :
    {b : Sorts} → Term S Γ b → ((i : Fin m) → Term S Δ (Γ i)) → Term S Δ b
  | _, .var i, σ => σ i
  | _, .node rule children, σ => .node rule (fun p => (children p).subst σ)

@[simp] theorem subst_var' {m n : ℕ} {Γ : Fin m → Sorts} {Δ : Fin n → Sorts}
    (σ : (i : Fin m) → Term S Δ (Γ i)) (i : Fin m) : (Term.var (S := S) i).subst σ = σ i := rfl

theorem subst_vars {n : ℕ} {Γ : Fin n → Sorts} :
    ∀ {b : Sorts} (t : Term S Γ b), t.subst (fun i => .var i) = t
  | _, .var _ => rfl
  | _, .node rule children => by
      simp only [subst]
      congr 1
      funext p
      exact subst_vars (children p)

theorem subst_subst {k m n : ℕ} {Γ : Fin k → Sorts} {Δ : Fin m → Sorts} {Θ : Fin n → Sorts} :
    ∀ {b : Sorts} (t : Term S Γ b) (σ : (i : Fin k) → Term S Δ (Γ i))
      (τ : (j : Fin m) → Term S Θ (Δ j)),
      (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ)
  | _, .var _, _, _ => rfl
  | _, .node rule children, σ, τ => by
      simp only [subst]
      congr 1
      funext p
      exact subst_subst (children p) σ τ

/-- The hole selected by an open derivation, if it is a hole. -/
def index? {n : ℕ} {Γ : Fin n → Sorts} : {b : Sorts} → Term S Γ b → Option (Fin n)
  | _, .var i => some i
  | _, .node _ _ => none

theorem index?_heq {n : ℕ} {Γ : Fin n → Sorts} {a a' : Sorts} (same : a = a')
    {x : Term S Γ a} {y : Term S Γ a'} (h : HEq x y) : x.index? = y.index? := by
  subst same
  cases h
  rfl

/-- Two holes of the same sort remain different open derivations: the
identity of premise occurrences is retained. -/
theorem duplicate_holes_distinct (a : Sorts) :
    (Term.var (S := S) (Γ := fun _ : Fin 2 => a) 0) ≠ Term.var 1 := by
  intro same
  have indices := congrArg Term.index? same
  change some (0 : Fin 2) = some 1 at indices
  exact absurd (Option.some.inj indices) (by decide)

end Term

/-- Open derivations of a signature with substitution: a cartesian multicategory. -/
def free (S : RuleSignature.{u, v} Sorts) : CartesianMulticategory.{u, max u v} Sorts where
  Hom Γ b := Term S Γ b
  var i := .var i
  subst t σ := t.subst σ
  subst_var _ _ := rfl
  subst_vars t := Term.subst_vars t
  subst_subst t σ τ := Term.subst_subst t σ τ

variable {S : RuleSignature.{u, v} Sorts}

/-- A rule instance as a multimorphism from its premise list. -/
def gen {premises : List Sorts} {conclusion : Sorts} (rule : S premises conclusion) :
    Term S premises.get conclusion :=
  .node rule (fun p => .var p)

/-- Every node is a generator with its children substituted. -/
theorem gen_subst {n : ℕ} {Δ : Fin n → Sorts} {premises : List Sorts} {conclusion : Sorts}
    (rule : S premises conclusion)
    (children : (p : Fin premises.length) → Term S Δ (premises.get p)) :
    (gen rule).subst children = .node rule children := rfl

/-- An interpretation of the rule instances in a cartesian multicategory, over a
map of sorts. -/
abbrev Interpretation (S : RuleSignature.{u, v} Sorts)
    (M : CartesianMulticategory.{u', w} Sorts') (obj : Sorts → Sorts') :=
  ∀ (premises : List Sorts) (conclusion : Sorts),
    S premises conclusion → M.Hom (obj ∘ premises.get) (obj conclusion)

variable {M : CartesianMulticategory.{u', w} Sorts'} {obj : Sorts → Sorts'}

/-- The extension of an interpretation from generators to all open derivations. -/
def Term.lift (φ : Interpretation S M obj) {n : ℕ} {Γ : Fin n → Sorts} :
    {b : Sorts} → Term S Γ b → M.Hom (obj ∘ Γ) (obj b)
  | _, .var i => M.var (Γ := obj ∘ Γ) i
  | _, .node rule children => M.subst (φ _ _ rule) (fun p => (children p).lift φ)

theorem Term.lift_subst (φ : Interpretation S M obj) {m n : ℕ} {Γ : Fin m → Sorts}
    {Δ : Fin n → Sorts} :
    ∀ {b : Sorts} (t : Term S Γ b) (σ : (i : Fin m) → Term S Δ (Γ i)),
      (t.subst σ).lift φ = M.subst (t.lift φ) (fun i => (σ i).lift φ)
  | _, .var i, σ => (M.subst_var (Γ := obj ∘ Γ) (fun i => (σ i).lift φ) i).symm
  | _, .node rule children, σ => by
      change M.subst (φ _ _ rule) (fun p => ((children p).subst σ).lift φ) =
        M.subst (M.subst (φ _ _ rule) (fun p => (children p).lift φ)) (fun i => (σ i).lift φ)
      rw [M.subst_subst]
      congr 1
      funext p
      exact Term.lift_subst φ (children p) σ

/-- The multifunctor induced by an interpretation of the generators. -/
def liftFunctor (φ : Interpretation S M obj) : (free S).Functor M obj where
  map t := Term.lift φ t
  map_var _ := rfl
  map_subst t σ := Term.lift_subst φ t σ

@[simp] theorem liftFunctor_map (φ : Interpretation S M obj) {n : ℕ} {Γ : Fin n → Sorts}
    {b : Sorts} (t : Term S Γ b) : (liftFunctor φ).map t = t.lift φ := rfl

/-- Restricting a multifunctor to the generators. -/
def restrict (F : (free S).Functor M obj) : Interpretation S M obj :=
  fun _ _ rule => F.map (gen rule)

theorem lift_restrict_map (F : (free S).Functor M obj) {n : ℕ} {Γ : Fin n → Sorts} :
    ∀ {b : Sorts} (t : Term S Γ b), t.lift (restrict F) = F.map t
  | _, .var i => (F.map_var i).symm
  | _, .node rule children => by
      calc Term.lift (restrict F) (Term.node rule children)
          = M.subst (F.map (gen rule)) (fun p => F.map (children p)) := by
            change M.subst (F.map (gen rule)) (fun p => (children p).lift (restrict F)) = _
            congr 1
            funext p
            exact lift_restrict_map F (children p)
        _ = F.map (Term.node rule children) := (F.map_subst (gen rule) children).symm

theorem lift_gen (φ : Interpretation S M obj) {premises : List Sorts} {conclusion : Sorts}
    (rule : S premises conclusion) : (gen rule).lift φ = φ _ _ rule :=
  M.subst_vars (φ _ _ rule)

/-- **Freeness.** Multifunctors out of the open derivations of a rule signature
are exactly interpretations of its rule instances. -/
def universal : (free S).Functor M obj ≃ Interpretation S M obj where
  toFun := restrict
  invFun := liftFunctor
  left_inv F := CartesianMulticategory.Functor.ext fun t => lift_restrict_map F t
  right_inv φ := by
    funext premises conclusion rule
    exact lift_gen φ rule

/-- Uniqueness: a multifunctor is determined by its values on generators. -/
theorem functor_eq_of_gen {F G : (free S).Functor M obj}
    (same : ∀ (premises : List Sorts) (conclusion : Sorts) (rule : S premises conclusion),
      F.map (gen rule) = G.map (gen rule)) : F = G :=
  universal.injective (funext fun premises => funext fun conclusion =>
    funext fun rule => same premises conclusion rule)

/-! ## Derivability -/

/-- A sort is derivable when it has a closed derivation. -/
def Derivable (S : RuleSignature.{u, v} Sorts) (b : Sorts) : Prop :=
  (free S).Inhabited b

/-- Translations preserve derivability. -/
theorem Derivable.map {S' : RuleSignature.{u', v'} Sorts'} (φ : Interpretation S (free S') obj)
    {b : Sorts} (derivable : Derivable S b) : Derivable S' (obj b) :=
  (liftFunctor φ).inhabited derivable

/-- The rule predicate of a signature: a rule instance exists. -/
def Holds (S : RuleSignature.{u, v} Sorts) (premises : List Sorts) (conclusion : Sorts) : Prop :=
  Nonempty (S premises conclusion)

private theorem finite_nonempty {n : ℕ} (F : Fin n → Type w)
    (present : ∀ position, Nonempty (F position)) :
    Nonempty ((position : Fin n) → F position) := by
  induction n with
  | zero => exact ⟨fun position => position.elim0⟩
  | succ n ih =>
      obtain ⟨first⟩ := present 0
      obtain ⟨later⟩ := ih (fun position => F position.succ) (fun position => present position.succ)
      exact ⟨Fin.cases first later⟩

/-- Closed derivations of the free multicategory give exactly the inductive rule
closure of `Logic.Derivation`. -/
theorem derivable_iff_derives (b : Sorts) : Derivable S b ↔ Derives S.Holds b := by
  constructor
  · rintro ⟨t⟩
    have closed : ∀ {c : Sorts} (t : Term S CartesianMulticategory.closedContext c),
        Derives S.Holds c := by
      intro c t
      induction t with
      | var i => exact i.elim0
      | node rule children ih =>
          refine Derives.node _ _ ⟨rule⟩ ?_
          intro premise member
          obtain ⟨p, rfl⟩ := List.get_of_mem member
          exact ih p
    exact closed t
  · intro derivation
    refine Derives.least (fun c => Derivable S c) ?_ derivation
    intro premises conclusion ⟨rule⟩ children
    obtain ⟨found⟩ := finite_nonempty
      (fun p : Fin premises.length => Term S CartesianMulticategory.closedContext (premises.get p))
      (fun p => children _ (List.get_mem premises p))
    exact ⟨.node rule found⟩

/-! ## Actions on rule instances -/

/-- Move a term from a mapped list context to the composite context. -/
def Term.reindexMap {α : Type u'} (f : α → Sorts) (l : List α) {b : Sorts}
    (t : Term S (l.map f).get b) : Term S (f ∘ l.get) b :=
  t.subst fun i =>
    (show f (l.get (Fin.cast (by simp) i)) = (l.map f).get i by simp) ▸
      Term.var (S := S) (Γ := f ∘ l.get) (Fin.cast (by simp) i)

/-- An action of a map of sorts on rule instances: every instance moves to an
instance of the mapped premises and conclusion. Substitution into schematic
rules, renaming of object variables and relabelling of judgments have this
shape whenever the rule-instance predicate is stable under them. -/
abbrev InstanceAction (S : RuleSignature.{u, v} Sorts) (σ : Sorts → Sorts) :=
  ∀ premises conclusion, S premises conclusion → S (premises.map σ) (σ conclusion)

/-- The interpretation of an instance action: each instance becomes the moved
generator. -/
def actInterpretation (σ : Sorts → Sorts) (ψ : InstanceAction S σ) : Interpretation S (free S) σ :=
  fun premises conclusion rule => Term.reindexMap σ premises (gen (ψ premises conclusion rule))

/-- **Stable instance predicates act by multifunctors.** -/
def actFunctor (σ : Sorts → Sorts) (ψ : InstanceAction S σ) : (free S).Functor (free S) σ :=
  liftFunctor (actInterpretation σ ψ)

/-- Derivability is closed under every instance action. -/
theorem Derivable.act (σ : Sorts → Sorts) (ψ : InstanceAction S σ) {b : Sorts}
    (derivable : Derivable S b) : Derivable S (σ b) :=
  (actFunctor σ ψ).inhabited derivable

/-- Substituting into a transported term transports the result. -/
theorem Term.subst_cast_heq {m n : ℕ} {Γ : Fin m → Sorts} {Δ : Fin n → Sorts} {a a' : Sorts}
    (same : a = a') (t : Term S Γ a) (σ : (i : Fin m) → Term S Δ (Γ i)) :
    HEq ((same ▸ t : Term S Γ a').subst σ) (t.subst σ) := by
  subst same
  rfl

/-- Lifting respects heterogeneous equality of terms over equal sorts. -/
theorem Term.lift_heq {Sorts' : Type u'} {M : CartesianMulticategory.{u', w} Sorts'}
    {obj : Sorts → Sorts'} (φ : Interpretation S M obj) {n : ℕ} {Γ : Fin n → Sorts} {a a' : Sorts}
    (same : a = a') {t : Term S Γ a} {t' : Term S Γ a'} (h : HEq t t') :
    HEq (t.lift φ) (t'.lift φ) := by
  subst same
  cases h
  rfl

/-- Nodes with transported premise lists, rules and children. -/
theorem Term.node_heq {n n' : ℕ} {Δ : Fin n → Sorts} {Δ' : Fin n' → Sorts} (sizes : n = n')
    (contexts : HEq Δ Δ') {L L' : List Sorts} (lists : L = L') {c c' : Sorts} (conclusions : c = c')
    {r : S L c} {r' : S L' c'} (rules : HEq r r')
    {children : (p : Fin L.length) → Term S Δ (L.get p)}
    {children' : (p : Fin L'.length) → Term S Δ' (L'.get p)}
    (pointwise : ∀ (p : Fin L.length) (p' : Fin L'.length), (p : ℕ) = p' → HEq (children p) (children' p')) :
    HEq (Term.node r children) (Term.node r' children') := by
  subst sizes
  cases contexts
  subst lists
  subst conclusions
  cases rules
  have : children = children' := funext fun p => eq_of_heq (pointwise p p rfl)
  subst this
  rfl

/-- **Coherence of instance actions.** If two actions compose, on sorts and on
rule instances, to a third, then acting by the two in turn agrees with acting
by the third on every derivation, up to the identification of sorts. -/
theorem act_comp_heq (σ τ ρ : Sorts → Sorts) (ψσ : InstanceAction S σ) (ψτ : InstanceAction S τ)
    (ψρ : InstanceAction S ρ) (sorts : ∀ b, σ (τ b) = ρ b)
    (rules : ∀ premises conclusion (rule : S premises conclusion),
      HEq (ψσ _ _ (ψτ premises conclusion rule)) (ψρ premises conclusion rule))
    {n : ℕ} {Γ : Fin n → Sorts} {b : Sorts} (t : Term S Γ b) :
    HEq ((t.lift (actInterpretation τ ψτ)).lift (actInterpretation σ ψσ))
      (t.lift (actInterpretation ρ ψρ)) := by
  have contexts : HEq (σ ∘ (τ ∘ Γ)) (ρ ∘ Γ) := heq_of_eq (funext fun i => sorts (Γ i))
  induction t with
  | var i =>
      change HEq (Term.var (S := S) (Γ := σ ∘ (τ ∘ Γ)) i) (Term.var (S := S) (Γ := ρ ∘ Γ) i)
      have equal : σ ∘ (τ ∘ Γ) = ρ ∘ Γ := eq_of_heq contexts
      rw [equal]
  | @node premises conclusion rule children ih =>
      apply Term.node_heq rfl contexts
        (by rw [List.map_map]; exact List.map_congr_left fun b _ => sorts b) (sorts conclusion)
        (rules premises conclusion rule)
      intro p p' values
      refine HEq.trans (Term.subst_cast_heq _ _ _) ?_
      refine HEq.trans ?_ (Term.subst_cast_heq _ _ _).symm
      change HEq ((Term.subst _ _).lift (actInterpretation σ ψσ)) ((children _).lift _)
      refine HEq.trans (Term.lift_heq (actInterpretation σ ψσ) (by simp) (Term.subst_cast_heq _ _ _)) ?_
      change HEq ((children _).lift (actInterpretation τ ψτ) |>.lift (actInterpretation σ ψσ)) _
      have sameIndex : (Fin.cast (by simp) (Fin.cast (by simp) p : Fin (premises.map τ).length) :
          Fin premises.length) = Fin.cast (by simp) p' := by
        ext
        simpa using values
      rw [sameIndex]
      exact ih _

/-! ## Faithful translations -/

variable {S' : RuleSignature.{u, v'} Sorts}

/-- A sort-preserving renaming of rule instances. -/
def rename (ψ : ∀ premises conclusion, S premises conclusion → S' premises conclusion) :
    Interpretation S (free S') _root_.id :=
  fun _ _ rule => gen (ψ _ _ rule)

theorem lift_rename_node (ψ : ∀ premises conclusion, S premises conclusion → S' premises conclusion)
    {n : ℕ} {Γ : Fin n → Sorts} {premises : List Sorts} {conclusion : Sorts}
    (rule : S premises conclusion) (children : (p : Fin premises.length) → Term S Γ (premises.get p)) :
    (Term.node rule children).lift (rename ψ) =
      Term.node (ψ _ _ rule) (fun p => (children p).lift (rename ψ)) := rfl

/-- **Faithfulness.** A sort-preserving renaming that is injective on rule
instances induces an injective multifunctor: distinct open derivations stay
distinct. The heterogeneous form allows the conclusion index to vary. -/
theorem lift_rename_heq (ψ : ∀ premises conclusion, S premises conclusion → S' premises conclusion)
    (injective : ∀ premises conclusion, Function.Injective (ψ premises conclusion))
    {n : ℕ} {Γ : Fin n → Sorts} {b : Sorts} (t : Term S Γ b) :
    ∀ {b' : Sorts} (t' : Term S Γ b'), b = b' →
      HEq (t.lift (rename ψ)) (t'.lift (rename ψ)) → HEq t t' := by
  induction t with
  | var i =>
      intro b' t' same h
      cases t' with
      | var j =>
          have indices := Term.index?_heq same h
          change some i = some j at indices
          cases Option.some.inj indices
          rfl
      | node rule' children' =>
          have indices := Term.index?_heq same h
          change some i = none at indices
          cases indices
  | node rule children ih =>
      intro b' t' same h
      cases t' with
      | var j =>
          have indices := Term.index?_heq same h
          change none = some j at indices
          cases indices
      | node rule' children' =>
          subst same
          have images := eq_of_heq h
          change Term.node (ψ _ _ rule) (fun p => (children p).lift (rename ψ)) =
            Term.node (ψ _ _ rule') (fun p => (children' p).lift (rename ψ)) at images
          have parts := Term.node.inj images
          obtain ⟨lists, rules, kids⟩ := parts
          subst lists
          have equalRules : rule = rule' := injective _ _ (eq_of_heq rules)
          subst equalRules
          have equalKids := eq_of_heq kids
          have pointwise : ∀ p, children p = children' p := fun p =>
            eq_of_heq (ih p (children' p) rfl (heq_of_eq (congrFun equalKids p)))
          have : children = children' := funext pointwise
          subst this
          rfl

theorem lift_rename_injective (ψ : ∀ premises conclusion, S premises conclusion → S' premises conclusion)
    (injective : ∀ premises conclusion, Function.Injective (ψ premises conclusion))
    {n : ℕ} {Γ : Fin n → Sorts} {b : Sorts} {t t' : Term S Γ b}
    (same : t.lift (rename ψ) = t'.lift (rename ψ)) : t = t' :=
  eq_of_heq (lift_rename_heq ψ injective t t' rfl (heq_of_eq same))

/-! ## Structural rules -/

namespace Term

variable {S : RuleSignature.{u, v} Sorts}

/-- The premise holes used by an open derivation, from left to right, with
repetition. -/
def occurrences {n : ℕ} {Γ : Fin n → Sorts} : {b : Sorts} → Term S Γ b → List (Fin n)
  | _, .var i => [i]
  | _, .node _ children => (List.ofFn fun p => (children p).occurrences).flatten

/-- Planar: every hole used exactly once, in context order. -/
def Linear {n : ℕ} {Γ : Fin n → Sorts} {b : Sorts} (t : Term S Γ b) : Prop :=
  t.occurrences = List.finRange n

/-- No contraction: no hole used twice. -/
def Affine {n : ℕ} {Γ : Fin n → Sorts} {b : Sorts} (t : Term S Γ b) : Prop :=
  t.occurrences.Nodup

theorem occurrences_closed {Γ : Fin 0 → Sorts} {b : Sorts} (t : Term S Γ b) :
    t.occurrences = [] := by
  cases h : t.occurrences with
  | nil => rfl
  | cons i _ => exact i.elim0

/-- Closed derivations do not see the structural rules: each is linear. -/
theorem closed_linear {Γ : Fin 0 → Sorts} {b : Sorts} (t : Term S Γ b) : t.Linear := by
  simp [Linear, occurrences_closed t, List.finRange_zero]

/-- A generator uses each premise exactly once, in order. -/
theorem gen_linear {premises : List Sorts} {conclusion : Sorts} (rule : S premises conclusion) :
    (gen rule).Linear := by
  simp [Linear, gen, occurrences, List.ofFn_eq_map]
  induction (List.finRange premises.length) with
  | nil => rfl
  | cons i rest ih => simp [ih]

end Term

/-! ## Logical work -/

namespace Term

variable {S : RuleSignature.{u, v} Sorts}

/-- Rule nodes of an open derivation tree: its logical work. -/
def size {n : ℕ} {Γ : Fin n → Sorts} : {b : Sorts} → Term S Γ b → ℕ
  | _, .var _ => 0
  | _, .node _ children => (List.ofFn fun p => (children p).size).sum + 1

private theorem sum_ofFn_add {k : ℕ} (f g : Fin k → ℕ) :
    (List.ofFn fun p => f p + g p).sum = (List.ofFn f).sum + (List.ofFn g).sum := by
  simp only [List.ofFn_eq_map]
  exact List.sum_map_add

/-- **Additivity.** Substitution adds the work of every plugged derivation once
per occurrence of its hole. -/
theorem size_subst {m n : ℕ} {Γ : Fin m → Sorts} {Δ : Fin n → Sorts} :
    ∀ {b : Sorts} (t : Term S Γ b) (σ : (i : Fin m) → Term S Δ (Γ i)),
      (t.subst σ).size = t.size + (t.occurrences.map fun i => (σ i).size).sum
  | _, .var i, σ => by simp [subst, size, occurrences]
  | _, .node rule children, σ => by
      have step : ∀ p, ((children p).subst σ).size =
          (children p).size + ((children p).occurrences.map fun i => (σ i).size).sum :=
        fun p => size_subst (children p) σ
      simp only [subst, size, occurrences, step, sum_ofFn_add, List.map_flatten, List.sum_flatten,
        List.map_ofFn, Function.comp_def]
      omega

end Term

/-- The sum of a nonnegative function over a duplicate-free list of positions is
at most its sum over all positions. -/
private theorem nodup_sum_le {k : ℕ} (l : List (Fin k)) (nodup : l.Nodup) (f : Fin k → ℕ) :
    (l.map f).sum ≤ (List.ofFn f).sum := by
  classical
  rw [← List.sum_toFinset f nodup, List.sum_ofFn]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **Affine translations are linear on trees.** If every rule image uses each
premise at most once and has at most `c` rule nodes, translation multiplies
tree size by at most `c`. -/
theorem lift_size_le {S' : RuleSignature.{u', v'} Sorts'} (φ : Interpretation S (free S') obj)
    (c : ℕ) (affine : ∀ premises conclusion (rule : S premises conclusion),
      Term.Affine (S := S') (φ premises conclusion rule))
    (small : ∀ premises conclusion (rule : S premises conclusion),
      Term.size (φ premises conclusion rule) ≤ c) {n : ℕ} {Γ : Fin n → Sorts} :
    ∀ {b : Sorts} (t : Term S Γ b), (t.lift φ).size ≤ c * t.size
  | _, .var _ => by simp [Term.lift, Term.size, free]
  | _, .node rule children => by
      let image : Term S' (obj ∘ _) (obj _) := φ _ _ rule
      have expand : ((Term.node rule children).lift φ).size =
          image.size + (image.occurrences.map fun p => ((children p).lift φ).size).sum :=
        Term.size_subst image (fun p => (children p).lift φ)
      have kids : ∀ p, ((children p).lift φ).size ≤ c * (children p).size :=
        fun p => lift_size_le φ c affine small (children p)
      have occurrencesBound := nodup_sum_le image.occurrences (affine _ _ rule)
        (fun p => ((children p).lift φ).size)
      have total : (List.ofFn fun p => ((children p).lift φ).size).sum ≤
          (List.ofFn fun p => c * (children p).size).sum := by
        simp only [List.sum_ofFn]
        exact Finset.sum_le_sum fun p _ => kids p
      have scaled : (List.ofFn fun p => c * (children p).size).sum =
          c * (List.ofFn fun p => (children p).size).sum := by
        simp only [List.sum_ofFn, Finset.mul_sum]
      have own : image.size ≤ c := small _ _ rule
      have nodeSize : (Term.node rule children).size =
          (List.ofFn fun p => (children p).size).sum + 1 := rfl
      rw [expand, nodeSize, Nat.mul_add, Nat.mul_one]
      omega

end RuleSignature

/-! ## Rule witnesses as signatures -/

namespace RuleWitness

variable {J : Type u} {rules : List J → J → Prop}

/-- The proof-relevant signature of a decidable rule-instance interface: a rule
instance is an accepted witness. -/
def signature (interface : RuleWitness.{u, v} rules) : RuleSignature.{u, v} J :=
  fun premises conclusion => {w : interface.W // interface.isInstance w premises conclusion = true}

/-- The witness signature presents exactly the source rules. -/
theorem signature_holds_iff (interface : RuleWitness.{u, v} rules) (premises : List J) (conclusion : J) :
    (signature interface).Holds premises conclusion ↔ rules premises conclusion := by
  constructor
  · rintro ⟨⟨w, accepted⟩⟩
    exact interface.sound w premises conclusion accepted
  · intro rule
    obtain ⟨w, accepted⟩ := interface.complete premises conclusion rule
    exact ⟨⟨w, accepted⟩⟩

/-- **Kernel derivability is closed derivability in the free multicategory** on
the kernel's rule instances. -/
theorem derivable_iff_derives (interface : RuleWitness.{u, v} rules) (judgment : J) :
    RuleSignature.Derivable (signature interface) judgment ↔ Derives rules judgment := by
  rw [RuleSignature.derivable_iff_derives]
  constructor
  · exact Derives.mono fun premises conclusion => (signature_holds_iff interface premises conclusion).mp
  · exact Derives.mono fun premises conclusion => (signature_holds_iff interface premises conclusion).mpr

end RuleWitness

end Mettapedia.Logic
