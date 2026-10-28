import Mettapedia.Logic.LP.Semantics
import Mettapedia.Logic.LP.StandardizeApart

/-!
# Logic Programming Kernel: SLD Resolution

SLD (Selective Linear Definite clause) resolution for logic programs.

## Scope

SLD resolution is formalized for **full first-order LP** — no function-free
restriction. The `SLDTree` type and `SLDTree_sound` theorem work with
compound terms including nested function symbol applications.

## Design

- `Grounding.compSubst` — composition of a grounding with a substitution,
  yielding a new grounding. Key bridge between SLD steps and model theory.
- `SLDTree prog goals θ` — big-step SLD refutation tree (leftmost selection).
  An SLD refutation reduces goals to empty via clause resolution steps.
- `SLDTree_sound` — soundness: if there is a refutation with computed answer θ,
  then every goal atom, grounded via θ and any further grounding, is in the
  least Herbrand model (Lloyd's Soundness Theorem, FLP Theorem 3.1).
- `SLDTree` leaves variable freshening as an informal convention, which makes
  derivations collide whenever a clause shares variable names with the query
  or with another activation.  `SLDScopedTree` repairs this: each resolution
  step names its source clause *and* an explicit activation scope, the clause
  is renamed by `Clause.atScope` as part of the step, and scopes strictly
  increase along the derivation — so standardization apart is structural, not
  assumed.  `SLDScopedTree_sound` grounds it in the same least Herbrand model.

## References

- Lloyd, *Foundations of Logic Programming*, 2nd ed., Ch. 3
- Apt, "Logic Programming", Ch. 4 (SLD Trees)
- van Emden & Kowalski, "Semantics of predicate logic as a programming language", 1976
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: Grounding-substitution composition -/

/-- Compose a grounding with a substitution: first apply θ to get terms,
    then ground the resulting terms. -/
def Grounding.compSubst {σ : LPSignature} (g : Grounding σ) (θ : Subst σ) : Grounding σ :=
  fun v => g.groundTerm (θ v)

/-- Grounding a substituted term equals applying the composed grounding. -/
theorem Grounding.groundTerm_applyTerm {σ : LPSignature}
    (g : Grounding σ) (θ : Subst σ) (t : Term σ) :
    g.groundTerm (θ.applyTerm t) = (g.compSubst θ).groundTerm t := by
  induction t with
  | var v => rfl
  | const _ => rfl
  | app f ts ih =>
    simp only [Subst.applyTerm, Grounding.groundTerm]
    congr 1; funext i; exact ih i

/-- Grounding a substituted atom equals applying the composed grounding. -/
theorem Grounding.groundAtom_applyAtom {σ : LPSignature}
    (g : Grounding σ) (θ : Subst σ) (a : Atom σ) :
    g.groundAtom (θ.applyAtom a) = (g.compSubst θ).groundAtom a := by
  unfold Grounding.groundAtom Subst.applyAtom
  congr 1; funext i; exact g.groundTerm_applyTerm θ (a.args i)

/-- Composing with a composition of substitutions equals composing stepwise. -/
theorem Grounding.compSubst_comp {σ : LPSignature}
    (g : Grounding σ) (θ₁ θ₂ : Subst σ) :
    g.compSubst (θ₁ ∘ₛ θ₂) = (g.compSubst θ₁).compSubst θ₂ := by
  funext v
  exact g.groundTerm_applyTerm θ₁ (θ₂ v)

private theorem Grounding.groundTerm_compSubst_id {σ : LPSignature}
    (g : Grounding σ) (t : Term σ) :
    (g.compSubst (Subst.id σ)).groundTerm t = g.groundTerm t := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app f ts ih =>
      simp [Grounding.groundTerm, ih]

private theorem Grounding.groundAtom_compSubst_id {σ : LPSignature}
    (g : Grounding σ) (a : Atom σ) :
    (g.compSubst (Subst.id σ)).groundAtom a = g.groundAtom a := by
  cases a with
  | mk symbol args =>
      simp [Grounding.groundAtom, Grounding.groundTerm_compSubst_id]

/-- Key equation: grounding via a composed substitution equals grounding the
    substituted atom. Combines `compSubst_comp` and `groundAtom_applyAtom`. -/
private theorem ground_comp_eq {σ : LPSignature}
    (g : Grounding σ) (θ₁ θ₂ : Subst σ) (a : Atom σ) :
    (g.compSubst (θ₁ ∘ₛ θ₂)).groundAtom a = (g.compSubst θ₁).groundAtom (θ₂.applyAtom a) := by
  rw [Grounding.compSubst_comp, ← Grounding.groundAtom_applyAtom]

/-! ## Section 2: SLD derivation trees -/

/-- SLD refutation tree (big-step, leftmost selection rule).

    `SLDTree prog goals θ` means there is an SLD refutation of `← goals`
    using clauses from `prog`, with computed answer substitution `θ`.

    At each step, the leftmost goal atom is selected, unified with a clause
    head, and replaced by the (substituted) clause body. The computed answer
    is the composition of all unifiers.

    **Variable freshening**: This definition assumes clauses are appropriately
    renamed at each step (standard "standardized apart" convention from Lloyd).
    Soundness holds regardless of freshening. -/
inductive SLDTree {σ : LPSignature} (prog : Program σ) :
    List (Atom σ) → Subst σ → Prop where
  /-- Empty goal list: refutation found with identity substitution. -/
  | nil : SLDTree prog [] (Subst.id σ)
  /-- Resolution step: unify leftmost goal with clause head, continue with
      the substituted clause body prepended to the remaining goals. -/
  | cons (a : Atom σ) (goals : List (Atom σ)) (c : Clause σ) (θ θ' : Subst σ) :
      c ∈ prog →
      θ.applyAtom a = θ.applyAtom c.head →
      SLDTree prog (θ.applyAtoms (c.body ++ goals)) θ' →
      SLDTree prog (a :: goals) (θ' ∘ₛ θ)

/-! ## Section 3: Soundness -/

/-- **Soundness of SLD resolution** (Lloyd, FLP Theorem 3.1):
    if there is an SLD refutation of `← goals` with computed answer `θ`,
    then for any grounding `g`, every goal atom grounded via `g ∘ θ`
    is in the least Herbrand model.

    Formally: `(g.compSubst θ).groundAtom a ∈ leastHerbrandModel kb`
    for every `a ∈ goals`. -/
theorem SLDTree_sound {σ : LPSignature} (kb : KnowledgeBase σ)
    (goals : List (Atom σ)) (θ : Subst σ) (h : SLDTree kb.prog goals θ) :
    ∀ g : Grounding σ, ∀ a ∈ goals,
      (g.compSubst θ).groundAtom a ∈ leastHerbrandModel kb := by
  induction h with
  | nil => intro _ _ ha; simp at ha
  | cons a goals c θ θ' hc hunif _ ih =>
    intro g a' ha'
    simp only [List.mem_cons] at ha'
    -- Rewrite: (g.compSubst (θ' ∘ₛ θ)).groundAtom a'
    --        = (g.compSubst θ').groundAtom (θ.applyAtom a')
    rw [ground_comp_eq]
    rcases ha' with rfl | ha'
    · -- Selected atom: use clause soundness
      -- (g.compSubst θ').groundAtom (θ.applyAtom a)
      -- = (g.compSubst θ').groundAtom (θ.applyAtom c.head)  [by hunif]
      rw [hunif]
      -- = (g.compSubst (θ' ∘ₛ θ)).groundAtom c.head        [by ground_comp_eq⁻¹]
      rw [← ground_comp_eq]
      -- Apply leastHerbrandModel_clause
      apply leastHerbrandModel_clause kb c hc (g.compSubst (θ' ∘ₛ θ))
      -- Need: ∀ b ∈ c.body, (g.compSubst (θ' ∘ₛ θ)).groundAtom b ∈ model
      intro b hb
      rw [ground_comp_eq]
      -- (g.compSubst θ').groundAtom (θ.applyAtom b) ∈ model
      -- θ.applyAtom b ∈ θ.applyAtoms (c.body ++ goals)
      exact ih g (θ.applyAtom b)
        (List.mem_map.mpr ⟨b, List.mem_append_left goals hb, rfl⟩)
    · -- Remaining goals: directly from IH
      exact ih g (θ.applyAtom a')
        (List.mem_map.mpr ⟨a', List.mem_append_right c.body ha', rfl⟩)

/-- Soundness for single-atom queries: if we can refute `← a`, then
    any grounding of the computed answer produces a model element. -/
theorem SLDTree_sound_single {σ : LPSignature} (kb : KnowledgeBase σ)
    (a : Atom σ) (θ : Subst σ) (h : SLDTree kb.prog [a] θ) (g : Grounding σ) :
    (g.compSubst θ).groundAtom a ∈ leastHerbrandModel kb :=
  SLDTree_sound kb [a] θ h g a (List.mem_cons_self ..)

/-! ## Section 4: Derived properties -/

/-- An SLD refutation with identity substitution means the goals were
    already ground consequences. -/
theorem SLDTree_id_ground {σ : LPSignature} (kb : KnowledgeBase σ)
    (goals : List (Atom σ)) (h : SLDTree kb.prog goals (Subst.id σ)) :
    ∀ g : Grounding σ, ∀ a ∈ goals,
      g.groundAtom a ∈ leastHerbrandModel kb := by
  intro g a ha
  have := SLDTree_sound kb goals (Subst.id σ) h g a ha
  simpa [Grounding.groundAtom_compSubst_id] using this

/-- SLD refutation of empty goals is trivially constructible. -/
theorem SLDTree_nil {σ : LPSignature} (prog : Program σ) :
    SLDTree prog [] (Subst.id σ) :=
  SLDTree.nil

/-- If we can refute `← body` and the clause `head :- body` is in the program,
    then we can construct a refutation involving the head. -/
theorem SLDTree_clause {σ : LPSignature} (prog : Program σ)
    (c : Clause σ) (hc : c ∈ prog) (θ θ' : Subst σ)
    (_hunif : θ.applyAtom c.head = θ.applyAtom c.head)
    (hbody : SLDTree prog (θ.applyAtoms (c.body ++ [])) θ') :
    SLDTree prog [c.head] (θ' ∘ₛ θ) := by
  exact SLDTree.cons c.head [] c θ θ' hc (by rfl) (by simpa using hbody)

/-! ## Section 5: Standardized-apart SLD

The repair of the freshening gap.  Ground terms and atoms mention no
variables, so a scoped ground atom reindexes to a base ground atom by the
structural identity `unscope`; soundness of the scoped judgment then lands in
the *same* least Herbrand model as the base judgment. -/

/-- Reindex a scoped ground term to the base signature.  Structurally the
identity: ground terms mention no variables. -/
def GroundTerm.unscope {σ : LPSignature} : GroundTerm σ.scoped → GroundTerm σ
  | .const c => .const c
  | .app f ts => .app f (fun i => (ts i).unscope)

/-- Reindex a scoped ground atom to the base signature. -/
def GroundAtom.unscope {σ : LPSignature} (a : GroundAtom σ.scoped) :
    GroundAtom σ where
  symbol := a.symbol
  args := fun i => (a.args i).unscope

/-- Restrict a scoped grounding to one activation scope, as a base
grounding of that activation's clause variables. -/
def Grounding.baseAt {σ : LPSignature} (scope : Nat)
    (g : Grounding σ.scoped) : Grounding σ :=
  fun v => (g ⟨scope, v⟩).unscope

/-- Grounding a scoped copy of a term is grounding the term by the
scope-restricted base grounding. -/
theorem Grounding.unscope_groundTerm_atScope {σ : LPSignature}
    (g : Grounding σ.scoped) (scope : Nat) (t : Term σ) :
    (g.groundTerm (t.atScope scope)).unscope =
      (g.baseAt scope).groundTerm t := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app f ts ih =>
      simp only [Term.atScope, Term.renameVars, Grounding.groundTerm,
        GroundTerm.unscope]
      congr 1
      funext i
      exact ih i

/-- Grounding a scoped copy of an atom is grounding the atom by the
scope-restricted base grounding. -/
theorem Grounding.unscope_groundAtom_atScope {σ : LPSignature}
    (g : Grounding σ.scoped) (scope : Nat) (a : Atom σ) :
    (g.groundAtom (a.atScope scope)).unscope =
      (g.baseAt scope).groundAtom a := by
  show GroundAtom.mk _ _ = GroundAtom.mk _ _
  congr 1
  funext i
  exact g.unscope_groundTerm_atScope scope (a.args i)

/-- Standardized-apart SLD refutation (big-step, leftmost selection).

`SLDScopedTree prog scope goals θ` derives the scoped goal list `goals` with
computed answer `θ`, where every clause activation happens at an explicit
scope and scopes strictly increase along the derivation.  A caller whose
query variables live at scopes below the starting scope therefore gets
structural standardization apart: no activation can collide with the query or
with any other activation, by the type of `ScopedVar` alone.  This mirrors
the runtime's `nextScope` discipline exactly, including scope gaps. -/
inductive SLDScopedTree {σ : LPSignature} (prog : Program σ) :
    Nat → List (Atom σ.scoped) → Subst σ.scoped → Prop where
  /-- Empty goal list: refutation found with the identity answer. -/
  | nil (scope : Nat) : SLDScopedTree prog scope [] (Subst.id σ.scoped)
  /-- Resolve the leftmost goal against the `scope`-renamed copy of a program
  clause; continue at any strictly larger scope. -/
  | cons (scope next : Nat) (a : Atom σ.scoped) (goals : List (Atom σ.scoped))
      (c : Clause σ) (θ θ' : Subst σ.scoped)
      (hfresh : scope < next)
      (hc : c ∈ prog)
      (hunif : θ.applyAtom a = θ.applyAtom (c.head.atScope scope))
      (hrest : SLDScopedTree prog next
        (θ.applyAtoms ((c.body.map (Atom.atScope scope)) ++ goals)) θ') :
      SLDScopedTree prog scope (a :: goals) (θ' ∘ₛ θ)

/-- **Soundness of standardized-apart SLD**: a scoped refutation grounds
every goal, via `unscope`, into the least Herbrand model of the base
knowledge base.  Freshness is not needed for soundness — it is carried for
completeness and for runtime refinement — so no hypothesis beyond the
derivation itself is required. -/
theorem SLDScopedTree_sound {σ : LPSignature} (kb : KnowledgeBase σ)
    (scope : Nat) (goals : List (Atom σ.scoped)) (θ : Subst σ.scoped)
    (h : SLDScopedTree kb.prog scope goals θ) :
    ∀ g : Grounding σ.scoped, ∀ a ∈ goals,
      ((g.compSubst θ).groundAtom a).unscope ∈ leastHerbrandModel kb := by
  induction h with
  | nil => intro _ _ ha; simp at ha
  | cons scope next a goals c θ θ' hfresh hc hunif _ ih =>
      intro g a' ha'
      simp only [List.mem_cons] at ha'
      rw [ground_comp_eq]
      rcases ha' with rfl | ha'
      · -- Selected atom: transport along the unifier, then along `atScope`,
        -- and close with the clause rule of the least model.
        rw [hunif, ← ground_comp_eq, Grounding.unscope_groundAtom_atScope]
        apply leastHerbrandModel_clause kb c hc
        intro b hb
        rw [← Grounding.unscope_groundAtom_atScope, ground_comp_eq]
        exact ih g (θ.applyAtom (b.atScope scope))
          (List.mem_map.mpr ⟨b.atScope scope,
            List.mem_append_left _ (List.mem_map.mpr ⟨b, hb, rfl⟩), rfl⟩)
      · exact ih g (θ.applyAtom a')
          (List.mem_map.mpr ⟨a', List.mem_append_right _ ha', rfl⟩)

/-! ### Freshening witness

`p(a) :- q(X).  q(b).  ?- p(X).` — the query variable and the clause-body
variable share one source name.  `SLDScopedTree` derives the query because
the activation renames the clause copy apart; the unscoped `SLDTree` fails
on exactly this program (the executable counterexample suite keeps that
failure red).  This witness keeps the repair non-vacuous. -/

private inductive FreshC | a | b deriving DecidableEq
private inductive FreshR | p | q deriving DecidableEq

private def freshSig : LPSignature where
  constants := FreshC
  vars := Unit
  relationSymbols := FreshR
  relationArity := fun _ => 1
  functionSymbols := Empty
  functionArity := fun f => nomatch f

private def freshAtom (r : FreshR) (t : Term freshSig) : Atom freshSig where
  symbol := r
  args := fun _ => t

private def freshProg : Program freshSig :=
  [ { head := freshAtom .p (.const .a), body := [freshAtom .q (.var ())] },
    { head := freshAtom .q (.const .b), body := [] } ]

/-- First unifier: send the scope-0 query variable to `a`, leave the scope-1
activation variable alone. -/
private def freshTheta1 : Subst freshSig.scoped :=
  fun v => match v.scope with
    | 0 => .const .a
    | _ + 1 => .var v

/-- Second unifier: send the scope-1 activation variable to `b`. -/
private def freshTheta2 : Subst freshSig.scoped :=
  fun v => match v.scope with
    | 1 => .const .b
    | _ => .var v

example : ∃ θ, SLDScopedTree freshProg 1
    [(freshAtom .p (.var ())).atScope 0] θ := by
  have step2 : SLDScopedTree freshProg 2
      (freshTheta1.applyAtoms
        (([freshAtom .q (.var ())].map (Atom.atScope 1)) ++ []))
      (Subst.id _ ∘ₛ freshTheta2) :=
    .cons 2 3 _ []
      { head := freshAtom .q (.const .b), body := [] }
      freshTheta2 (Subst.id _) (by omega)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) rfl (.nil 3)
  exact ⟨_, .cons 1 2 _ []
    { head := freshAtom .p (.const .a), body := [freshAtom .q (.var ())] }
    freshTheta1 (Subst.id _ ∘ₛ freshTheta2) (by omega)
    (List.mem_cons_self ..) rfl step2⟩

end Mettapedia.Logic.LP
