import Mettapedia.Logic.RuleMulticategory
import Mettapedia.Logic.DerivationGraph.Schedules

/-!
# Kernel certificates as morphisms of the free multicategory

For a kernel presented by a decidable rule-instance interface (`RuleWitness`),
the rule instances are accepted witnesses (`RuleWitness.signature`). This module
identifies the kernel's certificates with closed morphisms of the free cartesian
multicategory on that signature.

* **Trees.** Closed open-derivation terms are in bijection with accepted
  certificate trees of the same conclusion (`RuleWitness.closedEquiv`).
* **Graphs.** A shared derivation graph unfolds node by node into closed terms
  (`RuleWitness.termStep`); unfolding agrees with judgment replay
  (`RuleWitness.unfold_judgments`), so every accepted node denotes a closed
  morphism of its conclusion (`RuleWitness.unfold_root`).
* **Schedules.** The unfolding of every node is independent of the order in
  which independent nodes are checked (`RuleWitness.unfold_permute`).

Sharing is a property of the representation: two graphs whose nodes unfold to
the same term present the same morphism, while their sizes can differ
exponentially (`Logic.ProofSharingBounds`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic

universe u v w x

open RuleSignature CartesianMulticategory DerivationGraph

namespace RuleWitness

variable {J : Type u} {rules : List J → J → Prop} (interface : RuleWitness.{u, v} rules)

/-! ## Trees -/

/-- Erase a closed open-derivation term to a certificate tree. -/
def toDerivation {Γ : Fin 0 → J} : {b : J} → Term interface.signature Γ b → Derivation J interface.W
  | _, .var i => i.elim0
  | b, .node rule children => .node b rule.1 _ (fun p => toDerivation (children p))

variable {interface}

theorem toDerivation_concl {Γ : Fin 0 → J} {b : J} (t : Term interface.signature Γ b) :
    (toDerivation interface t).concl = b := by
  cases t with
  | var i => exact i.elim0
  | node rule children => rfl

theorem toDerivation_valid {Γ : Fin 0 → J} :
    ∀ {b : J} (t : Term interface.signature Γ b), (toDerivation interface t).valid interface = true
  | _, .var i => i.elim0
  | b, .node (premises := premises) rule children => by
      have concls : (List.ofFn fun p => (toDerivation interface (children p)).concl) = premises := by
        conv_rhs => rw [← List.ofFn_get premises]
        congr 1
        funext p
        exact toDerivation_concl (children p)
      show (interface.isInstance rule.1
          (List.ofFn fun p => (toDerivation interface (children p)).concl) b &&
          (List.ofFn fun p => (toDerivation interface (children p)).valid interface).all id) = true
      rw [concls]
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_ofFn, id]
      refine ⟨rule.2, ?_⟩
      rintro _ ⟨p, rfl⟩
      exact toDerivation_valid (children p)

theorem toDerivation_cast {Γ : Fin 0 → J} {b b' : J} (same : b = b')
    (t : Term interface.signature Γ b) :
    toDerivation interface (same ▸ t) = toDerivation interface t := by
  subst same
  rfl

/-- A heterogeneous form of injectivity, allowing the conclusion index to vary. -/
theorem toDerivation_heq {Γ : Fin 0 → J} {b : J} (t : Term interface.signature Γ b) :
    ∀ {b' : J} (t' : Term interface.signature Γ b'), b = b' →
      toDerivation interface t = toDerivation interface t' → HEq t t' := by
  induction t with
  | var i => exact i.elim0
  | node rule children ih =>
      intro b' t' same erased
      cases t' with
      | var j => exact j.elim0
      | node rule' children' =>
          subst same
          rename_i premises conclusion premises'
          have parts := Derivation.node.inj erased
          obtain ⟨-, witnesses, lengths, kids⟩ := parts
          have pointwise := (Fin.heq_fun_iff lengths).mp kids
          have lists : premises = premises' := by
            apply List.ext_get lengths
            intro n h₁ h₂
            have := congrArg Derivation.concl (pointwise ⟨n, h₁⟩)
            rwa [toDerivation_concl, toDerivation_concl] at this
          subst lists
          have rules : rule = rule' := Subtype.ext witnesses
          subst rules
          have kidsEq : children = children' := funext fun p =>
            eq_of_heq (ih p (children' p) rfl (pointwise p))
          subst kidsEq
          rfl

/-- **Erasure is injective**: a closed derivation is determined by its
certificate tree. -/
theorem toDerivation_injective {Γ : Fin 0 → J} {b : J} {t t' : Term interface.signature Γ b}
    (same : toDerivation interface t = toDerivation interface t') : t = t' :=
  eq_of_heq (toDerivation_heq t t' rfl same)

variable (interface)

/-- Read an accepted certificate tree as a closed derivation term. -/
def ofDerivation {Γ : Fin 0 → J} :
    (d : Derivation J interface.W) → d.valid interface = true → Term interface.signature Γ d.concl
  | .node c w _ children, valid =>
      have parts : interface.isInstance w (List.ofFn fun i => (children i).concl) c = true ∧
          ∀ i, (children i).valid interface = true := by
        simpa [Derivation.valid, Bool.and_eq_true, List.all_eq_true, List.mem_ofFn] using valid
      .node (premises := List.ofFn fun i => (children i).concl) ⟨w, parts.1⟩
        (fun p => (List.get_ofFn (fun i => (children i).concl) p).symm ▸
          ofDerivation (children (Fin.cast (by simp) p)) (parts.2 _))

variable {interface}

theorem toDerivation_ofDerivation {Γ : Fin 0 → J} :
    ∀ (d : Derivation J interface.W) (valid : d.valid interface = true),
      toDerivation interface (ofDerivation interface (Γ := Γ) d valid) = d
  | .node c w k children, valid => by
      simp only [ofDerivation, toDerivation]
      have lengths : (List.ofFn fun i => (children i).concl).length = k := List.length_ofFn
      congr 1
      apply (Fin.heq_fun_iff lengths).mpr
      intro p
      rw [toDerivation_cast, toDerivation_ofDerivation]
      rfl

variable (interface)

/-- **Closed morphisms are certificate trees.** Closed derivations of a
conclusion in the free multicategory on the kernel's rule instances correspond
exactly to the kernel's accepted certificate trees for that conclusion. -/
def closedEquiv {Γ : Fin 0 → J} (b : J) :
    Term interface.signature Γ b ≃
      {d : Derivation J interface.W // d.valid interface = true ∧ d.concl = b} where
  toFun t := ⟨toDerivation interface t, toDerivation_valid t, toDerivation_concl t⟩
  invFun d := d.2.2 ▸ ofDerivation interface d.1 d.2.1
  left_inv t := by
    apply toDerivation_injective
    rw [toDerivation_cast, toDerivation_ofDerivation]
  right_inv d := by
    apply Subtype.ext
    change toDerivation interface (d.2.2 ▸ ofDerivation interface d.1 d.2.1) = d.1
    rw [toDerivation_cast, toDerivation_ofDerivation]

/-! ## Graphs -/

/-- Children of a node read from a list of sorted terms, without transport. -/
def sigmaChildren {S : RuleSignature.{u, v} J} {n : ℕ} {Γ : Fin n → J} :
    (l : List (Σ b, Term S Γ b)) → (p : Fin (l.map Sigma.fst).length) →
      Term S Γ ((l.map Sigma.fst).get p)
  | [], p => p.elim0
  | x :: _, ⟨0, _⟩ => x.2
  | _ :: rest, ⟨k + 1, h⟩ => sigmaChildren rest ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- The unfolding step: a node checked against the sorts of its premise terms
becomes the corresponding rule node. -/
def termStep {Origin : Type w} {n : ℕ} {Γ : Fin n → J} (node : Node J interface.W Origin)
    (premises : List (Σ b, Term interface.signature Γ b)) :
    Option (Σ b, Term interface.signature Γ b) :=
  if h : interface.isInstance node.witness (premises.map Sigma.fst) node.conclusion = true then
    some ⟨node.conclusion, .node ⟨node.witness, h⟩ (sigmaChildren premises)⟩
  else none

theorem lookupPremises_map {α : Type x} {β : Type w} (f : α → β) (cache : Array α) :
    ∀ indices : List Nat,
      lookupPremises (cache.map f) indices = (lookupPremises cache indices).map (List.map f)
  | [] => rfl
  | index :: rest => by
      simp only [lookupPremises, Array.getElem?_map]
      cases cache[index]? with
      | none => rfl
      | some value =>
          simp only [Option.map_some]
          rw [lookupPremises_map f cache rest]
          cases lookupPremises cache rest <;> rfl

/-- **Unfolding agrees with checking.** Replaying a graph with the unfolding step
produces exactly the judgments of ordinary replay, now with their closed
derivations. -/
theorem unfold_judgments {Origin : Type w} {n : ℕ} {Γ : Fin n → J}
    (cache : Array (Σ b, Term interface.signature Γ b)) (nodes : List (Node J interface.W Origin)) :
    (replayWith (termStep interface) cache nodes).map (Array.map Sigma.fst) =
      replayFrom interface (cache.map Sigma.fst) nodes := by
  rw [← replayWith_judgmentStep]
  induction nodes generalizing cache with
  | nil => rfl
  | cons node rest ih =>
      simp only [replayWith]
      rw [lookupPremises_map]
      cases lookupPremises cache node.parents with
      | none => rfl
      | some premises =>
          simp only [Option.map_some, termStep, judgmentStep]
          by_cases accepted :
              interface.isInstance node.witness (premises.map Sigma.fst) node.conclusion = true
          · simp only [accepted, dif_pos, if_true]
            rw [ih]
            simp [Array.map_push]
          · simp [accepted]

/-- **Every accepted node denotes a closed morphism.** If a graph replays, the
unfolding replay succeeds as well, and its value at each position is a closed
derivation of the replayed judgment there. -/
theorem unfold_root {Origin : Type w} {nodes : List (Node J interface.W Origin)} {cache : Array J}
    (accepted : replay interface nodes = some cache) :
    ∃ terms : Array (Σ b, Term interface.signature closedContext b),
      replayWith (termStep interface) #[] nodes = some terms ∧ terms.map Sigma.fst = cache := by
  have projected := unfold_judgments interface (Γ := closedContext) #[] nodes
  simp only [Array.map_empty] at projected
  unfold replay at accepted
  rw [accepted] at projected
  cases unfolded : replayWith (termStep interface) (#[] : Array (Σ b, Term interface.signature
      closedContext b)) nodes with
  | none => rw [unfolded] at projected; cases projected
  | some terms =>
      rw [unfolded] at projected
      exact ⟨terms, rfl, Option.some.inj projected⟩

/-- The unfolding step does not read physical reference positions. -/
theorem termStep_relocate {Origin : Type w} {n : ℕ} {Γ : Fin n → J}
    (node : Node J interface.W Origin) (address : Nat → Nat) :
    termStep interface (Γ := Γ) (node.relocate address) = termStep interface node := rfl

/-- **Unfolding is schedule independent.** Every node of a reordered graph
unfolds to the same closed derivation as in the original order. -/
theorem unfold_permute {Origin : Type w} {n : ℕ} {Γ : Fin n → J}
    (nodes : List (Node J interface.W Origin)) (π : Equiv.Perm (Fin nodes.length))
    (respects : Respects nodes π) {terms : Array (Σ b, Term interface.signature Γ b)}
    (unfolded : replayWith (termStep interface) #[] nodes = some terms) :
    ∃ terms', replayWith (termStep interface) #[] (permute nodes π) = some terms' ∧
      ∀ i : Fin nodes.length, terms'[(π i : Nat)]? = terms[(i : Nat)]? :=
  replayWith_permute (termStep interface) (termStep_relocate interface) nodes π respects unfolded

/-- An accepted graph yields an accepted certificate tree at every node. -/
theorem unfold_tree {Origin : Type w} {nodes : List (Node J interface.W Origin)} {cache : Array J}
    (accepted : replay interface nodes = some cache) {index : Nat} {claim : J}
    (found : cache[index]? = some claim) :
    ∃ d : Derivation J interface.W, d.valid interface = true ∧ d.concl = claim := by
  obtain ⟨terms, -, projected⟩ := unfold_root interface accepted
  rw [← projected, Array.getElem?_map] at found
  cases entry : terms[index]? with
  | none => rw [entry] at found; cases found
  | some value =>
      rw [entry] at found
      cases Option.some.inj found
      exact ⟨toDerivation interface value.2, toDerivation_valid value.2, toDerivation_concl value.2⟩

/-! ## Every closed morphism is presented by a graph -/

section Presentation

variable {Γ : Fin 0 → J}

/-- Reading a child through `sigmaChildren` reads the corresponding entry. -/
theorem toDerivation_sigmaChildren :
    ∀ (l : List (Σ b, Term interface.signature Γ b)) (i : Nat) (h : i < (l.map Sigma.fst).length),
      toDerivation interface (sigmaChildren l ⟨i, h⟩) =
        toDerivation interface (l.get ⟨i, by simpa using h⟩).2
  | [], i, h => by simp at h
  | x :: rest, 0, _ => rfl
  | x :: rest, i + 1, h => toDerivation_sigmaChildren rest i (Nat.lt_of_succ_lt_succ h)

theorem map_fst_ofFn {premises : List J}
    (children : (p : Fin premises.length) → Term interface.signature Γ (premises.get p)) :
    (List.ofFn fun p => (⟨premises.get p, children p⟩ : Σ b, Term interface.signature Γ b)).map
      Sigma.fst = premises := by
  rw [List.map_ofFn]
  exact List.ofFn_get premises

/-- The unfolding step rebuilds a node from the entries of its children. -/
theorem termStep_node_eq {premises : List J} {b : J} (rule : interface.signature premises b)
    (children : (p : Fin premises.length) → Term interface.signature Γ (premises.get p))
    (accepted : interface.isInstance rule.1
      ((List.ofFn fun p => (⟨premises.get p, children p⟩ : Σ c, Term interface.signature Γ c)).map
        Sigma.fst) b = true) :
    Term.node (S := interface.signature) ⟨rule.1, accepted⟩
        (sigmaChildren (List.ofFn fun p => (⟨premises.get p, children p⟩ : Σ c, Term interface.signature Γ c))) =
      Term.node rule children := by
  apply toDerivation_injective
  simp only [toDerivation]
  have lengths : ((List.ofFn fun p => (⟨premises.get p, children p⟩ :
      Σ c, Term interface.signature Γ c)).map Sigma.fst).length = premises.length := by simp
  congr 1
  apply (Fin.heq_fun_iff lengths).mpr
  intro i
  rw [toDerivation_sigmaChildren]
  simp only [List.get_eq_getElem]
  rw [List.getElem_ofFn]

/-- A block of presented entries is presented by one graph, with their positions. -/
theorem presented_block :
    ∀ (entries : List (Σ b, Term interface.signature Γ b)),
      (∀ entry ∈ entries, ∃ (nodes : List (Node J interface.W Unit))
          (terms : Array (Σ b, Term interface.signature Γ b)),
          replayWith (termStep interface) #[] nodes = some terms ∧ terms.back? = some entry) →
        ∃ (nodes : List (Node J interface.W Unit)) (terms : Array (Σ b, Term interface.signature Γ b))
          (positions : List Nat),
          replayWith (termStep interface) #[] nodes = some terms ∧
            lookupPremises terms positions = some entries
  | [], _ => ⟨[], #[], [], rfl, rfl⟩
  | entry :: rest, presented => by
      obtain ⟨first, firstTerms, firstReplay, firstBack⟩ := presented entry List.mem_cons_self
      obtain ⟨later, laterTerms, positions, laterReplay, laterFound⟩ :=
        presented_block rest fun other member => presented other (List.mem_cons_of_mem _ member)
      have agreement : LookupAgreement (#[] : Array (Σ b, Term interface.signature Γ b)) firstTerms
          (· + firstTerms.size) := by
        intro index
        simp
      obtain ⟨combined, combinedReplay, combinedAgreement⟩ :=
        replayWith_relocate (termStep interface) (termStep_relocate interface) agreement
          (fun offset => by simp [Nat.add_comm]) laterReplay
      obtain ⟨-, prefixAgree, -⟩ :=
        (replayWith_iff_local (termStep interface) firstTerms _ combined).mp combinedReplay
      have nonempty : 0 < firstTerms.size := by
        cases size : firstTerms.size with
        | zero =>
            have : firstTerms = #[] := Array.eq_empty_of_size_eq_zero size
            subst this
            simp at firstBack
        | succ n => omega
      refine ⟨first ++ later.map (Node.relocate (· + firstTerms.size)), combined,
        (firstTerms.size - 1) :: positions.map (· + firstTerms.size), ?_, ?_⟩
      · rw [replayWith_append, firstReplay]
        exact combinedReplay
      · simp only [lookupPremises]
        have head : combined[firstTerms.size - 1]? = some entry := by
          rw [prefixAgree _ (by omega), ← Array.back?_eq_getElem?]
          exact firstBack
        rw [head, lookupPremises_relocate combinedAgreement, laterFound]
        rfl

/-- **Every closed morphism is the unfolding of an accepted graph.** Together
with `unfold_root`, accepted graphs present exactly the closed morphisms of the
free multicategory; sharing changes only the representation. -/
theorem presented {b : J} (t : Term interface.signature Γ b) :
    ∃ (nodes : List (Node J interface.W Unit)) (terms : Array (Σ c, Term interface.signature Γ c)),
      replayWith (termStep interface) #[] nodes = some terms ∧ terms.back? = some ⟨b, t⟩ := by
  induction t with
  | var i => exact i.elim0
  | @node premises conclusion rule children ih =>
      let entries : List (Σ c, Term interface.signature Γ c) :=
        List.ofFn fun p => ⟨premises.get p, children p⟩
      obtain ⟨nodes, terms, positions, replayed, found⟩ := presented_block interface entries (by
        intro entry member
        obtain ⟨p, rfl⟩ := List.mem_ofFn.mp member
        exact ih p)
      have accepted : interface.isInstance rule.1 (entries.map Sigma.fst) conclusion = true := by
        rw [map_fst_ofFn interface children]
        exact rule.2
      refine ⟨nodes ++ [⟨conclusion, rule.1, positions, ()⟩],
        terms.push ⟨conclusion, Term.node ⟨rule.1, accepted⟩ (sigmaChildren entries)⟩, ?_, ?_⟩
      · rw [replayWith_append, replayed]
        simp only [Option.bind_some, replayWith, found, termStep, accepted, dif_pos]
      · rw [Array.back?_push]
        congr 2
        exact termStep_node_eq interface rule children accepted

end Presentation

/-! ## Translating shared graphs node by node -/

section SharedTranslation

universe u' v'

variable {J' : Type u'} {S' : RuleSignature.{u', v'} J'} {f : J → J'}
  (φ : Interpretation interface.signature (free S') f)

/-- Children read from translated entries indexed by their source sorts. -/
def sigmaChildrenOver {n : ℕ} {Δ : Fin n → J'} :
    (l : List (Σ b : J, Term S' Δ (f b))) → (p : Fin (l.map Sigma.fst).length) →
      Term S' Δ (f ((l.map Sigma.fst).get p))
  | [], p => p.elim0
  | x :: _, ⟨0, _⟩ => x.2
  | _ :: rest, ⟨k + 1, h⟩ => sigmaChildrenOver rest ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- The node-by-node translation step: check the node against its source premise
sorts, then instantiate the rule image with the translated premises. A shared
graph is translated with one rule image per node, never per tree occurrence. -/
def liftStep {Origin : Type w} {n : ℕ} {Δ : Fin n → J'} (node : Node J interface.W Origin)
    (premises : List (Σ b : J, Term S' Δ (f b))) : Option (Σ b : J, Term S' Δ (f b)) :=
  if h : interface.isInstance node.witness (premises.map Sigma.fst) node.conclusion = true then
    some ⟨node.conclusion, (φ _ _ ⟨node.witness, h⟩).subst (sigmaChildrenOver premises)⟩
  else none

/-- A translated entry: the multifunctor image of a source entry. -/
def liftEntry {n : ℕ} {Γ : Fin n → J} (entry : Σ b, Term interface.signature Γ b) :
    Σ b : J, Term S' (f ∘ Γ) (f b) :=
  ⟨entry.1, entry.2.lift φ⟩

theorem map_liftEntry_fst {n : ℕ} {Γ : Fin n → J} (premises : List (Σ b, Term interface.signature Γ b)) :
    (premises.map (liftEntry interface φ)).map Sigma.fst = premises.map Sigma.fst := by
  induction premises with
  | nil => rfl
  | cons x rest ih => simp only [List.map_cons]; rw [ih]; rfl

theorem sigmaChildrenOver_liftEntry_at {n : ℕ} {Γ : Fin n → J} :
    ∀ (premises : List (Σ b, Term interface.signature Γ b)) (i : Nat)
      (h : i < ((premises.map (liftEntry interface φ)).map Sigma.fst).length)
      (h' : i < (premises.map Sigma.fst).length),
      HEq (sigmaChildrenOver (premises.map (liftEntry interface φ)) ⟨i, h⟩)
        ((sigmaChildren premises ⟨i, h'⟩).lift φ)
  | [], _, h, _ => by simp at h
  | x :: rest, 0, _, _ => HEq.rfl
  | x :: rest, i + 1, h, h' =>
      sigmaChildrenOver_liftEntry_at rest i (Nat.lt_of_succ_lt_succ h) (Nat.lt_of_succ_lt_succ h')

theorem sigmaChildrenOver_liftEntry {n : ℕ} {Γ : Fin n → J}
    (premises : List (Σ b, Term interface.signature Γ b)) :
    HEq (sigmaChildrenOver (premises.map (liftEntry interface φ)))
      (fun p : Fin (premises.map Sigma.fst).length => (sigmaChildren premises p).lift φ) := by
  have lengths := map_liftEntry_fst interface φ premises
  apply Function.hfunext (by rw [lengths])
  intro p p' samePosition
  have values : (p : Nat) = (p' : Nat) := (Fin.heq_ext_iff (by rw [lengths])).mp samePosition
  obtain ⟨k, hk⟩ := p
  obtain ⟨k', hk'⟩ := p'
  simp only at values
  subst values
  exact sigmaChildrenOver_liftEntry_at interface φ premises k hk hk'

/-- Instantiating a rule image is invariant under transport of its premise list. -/
theorem image_subst_congr {n : ℕ} {Δ : Fin n → J'} {L L' : List J} (same : L' = L) {c : J}
    (w : interface.W) (accepted' : interface.isInstance w L' c = true)
    (accepted : interface.isInstance w L c = true)
    (children' : (p : Fin L'.length) → Term S' Δ (f (L'.get p)))
    (children : (p : Fin L.length) → Term S' Δ (f (L.get p))) (sameChildren : HEq children' children) :
    (φ L' c ⟨w, accepted'⟩).subst children' = (φ L c ⟨w, accepted⟩).subst children := by
  subst same
  cases sameChildren
  rfl

/-- **One node.** Translating a node from translated premises gives the
multifunctor image of the node's unfolding. -/
theorem liftStep_liftEntry {Origin : Type w} {n : ℕ} {Γ : Fin n → J} (node : Node J interface.W Origin)
    (premises : List (Σ b, Term interface.signature Γ b)) :
    liftStep interface φ node (premises.map (liftEntry interface φ)) =
      (termStep interface node premises).map (liftEntry interface φ) := by
  have lists := map_liftEntry_fst interface φ premises
  unfold liftStep termStep
  by_cases accepted : interface.isInstance node.witness (premises.map Sigma.fst) node.conclusion = true
  · have accepted' : interface.isInstance node.witness ((premises.map (liftEntry interface φ)).map Sigma.fst)
        node.conclusion = true := by rw [lists]; exact accepted
    rw [dif_pos accepted', dif_pos accepted]
    simp only [Option.map_some, liftEntry, Option.some.injEq]
    congr 1
    exact image_subst_congr interface φ lists node.witness accepted' accepted _ _
      (sigmaChildrenOver_liftEntry interface φ premises)
  · have refused' : ¬ interface.isInstance node.witness ((premises.map (liftEntry interface φ)).map Sigma.fst)
        node.conclusion = true := by rw [lists]; exact accepted
    rw [dif_neg refused', dif_neg accepted]
    rfl

/-- **SHARE commutes with translation.** Replaying a graph with the node-by-node
translation step from translated entries yields exactly the multifunctor images
of the unfolding. -/
theorem replay_liftStep {Origin : Type w} {n : ℕ} {Γ : Fin n → J}
    (cache : Array (Σ b, Term interface.signature Γ b)) (nodes : List (Node J interface.W Origin)) :
    replayWith (liftStep interface φ) (cache.map (liftEntry interface φ)) nodes =
      (replayWith (termStep interface) cache nodes).map (Array.map (liftEntry interface φ)) := by
  induction nodes generalizing cache with
  | nil => rfl
  | cons node rest ih =>
      simp only [replayWith]
      rw [lookupPremises_map]
      cases lookupPremises cache node.parents with
      | none => rfl
      | some premises =>
          simp only [Option.map_some]
          rw [liftStep_liftEntry]
          cases termStep interface node premises with
          | none => rfl
          | some value =>
              simp only [Option.map_some]
              rw [← Array.map_push]
              exact ih _

/-- For an accepted graph, the node-by-node translation succeeds and its value at
every node is the multifunctor image of that node's closed derivation. -/
theorem shared_translation {Origin : Type w} {nodes : List (Node J interface.W Origin)} {cache : Array J}
    (accepted : replay interface nodes = some cache) :
    ∃ terms : Array (Σ b, Term interface.signature closedContext b),
      replayWith (termStep interface) #[] nodes = some terms ∧ terms.map Sigma.fst = cache ∧
      replayWith (liftStep interface φ) #[] nodes = some (terms.map (liftEntry interface φ)) := by
  obtain ⟨terms, unfolded, projected⟩ := unfold_root interface accepted
  refine ⟨terms, unfolded, projected, ?_⟩
  have := replay_liftStep interface φ (#[] : Array (Σ b, Term interface.signature closedContext b)) nodes
  simp only [Array.map_empty] at this
  rw [this, unfolded]
  rfl

end SharedTranslation

end RuleWitness

end Mettapedia.Logic
