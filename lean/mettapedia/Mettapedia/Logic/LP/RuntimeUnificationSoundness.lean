import Mettapedia.Logic.LP.RuntimeUnifierSoundness
import Mettapedia.Logic.LP.RuntimeMaterializeSoundness
import Mettapedia.Logic.LP.Substitution
import Mettapedia.Logic.LP.SLD

/-!
# Toward success soundness of the runtime graph unifier

The unification machine has executable behavior but no semantic theorem:
nothing yet says that reaching `.success` makes a unified pair denote the same
term.  This module builds the semantic layer for that theorem on the
function-free fragment (no `app` cells).  Scope, stated honestly: this covers
the current regression *fixtures*, not the runtime — `RuntimeQuery`
materializes and unifies compound cells, whose treatment needs structural
graph correspondence (a later milestone), and rational (cyclic) structures are
excluded by the `.ok`-conditional statements rather than handled.  These are
implementation-refinement lemmas about the canonical representation; they are
not, by themselves, semantic grounding against an SLD judgment.

Design, chosen to avoid fighting the fixed readback budget:

* equalities are carried as **root convergence at some explicit fuel**
  (`ConvergedAt`), which is budget-free and survives later bindings;
* machine writes only overwrite an *unbound* variable cell — a dereference
  terminal — and never change heap size, so every other cell (including every
  `const` root) is immutable along a unification run;
* readback is connected to convergence by `readTermFuel_of_root`, and final
  `Heap.readTerm` statements follow by fuel monotonicity alone.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeUnificationSoundness

open RuntimeTerm RuntimeUnification RuntimeReadback RuntimeMaterialize

/-! ## Stage 2: the canonical answer substitution

The refinement theorem's substitution is not chosen — it is *read off the
answer heap*.  Under identity-injectivity (at most one cell per variable
identity, a consequence of the scope discipline) the denoted substitution is
well-defined and idempotent, which is what lets the SLD judgment's answer
compositions telescope to it. -/


attribute [local instance] Classical.propDecidable

/-- The cell carrying one variable identity, when it exists. -/
noncomputable def cellOf {σ : LPSignature} (heap : Heap σ) (v : σ.vars) :
    Option Addr :=
  if h : ∃ a : Addr, ∃ link, heap[a]? = some (Cell.var v link) then
    some h.choose
  else none

/-- Every listed variable has a cell with *finite* readback.  This is the
interface guard for `heapSubst`: outside a readable support, its fallback
below silently treats a variable as unbound, which would misrepresent a
rational (cyclic) binding as freedom.  Theorems must either hypothesize
readability of every relevant variable or discharge it (the function-free
fragment proves it outright). -/
def ReadableOn {σ : LPSignature} (heap : Heap σ) (support : List σ.vars) :
    Prop :=
  ∀ v ∈ support, ∃ address term,
    cellOf heap v = some address ∧
    Heap.readTerm heap address = .ok term

/-- The **finite heap projection**: each identity reads back its cell;
identities without a cell, or whose cell has no finite readback (a rational
cycle), fall back to themselves.  On a `ReadableOn` support — automatic in
the function-free fragment — this is the canonical answer substitution; the
fallback is never semantically meaningful and consumers must not rely on
it. -/
noncomputable def heapSubst {σ : LPSignature} (heap : Heap σ) : Subst σ :=
  fun v =>
    match cellOf heap v with
    | none => .var v
    | some address =>
        match Heap.readTerm heap address with
        | .ok term => term
        | .error _ => .var v

/-- List companion for `readTermFuel_freeVar_unbound`. -/
theorem readListFuel_freeVar_unbound {σ : LPSignature} [DecidableEq σ.vars]
    {heap : Heap σ} {fuel : Nat}
    (termCase : ∀ address term, readTermFuel heap fuel address = .ok term →
      ∀ w ∈ term.freeVars, ∃ b : Addr, heap[b]? = some (Cell.var w none)) :
    ∀ (addresses : List Addr) (terms : List (Term σ)),
      readListFuel heap fuel addresses = .ok terms →
      ∀ c ∈ terms, ∀ w ∈ c.freeVars,
        ∃ b : Addr, heap[b]? = some (Cell.var w none) := by
  intro addresses
  induction addresses with
  | nil =>
      intro terms h c hc _ _
      have : ([] : List (Term σ)) = terms := by simpa [readListFuel] using h
      subst this
      simp at hc
  | cons head tailA tailIh =>
      intro terms h c hc w hw
      simp only [readListFuel, Bind.bind, Except.bind] at h
      cases hHead : readTermFuel heap fuel head with
      | error e => rw [hHead] at h; simp at h
      | ok headTerm =>
          rw [hHead] at h
          cases hTail : readListFuel heap fuel tailA with
          | error e => rw [hTail] at h; simp at h
          | ok tailTerms =>
              rw [hTail] at h
              have : headTerm :: tailTerms = terms := by simpa using h
              subst this
              rcases List.mem_cons.mp hc with rfl | hc'
              · exact termCase head c hHead w hw
              · exact tailIh tailTerms hTail c hc' w hw

/-- Every free variable of a finite readback names an *unbound* cell. -/
theorem readTermFuel_freeVar_unbound {σ : LPSignature}
    [DecidableEq σ.vars] (heap : Heap σ) :
    ∀ (fuel : Nat) (address : Addr) (term : Term σ),
      readTermFuel heap fuel address = .ok term →
      ∀ w ∈ term.freeVars, ∃ b : Addr, heap[b]? = some (Cell.var w none) := by
  intro fuel
  induction fuel with
  | zero => intro address term h; simp [readTermFuel] at h
  | succ fuel ih =>
      intro address term h w hw
      cases hcell : heap[address]? with
      | none =>
          rw [readTermFuel_invalid heap fuel address hcell] at h
          exact absurd h (by simp)
      | some cell =>
          cases cell with
          | var identity link =>
              cases link with
              | none =>
                  rw [readTermFuel_unbound heap fuel address identity hcell] at h
                  have : Term.var identity = term := by simpa using h
                  subst this
                  have : w = identity := by
                    simpa [Term.freeVars] using hw
                  subst this
                  exact ⟨address, hcell⟩
              | some target =>
                  rw [readTermFuel_link heap fuel address target identity
                    hcell] at h
                  exact ih target term h w hw
          | const symbol =>
              rw [readTermFuel_const heap fuel address symbol hcell] at h
              have : Term.const symbol = term := by simpa using h
              subst this
              simp [Term.freeVars] at hw
          | app symbol args =>
              rw [readTermFuel_app heap fuel address symbol args hcell] at h
              simp only [Bind.bind, Except.bind] at h
              cases hArgs : readListFuel heap fuel args.toList with
              | error e => rw [hArgs] at h; simp at h
              | ok children =>
                  simp only [hArgs] at h
                  by_cases hLength :
                      children.length = σ.functionArity symbol
                  case neg =>
                    rw [dif_neg hLength] at h
                    exact absurd h (by simp)
                  case pos =>
                    rw [dif_pos hLength] at h
                    have hterm :
                        Term.app symbol (fun index =>
                          children.get (Fin.cast hLength.symm index)) =
                          term := by
                      simpa using h
                    subst hterm
                    simp only [Term.freeVars, Finset.mem_biUnion,
                      Finset.mem_univ, true_and] at hw
                    obtain ⟨i, hi⟩ := hw
                    exact readListFuel_freeVar_unbound
                      (fun a t ht => ih a t ht) args.toList children hArgs
                      _ (children.get_mem _) w hi

/-- Under injectivity, `cellOf` finds exactly the unbound cell. -/
theorem cellOf_unbound {σ : LPSignature} {heap : Heap σ}
    (inj : IdentityInjective heap) {b : Addr} {w : σ.vars}
    (hb : heap[b]? = some (Cell.var w none)) :
    cellOf heap w = some b := by
  unfold cellOf
  have hex : ∃ a : Addr, ∃ link, heap[a]? = some (Cell.var w link) :=
    ⟨b, none, hb⟩
  rw [dif_pos hex]
  obtain ⟨link, hl⟩ := hex.choose_spec
  exact congrArg some (inj _ b w link none hl hb)

/-- An unbound identity denotes itself. -/
theorem heapSubst_unbound {σ : LPSignature} {heap : Heap σ}
    (inj : IdentityInjective heap) {b : Addr} {w : σ.vars}
    (hb : heap[b]? = some (Cell.var w none)) :
    heapSubst heap w = .var w := by
  have hread : Heap.readTerm heap b = .ok (Term.var w) :=
    readTermFuel_unbound heap heap.size b w hb
  simp [heapSubst, cellOf_unbound inj hb, hread]

/-- A substitution fixing every free variable fixes the term. -/
theorem applyTerm_eq_self_of_freeVars {σ : LPSignature} [DecidableEq σ.vars]
    {θ : Subst σ} :
    ∀ {t : Term σ}, (∀ w ∈ t.freeVars, θ w = .var w) →
      θ.applyTerm t = t := by
  intro t
  induction t with
  | var v =>
      intro h
      simpa [Subst.applyTerm] using h v (by simp [Term.freeVars])
  | const c => intro _; rfl
  | app f ts ih =>
      intro h
      simp only [Subst.applyTerm]
      congr 1
      funext i
      exact ih i (fun w hw => h w (by
        simp only [Term.freeVars, Finset.mem_biUnion, Finset.mem_univ,
          true_and]
        exact ⟨i, hw⟩))

/-- Pointwise idempotence of the denoted substitution. -/
theorem heapSubst_applyTerm_self {σ : LPSignature} [DecidableEq σ.vars]
    {heap : Heap σ} (inj : IdentityInjective heap) (v : σ.vars) :
    (heapSubst heap).applyTerm (heapSubst heap v) = heapSubst heap v := by
  have hval : heapSubst heap v = .var v ∨
      ∃ a t, Heap.readTerm heap a = .ok t ∧ heapSubst heap v = t := by
    cases hc : cellOf heap v with
    | none => exact .inl (by simp [heapSubst, hc])
    | some a =>
        cases hr : Heap.readTerm heap a with
        | ok term => exact .inr ⟨a, term, hr, by simp [heapSubst, hc, hr]⟩
        | error e => exact .inl (by simp [heapSubst, hc, hr])
  rcases hval with h | ⟨a, t, hrt, h⟩
  · rw [h]
    simp only [Subst.applyTerm]
    exact h
  · rw [h]
    apply applyTerm_eq_self_of_freeVars
    intro w hw
    obtain ⟨b, hb⟩ :=
      readTermFuel_freeVar_unbound heap (heap.size + 1) a t hrt w hw
    exact heapSubst_unbound inj hb

/-- **Idempotence**: the denoted substitution absorbs itself under
composition — the law that lets SLD answer compositions telescope. -/
theorem heapSubst_idem {σ : LPSignature} [DecidableEq σ.vars]
    {heap : Heap σ} (inj : IdentityInjective heap) :
    heapSubst heap ∘ₛ heapSubst heap = heapSubst heap := by
  funext v
  simpa [Subst.comp] using heapSubst_applyTerm_self inj v

/-! ## The keystone endpoint, pinned

The exact statement stages S4–S6 must produce — written down now so the arc
has one fixed consumer and cannot drift.  `Prop`-level only; proving it *is*
the remaining work, and immediately afterwards it must be composed with
`SLDScopedTree_sound` into one named least-model theorem. -/

/-- Static, cut-free execution of a materialized query yields only answers
that the standardized-apart SLD judgment derives, with the yielded bindings
agreeing with the derivation's substitution. -/
def RefinementEndpoint (σ : LPSignature) [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols] : Prop :=
  ∀ (builtins : RuntimeQuery.Builtins σ)
    (program : Program σ) (goals : List (Atom σ))
    (state : RuntimeQuery.State σ) (fuel : Nat)
    (answer : RuntimeQuery.Answer σ) (resumed : RuntimeQuery.State σ),
    (∀ symbol, builtins.isCut symbol = false) →
    RuntimeQuery.openQuery (Memory.empty σ.scoped) 0 1 goals = .ok state →
    RuntimeQuery.pull builtins program fuel state = .answer answer resumed →
    ∃ θ : Subst σ.scoped,
      SLDScopedTree program 1 (queryAtScope 0 goals) θ ∧
      ∀ pair ∈ answer.queryVarMap, ∀ term,
        Heap.readTerm answer.memory.heap pair.2 = .ok term →
        θ pair.1 = term

/-! ## Stage 4: readback naturality

Between two snapshots of one run segment, cells change in exactly one way:
an unbound variable acquires a binding.  `BindingExtension` captures that,
and `readback_naturality` proves the payoff: the later readback of any
address is the finite heap projection applied to its earlier readback.
This is the bridge that lets one substitution — read off the final memory —
justify every resolution step of a derivation. -/


/-- Interior chain links (bound variables) are always preserved. -/
theorem BindingExtension.link_preserved {σ : LPSignature}
    {heap₀ heap₁ : Heap σ} (ext : BindingExtension heap₀ heap₁)
    {a target : Addr} {identity : σ.vars}
    (h : heap₀[a]? = some (Cell.var identity (some target))) :
    heap₁[a]? = some (Cell.var identity (some target)) := by
  rcases ext.2 a _ h with hsame | ⟨_, _, habs, _⟩
  · exact hsame
  · cases habs

/-- Constant cells are always preserved. -/
theorem BindingExtension.const_preserved {σ : LPSignature}
    {heap₀ heap₁ : Heap σ} (ext : BindingExtension heap₀ heap₁)
    {a : Addr} {symbol : σ.constants}
    (h : heap₀[a]? = some (Cell.const symbol)) :
    heap₁[a]? = some (Cell.const symbol) := by
  rcases ext.2 a _ h with hsame | ⟨_, _, habs, _⟩
  · exact hsame
  · cases habs

/-- Application cells are always preserved.  A binding extension may only
replace an unbound variable cell by a link; compound structure is immutable. -/
theorem BindingExtension.app_preserved {σ : LPSignature}
    {heap₀ heap₁ : Heap σ} (ext : BindingExtension heap₀ heap₁)
    {a : Addr} {symbol : σ.functionSymbols} {args : Array Addr}
    (h : heap₀[a]? = some (Cell.app symbol args)) :
    heap₁[a]? = some (Cell.app symbol args) := by
  rcases ext.2 a _ h with hsame | ⟨_, _, habs, _⟩
  · exact hsame
  · cases habs

/-- Function-freeness transfers backwards along a binding extension. -/
theorem BindingExtension.ff_back {σ : LPSignature}
    {heap₀ heap₁ : Heap σ} (ext : BindingExtension heap₀ heap₁)
    (ff : FunctionFree heap₁) : FunctionFree heap₀ := by
  intro a symbol args h
  rcases ext.2 a _ h with hsame | ⟨_, _, habs, _⟩
  · exact ff a symbol args hsame
  · cases habs

/-- Generalized `cellOf` characterization: any cell carrying the identity is
the cell `cellOf` finds, bound or not. -/
theorem cellOf_of_cell {σ : LPSignature} {heap : Heap σ}
    (inj : IdentityInjective heap) {b : Addr} {w : σ.vars}
    {link : Option Addr}
    (hb : heap[b]? = some (Cell.var w link)) :
    cellOf heap w = some b := by
  unfold cellOf
  have hex : ∃ a : Addr, ∃ l, heap[a]? = some (Cell.var w l) :=
    ⟨b, link, hb⟩
  rw [dif_pos hex]
  obtain ⟨l', hl'⟩ := hex.choose_spec
  exact congrArg some (inj _ b w l' link hl' hb)

/-- Local inversion used by finite readback naturality. -/
private theorem readListFuel_ok_pointwise_naturality {σ : LPSignature}
    {heap : Heap σ} {fuel : Nat} :
    ∀ {addresses : List Addr} {terms : List (Term σ)},
      readListFuel heap fuel addresses = .ok terms →
      addresses.length = terms.length ∧
      ∀ k (hk : k < addresses.length) (hk' : k < terms.length),
        readTermFuel heap fuel addresses[k] = .ok terms[k] := by
  intro addresses
  induction addresses with
  | nil =>
      intro terms h
      simp only [readListFuel] at h
      cases h
      exact ⟨rfl, fun k hk _ => absurd hk (Nat.not_lt_zero k)⟩
  | cons head tail ih =>
      intro terms h
      simp only [readListFuel, Bind.bind, Except.bind] at h
      cases hHead : readTermFuel heap fuel head with
      | error e => rw [hHead] at h; cases h
      | ok headTerm =>
          rw [hHead] at h
          cases hTail : readListFuel heap fuel tail with
          | error e => rw [hTail] at h; cases h
          | ok tailTerms =>
              rw [hTail] at h
              cases h
              obtain ⟨hLength, hPoint⟩ := ih hTail
              refine ⟨congrArg (· + 1) hLength, ?_⟩
              intro k hk hk'
              cases k with
              | zero => simpa using hHead
              | succ k =>
                  have := hPoint k (by simpa using hk) (by simpa using hk')
                  simpa using this

/-- Finite readback is natural along a binding extension on arbitrary heaps:
the later finite heap projection, applied to an earlier finite readback, is
the later readback.  Compound nodes recurse through their immutable child
addresses.  Rational cycles remain outside the statement because the later
readback premise must be `.ok`. -/
theorem readTermFuel_naturality_finite {σ : LPSignature}
    [DecidableEq σ.vars] {heap₀ heap₁ : Heap σ}
    (ext : BindingExtension heap₀ heap₁)
    (inj : IdentityInjective heap₁) :
    ∀ (fuel : Nat) (address : Addr) (t₀ : Term σ),
      readTermFuel heap₀ fuel address = .ok t₀ →
      ∀ (t₁ : Term σ), Heap.readTerm heap₁ address = .ok t₁ →
        (heapSubst heap₁).applyTerm t₀ = t₁ := by
  intro fuel
  induction fuel with
  | zero =>
      intro address t₀ h₀
      simp [readTermFuel] at h₀
  | succ fuel ih =>
      intro address t₀ h₀ t₁ h₁
      cases hcell₀ : heap₀[address]? with
      | none =>
          rw [readTermFuel_invalid heap₀ fuel address hcell₀] at h₀
          exact absurd h₀ (by simp)
      | some cell =>
          cases cell with
          | var identity link =>
              cases link with
              | none =>
                  rw [readTermFuel_unbound heap₀ fuel address identity hcell₀]
                    at h₀
                  have ht₀ : Term.var identity = t₀ := by simpa using h₀
                  subst t₀
                  have hcell₁ : ∃ link,
                      heap₁[address]? = some (Cell.var identity link) := by
                    rcases ext.2 address _ hcell₀ with hsame |
                        ⟨identity', target, hshape, hbound⟩
                    · exact ⟨none, hsame⟩
                    · cases hshape
                      exact ⟨some target, hbound⟩
                  obtain ⟨link₁, hcell₁⟩ := hcell₁
                  show heapSubst heap₁ identity = t₁
                  simp [heapSubst, cellOf_of_cell inj hcell₁, h₁]
              | some target =>
                  rw [readTermFuel_link heap₀ fuel address target identity
                    hcell₀] at h₀
                  have hcell₁ := ext.link_preserved hcell₀
                  unfold Heap.readTerm at h₁
                  rw [readTermFuel_link heap₁ heap₁.size address target
                    identity hcell₁] at h₁
                  have htarget : Heap.readTerm heap₁ target = .ok t₁ :=
                    readTermFuel_mono heap₁ heap₁.size target t₁ h₁
                  exact ih target t₀ h₀ t₁ htarget
          | const symbol =>
              rw [readTermFuel_const heap₀ fuel address symbol hcell₀] at h₀
              have ht₀ : Term.const symbol = t₀ := by simpa using h₀
              subst t₀
              have hcell₁ := ext.const_preserved hcell₀
              have ht₁ : Term.const symbol = t₁ := by
                unfold Heap.readTerm at h₁
                rw [readTermFuel_const heap₁ heap₁.size address symbol hcell₁]
                  at h₁
                simpa using h₁
              subst t₁
              rfl
          | app symbol args =>
              rw [readTermFuel_app heap₀ fuel address symbol args hcell₀] at h₀
              simp only [Bind.bind, Except.bind] at h₀
              cases hArgs₀ : readListFuel heap₀ fuel args.toList with
              | error e => rw [hArgs₀] at h₀; simp at h₀
              | ok children₀ =>
                  simp only [hArgs₀] at h₀
                  by_cases hLength₀ :
                      children₀.length = σ.functionArity symbol
                  · rw [dif_pos hLength₀] at h₀
                    have ht₀ : Term.app symbol (fun index =>
                        children₀.get (Fin.cast hLength₀.symm index)) = t₀ := by
                      simpa using h₀
                    subst t₀
                    have hcell₁ := ext.app_preserved hcell₀
                    unfold Heap.readTerm at h₁
                    rw [readTermFuel_app heap₁ heap₁.size address symbol args
                      hcell₁] at h₁
                    simp only [Bind.bind, Except.bind] at h₁
                    cases hArgs₁ :
                        readListFuel heap₁ heap₁.size args.toList with
                    | error e => rw [hArgs₁] at h₁; simp at h₁
                    | ok children₁ =>
                        simp only [hArgs₁] at h₁
                        by_cases hLength₁ :
                            children₁.length = σ.functionArity symbol
                        · rw [dif_pos hLength₁] at h₁
                          have ht₁ : Term.app symbol (fun index =>
                              children₁.get (Fin.cast hLength₁.symm index)) =
                              t₁ := by
                            simpa using h₁
                          subst t₁
                          obtain ⟨hArgsLength₀, hPoint₀⟩ :=
                            readListFuel_ok_pointwise_naturality hArgs₀
                          obtain ⟨hArgsLength₁, hPoint₁⟩ :=
                            readListFuel_ok_pointwise_naturality hArgs₁
                          simp only [Subst.applyTerm]
                          congr 1
                          funext index
                          let k := index.val
                          have hkArgs : k < args.toList.length := by
                            rw [hArgsLength₀, hLength₀]
                            exact index.isLt
                          have hk₀ : k < children₀.length := by
                            rw [hLength₀]
                            exact index.isLt
                          have hk₁ : k < children₁.length := by
                            rw [hLength₁]
                            exact index.isLt
                          have hOld := hPoint₀ k hkArgs hk₀
                          have hLaterSmall := hPoint₁ k hkArgs hk₁
                          have hLater : Heap.readTerm heap₁ args.toList[k] =
                              .ok children₁[k] :=
                            readTermFuel_mono heap₁ heap₁.size _ _ hLaterSmall
                          have hChild := ih args.toList[k] children₀[k]
                            hOld children₁[k] hLater
                          simpa [k, List.get_eq_getElem] using hChild
                        · rw [dif_neg hLength₁] at h₁
                          simp at h₁
                  · rw [dif_neg hLength₀] at h₀
                    simp at h₀

/-- Public naturality statement at the standard finite readback budget. -/
theorem readback_naturality_finite {σ : LPSignature}
    [DecidableEq σ.vars] {heap₀ heap₁ : Heap σ}
    (ext : BindingExtension heap₀ heap₁)
    (inj : IdentityInjective heap₁)
    {address : Addr} {t₀ t₁ : Term σ}
    (h₀ : Heap.readTerm heap₀ address = .ok t₀)
    (h₁ : Heap.readTerm heap₁ address = .ok t₁) :
    (heapSubst heap₁).applyTerm t₀ = t₁ :=
  readTermFuel_naturality_finite ext inj (heap₀.size + 1) address t₀ h₀ t₁ h₁

/-- On a function-free heap, an `.ok` readback pins the dereference root and
the read value simultaneously. -/
theorem deref_of_readTerm_ff {σ : LPSignature} {heap : Heap σ}
    (ff : FunctionFree heap) :
    ∀ (fuel : Nat) (address : Addr) (t : Term σ),
      readTermFuel heap fuel address = .ok t →
      ∃ root, Heap.derefLoop heap fuel address = .ok (.root root) ∧
        ((∃ identity, heap[root]? = some (Cell.var identity none) ∧
            t = .var identity) ∨
         (∃ symbol, heap[root]? = some (Cell.const symbol) ∧
            t = .const symbol)) := by
  intro fuel
  induction fuel with
  | zero => intro address t h; simp [readTermFuel] at h
  | succ fuel ih =>
      intro address t h
      cases hcell : heap[address]? with
      | none =>
          rw [readTermFuel_invalid heap fuel address hcell] at h
          exact absurd h (by simp)
      | some cell =>
          cases cell with
          | var identity link =>
              cases link with
              | none =>
                  rw [readTermFuel_unbound heap fuel address identity hcell]
                    at h
                  have ht : Term.var identity = t := by simpa using h
                  refine ⟨address, ?_, .inl ⟨identity, hcell, ht.symm⟩⟩
                  simp [Heap.derefLoop, hcell]
              | some target =>
                  rw [readTermFuel_link heap fuel address target identity
                    hcell] at h
                  obtain ⟨root, hroot, hval⟩ := ih target t h
                  refine ⟨root, ?_, hval⟩
                  simp only [Heap.derefLoop, hcell]
                  exact hroot
          | const symbol =>
              rw [readTermFuel_const heap fuel address symbol hcell] at h
              have ht : Term.const symbol = t := by simpa using h
              refine ⟨address, ?_, .inr ⟨symbol, hcell, ht.symm⟩⟩
              simp [Heap.derefLoop, hcell]
          | app symbol args => exact absurd hcell (ff address symbol args)

/-- Walking a preserved chain down: a later-heap `.ok` readback of the chain
head is also the later-heap readback of the old root, at no more fuel. -/
theorem readTermFuel_descend_ext {σ : LPSignature} {heap₀ heap₁ : Heap σ}
    (ext : BindingExtension heap₀ heap₁) :
    ∀ (fuel : Nat) (address root : Addr),
      Heap.derefLoop heap₀ fuel address = .ok (.root root) →
      ∀ (bigFuel : Nat) (t : Term σ),
        readTermFuel heap₁ bigFuel address = .ok t →
        ∃ smallFuel ≤ bigFuel, readTermFuel heap₁ smallFuel root = .ok t := by
  intro fuel
  induction fuel with
  | zero => intro address root h; simp [Heap.derefLoop] at h
  | succ fuel ih =>
      intro address root h bigFuel t hread
      cases hcell : heap₀[address]? with
      | none => simp [Heap.derefLoop, hcell] at h
      | some cell =>
          cases cell with
          | var identity link =>
              cases link with
              | some target =>
                  simp only [Heap.derefLoop, hcell] at h
                  have hcell₁ := ext.link_preserved hcell
                  cases bigFuel with
                  | zero => simp [readTermFuel] at hread
                  | succ bigFuel =>
                      rw [readTermFuel_link heap₁ bigFuel address target
                        identity hcell₁] at hread
                      obtain ⟨smallFuel, hle, hres⟩ :=
                        ih target root h bigFuel t hread
                      exact ⟨smallFuel, Nat.le_succ_of_le hle, hres⟩
              | none =>
                  simp only [Heap.derefLoop, hcell] at h
                  obtain rfl : address = root := by simpa using h
                  exact ⟨bigFuel, Nat.le_refl _, hread⟩
          | const symbol =>
              simp only [Heap.derefLoop, hcell] at h
              obtain rfl : address = root := by simpa using h
              exact ⟨bigFuel, Nat.le_refl _, hread⟩
          | app symbol args =>
              simp only [Heap.derefLoop, hcell] at h
              obtain rfl : address = root := by simpa using h
              exact ⟨bigFuel, Nat.le_refl _, hread⟩

/-- **Readback naturality**: along a binding extension, the later readback
of any address is the finite heap projection of the later heap applied to
its earlier readback. -/
theorem readback_naturality {σ : LPSignature} [DecidableEq σ.vars]
    {heap₀ heap₁ : Heap σ}
    (ext : BindingExtension heap₀ heap₁)
    (inj : IdentityInjective heap₁)
    (_ff : FunctionFree heap₁)
    {address : Addr} {t₀ t₁ : Term σ}
    (h₀ : Heap.readTerm heap₀ address = .ok t₀)
    (h₁ : Heap.readTerm heap₁ address = .ok t₁) :
    (heapSubst heap₁).applyTerm t₀ = t₁ :=
  readback_naturality_finite ext inj h₀ h₁

theorem readableOn_of_orderedFF {σ : LPSignature} {heap : Heap σ}
    (hwf : OrderedFF heap) (support : List σ.vars)
    (hcells : ∀ v ∈ support, ∃ (address : Addr) (link : Option Addr),
      heap[address]? = some (Cell.var v link)) :
    ReadableOn heap support := by
  intro v hv
  obtain ⟨address, link, hcell⟩ := hcells v hv
  have hex : ∃ a : Addr, ∃ link, heap[a]? = some (Cell.var v link) :=
    ⟨address, link, hcell⟩
  have hcellOf : cellOf heap v = some hex.choose := by
    unfold cellOf
    rw [dif_pos hex]
  obtain ⟨link', hchoose⟩ := hex.choose_spec
  obtain ⟨term, hterm⟩ :=
    readTerm_total_of_orderedFF hwf (lt_of_getElem?_some hchoose)
  exact ⟨hex.choose, term, hcellOf, hterm⟩

/-! ## Stage 6: big-step extraction of the unifier phase

`RuntimeQuery.step` relays exactly one unifier microstep per query step, so
a successful `pull` through a `unifying` phase factors as: some number of
machine steps reaching the unifier's own terminal, then the query continues
from the dispatch (success) or backtrack (failure) boundary.  This lets the
run induction consume whole-run unifier theorems (`startMany_success_*`)
instead of threading a microstep invariant. -/

section QueryExtraction

open RuntimeQuery

/-- `failWith` is always terminal. -/
theorem failWith_terminal {σ : LPSignature} (state : State σ)
    (error : QueryError) :
    ∃ result, failWith state error = .terminal result := by
  unfold failWith
  cases closeMemory state with
  | ok memory => exact ⟨_, rfl⟩
  | error cleanup => exact ⟨_, rfl⟩

/-- `complete` is always terminal. -/
theorem complete_terminal {σ : LPSignature} (state : State σ) :
    ∃ result, complete state = .terminal result := by
  unfold complete
  cases closeMemory state with
  | ok memory => exact ⟨_, rfl⟩
  | error cleanup => exact ⟨_, rfl⟩

/-- The dispatch state entered when a selected head unifies. -/
def unifySuccessState {σ : LPSignature} (state : State σ)
    (attempt : Attempt σ) (memory : Memory σ.scoped) : State σ :=
  { state with
    memory
    control := {
      current := attempt.body
      cutDepth := attempt.cutDepth
      frames := attempt.frames
    }
    phase := .dispatch }

/-- Factor a successful `pull` through a running unifier: the machine
reaches its own terminal in as many microsteps, and the query resumes from
the corresponding boundary state with the remaining fuel. -/
theorem pull_unifying_extract {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    (builtins : Builtins σ) (program : Program σ) :
    ∀ (fuel : Nat) (state : State σ) (attempt : Attempt σ)
      (machine : RuntimeUnification.Machine σ.scoped)
      (answer : Answer σ) (resumed : State σ),
      state.phase = .unifying attempt machine →
      pull builtins program fuel state = .answer answer resumed →
      ∃ (unifierSteps rest : Nat), fuel = unifierSteps + 1 + rest ∧
        ((∃ m, RuntimeUnification.runSteps unifierSteps machine =
            .terminal (.success m) ∧
          pull builtins program rest (unifySuccessState state attempt m) =
            .answer answer resumed) ∨
         (∃ m, RuntimeUnification.runSteps unifierSteps machine =
            .terminal (.failure m) ∧
          pull builtins program rest
            { state with memory := m, phase := .backtrack } =
            .answer answer resumed)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro state attempt machine answer resumed hPhase hPull
      simp [pull, RuntimeQuery.pullCore] at hPull
  | succ fuel ih =>
      intro state attempt machine answer resumed hPhase hPull
      simp only [pull, RuntimeQuery.pullCore,
        RuntimeQuery.lp_stepCore_eq_step] at hPull
      cases machine with
      | running c =>
          cases hms : RuntimeUnification.step (RuntimeUnification.Machine.running c) with
          | some next =>
              have hstep : RuntimeQuery.step builtins program state =
                  .next { state with phase := .unifying attempt next } none := by
                simp [RuntimeQuery.step, RuntimeQuery.stepCore, hPhase, hms]
              rw [hstep] at hPull
              dsimp only at hPull
              obtain ⟨k, rest, hfuel, hdisj⟩ :=
                ih { state with phase := .unifying attempt next } attempt next
                  answer resumed rfl hPull
              refine ⟨k + 1, rest, ?_, ?_⟩
              · rw [hfuel]
                exact Nat.add_right_comm (k + 1) rest 1
              · rw [runSteps_succ_some hms]
                exact hdisj
          | none =>
              have hstep : RuntimeQuery.step builtins program state =
                  failWith state .stalledUnifier := by
                simp [RuntimeQuery.step, RuntimeQuery.stepCore, hPhase, hms]
              rw [hstep] at hPull
              obtain ⟨result, hres⟩ := failWith_terminal state .stalledUnifier
              rw [hres] at hPull
              dsimp only at hPull
              cases hPull
      | terminal t =>
          cases t with
          | success m =>
              have hstep : RuntimeQuery.step builtins program state = .next
                  (unifySuccessState state attempt m) none := by
                simp [RuntimeQuery.step, RuntimeQuery.stepCore, hPhase,
                  unifySuccessState]
              rw [hstep] at hPull
              dsimp only at hPull
              exact ⟨0, fuel, by omega, .inl ⟨m, rfl, hPull⟩⟩
          | failure m =>
              have hstep : RuntimeQuery.step builtins program state = .next
                  { state with memory := m, phase := .backtrack } none := by
                simp [RuntimeQuery.step, RuntimeQuery.stepCore, hPhase]
              rw [hstep] at hPull
              dsimp only at hPull
              exact ⟨0, fuel, by omega, .inr ⟨m, rfl, hPull⟩⟩
          | runtimeError e m =>
              have hstep : RuntimeQuery.step builtins program state =
                  failWith { state with memory := m } (.memory e) := by
                simp [RuntimeQuery.step, RuntimeQuery.stepCore, hPhase]
              rw [hstep] at hPull
              obtain ⟨result, hres⟩ :=
                failWith_terminal { state with memory := m } (.memory e)
              rw [hres] at hPull
              dsimp only at hPull
              cases hPull

end QueryExtraction

/-! ## Stage 6: the opened query state

`openQuery` is the endpoint's entry: invert it, and establish the full
heap-invariant bundle at the state it constructs.  On the empty memory the
caller-side hypotheses are all vacuous. -/

section OpenedState

open RuntimeQuery

/-- Function-free is definitionally free when the signature has no function
symbols — the fragment the composed endpoint theorem lives in. -/
theorem functionFree_of_isEmpty {σ : LPSignature}
    [IsEmpty σ.functionSymbols] (heap : Heap σ) : FunctionFree heap :=
  fun _ symbol _ _ => (IsEmpty.false symbol).elim

/-- The state `openQuery` constructs on success. -/
def openedState {σ : LPSignature} (memory : Memory σ.scoped)
    (nextScope : Nat) (result : MaterializedGoals σ.scoped) : State σ :=
  { memory := result.memory
    control := {
      current := result.goals
      cutDepth := 0
      frames := []
    }
    choices := []
    queryCheckpoint := memory.checkpoint
    queryVarMap := result.varMap
    nextScope
    phase := .dispatch }

/-- Invert a successful `openQuery`. -/
theorem openQuery_ok_inv {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ.scoped} {queryScope nextScope : Nat}
    {goals : List (Atom σ)} {state : State σ}
    (h : openQuery memory queryScope nextScope goals = .ok state) :
    queryScope < nextScope ∧
    heapScopesBelow memory.heap nextScope = true ∧
    ∃ result,
      materializeGoals memory (queryAtScope queryScope goals) =
        .ok result ∧
      state = openedState memory nextScope result := by
  unfold openQuery openQueryCore lpQueryMaterializer at h
  by_cases hScope : queryScope < nextScope
  case neg => rw [if_neg hScope] at h; cases h
  case pos =>
  rw [if_pos hScope] at h
  by_cases hBelow : heapScopesBelow memory.heap nextScope = true
  case neg => rw [if_neg hBelow] at h; cases h
  case pos =>
  rw [if_pos hBelow] at h
  dsimp only at h
  cases hMat : materializeGoals memory (queryAtScope queryScope goals) with
  | error e => rw [hMat] at h; cases h
  | ok result =>
      rw [hMat] at h
      dsimp only at h
      cases h
      exact ⟨hScope, hBelow, result, rfl, rfl⟩

/-- The heap-invariant bundle carried by every query boundary state. -/
def StateHeapInv {σ : LPSignature} (state : State σ) : Prop :=
  Heap.WellFormed state.memory.heap ∧
  DescendingOrConst state.memory.heap ∧
  IdentityInjective state.memory.heap ∧
  HeapScopesBelow state.nextScope state.memory.heap

/-- Opening a query over an invariant-satisfying memory establishes the
bundle, and the query variable map is fresh-coherent at the query scope. -/
theorem openQuery_stateHeapInv {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ.scoped} {queryScope nextScope : Nat}
    {goals : List (Atom σ)} {state : State σ}
    (h : openQuery memory queryScope nextScope goals = .ok state)
    (hDesc : DescendingOrConst memory.heap)
    (hInj : IdentityInjective memory.heap)
    (hBelowQ : HeapScopesBelow queryScope memory.heap) :
    StateHeapInv state ∧
    FreshInv (fun v : ScopedVar σ.vars => v.scope = queryScope)
      { heap := state.memory.heap, varMap := state.queryVarMap } := by
  obtain ⟨hScope, _, result, hMat, rfl⟩ := openQuery_ok_inv h
  obtain ⟨_, _, _, hWF, _⟩ := materializeGoals_roundtrip hMat
  refine ⟨⟨hWF, ?_, ?_, ?_⟩, ?_⟩
  · exact materializeGoals_descendingOrConst hMat hDesc
  · exact (materializeGoals_scoped_freshInv hMat hBelowQ hInj).injective
  · exact materializeGoals_scopesBelow hMat hScope
      (fun a id link hcell =>
        Nat.lt_trans (hBelowQ a id link hcell) hScope)
  · exact materializeGoals_scoped_freshInv hMat hBelowQ hInj

/-- The empty memory holds no cells. -/
theorem empty_heap_getElem {σ : LPSignature} (a : Addr) :
    (Memory.empty σ).heap[a]? = none := by
  rw [Array.getElem?_eq_none]
  exact Nat.zero_le a

/-- The endpoint's entry instance: everything vacuous on the empty memory. -/
theorem openQuery_empty_stateHeapInv {σ : LPSignature} [DecidableEq σ.vars]
    {goals : List (Atom σ)} {state : State σ}
    (h : openQuery (Memory.empty σ.scoped) 0 1 goals = .ok state) :
    StateHeapInv state ∧
    FreshInv (fun v : ScopedVar σ.vars => v.scope = 0)
      { heap := state.memory.heap, varMap := state.queryVarMap } :=
  openQuery_stateHeapInv h
    (fun a id t hcell => by rw [empty_heap_getElem] at hcell; cases hcell)
    (fun a b id la lb ha _ => by rw [empty_heap_getElem] at ha; cases ha)
    (fun a id link hcell => by rw [empty_heap_getElem] at hcell; cases hcell)

end OpenedState

/-! ## Stage 6: the reachable-state invariant

The bundle every query boundary state satisfies, with the choice stack
carried as an `Extends`-anchored chain of checkpoint memories: restoring a
cursor recovers *exactly* a previously reached memory together with its
stored invariants. -/

section QueryInvariant

open RuntimeQuery

/-- A successful write's cell had its references checked in bounds. -/
theorem write_ok_refs {σ : LPSignature} {memory memory' : Memory σ}
    {address : Addr} {cell : Cell σ}
    (h : memory.write address cell = .ok memory') :
    ∀ target ∈ Cell.references cell, target < memory.heap.size := by
  unfold Memory.write at h
  split at h
  · split at h
    · split at h
      next hrefs =>
        intro target ht
        exact of_decide_eq_true (List.all_eq_true.mp hrefs target ht)
      next =>
        rcases hfind : (Cell.references cell).find?
            (fun target => decide (memory.heap.size ≤ target)) with _ | t <;>
          rw [hfind] at h <;> cases h
    · cases h
  · cases h

/-- A successful allocation's cell had its references checked in bounds. -/
theorem allocate_ok_refs {σ : LPSignature} {memory memory' : Memory σ}
    {address : Addr} {cell : Cell σ}
    (h : memory.allocate cell = .ok (address, memory')) :
    ∀ target ∈ Cell.references cell, target < memory.heap.size := by
  unfold Memory.allocate at h
  split at h
  · split at h
    next hrefs =>
      intro target ht
      exact of_decide_eq_true (List.all_eq_true.mp hrefs target ht)
    next =>
      rcases hfind : (Cell.references cell).find?
          (fun address => decide (memory.heap.size ≤ address)) with _ | t <;>
        rw [hfind] at h <;> cases h
  · cases h

/-- Successful writes preserve heap well-formedness. -/
theorem wellFormed_write {σ : LPSignature} {memory memory' : Memory σ}
    {address : Addr} {cell : Cell σ}
    (h : memory.write address cell = .ok memory')
    (hwf : Heap.WellFormed memory.heap) :
    Heap.WellFormed memory'.heap := by
  obtain ⟨hlt, hmem⟩ := write_ok_inv h
  have hheap : memory'.heap = memory.heap.set address cell hlt := by
    rw [hmem]
  have hsize : memory'.heap.size = memory.heap.size := by
    rw [hheap]; simp
  intro a c hcell target ht
  rw [hheap] at hcell
  rw [hsize]
  by_cases haddr : a = address
  · rw [haddr, heap_set_get_self _ _ hlt] at hcell
    cases hcell
    exact write_ok_refs h target ht
  · rw [heap_set_get_ne _ _ hlt haddr] at hcell
    exact hwf a c hcell target ht

/-- Successful allocations preserve heap well-formedness. -/
theorem wellFormed_allocate {σ : LPSignature} {memory memory' : Memory σ}
    {address : Addr} {cell : Cell σ}
    (h : memory.allocate cell = .ok (address, memory'))
    (hwf : Heap.WellFormed memory.heap) :
    Heap.WellFormed memory'.heap := by
  obtain ⟨haddr, hmem⟩ := allocate_ok_inv h
  have hheap : memory'.heap = memory.heap.push cell := by
    rw [hmem]
  have hsize : memory'.heap.size = memory.heap.size + 1 := by
    rw [hheap]; simp
  intro a c hcell target ht
  rw [hheap] at hcell
  rw [hsize]
  rcases getElem?_push_cases hcell with ⟨_, hold⟩ | ⟨_, hcelleq⟩
  · exact Nat.lt_succ_of_lt (hwf a c hold target ht)
  · subst hcelleq
    exact Nat.lt_succ_of_lt (allocate_ok_refs h target ht)

/-- A write/allocation history preserves heap well-formedness. -/
theorem Extends.wellFormed {σ : LPSignature} {m₀ m₁ : Memory σ}
    (h : Extends m₀ m₁) (hwf : Heap.WellFormed m₀.heap) :
    Heap.WellFormed m₁.heap := by
  induction h with
  | refl => exact hwf
  | write _ step ih => exact wellFormed_write step ih
  | alloc _ step ih => exact wellFormed_allocate step ih

/-! ### Boundedness of the live control data -/

/-- Every runtime atom of the list is well-formed over the heap. -/
def AtomsWF {σ : LPSignature} (heap : Heap σ.scoped)
    (atoms : List (RuntimeAtom σ.scoped)) : Prop :=
  ∀ atom ∈ atoms, atom.WellFormed heap

/-- Every stored continuation is well-formed over the heap. -/
def FramesWF {σ : LPSignature} (heap : Heap σ.scoped)
    (frames : List (ReturnFrame σ)) : Prop :=
  ∀ frame ∈ frames, AtomsWF heap frame.continuation

/-- Every query variable's cell is present, carrying its identity. -/
def VarMapCellsWF {σ : LPSignature} (heap : Heap σ.scoped)
    (varMap : List (ScopedVar σ.vars × Addr)) : Prop :=
  ∀ pair ∈ varMap, ∃ link,
    heap[pair.2]? = some (Cell.var pair.1 link)

theorem RuntimeAtom.wellFormed_mono {σ : LPSignature}
    {heap heap' : Heap σ.scoped} {atom : RuntimeAtom σ.scoped}
    (hle : heap.size ≤ heap'.size) (h : atom.WellFormed heap) :
    atom.WellFormed heap' :=
  ⟨h.1, fun a ha => Nat.lt_of_lt_of_le (h.2 a ha) hle⟩

theorem AtomsWF.mono {σ : LPSignature} {heap heap' : Heap σ.scoped}
    {atoms : List (RuntimeAtom σ.scoped)}
    (hle : heap.size ≤ heap'.size) (h : AtomsWF heap atoms) :
    AtomsWF heap' atoms :=
  fun atom hatom => RuntimeAtom.wellFormed_mono hle (h atom hatom)

theorem FramesWF.mono {σ : LPSignature} {heap heap' : Heap σ.scoped}
    {frames : List (ReturnFrame σ)}
    (hle : heap.size ≤ heap'.size) (h : FramesWF heap frames) :
    FramesWF heap' frames :=
  fun frame hframe => (h frame hframe).mono hle

/-- Cells survive verbatim under prefix-preserving growth. -/
theorem VarMapCellsWF.of_prefix {σ : LPSignature}
    {heap heap' : Heap σ.scoped}
    {varMap : List (ScopedVar σ.vars × Addr)}
    (hprefix : ∀ i, i < heap.size → heap'[i]? = heap[i]?)
    (h : VarMapCellsWF heap varMap) : VarMapCellsWF heap' varMap := by
  intro pair hpair
  obtain ⟨link, hcell⟩ := h pair hpair
  exact ⟨link, by
    rw [hprefix pair.2 (lt_of_getElem?_some hcell)]
    exact hcell⟩

/-- Cells keep their identity under binding extensions. -/
theorem VarMapCellsWF.of_bindingExtension {σ : LPSignature}
    {heap heap' : Heap σ.scoped}
    {varMap : List (ScopedVar σ.vars × Addr)}
    (hext : BindingExtension heap heap')
    (h : VarMapCellsWF heap varMap) : VarMapCellsWF heap' varMap := by
  intro pair hpair
  obtain ⟨link, hcell⟩ := h pair hpair
  rcases hext.2 pair.2 _ hcell with hsame | ⟨id, target, hEq, hbound⟩
  · exact ⟨link, hsame⟩
  · cases hEq
    exact ⟨some target, hbound⟩

/-- Scope bounds transfer along size-preserving binding extensions:
identities never change. -/
theorem HeapScopesBelow.of_bindingExtension {σ : LPSignature}
    {heap heap' : Heap σ.scoped} {bound : Nat}
    (hext : BindingExtension heap heap') (hsize : heap.size = heap'.size)
    (h : HeapScopesBelow bound heap) : HeapScopesBelow bound heap' := by
  intro a identity link hcell
  have hlt : a < heap.size := by
    rw [hsize]
    exact lt_of_getElem?_some hcell
  obtain ⟨link₀, hcell₀⟩ := hext.var_back hlt hcell
  exact h a identity link₀ hcell₀

/-- Scope bounds are monotone in the bound. -/
theorem HeapScopesBelow.mono {σ : LPSignature} {heap : Heap σ.scoped}
    {bound bound' : Nat} (hle : bound ≤ bound')
    (h : HeapScopesBelow bound heap) : HeapScopesBelow bound' heap :=
  fun a identity link hcell =>
    Nat.lt_of_lt_of_le (h a identity link hcell) hle

/-! ### The choice chain -/

/-- The choice stack as an `Extends`-anchored chain: each cursor stores the
memory its checkpoint denotes, that memory's invariants, and the bounds of
everything the cursor will need after restoring.  Deeper cursors anchor to
the memory of the cursor above them. -/
inductive ChoiceChain {σ : LPSignature} [DecidableEq σ.relationSymbols]
    (program : Program σ)
    (varMap : List (ScopedVar σ.vars × Addr)) :
    Nat → List (ClauseCursor σ) → Memory σ.scoped → Prop
  | nil (bound : Nat) (memory : Memory σ.scoped) :
      ChoiceChain program varMap bound [] memory
  | cons {bound : Nat} {cursor : ClauseCursor σ}
      {older : List (ClauseCursor σ)} {memory m₀ : Memory σ.scoped}
      (hcp : cursor.checkpoint = m₀.checkpoint)
      (hext : Extends m₀ memory)
      (hwf : Heap.WellFormed m₀.heap)
      (hshaped : Heap.WellShaped m₀.heap)
      (hdesc : DescendingOrConst m₀.heap)
      (hinj : IdentityInjective m₀.heap)
      (hscopes : HeapScopesBelow bound m₀.heap)
      (hvarMap : VarMapCellsWF m₀.heap varMap)
      (hgoal : cursor.goal.WellFormed m₀.heap)
      (hframes : FramesWF m₀.heap cursor.frames)
      (hclauses : ∀ c ∈ cursor.clauses,
        c ∈ clausesFor program cursor.goal.symbol)
      (holder : ChoiceChain program varMap bound older m₀) :
      ChoiceChain program varMap bound (cursor :: older) memory

/-- Re-anchor a chain along a further extension. -/
theorem ChoiceChain.anchor {σ : LPSignature}
    [DecidableEq σ.relationSymbols] {program : Program σ}
    {varMap : List (ScopedVar σ.vars × Addr)} {bound : Nat}
    {choices : List (ClauseCursor σ)} {memory memory' : Memory σ.scoped}
    (h : ChoiceChain program varMap bound choices memory)
    (hext : Extends memory memory') :
    ChoiceChain program varMap bound choices memory' := by
  cases h with
  | nil => exact .nil bound memory'
  | cons hcp hext₀ hwf hshaped hdesc hinj hscopes hvarMap hgoal hframes
      hclauses holder =>
      exact .cons hcp (hext₀.trans hext) hwf hshaped hdesc hinj hscopes
        hvarMap hgoal hframes hclauses holder

/-- Lift a chain to a larger scope bound. -/
theorem ChoiceChain.scope_mono {σ : LPSignature}
    [DecidableEq σ.relationSymbols] {program : Program σ}
    {varMap : List (ScopedVar σ.vars × Addr)} {bound bound' : Nat}
    {choices : List (ClauseCursor σ)} {memory : Memory σ.scoped}
    (hle : bound ≤ bound')
    (h : ChoiceChain program varMap bound choices memory) :
    ChoiceChain program varMap bound' choices memory := by
  induction h with
  | nil => exact .nil bound' _
  | cons hcp hext hwf hshaped hdesc hinj hscopes hvarMap hgoal hframes
      hclauses holder ih =>
      exact .cons hcp hext hwf hshaped hdesc hinj (hscopes.mono hle)
        hvarMap hgoal hframes hclauses ih

/-- Drop the newest cursors; the rest stay chained to the same anchor. -/
theorem ChoiceChain.drop {σ : LPSignature}
    [DecidableEq σ.relationSymbols] {program : Program σ}
    {varMap : List (ScopedVar σ.vars × Addr)} {bound : Nat} :
    ∀ (k : Nat) {choices : List (ClauseCursor σ)}
      {memory : Memory σ.scoped},
      ChoiceChain program varMap bound choices memory →
      ChoiceChain program varMap bound (choices.drop k) memory := by
  intro k
  induction k with
  | zero => intro choices memory h; exact h
  | succ k ih =>
      intro choices memory h
      cases h with
      | nil => exact .nil bound _
      | cons hcp hext hwf hshaped hdesc hinj hscopes hvarMap hgoal hframes
          hclauses holder =>
          exact ih (holder.anchor hext)

/-- Retaining the oldest cursors preserves the chain. -/
theorem ChoiceChain.retainBottom {σ : LPSignature}
    [DecidableEq σ.relationSymbols] {program : Program σ}
    {varMap : List (ScopedVar σ.vars × Addr)} {bound : Nat}
    {choices : List (ClauseCursor σ)} {memory : Memory σ.scoped}
    (mark : Nat)
    (h : ChoiceChain program varMap bound choices memory) :
    ChoiceChain program varMap bound
      (RuntimeQuery.retainBottom mark choices) memory :=
  ChoiceChain.drop (choices.length - mark) h

/-! ### The boundary invariant -/

/-- What every reachable query state satisfies at its own memory.  The
control's own bounds live in `ControlWF`: they hold at dispatch states but
are deliberately absent here, because the control is stale — dead data —
between a backtrack restore and the unify success that replaces it. -/
structure QueryInv {σ : LPSignature} [DecidableEq σ.relationSymbols]
    (program : Program σ) (state : State σ) : Prop where
  wf : Heap.WellFormed state.memory.heap
  shaped : Heap.WellShaped state.memory.heap
  desc : DescendingOrConst state.memory.heap
  inj : IdentityInjective state.memory.heap
  scopes : HeapScopesBelow state.nextScope state.memory.heap
  varMap : VarMapCellsWF state.memory.heap state.queryVarMap
  chain : ChoiceChain program state.queryVarMap state.nextScope
    state.choices state.memory

/-- The live control is bounded — required exactly at dispatch states. -/
def ControlWF {σ : LPSignature} (state : State σ) : Prop :=
  AtomsWF state.memory.heap state.control.current ∧
  FramesWF state.memory.heap state.control.frames

/-- Extra facts carried by a `select` phase, about its cursor. -/
structure SelectInv {σ : LPSignature} [DecidableEq σ.relationSymbols]
    (program : Program σ) (state : State σ) (cursor : ClauseCursor σ) :
    Prop where
  checkpoint : cursor.checkpoint = state.memory.checkpoint
  goal : cursor.goal.WellFormed state.memory.heap
  frames : FramesWF state.memory.heap cursor.frames
  clauses : ∀ c ∈ cursor.clauses, c ∈ clausesFor program cursor.goal.symbol

/-! ### Executable checks from the propositions -/

theorem Cell.check_of_shapeCorrect {σ : LPSignature} {cell : Cell σ}
    (h : cell.ShapeCorrect) : cell.checkShape = true := by
  cases cell with
  | var => rfl
  | const => rfl
  | app symbol args => exact beq_iff_eq.mpr h

theorem Heap.check_of_wellFormed {σ : LPSignature} {heap : Heap σ}
    (h : heap.WellFormed) : heap.checkWellFormed = true := by
  apply Array.all_eq_true.mpr
  intro a hlt
  apply List.all_eq_true.mpr
  intro target ht
  apply decide_eq_true
  exact h a heap[a] (Array.getElem?_eq_getElem hlt) target ht

theorem Heap.check_of_wellShaped {σ : LPSignature} {heap : Heap σ}
    (h : heap.WellShaped) : heap.checkWellShaped = true := by
  apply Array.all_eq_true.mpr
  intro a hlt
  exact Cell.check_of_shapeCorrect (h a heap[a] (Array.getElem?_eq_getElem hlt))

/-- A write/allocation history preserves heap well-shapedness. -/
theorem Extends.wellShaped {σ : LPSignature} {m₀ m₁ : Memory σ}
    (h : Extends m₀ m₁) (hshaped : Heap.WellShaped m₀.heap) :
    Heap.WellShaped m₁.heap := by
  induction h with
  | refl => exact hshaped
  | write _ step ih => exact Memory.write_wellShaped ih step
  | alloc _ step ih => exact Memory.allocate_wellShaped ih step

/-! ### Structural facts of checked materialization -/

/-- Everything the query transition needs from a successful clause
materialization: old cells verbatim, heap growth, a well-formed runtime
clause, executable checks of the result, and an untouched trail. -/
theorem materializeClause_facts {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ} {clause : Clause σ}
    {result : MaterializedClause σ}
    (h : materializeClause memory clause = .ok result) :
    (∀ i, i < memory.heap.size →
      result.memory.heap[i]? = memory.heap[i]?) ∧
    memory.heap.size ≤ result.memory.heap.size ∧
    result.clause.WellFormed result.memory.heap ∧
    result.memory.heap.checkWellFormed = true ∧
    result.memory.heap.checkWellShaped = true ∧
    result.memory.trail = memory.trail := by
  unfold materializeClause at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeClauseAux clause) memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeClause, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨hWF, _, hrun, hWF', hWS'⟩ := runChecked_ok hrc
      by_cases hCheck :
          runtimeClause.checkWellFormed state.heap = true
      case neg => rw [if_neg hCheck] at h; cases h
      case pos =>
        rw [if_pos hCheck] at h
        cases h
        simp only [materializeClauseAux, BuilderM.run_bind] at hrun
        cases hHead : (materializeAtomAux clause.head).run
            (BuilderState.start memory.heap) with
        | error e => rw [hHead] at hrun; cases hrun
        | ok headPair =>
            obtain ⟨headAtom, sMid⟩ := headPair
            rw [hHead] at hrun
            dsimp only at hrun
            cases hBody : (clause.body.mapM materializeAtomAux).run sMid with
            | error e => rw [hBody] at hrun; cases hrun
            | ok bodyPair =>
                obtain ⟨bodyAtoms, sEnd⟩ := bodyPair
                rw [hBody] at hrun
                dsimp only at hrun
                cases hrun
                obtain ⟨bHead, _, _⟩ :=
                  materializeAtomAux_spec clause.head hHead
                    (Heap.wellFormed_of_check hWF)
                    (fun pair hp => by simp [BuilderState.start] at hp)
                obtain ⟨bBody, _, _⟩ :=
                  materializeAtomsMapM_spec clause.body hBody
                    bHead.wf bHead.cells
                have bAll := bHead.trans bBody
                exact ⟨bAll.prefixEq, bAll.sizeLe,
                  RuntimeClause.wellFormed_of_check hCheck, hWF', hWS', rfl⟩

/-- Everything the opened query needs from goal materialization. -/
theorem materializeGoals_facts {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ} {goals : List (Atom σ)}
    {result : MaterializedGoals σ}
    (h : materializeGoals memory goals = .ok result) :
    (∀ atom ∈ result.goals, atom.WellFormed result.memory.heap) ∧
    result.memory.heap.checkWellFormed = true ∧
    result.memory.heap.checkWellShaped = true := by
  unfold materializeGoals at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeGoalsAux goals) memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeGoals, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨_, _, _, hWF', hWS'⟩ := runChecked_ok hrc
      by_cases hCheck : (runtimeGoals.all
          fun atom => atom.checkWellFormed state.heap) = true
      case neg => rw [if_neg hCheck] at h; cases h
      case pos =>
        rw [if_pos hCheck] at h
        cases h
        exact ⟨fun atom hatom => RuntimeAtom.wellFormed_of_check
          (List.all_eq_true.mp hCheck atom hatom), hWF', hWS'⟩

/-! ### The invariant at the endpoint's entry -/

/-- The endpoint's opened state satisfies the full boundary invariant. -/
theorem openQuery_empty_queryInv {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.relationSymbols]
    {program : Program σ} {goals : List (Atom σ)} {state : State σ}
    (h : openQuery (Memory.empty σ.scoped) 0 1 goals = .ok state) :
    QueryInv program state ∧ ControlWF state := by
  obtain ⟨hScope, _, result, hMat, rfl⟩ := openQuery_ok_inv h
  obtain ⟨_, _, _, hWF, hCells⟩ := materializeGoals_roundtrip hMat
  obtain ⟨hAtoms, _, hCWS⟩ := materializeGoals_facts hMat
  have hEmptyCell : ∀ (a : Addr) (cell : Cell σ.scoped),
      (Memory.empty σ.scoped).heap[a]? = some cell → False := by
    intro a cell hcell
    rw [empty_heap_getElem] at hcell
    cases hcell
  refine ⟨⟨hWF, Heap.wellShaped_of_check hCWS, ?_, ?_, ?_, ?_, .nil 1 _⟩,
    hAtoms, ?_⟩
  · exact materializeGoals_descendingOrConst hMat
      (fun a id t hcell => (hEmptyCell a _ hcell).elim)
  · exact (materializeGoals_scoped_freshInv hMat
      (fun a id link hcell => (hEmptyCell a _ hcell).elim)
      (fun a b id la lb ha _ => (hEmptyCell a _ ha).elim)).injective
  · exact materializeGoals_scopesBelow hMat hScope
      (fun a id link hcell => (hEmptyCell a _ hcell).elim)
  · exact fun pair hp => ⟨none, hCells pair hp⟩
  · exact fun frame hframe => by cases hframe

/-! ### Per-arm preservation -/

/-- Changing only the phase keeps the boundary invariant. -/
theorem QueryInv.set_phase {σ : LPSignature}
    [DecidableEq σ.relationSymbols] {program : Program σ}
    {state : State σ} (h : QueryInv program state) (p : Phase σ) :
    QueryInv program { state with phase := p } :=
  ⟨h.wf, h.shaped, h.desc, h.inj, h.scopes, h.varMap, h.chain⟩

/-- Changing only the phase also keeps the control bounds. -/
theorem ControlWF.set_phase {σ : LPSignature} {state : State σ}
    (h : ControlWF state) (p : Phase σ) :
    ControlWF { state with phase := p } := h

/-- The state entered when the current goal list empties into a stored
return frame. -/
def framePopState {σ : LPSignature} (state : State σ)
    (frame : ReturnFrame σ) (frames' : List (ReturnFrame σ)) : State σ :=
  { state with
    control := {
      current := frame.continuation
      cutDepth := frame.callerCutDepth
      frames := frames'
    } }

theorem QueryInv.framePop {σ : LPSignature}
    [DecidableEq σ.relationSymbols] {program : Program σ}
    {state : State σ} {frame : ReturnFrame σ}
    {frames' : List (ReturnFrame σ)}
    (h : QueryInv program state) :
    QueryInv program (framePopState state frame frames') :=
  ⟨h.wf, h.shaped, h.desc, h.inj, h.scopes, h.varMap, h.chain⟩

theorem ControlWF.framePop {σ : LPSignature} {state : State σ}
    {frame : ReturnFrame σ} {frames' : List (ReturnFrame σ)}
    (h : ControlWF state)
    (hframes : state.control.frames = frame :: frames') :
    ControlWF (framePopState state frame frames') :=
  ⟨h.2 frame (by rw [hframes]; exact List.mem_cons_self ..),
    fun f hf => h.2 f (by rw [hframes]; exact List.mem_cons_of_mem _ hf)⟩

/-- A predicate call: the dispatch arm packages the caller into a cursor
and moves to clause selection.  The boundary invariant is untouched and the
cursor facts follow from the goal being live. -/
theorem ControlWF.callCursor {σ : LPSignature}
    [DecidableEq σ.relationSymbols] {program : Program σ}
    {state : State σ} {goal : RuntimeAtom σ.scoped}
    {rest : List (RuntimeAtom σ.scoped)}
    (h : ControlWF state)
    (hcurrent : state.control.current = goal :: rest) :
    SelectInv program state {
      checkpoint := state.memory.checkpoint
      goal
      clauses := clausesFor program goal.symbol
      cutDepth := state.choices.length
      frames := { continuation := rest, callerCutDepth := state.control.cutDepth } :: state.control.frames
    } :=
  ⟨rfl,
    h.1 goal (by rw [hcurrent]; exact List.mem_cons_self ..),
    fun f hf => by
      rcases List.mem_cons.mp hf with rfl | hf'
      · exact fun atom hatom => h.1 atom
          (by rw [hcurrent]; exact List.mem_cons_of_mem _ hatom)
      · exact h.2 f hf',
    fun c hc => hc⟩

/-- The unifying-entry state built by a successful clause selection. -/
def unifyEntryState {σ : LPSignature} (state : State σ)
    (cursor : ClauseCursor σ) (remaining : List (Clause σ))
    (copied : MaterializedClause σ.scoped) : State σ :=
  { state with
    memory := copied.memory
    choices := replacementChoices cursor remaining state.choices
    nextScope := state.nextScope + 1
    phase := .unifying {
        body := copied.clause.body
        cutDepth := cursor.cutDepth
        frames := cursor.frames
      }
      (RuntimeUnification.startMany copied.memory
        (cursor.goal.args.toList.zip copied.clause.head.args.toList)) }

/-- **Clause selection preserves the boundary invariant** and yields the
activation facts the unifier boundary will consume. -/
theorem selectSuccess_inv {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.relationSymbols]
    {program : Program σ} {state : State σ} {cursor : ClauseCursor σ}
    {clause : Clause σ} {remaining : List (Clause σ)}
    {copied : MaterializedClause σ.scoped}
    (hq : QueryInv program state) (hs : SelectInv program state cursor)
    (hclauses : cursor.clauses = clause :: remaining)
    (hMat : materializeClause state.memory
      (clause.atScope state.nextScope) = .ok copied) :
    QueryInv program (unifyEntryState state cursor remaining copied) ∧
    Extends state.memory copied.memory ∧
    copied.clause.WellFormed copied.memory.heap ∧
    FreshInv (fun v : ScopedVar σ.vars => v.scope = state.nextScope)
      { heap := copied.memory.heap, varMap := copied.varMap } := by
  obtain ⟨hExt, _, _, _, hWFc, _⟩ := materializeClause_roundtrip hMat
  obtain ⟨hPrefix, hSize, hClauseWF, _, hWS', _⟩ :=
    materializeClause_facts hMat
  have hFresh := materializeClause_scoped_freshInv hMat hq.scopes hq.inj
  refine ⟨⟨hWFc, Heap.wellShaped_of_check hWS', ?_, hFresh.injective, ?_,
    hq.varMap.of_prefix hPrefix, ?_⟩, hExt, hClauseWF, hFresh⟩
  · exact materializeClause_descendingOrConst hMat hq.desc
  · exact materializeClause_scopesBelow hMat (Nat.lt_succ_self _)
      (hq.scopes.mono (Nat.le_succ _))
  · show ChoiceChain program state.queryVarMap (state.nextScope + 1)
      (replacementChoices cursor remaining state.choices) copied.memory
    cases remaining with
    | nil =>
        show ChoiceChain program state.queryVarMap (state.nextScope + 1)
          state.choices copied.memory
        exact (hq.chain.anchor hExt).scope_mono (Nat.le_succ _)
    | cons r rs =>
        show ChoiceChain program state.queryVarMap (state.nextScope + 1)
          ({ cursor with clauses := r :: rs } :: state.choices)
          copied.memory
        refine ChoiceChain.cons (m₀ := state.memory) hs.checkpoint hExt
          hq.wf hq.shaped hq.desc hq.inj
          (hq.scopes.mono (Nat.le_succ _)) hq.varMap hs.goal hs.frames
          ?_ (hq.chain.scope_mono (Nat.le_succ _))
        intro c hc
        exact hs.clauses c (by
          rw [hclauses]
          exact List.mem_cons_of_mem _ hc)

end QueryInvariant
section BoundaryLemmas

open RuntimeQuery

/-- **Unify-success boundary**: a successful head unification from any
invariant-satisfying entry memory re-establishes the full boundary
invariant, and the replacing control is bounded at the success memory. -/
theorem unifySuccess_queryInv {σ : LPSignature} [IsEmpty σ.functionSymbols]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols]
    {program : Program σ} {stateE : State σ} {attempt : Attempt σ}
    {agenda : List (Addr × Addr)} {k : Nat} {m : Memory σ.scoped}
    (hq : QueryInv program stateE)
    (hBody : AtomsWF stateE.memory.heap attempt.body)
    (hFrames : FramesWF stateE.memory.heap attempt.frames)
    (hrun : RuntimeUnification.runSteps k
      (RuntimeUnification.startMany stateE.memory agenda) =
      .terminal (.success m)) :
    QueryInv program (unifySuccessState stateE attempt m) ∧
    ControlWF (unifySuccessState stateE attempt m) := by
  obtain ⟨ext, hExt, hsize⟩ :=
    startMany_success_extension k stateE.memory agenda m hrun
  have hOFF := startMany_success_orderedFF k stateE.memory agenda m hrun
    ⟨hq.desc, functionFree_of_isEmpty _⟩
  exact ⟨⟨hExt.wellFormed hq.wf, hExt.wellShaped hq.shaped, hOFF.1,
    IdentityInjective.of_bindingExtension ext hsize hq.inj,
    hq.scopes.of_bindingExtension ext hsize,
    hq.varMap.of_bindingExtension ext,
    hq.chain.anchor hExt⟩,
    hBody.mono ext.1, hFrames.mono ext.1⟩

/-- **Backtrack boundary**: popping a cursor restores exactly the chained
checkpoint memory, with its stored invariants and the cursor's facts. -/
theorem backtrackPop_inv {σ : LPSignature} [DecidableEq σ.relationSymbols]
    {program : Program σ} {state : State σ} {cursor : ClauseCursor σ}
    {older : List (ClauseCursor σ)}
    (hq : QueryInv program state)
    (hchoices : state.choices = cursor :: older) :
    ∃ m₀, state.memory.restore cursor.checkpoint = .ok m₀ ∧
      QueryInv program { state with memory := m₀, choices := older, phase := .select cursor } ∧
      SelectInv program { state with memory := m₀, choices := older, phase := .select cursor } cursor := by
  have hchain := hq.chain
  rw [hchoices] at hchain
  cases hchain with
  | cons hcp hext hwf hshaped hdesc hinj hscopes hvarMap hgoal hframes
      hclauses holder =>
      rename_i m₀
      refine ⟨m₀, ?_,
        ⟨hwf, hshaped, hdesc, hinj, hscopes, hvarMap, holder⟩,
        ⟨hcp, hgoal, hframes, hclauses⟩⟩
      rw [hcp]
      exact hext.restore_exact (Heap.check_of_wellFormed hwf)
        (Heap.check_of_wellShaped hshaped)

end BoundaryLemmas


/-! ## Stage 6: the readback toolkit for the witness layer

Goal-list readback, its inversions, totality on ordered function-free
heaps, the fixed-point law (answer projections fix answer readbacks), and
atom-level naturality.  These are the interior facts of every lane
property. -/

section ReadbackToolkit

/-- Finite readback of a whole runtime goal list. -/
def readGoals {σ : LPSignature} (heap : Heap σ)
    (atoms : List (RuntimeMaterialize.RuntimeAtom σ)) :
    Except ReadbackError (List (Atom σ)) :=
  atoms.mapM (readAtom heap)

@[simp] theorem readGoals_nil {σ : LPSignature} (heap : Heap σ) :
    readGoals heap [] = .ok [] := rfl

theorem readGoals_cons_ok {σ : LPSignature} {heap : Heap σ}
    {atom : RuntimeMaterialize.RuntimeAtom σ}
    {atoms : List (RuntimeMaterialize.RuntimeAtom σ)}
    {src : List (Atom σ)}
    (h : readGoals heap (atom :: atoms) = .ok src) :
    ∃ a rest, src = a :: rest ∧ readAtom heap atom = .ok a ∧
      readGoals heap atoms = .ok rest := by
  rw [readGoals, List.mapM_cons] at h
  cases hHead : readAtom heap atom with
  | error e => rw [hHead] at h; cases h
  | ok a =>
      rw [hHead] at h
      cases hTail : atoms.mapM (readAtom heap) with
      | error e =>
          rw [hTail] at h
          cases h
      | ok rest =>
          rw [hTail] at h
          have h' : Except.ok (a :: rest) = Except.ok src := h
          cases h'
          exact ⟨a, rest, rfl, rfl, hTail⟩

theorem readGoals_cons_of {σ : LPSignature} {heap : Heap σ}
    {atom : RuntimeMaterialize.RuntimeAtom σ}
    {atoms : List (RuntimeMaterialize.RuntimeAtom σ)}
    {a : Atom σ} {rest : List (Atom σ)}
    (hHead : readAtom heap atom = .ok a)
    (hTail : readGoals heap atoms = .ok rest) :
    readGoals heap (atom :: atoms) = .ok (a :: rest) := by
  rw [readGoals, List.mapM_cons, hHead]
  rw [readGoals] at hTail
  rw [hTail]
  rfl

theorem readGoals_append_ok {σ : LPSignature} {heap : Heap σ} :
    ∀ {left right : List (RuntimeMaterialize.RuntimeAtom σ)}
      {src : List (Atom σ)},
      readGoals heap (left ++ right) = .ok src →
      ∃ srcL srcR, src = srcL ++ srcR ∧
        readGoals heap left = .ok srcL ∧ readGoals heap right = .ok srcR := by
  intro left
  induction left with
  | nil =>
      intro right src h
      exact ⟨[], src, rfl, rfl, h⟩
  | cons atom atoms ih =>
      intro right src h
      rw [List.cons_append] at h
      obtain ⟨a, rest, rfl, hHead, hTail⟩ := readGoals_cons_ok h
      obtain ⟨srcL, srcR, rfl, hL, hR⟩ := ih hTail
      exact ⟨a :: srcL, srcR, rfl, readGoals_cons_of hHead hL, hR⟩

theorem readGoals_append_of {σ : LPSignature} {heap : Heap σ} :
    ∀ {left right : List (RuntimeMaterialize.RuntimeAtom σ)}
      {srcL srcR : List (Atom σ)},
      readGoals heap left = .ok srcL → readGoals heap right = .ok srcR →
      readGoals heap (left ++ right) = .ok (srcL ++ srcR) := by
  intro left
  induction left with
  | nil =>
      intro right srcL srcR hL hR
      cases hL
      exact hR
  | cons atom atoms ih =>
      intro right srcL srcR hL hR
      obtain ⟨a, rest, rfl, hHead, hTail⟩ := readGoals_cons_ok hL
      rw [List.cons_append, List.cons_append]
      exact readGoals_cons_of hHead (ih hTail hR)

/-- Invert a successful list readback pointwise. -/
theorem readListFuel_ok_pointwise {σ : LPSignature} {heap : Heap σ}
    {fuel : Nat} :
    ∀ {addresses : List Addr} {terms : List (Term σ)},
      readListFuel heap fuel addresses = .ok terms →
      addresses.length = terms.length ∧
      ∀ k (hk : k < addresses.length) (hk' : k < terms.length),
        readTermFuel heap fuel addresses[k] = .ok terms[k] := by
  intro addresses
  induction addresses with
  | nil =>
      intro terms h
      simp only [readListFuel] at h
      cases h
      exact ⟨rfl, fun k hk _ => absurd hk (Nat.not_lt_zero k)⟩
  | cons head tailA ih =>
      intro terms h
      simp only [readListFuel, Bind.bind, Except.bind] at h
      cases hHead : readTermFuel heap fuel head with
      | error e => rw [hHead] at h; cases h
      | ok headTerm =>
          rw [hHead] at h
          cases hTail : readListFuel heap fuel tailA with
          | error e => rw [hTail] at h; cases h
          | ok tailTerms =>
              rw [hTail] at h
              cases h
              obtain ⟨hLen, hPoint⟩ := ih hTail
              refine ⟨congrArg (· + 1) hLen, ?_⟩
              intro k hk hk'
              cases k with
              | zero => simpa using hHead
              | succ k =>
                  have := hPoint k (by simpa using hk) (by simpa using hk')
                  simpa using this

/-- Invert a successful atom readback: same symbol, pointwise arguments. -/
theorem readAtom_ok_inv {σ : LPSignature} {heap : Heap σ}
    {ratom : RuntimeMaterialize.RuntimeAtom σ} {atom : Atom σ}
    (h : readAtom heap ratom = .ok atom) :
    atom.symbol = ratom.symbol ∧
    ∃ (children : List (Term σ))
      (hlen : children.length = σ.relationArity ratom.symbol),
      readListFuel heap (heap.size + 1) ratom.args.toList = .ok children ∧
      HEq atom.args (fun index => children.get (Fin.cast hlen.symm index)) := by
  unfold readAtom at h
  simp only [Bind.bind, Except.bind] at h
  cases hChildren : readListFuel heap (heap.size + 1) ratom.args.toList with
  | error e => rw [hChildren] at h; cases h
  | ok children =>
      rw [hChildren] at h
      dsimp only at h
      by_cases hlen : children.length = σ.relationArity ratom.symbol
      · rw [dif_pos hlen] at h
        cases h
        exact ⟨rfl, children, hlen, rfl, HEq.rfl⟩
      · rw [dif_neg hlen] at h
        cases h

/-- Atom readback is total for well-formed atoms over an ordered
function-free heap. -/
theorem readAtom_total {σ : LPSignature} {heap : Heap σ}
    {ratom : RuntimeMaterialize.RuntimeAtom σ}
    (hwf : ratom.WellFormed heap) (hOFF : OrderedFF heap) :
    ∃ atom, readAtom heap ratom = .ok atom := by
  have hTerms : ∀ (addresses : List Addr),
      (∀ a ∈ addresses, a < heap.size) →
      ∃ terms, readListFuel heap (heap.size + 1) addresses = .ok terms ∧
        addresses.length = terms.length := by
    intro addresses
    induction addresses with
    | nil => exact fun _ => ⟨[], by simp [readListFuel], rfl⟩
    | cons head tailA ih =>
        intro hbound
        obtain ⟨headTerm, hHead⟩ :=
          readTerm_total_of_orderedFF hOFF (hbound head (by simp))
        obtain ⟨tailTerms, hTail, hLen⟩ :=
          ih (fun a ha => hbound a (by simp [ha]))
        refine ⟨headTerm :: tailTerms, ?_, by simpa using hLen⟩
        simp only [readListFuel, Bind.bind, Except.bind]
        rw [show readTermFuel heap (heap.size + 1) head = .ok headTerm
          from hHead, hTail]
  obtain ⟨children, hChildren, hLen⟩ :=
    hTerms ratom.args.toList (fun a ha => hwf.2 a ha)
  have hlen : children.length = σ.relationArity ratom.symbol := by
    rw [← hLen]
    simpa using hwf.1
  refine ⟨⟨ratom.symbol, fun index =>
    children.get (Fin.cast hlen.symm index)⟩, ?_⟩
  unfold readAtom
  simp only [Bind.bind, Except.bind]
  rw [hChildren]
  dsimp only
  rw [dif_pos hlen]

/-- Goal-list readback is total for well-formed atoms over an ordered
function-free heap. -/
theorem readGoals_total {σ : LPSignature} {heap : Heap σ}
    {atoms : List (RuntimeMaterialize.RuntimeAtom σ)}
    (hwf : ∀ atom ∈ atoms, atom.WellFormed heap) (hOFF : OrderedFF heap) :
    ∃ src, readGoals heap atoms = .ok src := by
  induction atoms with
  | nil => exact ⟨[], rfl⟩
  | cons atom rest ih =>
      obtain ⟨a, hHead⟩ := readAtom_total (hwf atom (by simp)) hOFF
      obtain ⟨srcRest, hTail⟩ := ih (fun x hx => hwf x (by simp [hx]))
      exact ⟨a :: srcRest, readGoals_cons_of hHead hTail⟩

/-! ### The fixed-point law -/

/-- Answer projections fix answer readbacks: every free variable of a
readback denotes an unbound cell, which the projection leaves alone. -/
theorem heapSubst_fix_readTerm {σ : LPSignature} [DecidableEq σ.vars]
    {heap : Heap σ} (inj : IdentityInjective heap) {address : Addr}
    {t : Term σ} (h : Heap.readTerm heap address = .ok t) :
    (heapSubst heap).applyTerm t = t := by
  apply applyTerm_eq_self_of_freeVars
  intro w hw
  obtain ⟨b, hb⟩ :=
    readTermFuel_freeVar_unbound heap (heap.size + 1) address t h w hw
  exact heapSubst_unbound inj hb

theorem heapSubst_fix_readAtom {σ : LPSignature} [DecidableEq σ.vars]
    {heap : Heap σ} (inj : IdentityInjective heap)
    {ratom : RuntimeMaterialize.RuntimeAtom σ} {atom : Atom σ}
    (h : readAtom heap ratom = .ok atom) :
    (heapSubst heap).applyAtom atom = atom := by
  obtain ⟨hsym, children, hlen, hChildren, hargs⟩ := readAtom_ok_inv h
  obtain ⟨hLen, hPoint⟩ := readListFuel_ok_pointwise hChildren
  cases atom with
  | mk symbol args =>
      cases hsym
      simp only [Subst.applyAtom]
      congr 1
      funext index
      have hargs' : args = fun index =>
          children.get (Fin.cast hlen.symm index) := eq_of_heq hargs
      have hidx : args index = children[(Fin.cast hlen.symm index).val] := by
        rw [hargs']
        simp [List.get_eq_getElem]
      rw [hidx]
      have hk' : (Fin.cast hlen.symm index).val < children.length :=
        (Fin.cast hlen.symm index).isLt
      have hk : (Fin.cast hlen.symm index).val <
          ratom.args.toList.length := by
        rw [hLen]
        exact hk'
      exact heapSubst_fix_readTerm inj (hPoint _ hk hk')

theorem heapSubst_fix_readGoals {σ : LPSignature} [DecidableEq σ.vars]
    {heap : Heap σ} (inj : IdentityInjective heap) :
    ∀ {atoms : List (RuntimeMaterialize.RuntimeAtom σ)}
      {src : List (Atom σ)},
      readGoals heap atoms = .ok src →
      (heapSubst heap).applyAtoms src = src := by
  intro atoms
  induction atoms with
  | nil =>
      intro src h
      cases h
      rfl
  | cons atom rest ih =>
      intro src h
      obtain ⟨a, srcRest, rfl, hHead, hTail⟩ := readGoals_cons_ok h
      show (heapSubst heap).applyAtom a ::
        (heapSubst heap).applyAtoms srcRest = a :: srcRest
      rw [heapSubst_fix_readAtom inj hHead, ih hTail]

/-! ### Atom-level naturality -/

/-- Naturality at the atom level: the later readback of a runtime atom is
the later projection applied to its earlier readback. -/
theorem readAtom_naturality {σ : LPSignature} [DecidableEq σ.vars]
    {heap₀ heap₁ : Heap σ}
    (ext : BindingExtension heap₀ heap₁)
    (inj : IdentityInjective heap₁) (ff : FunctionFree heap₁)
    {ratom : RuntimeMaterialize.RuntimeAtom σ} {a₀ a₁ : Atom σ}
    (h₀ : readAtom heap₀ ratom = .ok a₀)
    (h₁ : readAtom heap₁ ratom = .ok a₁) :
    a₁ = (heapSubst heap₁).applyAtom a₀ := by
  obtain ⟨hsym₀, children₀, hlen₀, hChildren₀, hargs₀⟩ := readAtom_ok_inv h₀
  obtain ⟨hsym₁, children₁, hlen₁, hChildren₁, hargs₁⟩ := readAtom_ok_inv h₁
  obtain ⟨hLen₀, hPoint₀⟩ := readListFuel_ok_pointwise hChildren₀
  obtain ⟨hLen₁, hPoint₁⟩ := readListFuel_ok_pointwise hChildren₁
  cases a₀ with
  | mk symbol₀ args₀ =>
      cases a₁ with
      | mk symbol₁ args₁ =>
          cases hsym₀
          cases hsym₁
          simp only [Subst.applyAtom]
          congr 1
          funext index
          have hargs₀' : args₀ = fun index =>
              children₀.get (Fin.cast hlen₀.symm index) := eq_of_heq hargs₀
          have hargs₁' : args₁ = fun index =>
              children₁.get (Fin.cast hlen₁.symm index) := eq_of_heq hargs₁
          rw [hargs₀', hargs₁']
          simp only [List.get_eq_getElem]
          have hk₁ : (Fin.cast hlen₁.symm index).val < children₁.length :=
            (Fin.cast hlen₁.symm index).isLt
          have hk₀ : (Fin.cast hlen₀.symm index).val < children₀.length :=
            (Fin.cast hlen₀.symm index).isLt
          have hb₀ : (Fin.cast hlen₀.symm index).val <
              ratom.args.toList.length := by
            rw [hLen₀]; exact hk₀
          have hb₁ : (Fin.cast hlen₁.symm index).val <
              ratom.args.toList.length := by
            rw [hLen₁]; exact hk₁
          have hr₀ := hPoint₀ _ hb₀ hk₀
          have hr₁ := hPoint₁ _ hb₁ hk₁
          exact (readback_naturality ext inj ff hr₀ hr₁).symm

/-! ### Small bridges -/

/-- Prefix-preserving growth is a binding extension (with no bindings). -/
theorem bindingExtension_of_prefix {σ : LPSignature}
    {heap₀ heap₁ : Heap σ}
    (hprefix : ∀ i, i < heap₀.size → heap₁[i]? = heap₀[i]?)
    (hle : heap₀.size ≤ heap₁.size) : BindingExtension heap₀ heap₁ :=
  ⟨hle, fun a cell hc => .inl (by
    rw [hprefix a (lt_of_getElem?_some hc)]
    exact hc)⟩

/-- Selected clauses are program clauses. -/
theorem clausesFor_mem_program {σ : LPSignature}
    [DecidableEq σ.relationSymbols] {program : Program σ}
    {symbol : σ.relationSymbols} {c : Clause σ}
    (h : c ∈ RuntimeQuery.clausesFor program symbol) : c ∈ program :=
  (List.mem_filter.mp h).1

end ReadbackToolkit

/-! ## Stage 6: lanes — root-connectible resolvents

A lane is a live runtime resolvent (the current control, or a stored
cursor) together with the proof that any scoped derivation of its readback
extends to a derivation of the *root* query.  The lane property quantifies
over every future heap `H` reachable by bindings from the lane's anchor —
never over the eventual answer — which is what makes it maintainable
forward: lanes whose subtrees die are simply never consumed. -/

section LaneMachinery

open RuntimeQuery

/-- The runtime resolvent of the live control: current goals, then every
stored continuation in return order. -/
def flattenControl {σ : LPSignature} (control : Control σ) :
    List (RuntimeMaterialize.RuntimeAtom σ.scoped) :=
  control.current ++ control.frames.flatMap (·.continuation)

/-- The runtime resolvent a cursor will retry: its goal, then its stored
continuations. -/
def cursorResolvent {σ : LPSignature} (cursor : ClauseCursor σ) :
    List (RuntimeMaterialize.RuntimeAtom σ.scoped) :=
  cursor.goal :: cursor.frames.flatMap (·.continuation)

/-- **The lane property.**  For every binding-extension `H` of the anchor
that is injective and ordered function-free, every scoped derivation of the
lane's readback at `H` (at any scope past the barrier) yields a derivation
of the root at scope 1 whose answer agrees with the derivation's
substitution composed with `H`'s projection, on the query variables. -/
def LaneOk {σ : LPSignature} [DecidableEq σ.vars] (program : Program σ)
    (root : List (Atom σ.scoped)) (keys : List (ScopedVar σ.vars))
    (anchor : Heap σ.scoped) (barrier : Nat)
    (res : List (RuntimeMaterialize.RuntimeAtom σ.scoped)) : Prop :=
  ∀ (H : Heap σ.scoped), BindingExtension anchor H →
    IdentityInjective H → DescendingOrConst H → FunctionFree H →
    ∀ (s : Nat), barrier ≤ s →
    ∀ (θ' : Subst σ.scoped) (src : List (Atom σ.scoped)),
      readGoals H res = .ok src →
      SLDScopedTree program s src θ' →
      ∃ Θ, SLDScopedTree program 1 root Θ ∧
        ∀ v ∈ keys, Θ v = (θ' ∘ₛ heapSubst H) v

/-- Slide the anchor forward along a binding extension. -/
theorem LaneOk.anchor_slide {σ : LPSignature} [DecidableEq σ.vars]
    {program : Program σ} {root : List (Atom σ.scoped)}
    {keys : List (ScopedVar σ.vars)} {anchor anchor' : Heap σ.scoped}
    {barrier : Nat} {res : List (RuntimeMaterialize.RuntimeAtom σ.scoped)}
    (h : LaneOk program root keys anchor barrier res)
    (hext : BindingExtension anchor anchor') :
    LaneOk program root keys anchor' barrier res :=
  fun H hB => h H (hext.trans hB)

/-- Raise the barrier. -/
theorem LaneOk.barrier_mono {σ : LPSignature} [DecidableEq σ.vars]
    {program : Program σ} {root : List (Atom σ.scoped)}
    {keys : List (ScopedVar σ.vars)} {anchor : Heap σ.scoped}
    {barrier barrier' : Nat}
    {res : List (RuntimeMaterialize.RuntimeAtom σ.scoped)}
    (hle : barrier ≤ barrier')
    (h : LaneOk program root keys anchor barrier res) :
    LaneOk program root keys anchor barrier' res :=
  fun H hB hinj hdesc hff s hs =>
    h H hB hinj hdesc hff s (Nat.le_trans hle hs)

/-- The choice stack's lanes, anchored like `ChoiceChain`: each cursor
stores the memory its checkpoint denotes together with its lane property
at that anchor.  Restoration re-identifies the two chains' memories via
exact restoration. -/
inductive LaneChain {σ : LPSignature} [DecidableEq σ.vars]
    (program : Program σ) (root : List (Atom σ.scoped))
    (keys : List (ScopedVar σ.vars)) :
    Nat → List (ClauseCursor σ) → Memory σ.scoped → Prop
  | nil (bound : Nat) (memory : Memory σ.scoped) :
      LaneChain program root keys bound [] memory
  | cons {bound : Nat} {cursor : ClauseCursor σ}
      {older : List (ClauseCursor σ)} {memory m₀ : Memory σ.scoped}
      {barrier : Nat}
      (hext : Extends m₀ memory)
      (hcp : cursor.checkpoint = m₀.checkpoint)
      (hwf : Heap.WellFormed m₀.heap)
      (hshaped : Heap.WellShaped m₀.heap)
      (hbarrier : barrier ≤ bound)
      (hlane : LaneOk program root keys m₀.heap barrier
        (cursorResolvent cursor))
      (holder : LaneChain program root keys bound older m₀) :
      LaneChain program root keys bound (cursor :: older) memory

/-- Re-anchor the lane chain along a further extension. -/
theorem LaneChain.anchor {σ : LPSignature} [DecidableEq σ.vars]
    {program : Program σ} {root : List (Atom σ.scoped)}
    {keys : List (ScopedVar σ.vars)} {bound : Nat}
    {choices : List (ClauseCursor σ)} {memory memory' : Memory σ.scoped}
    (h : LaneChain program root keys bound choices memory)
    (hextM : Extends memory memory') :
    LaneChain program root keys bound choices memory' := by
  cases h with
  | nil => exact .nil bound memory'
  | cons hext hcp hwf hshaped hbarrier hlane holder =>
      exact .cons (hext.trans hextM) hcp hwf hshaped hbarrier hlane holder

/-- Lift the lane chain's scope bound. -/
theorem LaneChain.scope_mono {σ : LPSignature} [DecidableEq σ.vars]
    {program : Program σ} {root : List (Atom σ.scoped)}
    {keys : List (ScopedVar σ.vars)} {bound bound' : Nat}
    {choices : List (ClauseCursor σ)} {memory : Memory σ.scoped}
    (hle : bound ≤ bound')
    (h : LaneChain program root keys bound choices memory) :
    LaneChain program root keys bound' choices memory := by
  induction h with
  | nil => exact .nil bound' _
  | cons hext hcp hwf hshaped hbarrier hlane holder ih =>
      exact .cons hext hcp hwf hshaped (Nat.le_trans hbarrier hle) hlane ih

/-- Consume the top lane at a backtrack: exact restoration re-identifies
the stored anchor with the restored memory. -/
theorem LaneChain.pop {σ : LPSignature} [DecidableEq σ.vars]
    {program : Program σ} {root : List (Atom σ.scoped)}
    {keys : List (ScopedVar σ.vars)} {bound : Nat}
    {cursor : ClauseCursor σ} {older : List (ClauseCursor σ)}
    {memory m₀ : Memory σ.scoped}
    (h : LaneChain program root keys bound (cursor :: older) memory)
    (hrestore : memory.restore cursor.checkpoint = .ok m₀) :
    (∃ barrier, barrier ≤ bound ∧
      LaneOk program root keys m₀.heap barrier (cursorResolvent cursor)) ∧
    LaneChain program root keys bound older m₀ := by
  cases h with
  | cons hext hcp hwf hshaped hbarrier hlane holder =>
      rename_i m₀' barrier
      have hres' : memory.restore cursor.checkpoint = .ok m₀' := by
        rw [hcp]
        exact hext.restore_exact (Heap.check_of_wellFormed hwf)
          (Heap.check_of_wellShaped hshaped)
      rw [hrestore] at hres'
      injection hres' with hres'
      cases hres'
      exact ⟨⟨barrier, hbarrier, hlane⟩, holder⟩

/-- The full lane invariant of a state: the live control's lane at the
current memory, plus the stored cursor lanes. -/
def Lanes {σ : LPSignature} [DecidableEq σ.vars] (program : Program σ)
    (root : List (Atom σ.scoped)) (keys : List (ScopedVar σ.vars))
    (state : State σ) : Prop :=
  (∃ barrier, barrier ≤ state.nextScope ∧
    LaneOk program root keys state.memory.heap barrier
      (flattenControl state.control)) ∧
  LaneChain program root keys state.nextScope state.choices state.memory

end LaneMachinery

/-! ## Stage 6: the root lane

The endpoint judgment is pinned at scope 1, but after failed clauses the
runtime's first surviving activation runs at a later scope.  Only the root
node's index is pinned — deeper nodes may use any strictly larger scope —
so one substitution override re-expresses the surviving activation at
scope 1: on scope-1 names it behaves as the derivation's step substitution
did on the actual activation names, elsewhere as the composed answer.
Query variables live at scope 0, untouched by the override. -/

section RootLane

open RuntimeQuery

/-- Pointwise inversion of a successful goal-list readback. -/
theorem readGoals_ok_pointwise {σ : LPSignature} {heap : Heap σ} :
    ∀ {atoms : List (RuntimeMaterialize.RuntimeAtom σ)}
      {src : List (Atom σ)},
      readGoals heap atoms = .ok src →
      atoms.length = src.length ∧
      ∀ k (hk : k < atoms.length) (hk' : k < src.length),
        readAtom heap atoms[k] = .ok src[k] := by
  intro atoms
  induction atoms with
  | nil =>
      intro src h
      cases h
      exact ⟨rfl, fun k hk _ => absurd hk (Nat.not_lt_zero k)⟩
  | cons atom rest ih =>
      intro src h
      obtain ⟨a, srcRest, rfl, hHead, hTail⟩ := readGoals_cons_ok h
      obtain ⟨hLen, hPoint⟩ := ih hTail
      refine ⟨congrArg (· + 1) hLen, ?_⟩
      intro k hk hk'
      cases k with
      | zero => simpa using hHead
      | succ k =>
          have := hPoint k (by simpa using hk) (by simpa using hk')
          simpa using this

/-- Substitutions agreeing on a term's variables act identically on it. -/
theorem Subst.applyTerm_congr {σ : LPSignature} [DecidableEq σ.vars]
    {θ θ' : Subst σ} :
    ∀ {t : Term σ}, (∀ v ∈ t.freeVars, θ v = θ' v) →
      θ.applyTerm t = θ'.applyTerm t := by
  intro t
  induction t with
  | var v =>
      intro h
      simpa [Subst.applyTerm] using h v (by simp [Term.freeVars])
  | const c => intro _; rfl
  | app f ts ih =>
      intro h
      simp only [Subst.applyTerm]
      congr 1
      funext i
      exact ih i (fun v hv => h v (by
        simp only [Term.freeVars, Finset.mem_biUnion, Finset.mem_univ,
          true_and]
        exact ⟨i, hv⟩))

theorem Subst.applyAtom_congr {σ : LPSignature} [DecidableEq σ.vars]
    {θ θ' : Subst σ} {a : Atom σ}
    (h : ∀ v ∈ a.freeVars, θ v = θ' v) :
    θ.applyAtom a = θ'.applyAtom a := by
  cases a with
  | mk symbol args =>
      simp only [Subst.applyAtom]
      congr 1
      funext i
      exact Subst.applyTerm_congr (fun v hv => h v
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩))

/-- Substitutions agreeing across a scope renaming act identically on the
two scoped copies. -/
theorem applyTerm_atScope_reindex {σ : LPSignature} [DecidableEq σ.vars]
    {θA θB : Subst σ.scoped} {s₁ s₂ : Nat}
    (h : ∀ name : σ.vars, θA (ScopedVar.at s₁ name) =
      θB (ScopedVar.at s₂ name)) :
    ∀ (t : Term σ),
      θA.applyTerm (Term.atScope s₁ t) =
        θB.applyTerm (Term.atScope s₂ t) := by
  intro t
  induction t with
  | var v =>
      simpa [Term.atScope, Term.renameVars_var, Subst.applyTerm] using h v
  | const c => rfl
  | app f ts ih =>
      simp only [Term.atScope, Term.renameVars_app, Subst.applyTerm]
      congr 1
      funext i
      exact ih i

theorem applyAtom_atScope_reindex {σ : LPSignature} [DecidableEq σ.vars]
    {θA θB : Subst σ.scoped} {s₁ s₂ : Nat}
    (h : ∀ name : σ.vars, θA (ScopedVar.at s₁ name) =
      θB (ScopedVar.at s₂ name))
    (a : Atom σ) :
    θA.applyAtom (Atom.atScope s₁ a) = θB.applyAtom (Atom.atScope s₂ a) := by
  cases a with
  | mk symbol args =>
      simp only [Atom.atScope, Atom.renameVars, Subst.applyAtom]
      congr 1
      funext i
      exact applyTerm_atScope_reindex h (args i)

/-- **Scope-1 re-expression of the surviving root activation.**  A cons of
the projected root at any scope `s ≥ 1` rebuilds at scope 1: the override
substitution behaves on scope-1 names as the step substitution did on the
scope-`s` names.  Scope-0 (query) values are untouched. -/
theorem root_cons_reindex {σ : LPSignature} [DecidableEq σ.vars]
    {program : Program σ} {a : Atom σ.scoped}
    {rootRest : List (Atom σ.scoped)} {H : Heap σ.scoped}
    {s next : Nat} {c : Clause σ} {θ₁ θ₁' : Subst σ.scoped}
    (hs : 1 ≤ s)
    (hA : ∀ v ∈ a.freeVars, v.scope = 0)
    (hRest : ∀ atom ∈ rootRest, ∀ v ∈ atom.freeVars, v.scope = 0)
    (hfresh : s < next) (hc : c ∈ program)
    (hunif : θ₁.applyAtom ((heapSubst H).applyAtom a) =
      θ₁.applyAtom (c.head.atScope s))
    (hrest : SLDScopedTree program next
      (θ₁.applyAtoms ((c.body.map (Atom.atScope s)) ++
        (heapSubst H).applyAtoms rootRest)) θ₁') :
    ∃ Θ, SLDScopedTree program 1 (a :: rootRest) Θ ∧
      ∀ v : ScopedVar σ.vars, v.scope = 0 →
        Θ v = ((θ₁' ∘ₛ θ₁) ∘ₛ heapSubst H) v := by
  set θnew : Subst σ.scoped := fun w =>
    if w.scope = 1 then θ₁ (ScopedVar.at s w.name)
    else (θ₁ ∘ₛ heapSubst H) w with hθnew
  have hzero : ∀ v : ScopedVar σ.vars, v.scope = 0 →
      θnew v = (θ₁ ∘ₛ heapSubst H) v := by
    intro v h0
    simp only [hθnew]
    rw [if_neg (by simp [h0])]
  refine ⟨θ₁' ∘ₛ θnew, ?_, ?_⟩
  · refine SLDScopedTree.cons 1 next a rootRest c θnew θ₁'
      (Nat.lt_of_le_of_lt hs hfresh) hc ?_ ?_
    · have hLHS : θnew.applyAtom a =
          θ₁.applyAtom ((heapSubst H).applyAtom a) := by
        rw [← Subst.applyAtom_comp]
        exact Subst.applyAtom_congr (fun v hv => hzero v (hA v hv))
      have hRHS : θnew.applyAtom (c.head.atScope 1) =
          θ₁.applyAtom (c.head.atScope s) := by
        apply applyAtom_atScope_reindex
        intro name
        simp only [hθnew]
        rw [if_pos (ScopedVar.at_scope 1 name)]
        rfl
      rw [hLHS, hRHS]
      exact hunif
    · have hSubject :
          θnew.applyAtoms ((c.body.map (Atom.atScope 1)) ++ rootRest) =
          θ₁.applyAtoms ((c.body.map (Atom.atScope s)) ++
            (heapSubst H).applyAtoms rootRest) := by
        simp only [Subst.applyAtoms, List.map_append, List.map_map]
        congr 1
        · apply List.map_congr_left
          intro atom _
          show θnew.applyAtom (atom.atScope 1) =
            θ₁.applyAtom (atom.atScope s)
          apply applyAtom_atScope_reindex
          intro name
          simp only [hθnew]
          rw [if_pos (ScopedVar.at_scope 1 name)]
          rfl
        · apply List.map_congr_left
          intro atom hatom
          show θnew.applyAtom atom =
            (θ₁.applyAtom ∘ (heapSubst H).applyAtom) atom
          rw [Function.comp_apply, ← Subst.applyAtom_comp]
          exact Subst.applyAtom_congr
            (fun v hv => hzero v (hRest atom hatom v hv))
      rw [hSubject]
      exact hrest
  · intro v h0
    show θ₁'.applyTerm (θnew v) = ((θ₁' ∘ₛ θ₁) ∘ₛ heapSubst H) v
    rw [hzero v h0]
    simp [Subst.comp, Subst.applyTerm_comp]

/-- **The root lane**: the materialized query is root-connectible from its
own memory at barrier 1. -/
theorem rootLane_initial {σ : LPSignature} [DecidableEq σ.vars]
    {program : Program σ} {goals : List (Atom σ)}
    {result : MaterializedGoals σ.scoped}
    (keys : List (ScopedVar σ.vars))
    (hKeys : ∀ v ∈ keys, v.scope = 0)
    (hKeysEmpty : goals = [] → keys = [])
    (hMat : materializeGoals (Memory.empty σ.scoped)
      (queryAtScope 0 goals) = .ok result) :
    LaneOk program (queryAtScope 0 goals) keys result.memory.heap 1
      result.goals := by
  intro H hB hinj hdesc hff s hs θ' src hread D
  obtain ⟨_, hLen, hPoint, _, _⟩ := materializeGoals_roundtrip hMat
  obtain ⟨hLenH, hPointH⟩ := readGoals_ok_pointwise hread
  have hsrc : src = (heapSubst H).applyAtoms (queryAtScope 0 goals) := by
    have hLenQ : (queryAtScope 0 goals).length = result.goals.length :=
      hLen.symm
    apply List.ext_getElem
    · simp only [Subst.applyAtoms, List.length_map]
      rw [← hLenH, ← hLenQ]
    · intro k hk hk'
      simp only [Subst.applyAtoms, List.getElem_map] at hk' ⊢
      have hkG : k < result.goals.length := by
        rw [hLenH]
        exact hk
      have hkQ : k < (queryAtScope 0 goals).length := by
        simp only [List.length_map] at hk'
        exact hk'
      have h₀ := hPoint k hkG hkQ
      have h₁ := hPointH k hkG hk
      exact readAtom_naturality hB hinj hff h₀ h₁
  cases hroot : queryAtScope 0 goals with
  | nil =>
      have hGoalsNil : goals = [] := by
        cases goals with
        | nil => rfl
        | cons g gs => simp [queryAtScope] at hroot
      rw [hroot] at hsrc
      have hsrcNil : src = [] := by simpa [Subst.applyAtoms] using hsrc
      subst hsrcNil
      cases D with
      | nil =>
          refine ⟨Subst.id σ.scoped, .nil 1, ?_⟩
          intro v hv
          rw [hKeysEmpty hGoalsNil] at hv
          cases hv
  | cons a rootRest =>
      have haMem : a ∈ queryAtScope 0 goals := by
        rw [hroot]
        exact List.mem_cons_self ..
      obtain ⟨g, _, hga⟩ := List.mem_map.mp haMem
      have hA : ∀ v ∈ a.freeVars, v.scope = 0 := by
        intro v hv
        rw [← hga] at hv
        exact Atom.freeVars_atScope 0 g v hv
      have hRest : ∀ atom ∈ rootRest, ∀ v ∈ atom.freeVars, v.scope = 0 := by
        intro atom hatom v hv
        have hMem : atom ∈ queryAtScope 0 goals := by
          rw [hroot]
          exact List.mem_cons_of_mem _ hatom
        obtain ⟨g', _, hg'⟩ := List.mem_map.mp hMem
        rw [← hg'] at hv
        exact Atom.freeVars_atScope 0 g' v hv
      rw [hroot] at hsrc
      have hsrcCons : src = (heapSubst H).applyAtom a ::
          (heapSubst H).applyAtoms rootRest := by
        simpa [Subst.applyAtoms] using hsrc
      subst hsrcCons
      cases D with
      | cons _ next _ _ c θ₁ θ₁' hfresh hc hunif₁ hrest₁ =>
          obtain ⟨Θ, hΘ, hAgree⟩ := root_cons_reindex hs hA hRest hfresh
            hc hunif₁ hrest₁
          exact ⟨Θ, hΘ, fun v hv => hAgree v (hKeys v hv)⟩

end RootLane

/-! ## Stage 6: the cons transfer

One successful clause selection extends the SLD derivation by one node.
The continuation lane (clause body before the stored continuations, at the
successor scope, anchored at the unified memory) is root-connectible
because the parent lane was: the head unification's readback equalities
lift to any admissible future heap by naturality, and the projected
substitution telescopes by idempotence. -/

section ConsTransfer

open RuntimeQuery

/-- Two runtime atoms with one symbol and pointwise-equal argument
readbacks read back to the same atom. -/
theorem readAtom_eq_of_args {σ : LPSignature} {heap : Heap σ}
    {ra rb : RuntimeMaterialize.RuntimeAtom σ} {a b : Atom σ}
    (hsym : ra.symbol = rb.symbol)
    (hpoint : ∀ k, k < ra.args.toList.length →
      k < rb.args.toList.length → ∀ (ta tb : Term σ),
      readTermFuel heap (heap.size + 1) ra.args.toList[k]! = .ok ta →
      readTermFuel heap (heap.size + 1) rb.args.toList[k]! = .ok tb →
      ta = tb)
    (ha : readAtom heap ra = .ok a) (hb : readAtom heap rb = .ok b) :
    a = b := by
  obtain ⟨rsa, rargsA⟩ := ra
  obtain ⟨rsb, rargsB⟩ := rb
  simp only at hsym
  subst hsym
  obtain ⟨hsa, childrenA, hlenA, hChA, hargsA⟩ := readAtom_ok_inv ha
  obtain ⟨hsb, childrenB, hlenB, hChB, hargsB⟩ := readAtom_ok_inv hb
  obtain ⟨hLA, hPA⟩ := readListFuel_ok_pointwise hChA
  obtain ⟨hLB, hPB⟩ := readListFuel_ok_pointwise hChB
  cases a with
  | mk sa argsA =>
      cases b with
      | mk sb argsB =>
          simp only at hsa hsb
          subst hsa
          subst hsb
          have hargsA' := eq_of_heq hargsA
          have hargsB' := eq_of_heq hargsB
          subst hargsA'
          subst hargsB'
          refine congrArg (Atom.mk _) ?_
          funext index
          have hkA : ((Fin.cast hlenA.symm index) :
              Fin childrenA.length).val < childrenA.length :=
            (Fin.cast hlenA.symm index).isLt
          have hkB : ((Fin.cast hlenB.symm index) :
              Fin childrenB.length).val < childrenB.length :=
            (Fin.cast hlenB.symm index).isLt
          have hbA : index.val < rargsA.toList.length := by
            rw [hLA]
            exact hkA
          have hbB : index.val < rargsB.toList.length := by
            rw [hLB]
            exact hkB
          have hrA := hPA index.val hbA hkA
          have hrB := hPB index.val hbB hkB
          simp only [List.get_eq_getElem]
          have := hpoint index.val hbA hbB
            childrenA[index.val] childrenB[index.val]
            (by rw [getElem!_pos rargsA.toList index.val hbA]; exact hrA)
            (by rw [getElem!_pos rargsB.toList index.val hbB]; exact hrB)
          exact this

/-- **The cons transfer.**  A successful clause selection turns the parent
lane into the continuation lane: body goals before the stored
continuations, successor barrier, anchored at the unified memory. -/
theorem laneCons_transfer {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols] [IsEmpty σ.functionSymbols]
    {program : Program σ} {root : List (Atom σ.scoped)}
    {keys : List (ScopedVar σ.vars)}
    {m₀ m₁ : Memory σ.scoped} {cursor : ClauseCursor σ}
    {clause : Clause σ} {copied : MaterializedClause σ.scoped}
    {activation barrier k : Nat}
    (hbarrier : barrier ≤ activation)
    (hMat : materializeClause m₀ (clause.atScope activation) = .ok copied)
    (hrun : RuntimeUnification.runSteps k
      (RuntimeUnification.startMany copied.memory
        (cursor.goal.args.toList.zip copied.clause.head.args.toList)) =
      .terminal (.success m₁))
    (hPredicate : cursor.goal.symbol = copied.clause.head.symbol)
    (hArity : cursor.goal.args.size = copied.clause.head.args.size)
    (hclause : clause ∈ program)
    (hGoalWF : cursor.goal.WellFormed m₀.heap)
    (hDesc₁ : DescendingOrConst m₁.heap)
    (hlane : LaneOk program root keys m₀.heap barrier
      (cursorResolvent cursor)) :
    LaneOk program root keys m₁.heap (activation + 1)
      (copied.clause.body ++ cursor.frames.flatMap (·.continuation)) := by
  intro H hB hinjH hdescH hffH s' hs' θ'' src'' hread'' D''
  obtain ⟨hPrefix, hSizeLe, hClauseWF, _, _, _⟩ := materializeClause_facts hMat
  have hBmat : BindingExtension m₀.heap copied.memory.heap :=
    bindingExtension_of_prefix hPrefix hSizeLe
  obtain ⟨hBuni, _, hSizeEq⟩ :=
    startMany_success_extension k copied.memory _ m₁ hrun
  have hB1H : BindingExtension m₁.heap H := hB
  have hBcH : BindingExtension copied.memory.heap H := hBuni.trans hB1H
  have hB0H : BindingExtension m₀.heap H := hBmat.trans hBcH
  have hOFF_H : OrderedFF H := ⟨hdescH, hffH⟩
  have hOFF₁ : OrderedFF m₁.heap := ⟨hDesc₁, functionFree_of_isEmpty _⟩
  obtain ⟨srcBody, srcRest, rfl, hreadBody, hreadRest⟩ :=
    readGoals_append_ok hread''
  -- goal atom at H
  have hGoalWF_H : cursor.goal.WellFormed H :=
    RuntimeAtom.wellFormed_mono hB0H.1 hGoalWF
  obtain ⟨ga, hga⟩ := readAtom_total hGoalWF_H hOFF_H
  -- head atom at H
  have hHeadWF_c : copied.clause.head.WellFormed copied.memory.heap :=
    hClauseWF.1
  have hHeadWF_H : copied.clause.head.WellFormed H :=
    RuntimeAtom.wellFormed_mono hBcH.1 hHeadWF_c
  obtain ⟨haH, hhaH⟩ := readAtom_total hHeadWF_H hOFF_H
  obtain ⟨_, hHeadRead, hBodyLen, hBodyPoint, _, _⟩ :=
    materializeClause_roundtrip hMat
  have hK2 := startMany_success_readTerm_eq k copied.memory _ m₁
    (functionFree_of_isEmpty _) hrun
  -- the unified head equals the goal in every admissible future heap
  have hAtomEq : ga = haH := by
    refine readAtom_eq_of_args hPredicate ?_ hga hhaH
    intro j hjG hjH ta tb hta htb
    have hjG' : j < cursor.goal.args.size := by
      simpa using hjG
    have hjH' : j < copied.clause.head.args.size := by
      simpa using hjH
    have haddrG : cursor.goal.args.toList[j] < m₀.heap.size :=
      hGoalWF.2 _ (List.getElem_mem hjG)
    have haddrH : copied.clause.head.args.toList[j] <
        copied.memory.heap.size :=
      hHeadWF_c.2 _ (List.getElem_mem hjH)
    have haddrG₁ : cursor.goal.args.toList[j] < m₁.heap.size :=
      Nat.lt_of_lt_of_le haddrG (hBmat.trans hBuni).1
    have haddrH₁ : copied.clause.head.args.toList[j] < m₁.heap.size :=
      Nat.lt_of_lt_of_le haddrH hBuni.1
    obtain ⟨tl, htl⟩ := readTerm_total_of_orderedFF hOFF₁ haddrG₁
    obtain ⟨tr, htr⟩ := readTerm_total_of_orderedFF hOFF₁ haddrH₁
    have hjZ : j < (cursor.goal.args.toList.zip
        copied.clause.head.args.toList).length := by
      simp only [List.length_zip, Array.length_toList]
      omega
    have hpair : (cursor.goal.args.toList[j],
        copied.clause.head.args.toList[j]) ∈
        cursor.goal.args.toList.zip copied.clause.head.args.toList := by
      have := List.getElem_mem hjZ
      rwa [List.getElem_zip] at this
    have heqm₁ : tl = tr := hK2 _ hpair tl tr htl htr
    rw [getElem!_pos cursor.goal.args.toList j hjG] at hta
    rw [getElem!_pos copied.clause.head.args.toList j hjH] at htb
    have hnatL := readback_naturality hB1H hinjH hffH htl hta
    have hnatR := readback_naturality hB1H hinjH hffH htr htb
    rw [← hnatL, ← hnatR, heqm₁]
  -- the body readback is the projected scoped body
  have hbodyDef : (clause.atScope activation).body =
      clause.body.map (Atom.atScope activation) := rfl
  have hBodyEq : srcBody = (heapSubst H).applyAtoms
      (clause.body.map (Atom.atScope activation)) := by
    obtain ⟨hLenB, hPointB⟩ := readGoals_ok_pointwise hreadBody
    apply List.ext_getElem
    · simp only [Subst.applyAtoms, List.length_map]
      rw [← hLenB, hBodyLen, hbodyDef, List.length_map]
    · intro j hj hj'
      have hjB : j < copied.clause.body.length := by
        rw [hLenB]
        exact hj
      have hjS : j < (clause.atScope activation).body.length := by
        rw [← hBodyLen]
        exact hjB
      have h₀ := hBodyPoint j hjB hjS
      have h₁ := hPointB j hjB hj
      have hnat := readAtom_naturality hBcH hinjH hffH h₀ h₁
      rw [hnat]
      simp only [Subst.applyAtoms, List.getElem_map]
      congr 1
      have hjC : j < clause.body.length := by
        have hjS' := hjS
        rw [hbodyDef, List.length_map] at hjS'
        exact hjS'
      show (clause.body.map (Atom.atScope activation))[j]'(hbodyDef ▸ hjS) =
        Atom.atScope activation (clause.body[j]'hjC)
      simp
  have hRestFix : (heapSubst H).applyAtoms srcRest = srcRest :=
    heapSubst_fix_readGoals hinjH hreadRest
  have hfresh : activation < s' := Nat.lt_of_lt_of_le
    (Nat.lt_succ_self _) hs'
  have hunifNode : (heapSubst H).applyAtom ga =
      (heapSubst H).applyAtom (clause.head.atScope activation) := by
    rw [heapSubst_fix_readAtom hinjH hga, hAtomEq]
    exact readAtom_naturality hBcH hinjH hffH hHeadRead hhaH
  have happend : (heapSubst H).applyAtoms
      ((clause.body.map (Atom.atScope activation)) ++ srcRest) =
      (heapSubst H).applyAtoms (clause.body.map (Atom.atScope activation))
        ++ (heapSubst H).applyAtoms srcRest := by
    simp [Subst.applyAtoms]
  have hrestNode : SLDScopedTree program s'
      ((heapSubst H).applyAtoms
        ((clause.body.map (Atom.atScope activation)) ++ srcRest)) θ'' := by
    rw [happend, ← hBodyEq, hRestFix]
    exact D''
  have hNode := SLDScopedTree.cons activation s' ga srcRest clause
    (heapSubst H) θ'' hfresh hclause hunifNode hrestNode
  have hreadParent : readGoals H (cursorResolvent cursor) =
      .ok (ga :: srcRest) :=
    readGoals_cons_of hga hreadRest
  obtain ⟨Θ, hΘ, hAg⟩ := hlane H hB0H hinjH hdescH hffH activation hbarrier
    (θ'' ∘ₛ heapSubst H) (ga :: srcRest) hreadParent hNode
  refine ⟨Θ, hΘ, ?_⟩
  intro v hv
  rw [hAg v hv]
  show ((θ'' ∘ₛ heapSubst H) ∘ₛ heapSubst H) v = (θ'' ∘ₛ heapSubst H) v
  rw [Subst.comp_assoc, heapSubst_idem hinjH]

end ConsTransfer

/-! ## Stage 6: the run induction

One strong induction over `pull`'s fuel carries the boundary invariant,
the per-phase data, and the lanes.  The answer arm consumes the live lane
at the yielded memory itself; the clause-selection arm extracts the whole
unifier run and transfers the lane by one SLD node; backtracking pops both
chains in step, restoring exactly. -/

section RunInduction

open RuntimeQuery

/-- Per-phase data of the run induction: control bounds and the live lane
at dispatch; the cursor's facts and lane at select; nothing at the
transient phases; unifying states are never entered by the induction. -/
def PhaseLane {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.relationSymbols] (program : Program σ)
    (root : List (Atom σ.scoped)) (keys : List (ScopedVar σ.vars))
    (state : State σ) : Prop :=
  match state.phase with
  | .dispatch => ControlWF state ∧ ∃ barrier, barrier ≤ state.nextScope ∧
      LaneOk program root keys state.memory.heap barrier
        (flattenControl state.control)
  | .select cursor => SelectInv program state cursor ∧
      ∃ barrier, barrier ≤ state.nextScope ∧
      LaneOk program root keys state.memory.heap barrier
        (cursorResolvent cursor)
  | .backtrack => True
  | .afterAnswer => True
  | .unifying _ _ => False

/-- Popping a return frame preserves the flattened resolvent. -/
theorem flatten_framePop {σ : LPSignature} {control : Control σ}
    {frame : ReturnFrame σ} {frames' : List (ReturnFrame σ)}
    (hcurrent : control.current = [])
    (hframes : control.frames = frame :: frames') (d : Nat) :
    flattenControl ({ current := frame.continuation, cutDepth := d, frames := frames' } : Control σ) =
      flattenControl control := by
  simp [flattenControl, hcurrent, hframes]

/-- Packaging a call into a cursor preserves the flattened resolvent. -/
theorem flatten_callCursor {σ : LPSignature}
    [DecidableEq σ.relationSymbols] (program : Program σ)
    {state : State σ}
    {goal : RuntimeMaterialize.RuntimeAtom σ.scoped}
    {rest : List (RuntimeMaterialize.RuntimeAtom σ.scoped)}
    (hcurrent : state.control.current = goal :: rest) :
    cursorResolvent ({
      checkpoint := state.memory.checkpoint
      goal
      clauses := RuntimeQuery.clausesFor program goal.symbol
      cutDepth := state.choices.length
      frames := { continuation := rest, callerCutDepth := state.control.cutDepth } :: state.control.frames
    } : ClauseCursor σ) = flattenControl state.control := by
  simp [cursorResolvent, flattenControl, hcurrent, List.flatMap_cons]

/-- **The run induction**: from any invariant state, a pulled answer is a
scope-1 derivation of the root whose substitution answers the query
variables exactly as the yielded memory reads them. -/
theorem pull_root_sound {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols] [IsEmpty σ.functionSymbols]
    (builtins : Builtins σ) (program : Program σ)
    (hCutFree : ∀ symbol, builtins.isCut symbol = false)
    (root : List (Atom σ.scoped)) (keys : List (ScopedVar σ.vars)) :
    ∀ (fuel : Nat) (state : State σ) (ans : Answer σ) (resumed : State σ),
      pull builtins program fuel state = .answer ans resumed →
      QueryInv program state →
      PhaseLane program root keys state →
      LaneChain program root keys state.nextScope state.choices
        state.memory →
      ans.queryVarMap = state.queryVarMap ∧
      ∃ Θ, SLDScopedTree program 1 root Θ ∧
        ∀ pair ∈ ans.queryVarMap, pair.1 ∈ keys → ∀ term,
          Heap.readTerm ans.memory.heap pair.2 = .ok term →
          Θ pair.1 = term := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
      intro state ans resumed hPull hq hPL hLC
      cases fuel with
      | zero => simp [pull, RuntimeQuery.pullCore] at hPull
      | succ fuel =>
          simp only [pull, RuntimeQuery.pullCore,
            RuntimeQuery.lp_stepCore_eq_step] at hPull
          cases hphase : state.phase with
          | afterAnswer =>
              have hstep : RuntimeQuery.step builtins program state =
                  .next { state with phase := .backtrack } none := by
                simp [RuntimeQuery.step, RuntimeQuery.stepCore, hphase]
              rw [hstep] at hPull
              dsimp only at hPull
              exact ih fuel (Nat.lt_succ_self _) { state with phase := .backtrack } ans resumed hPull
                (hq.set_phase _) (by simp [PhaseLane]) hLC
          | unifying attempt machine =>
              simp only [PhaseLane, hphase] at hPL
          | backtrack =>
              cases hchoices : state.choices with
              | nil =>
                  have hstep : RuntimeQuery.step builtins program state =
                      complete state := by
                    simp [RuntimeQuery.step, RuntimeQuery.stepCore, hphase,
                      hchoices]
                  rw [hstep] at hPull
                  obtain ⟨result, hres⟩ := complete_terminal state
                  rw [hres] at hPull
                  dsimp only at hPull
                  cases hPull
              | cons cursor older =>
                  obtain ⟨m₀, hres, hqPop, hsPop⟩ :=
                    backtrackPop_inv hq hchoices
                  have hstep : RuntimeQuery.step builtins program state =
                      .next { state with memory := m₀, choices := older, phase := .select cursor } none := by
                    simp [RuntimeQuery.step, RuntimeQuery.stepCore, hphase,
                      hchoices, hres]
                  rw [hstep] at hPull
                  dsimp only at hPull
                  rw [hchoices] at hLC
                  obtain ⟨⟨barrier, hb, hlanePop⟩, hLCPop⟩ :=
                    hLC.pop hres
                  refine ih fuel (Nat.lt_succ_self _) { state with memory := m₀, choices := older, phase := .select cursor } ans resumed hPull
                    hqPop ?_ hLCPop
                  simp only [PhaseLane]
                  exact ⟨hsPop, barrier, hb, hlanePop⟩
          | dispatch =>
              obtain ⟨hCW, barrier, hb, hlane⟩ := by
                simpa only [PhaseLane, hphase] using hPL
              cases hcurrent : state.control.current with
              | nil =>
                  cases hframes : state.control.frames with
                  | nil =>
                      have hstep : RuntimeQuery.step builtins program state =
                          .next { state with phase := .afterAnswer }
                            (some (.answer { memory := state.memory, queryVarMap := state.queryVarMap })) := by
                        simp [RuntimeQuery.step, RuntimeQuery.stepCore, hphase,
                          hcurrent, hframes]
                      rw [hstep] at hPull
                      dsimp only at hPull
                      cases hPull
                      refine ⟨rfl, ?_⟩
                      have hflat : flattenControl state.control = [] := by
                        simp [flattenControl, hcurrent, hframes]
                      have hread : readGoals state.memory.heap
                          (flattenControl state.control) = .ok [] := by
                        rw [hflat]
                        rfl
                      obtain ⟨Θ, hΘ, hAg⟩ := hlane state.memory.heap
                        (BindingExtension.rfl _) hq.inj hq.desc
                        (functionFree_of_isEmpty _) state.nextScope hb
                        (Subst.id σ.scoped) [] hread (.nil state.nextScope)
                      refine ⟨Θ, hΘ, ?_⟩
                      intro pair hpair hkey term hterm
                      rw [hAg pair.1 hkey, Subst.comp_id_left]
                      obtain ⟨link, hcell⟩ := hq.varMap pair hpair
                      have hcellOf : cellOf state.memory.heap pair.1 =
                          some pair.2 := by
                        unfold cellOf
                        have hex : ∃ a : Addr, ∃ l,
                            state.memory.heap[a]? =
                              some (Cell.var pair.1 l) :=
                          ⟨pair.2, link, hcell⟩
                        rw [dif_pos hex]
                        obtain ⟨l', hl'⟩ := hex.choose_spec
                        exact congrArg some
                          (hq.inj _ pair.2 pair.1 l' link hl' hcell)
                      show heapSubst state.memory.heap pair.1 = term
                      simp [heapSubst, hcellOf, hterm]
                  | cons frame frames' =>
                      have hstep : RuntimeQuery.step builtins program state =
                          .next (framePopState state frame frames') none := by
                        simp [RuntimeQuery.step, RuntimeQuery.stepCore, hphase,
                          hcurrent, hframes,
                          framePopState]
                      rw [hstep] at hPull
                      dsimp only at hPull
                      refine ih fuel (Nat.lt_succ_self _)
                        (framePopState state frame frames') ans resumed
                        hPull (hq.framePop) ?_ hLC
                      simp only [PhaseLane, framePopState, hphase]
                      refine ⟨hCW.framePop hframes, barrier, hb, ?_⟩
                      rw [flatten_framePop hcurrent hframes
                        frame.callerCutDepth]
                      exact hlane
              | cons goal rest =>
                  have hnotCut : ¬ (builtins.isCut goal.symbol = true) := by
                    simp [hCutFree goal.symbol]
                  have hstep : RuntimeQuery.step builtins program state =
                      .next { state with phase := .select {
                        checkpoint := state.memory.checkpoint
                        goal
                        clauses := clausesFor program goal.symbol
                        cutDepth := state.choices.length
                        frames := { continuation := rest, callerCutDepth := state.control.cutDepth } :: state.control.frames
                      } } none := by
                    simp [RuntimeQuery.step, RuntimeQuery.stepCore,
                      RuntimeQuery.lpDispatchAction, hphase, hcurrent, hnotCut]
                  rw [hstep] at hPull
                  dsimp only at hPull
                  refine ih fuel (Nat.lt_succ_self _) { state with phase := .select { checkpoint := state.memory.checkpoint, goal := goal, clauses := clausesFor program goal.symbol, cutDepth := state.choices.length, frames := { continuation := rest, callerCutDepth := state.control.cutDepth } :: state.control.frames } } ans resumed
                    hPull (hq.set_phase _) ?_ hLC
                  simp only [PhaseLane]
                  have hcc := hCW.callCursor (program := program) hcurrent
                  refine ⟨⟨hcc.checkpoint, hcc.goal, hcc.frames,
                    hcc.clauses⟩, barrier, hb, ?_⟩
                  rw [flatten_callCursor program hcurrent]
                  exact hlane
          | select cursor =>
              obtain ⟨hs, barrier, hb, hlane⟩ := by
                simpa only [PhaseLane, hphase] using hPL
              cases hclauses : cursor.clauses with
              | nil =>
                  have hstep : RuntimeQuery.step builtins program state =
                      .next { state with phase := .backtrack } none := by
                    simp [RuntimeQuery.step, RuntimeQuery.stepCore,
                      RuntimeQuery.selectStep, hphase,
                      hclauses]
                  rw [hstep] at hPull
                  dsimp only at hPull
                  exact ih fuel (Nat.lt_succ_self _) { state with phase := .backtrack } ans resumed hPull
                    (hq.set_phase _) (by simp [PhaseLane]) hLC
              | cons clause remaining =>
                  cases hMat : materializeClause state.memory
                      (clause.atScope state.nextScope) with
                  | error e =>
                      have hstep : RuntimeQuery.step builtins program state =
                          failWith state (.memory e) := by
                        simp [RuntimeQuery.step, RuntimeQuery.stepCore,
                          RuntimeQuery.selectStep,
                          RuntimeQuery.lpClauseMaterializer, hphase, hclauses,
                          hMat]
                      rw [hstep] at hPull
                      obtain ⟨result, hres⟩ := failWith_terminal state _
                      rw [hres] at hPull
                      dsimp only at hPull
                      cases hPull
                  | ok copied =>
                      by_cases hPredicate :
                          cursor.goal.symbol = copied.clause.head.symbol
                      case neg =>
                          have hstep : RuntimeQuery.step builtins program
                            state = failWith state .predicateMismatch := by
                            simp [RuntimeQuery.step, RuntimeQuery.stepCore,
                              RuntimeQuery.selectStep,
                              RuntimeQuery.lpClauseMaterializer, hphase,
                              hclauses, hMat, RuntimeClauseEntry.enter,
                              hPredicate]
                          rw [hstep] at hPull
                          obtain ⟨result, hres⟩ := failWith_terminal state _
                          rw [hres] at hPull
                          dsimp only at hPull
                          cases hPull
                      case pos =>
                      by_cases hArity : cursor.goal.args.size =
                          copied.clause.head.args.size
                      case neg =>
                          have hstep : RuntimeQuery.step builtins program
                            state = failWith state .predicateMismatch := by
                            simp [RuntimeQuery.step, RuntimeQuery.stepCore,
                              RuntimeQuery.selectStep,
                              RuntimeQuery.lpClauseMaterializer, hphase,
                              hclauses, hMat, RuntimeClauseEntry.enter,
                              hPredicate, hArity]
                          rw [hstep] at hPull
                          obtain ⟨result, hres⟩ := failWith_terminal state _
                          rw [hres] at hPull
                          dsimp only at hPull
                          cases hPull
                      case pos =>
                      have hstep : RuntimeQuery.step builtins program state =
                          .next (unifyEntryState state cursor remaining
                            copied) none := by
                        simp [RuntimeQuery.step, RuntimeQuery.stepCore,
                          RuntimeQuery.selectStep,
                          RuntimeQuery.lpClauseMaterializer, hphase, hclauses,
                          hMat, RuntimeClauseEntry.enter, hPredicate, hArity,
                          unifyEntryState]
                      rw [hstep] at hPull
                      dsimp only at hPull
                      obtain ⟨hqE, hExtMat, hClauseWF, hFresh⟩ :=
                        selectSuccess_inv hq hs hclauses hMat
                      obtain ⟨hPrefix, hSizeLe, _, _, _, _⟩ :=
                        materializeClause_facts hMat
                      have hBmat : BindingExtension state.memory.heap
                          copied.memory.heap :=
                        bindingExtension_of_prefix hPrefix hSizeLe
                      have hclauseMem : clause ∈ program :=
                        clausesFor_mem_program (hs.clauses clause (by
                          rw [hclauses]
                          exact List.mem_cons_self ..))
                      -- the retry chain at the unify entry
                      have hLCEntry : LaneChain program root keys
                          (state.nextScope + 1)
                          (replacementChoices cursor remaining state.choices)
                          copied.memory := by
                        cases remaining with
                        | nil =>
                            show LaneChain program root keys
                              (state.nextScope + 1) state.choices
                              copied.memory
                            exact (hLC.scope_mono (Nat.le_succ _)).anchor
                              hExtMat
                        | cons r rs =>
                            show LaneChain program root keys
                              (state.nextScope + 1)
                              ({ cursor with clauses := r :: rs } ::
                                state.choices) copied.memory
                            exact LaneChain.cons (m₀ := state.memory)
                              hExtMat hs.checkpoint hq.wf hq.shaped
                              (Nat.le_trans hb (Nat.le_succ _)) hlane
                              (hLC.scope_mono (Nat.le_succ _))
                      obtain ⟨k', rest', hfuelEq, hdisj⟩ :=
                        pull_unifying_extract builtins program fuel
                          (unifyEntryState state cursor remaining copied)
                          _ _ ans resumed rfl hPull
                      rcases hdisj with ⟨m₁, hrunU, hPull'⟩ |
                        ⟨mF, hrunF, hPull'⟩
                      · -- unify success
                        have hrest' : rest' < fuel + 1 := by omega
                        have hBodyWF : AtomsWF copied.memory.heap
                            (copied.clause.body) :=
                          fun atom hatom => hClauseWF.2 atom hatom
                        have hFramesWF : FramesWF copied.memory.heap
                            cursor.frames :=
                          hs.frames.mono hSizeLe
                        obtain ⟨hq', hc'⟩ := unifySuccess_queryInv
                          (program := program)
                          (attempt := { body := copied.clause.body, cutDepth := cursor.cutDepth, frames := cursor.frames })
                          hqE hBodyWF hFramesWF hrunU
                        obtain ⟨hBuni, hExtUni, _⟩ :=
                          startMany_success_extension k' copied.memory _
                            m₁ hrunU
                        have hlane' := laneCons_transfer hb hMat hrunU
                          hPredicate hArity hclauseMem hs.goal hq'.desc
                          hlane
                        refine ih rest' hrest'
                          (unifySuccessState (unifyEntryState state cursor remaining copied) { body := copied.clause.body, cutDepth := cursor.cutDepth, frames := cursor.frames } m₁)
                          ans resumed hPull'
                          hq' ?_ (hLCEntry.anchor hExtUni)
                        simp only [PhaseLane]
                        exact ⟨hc', state.nextScope + 1, Nat.le_refl _,
                          hlane'⟩
                      · -- unify failure: exact rollback to the entry
                        have hrest' : rest' < fuel + 1 := by omega
                        have hmF : mF = copied.memory :=
                          startMany_failure_exact k' copied.memory _ mF
                            hrunF
                        subst hmF
                        exact ih rest' hrest'
                          { unifyEntryState state cursor remaining copied with memory := copied.memory, phase := .backtrack }
                          ans resumed hPull'
                          (hqE.set_phase _) (by simp [PhaseLane])
                          hLCEntry

/-- The empty query materializes an empty variable map. -/
theorem materializeGoals_nil_varMap {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ} {result : MaterializedGoals σ}
    (h : materializeGoals memory [] = .ok result) :
    result.varMap = [] := by
  unfold materializeGoals at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeGoalsAux ([] : List (Atom σ))) memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeGoals, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨_, _, hrun, _, _⟩ := runChecked_ok hrc
      rw [show materializeGoalsAux ([] : List (Atom σ)) =
        ([] : List (Atom σ)).mapM materializeAtomAux from rfl,
        run_mapM_nil] at hrun
      cases hrun
      simp only [List.all_nil, if_true] at h
      cases h
      rfl

/-- **The keystone, proved for function-free signatures**: static, cut-free
runtime answers are derivable in the standardized-apart SLD judgment, with
the yielded bindings agreeing with the derivation's substitution.  (With
function symbols the runtime's rational-tree unification outruns finite
SLD — the executable canaries pin that separation — so the function-free
fragment is exactly where the endpoint holds.) -/
theorem refinementEndpoint_functionFree (σ : LPSignature)
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    [IsEmpty σ.functionSymbols] :
    RefinementEndpoint σ := by
  intro builtins program goals state fuel answer resumed hCutFree hOpen
    hPull
  obtain ⟨hq, hCW⟩ := openQuery_empty_queryInv (program := program) hOpen
  obtain ⟨hScope01, _, result, hMat, hstateEq⟩ := openQuery_ok_inv hOpen
  subst hstateEq
  have hKeys : ∀ v ∈ result.varMap.map Prod.fst, v.scope = 0 := by
    intro v hv
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hv
    obtain ⟨link, hcell⟩ := hq.varMap pair hpair
    exact Nat.lt_one_iff.mp (hq.scopes _ _ _ hcell)
  have hKeysEmpty : goals = [] → result.varMap.map Prod.fst = [] := by
    intro hnil
    subst hnil
    rw [materializeGoals_nil_varMap hMat]
    rfl
  have hlaneRoot := rootLane_initial (program := program)
    (result.varMap.map Prod.fst) hKeys hKeysEmpty hMat
  have hflat : flattenControl
      (openedState (Memory.empty σ.scoped) 1 result).control =
      result.goals := by
    simp [flattenControl, openedState]
  obtain ⟨hqv, Θ, hΘ, hAg⟩ := pull_root_sound builtins program hCutFree
    (queryAtScope 0 goals) (result.varMap.map Prod.fst) fuel
    (openedState (Memory.empty σ.scoped) 1 result) answer resumed hPull hq
    (by
      simp only [PhaseLane]
      refine ⟨hCW, 1, Nat.le_refl _, ?_⟩
      rw [hflat]
      exact hlaneRoot)
    (.nil _ _)
  refine ⟨Θ, hΘ, ?_⟩
  intro pair hpair term hterm
  have hpairS : pair ∈
      (openedState (Memory.empty σ.scoped) 1 result).queryVarMap := by
    rw [← hqv]
    exact hpair
  exact hAg pair hpair (List.mem_map.mpr ⟨pair, hpairS, rfl⟩) term hterm

/-- **Runtime answers are true in the least Herbrand model**: the composed
theorem.  A static, cut-free pulled answer over a function-free signature
carries an SLD derivation of the query at scope 1 whose substitution
matches the yielded bindings, and every query goal grounds — under that
substitution and any grounding — into the least Herbrand model of the
knowledge base. -/
theorem runtimeAnswer_leastModel {σ : LPSignature} [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols] [IsEmpty σ.functionSymbols]
    (builtins : Builtins σ) (kb : KnowledgeBase σ)
    (goals : List (Atom σ)) (state : State σ) (fuel : Nat)
    (answer : Answer σ) (resumed : State σ)
    (hCutFree : ∀ symbol, builtins.isCut symbol = false)
    (hOpen : openQuery (Memory.empty σ.scoped) 0 1 goals = .ok state)
    (hPull : pull builtins kb.prog fuel state = .answer answer resumed) :
    ∃ θ : Subst σ.scoped,
      SLDScopedTree kb.prog 1 (queryAtScope 0 goals) θ ∧
      (∀ pair ∈ answer.queryVarMap, ∀ term,
        Heap.readTerm answer.memory.heap pair.2 = .ok term →
        θ pair.1 = term) ∧
      ∀ g : Grounding σ.scoped, ∀ a ∈ queryAtScope 0 goals,
        ((g.compSubst θ).groundAtom a).unscope ∈ leastHerbrandModel kb := by
  obtain ⟨θ, hSLD, hAg⟩ := refinementEndpoint_functionFree σ builtins
    kb.prog goals state fuel answer resumed hCutFree hOpen hPull
  exact ⟨θ, hSLD, hAg, SLDScopedTree_sound kb 1 _ θ hSLD⟩

end RunInduction

end RuntimeUnificationSoundness
end Mettapedia.Logic.LP
