import Mettapedia.Logic.LP.RuntimeRestoration

/-!
# Materialization soundness

Builder mechanics, the term/atom/goals/clause round-trips (materialized
structure reads back verbatim), identity-injectivity establishment under
the scope discipline, and generic transport of heap invariants along
materialization.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeUnificationSoundness

open RuntimeTerm RuntimeUnification RuntimeReadback
/-! ## Stage 3a: readback under append-only extension, and atom readback -/

/-- List companion for `readTermFuel_extend`. -/
theorem readListFuel_extend {σ : LPSignature} {heap heap' : Heap σ}
    {fuel : Nat}
    (termCase : ∀ address, address < heap.size → ∀ t,
      readTermFuel heap fuel address = .ok t →
      readTermFuel heap' fuel address = .ok t) :
    ∀ (addresses : List Addr), (∀ a ∈ addresses, a < heap.size) →
      ∀ (terms : List (Term σ)),
        readListFuel heap fuel addresses = .ok terms →
        readListFuel heap' fuel addresses = .ok terms := by
  intro addresses
  induction addresses with
  | nil => intro _ terms h; simpa [readListFuel] using h
  | cons head tailA tailIh =>
      intro hbound terms h
      simp only [readListFuel, Bind.bind, Except.bind] at h ⊢
      cases hHead : readTermFuel heap fuel head with
      | error e => rw [hHead] at h; simp at h
      | ok headTerm =>
          rw [hHead] at h
          rw [termCase head (hbound head (by simp)) headTerm hHead]
          cases hTail : readListFuel heap fuel tailA with
          | error e => rw [hTail] at h; simp at h
          | ok tailTerms =>
              rw [hTail] at h
              rw [tailIh (fun a ha => hbound a (by simp [ha])) tailTerms hTail]
              exact h

/-- Readback is stable under append-only extension of a *well-formed* heap:
the prefix is reference-closed, so chains never leave it. -/
theorem readTermFuel_extend {σ : LPSignature} {heap heap' : Heap σ}
    (hwf : Heap.WellFormed heap)
    (hpre : ∀ i, i < heap.size → heap'[i]? = heap[i]?) :
    ∀ (fuel : Nat) (address : Addr), address < heap.size →
      ∀ t, readTermFuel heap fuel address = .ok t →
        readTermFuel heap' fuel address = .ok t := by
  intro fuel
  induction fuel with
  | zero => intro address _ t h; simp [readTermFuel] at h
  | succ fuel ih =>
      intro address haddr t h
      cases hcell : heap[address]? with
      | none =>
          rw [readTermFuel_invalid heap fuel address hcell] at h
          exact absurd h (by simp)
      | some cell =>
          have hcell' : heap'[address]? = some cell := by
            rw [hpre address haddr]; exact hcell
          cases cell with
          | var identity link =>
              cases link with
              | none =>
                  rw [readTermFuel_unbound heap fuel address identity hcell] at h
                  rw [readTermFuel_unbound heap' fuel address identity hcell']
                  exact h
              | some target =>
                  rw [readTermFuel_link heap fuel address target identity
                    hcell] at h
                  rw [readTermFuel_link heap' fuel address target identity
                    hcell']
                  have htarget : target < heap.size :=
                    hwf address _ hcell target (by simp [Cell.references])
                  exact ih target htarget t h
          | const symbol =>
              rw [readTermFuel_const heap fuel address symbol hcell] at h
              rw [readTermFuel_const heap' fuel address symbol hcell']
              exact h
          | app symbol args =>
              rw [readTermFuel_app heap fuel address symbol args hcell] at h
              rw [readTermFuel_app heap' fuel address symbol args hcell']
              simp only [Bind.bind, Except.bind] at h ⊢
              cases hArgs : readListFuel heap fuel args.toList with
              | error e => rw [hArgs] at h; simp at h
              | ok children =>
                  rw [hArgs] at h
                  have hbound : ∀ a ∈ args.toList, a < heap.size := by
                    intro a ha
                    exact hwf address _ hcell a (by
                      simpa [Cell.references] using ha)
                  rw [readListFuel_extend (fun a ha => ih a ha) args.toList
                    hbound children hArgs]
                  exact h

/-- Read one runtime atom back into a canonical LP atom. -/
def readAtom {σ : LPSignature} (heap : Heap σ)
    (atom : RuntimeMaterialize.RuntimeAtom σ) :
    Except ReadbackError (Atom σ) := do
  let children ← readListFuel heap (heap.size + 1) atom.args.toList
  if h : children.length = σ.relationArity atom.symbol then
    .ok ⟨atom.symbol, fun index => children.get (Fin.cast h.symm index)⟩
  else
    .error .arityMismatch

/-! ## Stage 3b: builder mechanics -/

open RuntimeMaterialize in
/-- All variable-map entries point at unbound cells carrying their identity. -/
def VarMapCells {σ : LPSignature} (state : BuilderState σ) : Prop :=
  ∀ pair ∈ state.varMap,
    state.heap[pair.2]? = some (Cell.var pair.1 none)

@[simp] theorem BuilderM.run_bind {σ : LPSignature} {α β : Type _}
    (action : RuntimeMaterialize.BuilderM σ α)
    (next : α → RuntimeMaterialize.BuilderM σ β)
    (state : RuntimeMaterialize.BuilderState σ) :
    (action >>= next).run state =
      match action.run state with
      | .error error => .error error
      | .ok (value, nextState) => (next value).run nextState := rfl

@[simp] theorem BuilderM.run_pure {σ : LPSignature} {α : Type _}
    (value : α) (state : RuntimeMaterialize.BuilderState σ) :
    (pure value : RuntimeMaterialize.BuilderM σ α).run state =
      .ok (value, state) := rfl

open RuntimeMaterialize in
/-- Builder-level allocation, inverted. -/
theorem allocate_run_spec {σ : LPSignature} {cell : Cell σ}
    {s₀ s₁ : BuilderState σ} {address : Addr}
    (h : (RuntimeMaterialize.allocate cell).run s₀ = .ok (address, s₁)) :
    address = s₀.heap.size ∧ s₁.heap = s₀.heap.push cell ∧
      s₁.varMap = s₀.varMap := by
  simp only [RuntimeMaterialize.allocate, BuilderM.run_bind,
    BuilderM.get, BuilderM.set, BuilderM.throw] at h
  cases halloc : Memory.allocate { heap := s₀.heap, trail := #[] } cell with
  | error e => rw [halloc] at h; cases h
  | ok pair =>
      obtain ⟨addr₀, memory₀⟩ := pair
      rw [halloc] at h
      obtain ⟨haddr, hmem⟩ := allocate_ok_inv halloc
      cases h
      refine ⟨haddr, ?_, rfl⟩
      rw [hmem]

/-- Pointwise readbacks assemble into a list readback. -/
theorem readListFuel_of_pointwise {σ : LPSignature} {heap : Heap σ}
    {fuel : Nat} :
    ∀ (addresses : List Addr) (terms : List (Term σ)),
      addresses.length = terms.length →
      (∀ k (hk : k < addresses.length) (hk' : k < terms.length),
        readTermFuel heap fuel addresses[k] = .ok terms[k]) →
      readListFuel heap fuel addresses = .ok terms := by
  intro addresses
  induction addresses with
  | nil =>
      intro terms hlen _
      cases terms with
      | nil => simp [readListFuel]
      | cons _ _ => simp at hlen
  | cons head tailA tailIh =>
      intro terms hlen hpoint
      cases terms with
      | nil => simp at hlen
      | cons headTerm tailTerms =>
          simp only [readListFuel, Bind.bind, Except.bind]
          have hhead := hpoint 0 (by simp) (by simp)
          simp only [List.getElem_cons_zero] at hhead
          rw [hhead]
          have htail := tailIh tailTerms (by simpa using hlen)
            (fun k hk hk' => by
              have := hpoint (k + 1) (by simpa using hk)
                (by simpa using hk')
              simpa using this)
          rw [htail]

open RuntimeMaterialize



/-- What one builder step must preserve. -/
structure BuildOk {σ : LPSignature} (s₀ s₁ : BuilderState σ) : Prop where
  prefixEq : ∀ i, i < s₀.heap.size → s₁.heap[i]? = s₀.heap[i]?
  sizeLe : s₀.heap.size ≤ s₁.heap.size
  wf : Heap.WellFormed s₁.heap
  cells : VarMapCells s₁
  varMono : ∀ pair ∈ s₀.varMap, pair ∈ s₁.varMap

theorem BuildOk.rfl {σ : LPSignature} {s : BuilderState σ}
    (hwf : Heap.WellFormed s.heap) (hcells : VarMapCells s) : BuildOk s s :=
  ⟨fun _ _ => _root_.rfl, Nat.le_refl _, hwf, hcells, fun _ hp => hp⟩

theorem BuildOk.trans {σ : LPSignature} {s₀ s₁ s₂ : BuilderState σ}
    (a : BuildOk s₀ s₁) (b : BuildOk s₁ s₂) : BuildOk s₀ s₂ where
  prefixEq i hi := by
    rw [b.prefixEq i (Nat.lt_of_lt_of_le hi a.sizeLe)]
    exact a.prefixEq i hi
  sizeLe := a.sizeLe.trans b.sizeLe
  wf := b.wf
  cells := b.cells
  varMono pair hp := b.varMono pair (a.varMono pair hp)

/-- Pushing a reference-closed cell is a valid builder step. -/
theorem BuildOk.push {σ : LPSignature} {s : BuilderState σ} {cell : Cell σ}
    (hwf : Heap.WellFormed s.heap) (hcells : VarMapCells s)
    (hrefs : ∀ target ∈ Cell.references cell, target < s.heap.size) :
    BuildOk s { heap := s.heap.push cell, varMap := s.varMap } where
  prefixEq i hi := getElem?_push_lt s.heap cell hi
  sizeLe := by
    simp only [Array.size_push]
    exact Nat.le_succ _
  wf := by
    intro address cell' hcell' target ht
    simp only [Array.size_push]
    by_cases haddr : address = s.heap.size
    · subst haddr
      have hpe : (s.heap.push cell)[s.heap.size]? = some cell := by
        simp
      rw [hpe] at hcell'
      cases hcell'
      exact Nat.lt_succ_of_lt (hrefs target ht)
    · have hlt : address < s.heap.size := by
        have hlt' := lt_of_getElem?_some hcell'
        simp only [Array.size_push] at hlt'
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt') haddr
      rw [getElem?_push_lt s.heap cell hlt] at hcell'
      exact Nat.lt_succ_of_lt (hwf address cell' hcell' target ht)
  cells pair hp := by
    have hcell := hcells pair hp
    have hlt := lt_of_getElem?_some hcell
    rw [getElem?_push_lt s.heap cell hlt]
    exact hcell
  varMono _ hp := hp

/-- A successful association-list lookup names an entry. -/
theorem mem_of_list_lookup {σ : LPSignature} [DecidableEq σ.vars] :
    ∀ {varMap : List (σ.vars × Addr)} {identity : σ.vars} {address : Addr},
      List.lookup identity varMap = some address →
      (identity, address) ∈ varMap := by
  intro varMap
  induction varMap with
  | nil => intro _ _ h; simp [List.lookup] at h
  | cons head tailM ih =>
      intro identity address h
      obtain ⟨key, value⟩ := head
      by_cases he : identity = key
      · subst he
        simp [List.lookup] at h
        subst h
        exact List.mem_cons_self ..
      · have hne : (identity == key) = false := by
          simpa using he
        simp [List.lookup, hne] at h
        exact List.mem_cons_of_mem _ (ih h)

/-- The specification one materialized term satisfies. -/
def TermSpec {σ : LPSignature} [DecidableEq σ.vars] (t : Term σ) : Prop :=
  ∀ {s₀ s₁ : BuilderState σ} {address : Addr},
    (materializeTermAux t).run s₀ = .ok (address, s₁) →
    Heap.WellFormed s₀.heap → VarMapCells s₀ →
    BuildOk s₀ s₁ ∧ address < s₁.heap.size ∧
      readTermFuel s₁.heap (s₁.heap.size + 1) address = .ok t

/-- Run-level unfolding of `List.mapM.loop` for the builder monad, proved
directly so no `LawfulMonad` instance is needed. -/
theorem run_mapM_loop {σ : LPSignature} {α β : Type _}
    (f : α → RuntimeMaterialize.BuilderM σ β) :
    ∀ (as : List α) (acc : List β) (s : BuilderState σ),
      (List.mapM.loop f as acc).run s =
        match (as.mapM f).run s with
        | .error e => .error e
        | .ok (bs, s') => .ok (acc.reverse ++ bs, s') := by
  intro as
  induction as with
  | nil =>
      intro acc s
      simp [List.mapM, List.mapM.loop, BuilderM.run_pure]
  | cons head tailA ih =>
      intro acc s
      show (List.mapM.loop f (head :: tailA) acc).run s = _
      simp only [List.mapM.loop, BuilderM.run_bind]
      cases hHead : (f head).run s with
      | error e =>
          simp only [List.mapM, List.mapM.loop, BuilderM.run_bind, hHead]
      | ok pair =>
          obtain ⟨b, s'⟩ := pair
          simp only [List.mapM, List.mapM.loop, BuilderM.run_bind, hHead]
          rw [ih (b :: acc) s', ih [b] s']
          cases hTail : (tailA.mapM f).run s' with
          | error e => rfl
          | ok pair' =>
              obtain ⟨bs, s''⟩ := pair'
              simp

theorem run_mapM_nil {σ : LPSignature} {α β : Type _}
    (f : α → RuntimeMaterialize.BuilderM σ β) (s : BuilderState σ) :
    (([] : List α).mapM f).run s = .ok (([] : List β), s) := by
  simp [List.mapM, List.mapM.loop, BuilderM.run_pure]

theorem run_mapM_cons {σ : LPSignature} {α β : Type _}
    (f : α → RuntimeMaterialize.BuilderM σ β) (a : α) (as : List α)
    (s : BuilderState σ) :
    ((a :: as).mapM f).run s =
      match (f a).run s with
      | .error e => .error e
      | .ok (b, s') =>
          match (as.mapM f).run s' with
          | .error e => .error e
          | .ok (bs, s'') => .ok (b :: bs, s'') := by
  show (List.mapM.loop f (a :: as) []).run s = _
  simp only [List.mapM.loop, BuilderM.run_bind]
  cases hHead : (f a).run s with
  | error e => rfl
  | ok pair =>
      obtain ⟨b, s'⟩ := pair
      dsimp only
      rw [run_mapM_loop f as [b] s']
      cases hTail : (as.mapM f).run s' with
      | error e => rfl
      | ok pair' =>
          obtain ⟨bs, s''⟩ := pair'
          simp

/-- mapM companion: element specs assemble into a run over an index list. -/
theorem materializeMapM_spec {σ : LPSignature} [DecidableEq σ.vars]
    {ι : Type _} (f : ι → Term σ) :
    ∀ (indices : List ι),
      (∀ i ∈ indices, TermSpec (f i)) →
      ∀ {s₀ s₁ : BuilderState σ} {addresses : List Addr},
        (indices.mapM fun i => materializeTermAux (f i)).run s₀ =
          .ok (addresses, s₁) →
        Heap.WellFormed s₀.heap → VarMapCells s₀ →
        BuildOk s₀ s₁ ∧ addresses.length = indices.length ∧
          ∀ k (hk : k < addresses.length) (hk' : k < indices.length),
            addresses[k] < s₁.heap.size ∧
            readTermFuel s₁.heap (s₁.heap.size + 1) addresses[k] =
              .ok (f indices[k]) := by
  intro indices
  induction indices with
  | nil =>
      intro _ s₀ s₁ addresses h hwf hcells
      rw [run_mapM_nil] at h
      cases h
      exact ⟨BuildOk.rfl hwf hcells, _root_.rfl,
        fun k hk _ => absurd hk (Nat.not_lt_zero k)⟩
  | cons head tailI tailIh =>
      intro elemSpec s₀ s₁ addresses h hwf hcells
      rw [run_mapM_cons] at h
      cases hHead : (materializeTermAux (f head)).run s₀ with
      | error e => rw [hHead] at h; cases h
      | ok headPair =>
          obtain ⟨headAddr, sMid⟩ := headPair
          rw [hHead] at h
          dsimp only at h
          cases hTail : (tailI.mapM fun i => materializeTermAux (f i)).run
              sMid with
          | error e => rw [hTail] at h; cases h
          | ok tailPair =>
              obtain ⟨tailAddrs, sEnd⟩ := tailPair
              rw [hTail] at h
              dsimp only at h
              cases h
              obtain ⟨bHead, hHeadLt, hHeadRead⟩ :=
                elemSpec head (by simp) hHead hwf hcells
              obtain ⟨bTail, hLen, hPoint⟩ :=
                tailIh (fun i hi => elemSpec i (by simp [hi]))
                  hTail bHead.wf bHead.cells
              refine ⟨bHead.trans bTail,
                congrArg (fun n => n + 1) hLen, ?_⟩
              intro k hk hk'
              cases k with
              | zero =>
                  refine ⟨Nat.lt_of_lt_of_le hHeadLt bTail.sizeLe, ?_⟩
                  simp only [List.getElem_cons_zero]
                  have hExt := readTermFuel_extend bHead.wf bTail.prefixEq
                    (sMid.heap.size + 1) headAddr hHeadLt _ hHeadRead
                  exact readTermFuel_mono_le _
                    (Nat.succ_le_succ bTail.sizeLe) headAddr _ hExt
              | succ k =>
                  have := hPoint k (by simpa using hk) (by simpa using hk')
                  simpa using this

/-- **Materialization round-trip** (term level): a materialized term reads
back verbatim, the heap grows append-only and stays well-formed, and the
variable map stays coherent. -/
theorem materializeTermAux_spec {σ : LPSignature} [DecidableEq σ.vars] :
    ∀ t : Term σ, TermSpec t := by
  intro t
  induction t with
  | var identity =>
      intro s₀ s₁ address h hwf hcells
      simp only [materializeTermAux, BuilderM.run_bind, BuilderM.get] at h
      cases hlook : List.lookup identity s₀.varMap with
      | some existing =>
          simp only [hlook, BuilderM.run_pure] at h
          cases h
          exact ⟨BuildOk.rfl hwf hcells,
            lt_of_getElem?_some (hcells _ (mem_of_list_lookup hlook)),
            readTermFuel_unbound _ _ _ _
              (hcells _ (mem_of_list_lookup hlook))⟩
      | none =>
          simp only [hlook, BuilderM.run_bind] at h
          cases hAlloc : (RuntimeMaterialize.allocate
              (Cell.var identity none)).run s₀ with
          | error e => rw [hAlloc] at h; cases h
          | ok pair =>
              obtain ⟨addr₀, sMid⟩ := pair
              rw [hAlloc] at h
              obtain ⟨haddr, hheap, hvar⟩ := allocate_run_spec hAlloc
              simp only [BuilderM.set, BuilderM.run_pure] at h
              cases h
              subst haddr
              have hself : sMid.heap[s₀.heap.size]? =
                  some (Cell.var identity none) := by
                rw [hheap]
                simp
              have bPush : BuildOk s₀
                  { heap := sMid.heap, varMap := s₀.varMap } := by
                have := BuildOk.push (cell := Cell.var identity none)
                  hwf hcells (by simp [Cell.references])
                rwa [← hheap] at this
              have hCells : VarMapCells
                  ({ heap := sMid.heap,
                     varMap := (identity, s₀.heap.size) :: sMid.varMap } :
                    BuilderState σ) := by
                intro pair hp
                rcases List.mem_cons.mp hp with hhd | hp'
                · rw [hhd]
                  exact hself
                · rw [hvar] at hp'
                  exact bPush.cells pair hp'
              have hVarMono : ∀ pair ∈ s₀.varMap,
                  pair ∈ (identity, s₀.heap.size) :: sMid.varMap := by
                intro pair hp
                rw [hvar]
                exact List.mem_cons_of_mem _ hp
              refine ⟨⟨bPush.prefixEq, bPush.sizeLe, bPush.wf, hCells,
                hVarMono⟩, ?_, ?_⟩
              · rw [hheap]
                simp only [Array.size_push]
                exact Nat.lt_succ_self _
              · exact readTermFuel_unbound sMid.heap sMid.heap.size
                  s₀.heap.size identity hself
  | const symbol =>
      intro s₀ s₁ address h hwf hcells
      simp only [materializeTermAux] at h
      obtain ⟨haddr, hheap, hvar⟩ := allocate_run_spec h
      subst haddr
      have hself : s₁.heap[s₀.heap.size]? = some (Cell.const symbol) := by
        rw [hheap]
        simp
      have bPush : BuildOk s₀ { heap := s₁.heap, varMap := s₀.varMap } := by
        have := BuildOk.push (cell := Cell.const symbol) hwf hcells
          (by simp [Cell.references])
        rwa [← hheap] at this
      have hCells : VarMapCells s₁ := by
        intro pair hp
        rw [hvar] at hp
        exact bPush.cells pair hp
      have hVarMono : ∀ pair ∈ s₀.varMap, pair ∈ s₁.varMap := by
        intro pair hp
        rw [hvar]
        exact bPush.varMono pair hp
      refine ⟨⟨bPush.prefixEq, bPush.sizeLe, bPush.wf, hCells, hVarMono⟩,
        ?_, ?_⟩
      · rw [hheap]
        simp only [Array.size_push]
        exact Nat.lt_succ_self _
      · exact readTermFuel_const s₁.heap s₁.heap.size s₀.heap.size symbol hself
  | app symbol args ih =>
      intro s₀ s₁ address h hwf hcells
      simp only [materializeTermAux, BuilderM.run_bind] at h
      cases hMap : ((List.finRange (σ.functionArity symbol)).mapM fun index =>
          materializeTermAux (args index)).run s₀ with
      | error e => rw [hMap] at h; cases h
      | ok mapPair =>
          obtain ⟨childAddrs, sMid⟩ := mapPair
          rw [hMap] at h
          obtain ⟨bMap, hLen, hPoint⟩ :=
            materializeMapM_spec (fun index => args index)
              (List.finRange (σ.functionArity symbol))
              (fun i _ => ih i) hMap hwf hcells
          obtain ⟨haddr, hheap, hvar⟩ := allocate_run_spec h
          subst haddr
          have hLenArity : childAddrs.length = σ.functionArity symbol := by
            simpa [List.length_finRange] using hLen
          have hself : s₁.heap[sMid.heap.size]? =
              some (Cell.app symbol childAddrs.toArray) := by
            rw [hheap]
            simp
          have hrefs : ∀ target ∈ Cell.references
              (Cell.app symbol childAddrs.toArray),
              target < sMid.heap.size := by
            intro target ht
            simp only [Cell.references] at ht
            obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
            exact (hPoint k hk (by omega)).1
          have bPush : BuildOk sMid
              { heap := s₁.heap, varMap := sMid.varMap } := by
            have := BuildOk.push (cell := Cell.app symbol childAddrs.toArray)
              bMap.wf bMap.cells hrefs
            rwa [← hheap] at this
          have bAll : BuildOk s₀ { heap := s₁.heap, varMap := sMid.varMap } :=
            bMap.trans bPush
          have hCells : VarMapCells s₁ := by
            intro pair hp
            rw [hvar] at hp
            exact bAll.cells pair hp
          have hVarMono : ∀ pair ∈ s₀.varMap, pair ∈ s₁.varMap := by
            intro pair hp
            rw [hvar]
            exact bAll.varMono pair hp
          have hsize : s₁.heap.size = sMid.heap.size + 1 := by
            rw [hheap]
            simp
          refine ⟨⟨bAll.prefixEq, bAll.sizeLe, bAll.wf, hCells, hVarMono⟩,
            ?_, ?_⟩
          · rw [hheap]
            simp only [Array.size_push]
            exact Nat.lt_succ_self _
          · rw [readTermFuel_app s₁.heap s₁.heap.size sMid.heap.size symbol
              childAddrs.toArray hself]
            have hChildren :
                readListFuel s₁.heap s₁.heap.size childAddrs.toArray.toList =
                  .ok ((List.finRange (σ.functionArity symbol)).map
                    fun index => args index) := by
              rw [show childAddrs.toArray.toList = childAddrs from by simp]
              apply readListFuel_of_pointwise
              · simp [hLenArity, List.length_finRange]
              · intro k hk hk'
                have hp := hPoint k hk (by
                  simpa [List.length_finRange, hLenArity] using hk)
                have hExt := readTermFuel_extend bMap.wf bPush.prefixEq
                  (sMid.heap.size + 1) childAddrs[k] hp.1 _ hp.2
                rw [hsize]
                have hidx :
                    ((List.finRange (σ.functionArity symbol)).map
                      fun index => args index)[k]'hk' =
                      args ((List.finRange (σ.functionArity symbol))[k]'(by
                        simpa [List.length_finRange, hLenArity] using hk)) := by
                  simp
                rw [hidx]
                exact hExt
            simp only [Bind.bind, Except.bind, hChildren]
            rw [dif_pos (by simp [List.length_finRange])]
            refine congrArg Except.ok ?_
            refine congrArg (Term.app symbol) ?_
            funext index
            simp [List.get_eq_getElem, List.getElem_map,
              List.getElem_finRange]

/-! ## Stage 5a: materializer discharge

Every S1–S4 hypothesis, proved for what materialization actually does:
the memory-level history is a genuine `Extends` chain of real allocations
(trail untouched), and function-free source keeps the heap function-free. -/


/-- `Memory.allocate` ignores the trail: success transports to any trail. -/
theorem allocate_trail_irrelevant {σ : LPSignature} {heap : Heap σ}
    {trail₁ trail₂ : Array (TrailEntry σ)} {cell : Cell σ}
    {address : Addr} {memory' : Memory σ}
    (h : Memory.allocate { heap := heap, trail := trail₁ } cell =
      .ok (address, memory')) :
    Memory.allocate { heap := heap, trail := trail₂ } cell =
      .ok (address, { heap := memory'.heap, trail := trail₂ }) := by
  obtain ⟨haddr, hmem⟩ := allocate_ok_inv h
  subst haddr
  unfold Memory.allocate at h ⊢
  split at h
  · split at h
    · rw [if_pos ‹_›, if_pos ‹_›]
      rw [hmem]
      rfl
    · rcases hfind :
          (Cell.references cell).find?
            (fun target => decide (heap.size ≤ target)) with _ | t <;>
        rw [hfind] at h <;> cases h
  · cases h

/-- A successful builder allocation is a real memory-level allocation step,
for any caller trail. -/
theorem allocate_extends {σ : LPSignature} {cell : Cell σ}
    {s₀ s₁ : BuilderState σ} {address : Addr}
    (h : (RuntimeMaterialize.allocate cell).run s₀ = .ok (address, s₁))
    (trail : Array (TrailEntry σ)) :
    Extends { heap := s₀.heap, trail := trail }
      { heap := s₁.heap, trail := trail } := by
  simp only [RuntimeMaterialize.allocate, BuilderM.run_bind,
    BuilderM.get, BuilderM.set, BuilderM.throw] at h
  cases hSc : Memory.allocate { heap := s₀.heap, trail := #[] } cell with
  | error e => rw [hSc] at h; cases h
  | ok pair =>
      obtain ⟨addr₀, memory₀⟩ := pair
      rw [hSc] at h
      cases h
      exact .alloc (.refl _) (allocate_trail_irrelevant hSc)

/-- mapM companion for `Extends`, over any builder element action. -/
theorem mapM_extends {σ : LPSignature}
    {ι : Type _} {β : Type _} (g : ι → RuntimeMaterialize.BuilderM σ β) :
    ∀ (indices : List ι),
      (∀ i ∈ indices, ∀ {s₀ s₁ : BuilderState σ} {value : β}
        (trail : Array (TrailEntry σ)),
        (g i).run s₀ = .ok (value, s₁) →
        Extends { heap := s₀.heap, trail := trail }
          { heap := s₁.heap, trail := trail }) →
      ∀ {s₀ s₁ : BuilderState σ} {values : List β}
        (trail : Array (TrailEntry σ)),
        (indices.mapM g).run s₀ = .ok (values, s₁) →
        Extends { heap := s₀.heap, trail := trail }
          { heap := s₁.heap, trail := trail } := by
  intro indices
  induction indices with
  | nil =>
      intro _ s₀ s₁ values trail h
      rw [run_mapM_nil] at h
      cases h
      exact .refl _
  | cons head tailI tailIh =>
      intro elemExt s₀ s₁ values trail h
      rw [run_mapM_cons] at h
      cases hHead : (g head).run s₀ with
      | error e => rw [hHead] at h; cases h
      | ok headPair =>
          obtain ⟨headVal, sMid⟩ := headPair
          rw [hHead] at h
          dsimp only at h
          cases hTail : (tailI.mapM g).run sMid with
          | error e => rw [hTail] at h; cases h
          | ok tailPair =>
              obtain ⟨tailVals, sEnd⟩ := tailPair
              rw [hTail] at h
              dsimp only at h
              cases h
              exact (elemExt head (by simp) trail hHead).trans
                (tailIh (fun i hi => elemExt i (by simp [hi]))
                  trail hTail)

/-- A materializer run realizes a genuine memory-level `Extends` history. -/
theorem materializeTermAux_extends {σ : LPSignature} [DecidableEq σ.vars] :
    ∀ (t : Term σ) {s₀ s₁ : BuilderState σ} {address : Addr}
      (trail : Array (TrailEntry σ)),
      (materializeTermAux t).run s₀ = .ok (address, s₁) →
      Extends { heap := s₀.heap, trail := trail }
        { heap := s₁.heap, trail := trail } := by
  intro t
  induction t with
  | var identity =>
      intro s₀ s₁ address trail h
      simp only [materializeTermAux, BuilderM.run_bind, BuilderM.get] at h
      cases hlook : List.lookup identity s₀.varMap with
      | some existing =>
          simp only [hlook, BuilderM.run_pure] at h
          cases h
          exact .refl _
      | none =>
          simp only [hlook, BuilderM.run_bind] at h
          cases hAlloc : (RuntimeMaterialize.allocate
              (Cell.var identity none)).run s₀ with
          | error e => rw [hAlloc] at h; cases h
          | ok pair =>
              obtain ⟨addr₀, sMid⟩ := pair
              rw [hAlloc] at h
              simp only [BuilderM.set, BuilderM.run_pure] at h
              cases h
              exact allocate_extends hAlloc trail
  | const symbol =>
      intro s₀ s₁ address trail h
      simp only [materializeTermAux] at h
      exact allocate_extends h trail
  | app symbol args ih =>
      intro s₀ s₁ address trail h
      simp only [materializeTermAux, BuilderM.run_bind] at h
      cases hMap : ((List.finRange (σ.functionArity symbol)).mapM fun index =>
          materializeTermAux (args index)).run s₀ with
      | error e => rw [hMap] at h; cases h
      | ok mapPair =>
          obtain ⟨childAddrs, sMid⟩ := mapPair
          rw [hMap] at h
          exact (mapM_extends
            (fun index => materializeTermAux (args index))
            (List.finRange (σ.functionArity symbol))
            (fun i _ => ih i) trail hMap).trans
            (allocate_extends h trail)

/-- Function-free source syntax: no function applications. -/
def TermFF {σ : LPSignature} : Term σ → Prop
  | .var _ => True
  | .const _ => True
  | .app _ _ => False

/-- Materializing function-free source keeps the heap function-free. -/
theorem materializeTermAux_ff {σ : LPSignature} [DecidableEq σ.vars] :
    ∀ (t : Term σ) {s₀ s₁ : BuilderState σ} {address : Addr},
      TermFF t →
      (materializeTermAux t).run s₀ = .ok (address, s₁) →
      FunctionFree s₀.heap → FunctionFree s₁.heap := by
  intro t
  cases t with
  | var identity =>
      intro s₀ s₁ address _ h ff
      simp only [materializeTermAux, BuilderM.run_bind, BuilderM.get] at h
      cases hlook : List.lookup identity s₀.varMap with
      | some existing =>
          simp only [hlook, BuilderM.run_pure] at h
          cases h
          exact ff
      | none =>
          simp only [hlook, BuilderM.run_bind] at h
          cases hAlloc : (RuntimeMaterialize.allocate
              (Cell.var identity none)).run s₀ with
          | error e => rw [hAlloc] at h; cases h
          | ok pair =>
              obtain ⟨addr₀, sMid⟩ := pair
              rw [hAlloc] at h
              obtain ⟨_, hheap, _⟩ := allocate_run_spec hAlloc
              simp only [BuilderM.set, BuilderM.run_pure] at h
              cases h
              intro a symbol args ha
              rcases Nat.lt_trichotomy a s₀.heap.size with hlt | heq | hgt
              · rw [hheap, getElem?_push_lt _ _ hlt] at ha
                exact ff a symbol args ha
              · subst heq
                rw [hheap] at ha
                simp at ha
              · rw [hheap, Array.getElem?_eq_none (by
                  simp only [Array.size_push]; omega)] at ha
                cases ha
  | const symbol =>
      intro s₀ s₁ address _ h ff
      simp only [materializeTermAux] at h
      obtain ⟨_, hheap, _⟩ := allocate_run_spec h
      intro a symbol' args ha
      rcases Nat.lt_trichotomy a s₀.heap.size with hlt | heq | hgt
      · rw [hheap, getElem?_push_lt _ _ hlt] at ha
        exact ff a symbol' args ha
      · subst heq
        rw [hheap] at ha
        simp at ha
      · rw [hheap, Array.getElem?_eq_none (by
          simp only [Array.size_push]; omega)] at ha
        cases ha
  | app symbol args =>
      intro _ _ _ hFF
      cases hFF

/-! ## Stage 5a continued: atom, goals, and clause round-trips -/

theorem readListFuel_mono_le {σ : LPSignature} (heap : Heap σ)
    {small large : Nat} (hle : small ≤ large)
    (addresses : List Addr) (terms : List (Term σ))
    (h : readListFuel heap small addresses = .ok terms) :
    readListFuel heap large addresses = .ok terms := by
  induction hle with
  | refl => exact h
  | step _ ih =>
      exact readListFuel_mono
        (fun a t' ht => readTermFuel_mono heap _ a t' ht) addresses terms ih

/-- `readAtom` results survive append-only extension of a well-formed heap. -/
theorem readAtom_extend {σ : LPSignature} {heap heap' : Heap σ}
    (hwf : Heap.WellFormed heap)
    (hpre : ∀ i, i < heap.size → heap'[i]? = heap[i]?)
    (hsize : heap.size ≤ heap'.size)
    {atom : RuntimeAtom σ} {result : Atom σ}
    (hbound : ∀ a ∈ atom.args.toList, a < heap.size)
    (h : readAtom heap atom = .ok result) :
    readAtom heap' atom = .ok result := by
  unfold readAtom at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases hList : readListFuel heap (heap.size + 1) atom.args.toList with
  | error e => rw [hList] at h; simp at h
  | ok children =>
      rw [hList] at h
      have hExt := readListFuel_extend
        (fun a ha t' ht => readTermFuel_extend hwf hpre (heap.size + 1)
          a ha t' ht) atom.args.toList hbound children hList
      have hLift := readListFuel_mono_le heap'
        (Nat.succ_le_succ hsize) atom.args.toList children hExt
      rw [hLift]
      exact h

/-- What one materialized atom satisfies. -/
theorem materializeAtomAux_spec {σ : LPSignature} [DecidableEq σ.vars]
    (atom : Atom σ) {s₀ s₁ : BuilderState σ}
    {ratom : RuntimeAtom σ}
    (h : (materializeAtomAux atom).run s₀ = .ok (ratom, s₁))
    (hwf : Heap.WellFormed s₀.heap) (hcells : VarMapCells s₀) :
    BuildOk s₀ s₁ ∧
    (∀ a ∈ ratom.args.toList, a < s₁.heap.size) ∧
    readAtom s₁.heap ratom = .ok atom := by
  simp only [materializeAtomAux, BuilderM.run_bind] at h
  cases hMap : ((List.finRange (σ.relationArity atom.symbol)).mapM
      fun index => materializeTermAux (atom.args index)).run s₀ with
  | error e => rw [hMap] at h; cases h
  | ok mapPair =>
      obtain ⟨childAddrs, sMid⟩ := mapPair
      rw [hMap] at h
      dsimp only at h
      cases h
      obtain ⟨bMap, hLen, hPoint⟩ :=
        materializeMapM_spec (fun index => atom.args index)
          (List.finRange (σ.relationArity atom.symbol))
          (fun i _ => materializeTermAux_spec (atom.args i)) hMap hwf hcells
      have hLenArity : childAddrs.length = σ.relationArity atom.symbol := by
        simpa [List.length_finRange] using hLen
      have hbound : ∀ a ∈ childAddrs.toArray.toList, a < s₁.heap.size := by
        intro a ha
        rw [show childAddrs.toArray.toList = childAddrs from by simp] at ha
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
        exact (hPoint k hk (by omega)).1
      refine ⟨bMap, hbound, ?_⟩
      unfold readAtom
      simp only [Bind.bind, Except.bind]
      have hChildren :
          readListFuel s₁.heap (s₁.heap.size + 1)
              childAddrs.toArray.toList =
            .ok ((List.finRange (σ.relationArity atom.symbol)).map
              fun index => atom.args index) := by
        rw [show childAddrs.toArray.toList = childAddrs from by simp]
        apply readListFuel_of_pointwise
        · simp [hLenArity, List.length_finRange]
        · intro k hk hk'
          have hp := hPoint k hk (by
            simpa [List.length_finRange, hLenArity] using hk)
          have hidx :
              ((List.finRange (σ.relationArity atom.symbol)).map
                fun index => atom.args index)[k]'hk' =
                atom.args ((List.finRange (σ.relationArity atom.symbol))[k]'(by
                  simpa [List.length_finRange, hLenArity] using hk)) := by
            simp
          rw [hidx]
          exact hp.2
      rw [hChildren]
      dsimp only
      rw [dif_pos (by simp [List.length_finRange])]
      refine congrArg Except.ok ?_
      cases atom with
      | mk symbol args =>
          refine congrArg (Atom.mk symbol) ?_
          funext index
          simp [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]

/-- Generic mapM preservation of a heap invariant. -/
theorem mapM_heap_preserves {σ : LPSignature} {ι β : Type _}
    {P : Heap σ → Prop} (g : ι → RuntimeMaterialize.BuilderM σ β) :
    ∀ (indices : List ι),
      (∀ i ∈ indices, ∀ {s₀ s₁ : BuilderState σ} {value : β},
        (g i).run s₀ = .ok (value, s₁) → P s₀.heap → P s₁.heap) →
      ∀ {s₀ s₁ : BuilderState σ} {values : List β},
        (indices.mapM g).run s₀ = .ok (values, s₁) →
        P s₀.heap → P s₁.heap := by
  intro indices
  induction indices with
  | nil =>
      intro _ s₀ s₁ values h hP
      rw [run_mapM_nil] at h
      cases h
      exact hP
  | cons head tailI tailIh =>
      intro elem s₀ s₁ values h hP
      rw [run_mapM_cons] at h
      cases hHead : (g head).run s₀ with
      | error e => rw [hHead] at h; cases h
      | ok headPair =>
          obtain ⟨headVal, sMid⟩ := headPair
          rw [hHead] at h
          dsimp only at h
          cases hTail : (tailI.mapM g).run sMid with
          | error e => rw [hTail] at h; cases h
          | ok tailPair =>
              obtain ⟨tailVals, sEnd⟩ := tailPair
              rw [hTail] at h
              dsimp only at h
              cases h
              exact tailIh (fun i hi => elem i (by simp [hi])) hTail
                (elem head (by simp) hHead hP)

/-- Atom materialization is a memory-level `Extends` history. -/
theorem materializeAtomAux_extends {σ : LPSignature} [DecidableEq σ.vars]
    (atom : Atom σ) {s₀ s₁ : BuilderState σ} {ratom : RuntimeAtom σ}
    (trail : Array (TrailEntry σ))
    (h : (materializeAtomAux atom).run s₀ = .ok (ratom, s₁)) :
    Extends { heap := s₀.heap, trail := trail }
      { heap := s₁.heap, trail := trail } := by
  simp only [materializeAtomAux, BuilderM.run_bind] at h
  cases hMap : ((List.finRange (σ.relationArity atom.symbol)).mapM
      fun index => materializeTermAux (atom.args index)).run s₀ with
  | error e => rw [hMap] at h; cases h
  | ok mapPair =>
      obtain ⟨childAddrs, sMid⟩ := mapPair
      rw [hMap] at h
      dsimp only at h
      cases h
      exact mapM_extends _ _
        (fun i _ => fun {s₀ s₁ value} trail' h' =>
          materializeTermAux_extends (atom.args i) trail' h') trail hMap

/-- Function-free atoms keep the heap function-free. -/
def AtomFF {σ : LPSignature} (atom : Atom σ) : Prop :=
  ∀ index, TermFF (atom.args index)

theorem materializeAtomAux_ff {σ : LPSignature} [DecidableEq σ.vars]
    (atom : Atom σ) {s₀ s₁ : BuilderState σ} {ratom : RuntimeAtom σ}
    (hFF : AtomFF atom)
    (h : (materializeAtomAux atom).run s₀ = .ok (ratom, s₁)) :
    FunctionFree s₀.heap → FunctionFree s₁.heap := by
  intro ff
  simp only [materializeAtomAux, BuilderM.run_bind] at h
  cases hMap : ((List.finRange (σ.relationArity atom.symbol)).mapM
      fun index => materializeTermAux (atom.args index)).run s₀ with
  | error e => rw [hMap] at h; cases h
  | ok mapPair =>
      obtain ⟨childAddrs, sMid⟩ := mapPair
      rw [hMap] at h
      dsimp only at h
      cases h
      exact mapM_heap_preserves _ _
        (fun i _ => fun {s₀ s₁ value} h' hp =>
          materializeTermAux_ff (atom.args i) (hFF i) h' hp)
        hMap ff

/-- mapM companion for atom round-trips: every materialized atom reads back
in the final builder heap. -/
theorem materializeAtomsMapM_spec {σ : LPSignature} [DecidableEq σ.vars] :
    ∀ (atoms : List (Atom σ)) {s₀ s₁ : BuilderState σ}
      {ratoms : List (RuntimeAtom σ)},
      (atoms.mapM materializeAtomAux).run s₀ = .ok (ratoms, s₁) →
      Heap.WellFormed s₀.heap → VarMapCells s₀ →
      BuildOk s₀ s₁ ∧ ratoms.length = atoms.length ∧
        ∀ k (hk : k < ratoms.length) (hk' : k < atoms.length),
          readAtom s₁.heap ratoms[k] = .ok atoms[k] := by
  intro atoms
  induction atoms with
  | nil =>
      intro s₀ s₁ ratoms h hwf hcells
      rw [run_mapM_nil] at h
      cases h
      exact ⟨BuildOk.rfl hwf hcells, _root_.rfl,
        fun k hk _ => absurd hk (Nat.not_lt_zero k)⟩
  | cons head tailA tailIh =>
      intro s₀ s₁ ratoms h hwf hcells
      rw [run_mapM_cons] at h
      cases hHead : (materializeAtomAux head).run s₀ with
      | error e => rw [hHead] at h; cases h
      | ok headPair =>
          obtain ⟨headAtom, sMid⟩ := headPair
          rw [hHead] at h
          dsimp only at h
          cases hTail : (tailA.mapM materializeAtomAux).run sMid with
          | error e => rw [hTail] at h; cases h
          | ok tailPair =>
              obtain ⟨tailAtoms, sEnd⟩ := tailPair
              rw [hTail] at h
              dsimp only at h
              cases h
              obtain ⟨bHead, hBound, hHeadRead⟩ :=
                materializeAtomAux_spec head hHead hwf hcells
              obtain ⟨bTail, hLen, hPoint⟩ :=
                tailIh hTail bHead.wf bHead.cells
              refine ⟨bHead.trans bTail,
                congrArg (fun n => n + 1) hLen, ?_⟩
              intro k hk hk'
              cases k with
              | zero =>
                  simp only [List.getElem_cons_zero]
                  exact readAtom_extend bHead.wf bTail.prefixEq bTail.sizeLe
                    hBound hHeadRead
              | succ k =>
                  have := hPoint k (by simpa using hk) (by simpa using hk')
                  simpa using this

/-- Invert `runChecked` success into its checks and the raw run. -/
theorem runChecked_ok {σ : LPSignature} {α : Type _}
    {action : RuntimeMaterialize.BuilderM σ α} {heap : Heap σ}
    {value : α} {state : BuilderState σ}
    (h : RuntimeMaterialize.runChecked action heap = .ok (value, state)) :
    heap.checkWellFormed = true ∧ heap.checkWellShaped = true ∧
      action.run (BuilderState.start heap) = .ok (value, state) ∧
      state.heap.checkWellFormed = true ∧
      state.heap.checkWellShaped = true := by
  unfold RuntimeMaterialize.runChecked at h
  by_cases hWF : heap.checkWellFormed
  case neg => rw [if_neg hWF] at h; cases h
  case pos =>
  rw [if_pos hWF] at h
  by_cases hWS : heap.checkWellShaped
  case neg => rw [if_neg hWS] at h; cases h
  case pos =>
  rw [if_pos hWS] at h
  cases hrun : action.run (BuilderState.start heap) with
  | error e => rw [hrun] at h; cases h
  | ok pair =>
      rw [hrun] at h
      dsimp only at h
      by_cases hWF' : pair.2.heap.checkWellFormed
      case neg => rw [if_neg hWF'] at h; cases h
      case pos =>
      rw [if_pos hWF'] at h
      by_cases hWS' : pair.2.heap.checkWellShaped
      case neg => rw [if_neg hWS'] at h; cases h
      case pos =>
      rw [if_pos hWS'] at h
      cases h
      exact ⟨hWF, hWS, by first | exact hrun | rfl, hWF', hWS'⟩

/-- **Public term round-trip**: materializing one finite term extends the
canonical memory by real allocations only, and reading the returned root from
that same heap yields exactly the source term. -/
theorem materializeTerm_roundtrip {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ} {term : Term σ}
    {result : MaterializedTerm σ}
    (h : materializeTerm memory term = .ok result) :
    Extends memory result.memory ∧
      Heap.readTerm result.memory.heap result.root = .ok term ∧
      Heap.WellFormed result.memory.heap ∧
      VarMapCells { heap := result.memory.heap, varMap := result.varMap } := by
  unfold materializeTerm at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeTermAux term) memory.heap with
  | error error => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨root, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      by_cases hRoot : root < state.heap.size
      · rw [if_pos hRoot] at h
        cases h
        obtain ⟨hWF, _, hrun, _, _⟩ := runChecked_ok hrc
        obtain ⟨build, _, hRead⟩ :=
          materializeTermAux_spec term hrun
            (Heap.wellFormed_of_check hWF)
            (fun pair hPair => by simp [BuilderState.start] at hPair)
        have hExtends := materializeTermAux_extends term memory.trail hrun
        refine ⟨?_, ?_, build.wf, build.cells⟩
        · simpa [BuilderState.start] using hExtends
        · simpa [RuntimeReadback.Heap.readTerm] using hRead
      · rw [if_neg hRoot] at h
        cases h

/-- **Public goals round-trip**: a materialized query's runtime atoms read
back verbatim in the result memory; the memory extends the caller's by real
allocations only; and the variable map is cell-coherent. -/
theorem materializeGoals_roundtrip {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ} {goals : List (Atom σ)}
    {result : MaterializedGoals σ}
    (h : materializeGoals memory goals = .ok result) :
    Extends memory result.memory ∧
    result.goals.length = goals.length ∧
    (∀ k (hk : k < result.goals.length) (hk' : k < goals.length),
      readAtom result.memory.heap result.goals[k] = .ok goals[k]) ∧
    Heap.WellFormed result.memory.heap ∧
    VarMapCells { heap := result.memory.heap, varMap := result.varMap } := by
  unfold materializeGoals at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeGoalsAux goals) memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeGoals, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨hWF, hWS, hrun, hWF', hWS'⟩ := runChecked_ok hrc
      by_cases hCheck : (runtimeGoals.all
          fun atom => atom.checkWellFormed state.heap) = true
      case neg => rw [if_neg hCheck] at h; cases h
      case pos =>
        rw [if_pos hCheck] at h
        cases h
        obtain ⟨bOk, hLen, hPoint⟩ :=
          materializeAtomsMapM_spec goals hrun
            (Heap.wellFormed_of_check hWF)
            (fun pair hp => by simp [BuilderState.start] at hp)
        have hExtends : Extends memory
            { heap := state.heap, trail := memory.trail } := by
          have := mapM_extends materializeAtomAux goals
            (fun i _ => fun {s₀ s₁ value} trail' h' =>
              materializeAtomAux_extends i trail' h')
            memory.trail hrun
          simpa [BuilderState.start] using this
        exact ⟨hExtends, hLen, hPoint, bOk.wf, bOk.cells⟩

/-- **Public clause round-trip**: a materialized (already standardized-apart)
clause reads back verbatim — head and every body atom — in the result
memory, which extends the caller's by real allocations only. -/
theorem materializeClause_roundtrip {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ} {clause : Clause σ}
    {result : MaterializedClause σ}
    (h : materializeClause memory clause = .ok result) :
    Extends memory result.memory ∧
    readAtom result.memory.heap result.clause.head = .ok clause.head ∧
    result.clause.body.length = clause.body.length ∧
    (∀ k (hk : k < result.clause.body.length)
      (hk' : k < clause.body.length),
      readAtom result.memory.heap result.clause.body[k] =
        .ok clause.body[k]) ∧
    Heap.WellFormed result.memory.heap ∧
    VarMapCells { heap := result.memory.heap, varMap := result.varMap } := by
  unfold materializeClause at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeClauseAux clause) memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeClause, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨hWF, hWS, hrun, hWF', hWS'⟩ := runChecked_ok hrc
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
                have hwf₀ : Heap.WellFormed
                    (BuilderState.start memory.heap).heap :=
                  Heap.wellFormed_of_check hWF
                have hcells₀ : VarMapCells (BuilderState.start memory.heap) :=
                  fun pair hp => by simp [BuilderState.start] at hp
                obtain ⟨bHead, hBound, hHeadRead⟩ :=
                  materializeAtomAux_spec clause.head hHead hwf₀ hcells₀
                obtain ⟨bBody, hLen, hPoint⟩ :=
                  materializeAtomsMapM_spec clause.body hBody
                    bHead.wf bHead.cells
                have hExtends : Extends memory
                    { heap := state.heap, trail := memory.trail } := by
                  have hHeadExt := materializeAtomAux_extends clause.head
                    memory.trail hHead
                  have hBodyExt := mapM_extends materializeAtomAux clause.body
                    (fun i _ => fun {s₀ s₁ value} trail' h' =>
                      materializeAtomAux_extends i trail' h')
                    memory.trail hBody
                  have := hHeadExt.trans hBodyExt
                  simpa [BuilderState.start] using this
                refine ⟨hExtends, ?_, hLen, hPoint, bBody.wf,
                  bBody.cells⟩
                exact readAtom_extend bHead.wf bBody.prefixEq bBody.sizeLe
                  hBound hHeadRead

/-! ## Stage 5b: identity injectivity is established at materialization

Materialization is where variable identities enter the heap.  Under a
freshness predicate separating the activation's identities from everything
already allocated — discharged at the call sites by the scope discipline —
the builder's variable-map bookkeeping yields identity injectivity outright:
a fresh identity is allocated at most once because the variable map is
consulted first, and a fresh identity can never collide with an old cell
because old cells are never fresh. -/


/-- A failed association-list lookup excludes every entry with that key. -/
theorem lookup_none_not_mem {σ : LPSignature} [DecidableEq σ.vars] :
    ∀ {varMap : List (σ.vars × Addr)} {identity : σ.vars},
      List.lookup identity varMap = none →
      ∀ address, (identity, address) ∉ varMap := by
  intro varMap
  induction varMap with
  | nil =>
      intro _ _ address hmem
      cases hmem
  | cons head tailM ih =>
      intro identity h address hmem
      obtain ⟨key, value⟩ := head
      by_cases he : identity = key
      · subst he
        simp [List.lookup] at h
      · have hne : (identity == key) = false := by simpa using he
        simp only [List.lookup, hne] at h
        rcases List.mem_cons.mp hmem with heq | hmem'
        · exact he (by cases heq; rfl)
        · exact ih h address hmem'

/-- The freshness bundle carried through one materialization: the variable
map is functional, every heap cell carrying a fresh identity is registered
in the variable map, and the whole heap is identity-injective. -/
structure FreshInv {σ : LPSignature} (Fresh : σ.vars → Prop)
    (s : BuilderState σ) : Prop where
  functional : ∀ (identity : σ.vars) (a b : Addr),
    (identity, a) ∈ s.varMap → (identity, b) ∈ s.varMap → a = b
  registered : ∀ (a : Addr) (identity : σ.vars) (link : Option Addr),
    s.heap[a]? = some (Cell.var identity link) → Fresh identity →
      (identity, a) ∈ s.varMap
  injective : IdentityInjective s.heap

/-- Pushing a non-variable cell preserves the freshness bundle. -/
theorem FreshInv.push_nonvar {σ : LPSignature} {Fresh : σ.vars → Prop}
    {s : BuilderState σ} (hInv : FreshInv Fresh s) {cell : Cell σ}
    (hNonvar : ∀ identity link, cell ≠ Cell.var identity link) :
    FreshInv Fresh { heap := s.heap.push cell, varMap := s.varMap } where
  functional := hInv.functional
  registered := by
    intro a identity link hcell hFid
    rcases getElem?_push_cases hcell with ⟨_, hold⟩ | ⟨_, hcelleq⟩
    · exact hInv.registered a identity link hold hFid
    · exact absurd hcelleq.symm (hNonvar identity link)
  injective := by
    intro a b identity la lb ha hb
    rcases getElem?_push_cases ha with ⟨_, haOld⟩ | ⟨_, haNew⟩
    · rcases getElem?_push_cases hb with ⟨_, hbOld⟩ | ⟨_, hbNew⟩
      · exact hInv.injective a b identity la lb haOld hbOld
      · exact absurd hbNew.symm (hNonvar identity lb)
    · exact absurd haNew.symm (hNonvar identity la)

/-- Generic mapM preservation of a builder-state invariant. -/
theorem mapM_state_preserves {σ : LPSignature} {ι β : Type _}
    {P : BuilderState σ → Prop} (g : ι → RuntimeMaterialize.BuilderM σ β) :
    ∀ (indices : List ι),
      (∀ i ∈ indices, ∀ {s₀ s₁ : BuilderState σ} {value : β},
        (g i).run s₀ = .ok (value, s₁) → P s₀ → P s₁) →
      ∀ {s₀ s₁ : BuilderState σ} {values : List β},
        (indices.mapM g).run s₀ = .ok (values, s₁) →
        P s₀ → P s₁ := by
  intro indices
  induction indices with
  | nil =>
      intro _ s₀ s₁ values h hP
      rw [run_mapM_nil] at h
      cases h
      exact hP
  | cons head tailI tailIh =>
      intro elem s₀ s₁ values h hP
      rw [run_mapM_cons] at h
      cases hHead : (g head).run s₀ with
      | error e => rw [hHead] at h; cases h
      | ok headPair =>
          obtain ⟨headVal, sMid⟩ := headPair
          rw [hHead] at h
          dsimp only at h
          cases hTail : (tailI.mapM g).run sMid with
          | error e => rw [hTail] at h; cases h
          | ok tailPair =>
              obtain ⟨tailVals, sEnd⟩ := tailPair
              rw [hTail] at h
              dsimp only at h
              cases h
              exact tailIh (fun i hi => elem i (by simp [hi])) hTail
                (elem head (by simp) hHead hP)

/-- Term materialization preserves the freshness bundle when every variable
of the term is fresh. -/
theorem materializeTermAux_freshInv {σ : LPSignature} [DecidableEq σ.vars]
    {Fresh : σ.vars → Prop} :
    ∀ (t : Term σ) {s₀ s₁ : BuilderState σ} {address : Addr},
      (∀ v ∈ t.freeVars, Fresh v) →
      (materializeTermAux t).run s₀ = .ok (address, s₁) →
      FreshInv Fresh s₀ → FreshInv Fresh s₁ := by
  intro t
  induction t with
  | var identity =>
      intro s₀ s₁ address hFreshT h hInv
      have hFreshId : Fresh identity :=
        hFreshT identity (by simp [Term.freeVars])
      simp only [materializeTermAux, BuilderM.run_bind, BuilderM.get] at h
      cases hlook : List.lookup identity s₀.varMap with
      | some existing =>
          simp only [hlook, BuilderM.run_pure] at h
          cases h
          exact hInv
      | none =>
          simp only [hlook, BuilderM.run_bind] at h
          cases hAlloc : (RuntimeMaterialize.allocate
              (Cell.var identity none)).run s₀ with
          | error e => rw [hAlloc] at h; cases h
          | ok pair =>
              obtain ⟨addr₀, sMid⟩ := pair
              rw [hAlloc] at h
              obtain ⟨haddr, hheap, hvar⟩ := allocate_run_spec hAlloc
              simp only [BuilderM.set, BuilderM.run_pure] at h
              cases h
              subst haddr
              refine ⟨?_, ?_, ?_⟩
              · -- functionality of the extended variable map
                intro id a b ha hb
                rcases List.mem_cons.mp ha with haH | haT
                · rcases List.mem_cons.mp hb with hbH | hbT
                  · rw [Prod.mk.injEq] at haH hbH
                    exact haH.2.trans hbH.2.symm
                  · rw [Prod.mk.injEq] at haH
                    rw [hvar] at hbT
                    exact absurd (haH.1 ▸ hbT)
                      (lookup_none_not_mem hlook b)
                · rcases List.mem_cons.mp hb with hbH | hbT
                  · rw [Prod.mk.injEq] at hbH
                    rw [hvar] at haT
                    exact absurd (hbH.1 ▸ haT)
                      (lookup_none_not_mem hlook a)
                  · rw [hvar] at haT hbT
                    exact hInv.functional id a b haT hbT
              · -- fresh cells stay registered
                intro a id link hcell hFid
                rw [hheap] at hcell
                rcases getElem?_push_cases hcell with ⟨_, hold⟩ | ⟨heq, hcelleq⟩
                · have := hInv.registered a id link hold hFid
                  rw [← hvar] at this
                  exact List.mem_cons_of_mem _ this
                · injection hcelleq with hid _
                  subst heq
                  subst hid
                  exact List.mem_cons_self ..
              · -- injectivity with one genuinely new identity
                intro a b id la lb ha hb
                rw [hheap] at ha hb
                rcases getElem?_push_cases ha with ⟨_, haOld⟩ | ⟨haEq, haNew⟩
                · rcases getElem?_push_cases hb with ⟨_, hbOld⟩ | ⟨hbEq, hbNew⟩
                  · exact hInv.injective a b id la lb haOld hbOld
                  · injection hbNew with hid _
                    subst hid
                    exact absurd (hInv.registered a id la haOld hFreshId)
                      (lookup_none_not_mem hlook a)
                · rcases getElem?_push_cases hb with ⟨_, hbOld⟩ | ⟨hbEq, hbNew⟩
                  · injection haNew with hid _
                    subst hid
                    exact absurd (hInv.registered b id lb hbOld hFreshId)
                      (lookup_none_not_mem hlook b)
                  · exact haEq.trans hbEq.symm
  | const symbol =>
      intro s₀ s₁ address _ h hInv
      simp only [materializeTermAux] at h
      obtain ⟨_, hheap, hvar⟩ := allocate_run_spec h
      have := hInv.push_nonvar (cell := Cell.const symbol)
        (fun _ _ hEq => by cases hEq)
      rw [← hheap, ← hvar] at this
      exact this
  | app symbol args ih =>
      intro s₀ s₁ address hFreshT h hInv
      simp only [materializeTermAux, BuilderM.run_bind] at h
      cases hMap : ((List.finRange (σ.functionArity symbol)).mapM fun index =>
          materializeTermAux (args index)).run s₀ with
      | error e => rw [hMap] at h; cases h
      | ok mapPair =>
          obtain ⟨childAddrs, sMid⟩ := mapPair
          rw [hMap] at h
          obtain ⟨_, hheap, hvar⟩ := allocate_run_spec h
          have hMid : FreshInv Fresh sMid :=
            mapM_state_preserves _ _
              (fun i _ => fun {s₀ s₁ value} h' hp =>
                ih i (fun v hv => hFreshT v (by
                  simp only [Term.freeVars]
                  exact Finset.mem_biUnion.mpr
                    ⟨i, Finset.mem_univ i, hv⟩)) h' hp)
              hMap hInv
          have := hMid.push_nonvar
            (cell := Cell.app symbol childAddrs.toArray)
            (fun _ _ hEq => by cases hEq)
          rw [← hheap, ← hvar] at this
          exact this

/-- Atom materialization preserves the freshness bundle when every variable
of the atom is fresh. -/
theorem materializeAtomAux_freshInv {σ : LPSignature} [DecidableEq σ.vars]
    {Fresh : σ.vars → Prop} (atom : Atom σ)
    {s₀ s₁ : BuilderState σ} {ratom : RuntimeAtom σ}
    (hFresh : ∀ v ∈ atom.freeVars, Fresh v)
    (h : (materializeAtomAux atom).run s₀ = .ok (ratom, s₁)) :
    FreshInv Fresh s₀ → FreshInv Fresh s₁ := by
  intro hInv
  simp only [materializeAtomAux, BuilderM.run_bind] at h
  cases hMap : ((List.finRange (σ.relationArity atom.symbol)).mapM
      fun index => materializeTermAux (atom.args index)).run s₀ with
  | error e => rw [hMap] at h; cases h
  | ok mapPair =>
      obtain ⟨childAddrs, sMid⟩ := mapPair
      rw [hMap] at h
      dsimp only at h
      cases h
      exact mapM_state_preserves _ _
        (fun i _ => fun {s₀ s₁ value} h' hp =>
          materializeTermAux_freshInv (atom.args i)
            (fun v hv => hFresh v (by
              exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩))
            h' hp)
        hMap hInv

/-- **Goal materialization establishes injectivity.**  If the caller's heap
is identity-injective and carries no fresh identities, and every goal
variable is fresh, then the materialized result is identity-injective and
every fresh-identity cell is registered in the returned variable map. -/
theorem materializeGoals_freshInv {σ : LPSignature} [DecidableEq σ.vars]
    {Fresh : σ.vars → Prop} {memory : Memory σ} {goals : List (Atom σ)}
    {result : MaterializedGoals σ}
    (h : materializeGoals memory goals = .ok result)
    (hFresh : ∀ atom ∈ goals, ∀ v ∈ atom.freeVars, Fresh v)
    (hFree : ∀ (a : Addr) (identity : σ.vars) (link : Option Addr),
      memory.heap[a]? = some (Cell.var identity link) → ¬ Fresh identity)
    (hInj : IdentityInjective memory.heap) :
    FreshInv Fresh
      { heap := result.memory.heap, varMap := result.varMap } := by
  unfold materializeGoals at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeGoalsAux goals) memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeGoals, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨_, _, hrun, _, _⟩ := runChecked_ok hrc
      by_cases hCheck : (runtimeGoals.all
          fun atom => atom.checkWellFormed state.heap) = true
      case neg => rw [if_neg hCheck] at h; cases h
      case pos =>
        rw [if_pos hCheck] at h
        cases h
        have hStart : FreshInv Fresh (BuilderState.start memory.heap) := by
          refine ⟨?_, ?_, ?_⟩
          · intro id a b ha _
            cases ha
          · intro a id link hcell hFid
            exact absurd hFid (hFree a id link hcell)
          · exact hInj
        exact mapM_state_preserves materializeAtomAux goals
          (fun i hi => fun {s₀ s₁ value} h' hp =>
            materializeAtomAux_freshInv i (hFresh i hi) h' hp)
          hrun hStart

/-- **Clause materialization establishes injectivity**, under the same
freshness split: old cells are never fresh, clause variables always are. -/
theorem materializeClause_freshInv {σ : LPSignature} [DecidableEq σ.vars]
    {Fresh : σ.vars → Prop} {memory : Memory σ} {clause : Clause σ}
    {result : MaterializedClause σ}
    (h : materializeClause memory clause = .ok result)
    (hFreshHead : ∀ v ∈ clause.head.freeVars, Fresh v)
    (hFreshBody : ∀ atom ∈ clause.body, ∀ v ∈ atom.freeVars, Fresh v)
    (hFree : ∀ (a : Addr) (identity : σ.vars) (link : Option Addr),
      memory.heap[a]? = some (Cell.var identity link) → ¬ Fresh identity)
    (hInj : IdentityInjective memory.heap) :
    FreshInv Fresh
      { heap := result.memory.heap, varMap := result.varMap } := by
  unfold materializeClause at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeClauseAux clause) memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeClause, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨_, _, hrun, _, _⟩ := runChecked_ok hrc
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
                have hStart : FreshInv Fresh
                    (BuilderState.start memory.heap) := by
                  refine ⟨?_, ?_, ?_⟩
                  · intro id a b ha _
                    cases ha
                  · intro a id link hcell hFid
                    exact absurd hFid (hFree a id link hcell)
                  · exact hInj
                have hMid : FreshInv Fresh sMid :=
                  materializeAtomAux_freshInv clause.head hFreshHead
                    hHead hStart
                exact mapM_state_preserves materializeAtomAux clause.body
                  (fun i hi => fun {s₀ s₁ value} h' hp =>
                    materializeAtomAux_freshInv i (hFreshBody i hi) h' hp)
                  hBody hMid

/-! ### Scope discipline discharges freshness

Every variable of a term copied `atScope scope` carries exactly that scope,
so `Fresh := (·.scope = scope)` splits new activations from every heap
whose identities all live at strictly lower scopes. -/

theorem Term.freeVars_atScope {σ : LPSignature} [DecidableEq σ.vars]
    (scope : Nat) :
    ∀ (t : Term σ) (v : ScopedVar σ.vars),
      v ∈ (Term.atScope scope t).freeVars → v.scope = scope := by
  intro t
  induction t with
  | var w =>
      intro v hv
      simp only [Term.atScope, Term.renameVars_var, Term.freeVars,
        Finset.mem_singleton] at hv
      subst hv
      rfl
  | const c =>
      intro v hv
      simp [Term.atScope, Term.renameVars_const, Term.freeVars] at hv
  | app f ts ih =>
      intro v hv
      simp only [Term.atScope, Term.renameVars_app, Term.freeVars] at hv
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
      exact ih i v hi

theorem Atom.freeVars_atScope {σ : LPSignature} [DecidableEq σ.vars]
    (scope : Nat) (atom : Atom σ) (v : ScopedVar σ.vars)
    (hv : v ∈ (Atom.atScope scope atom).freeVars) : v.scope = scope := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
  exact Term.freeVars_atScope scope (atom.args i) v hi

/-- Every variable identity in the heap lives strictly below the bound.
This is the run invariant that makes each new activation scope fresh. -/
def HeapScopesBelow {σ : LPSignature} (bound : Nat)
    (heap : Heap σ.scoped) : Prop :=
  ∀ (a : Addr) (identity : ScopedVar σ.vars) (link : Option Addr),
    heap[a]? = some (Cell.var identity link) → identity.scope < bound

/-- Scoped instantiation for query materialization: a query copied at
`scope` over a heap whose scopes are below `scope` builds an
identity-injective heap with all `scope`-cells registered. -/
theorem materializeGoals_scoped_freshInv {σ : LPSignature}
    [DecidableEq σ.vars] {memory : Memory σ.scoped}
    {goals : List (Atom σ)} {scope : Nat}
    {result : MaterializedGoals σ.scoped}
    (h : materializeGoals memory (queryAtScope scope goals) = .ok result)
    (hBelow : HeapScopesBelow scope memory.heap)
    (hInj : IdentityInjective memory.heap) :
    FreshInv (fun v : ScopedVar σ.vars => v.scope = scope)
      { heap := result.memory.heap, varMap := result.varMap } :=
  materializeGoals_freshInv h
    (fun atom hatom v hv => by
      obtain ⟨source, _, rfl⟩ := List.mem_map.mp hatom
      exact Atom.freeVars_atScope scope source v hv)
    (fun a id link hcell => Nat.ne_of_lt (hBelow a id link hcell))
    hInj

/-- Scoped instantiation for clause activation: a clause standardized apart
at `scope` over a heap whose scopes are below `scope` builds an
identity-injective heap with all `scope`-cells registered. -/
theorem materializeClause_scoped_freshInv {σ : LPSignature}
    [DecidableEq σ.vars] {memory : Memory σ.scoped}
    {clause : Clause σ} {scope : Nat}
    {result : MaterializedClause σ.scoped}
    (h : materializeClause memory (clause.atScope scope) = .ok result)
    (hBelow : HeapScopesBelow scope memory.heap)
    (hInj : IdentityInjective memory.heap) :
    FreshInv (fun v : ScopedVar σ.vars => v.scope = scope)
      { heap := result.memory.heap, varMap := result.varMap } :=
  materializeClause_freshInv h
    (fun v hv => Atom.freeVars_atScope scope clause.head v hv)
    (fun atom hatom v hv => by
      obtain ⟨source, _, rfl⟩ := List.mem_map.mp hatom
      exact Atom.freeVars_atScope scope source v hv)
    (fun a id link hcell => Nat.ne_of_lt (hBelow a id link hcell))
    hInj

/-! ## Stage 6: heap invariants across materialization, generically

Materialization pushes exactly three cell shapes — an unbound variable
carrying a term identity, a constant, or a compound over already-built
children.  One parametric induction therefore transports every heap
invariant that survives those three pushes; `DescendingOrConst` and
`HeapScopesBelow` are the two instances the query run needs. -/

/-- Generic transport of a heap invariant along term materialization: `P`
must survive the three pushed shapes, with variable pushes drawing their
identities from the term (predicate `Q`). -/
theorem materializeTermAux_cell_preserves {σ : LPSignature}
    [DecidableEq σ.vars] (P : Heap σ → Prop) (Q : σ.vars → Prop)
    (hVar : ∀ (heap : Heap σ) (identity : σ.vars),
      P heap → Q identity → P (heap.push (Cell.var identity none)))
    (hConst : ∀ (heap : Heap σ) (symbol : σ.constants),
      P heap → P (heap.push (Cell.const symbol)))
    (hApp : ∀ (heap : Heap σ) (symbol : σ.functionSymbols)
      (args : Array Addr), P heap → P (heap.push (Cell.app symbol args))) :
    ∀ (t : Term σ) {s₀ s₁ : BuilderState σ} {address : Addr},
      (∀ v ∈ t.freeVars, Q v) →
      (materializeTermAux t).run s₀ = .ok (address, s₁) →
      P s₀.heap → P s₁.heap := by
  intro t
  induction t with
  | var identity =>
      intro s₀ s₁ address hQ h hP
      have hQid : Q identity := hQ identity (by simp [Term.freeVars])
      simp only [materializeTermAux, BuilderM.run_bind, BuilderM.get] at h
      cases hlook : List.lookup identity s₀.varMap with
      | some existing =>
          simp only [hlook, BuilderM.run_pure] at h
          cases h
          exact hP
      | none =>
          simp only [hlook, BuilderM.run_bind] at h
          cases hAlloc : (RuntimeMaterialize.allocate
              (Cell.var identity none)).run s₀ with
          | error e => rw [hAlloc] at h; cases h
          | ok pair =>
              obtain ⟨addr₀, sMid⟩ := pair
              rw [hAlloc] at h
              obtain ⟨_, hheap, _⟩ := allocate_run_spec hAlloc
              simp only [BuilderM.set, BuilderM.run_pure] at h
              cases h
              rw [hheap]
              exact hVar s₀.heap identity hP hQid
  | const symbol =>
      intro s₀ s₁ address _ h hP
      simp only [materializeTermAux] at h
      obtain ⟨_, hheap, _⟩ := allocate_run_spec h
      rw [hheap]
      exact hConst s₀.heap symbol hP
  | app symbol args ih =>
      intro s₀ s₁ address hQ h hP
      simp only [materializeTermAux, BuilderM.run_bind] at h
      cases hMap : ((List.finRange (σ.functionArity symbol)).mapM fun index =>
          materializeTermAux (args index)).run s₀ with
      | error e => rw [hMap] at h; cases h
      | ok mapPair =>
          obtain ⟨childAddrs, sMid⟩ := mapPair
          rw [hMap] at h
          obtain ⟨_, hheap, _⟩ := allocate_run_spec h
          have hMid : P sMid.heap :=
            mapM_heap_preserves _ _
              (fun i _ => fun {s₀ s₁ value} h' hp =>
                ih i (fun v hv => hQ v (by
                  simp only [Term.freeVars]
                  exact Finset.mem_biUnion.mpr
                    ⟨i, Finset.mem_univ i, hv⟩)) h' hp)
              hMap hP
          rw [hheap]
          exact hApp sMid.heap symbol childAddrs.toArray hMid

/-- Atom-level generic transport. -/
theorem materializeAtomAux_cell_preserves {σ : LPSignature}
    [DecidableEq σ.vars] (P : Heap σ → Prop) (Q : σ.vars → Prop)
    (hVar : ∀ (heap : Heap σ) (identity : σ.vars),
      P heap → Q identity → P (heap.push (Cell.var identity none)))
    (hConst : ∀ (heap : Heap σ) (symbol : σ.constants),
      P heap → P (heap.push (Cell.const symbol)))
    (hApp : ∀ (heap : Heap σ) (symbol : σ.functionSymbols)
      (args : Array Addr), P heap → P (heap.push (Cell.app symbol args)))
    (atom : Atom σ) {s₀ s₁ : BuilderState σ} {ratom : RuntimeAtom σ}
    (hQ : ∀ v ∈ atom.freeVars, Q v)
    (h : (materializeAtomAux atom).run s₀ = .ok (ratom, s₁)) :
    P s₀.heap → P s₁.heap := by
  intro hP
  simp only [materializeAtomAux, BuilderM.run_bind] at h
  cases hMap : ((List.finRange (σ.relationArity atom.symbol)).mapM
      fun index => materializeTermAux (atom.args index)).run s₀ with
  | error e => rw [hMap] at h; cases h
  | ok mapPair =>
      obtain ⟨childAddrs, sMid⟩ := mapPair
      rw [hMap] at h
      dsimp only at h
      cases h
      exact mapM_heap_preserves _ _
        (fun i _ => fun {s₀ s₁ value} h' hp =>
          materializeTermAux_cell_preserves P Q hVar hConst hApp
            (atom.args i)
            (fun v hv => hQ v
              (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩))
            h' hp)
        hMap hP

/-! ### Instance 1: descending links -/

/-- Pushing any cell that is not a bound variable preserves descending
links: the new cell adds no link, old links and their constant targets are
untouched. -/
theorem descendingOrConst_push {σ : LPSignature} {heap : Heap σ}
    {cell : Cell σ}
    (hNotBound : ∀ (identity : σ.vars) (target : Addr),
      cell ≠ Cell.var identity (some target))
    (hDesc : DescendingOrConst heap) :
    DescendingOrConst (heap.push cell) := by
  intro a id t hcellA
  rcases getElem?_push_cases hcellA with ⟨_, hold⟩ | ⟨_, hcelleq⟩
  · rcases hDesc a id t hold with hord | ⟨symbol, hconst⟩
    · exact .inl hord
    · exact .inr ⟨symbol,
        by rw [getElem?_push_lt heap cell (lt_of_getElem?_some hconst)]
           exact hconst⟩
  · exact absurd hcelleq.symm (hNotBound id t)

/-- Goal materialization preserves descending links. -/
theorem materializeGoals_descendingOrConst {σ : LPSignature}
    [DecidableEq σ.vars] {memory : Memory σ} {goals : List (Atom σ)}
    {result : MaterializedGoals σ}
    (h : materializeGoals memory goals = .ok result)
    (hDesc : DescendingOrConst memory.heap) :
    DescendingOrConst result.memory.heap := by
  unfold materializeGoals at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeGoalsAux goals) memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeGoals, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨_, _, hrun, _, _⟩ := runChecked_ok hrc
      by_cases hCheck : (runtimeGoals.all
          fun atom => atom.checkWellFormed state.heap) = true
      case neg => rw [if_neg hCheck] at h; cases h
      case pos =>
        rw [if_pos hCheck] at h
        cases h
        exact mapM_heap_preserves materializeAtomAux goals
          (fun i _ => fun {s₀ s₁ value} h' hp =>
            materializeAtomAux_cell_preserves DescendingOrConst
              (fun _ => True)
              (fun heap identity hp' _ =>
                descendingOrConst_push (fun _ _ hEq => by cases hEq) hp')
              (fun heap symbol hp' =>
                descendingOrConst_push (fun _ _ hEq => by cases hEq) hp')
              (fun heap symbol args hp' =>
                descendingOrConst_push (fun _ _ hEq => by cases hEq) hp')
              i (fun _ _ => trivial) h' hp)
          hrun hDesc

/-- Clause materialization preserves descending links. -/
theorem materializeClause_descendingOrConst {σ : LPSignature}
    [DecidableEq σ.vars] {memory : Memory σ} {clause : Clause σ}
    {result : MaterializedClause σ}
    (h : materializeClause memory clause = .ok result)
    (hDesc : DescendingOrConst memory.heap) :
    DescendingOrConst result.memory.heap := by
  unfold materializeClause at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeClauseAux clause) memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeClause, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨_, _, hrun, _, _⟩ := runChecked_ok hrc
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
                have hMid : DescendingOrConst sMid.heap :=
                  materializeAtomAux_cell_preserves DescendingOrConst
                    (fun _ => True)
                    (fun heap identity hp _ =>
                      descendingOrConst_push (fun _ _ hEq => by cases hEq) hp)
                    (fun heap symbol hp =>
                      descendingOrConst_push (fun _ _ hEq => by cases hEq) hp)
                    (fun heap symbol args hp =>
                      descendingOrConst_push (fun _ _ hEq => by cases hEq) hp)
                    clause.head (fun _ _ => trivial) hHead hDesc
                exact mapM_heap_preserves materializeAtomAux clause.body
                  (fun i _ => fun {s₀ s₁ value} h' hp =>
                    materializeAtomAux_cell_preserves DescendingOrConst
                      (fun _ => True)
                      (fun heap identity hp' _ =>
                        descendingOrConst_push
                          (fun _ _ hEq => by cases hEq) hp')
                      (fun heap symbol hp' =>
                        descendingOrConst_push
                          (fun _ _ hEq => by cases hEq) hp')
                      (fun heap symbol args hp' =>
                        descendingOrConst_push
                          (fun _ _ hEq => by cases hEq) hp')
                      i (fun _ _ => trivial) h' hp)
                  hBody hMid

/-! ### Instance 2: scope bounds -/

/-- The executable scope check means exactly `HeapScopesBelow`. -/
theorem heapScopesBelow_iff {σ : LPSignature} (heap : Heap σ.scoped)
    (bound : Nat) :
    RuntimeQuery.heapScopesBelow heap bound = true ↔
      HeapScopesBelow bound heap := by
  constructor
  · intro h a identity link hcell
    have := Array.all_eq_true.mp h
    have hlt := lt_of_getElem?_some hcell
    have hbelow := this a hlt
    have hget : heap[a] = Cell.var identity link := by
      have := hcell
      rwa [Array.getElem?_eq_getElem hlt, Option.some_inj] at this
    rw [hget] at hbelow
    simpa [RuntimeQuery.Cell.scopeBelow] using hbelow
  · intro h
    apply Array.all_eq_true.mpr
    intro a hlt
    cases hcell : heap[a] with
    | var identity link =>
        have : heap[a]? = some (Cell.var identity link) := by
          rw [Array.getElem?_eq_getElem hlt, hcell]
        simpa [RuntimeQuery.Cell.scopeBelow] using h a identity link this
    | const symbol => simp [RuntimeQuery.Cell.scopeBelow]
    | app symbol args => simp [RuntimeQuery.Cell.scopeBelow]

/-- Pushing a cell whose identity (if any) is below the bound preserves the
scope bound. -/
theorem heapScopesBelow_push {σ : LPSignature} {heap : Heap σ.scoped}
    {bound : Nat} {cell : Cell σ.scoped}
    (hcell : ∀ (identity : ScopedVar σ.vars) (link : Option Addr),
      cell = Cell.var identity link → identity.scope < bound)
    (h : HeapScopesBelow bound heap) :
    HeapScopesBelow bound (heap.push cell) := by
  intro a identity link hcellA
  rcases getElem?_push_cases hcellA with ⟨_, hold⟩ | ⟨_, hcelleq⟩
  · exact h a identity link hold
  · exact hcell identity link hcelleq.symm

/-- Goal materialization at a scope strictly below the bound preserves the
scope bound. -/
theorem materializeGoals_scopesBelow {σ : LPSignature}
    [DecidableEq σ.vars] {memory : Memory σ.scoped}
    {goals : List (Atom σ)} {queryScope bound : Nat}
    {result : MaterializedGoals σ.scoped}
    (h : materializeGoals memory (queryAtScope queryScope goals) =
      .ok result)
    (hScope : queryScope < bound)
    (hBelow : HeapScopesBelow bound memory.heap) :
    HeapScopesBelow bound result.memory.heap := by
  unfold materializeGoals at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeGoalsAux (queryAtScope queryScope goals))
      memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeGoals, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨_, _, hrun, _, _⟩ := runChecked_ok hrc
      by_cases hCheck : (runtimeGoals.all
          fun atom => atom.checkWellFormed state.heap) = true
      case neg => rw [if_neg hCheck] at h; cases h
      case pos =>
        rw [if_pos hCheck] at h
        cases h
        refine mapM_heap_preserves materializeAtomAux
          (queryAtScope queryScope goals)
          (fun i hi => fun {s₀ s₁ value} h' hp => ?_) hrun hBelow
        obtain ⟨source, _, rfl⟩ := List.mem_map.mp hi
        exact materializeAtomAux_cell_preserves (HeapScopesBelow bound)
          (fun v => v.scope < bound)
          (fun heap identity hp' hQ =>
            heapScopesBelow_push
              (fun id link hEq => by cases hEq; exact hQ) hp')
          (fun heap symbol hp' =>
            heapScopesBelow_push (fun _ _ hEq => by cases hEq) hp')
          (fun heap symbol args hp' =>
            heapScopesBelow_push (fun _ _ hEq => by cases hEq) hp')
          (source.atScope queryScope)
          (fun v hv => by
            rw [Atom.freeVars_atScope queryScope source v hv]
            exact hScope)
          h' hp

/-- Clause activation at a scope strictly below the bound preserves the
scope bound. -/
theorem materializeClause_scopesBelow {σ : LPSignature}
    [DecidableEq σ.vars] {memory : Memory σ.scoped}
    {clause : Clause σ} {activationScope bound : Nat}
    {result : MaterializedClause σ.scoped}
    (h : materializeClause memory (clause.atScope activationScope) =
      .ok result)
    (hScope : activationScope < bound)
    (hBelow : HeapScopesBelow bound memory.heap) :
    HeapScopesBelow bound result.memory.heap := by
  unfold materializeClause at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeClauseAux (clause.atScope activationScope))
      memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeClause, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨_, _, hrun, _, _⟩ := runChecked_ok hrc
      by_cases hCheck :
          runtimeClause.checkWellFormed state.heap = true
      case neg => rw [if_neg hCheck] at h; cases h
      case pos =>
        rw [if_pos hCheck] at h
        cases h
        simp only [materializeClauseAux, BuilderM.run_bind] at hrun
        cases hHead : (materializeAtomAux
            ((clause.atScope activationScope).head)).run
            (BuilderState.start memory.heap) with
        | error e => rw [hHead] at hrun; cases hrun
        | ok headPair =>
            obtain ⟨headAtom, sMid⟩ := headPair
            rw [hHead] at hrun
            dsimp only at hrun
            cases hBody : (((clause.atScope activationScope).body).mapM
                materializeAtomAux).run sMid with
            | error e => rw [hBody] at hrun; cases hrun
            | ok bodyPair =>
                obtain ⟨bodyAtoms, sEnd⟩ := bodyPair
                rw [hBody] at hrun
                dsimp only at hrun
                cases hrun
                have hAtomPass : ∀ (atom : Atom σ)
                    {s₀ s₁ : BuilderState σ.scoped}
                    {ratom : RuntimeAtom σ.scoped},
                    (materializeAtomAux (atom.atScope activationScope)).run
                      s₀ = .ok (ratom, s₁) →
                    HeapScopesBelow bound s₀.heap →
                    HeapScopesBelow bound s₁.heap := by
                  intro atom s₀ s₁ ratom h' hp
                  exact materializeAtomAux_cell_preserves
                    (HeapScopesBelow bound) (fun v => v.scope < bound)
                    (fun heap identity hp' hQ =>
                      heapScopesBelow_push
                        (fun id link hEq => by cases hEq; exact hQ) hp')
                    (fun heap symbol hp' =>
                      heapScopesBelow_push
                        (fun _ _ hEq => by cases hEq) hp')
                    (fun heap symbol args hp' =>
                      heapScopesBelow_push
                        (fun _ _ hEq => by cases hEq) hp')
                    (atom.atScope activationScope)
                    (fun v hv => by
                      rw [Atom.freeVars_atScope activationScope atom v hv]
                      exact hScope)
                    h' hp
                have hMid : HeapScopesBelow bound sMid.heap :=
                  hAtomPass clause.head hHead hBelow
                refine mapM_heap_preserves materializeAtomAux
                  ((clause.atScope activationScope).body)
                  (fun i hi => fun {s₀ s₁ value} h' hp => ?_)
                  hBody hMid
                obtain ⟨source, _, rfl⟩ := List.mem_map.mp hi
                exact hAtomPass source h' hp

end RuntimeUnificationSoundness
end Mettapedia.Logic.LP
