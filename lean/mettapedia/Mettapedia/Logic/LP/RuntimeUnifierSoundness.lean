import Mettapedia.Logic.LP.RuntimeRestoration

/-!
# Unifier soundness: run invariants of the graph unification machine

Successful runs make the agenda's readbacks equal, extend the entry heap
by bindings only (a real write history, size-exact), and preserve
descending links; failing runs restore the entry memory verbatim.
Readback is total on the ordered function-free heaps these runs preserve.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeUnificationSoundness

open RuntimeTerm RuntimeUnification RuntimeReadback
/-! ## The success run invariant -/

/-- `Heap.deref` is `derefLoop` at the standard budget (definitional). -/
theorem deref_root {σ : LPSignature} {heap : Heap σ} {address root : Addr}
    (h : Heap.deref heap address = .ok (.root root)) :
    Heap.derefLoop heap (heap.size + 1) address = .ok (.root root) := h

/-- `beginRollback` never reaches `.success`. -/
theorem beginRollback_no_success {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (fuel : Nat) (c : Configuration σ)
    (reason : RollbackReason) (m : Memory σ) :
    runSteps fuel (beginRollback c reason) ≠ .terminal (.success m) :=
  rollback_no_success fuel { c with agenda := [], phase := .rollback reason }
    reason m rfl

/-- A successful graph-unification run closes a finite certificate over the
actual heap.  Each original equation is represented by that same certificate;
cycles remain graph cycles rather than being mistaken for finite terms. -/
def GraphCertificate {σ : LPSignature} (heap : Heap σ)
    (equations : List (Addr × Addr)) : Prop :=
  ∃ visited, VisitedClosed heap visited ∧
    ∀ pair ∈ equations, VisitedRelated heap visited pair.1 pair.2

/-- One successful binding step preserves the graph certificate obligations
for both the visited application graph and the fixed original equations. -/
theorem afterBinding_graph_certificate {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (fuel : Nat)
    (ih : ∀ (c' : Configuration σ) (equations : List (Addr × Addr))
      (m : Memory σ), c'.phase = .compare →
      VisitedCovered c'.memory.heap c'.agenda c'.visited →
      EquationsCovered c'.memory.heap c'.agenda c'.visited equations →
      runSteps fuel (.running c') = .terminal (.success m) →
      GraphCertificate m.heap equations)
    (c : Configuration σ) (equations : List (Addr × Addr))
    (m : Memory σ) (rest : List (Addr × Addr))
    (hphase : c.phase = .compare)
    {lAddr rAddr : Addr}
    (coveredVisited :
      VisitedCovered c.memory.heap ((lAddr, rAddr) :: rest) c.visited)
    (coveredEquations :
      EquationsCovered c.memory.heap ((lAddr, rAddr) :: rest) c.visited
        equations)
    {varAddr target : Addr} {identity : σ.vars}
    (hBound : c.memory.heap[varAddr]? = some (Cell.var identity none))
    (hTargetCell : ∃ cell, c.memory.heap[target]? = some cell ∧
      ∀ targetIdentity targetAddress,
        cell ≠ Cell.var targetIdentity (some targetAddress))
    (hTargetNe : target ≠ varAddr)
    {boundSide targetSide : Addr}
    (hBoundSide :
      Heap.derefLoop c.memory.heap (c.memory.heap.size + 1) boundSide =
      .ok (.root varAddr))
    (hTargetSide :
      Heap.derefLoop c.memory.heap (c.memory.heap.size + 1) targetSide =
      .ok (.root target))
    (hHeadOrientation :
      (lAddr = boundSide ∧ rAddr = targetSide) ∨
      (lAddr = targetSide ∧ rAddr = boundSide))
    (hrun : runSteps fuel (afterBinding c rest varAddr identity target) =
      .terminal (.success m)) :
    GraphCertificate m.heap equations := by
  cases hw : c.memory.write varAddr (Cell.var identity (some target)) with
  | error e =>
      simp only [afterBinding, hw] at hrun
      exact absurd hrun (beginRollback_no_success fuel c _ m)
  | ok memory' =>
      simp only [afterBinding, hw] at hrun
      obtain ⟨hlt, hheq⟩ := write_ok_heap hw
      have hFrame : ∀ other, other ≠ varAddr →
          memory'.heap[other]? = c.memory.heap[other]? := by
        intro other ho
        rw [hheq]
        exact heap_set_get_ne _ _ hlt ho
      have hBound' :
          memory'.heap[varAddr]? =
            some (Cell.var identity (some target)) := by
        rw [hheq]
        exact heap_set_get_self _ _ hlt
      obtain ⟨targetCell, hTargetCell, hTargetNotLink⟩ := hTargetCell
      have hTargetCell' : memory'.heap[target]? = some targetCell :=
        (hFrame target hTargetNe).trans hTargetCell
      have hTargetLeaf : ∀ f,
          Heap.derefLoop memory'.heap (f + 1) target = .ok (.root target) :=
        derefLoop_leaf hTargetCell' hTargetNotLink
      have boundRelated : GoodPair memory'.heap boundSide targetSide :=
        GoodPair.of_bind hBound hFrame hBound' hTargetLeaf hTargetNe
          hBoundSide hTargetSide
      have headRelated : VisitedRelated memory'.heap c.visited lAddr rAddr := by
        rcases hHeadOrientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .inl boundRelated
        · exact .inl boundRelated.symm
      have persistedVisited :=
        coveredVisited.persist_binding hBound hFrame hBound' hTargetLeaf
      have nextVisited : VisitedCovered memory'.heap rest c.visited :=
        persistedVisited.consume headRelated
      have persistedEquations :=
        coveredEquations.persist_binding coveredVisited hBound hFrame hBound'
          hTargetLeaf
      have nextEquations :
          EquationsCovered memory'.heap rest c.visited equations :=
        persistedEquations.consume headRelated
      exact ih { c with memory := memory', agenda := rest } equations m
        hphase nextVisited nextEquations hrun

/-- The three-part conclusion of the run invariant, abbreviated. -/
def InvariantConclusion {σ : LPSignature} (c : Configuration σ)
    (m : Memory σ) : Prop :=
  FunctionFree m.heap ∧
  (∀ x y, GoodPair c.memory.heap x y → GoodPair m.heap x y) ∧
  (∀ pair ∈ c.agenda, GoodPair m.heap pair.1 pair.2)

/-- One successful binding step, discharged uniformly for all four machine
orientations: the run invariant holds across `afterBinding`, and the bound
agenda pair is itself discharged. -/
theorem afterBinding_invariant {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (fuel : Nat)
    (ih : ∀ (c' : Configuration σ) (m : Memory σ), c'.phase = .compare →
      FunctionFree c'.memory.heap →
      runSteps fuel (.running c') = .terminal (.success m) →
      InvariantConclusion c' m)
    (c : Configuration σ) (m : Memory σ) (rest : List (Addr × Addr))
    (hphase : c.phase = .compare)
    (hFF : FunctionFree c.memory.heap)
    {varAddr target : Addr} {identity : σ.vars}
    (hBound : c.memory.heap[varAddr]? = some (Cell.var identity none))
    (hTargetCell :
      (∃ tid, c.memory.heap[target]? = some (Cell.var tid none)) ∨
      (∃ ts, c.memory.heap[target]? = some (Cell.const ts)))
    (hTargetNe : target ≠ varAddr)
    {lAddr rAddr : Addr}
    (hL : Heap.derefLoop c.memory.heap (c.memory.heap.size + 1) lAddr =
      .ok (.root varAddr))
    (hR : Heap.derefLoop c.memory.heap (c.memory.heap.size + 1) rAddr =
      .ok (.root target))
    (hrun : runSteps fuel (afterBinding c rest varAddr identity target) =
      .terminal (.success m)) :
    FunctionFree m.heap ∧
    (∀ x y, GoodPair c.memory.heap x y → GoodPair m.heap x y) ∧
    (∀ pair ∈ rest, GoodPair m.heap pair.1 pair.2) ∧
    GoodPair m.heap lAddr rAddr := by
  cases hw : c.memory.write varAddr (Cell.var identity (some target)) with
  | error e =>
      simp only [afterBinding, hw] at hrun
      exact absurd hrun (beginRollback_no_success fuel c _ m)
  | ok memory' =>
      simp only [afterBinding, hw] at hrun
      obtain ⟨hlt, hheq⟩ := write_ok_heap hw
      have hFrame : ∀ other, other ≠ varAddr →
          memory'.heap[other]? = c.memory.heap[other]? := by
        intro other ho
        rw [hheq]
        exact heap_set_get_ne _ _ hlt ho
      have hBound' :
          memory'.heap[varAddr]? =
            some (Cell.var identity (some target)) := by
        rw [hheq]
        exact heap_set_get_self _ _ hlt
      have hTargetCell' :
          memory'.heap[target]? = c.memory.heap[target]? :=
        hFrame target hTargetNe
      have hTargetLeaf : ∀ f,
          Heap.derefLoop memory'.heap (f + 1) target = .ok (.root target) := by
        rcases hTargetCell with ⟨tid, hc⟩ | ⟨ts, hc⟩
        · exact derefLoop_leaf (hTargetCell'.trans hc) (by intro _ _ h; cases h)
        · exact derefLoop_leaf (hTargetCell'.trans hc) (by intro _ _ h; cases h)
      have hFF' : FunctionFree memory'.heap := by
        rw [hheq]
        exact FunctionFree.set_var hFF hlt
      obtain ⟨ihFF, ihPersist, ihPairs⟩ :=
        ih { c with memory := memory', agenda := rest } m hphase hFF' hrun
      have persistBind : ∀ x y, GoodPair c.memory.heap x y →
          GoodPair memory'.heap x y :=
        fun _ _ g => GoodPair.persist hBound hFrame hBound' hTargetLeaf g
      have established : GoodPair memory'.heap lAddr rAddr :=
        GoodPair.of_bind hBound hFrame hBound' hTargetLeaf hTargetNe hL hR
      exact ⟨ihFF, fun x y g => ihPersist x y (persistBind x y g),
        fun pair hp => ihPairs pair hp, ihPersist _ _ established⟩

/-- **The run invariant**: a successful run from a compare-phase
configuration on a function-free heap (i) keeps the final heap
function-free, (ii) carries every already-discharged `GoodPair` to the final
heap, and (iii) discharges every agenda pair as a `GoodPair` of the final
heap. -/
theorem runSteps_success_invariant {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] :
    ∀ (fuel : Nat) (c : Configuration σ) (m : Memory σ),
      c.phase = .compare →
      FunctionFree c.memory.heap →
      runSteps fuel (.running c) = .terminal (.success m) →
      InvariantConclusion c m := by
  intro fuel
  induction fuel with
  | zero =>
      intro c m _ _ hrun
      rw [runSteps_zero] at hrun
      simp at hrun
  | succ fuel ih =>
      intro c m hphase hFF hrun
      cases hstep : step (Machine.running c) with
      | none =>
          rw [runSteps_succ_none hstep] at hrun
          simp at hrun
      | some next =>
          rw [runSteps_succ_some hstep] at hrun
          cases hagenda : c.agenda with
          | nil =>
              simp only [step, hphase, hagenda] at hstep
              cases hstep
              rw [runSteps_terminal] at hrun
              have hm : c.memory = m := by
                injection hrun with h1
                injection h1
              subst hm
              refine ⟨hFF, fun _ _ g => g, ?_⟩
              intro pair hp
              rw [hagenda] at hp
              simp at hp
          | cons pair rest =>
              obtain ⟨l, r⟩ := pair
              simp only [step, hphase, hagenda] at hstep
              cases hdl : c.memory.heap.deref l with
              | error e =>
                  simp only [hdl] at hstep
                  cases hstep
                  exact absurd hrun (beginRollback_no_success fuel c _ m)
              | ok dresL =>
                  cases dresL with
                  | variableCycle a =>
                      simp only [hdl] at hstep
                      cases hstep
                      exact absurd hrun (beginRollback_no_success fuel c _ m)
                  | root leftRoot =>
                      simp only [hdl] at hstep
                      cases hdr : c.memory.heap.deref r with
                      | error e =>
                          simp only [hdr] at hstep
                          cases hstep
                          exact absurd hrun (beginRollback_no_success fuel c _ m)
                      | ok dresR =>
                          cases dresR with
                          | variableCycle a =>
                              simp only [hdr] at hstep
                              cases hstep
                              exact absurd hrun (beginRollback_no_success fuel c _ m)
                          | root rightRoot =>
                              simp only [hdr] at hstep
                              split at hstep
                              · rename_i heq
                                cases hstep
                                obtain ⟨ihFF, ihPersist, ihPairs⟩ :=
                                  ih { c with agenda := rest, phase := .compare }
                                    m rfl hFF hrun
                                refine ⟨ihFF, ihPersist, ?_⟩
                                intro pair hp
                                rw [hagenda] at hp
                                rcases List.mem_cons.mp hp with hhd | htl
                                · cases hhd
                                  exact ihPersist l r
                                    (GoodPair.of_same_root (deref_root hdl)
                                      (heq ▸ deref_root hdr))
                                · exact ihPairs pair htl
                              · rename_i hne
                                cases hcl : c.memory.heap[leftRoot]? with
                                | none =>
                                    simp only [hcl] at hstep
                                    cases hstep
                                    exact absurd hrun
                                      (beginRollback_no_success fuel c _ m)
                                | some cellL =>
                                    cases cellL with
                                    | app symbol args =>
                                        exact absurd hcl (hFF leftRoot symbol args)
                                    | var lid linkL =>
                                        cases linkL with
                                        | some t =>
                                            exact absurd hcl
                                              (deref_root_cell c.memory.heap _ l
                                                leftRoot (deref_root hdl) lid t)
                                        | none =>
                                            cases hcr : c.memory.heap[rightRoot]? with
                                            | none =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success fuel c _ m)
                                            | some cellR =>
                                                cases cellR with
                                                | app symbol args =>
                                                    exact absurd hcr
                                                      (hFF rightRoot symbol args)
                                                | var rid linkR =>
                                                    cases linkR with
                                                    | some t =>
                                                        exact absurd hcr
                                                          (deref_root_cell
                                                            c.memory.heap _ r
                                                            rightRoot
                                                            (deref_root hdr) rid t)
                                                    | none =>
                                                        simp only [hcl, hcr] at hstep
                                                        split at hstep
                                                        · cases hstep
                                                          obtain ⟨jFF, jPersist,
                                                              jRest, jPair⟩ :=
                                                            afterBinding_invariant
                                                              fuel ih c m rest
                                                              hphase hFF hcr
                                                              (Or.inl ⟨lid, hcl⟩)
                                                              hne
                                                              (deref_root hdr)
                                                              (deref_root hdl) hrun
                                                          refine ⟨jFF, jPersist, ?_⟩
                                                          intro pair hp
                                                          rw [hagenda] at hp
                                                          rcases List.mem_cons.mp hp
                                                            with hhd | htl
                                                          · cases hhd
                                                            exact jPair.symm
                                                          · exact jRest pair htl
                                                        · cases hstep
                                                          obtain ⟨jFF, jPersist,
                                                              jRest, jPair⟩ :=
                                                            afterBinding_invariant
                                                              fuel ih c m rest
                                                              hphase hFF hcl
                                                              (Or.inl ⟨rid, hcr⟩)
                                                              (fun e => hne e.symm)
                                                              (deref_root hdl)
                                                              (deref_root hdr) hrun
                                                          refine ⟨jFF, jPersist, ?_⟩
                                                          intro pair hp
                                                          rw [hagenda] at hp
                                                          rcases List.mem_cons.mp hp
                                                            with hhd | htl
                                                          · cases hhd
                                                            exact jPair
                                                          · exact jRest pair htl
                                                | const symbolR =>
                                                    simp only [hcl, hcr] at hstep
                                                    cases hstep
                                                    obtain ⟨jFF, jPersist,
                                                        jRest, jPair⟩ :=
                                                      afterBinding_invariant
                                                        fuel ih c m rest
                                                        hphase hFF hcl
                                                        (Or.inr ⟨symbolR, hcr⟩)
                                                        (fun e => hne e.symm)
                                                        (deref_root hdl)
                                                        (deref_root hdr) hrun
                                                    refine ⟨jFF, jPersist, ?_⟩
                                                    intro pair hp
                                                    rw [hagenda] at hp
                                                    rcases List.mem_cons.mp hp
                                                      with hhd | htl
                                                    · cases hhd
                                                      exact jPair
                                                    · exact jRest pair htl
                                    | const symbolL =>
                                        cases hcr : c.memory.heap[rightRoot]? with
                                        | none =>
                                            simp only [hcl, hcr] at hstep
                                            cases hstep
                                            exact absurd hrun
                                              (beginRollback_no_success fuel c _ m)
                                        | some cellR =>
                                            cases cellR with
                                            | app symbol args =>
                                                exact absurd hcr
                                                  (hFF rightRoot symbol args)
                                            | var rid linkR =>
                                                cases linkR with
                                                | some t =>
                                                    exact absurd hcr
                                                      (deref_root_cell c.memory.heap
                                                        _ r rightRoot
                                                        (deref_root hdr) rid t)
                                                | none =>
                                                    simp only [hcl, hcr] at hstep
                                                    cases hstep
                                                    obtain ⟨jFF, jPersist,
                                                        jRest, jPair⟩ :=
                                                      afterBinding_invariant
                                                        fuel ih c m rest
                                                        hphase hFF hcr
                                                        (Or.inr ⟨symbolL, hcl⟩)
                                                        hne
                                                        (deref_root hdr)
                                                        (deref_root hdl) hrun
                                                    refine ⟨jFF, jPersist, ?_⟩
                                                    intro pair hp
                                                    rw [hagenda] at hp
                                                    rcases List.mem_cons.mp hp
                                                      with hhd | htl
                                                    · cases hhd
                                                      exact jPair.symm
                                                    · exact jRest pair htl
                                            | const symbolR =>
                                                simp only [hcl, hcr] at hstep
                                                split at hstep
                                                · rename_i hsym
                                                  cases hstep
                                                  obtain ⟨ihFF, ihPersist, ihPairs⟩ :=
                                                    ih { c with agenda := rest, phase := .compare } m rfl hFF hrun
                                                  refine ⟨ihFF, ihPersist, ?_⟩
                                                  intro pair hp
                                                  rw [hagenda] at hp
                                                  rcases List.mem_cons.mp hp
                                                    with hhd | htl
                                                  · cases hhd
                                                    exact ihPersist l r
                                                      (GoodPair.of_const
                                                        (deref_root hdl)
                                                        (deref_root hdr) hcl
                                                        (hsym ▸ hcr))
                                                  · exact ihPairs pair htl
                                                · cases hstep
                                                  exact absurd hrun
                                                    (beginRollback_no_success
                                                      fuel c _ m)

/-! ## Compound graph certificate -/

/-- A successful run closes the graph certificate for every equation present
at entry.  This follows the executable agenda and visited set exactly; it does
not define a second unification relation. -/
theorem runSteps_success_graph_certificate {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] :
    ∀ (fuel : Nat) (c : Configuration σ)
      (equations : List (Addr × Addr)) (m : Memory σ),
      c.phase = .compare →
      VisitedCovered c.memory.heap c.agenda c.visited →
      EquationsCovered c.memory.heap c.agenda c.visited equations →
      runSteps fuel (.running c) = .terminal (.success m) →
      GraphCertificate m.heap equations := by
  intro fuel
  induction fuel with
  | zero =>
      intro c equations m _ _ _ hrun
      rw [runSteps_zero] at hrun
      simp at hrun
  | succ fuel ih =>
      intro c equations m hphase coveredVisited coveredEquations hrun
      cases hstep : step (Machine.running c) with
      | none =>
          rw [runSteps_succ_none hstep] at hrun
          simp at hrun
      | some next =>
          rw [runSteps_succ_some hstep] at hrun
          cases hagenda : c.agenda with
          | nil =>
              simp only [step, hphase, hagenda] at hstep
              cases hstep
              rw [runSteps_terminal] at hrun
              have closedVisited :
                  VisitedCovered c.memory.heap [] c.visited := by
                simpa [hagenda] using coveredVisited
              have closedEquations :
                  EquationsCovered c.memory.heap [] c.visited equations := by
                simpa [hagenda] using coveredEquations
              have hm : c.memory = m := by
                injection hrun with h1
                injection h1
              subst hm
              exact ⟨c.visited, closedVisited.toClosed,
                closedEquations.toRelated⟩
          | cons pair rest =>
              obtain ⟨l, r⟩ := pair
              have liveVisited :
                  VisitedCovered c.memory.heap ((l, r) :: rest) c.visited := by
                simpa [hagenda] using coveredVisited
              have liveEquations :
                  EquationsCovered c.memory.heap ((l, r) :: rest) c.visited
                    equations := by
                simpa [hagenda] using coveredEquations
              simp only [step, hphase, hagenda] at hstep
              cases hdl : c.memory.heap.deref l with
              | error e =>
                  simp only [hdl] at hstep
                  cases hstep
                  exact absurd hrun (beginRollback_no_success fuel c _ m)
              | ok dresL =>
                  cases dresL with
                  | variableCycle a =>
                      simp only [hdl] at hstep
                      cases hstep
                      exact absurd hrun (beginRollback_no_success fuel c _ m)
                  | root leftRoot =>
                      simp only [hdl] at hstep
                      cases hdr : c.memory.heap.deref r with
                      | error e =>
                          simp only [hdr] at hstep
                          cases hstep
                          exact absurd hrun
                            (beginRollback_no_success fuel c _ m)
                      | ok dresR =>
                          cases dresR with
                          | variableCycle a =>
                              simp only [hdr] at hstep
                              cases hstep
                              exact absurd hrun
                                (beginRollback_no_success fuel c _ m)
                          | root rightRoot =>
                              simp only [hdr] at hstep
                              split at hstep
                              · rename_i heq
                                cases hstep
                                have headRelated :
                                    VisitedRelated c.memory.heap c.visited l r :=
                                  .inl (GoodPair.of_same_root (deref_root hdl)
                                    (heq ▸ deref_root hdr))
                                exact ih
                                  { c with agenda := rest, phase := .compare }
                                  equations m rfl
                                  (liveVisited.consume headRelated)
                                  (liveEquations.consume headRelated) hrun
                              · rename_i hne
                                cases hcl : c.memory.heap[leftRoot]? with
                                | none =>
                                    simp only [hcl] at hstep
                                    cases hstep
                                    exact absurd hrun
                                      (beginRollback_no_success fuel c _ m)
                                | some cellL =>
                                    cases cellL with
                                    | var lid linkL =>
                                        cases linkL with
                                        | some t =>
                                            exact absurd hcl
                                              (deref_root_cell c.memory.heap _ l
                                                leftRoot (deref_root hdl) lid t)
                                        | none =>
                                            cases hcr : c.memory.heap[rightRoot]?
                                            with
                                            | none =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                            | some cellR =>
                                                cases cellR with
                                                | var rid linkR =>
                                                    cases linkR with
                                                    | some t =>
                                                        exact absurd hcr
                                                          (deref_root_cell
                                                            c.memory.heap _ r
                                                            rightRoot
                                                            (deref_root hdr) rid t)
                                                    | none =>
                                                        simp only [hcl, hcr] at hstep
                                                        split at hstep
                                                        · cases hstep
                                                          exact
                                                            afterBinding_graph_certificate
                                                              fuel ih c equations m
                                                              rest hphase
                                                              liveVisited
                                                              liveEquations hcr
                                                              ⟨_, hcl, by
                                                                intro _ _ h
                                                                cases h⟩ hne
                                                              (deref_root hdr)
                                                              (deref_root hdl)
                                                              (.inr ⟨rfl, rfl⟩)
                                                              hrun
                                                        · cases hstep
                                                          exact
                                                            afterBinding_graph_certificate
                                                              fuel ih c equations m
                                                              rest hphase
                                                              liveVisited
                                                              liveEquations hcl
                                                              ⟨_, hcr, by
                                                                intro _ _ h
                                                                cases h⟩
                                                              (fun e => hne e.symm)
                                                              (deref_root hdl)
                                                              (deref_root hdr)
                                                              (.inl ⟨rfl, rfl⟩)
                                                              hrun
                                                | const symbolR =>
                                                    simp only [hcl, hcr] at hstep
                                                    cases hstep
                                                    exact
                                                      afterBinding_graph_certificate
                                                        fuel ih c equations m rest
                                                        hphase liveVisited
                                                        liveEquations hcl
                                                        ⟨_, hcr, by
                                                          intro _ _ h
                                                          cases h⟩
                                                        (fun e => hne e.symm)
                                                        (deref_root hdl)
                                                        (deref_root hdr)
                                                        (.inl ⟨rfl, rfl⟩) hrun
                                                | app symbolR argsR =>
                                                    simp only [hcl, hcr] at hstep
                                                    cases hstep
                                                    exact
                                                      afterBinding_graph_certificate
                                                        fuel ih c equations m rest
                                                        hphase liveVisited
                                                        liveEquations hcl
                                                        ⟨_, hcr, by
                                                          intro _ _ h
                                                          cases h⟩
                                                        (fun e => hne e.symm)
                                                        (deref_root hdl)
                                                        (deref_root hdr)
                                                        (.inl ⟨rfl, rfl⟩) hrun
                                    | const symbolL =>
                                        cases hcr : c.memory.heap[rightRoot]? with
                                        | none =>
                                            simp only [hcl, hcr] at hstep
                                            cases hstep
                                            exact absurd hrun
                                              (beginRollback_no_success fuel c _ m)
                                        | some cellR =>
                                            cases cellR with
                                            | var rid linkR =>
                                                cases linkR with
                                                | some t =>
                                                    exact absurd hcr
                                                      (deref_root_cell c.memory.heap
                                                        _ r rightRoot
                                                        (deref_root hdr) rid t)
                                                | none =>
                                                    simp only [hcl, hcr] at hstep
                                                    cases hstep
                                                    exact
                                                      afterBinding_graph_certificate
                                                        fuel ih c equations m rest
                                                        hphase liveVisited
                                                        liveEquations hcr
                                                        ⟨_, hcl, by
                                                          intro _ _ h
                                                          cases h⟩ hne
                                                        (deref_root hdr)
                                                        (deref_root hdl)
                                                        (.inr ⟨rfl, rfl⟩) hrun
                                            | const symbolR =>
                                                simp only [hcl, hcr] at hstep
                                                split at hstep
                                                · rename_i hsym
                                                  cases hstep
                                                  have headRelated :
                                                      VisitedRelated c.memory.heap
                                                        c.visited l r :=
                                                    .inl (GoodPair.of_const
                                                      (deref_root hdl)
                                                      (deref_root hdr) hcl
                                                      (hsym ▸ hcr))
                                                  exact ih
                                                    { c with agenda := rest, phase := .compare }
                                                    equations m rfl
                                                    (liveVisited.consume
                                                      headRelated)
                                                    (liveEquations.consume
                                                      headRelated) hrun
                                                · cases hstep
                                                  exact absurd hrun
                                                    (beginRollback_no_success
                                                      fuel c _ m)
                                            | app symbolR argsR =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                    | app symbolL argsL =>
                                        cases hcr : c.memory.heap[rightRoot]? with
                                        | none =>
                                            simp only [hcl, hcr] at hstep
                                            cases hstep
                                            exact absurd hrun
                                              (beginRollback_no_success fuel c _ m)
                                        | some cellR =>
                                            cases cellR with
                                            | var rid linkR =>
                                                cases linkR with
                                                | some t =>
                                                    exact absurd hcr
                                                      (deref_root_cell c.memory.heap
                                                        _ r rightRoot
                                                        (deref_root hdr) rid t)
                                                | none =>
                                                    simp only [hcl, hcr] at hstep
                                                    cases hstep
                                                    exact
                                                      afterBinding_graph_certificate
                                                        fuel ih c equations m rest
                                                        hphase liveVisited
                                                        liveEquations hcr
                                                        ⟨_, hcl, by
                                                          intro _ _ h
                                                          cases h⟩ hne
                                                        (deref_root hdr)
                                                        (deref_root hdl)
                                                        (.inr ⟨rfl, rfl⟩) hrun
                                            | const symbolR =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                            | app symbolR argsR =>
                                                simp only [hcl, hcr] at hstep
                                                split at hstep
                                                · rename_i hmatching
                                                  split at hstep
                                                  · rename_i hseen
                                                    cases hstep
                                                    have hMem :
                                                        orderedPair leftRoot
                                                          rightRoot ∈ c.visited := by
                                                      simpa [seen] using hseen
                                                    have headRelated :
                                                        VisitedRelated
                                                          c.memory.heap c.visited
                                                          l r :=
                                                      .inr ⟨_, _, leftRoot,
                                                        rightRoot,
                                                        deref_root hdl,
                                                        deref_root hdr, hMem⟩
                                                    exact ih
                                                      { c with agenda := rest, phase := .compare }
                                                      equations m rfl
                                                      (liveVisited.consume
                                                        headRelated)
                                                      (liveEquations.consume
                                                        headRelated) hrun
                                                  · rename_i hnotSeen
                                                    cases hstep
                                                    have nextVisited :=
                                                      liveVisited.expand
                                                        (deref_root hdl)
                                                        (deref_root hdr) hcl
                                                        (hmatching.1 ▸ hcr)
                                                        hmatching.2
                                                    have nextEquations :=
                                                      liveEquations.expand
                                                        (leftArgs := argsL)
                                                        (rightArgs := argsR)
                                                        (deref_root hdl)
                                                        (deref_root hdr)
                                                    let c' : Configuration σ :=
                                                      { c with
                                                        agenda := argsL.toList.zip argsR.toList ++ rest
                                                        visited := orderedPair leftRoot rightRoot :: c.visited
                                                        phase := .compare }
                                                    exact ih c' equations m rfl nextVisited
                                                      nextEquations hrun
                                                · cases hstep
                                                  exact absurd hrun
                                                    (beginRollback_no_success
                                                      fuel c _ m)

/-- Entry-point form of the graph certificate: the original `startMany`
agenda is exactly the fixed equation set certified at success. -/
theorem startMany_success_graph_certificate {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (fuel : Nat) (memory₀ : Memory σ) (agenda : List (Addr × Addr))
    (m : Memory σ)
    (hrun : runSteps fuel (startMany memory₀ agenda) =
      .terminal (.success m)) :
    GraphCertificate m.heap agenda := by
  apply runSteps_success_graph_certificate fuel
    { memory := memory₀, agenda := agenda, visited := []
      entryMark := memory₀.trailMark, phase := .compare }
    agenda m rfl
  · intro pair hPair
    simp at hPair
  · intro pair hPair
    exact .inr (.inl hPair)
  · exact hrun

/-! ## Success soundness -/

/-- **Success soundness of the runtime graph unifier (function-free
fragment)**: if `startMany` reaches `.success`, every entry agenda pair
reads back equally in the final memory — whenever both sides read back
finitely at all, they read back to the *same* canonical `Term`.  Rational
(cyclic) results are excluded honestly by the `.ok` hypotheses rather than
silently. -/
theorem startMany_success_readTerm_eq {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (fuel : Nat) (memory₀ : Memory σ) (agenda : List (Addr × Addr))
    (m : Memory σ)
    (hFF : FunctionFree memory₀.heap)
    (hrun : runSteps fuel (startMany memory₀ agenda) =
      .terminal (.success m)) :
    ∀ pair ∈ agenda, ∀ leftTerm rightTerm : Term σ,
      Heap.readTerm m.heap pair.1 = .ok leftTerm →
      Heap.readTerm m.heap pair.2 = .ok rightTerm →
      leftTerm = rightTerm := by
  obtain ⟨mFF, _, pairs⟩ :=
    runSteps_success_invariant fuel
      { memory := memory₀, agenda := agenda, visited := []
        entryMark := memory₀.trailMark, phase := .compare }
      m rfl hFF hrun
  intro pair hp leftTerm rightTerm hLeft hRight
  rcases pairs pair hp with conv | ⟨f, ρl, ρr, symbol, hL, hR, hCl, hCr⟩
  · exact ConvergedAt.readTerm_eq mFF conv hLeft hRight
  · have hTl : leftTerm = .const symbol := by
      have hBig : readTermFuel m.heap (f + (m.heap.size + 1)) pair.1 =
          .ok leftTerm :=
        readTermFuel_mono_le m.heap (by omega) pair.1 leftTerm hLeft
      have hRoot := readTermFuel_of_root mFF f pair.1 ρl hL (m.heap.size + 1)
      have hConst : readTermFuel m.heap (1 + (m.heap.size + 1)) ρl =
          .ok (.const symbol) := by
        have shift : 1 + (m.heap.size + 1) = (m.heap.size + 1) + 1 := by omega
        rw [shift]
        exact readTermFuel_const m.heap _ ρl symbol hCl
      have : (Except.ok leftTerm : Except ReadbackError (Term σ)) =
          .ok (.const symbol) := by
        rw [← hBig, hRoot, hConst]
      simpa using this
    have hTr : rightTerm = .const symbol := by
      have hBig : readTermFuel m.heap (f + (m.heap.size + 1)) pair.2 =
          .ok rightTerm :=
        readTermFuel_mono_le m.heap (by omega) pair.2 rightTerm hRight
      have hRoot := readTermFuel_of_root mFF f pair.2 ρr hR (m.heap.size + 1)
      have hConst : readTermFuel m.heap (1 + (m.heap.size + 1)) ρr =
          .ok (.const symbol) := by
        have shift : 1 + (m.heap.size + 1) = (m.heap.size + 1) + 1 := by omega
        rw [shift]
        exact readTermFuel_const m.heap _ ρr symbol hCr
      have : (Except.ok rightTerm : Except ReadbackError (Term σ)) =
          .ok (.const symbol) := by
        rw [← hBig, hRoot, hConst]
      simpa using this
    rw [hTl, hTr]

/-! ## Stage 5b: machine-side discharge

The unifier's success segments realize both relations S4 and S1 consume:
every write is a fresh binding over an unbound cell (`BindingExtension`)
and a genuine trailed `Memory.write` (`Extends`). -/

theorem BindingExtension.rfl {σ : LPSignature} (heap : Heap σ) :
    BindingExtension heap heap :=
  ⟨Nat.le_refl _, fun _ _ h => .inl h⟩

theorem BindingExtension.trans {σ : LPSignature}
    {heap₀ heap₁ heap₂ : Heap σ} (a : BindingExtension heap₀ heap₁)
    (b : BindingExtension heap₁ heap₂) : BindingExtension heap₀ heap₂ := by
  refine ⟨a.1.trans b.1, ?_⟩
  intro addr cell h
  rcases a.2 addr cell h with h₁ | ⟨id, target, rfl, h₁⟩
  · exact b.2 addr cell h₁
  · rcases b.2 addr _ h₁ with h₂ | ⟨id₂, target₂, habs, _⟩
    · exact .inr ⟨id, target, _root_.rfl, h₂⟩
    · cases habs

/-- One machine binding is a binding extension. -/
theorem bindingExtension_of_write {σ : LPSignature}
    {memory memory' : Memory σ} {address target : Addr} {identity : σ.vars}
    (hcell : memory.heap[address]? = some (Cell.var identity none))
    (hw : memory.write address (Cell.var identity (some target)) =
      .ok memory') :
    BindingExtension memory.heap memory'.heap := by
  obtain ⟨hlt, hheq⟩ := write_ok_heap hw
  refine ⟨by rw [hheq]; simp, ?_⟩
  intro addr cell h
  by_cases haddr : addr = address
  · subst haddr
    rw [h] at hcell
    cases hcell
    exact .inr ⟨identity, target, _root_.rfl, by
      rw [hheq]
      exact heap_set_get_self _ _ hlt⟩
  · exact .inl (by rw [hheq, heap_set_get_ne _ _ hlt haddr]; exact h)

/-- Abbreviation for the extension induction hypothesis. -/
def ExtensionIH (σ : LPSignature) [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (fuel : Nat) : Prop :=
  ∀ (c : Configuration σ) (m : Memory σ), c.phase = .compare →
    runSteps fuel (.running c) = .terminal (.success m) →
    BindingExtension c.memory.heap m.heap ∧ Extends c.memory m ∧
      c.memory.heap.size = m.heap.size

/-- One binding step followed by a successful run composes both relations. -/
theorem bindStep_extension {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] {fuel : Nat}
    (ih : ExtensionIH σ fuel) (c : Configuration σ) (m : Memory σ)
    (rest : List (Addr × Addr)) {bound target : Addr} {identity : σ.vars}
    (hphase : c.phase = .compare)
    (hcellBound : c.memory.heap[bound]? = some (Cell.var identity none))
    (hrun : runSteps fuel (afterBinding c rest bound identity target) =
      .terminal (.success m)) :
    BindingExtension c.memory.heap m.heap ∧ Extends c.memory m ∧
      c.memory.heap.size = m.heap.size := by
  simp only [afterBinding] at hrun
  cases hw : c.memory.write bound (Cell.var identity (some target)) with
  | error e =>
      rw [hw] at hrun
      exact absurd hrun (beginRollback_no_success fuel c _ m)
  | ok memory' =>
      rw [hw] at hrun
      obtain ⟨ihBE, ihEx, ihSize⟩ :=
        ih { c with memory := memory', agenda := rest } m hphase hrun
      obtain ⟨hlt, hheq⟩ := write_ok_heap hw
      refine ⟨(bindingExtension_of_write hcellBound hw).trans ihBE,
        (Extends.write (.refl c.memory) hw).trans ihEx, ?_⟩
      have hsz : memory'.heap.size = c.memory.heap.size := by
        rw [hheq]; simp
      exact hsz.symm.trans ihSize

/-- A successful unifier run is a binding extension and a real write
history of the entry memory. -/
theorem runSteps_success_extension {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] :
    ∀ (fuel : Nat) (c : Configuration σ) (m : Memory σ),
      c.phase = .compare →
      runSteps fuel (.running c) = .terminal (.success m) →
      BindingExtension c.memory.heap m.heap ∧ Extends c.memory m ∧
        c.memory.heap.size = m.heap.size := by
  intro fuel
  induction fuel with
  | zero =>
      intro c m _ hrun
      rw [runSteps_zero] at hrun
      simp at hrun
  | succ fuel ih =>
      intro c m hphase hrun
      cases hstep : step (Machine.running c) with
      | none =>
          rw [runSteps_succ_none hstep] at hrun
          simp at hrun
      | some next =>
          rw [runSteps_succ_some hstep] at hrun
          cases hagenda : c.agenda with
          | nil =>
              simp only [step, hphase, hagenda] at hstep
              cases hstep
              rw [runSteps_terminal] at hrun
              have hm : c.memory = m := by
                injection hrun with h1
                injection h1
              subst hm
              exact ⟨BindingExtension.rfl _, .refl _, _root_.rfl⟩
          | cons pair rest =>
              obtain ⟨l, r⟩ := pair
              simp only [step, hphase, hagenda] at hstep
              cases hdl : c.memory.heap.deref l with
              | error e =>
                  simp only [hdl] at hstep
                  cases hstep
                  exact absurd hrun (beginRollback_no_success fuel c _ m)
              | ok dresL =>
                  cases dresL with
                  | variableCycle a =>
                      simp only [hdl] at hstep
                      cases hstep
                      exact absurd hrun (beginRollback_no_success fuel c _ m)
                  | root leftRoot =>
                      simp only [hdl] at hstep
                      cases hdr : c.memory.heap.deref r with
                      | error e =>
                          simp only [hdr] at hstep
                          cases hstep
                          exact absurd hrun (beginRollback_no_success fuel c _ m)
                      | ok dresR =>
                          cases dresR with
                          | variableCycle a =>
                              simp only [hdr] at hstep
                              cases hstep
                              exact absurd hrun
                                (beginRollback_no_success fuel c _ m)
                          | root rightRoot =>
                              simp only [hdr] at hstep
                              split at hstep
                              · cases hstep
                                exact ih { c with agenda := rest, phase := .compare } m rfl hrun
                              · -- distinct roots: analyze both cells
                                cases hcl : c.memory.heap[leftRoot]? with
                                | none =>
                                    simp only [hcl] at hstep
                                    cases hstep
                                    exact absurd hrun
                                      (beginRollback_no_success fuel c _ m)
                                | some cellL =>
                                    cases hcr : c.memory.heap[rightRoot]? with
                                    | none =>
                                        cases cellL with
                                        | var lid linkL =>
                                            cases linkL with
                                            | none =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                            | some t =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                        | const s =>
                                            simp only [hcl, hcr] at hstep
                                            cases hstep
                                            exact absurd hrun
                                              (beginRollback_no_success
                                                fuel c _ m)
                                        | app s a =>
                                            simp only [hcl, hcr] at hstep
                                            cases hstep
                                            exact absurd hrun
                                              (beginRollback_no_success
                                                fuel c _ m)
                                    | some cellR =>
                                        cases cellL with
                                        | var lid linkL =>
                                            cases linkL with
                                            | some t =>
                                                cases cellR with
                                                | var rid linkR =>
                                                    cases linkR with
                                                    | none =>
                                                        simp only [hcl, hcr]
                                                          at hstep
                                                        cases hstep
                                                        exact
                                                          bindStep_extension
                                                            ih c m rest hphase
                                                            hcr hrun
                                                    | some t₂ =>
                                                        simp only [hcl, hcr]
                                                          at hstep
                                                        cases hstep
                                                        exact absurd hrun
                                                          (beginRollback_no_success
                                                            fuel c _ m)
                                                | const symbolR =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact absurd hrun
                                                      (beginRollback_no_success
                                                        fuel c _ m)
                                                | app symbolR argsR =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact absurd hrun
                                                      (beginRollback_no_success
                                                        fuel c _ m)
                                            | none =>
                                                cases cellR with
                                                | var rid linkR =>
                                                    cases linkR with
                                                    | none =>
                                                        simp only [hcl, hcr]
                                                          at hstep
                                                        split at hstep <;>
                                                          cases hstep
                                                        · exact
                                                            bindStep_extension
                                                              ih c m rest hphase
                                                              hcr hrun
                                                        · exact
                                                            bindStep_extension
                                                              ih c m rest hphase
                                                              hcl hrun
                                                    | some t =>
                                                        simp only [hcl, hcr]
                                                          at hstep
                                                        cases hstep
                                                        exact
                                                          bindStep_extension
                                                            ih c m rest hphase
                                                            hcl hrun
                                                | const symbolR =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_extension
                                                      ih c m rest hphase hcl hrun
                                                | app symbolR argsR =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_extension
                                                      ih c m rest hphase hcl hrun
                                        | const symbolL =>
                                            cases cellR with
                                            | var rid linkR =>
                                                cases linkR with
                                                | none =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_extension
                                                      ih c m rest hphase hcr hrun
                                                | some t =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact absurd hrun
                                                      (beginRollback_no_success
                                                        fuel c _ m)
                                            | const symbolR =>
                                                simp only [hcl, hcr] at hstep
                                                split at hstep <;> cases hstep
                                                · exact ih { c with agenda := rest, phase := .compare } m rfl hrun
                                                · exact absurd hrun
                                                    (beginRollback_no_success
                                                      fuel c _ m)
                                            | app symbolR argsR =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                        | app symbolL argsL =>
                                            cases cellR with
                                            | var rid linkR =>
                                                cases linkR with
                                                | none =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_extension
                                                      ih c m rest hphase hcr hrun
                                                | some t =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact absurd hrun
                                                      (beginRollback_no_success
                                                        fuel c _ m)
                                            | const symbolR =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                            | app symbolR argsR =>
                                                simp only [hcl, hcr] at hstep
                                                split at hstep
                                                · split at hstep <;> cases hstep
                                                  · exact ih { c with agenda := rest, phase := .compare } m rfl hrun
                                                  · exact ih { c with agenda := argsL.toList.zip argsR.toList ++ rest, visited := orderedPair leftRoot rightRoot :: c.visited, phase := .compare } m rfl hrun
                                                · cases hstep
                                                  exact absurd hrun
                                                    (beginRollback_no_success
                                                      fuel c _ m)

/-- Entry-point form: a successful `startMany` unification run extends its
entry memory by fresh bindings only, as a real write history. -/
theorem startMany_success_extension {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (fuel : Nat) (memory₀ : Memory σ) (agenda : List (Addr × Addr))
    (m : Memory σ)
    (hrun : runSteps fuel (startMany memory₀ agenda) =
      .terminal (.success m)) :
    BindingExtension memory₀.heap m.heap ∧ Extends memory₀ m ∧
      memory₀.heap.size = m.heap.size :=
  runSteps_success_extension fuel
    { memory := memory₀, agenda := agenda, visited := []
      entryMark := memory₀.trailMark, phase := .compare } m rfl hrun

/-- In-bounds addresses always hold a cell. -/
theorem getElem?_some_of_lt {σ : LPSignature} {heap : Heap σ} {a : Addr}
    (h : a < heap.size) : ∃ cell, heap[a]? = some cell := by
  rcases hcell : heap[a]? with _ | cell
  · rw [Array.getElem?_eq_none_iff] at hcell
    exact absurd hcell (Nat.not_le.mpr h)
  · exact ⟨cell, _root_.rfl⟩

/-- A later-heap variable cell came from an earlier variable cell with the
same identity, along a binding extension within bounds. -/
theorem BindingExtension.var_back {σ : LPSignature}
    {heap₀ heap₁ : Heap σ} (ext : BindingExtension heap₀ heap₁)
    {a : Addr} {identity : σ.vars} {link : Option Addr}
    (hlt : a < heap₀.size)
    (h : heap₁[a]? = some (Cell.var identity link)) :
    ∃ link₀, heap₀[a]? = some (Cell.var identity link₀) := by
  obtain ⟨cell, hc⟩ := getElem?_some_of_lt hlt
  rcases ext.2 a cell hc with hsame | ⟨id₂, target, rfl, hbound⟩
  · rw [hsame] at h
    cases h
    exact ⟨_, hc⟩
  · rw [hbound] at h
    cases h
    exact ⟨none, hc⟩

/-- Identity injectivity transfers across a size-preserving binding
extension: identities of existing cells never change, and no cells are
added. -/
theorem IdentityInjective.of_bindingExtension {σ : LPSignature}
    {heap₀ heap₁ : Heap σ} (ext : BindingExtension heap₀ heap₁)
    (hsize : heap₀.size = heap₁.size)
    (inj : IdentityInjective heap₀) : IdentityInjective heap₁ := by
  intro a b identity la lb ha hb
  have haLt : a < heap₀.size := hsize.symm ▸ lt_of_getElem?_some ha
  have hbLt : b < heap₀.size := hsize.symm ▸ lt_of_getElem?_some hb
  obtain ⟨la₀, ha₀⟩ := ext.var_back haLt ha
  obtain ⟨lb₀, hb₀⟩ := ext.var_back hbLt hb
  exact inj a b identity la₀ lb₀ ha₀ hb₀

/-! ## Stage 5b: the machine preserves descending links

The graph unifier binds the higher-addressed unbound variable toward the
lower one, and otherwise binds variables to constant cells.  On
function-free heaps this keeps every variable chain strictly descending or
terminating at a constant — the well-foundedness that makes finite readback
total.  This section proves that shape is a run invariant of successful
unifier runs. -/



/-- A machine binding whose target is lower or a constant preserves
descending links. -/
theorem descendingOrConst_write {σ : LPSignature}
    {memory memory' : Memory σ} {bound target : Addr} {identity : σ.vars}
    (hcell : memory.heap[bound]? = some (Cell.var identity none))
    (hw : memory.write bound (Cell.var identity (some target)) =
      .ok memory')
    (hTarget : target < bound ∨
      ∃ symbol, memory.heap[target]? = some (Cell.const symbol))
    (hDesc : DescendingOrConst memory.heap) :
    DescendingOrConst memory'.heap := by
  obtain ⟨hlt, hheq⟩ := write_ok_heap hw
  intro a id t hcellA
  rw [hheq] at hcellA
  by_cases haddr : a = bound
  · rw [haddr, heap_set_get_self _ _ hlt] at hcellA
    injection hcellA with hcellA'
    injection hcellA' with hid hlink
    injection hlink with htg
    rcases hTarget with hord | ⟨symbol, hconst⟩
    · rw [haddr, ← htg]
      exact .inl hord
    · refine .inr ⟨symbol, ?_⟩
      rw [hheq, ← htg]
      have hne : target ≠ bound := by
        intro hEq
        rw [hEq, hcell] at hconst
        cases hconst
      rw [heap_set_get_ne _ _ hlt hne]
      exact hconst
  · rw [heap_set_get_ne _ _ hlt haddr] at hcellA
    rcases hDesc a id t hcellA with hord | ⟨symbol, hconst⟩
    · exact .inl hord
    · refine .inr ⟨symbol, ?_⟩
      rw [hheq]
      have hne : t ≠ bound := by
        intro hEq
        rw [hEq, hcell] at hconst
        cases hconst
      rw [heap_set_get_ne _ _ hlt hne]
      exact hconst

/-- Machine bindings never create compound cells. -/
theorem functionFree_write {σ : LPSignature}
    {memory memory' : Memory σ} {bound target : Addr} {identity : σ.vars}
    (hw : memory.write bound (Cell.var identity (some target)) =
      .ok memory')
    (hFF : FunctionFree memory.heap) : FunctionFree memory'.heap := by
  obtain ⟨hlt, hheq⟩ := write_ok_heap hw
  intro a symbol args hcellA
  rw [hheq] at hcellA
  by_cases haddr : a = bound
  · subst haddr
    rw [heap_set_get_self _ _ hlt] at hcellA
    cases hcellA
  · rw [heap_set_get_ne _ _ hlt haddr] at hcellA
    exact hFF a symbol args hcellA

/-- Abbreviation for the wellfoundedness induction hypothesis. -/
def OrderedFFIH (σ : LPSignature) [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (fuel : Nat) : Prop :=
  ∀ (c : Configuration σ) (m : Memory σ), c.phase = .compare →
    runSteps fuel (.running c) = .terminal (.success m) →
    OrderedFF c.memory.heap → OrderedFF m.heap

/-- One ordered binding step followed by a successful run. -/
theorem bindStep_orderedFF {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] {fuel : Nat}
    (ih : OrderedFFIH σ fuel) (c : Configuration σ) (m : Memory σ)
    (rest : List (Addr × Addr)) {bound target : Addr} {identity : σ.vars}
    (hphase : c.phase = .compare)
    (hcellBound : c.memory.heap[bound]? = some (Cell.var identity none))
    (hTarget : target < bound ∨
      ∃ symbol, c.memory.heap[target]? = some (Cell.const symbol))
    (hrun : runSteps fuel (afterBinding c rest bound identity target) =
      .terminal (.success m))
    (hwf : OrderedFF c.memory.heap) : OrderedFF m.heap := by
  simp only [afterBinding] at hrun
  cases hw : c.memory.write bound (Cell.var identity (some target)) with
  | error e =>
      rw [hw] at hrun
      exact absurd hrun (beginRollback_no_success fuel c _ m)
  | ok memory' =>
      rw [hw] at hrun
      exact ih { c with memory := memory', agenda := rest } m hphase hrun
        ⟨descendingOrConst_write hcellBound hw hTarget hwf.1,
          functionFree_write hw hwf.2⟩

/-- **Successful unifier runs preserve descending links and
function-freeness.**  Together with size preservation this is exactly what
finite-readback totality needs at the answer memory. -/
theorem runSteps_success_orderedFF {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] :
    ∀ (fuel : Nat) (c : Configuration σ) (m : Memory σ),
      c.phase = .compare →
      runSteps fuel (.running c) = .terminal (.success m) →
      OrderedFF c.memory.heap → OrderedFF m.heap := by
  intro fuel
  induction fuel with
  | zero =>
      intro c m _ hrun _
      rw [runSteps_zero] at hrun
      simp at hrun
  | succ fuel ih =>
      intro c m hphase hrun hwf
      cases hstep : step (Machine.running c) with
      | none =>
          rw [runSteps_succ_none hstep] at hrun
          simp at hrun
      | some next =>
          rw [runSteps_succ_some hstep] at hrun
          cases hagenda : c.agenda with
          | nil =>
              simp only [step, hphase, hagenda] at hstep
              cases hstep
              rw [runSteps_terminal] at hrun
              have hm : c.memory = m := by
                injection hrun with h1
                injection h1
              subst hm
              exact hwf
          | cons pair rest =>
              obtain ⟨l, r⟩ := pair
              simp only [step, hphase, hagenda] at hstep
              cases hdl : c.memory.heap.deref l with
              | error e =>
                  simp only [hdl] at hstep
                  cases hstep
                  exact absurd hrun (beginRollback_no_success fuel c _ m)
              | ok dresL =>
                  cases dresL with
                  | variableCycle a =>
                      simp only [hdl] at hstep
                      cases hstep
                      exact absurd hrun (beginRollback_no_success fuel c _ m)
                  | root leftRoot =>
                      simp only [hdl] at hstep
                      cases hdr : c.memory.heap.deref r with
                      | error e =>
                          simp only [hdr] at hstep
                          cases hstep
                          exact absurd hrun
                            (beginRollback_no_success fuel c _ m)
                      | ok dresR =>
                          cases dresR with
                          | variableCycle a =>
                              simp only [hdr] at hstep
                              cases hstep
                              exact absurd hrun
                                (beginRollback_no_success fuel c _ m)
                          | root rightRoot =>
                              simp only [hdr] at hstep
                              by_cases hroots : leftRoot = rightRoot
                              · rw [if_pos hroots] at hstep
                                cases hstep
                                exact ih { c with agenda := rest, phase := .compare } m rfl hrun hwf
                              · rw [if_neg hroots] at hstep
                                cases hcl : c.memory.heap[leftRoot]? with
                                | none =>
                                    simp only [hcl] at hstep
                                    cases hstep
                                    exact absurd hrun
                                      (beginRollback_no_success fuel c _ m)
                                | some cellL =>
                                    cases hcr :
                                        c.memory.heap[rightRoot]? with
                                    | none =>
                                        cases cellL with
                                        | var lid linkL =>
                                            cases linkL with
                                            | none =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                            | some t =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                        | const s =>
                                            simp only [hcl, hcr] at hstep
                                            cases hstep
                                            exact absurd hrun
                                              (beginRollback_no_success
                                                fuel c _ m)
                                        | app s a =>
                                            simp only [hcl, hcr] at hstep
                                            cases hstep
                                            exact absurd hrun
                                              (beginRollback_no_success
                                                fuel c _ m)
                                    | some cellR =>
                                        cases cellL with
                                        | var lid linkL =>
                                            cases linkL with
                                            | some t =>
                                                exact absurd hcl
                                                  (deref_root_cell
                                                    c.memory.heap _ l leftRoot
                                                    (deref_root hdl) lid t)
                                            | none =>
                                                cases cellR with
                                                | var rid linkR =>
                                                    cases linkR with
                                                    | none =>
                                                        simp only [hcl, hcr]
                                                          at hstep
                                                        by_cases hord :
                                                            leftRoot < rightRoot
                                                        · rw [if_pos hord]
                                                            at hstep
                                                          cases hstep
                                                          exact
                                                            bindStep_orderedFF
                                                              ih c m rest hphase
                                                              hcr (.inl hord)
                                                              hrun hwf
                                                        · rw [if_neg hord]
                                                            at hstep
                                                          cases hstep
                                                          exact
                                                            bindStep_orderedFF
                                                              ih c m rest hphase
                                                              hcl
                                                              (.inl
                                                                (Nat.lt_of_le_of_ne
                                                                  (Nat.not_lt.mp
                                                                    hord)
                                                                  (fun hEq =>
                                                                    hroots
                                                                      hEq.symm)))
                                                              hrun hwf
                                                    | some t =>
                                                        exact absurd hcr
                                                          (deref_root_cell
                                                            c.memory.heap _ r
                                                            rightRoot
                                                            (deref_root hdr)
                                                            rid t)
                                                | const symbolR =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_orderedFF
                                                      ih c m rest hphase hcl
                                                      (.inr ⟨symbolR, hcr⟩)
                                                      hrun hwf
                                                | app symbolR argsR =>
                                                    exact absurd hcr
                                                      (hwf.2 rightRoot
                                                        symbolR argsR)
                                        | const symbolL =>
                                            cases cellR with
                                            | var rid linkR =>
                                                cases linkR with
                                                | none =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_orderedFF
                                                      ih c m rest hphase hcr
                                                      (.inr ⟨symbolL, hcl⟩)
                                                      hrun hwf
                                                | some t =>
                                                    exact absurd hcr
                                                      (deref_root_cell
                                                        c.memory.heap _ r
                                                        rightRoot
                                                        (deref_root hdr)
                                                        rid t)
                                            | const symbolR =>
                                                simp only [hcl, hcr] at hstep
                                                by_cases hsym :
                                                    symbolL = symbolR
                                                · rw [if_pos hsym] at hstep
                                                  cases hstep
                                                  exact ih { c with agenda := rest, phase := .compare } m rfl hrun hwf
                                                · rw [if_neg hsym] at hstep
                                                  cases hstep
                                                  exact absurd hrun
                                                    (beginRollback_no_success
                                                      fuel c _ m)
                                            | app symbolR argsR =>
                                                exact absurd hcr
                                                  (hwf.2 rightRoot
                                                    symbolR argsR)
                                        | app symbolL argsL =>
                                            exact absurd hcl
                                              (hwf.2 leftRoot symbolL argsL)

/-- Entry-point form: successful `startMany` runs preserve the
readback-wellfoundedness bundle. -/
theorem startMany_success_orderedFF {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (fuel : Nat) (memory₀ : Memory σ) (agenda : List (Addr × Addr))
    (m : Memory σ)
    (hrun : runSteps fuel (startMany memory₀ agenda) =
      .terminal (.success m))
    (hwf : OrderedFF memory₀.heap) : OrderedFF m.heap :=
  runSteps_success_orderedFF fuel
    { memory := memory₀, agenda := agenda, visited := []
      entryMark := memory₀.trailMark, phase := .compare } m rfl hrun hwf

/-! ## Stage 5b: readback totality on ordered function-free heaps

Descending links terminate: every chain strictly decreases its address or
reaches a constant cell.  So finite readback needs no more fuel than the
address itself allows, and `notFinite` is impossible — the discharge, not
an assumption, of every finite-readback side condition in the endpoint. -/

/-- On a descending, function-free heap every in-bounds address reads back
with fuel `address + 2`. -/
theorem readTermFuel_total_of_orderedFF {σ : LPSignature} {heap : Heap σ}
    (hwf : OrderedFF heap) :
    ∀ (address : Addr), address < heap.size →
      ∃ term, readTermFuel heap (address + 2) address = .ok term := by
  intro address
  induction address using Nat.strong_induction_on with
  | _ address ih =>
      intro ha
      obtain ⟨cell, hcell⟩ := getElem?_some_of_lt ha
      cases cell with
      | var identity link =>
          cases link with
          | none =>
              exact ⟨.var identity,
                readTermFuel_unbound heap _ address identity hcell⟩
          | some target =>
              rw [readTermFuel_link heap (address + 1) address target
                identity hcell]
              rcases hwf.1 address identity target hcell with
                hord | ⟨symbol, hconst⟩
              · obtain ⟨term, hterm⟩ :=
                  ih target hord (Nat.lt_trans hord ha)
                exact ⟨term, readTermFuel_mono_le heap
                  (Nat.succ_le_succ (Nat.succ_le_of_lt hord))
                  target term hterm⟩
              · exact ⟨.const symbol,
                  readTermFuel_const heap address target symbol hconst⟩
      | const symbol =>
          exact ⟨.const symbol,
            readTermFuel_const heap _ address symbol hcell⟩
      | app symbol args =>
          exact absurd hcell (hwf.2 address symbol args)

/-- Every in-bounds address of an ordered function-free heap has a finite
readback at the standard budget. -/
theorem readTerm_total_of_orderedFF {σ : LPSignature} {heap : Heap σ}
    (hwf : OrderedFF heap) {address : Addr} (ha : address < heap.size) :
    ∃ term, Heap.readTerm heap address = .ok term := by
  obtain ⟨term, hterm⟩ := readTermFuel_total_of_orderedFF hwf address ha
  exact ⟨term, readTermFuel_mono_le heap
    (Nat.succ_le_succ (Nat.succ_le_of_lt ha)) address term hterm⟩


/-! ### Failure exactness

The unifier never allocates; every compare-phase step is a trailed write.
Rollback undoes exactly those writes, so a failing run hands back the entry
memory verbatim — the law the query's backtrack chain stands on. -/

section FailureExact

/-- Rollback from a `WritesN` suffix terminates in the checkpointed memory
whenever it produces `.failure` at all. -/
theorem rollback_failure_exact {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] :
    ∀ (fuel : Nat) (c : Configuration σ) (reason : RollbackReason)
      (m m₀ : Memory σ) (k : Nat),
      c.phase = .rollback reason →
      Memory.WritesN k m₀ c.memory → c.entryMark = m₀.trailMark →
      runSteps fuel (.running c) = .terminal (.failure m) →
      m = m₀ := by
  intro fuel
  induction fuel with
  | zero =>
      intro c reason m m₀ k _ _ _ hrun
      rw [runSteps_zero] at hrun
      simp at hrun
  | succ fuel ih =>
      intro c reason m m₀ k hphase hW hmark hrun
      cases hstep : step (Machine.running c) with
      | none =>
          rw [runSteps_succ_none hstep] at hrun
          simp at hrun
      | some next =>
          rw [runSteps_succ_some hstep] at hrun
          simp only [step, hphase] at hstep
          have htrail : c.memory.trailMark = m₀.trailMark + k :=
            hW.trailMark_exact
          cases k with
          | zero =>
              cases hW
              have hcond : c.memory.trail.size = c.entryMark := hmark.symm
              rw [if_pos hcond] at hstep
              cases hstep
              cases reason with
              | unificationFailure =>
                  simp only [rollbackTerminal] at hrun
                  rw [runSteps_terminal] at hrun
                  injection hrun with h1
                  injection h1 with h2
                  exact h2.symm
              | runtimeError e =>
                  simp only [rollbackTerminal] at hrun
                  rw [runSteps_terminal] at hrun
                  simp at hrun
          | succ k' =>
              have hne : ¬ (c.memory.trail.size = c.entryMark) := by
                show ¬ (c.memory.trailMark = c.entryMark)
                rw [htrail, hmark]
                omega
              rw [if_neg hne] at hstep
              have hlt : c.entryMark < c.memory.trail.size := by
                show c.entryMark < c.memory.trailMark
                rw [htrail, hmark]
                omega
              rw [if_pos hlt] at hstep
              cases hW with
              | tail history hw =>
                  rw [Memory.undoLast_write hw] at hstep
                  cases hstep
                  rename_i middle _ _
                  exact ih { c with memory := middle, phase := .rollback reason } reason m m₀ k' rfl history hmark hrun

/-- Entering rollback with a `WritesN` suffix: any eventual `.failure`
memory is the checkpointed one. -/
theorem beginRollback_failure_exact {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    {fuel : Nat} {c : Configuration σ} {reason : RollbackReason}
    {m m₀ : Memory σ} {k : Nat}
    (hW : Memory.WritesN k m₀ c.memory) (hmark : c.entryMark = m₀.trailMark)
    (hrun : runSteps fuel (beginRollback c reason) =
      .terminal (.failure m)) :
    m = m₀ :=
  rollback_failure_exact fuel
    { c with agenda := [], phase := .rollback reason } reason m m₀ k rfl
    hW hmark hrun

/-- One binding step within a failing run keeps the write suffix. -/
theorem bindStep_failure {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] {fuel : Nat}
    (ih : ∀ (c : Configuration σ) (m m₀ : Memory σ) (k : Nat),
      c.phase = .compare → Memory.WritesN k m₀ c.memory →
      c.entryMark = m₀.trailMark →
      runSteps fuel (.running c) = .terminal (.failure m) → m = m₀)
    (c : Configuration σ) (m m₀ : Memory σ) (k : Nat)
    (rest : List (Addr × Addr)) {bound target : Addr} {identity : σ.vars}
    (hphase : c.phase = .compare)
    (hW : Memory.WritesN k m₀ c.memory) (hmark : c.entryMark = m₀.trailMark)
    (hrun : runSteps fuel (afterBinding c rest bound identity target) =
      .terminal (.failure m)) :
    m = m₀ := by
  simp only [afterBinding] at hrun
  cases hw : c.memory.write bound (Cell.var identity (some target)) with
  | error e =>
      rw [hw] at hrun
      exact beginRollback_failure_exact hW hmark hrun
  | ok memory' =>
      rw [hw] at hrun
      exact ih { c with memory := memory', agenda := rest } m m₀ (k + 1)
        hphase (hW.tail hw) hmark hrun

/-- **A failing unifier run restores its entry memory exactly.** -/
theorem runSteps_failure_exact {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] :
    ∀ (fuel : Nat) (c : Configuration σ) (m m₀ : Memory σ) (k : Nat),
      c.phase = .compare → Memory.WritesN k m₀ c.memory →
      c.entryMark = m₀.trailMark →
      runSteps fuel (.running c) = .terminal (.failure m) →
      m = m₀ := by
  intro fuel
  induction fuel with
  | zero =>
      intro c m m₀ k _ _ _ hrun
      rw [runSteps_zero] at hrun
      simp at hrun
  | succ fuel ih =>
      intro c m m₀ k hphase hW hmark hrun
      cases hstep : step (Machine.running c) with
      | none =>
          rw [runSteps_succ_none hstep] at hrun
          simp at hrun
      | some next =>
          rw [runSteps_succ_some hstep] at hrun
          cases hagenda : c.agenda with
          | nil =>
              simp only [step, hphase, hagenda] at hstep
              cases hstep
              rw [runSteps_terminal] at hrun
              cases hrun
          | cons pair rest =>
              obtain ⟨l, r⟩ := pair
              simp only [step, hphase, hagenda] at hstep
              cases hdl : c.memory.heap.deref l with
              | error e =>
                  simp only [hdl] at hstep
                  cases hstep
                  exact beginRollback_failure_exact hW hmark hrun
              | ok dresL =>
                  cases dresL with
                  | variableCycle a =>
                      simp only [hdl] at hstep
                      cases hstep
                      exact beginRollback_failure_exact hW hmark hrun
                  | root leftRoot =>
                      simp only [hdl] at hstep
                      cases hdr : c.memory.heap.deref r with
                      | error e =>
                          simp only [hdr] at hstep
                          cases hstep
                          exact beginRollback_failure_exact hW hmark hrun
                      | ok dresR =>
                          cases dresR with
                          | variableCycle a =>
                              simp only [hdr] at hstep
                              cases hstep
                              exact beginRollback_failure_exact hW hmark hrun
                          | root rightRoot =>
                              simp only [hdr] at hstep
                              by_cases hroots : leftRoot = rightRoot
                              · rw [if_pos hroots] at hstep
                                cases hstep
                                exact ih { c with agenda := rest, phase := .compare } m m₀ k rfl hW hmark hrun
                              · rw [if_neg hroots] at hstep
                                cases hcl : c.memory.heap[leftRoot]? with
                                | none =>
                                    simp only [hcl] at hstep
                                    cases hstep
                                    exact beginRollback_failure_exact hW
                                      hmark hrun
                                | some cellL =>
                                    cases hcr :
                                        c.memory.heap[rightRoot]? with
                                    | none =>
                                        cases cellL with
                                        | var lid linkL =>
                                            cases linkL with
                                            | none =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact
                                                  beginRollback_failure_exact
                                                    hW hmark hrun
                                            | some t =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact
                                                  beginRollback_failure_exact
                                                    hW hmark hrun
                                        | const s =>
                                            simp only [hcl, hcr] at hstep
                                            cases hstep
                                            exact
                                              beginRollback_failure_exact
                                                hW hmark hrun
                                        | app s a =>
                                            simp only [hcl, hcr] at hstep
                                            cases hstep
                                            exact
                                              beginRollback_failure_exact
                                                hW hmark hrun
                                    | some cellR =>
                                        cases cellL with
                                        | var lid linkL =>
                                            cases linkL with
                                            | some t =>
                                                cases cellR with
                                                | var rid linkR =>
                                                    cases linkR with
                                                    | none =>
                                                        simp only [hcl, hcr]
                                                          at hstep
                                                        cases hstep
                                                        exact bindStep_failure
                                                          ih c m m₀ k rest
                                                          hphase hW hmark hrun
                                                    | some t₂ =>
                                                        simp only [hcl, hcr]
                                                          at hstep
                                                        cases hstep
                                                        exact
                                                          beginRollback_failure_exact
                                                            hW hmark hrun
                                                | const symbolR =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact
                                                      beginRollback_failure_exact
                                                        hW hmark hrun
                                                | app symbolR argsR =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact
                                                      beginRollback_failure_exact
                                                        hW hmark hrun
                                            | none =>
                                                cases cellR with
                                                | var rid linkR =>
                                                    cases linkR with
                                                    | none =>
                                                        simp only [hcl, hcr]
                                                          at hstep
                                                        by_cases hord :
                                                            leftRoot < rightRoot
                                                        · rw [if_pos hord]
                                                            at hstep
                                                          cases hstep
                                                          exact
                                                            bindStep_failure
                                                              ih c m m₀ k rest
                                                              hphase hW hmark
                                                              hrun
                                                        · rw [if_neg hord]
                                                            at hstep
                                                          cases hstep
                                                          exact
                                                            bindStep_failure
                                                              ih c m m₀ k rest
                                                              hphase hW hmark
                                                              hrun
                                                    | some t =>
                                                        simp only [hcl, hcr]
                                                          at hstep
                                                        cases hstep
                                                        exact
                                                          bindStep_failure
                                                            ih c m m₀ k rest
                                                            hphase hW hmark
                                                            hrun
                                                | const symbolR =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_failure
                                                      ih c m m₀ k rest
                                                      hphase hW hmark hrun
                                                | app symbolR argsR =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_failure
                                                      ih c m m₀ k rest
                                                      hphase hW hmark hrun
                                        | const symbolL =>
                                            cases cellR with
                                            | var rid linkR =>
                                                cases linkR with
                                                | none =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_failure
                                                      ih c m m₀ k rest
                                                      hphase hW hmark hrun
                                                | some t =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact
                                                      beginRollback_failure_exact
                                                        hW hmark hrun
                                            | const symbolR =>
                                                simp only [hcl, hcr] at hstep
                                                by_cases hsym :
                                                    symbolL = symbolR
                                                · rw [if_pos hsym] at hstep
                                                  cases hstep
                                                  exact ih { c with agenda := rest, phase := .compare } m m₀ k rfl hW hmark hrun
                                                · rw [if_neg hsym] at hstep
                                                  cases hstep
                                                  exact
                                                    beginRollback_failure_exact
                                                      hW hmark hrun
                                            | app symbolR argsR =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact
                                                  beginRollback_failure_exact
                                                    hW hmark hrun
                                        | app symbolL argsL =>
                                            cases cellR with
                                            | var rid linkR =>
                                                cases linkR with
                                                | none =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_failure
                                                      ih c m m₀ k rest
                                                      hphase hW hmark hrun
                                                | some t =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact
                                                      beginRollback_failure_exact
                                                        hW hmark hrun
                                            | const symbolR =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact
                                                  beginRollback_failure_exact
                                                    hW hmark hrun
                                            | app symbolR argsR =>
                                                simp only [hcl, hcr] at hstep
                                                by_cases hshape :
                                                    symbolL = symbolR ∧
                                                      argsL.size = argsR.size
                                                · rw [if_pos hshape] at hstep
                                                  by_cases hseen :
                                                      seen c.visited leftRoot
                                                        rightRoot = true
                                                  · rw [if_pos hseen] at hstep
                                                    cases hstep
                                                    exact ih { c with agenda := rest, phase := .compare } m m₀ k rfl hW hmark hrun
                                                  · rw [if_neg hseen] at hstep
                                                    cases hstep
                                                    exact ih { c with agenda := argsL.toList.zip argsR.toList ++ rest, visited := orderedPair leftRoot rightRoot :: c.visited, phase := .compare } m m₀ k rfl hW hmark hrun
                                                · rw [if_neg hshape] at hstep
                                                  cases hstep
                                                  exact
                                                    beginRollback_failure_exact
                                                      hW hmark hrun

/-- Entry-point form: a failing `startMany` run returns the entry memory. -/
theorem startMany_failure_exact {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (fuel : Nat) (memory₀ : Memory σ) (agenda : List (Addr × Addr))
    (m : Memory σ)
    (hrun : runSteps fuel (startMany memory₀ agenda) =
      .terminal (.failure m)) :
    m = memory₀ :=
  runSteps_failure_exact fuel
    { memory := memory₀, agenda := agenda, visited := []
      entryMark := memory₀.trailMark, phase := .compare } m memory₀ 0 rfl
    (.refl memory₀) rfl hrun

end FailureExact

/-! ### Boundary lemmas: back into dispatch -/

end RuntimeUnificationSoundness
end Mettapedia.Logic.LP
