import Mettapedia.Languages.HOLLight.CachedHypothesisDischarge

/-!
# Discharging a list of retained theorem-cache roots

Each listed source root contributes two existing primitive inferences.
The earlier cache is preserved, the conclusion is unchanged, and dependencies
are exactly the union of the supplied proofs and input theorem. Publication
still requires that every hypothesis has actually been removed.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.CachedHypothesisList
open Mettapedia.Languages.OpenTheory Mettapedia.Logic.DerivationGraph
open GraphExpansion HypothesisExpansion

def result : List Theorem → Theorem → Theorem
  | [], input => input
  | source :: rest, input => result rest (proveHypResult source input)

def dependencies : List Theorem → Finset Sequent
  | [] => ∅
  | source :: rest => source.axioms ∪ dependencies rest

theorem result_conclusion (sources : List Theorem) (input : Theorem) :
    (result sources input).sequent.concl = input.sequent.concl := by
  induction sources generalizing input with
  | nil => rfl
  | cons source rest ih => exact ih (proveHypResult source input)

theorem result_axioms (sources : List Theorem) (input : Theorem) :
    (result sources input).axioms = dependencies sources ∪ input.axioms := by
  induction sources generalizing input with
  | nil => simp [result, dependencies]
  | cons source rest ih =>
    simp [result, dependencies, ih, proveHypResult, Theorem.unionResult,
      Finset.union_assoc, Finset.union_left_comm]

theorem result_hypotheses (sources : List Theorem) (input : Theorem)
    (closed : ∀ source ∈ sources, source.sequent.hyp = ∅) :
    (result sources input).sequent.hyp = input.sequent.hyp \ (sources.map (·.sequent.concl)).toFinset := by
  induction sources generalizing input with
  | nil => simp [result]
  | cons source rest ih =>
    rw [result, ih (proveHypResult source input) (fun item member => closed item (List.mem_cons_of_mem _ member))]
    simp only [proveHypResult, Theorem.unionResult, closed source List.mem_cons_self, Finset.empty_union,
      List.map_cons, List.toFinset_cons]
    ext term
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
    tauto

theorem result_closed (sources : List Theorem) (input : Theorem)
    (closed : ∀ source ∈ sources, source.sequent.hyp = ∅)
    (covered : input.sequent.hyp ⊆ (sources.map (·.sequent.concl)).toFinset) :
    (result sources input).sequent.hyp = ∅ := by
  rw [result_hypotheses sources input closed]
  exact Finset.sdiff_eq_empty_iff_subset.mpr covered

def closeOne? (policy : AxiomPolicy) [DecidablePred policy] (state : ProofExecution.State)
    (sourceRoot inputRoot : Nat) (origin : ProofExecution.Origin) : Option (ProofExecution.State × Nat) := do
  let source ← state.cache[sourceRoot]?
  let input ← state.cache[inputRoot]?
  if same : Ty.same source.sequent.concl.ty input.sequent.concl.ty = true then
    emitBlock policy [sourceRoot, inputRoot]
      (proveHypBlock source input ((Ty.same_eq_true_iff _ _).mp same) origin) state
  else none

theorem closeOne_checked {policy : AxiomPolicy} [DecidablePred policy]
    {premises : List Theorem} {state : ProofExecution.State} {source input : Theorem}
    {sourceRoot inputRoot : Nat} (earlier : BuildChecked policy premises state)
    (sourceFound : state.cache[sourceRoot]? = some source) (inputFound : state.cache[inputRoot]? = some input)
    (sameType : source.sequent.concl.ty = input.sequent.concl.ty) (origin : ProofExecution.Origin) :
    ∃ after root, closeOne? policy state sourceRoot inputRoot origin = some (after, root) ∧
      BuildChecked policy premises after ∧ after.cache[root]? = some (proveHypResult source input) ∧
      after.receipts.size = state.receipts.size + 2 ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → after.cache[index]? = some fact := by
  have selected : lookupPremises state.cache [sourceRoot, inputRoot] = some [source, input] := by
    simp [lookupPremises, sourceFound, inputFound]
  obtain ⟨after, root, emitted, checked, found, _, preserved⟩ := emitBlock_checked earlier selected
    (proveHypBlock_checked policy source input sameType origin)
  refine ⟨after, root, ?_, checked, found, ?_, preserved⟩
  · simpa [closeOne?, sourceFound, inputFound, (Ty.same_eq_true_iff _ _).mpr sameType] using emitted
  · simpa only [proveHypBlock, List.length_cons, List.length_nil] using (emitBlock_size emitted).2

def close? (policy : AxiomPolicy) [DecidablePred policy] :
    ProofExecution.State → List Nat → Nat → ProofExecution.Origin → Option (ProofExecution.State × Nat)
  | state, [], inputRoot, _ => some (state, inputRoot)
  | state, sourceRoot :: rest, inputRoot, origin => do
    let (after, next) ← closeOne? policy state sourceRoot inputRoot origin
    close? policy after rest next origin

theorem close_checked {policy : AxiomPolicy} [DecidablePred policy]
    {premises : List Theorem} (sources : List (Nat × Theorem))
    {state : ProofExecution.State} {input : Theorem} {inputRoot : Nat}
    (earlier : BuildChecked policy premises state) (inputFound : state.cache[inputRoot]? = some input)
    (found : ∀ source ∈ sources, state.cache[source.1]? = some source.2)
    (typed : ∀ source ∈ sources, source.2.sequent.concl.ty = input.sequent.concl.ty)
    (origin : ProofExecution.Origin) :
    ∃ after root, close? policy state (sources.map Prod.fst) inputRoot origin = some (after, root) ∧
      BuildChecked policy premises after ∧ after.cache[root]? = some (result (sources.map Prod.snd) input) ∧
      after.receipts.size = state.receipts.size + 2 * sources.length ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → after.cache[index]? = some fact := by
  induction sources generalizing state input inputRoot with
  | nil => exact ⟨state, inputRoot, rfl, earlier, inputFound, by simp, fun _ _ present => present⟩
  | cons source rest ih =>
    obtain ⟨middle, next, first, middleChecked, nextFound, firstSize, firstPreserved⟩ :=
      closeOne_checked earlier (found source List.mem_cons_self) inputFound (typed source List.mem_cons_self) origin
    obtain ⟨after, root, tail, afterChecked, rootFound, tailSize, tailPreserved⟩ :=
      ih middleChecked nextFound
        (fun item member => firstPreserved _ _ (found item (List.mem_cons_of_mem _ member)))
        (fun item member => typed item (List.mem_cons_of_mem _ member))
    refine ⟨after, root, ?_, afterChecked, rootFound, ?_, ?_⟩
    · simp only [List.map_cons, close?, first]
      exact tail
    · simp only [List.length_cons] at *
      omega
    · intro index fact present
      exact tailPreserved index fact (firstPreserved index fact present)

def closeAndRequire? (policy : AxiomPolicy) [DecidablePred policy] (state : ProofExecution.State)
    (sources : List Nat) (inputRoot : Nat) (origin : ProofExecution.Origin) : Option (ProofExecution.State × Nat) := do
  let (after, root) ← close? policy state sources inputRoot origin
  CachedHypothesisDischarge.requireClosed? after root

theorem closeAndRequire_checked {policy : AxiomPolicy} [DecidablePred policy]
    {premises : List Theorem} (sources : List (Nat × Theorem))
    {state : ProofExecution.State} {input : Theorem} {inputRoot : Nat}
    (earlier : BuildChecked policy premises state) (inputFound : state.cache[inputRoot]? = some input)
    (found : ∀ source ∈ sources, state.cache[source.1]? = some source.2)
    (typed : ∀ source ∈ sources, source.2.sequent.concl.ty = input.sequent.concl.ty)
    (closed : ∀ source ∈ sources, source.2.sequent.hyp = ∅)
    (covered : input.sequent.hyp ⊆ (sources.map (fun source => source.2.sequent.concl)).toFinset)
    (origin : ProofExecution.Origin) :
    ∃ after root,
      closeAndRequire? policy state (sources.map Prod.fst) inputRoot origin = some (after, root) ∧
      BuildChecked policy premises after ∧
      after.cache[root]? = some (result (sources.map Prod.snd) input) ∧
      (result (sources.map Prod.snd) input).sequent.hyp = ∅ ∧
      after.receipts.size = state.receipts.size + 2 * sources.length := by
  obtain ⟨after, root, computed, checked, rootFound, size, _⟩ :=
    close_checked sources earlier inputFound found typed origin
  have noHypotheses : (result (sources.map Prod.snd) input).sequent.hyp = ∅ := by
    apply result_closed
    · intro source member
      obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
      exact closed entry present
    · simpa only [List.map_map, Function.comp_def] using covered
  refine ⟨after, root, ?_, checked, rootFound, noHypotheses, size⟩
  simp only [closeAndRequire?, computed]
  exact (CachedHypothesisDischarge.requireClosed_iff after root).mpr ⟨_, rootFound, noHypotheses⟩

theorem close_missing_first (policy : AxiomPolicy) [DecidablePred policy] (state : ProofExecution.State)
    (sourceRoot inputRoot : Nat) (rest : List Nat) (origin : ProofExecution.Origin)
    (missing : state.cache[sourceRoot]? = none) :
    close? policy state (sourceRoot :: rest) inputRoot origin = none := by
  simp [close?, closeOne?, missing]

#print axioms result_axioms
#print axioms result_closed
#print axioms close_checked
#print axioms closeAndRequire_checked
end Mettapedia.Languages.HOLLight.CachedHypothesisList
