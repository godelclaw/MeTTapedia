import Mettapedia.Languages.HOLLight.ProofSystem
import Mathlib.Data.Nat.Size

/-!
# Chronological HOL Light graph expansion

A source output can be realized by a local graph of actual HOL Light rule
requests. The expansion resolves its ordered earlier-output references,
relocates only physical addresses, and appends its rule occurrences. Local
blocks are checked by the existing HOL rule-witness replay operation.

The correctness theorem establishes exact root theorems, shared references,
ordered witnesses and origins. Physical-node and payload-size bounds are
separate from an operational running-time bound for a complete translator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.GraphExpansion

open Mettapedia.Logic Mettapedia.Logic.DerivationGraph
open Mettapedia.Languages.OpenTheory
open ProofExecution (Receipt Origin)

/-- A local graph is checked with its ordered premise vector as the initial
cache. This reuses the actual HOL rule-witness replay judgment. -/
def BlockChecked (policy : AxiomPolicy) [DecidablePred policy]
    (premises : List Theorem) (conclusion : Theorem) (block : ProofSystem.Certificate) : Prop :=
  ∃ cache, replayFrom (ruleWitness policy) premises.toArray block.1 = some cache ∧
    cache[block.2]? = some conclusion

/-- Premise addresses select already stored proofs; new local addresses start
at the physical end of the receiving cache. -/
def address (premiseRoots : List Nat) (base index : Nat) : Nat :=
  if available : index < premiseRoots.length then premiseRoots[index]
  else base + (index - premiseRoots.length)

/-- A block keeps its rule requests and origins; only parent and root addresses
are relocated. -/
def expandBlock (premiseRoots : List Nat) (base : Nat) (block : ProofSystem.Certificate) :
    ProofSystem.Certificate :=
  (block.1.map (Node.relocate (address premiseRoots base)), address premiseRoots base block.2)

/-- Selecting the premise vector establishes exact physical lookup agreement,
including all future local addresses, which are absent in both caches. -/
theorem address_agreement {cache : Array Theorem} {roots : List Nat} {premises : List Theorem}
    (found : lookupPremises cache roots = some premises) :
    LookupAgreement premises.toArray cache (address roots cache.size) := by
  intro index
  have sameLength := lookupPremises_length cache found
  by_cases inside : index < roots.length
  · simpa [address, inside] using lookupPremises_at found index inside
  · have outside : premises.length ≤ index := by omega
    simp [address, inside, outside]

/-- New local nodes occupy the receiving cache's next physical positions. -/
theorem address_future {cache : Array Theorem} {roots : List Nat} {premises : List Theorem}
    (found : lookupPremises cache roots = some premises) (offset : Nat) :
    address roots cache.size (premises.toArray.size + offset) = cache.size + offset := by
  have sameLength := lookupPremises_length cache found
  simp only [List.size_toArray]
  rw [sameLength]
  simp [address]

/-- Expanding a checked block yields a real checked HOL proof graph and exactly
its selected theorem, with prior proofs remaining shared cache entries. -/
theorem expandBlock_checked {policy : AxiomPolicy} [DecidablePred policy]
    {cache : Array Theorem} {roots : List Nat} {premises : List Theorem}
    {conclusion : Theorem} {block : ProofSystem.Certificate}
    (found : lookupPremises cache roots = some premises)
    (checked : BlockChecked policy premises conclusion block) :
    ∃ result, replayFrom (ruleWitness policy) cache (expandBlock roots cache.size block).1 = some result ∧
      result[(expandBlock roots cache.size block).2]? = some conclusion := by
  obtain ⟨localResult, accepted, rootFound⟩ := checked
  obtain ⟨result, replayed, agreement⟩ := replayFrom_relocate (ruleWitness policy)
    (address_agreement found) (address_future found) accepted
  exact ⟨result, replayed, (agreement block.2).trans rootFound⟩

/-- Refusal of malformed or future-referencing local blocks is retained in
both directions by physical expansion. -/
theorem expandBlock_refused_iff {policy : AxiomPolicy} [DecidablePred policy]
    {cache : Array Theorem} {roots : List Nat} {premises : List Theorem}
    (found : lookupPremises cache roots = some premises) (block : ProofSystem.Certificate) :
    replayFrom (ruleWitness policy) cache (expandBlock roots cache.size block).1 = none ↔
      replayFrom (ruleWitness policy) premises.toArray block.1 = none :=
  replayFrom_relocate_none_iff (ruleWitness policy) (address_agreement found) (address_future found) block.1

/-- Expansion preserves and reflects the exact root theorem, not just whether
some node in the graph succeeded. -/
theorem expandBlock_checked_iff {policy : AxiomPolicy} [DecidablePred policy]
    {cache : Array Theorem} {roots : List Nat} {premises : List Theorem}
    (found : lookupPremises cache roots = some premises)
    (conclusion : Theorem) (block : ProofSystem.Certificate) :
    BlockChecked policy premises conclusion block ↔
      ∃ result, replayFrom (ruleWitness policy) cache (expandBlock roots cache.size block).1 = some result ∧
        result[(expandBlock roots cache.size block).2]? = some conclusion := by
  constructor
  · exact expandBlock_checked found
  · rintro ⟨result, accepted, rootFound⟩
    cases localReplay : replayFrom (ruleWitness policy) premises.toArray block.1 with
    | none =>
        have refused := (expandBlock_refused_iff found block).mpr localReplay
        rw [accepted] at refused
        contradiction
    | some localResult =>
        obtain ⟨actualResult, replayed, agreement⟩ := replayFrom_relocate (ruleWitness policy)
          (address_agreement found) (address_future found) localReplay
        have same := Option.some.inj (accepted.symm.trans replayed)
        subst actualResult
        exact ⟨localResult, localReplay, (agreement block.2).symm.trans rootFound⟩

/-- The emitted block retains every authored rule occurrence. -/
theorem expandBlock_length (roots : List Nat) (base : Nat) (block : ProofSystem.Certificate) :
    (expandBlock roots base block).1.length = block.1.length := by simp [expandBlock]

/-- Both witness requests and origin tags remain in physical order. -/
theorem expandBlock_witnesses (roots : List Nat) (base : Nat) (block : ProofSystem.Certificate) :
    (expandBlock roots base block).1.map (fun node => (node.witness, node.origin)) =
      block.1.map (fun node => (node.witness, node.origin)) := by
  simp [expandBlock, Node.relocate, List.map_map, Function.comp_def]

/-- Appending a block to a checked graph makes its exact result acceptable to
HOL Light's existing public certificate checker. -/
theorem appendBlock_accepted {policy : AxiomPolicy} [DecidablePred policy]
    {earlierNodes : List Receipt} {cache : Array Theorem} {roots : List Nat} {premises : List Theorem}
    {conclusion : Theorem} {block : ProofSystem.Certificate}
    (prefixChecked : replay (ruleWitness policy) earlierNodes = some cache)
    (found : lookupPremises cache roots = some premises)
    (checked : BlockChecked policy premises conclusion block) :
    (ProofSystem.checker policy).check conclusion
      (earlierNodes ++ (expandBlock roots cache.size block).1, (expandBlock roots cache.size block).2) = true := by
  obtain ⟨result, accepted, rootFound⟩ := expandBlock_checked found checked
  apply (ProofSystem.checker_check_iff policy _ _).mpr
  exact ⟨result, replayFrom_append (ruleWitness policy) prefixChecked accepted, rootFound⟩

/-- A singleton local HOL inference has one physical rule occurrence. -/
def primitiveBlock (request : RuleRequest) (conclusion : Theorem) (origin : Origin) :
    ProofSystem.Certificate :=
  ([⟨conclusion, request, List.range request.premises.length, origin⟩], request.premises.length)

private theorem lookupPremises_range (premises : List Theorem) :
    lookupPremises premises.toArray (List.range premises.length) = some premises := by
  have collect : ∀ (offset : Nat), lookupPremises premises.toArray
      (List.range' offset (premises.length - offset)) = some (premises.drop offset) := by
    intro offset
    induction remaining : premises.length - offset generalizing offset with
    | zero =>
        have outside : premises.length ≤ offset := by omega
        simp [List.range', List.drop_eq_nil_of_le outside, lookupPremises]
    | succ count ih =>
        have inside : offset < premises.length := by omega
        have next : premises.length - (offset + 1) = count := by omega
        have rest := ih (offset + 1) next
        rw [List.range'_succ]
        rw [lookupPremises]
        simp only [List.getElem?_toArray, List.getElem?_eq_getElem inside, rest]
        simp only [Option.pure_def]
        exact congrArg some (List.cons_getElem_drop_succ (l := premises) (n := offset) (h := inside))
  simpa [← List.range_eq_range'] using collect 0

/-- A primitive local block is admitted by the actual HOL request checker;
no separate inference-authority callback is used. -/
theorem primitiveBlock_checked {policy : AxiomPolicy} [DecidablePred policy]
    (request : RuleRequest) (conclusion : Theorem) (origin : Origin)
    (checked : request.check policy = some conclusion) :
    BlockChecked policy request.premises conclusion (primitiveBlock request conclusion origin) := by
  let node : Receipt := ⟨conclusion, request, List.range request.premises.length, origin⟩
  have admitted : node.replay (ruleWitness policy) request.premises.toArray =
      some (request.premises.toArray.push conclusion) := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    exact ⟨lookupPremises_range _, checked, rfl⟩
  refine ⟨request.premises.toArray.push conclusion, ?_, ?_⟩
  · simp [primitiveBlock, node, replayFrom, admitted]
  · simp [primitiveBlock]


/-- One source output names one checked local HOL block. Its parent vector
uses chronological source-output addresses, rather than expanded trees. -/
abbrev BlockRequest := Node Theorem ProofSystem.Certificate Origin

/-- The compiler resolves source references, relocates a local block, and
records one physical root for its output. It does not run a second checker. -/
def expandFrom : List Receipt → Array Nat → List BlockRequest →
    Option (List Receipt × Array Nat)
  | earlierNodes, roots, [] => some (earlierNodes, roots)
  | earlierNodes, roots, request :: rest => do
      let selected ← lookupPremises roots request.parents
      let expanded := expandBlock selected earlierNodes.length request.witness
      expandFrom (earlierNodes ++ expanded.1) (roots.push expanded.2) rest

/-- Local block obligations refer to actual HOL replay from precisely the
selected earlier outputs. Every authored request is retained. -/
inductive LocallyChecked (policy : AxiomPolicy) [DecidablePred policy] :
    Array Theorem → List BlockRequest → Prop
  | nil (outputs) : LocallyChecked policy outputs []
  | cons {outputs request rest premises} :
      lookupPremises outputs request.parents = some premises →
      BlockChecked policy premises request.conclusion request.witness →
      LocallyChecked policy (outputs.push request.conclusion) rest →
      LocallyChecked policy outputs (request :: rest)

/-- The physical root vector reads back exactly the chronological output
vector, including repeated proofs and all output occurrences. -/
def RootAlignment (outputs actual : Array Theorem) (roots : Array Nat) : Prop :=
  lookupPremises actual roots.toList = some outputs.toList

private theorem select_roots {outputs actual : Array Theorem} {roots : Array Nat}
    (aligned : RootAlignment outputs actual roots)
    {parents : List Nat} {premises : List Theorem}
    (found : lookupPremises outputs parents = some premises) :
    ∃ selected, lookupPremises roots parents = some selected ∧
      lookupPremises actual selected = some premises := by
  induction parents generalizing premises with
  | nil =>
      cases Option.some.inj found
      exact ⟨[], rfl, rfl⟩
  | cons index rest ih =>
      cases first : outputs[index]? with
      | none => simp [lookupPremises, first] at found
      | some premise =>
          cases later : lookupPremises outputs rest with
          | none => simp [lookupPremises, first, later] at found
          | some remaining =>
              have same : premise :: remaining = premises := by
                simpa [lookupPremises, first, later] using found
              subst premises
              obtain ⟨selected, selectedFound, actualFound⟩ := ih later
              have lengths := lookupPremises_length actual aligned
              have present := (Array.getElem?_eq_some_iff.mp first).1
              have inside : index < roots.size := by simp only [Array.length_toList] at lengths; omega
              have entry := lookupPremises_at aligned index (by simpa using inside)
              have entry' : actual[roots[index]]? = outputs[index]? := by simpa using entry
              have selectedFirst : roots[index]? = some roots[index] := Array.getElem?_eq_getElem inside
              have actualFirst : actual[roots[index]]? = some premise := entry'.trans first
              exact ⟨roots[index] :: selected,
                by rw [lookupPremises, selectedFirst, selectedFound]; rfl,
                by rw [lookupPremises, actualFirst, actualFound]; rfl⟩


private theorem alignment_push {policy : AxiomPolicy} [DecidablePred policy]
    {outputs actual result : Array Theorem} {roots : Array Nat} {nodes : List Receipt}
    {conclusion : Theorem} {root : Nat}
    (aligned : RootAlignment outputs actual roots)
    (accepted : replayFrom (ruleWitness policy) actual nodes = some result)
    (rootFound : result[root]? = some conclusion) :
    RootAlignment (outputs.push conclusion) result (roots.push root) := by
  have old := lookupPremises_preserved (ruleWitness policy) accepted aligned
  unfold RootAlignment
  simp only [Array.toList_push]
  rw [lookupPremises_append, old]
  simp [lookupPremises, rootFound]

/-- Chronological block expansion produces an actual checked HOL graph. The
physical output roots read back exactly the original ordered claims. -/
theorem expandFrom_checked {policy : AxiomPolicy} [DecidablePred policy]
    {outputs actual : Array Theorem} {earlierNodes : List Receipt} {roots : Array Nat}
    {requests : List BlockRequest}
    (earlierChecked : replay (ruleWitness policy) earlierNodes = some actual)
    (aligned : RootAlignment outputs actual roots)
    (localChecks : LocallyChecked policy outputs requests) :
    ∃ nodes finalRoots finalCache,
      expandFrom earlierNodes roots requests = some (nodes, finalRoots) ∧
      replay (ruleWitness policy) nodes = some finalCache ∧
      RootAlignment (outputs.toList ++ requests.map (·.conclusion)).toArray finalCache finalRoots := by
  induction localChecks generalizing earlierNodes actual roots with
  | nil outputs =>
      exact ⟨earlierNodes, roots, actual, rfl, earlierChecked, by simpa using aligned⟩
  | @cons outputs request rest premises found checked tail ih =>
      obtain ⟨selected, selectedFound, actualFound⟩ := select_roots aligned found
      have sizeSame : actual.size = earlierNodes.length := by
        have actualSize : actual.size = (#[] : Array Theorem).size + earlierNodes.length :=
          replayFrom_size (ruleWitness policy) (nodes := earlierNodes) earlierChecked
        simpa only [Array.size_empty, Nat.zero_add] using actualSize
      obtain ⟨nextCache, blockChecked, rootFound⟩ := expandBlock_checked actualFound checked
      rw [sizeSame] at blockChecked rootFound
      have joined := replayFrom_append (ruleWitness policy) earlierChecked blockChecked
      have nextAligned := alignment_push aligned blockChecked rootFound
      obtain ⟨nodes, finalRoots, finalCache, expanded, replayed, finalAligned⟩ :=
        ih joined nextAligned
      refine ⟨nodes, finalRoots, finalCache, ?_, replayed, ?_⟩
      · rw [expandFrom, selectedFound]; exact expanded
      · simpa [Array.toList_push, List.map_cons, List.append_assoc] using finalAligned

/-- Future source references are refused by address resolution before any
block is emitted. -/
theorem expandFrom_future_refused (earlierNodes : List Receipt) (roots : Array Nat)
    (request : BlockRequest) (rest : List BlockRequest) (index : Nat)
    (member : index ∈ request.parents) (future : roots.size ≤ index) :
    expandFrom earlierNodes roots (request :: rest) = none := by
  have refused := lookupPremises_none_of_future member future
  simp [expandFrom, refused]

/-- The number of physical rule occurrences is exactly the sum of the
local-block occurrence counts, with the original earlier graph retained. -/
theorem expandFrom_size {earlierNodes nodes : List Receipt} {roots finalRoots : Array Nat}
    {requests : List BlockRequest}
    (expanded : expandFrom earlierNodes roots requests = some (nodes, finalRoots)) :
    nodes.length = earlierNodes.length + (requests.map (fun request => request.witness.1.length)).sum ∧
      finalRoots.size = roots.size + requests.length := by
  induction requests generalizing earlierNodes roots with
  | nil =>
      have same := Option.some.inj expanded
      cases same
      simp
  | cons request rest ih =>
      cases selection : lookupPremises roots request.parents with
      | none => simp [expandFrom, selection] at expanded
      | some selected =>
          have tail : expandFrom (earlierNodes ++ (expandBlock selected earlierNodes.length request.witness).1)
              (roots.push (expandBlock selected earlierNodes.length request.witness).2) rest =
              some (nodes, finalRoots) := by simpa [expandFrom, selection] using expanded
          obtain ⟨nodeCount, outputCount⟩ := ih tail
          constructor
          · simpa [expandBlock, Nat.add_assoc] using nodeCount
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using outputCount

/-- Concatenation is chronological: no block's witnesses or origins are
permuted, deduplicated or expanded into their parent trees. -/
theorem expandFrom_witnesses {earlierNodes nodes : List Receipt} {roots finalRoots : Array Nat}
    {requests : List BlockRequest}
    (expanded : expandFrom earlierNodes roots requests = some (nodes, finalRoots)) :
    nodes.map (fun node => (node.witness, node.origin)) =
      earlierNodes.map (fun node => (node.witness, node.origin)) ++
      requests.flatMap (fun request => request.witness.1.map (fun node => (node.witness, node.origin))) := by
  induction requests generalizing earlierNodes roots with
  | nil => cases Option.some.inj expanded; simp
  | cons request rest ih =>
      cases selection : lookupPremises roots request.parents with
      | none => simp [expandFrom, selection] at expanded
      | some selected =>
          have tail : expandFrom (earlierNodes ++ (expandBlock selected earlierNodes.length request.witness).1)
              (roots.push (expandBlock selected earlierNodes.length request.witness).2) rest =
              some (nodes, finalRoots) := by simpa [expandFrom, selection] using expanded
          simpa [List.map_append, expandBlock_witnesses, List.append_assoc] using ih tail


/-- Compilation starts with no theorem cache and no physical graph. -/
def compile (requests : List BlockRequest) : Option (List Receipt × Array Nat) :=
  expandFrom [] #[] requests

/-- Each chronological source output has an actual physical root in the
compiled HOL graph. These roots may coincide when a block reuses a premise. -/
theorem compile_checked {policy : AxiomPolicy} [DecidablePred policy]
    {requests : List BlockRequest} (localChecks : LocallyChecked policy #[] requests) :
    ∃ nodes roots cache,
      compile requests = some (nodes, roots) ∧
      replay (ruleWitness policy) nodes = some cache ∧
      RootAlignment (requests.map (·.conclusion)).toArray cache roots := by
  obtain ⟨nodes, roots, cache, expanded, accepted, aligned⟩ := expandFrom_checked
    (earlierNodes := []) (roots := #[]) (actual := #[]) rfl rfl localChecks
  exact ⟨nodes, roots, cache, expanded, accepted, by simpa using aligned⟩

/-- Every selected output is accepted by HOL Light's existing certificate
checker, with its full theorem, axiom dependencies and hypotheses intact. -/
theorem compile_accepted {policy : AxiomPolicy} [DecidablePred policy]
    {requests : List BlockRequest} (localChecks : LocallyChecked policy #[] requests)
    {index : Nat} {conclusion : Theorem}
    (selected : (requests.map (·.conclusion))[index]? = some conclusion) :
    ∃ nodes roots root,
      compile requests = some (nodes, roots) ∧ roots[index]? = some root ∧
      (ProofSystem.checker policy).check conclusion (nodes, root) = true := by
  obtain ⟨nodes, roots, cache, compiled, accepted, aligned⟩ := compile_checked localChecks
  have lengths := lookupPremises_length cache aligned
  have inside := (List.getElem?_eq_some_iff.mp selected).1
  have rootInside : index < roots.size := by simpa using (show index < roots.toList.length from by simp_all)
  have found := lookupPremises_at aligned index (by simpa using rootInside)
  have actualFound : cache[roots[index]]? = some conclusion := by simpa using found.trans selected
  refine ⟨nodes, roots, roots[index], compiled, Array.getElem?_eq_getElem rootInside, ?_⟩
  exact (ProofSystem.checker_check_iff policy _ _).mpr ⟨cache, accepted, actualFound⟩

/-- Rule payload size and premise-occurrence count are additive under
expansion. Numeric address encodings require a separate bit-length bound. -/
def receiptWeight (payload : Theorem → RuleRequest → Origin → Nat) (node : Receipt) : Nat :=
  payload node.conclusion node.witness node.origin + node.parents.length + 1

def graphWeight (payload : Theorem → RuleRequest → Origin → Nat) (nodes : List Receipt) : Nat :=
  (nodes.map (receiptWeight payload)).sum

/-- Relocation neither copies rule payloads nor changes premise multiplicity. -/
theorem expandBlock_weight (payload : Theorem → RuleRequest → Origin → Nat)
    (roots : List Nat) (base : Nat) (block : ProofSystem.Certificate) :
    graphWeight payload (expandBlock roots base block).1 = graphWeight payload block.1 := by
  simp only [graphWeight, expandBlock, List.map_map]
  congr 2
  funext node
  simp only [Function.comp_apply, receiptWeight, Node.relocate, List.length_map]

theorem graphWeight_append (payload : Theorem → RuleRequest → Origin → Nat) (left right : List Receipt) :
    graphWeight payload (left ++ right) = graphWeight payload left + graphWeight payload right := by
  simp [graphWeight, List.map_append, List.sum_append]

/-- The emitted payload-size account is the sum of local block sizes;
shared references are not expanded into source proof trees. -/
theorem expandFrom_weight (payload : Theorem → RuleRequest → Origin → Nat)
    {earlierNodes nodes : List Receipt} {roots finalRoots : Array Nat}
    {requests : List BlockRequest}
    (expanded : expandFrom earlierNodes roots requests = some (nodes, finalRoots)) :
    graphWeight payload nodes = graphWeight payload earlierNodes +
      (requests.map (fun request => graphWeight payload request.witness.1)).sum := by
  induction requests generalizing earlierNodes roots with
  | nil => cases Option.some.inj expanded; simp
  | cons request rest ih =>
      cases selection : lookupPremises roots request.parents with
      | none => simp [expandFrom, selection] at expanded
      | some selected =>
          have tail : expandFrom (earlierNodes ++ (expandBlock selected earlierNodes.length request.witness).1)
              (roots.push (expandBlock selected earlierNodes.length request.witness).2) rest =
              some (nodes, finalRoots) := by simpa [expandFrom, selection] using expanded
          have counted := ih tail
          rw [graphWeight_append, expandBlock_weight] at counted
          simpa [Nat.add_assoc] using counted

/-- A uniform local-block occurrence bound gives a linear physical-node
bound in the number of source outputs. -/
theorem compile_nodes_bound {requests : List BlockRequest} {nodes : List Receipt} {roots : Array Nat}
    (compiled : compile requests = some (nodes, roots)) (bound : Nat)
    (localBound : ∀ request ∈ requests, request.witness.1.length ≤ bound) :
    nodes.length ≤ requests.length * bound ∧ roots.size = requests.length := by
  obtain ⟨counted, outputs⟩ := expandFrom_size compiled
  have total : ∀ items : List BlockRequest,
      (∀ request ∈ items, request.witness.1.length ≤ bound) →
      (items.map (fun request => request.witness.1.length)).sum ≤ items.length * bound := by
    intro items bounded
    induction items with
    | nil => simp
    | cons request rest ih =>
        have first := bounded request (by simp)
        have tail := ih (fun item member => bounded item (by simp [member]))
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul]
        omega
  constructor
  · rw [counted]
    simpa using total requests localBound
  · simpa using outputs

/-- The total number of ordered parent references, retaining repeated uses. -/
def parentOccurrences (nodes : List Receipt) : Nat :=
  (nodes.map (fun node => node.parents.length)).sum

/-- Numeric reference payload in binary, before any delimiters or framing. -/
def parentAddressBits (nodes : List Receipt) : Nat :=
  (nodes.map (fun node => (node.parents.map Nat.size).sum)).sum

private theorem addressBits_bound (limit : Nat) (parents : List Nat)
    (bounded : ∀ index ∈ parents, index < limit) :
    (parents.map Nat.size).sum ≤ parents.length * Nat.size limit := by
  induction parents with
  | nil => simp
  | cons index rest ih =>
      have first := Nat.size_le_size (Nat.le_of_lt (bounded index (by simp)))
      have later := ih (fun item member => bounded item (by simp [member]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul]
      omega

/-- Checked graphs bound every stored binary parent address by the completed
physical-node count; no unary or constant-cost address model is assumed. -/
theorem checked_parentAddressBits_bound {policy : AxiomPolicy} [DecidablePred policy]
    {nodes : List Receipt} {cache : Array Theorem}
    (accepted : replay (ruleWitness policy) nodes = some cache) :
    parentAddressBits nodes ≤ parentOccurrences nodes * Nat.size nodes.length := by
  have bounded : ∀ node ∈ nodes, ∀ index ∈ node.parents, index < cache.size :=
    replayFrom_parents_lt_result (ruleWitness policy) (nodes := nodes) accepted
  have counted : cache.size = nodes.length := by
    have count : cache.size = (#[] : Array Theorem).size + nodes.length :=
      replayFrom_size (ruleWitness policy) (nodes := nodes) accepted
    simpa only [Array.size_empty, Nat.zero_add] using count
  have total : ∀ items : List Receipt,
      (∀ node ∈ items, ∀ index ∈ node.parents, index < nodes.length) →
      parentAddressBits items ≤ parentOccurrences items * Nat.size nodes.length := by
    intro items cited
    induction items with
    | nil => simp [parentAddressBits, parentOccurrences]
    | cons node rest ih =>
        have first := addressBits_bound nodes.length node.parents (cited node (by simp))
        have later := ih (fun item member => cited item (by simp [member]))
        have joined := Nat.add_le_add first later
        simpa only [parentAddressBits, parentOccurrences, List.map_cons, List.sum_cons, Nat.add_mul] using joined
  rw [counted] at bounded
  exact total nodes bounded

/-- Every compiled output root selects a physical theorem in the emitted
graph, including roots that reuse an earlier block's proof. -/
theorem compile_roots_lt_nodes {policy : AxiomPolicy} [DecidablePred policy]
    {requests : List BlockRequest} {nodes : List Receipt} {roots : Array Nat}
    (compiled : compile requests = some (nodes, roots))
    (localChecks : LocallyChecked policy #[] requests) :
    ∀ root ∈ roots.toList, root < nodes.length := by
  obtain ⟨actualNodes, actualRoots, cache, emitted, accepted, aligned⟩ := compile_checked localChecks
  have same := Option.some.inj (compiled.symm.trans emitted)
  cases same
  have counted : cache.size = nodes.length := by
    have count : cache.size = (#[] : Array Theorem).size + nodes.length :=
      replayFrom_size (ruleWitness policy) (nodes := nodes) accepted
    simpa only [Array.size_empty, Nat.zero_add] using count
  intro root member
  have earlier := lookupPremises_indices_lt aligned root member
  simpa only [counted] using earlier

/-- The output-root vector also has a binary, rather than unary, size bound. -/
theorem compile_rootAddressBits_bound {policy : AxiomPolicy} [DecidablePred policy]
    {requests : List BlockRequest} {nodes : List Receipt} {roots : Array Nat}
    (compiled : compile requests = some (nodes, roots))
    (localChecks : LocallyChecked policy #[] requests) :
    (roots.toList.map Nat.size).sum ≤ requests.length * Nat.size nodes.length := by
  have bounded := addressBits_bound nodes.length roots.toList
    (compile_roots_lt_nodes compiled localChecks)
  have counted := (expandFrom_size compiled).2
  simpa using bounded.trans_eq (by simp [counted])

/-- A payload account that also charges binary parent addresses. Framing and
payload encodings may be supplied by their own declared per-receipt weights. -/
def binaryGraphWeight (payload : Theorem → RuleRequest → Origin → Nat) (nodes : List Receipt) : Nat :=
  graphWeight payload nodes + parentAddressBits nodes

/-- Address relocation has an explicit logarithmic-size charge on top of the
unchanged rule payload and occurrence sizes. This is a size bound only. -/
theorem compiled_binaryGraphWeight_bound (payload : Theorem → RuleRequest → Origin → Nat)
    {policy : AxiomPolicy} [DecidablePred policy] {requests : List BlockRequest}
    {nodes : List Receipt} {roots : Array Nat}
    (compiled : compile requests = some (nodes, roots))
    (localChecks : LocallyChecked policy #[] requests) :
    binaryGraphWeight payload nodes ≤
      (requests.map (fun request => graphWeight payload request.witness.1)).sum +
      parentOccurrences nodes * Nat.size nodes.length := by
  obtain ⟨actualNodes, actualRoots, cache, emitted, accepted, _⟩ := compile_checked localChecks
  have same := Option.some.inj (compiled.symm.trans emitted)
  cases same
  have payloadCount : graphWeight payload nodes =
      (requests.map (fun request => graphWeight payload request.witness.1)).sum := by
    have exactCount := expandFrom_weight payload (earlierNodes := []) compiled
    simpa only [graphWeight, List.map_nil, List.sum_nil, Nat.zero_add] using exactCount
  have addressCount := checked_parentAddressBits_bound accepted
  unfold binaryGraphWeight
  rw [payloadCount]
  exact Nat.add_le_add_left addressCount _

/-- Appending a supplied primitive request emits its actual receipt and
selects the newly stored theorem as the block root. -/
def appendPrimitive (premiseCount : Nat) (earlierNodes : List Receipt) (parents : List Nat)
    (request : RuleRequest) (conclusion : Theorem) (origin : Origin) : ProofSystem.Certificate :=
  (earlierNodes ++ [⟨conclusion, request, parents, origin⟩], premiseCount + earlierNodes.length)

/-- The append operation is checked by the original HOL rule-witness replay. -/
theorem appendPrimitive_checked {policy : AxiomPolicy} [DecidablePred policy]
    {premises : List Theorem} {earlierNodes : List Receipt} {cache : Array Theorem}
    {parents : List Nat} {request : RuleRequest} {conclusion : Theorem} {origin : Origin}
    (earlier : replayFrom (ruleWitness policy) premises.toArray earlierNodes = some cache)
    (selected : lookupPremises cache parents = some request.premises)
    (checked : request.check policy = some conclusion) :
    BlockChecked policy premises conclusion
      (appendPrimitive premises.length earlierNodes parents request conclusion origin) := by
  let node : Receipt := ⟨conclusion, request, parents, origin⟩
  have step : node.replay (ruleWitness policy) cache = some (cache.push conclusion) :=
    (ProofSystem.node_replay_iff policy _ _ _).mpr ⟨selected, checked, rfl⟩
  have accepted : replayFrom (ruleWitness policy) cache [node] = some (cache.push conclusion) := by
    simp [replayFrom, step]
  have counted : cache.size = premises.length + earlierNodes.length := by
    have counted : cache.size = premises.toArray.size + earlierNodes.length :=
      replayFrom_size (ruleWitness policy) (cache := premises.toArray) (nodes := earlierNodes) earlier
    simpa only [List.size_toArray] using counted
  refine ⟨cache.push conclusion, replayFrom_append (ruleWitness policy) earlier accepted, ?_⟩
  simp [appendPrimitive, ← counted]

/-- The builder reuses the proof-execution state, retaining external premises
in its cache and emitting only newly checked rule receipts. -/
def start (premises : List Theorem) : ProofExecution.State := ⟨premises.toArray, #[]⟩

/-- A builder state is checked by the original replay from its external
premise vector. This is an invariant, not a second rule authority. -/
def BuildChecked (policy : AxiomPolicy) [DecidablePred policy]
    (premises : List Theorem) (state : ProofExecution.State) : Prop :=
  replayFrom (ruleWitness policy) premises.toArray state.receipts.toList = some state.cache

theorem start_checked (policy : AxiomPolicy) [DecidablePred policy] (premises : List Theorem) :
    BuildChecked policy premises (start premises) := rfl

/-- Compute a primitive's result, replay its actual ordered parent vector,
and retain the exact receipt. Unsupported or mismatched requests are refused
by the existing HOL operations. -/
def emit (policy : AxiomPolicy) [DecidablePred policy] (request : RuleRequest)
    (parents : List Nat) (origin : Origin) (state : ProofExecution.State) :
    Option (ProofExecution.State × Nat) := do
  let conclusion ← request.check policy
  let node : Receipt := ⟨conclusion, request, parents, origin⟩
  let nextCache ← node.replay (ruleWitness policy) state.cache
  pure (⟨nextCache, state.receipts.push node⟩, state.cache.size)

/-- Successful emission keeps the exact primitive request, conclusion,
parent occurrences and origin, and grows the cache by one checked theorem. -/
theorem emit_eq_some_iff {policy : AxiomPolicy} [DecidablePred policy]
    (request : RuleRequest) (parents : List Nat) (origin : Origin)
    (state result : ProofExecution.State) (root : Nat) :
    emit policy request parents origin state = some (result, root) ↔
      ∃ conclusion, request.check policy = some conclusion ∧
        lookupPremises state.cache parents = some request.premises ∧
        result.cache = state.cache.push conclusion ∧
        result.receipts = state.receipts.push ⟨conclusion, request, parents, origin⟩ ∧
        root = state.cache.size := by
  unfold emit
  cases checked : request.check policy with
  | none => simp
  | some conclusion =>
      let node : Receipt := ⟨conclusion, request, parents, origin⟩
      cases replayed : node.replay (ruleWitness policy) state.cache with
      | none =>
          constructor
          · intro impossible
            simp [node, replayed] at impossible
          · rintro ⟨output, outputChecked, selected, cacheSame, receiptsSame, rootSame⟩
            have same := Option.some.inj outputChecked
            subst output
            have accepted : node.replay (ruleWitness policy) state.cache =
                some (state.cache.push conclusion) :=
              (ProofSystem.node_replay_iff policy _ _ _).mpr ⟨selected, checked, rfl⟩
            rw [replayed] at accepted
            contradiction
      | some next =>
          have facts := (ProofSystem.node_replay_iff policy _ _ _).mp replayed
          constructor
          · intro accepted
            have pairSame : (⟨next, state.receipts.push node⟩, state.cache.size) = (result, root) := by
              simpa [node, replayed] using accepted
            cases pairSame
            exact ⟨conclusion, rfl, facts.1, facts.2.2, rfl, rfl⟩
          · rintro ⟨output, outputChecked, selected, cacheSame, receiptsSame, rootSame⟩
            have same := Option.some.inj outputChecked
            subst output
            obtain ⟨resultCache, resultReceipts⟩ := result
            simp only at cacheSame receiptsSame
            subst resultCache resultReceipts root
            simp [node, replayed, facts.2.2]

/-- A concrete checked primitive computes its exact next builder state;
this lemma supports direct construction of derived-rule blocks. -/
theorem emit_of_checked {policy : AxiomPolicy} [DecidablePred policy]
    {request : RuleRequest} {parents : List Nat} {origin : Origin}
    {state : ProofExecution.State} {conclusion : Theorem}
    (checked : request.check policy = some conclusion)
    (selected : lookupPremises state.cache parents = some request.premises) :
    emit policy request parents origin state =
      some (⟨state.cache.push conclusion,
        state.receipts.push ⟨conclusion, request, parents, origin⟩⟩, state.cache.size) :=
  (emit_eq_some_iff _ _ _ _ _ _).mpr ⟨conclusion, checked, selected, rfl, rfl, rfl⟩

/-- Each emitted state replays from the same original external premises. -/
theorem emit_checked {policy : AxiomPolicy} [DecidablePred policy]
    {premises : List Theorem} {request : RuleRequest} {parents : List Nat} {origin : Origin}
    {state result : ProofExecution.State} {root : Nat}
    (earlier : BuildChecked policy premises state)
    (emitted : emit policy request parents origin state = some (result, root)) :
    BuildChecked policy premises result ∧ ∃ conclusion,
      request.check policy = some conclusion ∧ result.cache[root]? = some conclusion := by
  obtain ⟨conclusion, checked, selected, cacheSame, receiptsSame, rootSame⟩ :=
    (emit_eq_some_iff request parents origin state result root).mp emitted
  let node : Receipt := ⟨conclusion, request, parents, origin⟩
  have step : node.replay (ruleWitness policy) state.cache = some result.cache :=
    (ProofSystem.node_replay_iff policy _ _ _).mpr ⟨selected, checked, cacheSame⟩
  have accepted : replayFrom (ruleWitness policy) state.cache [node] = some result.cache := by
    simp [replayFrom, step]
  constructor
  · unfold BuildChecked
    rw [receiptsSame, Array.toList_push]
    exact replayFrom_append (ruleWitness policy) earlier accepted
  · refine ⟨conclusion, checked, ?_⟩
    rw [cacheSame, rootSame]
    exact Array.getElem?_push_size

/-- Emission cannot change any already stored theorem or its physical root. -/
theorem emit_preserves_lookup {policy : AxiomPolicy} [DecidablePred policy]
    {request : RuleRequest} {parents : List Nat} {origin : Origin}
    {state result : ProofExecution.State} {root index : Nat} {conclusion : Theorem}
    (emitted : emit policy request parents origin state = some (result, root))
    (found : state.cache[index]? = some conclusion) : result.cache[index]? = some conclusion := by
  obtain ⟨output, _, _, cacheSame, _, _⟩ :=
    (emit_eq_some_iff request parents origin state result root).mp emitted
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  rw [cacheSame, Array.getElem?_push, if_neg (Nat.ne_of_lt inside)]
  exact found

/-- A future parent is refused even if the primitive checker independently
returns a theorem. -/
theorem emit_future_refused (policy : AxiomPolicy) [DecidablePred policy]
    (request : RuleRequest) (parents : List Nat) (origin : Origin) (state : ProofExecution.State)
    {index : Nat} (member : index ∈ parents) (future : state.cache.size ≤ index) :
    emit policy request parents origin state = none := by
  cases checked : request.check policy with
  | none => simp [emit, checked]
  | some conclusion =>
      have refused := Node.future_reference_refused (ruleWitness policy) state.cache
        (⟨conclusion, request, parents, origin⟩ : Receipt) member future
      simp [emit, checked, refused]

/-- The builder's output is the existing certificate representation. -/
def finish (state : ProofExecution.State) (root : Nat) : ProofSystem.Certificate :=
  (state.receipts.toList, root)

theorem finish_checked {policy : AxiomPolicy} [DecidablePred policy]
    {premises : List Theorem} {state : ProofExecution.State} {root : Nat} {conclusion : Theorem}
    (checked : BuildChecked policy premises state) (found : state.cache[root]? = some conclusion) :
    BlockChecked policy premises conclusion (finish state root) := ⟨state.cache, checked, found⟩

/-- Append a concrete local graph using the original HOL replay. External
references and its final root are checked before returning a builder state. -/
def emitBlock (policy : AxiomPolicy) [DecidablePred policy] (roots : List Nat)
    (block : ProofSystem.Certificate) (state : ProofExecution.State) :
    Option (ProofExecution.State × Nat) := do
  let _ ← lookupPremises state.cache roots
  let expanded := expandBlock roots state.cache.size block
  let cache ← replayFrom (ruleWitness policy) state.cache expanded.1
  let _ ← cache[expanded.2]?
  pure (⟨cache, state.receipts ++ expanded.1.toArray⟩, expanded.2)

/-- Concrete block emission preserves the builder's original replay invariant
and every earlier root, and stores exactly the selected block theorem. -/
theorem emitBlock_checked {policy : AxiomPolicy} [DecidablePred policy]
    {premises blockPremises : List Theorem} {roots : List Nat}
    {block : ProofSystem.Certificate} {state : ProofExecution.State} {conclusion : Theorem}
    (earlier : BuildChecked policy premises state)
    (selected : lookupPremises state.cache roots = some blockPremises)
    (checked : BlockChecked policy blockPremises conclusion block) :
    ∃ result root,
      emitBlock policy roots block state = some (result, root) ∧
      BuildChecked policy premises result ∧ result.cache[root]? = some conclusion ∧
      result.receipts.toList = state.receipts.toList ++
        (expandBlock roots state.cache.size block).1 ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → result.cache[index]? = some fact := by
  obtain ⟨cache, accepted, rootFound⟩ := expandBlock_checked selected checked
  let result : ProofExecution.State :=
    ⟨cache, state.receipts ++ (expandBlock roots state.cache.size block).1.toArray⟩
  refine ⟨result, (expandBlock roots state.cache.size block).2, ?_, ?_, rootFound, ?_, ?_⟩
  · simp [emitBlock, selected, accepted, rootFound, result]
  · unfold BuildChecked
    simp only [result, Array.toList_append]
    exact replayFrom_append (ruleWitness policy) earlier accepted
  · simp [result]
  · intro index fact found
    exact replayFrom_preserves_lookup (ruleWitness policy) accepted found

/-- Successful block emission preserves the original replay invariant even
for arbitrary supplied block data. Its actual primitive replay is the
reason for soundness; no additional local-correctness assumption is needed. -/
theorem emitBlock_preserves_checked {policy : AxiomPolicy} [DecidablePred policy]
    {premises : List Theorem} {roots : List Nat} {block : ProofSystem.Certificate}
    {state result : ProofExecution.State} {root : Nat}
    (earlier : BuildChecked policy premises state)
    (emitted : emitBlock policy roots block state = some (result, root)) :
    BuildChecked policy premises result ∧ (∃ conclusion, result.cache[root]? = some conclusion) ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → result.cache[index]? = some fact := by
  cases selected : lookupPremises state.cache roots with
  | none => simp [emitBlock, selected] at emitted
  | some externalPremises =>
      let expanded := expandBlock roots state.cache.size block
      cases accepted : replayFrom (ruleWitness policy) state.cache expanded.1 with
      | none => simp [emitBlock, selected, expanded, accepted] at emitted
      | some cache =>
          cases found : cache[expanded.2]? with
          | none => simp [emitBlock, selected, expanded, accepted, found] at emitted
          | some conclusion =>
              have same : (⟨cache, state.receipts ++ expanded.1.toArray⟩, expanded.2) = (result, root) := by
                simpa [emitBlock, selected, expanded, accepted, found] using emitted
              cases same
              refine ⟨?_, ⟨conclusion, found⟩, ?_⟩
              · unfold BuildChecked
                simp only [Array.toList_append]
                exact replayFrom_append (ruleWitness policy) earlier accepted
              · intro index fact present
                exact replayFrom_preserves_lookup (ruleWitness policy) accepted present

/-- An unavailable external premise refuses the local block, even when none
of its internal primitive rules happens to use that slot. -/
theorem emitBlock_future_refused (policy : AxiomPolicy) [DecidablePred policy]
    (roots : List Nat) (block : ProofSystem.Certificate) (state : ProofExecution.State)
    {index : Nat} (member : index ∈ roots) (future : state.cache.size ≤ index) :
    emitBlock policy roots block state = none := by
  simp [emitBlock, lookupPremises_none_of_future member future]

namespace Controls

open ProofExecution.Controls

/-- The second local block has two distinct premise slots. Both are relocated
to the single physical proof created by the first block. -/
def sharedPlan (first second : Origin) : List BlockRequest :=
  [⟨reflexivityTheorem, primitiveBlock (.inference (.refl proposition)) reflexivityTheorem first, [], first⟩,
   ⟨reflexivityTheorem,
     primitiveBlock (.inference (.trans reflexivityTheorem reflexivityTheorem)) reflexivityTheorem second,
     [0, 0], second⟩]

theorem sharedPlan_checked (first second : Origin) :
    LocallyChecked emptyAxiomPolicy #[] (sharedPlan first second) := by
  have reflCheck := (ProofSystem.node_replay_iff emptyAxiomPolicy _ _ _).mp (reflexivity_replayed first)
  have transCheck := (ProofSystem.node_replay_iff emptyAxiomPolicy _ _ _).mp
    (shared_transitivity_replayed first second)
  apply LocallyChecked.cons (premises := []) rfl
  · exact primitiveBlock_checked _ _ _ reflCheck.2.1
  · apply LocallyChecked.cons (premises := [reflexivityTheorem, reflexivityTheorem]) rfl
    · exact primitiveBlock_checked _ _ _ transCheck.2.1
    · exact .nil _

/-- Computed graph construction keeps both parent occurrences pointing to
physical node zero; no second copy of the reflexivity proof is emitted. -/
theorem sharedPlan_emitted (first second : Origin) :
    compile (sharedPlan first second) =
      some ([reflexivity first, sharedTransitivity second], #[0, 1]) := by rfl

/-- The assembled output is accepted by the actual HOL Light checker. -/
theorem sharedPlan_accepted (first second : Origin) :
    (ProofSystem.checker emptyAxiomPolicy).check reflexivityTheorem
      ([reflexivity first, sharedTransitivity second], 1) = true := by
  obtain ⟨nodes, roots, root, compiled, selected, accepted⟩ :=
    compile_accepted (sharedPlan_checked first second) (index := 1) (conclusion := reflexivityTheorem) rfl
  rw [sharedPlan_emitted] at compiled
  have same := Option.some.inj compiled
  cases same
  have rootSame : root = 1 := by simpa using selected.symm
  simpa [rootSame] using accepted

/-- A future logical reference is refused before block relocation. -/
theorem future_plan_refused (origin : Origin) :
    compile [⟨reflexivityTheorem,
      primitiveBlock (.inference (.refl proposition)) reflexivityTheorem origin, [0], origin⟩] = none := by
  exact expandFrom_future_refused [] #[] _ [] 0 (by simp) (by simp)


/-- The runtime builder emits a checked primitive graph without choosing
proofs from existence theorems. -/
def buildShared (first second : Origin) : Option (ProofExecution.State × Nat) := do
  let (afterRefl, _) ← emit emptyAxiomPolicy (.inference (.refl proposition)) [] first (start [])
  emit emptyAxiomPolicy (.inference (.trans reflexivityTheorem reflexivityTheorem)) [0, 0] second afterRefl

theorem buildShared_emitted (first second : Origin) :
    buildShared first second = some (twice first second, 1) := by
  have reflCheck := (ProofSystem.node_replay_iff emptyAxiomPolicy _ _ _).mp (reflexivity_replayed first)
  have transCheck := (ProofSystem.node_replay_iff emptyAxiomPolicy _ _ _).mp
    (shared_transitivity_replayed first second)
  have firstEmitted : emit emptyAxiomPolicy (.inference (.refl proposition)) [] first (start []) =
      some (once first, 0) := by
    apply (emit_eq_some_iff _ _ _ _ _ _).mpr
    exact ⟨reflexivityTheorem, reflCheck.2.1, rfl, rfl, rfl, rfl⟩
  have secondEmitted : emit emptyAxiomPolicy (.inference (.trans reflexivityTheorem reflexivityTheorem))
      [0, 0] second (once first) = some (twice first second, 1) := by
    apply (emit_eq_some_iff _ _ _ _ _ _).mpr
    exact ⟨reflexivityTheorem, transCheck.2.1, rfl, rfl, rfl, rfl⟩
  simp [buildShared, firstEmitted, secondEmitted]

theorem builder_future_refused (origin : Origin) :
    emit emptyAxiomPolicy (.inference (.refl proposition)) [0] origin (start []) = none :=
  emit_future_refused _ _ _ _ _ (index := 0) (by simp) (by simp [start])

end Controls

end Mettapedia.Languages.HOLLight.GraphExpansion
