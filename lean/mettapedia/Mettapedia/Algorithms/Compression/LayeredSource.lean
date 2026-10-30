import Mettapedia.Algorithms.Compression.WholeArtifact
import Mettapedia.Algorithms.WellFoundedServices.DependencyAnalysis

/-!
# Layered source artifacts over the shared framing and dependency services

The LM1 record stores a final source tree once and explicit newest-first
LC1/LC2 decoder descriptors. These transport laws neither execute source nor
grant a certificate to decoded metadata. Source-profile and individual helper
expansion contracts remain separate from framing.

The partial expansion fold composes checked helper steps. Dependency checking
uses the existing catalogue's Kahn service. Its bounded wave loop agrees with
that service whenever the budget covers the pending items, so bound exhaustion
cannot be confused with a cycle in an admitted finite library.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.LayeredSource

open KolmogorovComplexity FramedTree
open WellFoundedServices

def octet (value : Fin 256) : BinString :=
  List.ofFn fun index : Fin 8 => value.val.testBit (7 - index.val)

def octets (values : List (Fin 256)) : BinString := values.flatMap octet

def envelopeTag : BinString := octets [83, 73, 67, 49]
def version : BinString := octets [76, 77, 49]
def layerTag : BinString := octet 10
def stackTag : BinString := octet 11
def literalTag : BinString := octet 7
def symbolKind : BinString := octets [83, 121, 109, 98, 111, 108]

structure Layer where
  codec : BinString
  name : BinString
  deriving DecidableEq, Repr

structure Payload where
  layers : List Layer
  source : Tree
  deriving Repr

def layerTree (layer : Layer) : Tree := .node layerTag [.leaf layer.codec, .leaf layer.name]

def parseLayer : Tree → Option Layer
  | .node tag [.leaf codec, .leaf name] => if tag = layerTag then some ⟨codec, name⟩ else none
  | _ => none

def toTree (payload : Payload) : Tree :=
  .node stackTag [.leaf version, .node [] (payload.layers.map layerTree), payload.source]

def fromTree : Tree → Option Payload
  | .node tag [.leaf label, .node marker entries, source] =>
      if tag = stackTag ∧ label = version ∧ marker = [] then
        (entries.mapM parseLayer).map fun layers => ⟨layers, source⟩
      else none
  | _ => none

theorem parseLayer_layerTree (layer : Layer) : parseLayer (layerTree layer) = some layer := by
  cases layer
  simp [layerTree, parseLayer]

theorem parse_layer_vector (layers : List Layer) :
    (layers.map layerTree).mapM parseLayer = some layers := by
  induction layers with
  | nil => rfl
  | cons first rest ih => simp [parseLayer_layerTree, ih]

theorem fromTree_toTree (payload : Payload) : fromTree (toTree payload) = some payload := by
  cases payload with
  | mk layers source =>
      change ((layers.map layerTree).mapM parseLayer).map (fun decoded => Payload.mk decoded source) = _
      rw [parse_layer_vector]
      rfl

theorem parseLayer_sound {tree : Tree} {layer : Layer} (found : parseLayer tree = some layer) :
    layerTree layer = tree := by
  unfold parseLayer at found
  split at found <;> try contradiction
  split at found <;> try contradiction
  cases Option.some.inj found
  simp_all [layerTree]

private theorem parse_vector_sound : ∀ (trees : List Tree) (layers : List Layer),
    trees.mapM parseLayer = some layers → layers.map layerTree = trees
  | [], layers, found => by cases Option.some.inj found; rfl
  | tree :: trees, layers, found => by
      cases first : parseLayer tree with
      | none => simp [first] at found
      | some layer =>
          cases tail : trees.mapM parseLayer with
          | none => simp [first, tail] at found
          | some rest =>
              simp [first, tail] at found
              subst layers
              simp only [List.map_cons, parseLayer_sound first, parse_vector_sound trees rest tail]

theorem fromTree_sound {tree : Tree} {payload : Payload} (found : fromTree tree = some payload) :
    toTree payload = tree := by
  unfold fromTree at found
  split at found <;> try contradiction
  split at found <;> try contradiction
  rename_i accepted
  simp only [Option.map_eq_some_iff] at found
  obtain ⟨layers, parsed, rfl⟩ := found
  simp_all [toTree, parse_vector_sound _ _ parsed]

def write (payload : Payload) : BinString :=
  Framing.encodePadded [envelopeTag, version, FramedTree.encode (toTree payload)]

def read (input : BinString) : Option Payload := do
  let fields ← Framing.decodePadded input
  match fields with
  | [header, label, payload] =>
      if header = envelopeTag ∧ label = version then do
        let tree ← FramedTree.decodeAll payload
        fromTree tree
      else none
  | _ => none

def byteCost (payload : Payload) : Nat :=
  Framing.byteLength [envelopeTag, version, FramedTree.encode (toTree payload)]

theorem read_write (payload : Payload) : read (write payload) = some payload := by
  simp [read, write, Framing.decodePadded_encode, FramedTree.decodeAll_encode, fromTree_toTree]

theorem write_injective : Function.Injective write := by
  intro first second same
  have equal := congrArg read same
  simpa only [read_write, Option.some.injEq] using equal

/-- Descriptor strings, vector framing and the complete source tree are
inside this length; there is no uncharged external helper table. -/
theorem serialized_length (payload : Payload) : (write payload).length = 8 * byteCost payload := by
  exact Framing.encodePadded_length _

section Expansion

variable {Source : Type*}

def expand (step : Layer → Source → Option Source) : List Layer → Source → Option Source
  | [], source => some source
  | first :: rest, source => (step first source).bind (expand step rest)

theorem expand_append (step : Layer → Source → Option Source)
    (first second : List Layer) (source : Source) :
    expand step (first ++ second) source = (expand step first source).bind (expand step second) := by
  induction first generalizing source with
  | nil => rfl
  | cons layer rest ih =>
      simp only [List.cons_append, expand]
      cases next : step layer source <;> simp [ih]

theorem prepend_reconstructs (step : Layer → Source → Option Source) (layers : List Layer)
    (layer : Layer) (candidate current original : Source)
    (newest : step layer candidate = some current) (earlier : expand step layers current = some original) :
    expand step (layer :: layers) candidate = some original := by
  simp only [expand, newest, Option.bind_some, earlier]

/-- A failed intermediate expansion never publishes a partially restored
source as a successful complete observation. -/
theorem failed_prefix_rejects (step : Layer → Source → Option Source)
    (first second : List Layer) (source : Source) (failed : expand step first source = none) :
    expand step (first ++ second) source = none := by rw [expand_append, failed]; rfl

end Expansion

/-! ## Finite dependency admission -/

mutual
  def mentions (name : BinString) : Tree → Bool
    | .leaf _ => false
    | .node tag children =>
        (match children with
        | [.leaf kind, .leaf value] => decide (tag = literalTag ∧ kind = symbolKind ∧ value = name)
        | _ => false) || mentionsAny name children

  def mentionsAny (name : BinString) : List Tree → Bool
    | [] => false
    | child :: rest => mentions name child || mentionsAny name rest
end

theorem mentionsAny_eq_any (name : BinString) (children : List Tree) :
    mentionsAny name children = children.any (mentions name) := by
  induction children with
  | nil => rfl
  | cons first rest ih => simp only [mentionsAny, List.any_cons, ih]

theorem mentions_symbol (name value : BinString) :
    mentions name (.node literalTag [.leaf symbolKind, .leaf value]) = decide (value = name) := by
  simp [mentions, mentionsAny]

def catalogue (names : List BinString) (body : BinString → Tree) : Catalogue BinString where
  items := names
  deps name := names.filter fun dependency => mentions dependency (body name)

theorem catalogue_uses (names : List BinString) (body : BinString → Tree) (first second : BinString) :
    (catalogue names body).Uses first second ↔
      first ∈ names ∧ second ∈ names ∧ mentions second (body first) = true := by
  simp [Catalogue.Uses, catalogue, List.mem_filter]

section BoundedWaves

variable {Name : Type*} [DecidableEq Name]

def rounds (graph : Catalogue Name) : Nat → Catalogue.Plan Name → Option (Catalogue.Schedule Name)
  | 0, plan => if plan.remaining = [] then some (.waves plan.layers) else none
  | fuel + 1, plan =>
      if plan.remaining = [] then some (.waves plan.layers)
      else if graph.ready plan.remaining = [] then some (.blocked plan.remaining)
      else rounds graph fuel ⟨plan.layers ++ [graph.ready plan.remaining],
        plan.remaining.filter fun item => decide (item ∉ graph.ready plan.remaining)⟩

/-- This is the bounded native wave-loop schedule, not a definition of the
reference schedule as itself. Their recursors and stop conditions differ. -/
theorem rounds_agrees (graph : Catalogue Name) (fuel : Nat) (plan : Catalogue.Plan Name)
    (enough : plan.remaining.length ≤ fuel) :
    rounds graph fuel plan = some (graph.kahn.run plan) := by
  induction fuel generalizing plan with
  | zero =>
      have empty : plan.remaining = [] := List.length_eq_zero_iff.mp (by omega)
      have stop : graph.kahn.step plan = .inr (.waves plan.layers) := by simp [Catalogue.kahn, empty]
      rw [graph.kahn.run_of_inr stop]
      simp [rounds, empty]
  | succ fuel ih =>
      by_cases empty : plan.remaining = []
      · have stop : graph.kahn.step plan = .inr (.waves plan.layers) := by simp [Catalogue.kahn, empty]
        rw [graph.kahn.run_of_inr stop]
        simp [rounds, empty]
      · by_cases blocked : graph.ready plan.remaining = []
        · have stop : graph.kahn.step plan = .inr (.blocked plan.remaining) := by
            simp [Catalogue.kahn, empty, blocked]
          rw [graph.kahn.run_of_inr stop]
          simp [rounds, empty, blocked]
        · let next : Catalogue.Plan Name := ⟨plan.layers ++ [graph.ready plan.remaining],
            plan.remaining.filter fun item => decide (item ∉ graph.ready plan.remaining)⟩
          have decrease : graph.kahn.measure next < graph.kahn.measure plan := graph.remaining_lt blocked
          have advance : graph.kahn.step plan = .inl ⟨next, decrease⟩ := by
            simp [Catalogue.kahn, empty, blocked, next]
          have bounded : next.remaining.length ≤ fuel := by
            change (plan.remaining.filter fun item => decide (item ∉ graph.ready plan.remaining)).length ≤ fuel
            have smaller := graph.remaining_lt blocked
            omega
          have referenceStep := graph.kahn.run_of_inl advance
          simp only [rounds, if_neg empty, if_neg blocked]
          rw [referenceStep]
          exact ih next bounded

theorem firstOccurrences_eq {names : List Name} (unique : names.Nodup) : firstOccurrences names = names := by
  induction names with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨fresh, tail⟩ := List.nodup_cons.mp unique
      simp only [firstOccurrences, ih tail, List.cons.injEq, true_and]
      apply List.filter_eq_self.mpr
      intro item present
      simpa using (show item ≠ first by intro same; subst item; exact fresh present)

theorem rounds_schedule (graph : Catalogue Name) (unique : graph.items.Nodup) :
    rounds graph graph.items.length ⟨[], graph.items⟩ = some (graph.schedule graph.items) := by
  rw [Catalogue.schedule, firstOccurrences_eq unique]
  exact rounds_agrees graph _ _ (Nat.le_refl _)

theorem checked_waves_acyclic (graph : Catalogue Name) (unique : graph.items.Nodup)
    (waves : List (List Name))
    (checked : rounds graph graph.items.length ⟨[], graph.items⟩ = some (.waves waves)) :
    ∀ name, ¬ Relation.TransGen graph.Uses name name := by
  have equal := rounds_schedule graph unique
  rw [checked] at equal
  have scheduled : graph.schedule graph.items = .waves waves := (Option.some.inj equal).symm
  have spec := graph.schedule_spec graph.items
  rw [scheduled] at spec
  exact spec.2.1.acyclic (fun name present => (spec.1 name).mpr present)

theorem sufficient_bound_never_exhausted (graph : Catalogue Name) (fuel : Nat) (plan : Catalogue.Plan Name)
    (enough : plan.remaining.length ≤ fuel) : rounds graph fuel plan ≠ none := by
  rw [rounds_agrees graph fuel plan enough]
  simp

end BoundedWaves
end Mettapedia.Algorithms.Compression.LayeredSource
