import Mettapedia.Algorithms.MonotoneRankEnumeration
import Mathlib.Data.List.Perm.Basic

/-!
# Certificates for ranked source prefixes

A prefix retains distinct source identities in nondecreasing cost order.
An omitted source member certifies a full requested prefix whose entries
are no dearer. Search allowance and requested size are separate: a fresh
slice certifies the smaller of those two quotas, or exhausts the source.
The source is graph reachability, independently of the extraction algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.DerivationPrefix

open MonotoneRankEnumeration

variable {Value : Type*}

structure Correct (requested : Nat) (cost : Value → Nat) (source : Value → Prop)
    (cached : List Value) : Prop where
  distinct : cached.Nodup
  sound : ∀ value ∈ cached, source value
  ordered : cached.Pairwise (fun first second => cost first ≤ cost second)
  bounded : cached.length ≤ requested
  omitted : ∀ value, source value → value ∉ cached →
    cached.length = requested ∧ ∀ selected ∈ cached, cost selected ≤ cost value

theorem zero_correct (cost : Value → Nat) (source : Value → Prop) :
    Correct 0 cost source [] := by
  constructor <;> simp

theorem empty_correct (requested : Nat) (cost : Value → Nat) (source : Value → Prop)
    (empty : ∀ value, ¬ source value) : Correct requested cost source [] := by
  constructor <;> simp_all

theorem member_or_full (requested : Nat) (cost : Value → Nat) (source : Value → Prop)
    (cached : List Value) (valid : Correct requested cost source cached)
    {value : Value} (allowed : source value) :
    value ∈ cached ∨ cached.length = requested := by
  classical
  exact or_iff_not_imp_left.mpr fun absent => (valid.omitted value allowed absent).1

theorem cheap_member (requested : Nat) (positive : 0 < requested)
    (cost : Value → Nat) (source : Value → Prop) (cached : List Value)
    (valid : Correct requested cost source cached) {value : Value} (allowed : source value) :
    ∃ selected ∈ cached, cost selected ≤ cost value := by
  classical
  by_cases member : value ∈ cached
  · exact ⟨value, member, le_rfl⟩
  · have full := valid.omitted value allowed member
    cases cached with
    | nil => simp only [List.length_nil] at full; omega
    | cons first rest => exact ⟨first, List.mem_cons_self, full.2 first List.mem_cons_self⟩

/-- Equivalent source predicates leave the supplied prefix and its costs intact. -/
theorem Correct.congr_source {requested : Nat} {cost : Value → Nat}
    {source target : Value → Prop} {cached : List Value}
    (valid : Correct requested cost source cached) (same : ∀ value, source value ↔ target value) :
    Correct requested cost target cached :=
  { valid with
    sound := fun value member => (same value).1 (valid.sound value member)
    omitted := fun value allowed absent => valid.omitted value ((same value).2 allowed) absent }

/-- A short certified prefix contains every source member. -/
theorem Correct.full_or_exhaustive {requested : Nat} {cost : Value → Nat}
    {source : Value → Prop} {cached : List Value} (valid : Correct requested cost source cached) :
    cached.length = requested ∨ ∀ value, source value → value ∈ cached := by
  classical
  exact or_iff_not_imp_left.mpr fun short value allowed => by
    by_contra absent
    exact short (valid.omitted value allowed absent).1

/-- Reconstruction needs injectivity on authorized source values. This
permits merging physically disjoint family caches without imposing an
irrelevant injectivity condition on malformed trees. -/
theorem map_correct_on {Other : Type*} (requested : Nat)
    (cost : Value → Nat) (otherCost : Other → Nat) (source : Value → Prop)
    (cached : List Value) (valid : Correct requested cost source cached)
    (reconstruct : Value → Other)
    (faithful : ∀ first, source first → ∀ second, source second →
      reconstruct first = reconstruct second → first = second)
    (sameCost : ∀ value, otherCost (reconstruct value) = cost value) :
    Correct requested otherCost
      (fun other => ∃ value, source value ∧ reconstruct value = other)
      (cached.map reconstruct) := by
  classical
  refine ⟨?_, ?_, ?_, by simpa using valid.bounded, ?_⟩
  · exact valid.distinct.map_on fun first presentFirst second presentSecond same =>
      faithful first (valid.sound first presentFirst) second (valid.sound second presentSecond) same
  · intro other member
    obtain ⟨value, present, same⟩ := List.mem_map.mp member
    exact ⟨value, valid.sound value present, same⟩
  · simpa only [List.pairwise_map, sameCost] using valid.ordered
  · intro other allowed omitted
    obtain ⟨value, permitted, same⟩ := allowed
    subst other
    have absent : value ∉ cached := fun member =>
      omitted (List.mem_map.mpr ⟨value, member, rfl⟩)
    have full := valid.omitted value permitted absent
    refine ⟨by simpa using full.1, ?_⟩
    intro selected member
    obtain ⟨original, present, equal⟩ := List.mem_map.mp member
    subst selected
    simpa only [sameCost] using full.2 original present

/-- Injective reconstruction changes representation without identifying
distinct derivations. The cost equality is checked separately. -/
theorem map_correct {Other : Type*} (requested : Nat)
    (cost : Value → Nat) (otherCost : Other → Nat) (source : Value → Prop)
    (cached : List Value) (valid : Correct requested cost source cached)
    (reconstruct : Value → Other) (faithful : Function.Injective reconstruct)
    (sameCost : ∀ value, otherCost (reconstruct value) = cost value) :
    Correct requested otherCost
      (fun other => ∃ value, source value ∧ reconstruct value = other)
      (cached.map reconstruct) := by
  exact map_correct_on requested cost otherCost source cached valid reconstruct
    (fun first _ second _ same => faithful same) sameCost

/-- Injective reconstruction transports an actual list of cheap witnesses. -/
theorem mapped_witnesses {Other : Type*} (requested : Nat) (cost : Other → Nat)
    (retained : Other → Prop) (bound : Nat) (values : List Value)
    (distinct : values.Nodup) (count : values.length = requested)
    (reconstruct : Value → Other) (faithful : Function.Injective reconstruct)
    (sound : ∀ value ∈ values, retained (reconstruct value))
    (cheap : ∀ value ∈ values, cost (reconstruct value) ≤ bound) :
    ∃ witnesses : List Other, witnesses.Nodup ∧ witnesses.length = requested ∧
      (∀ witness ∈ witnesses, retained witness) ∧ ∀ witness ∈ witnesses, cost witness ≤ bound :=
  ⟨values.map reconstruct, distinct.map faithful, by simpa using count,
    by simpa only [List.forall_mem_map] using sound, by simpa only [List.forall_mem_map] using cheap⟩

/-- Erasing an alternative tag is faithful on disjoint authorized sources,
even though the same erasure identifies malformed values outside them. -/
theorem sum_merge_injective_on (source : Value ⊕ Value → Prop)
    (disjoint : ∀ value, source (.inl value) → ¬ source (.inr value)) :
    ∀ first, source first → ∀ second, source second →
      Sum.elim id id first = Sum.elim id id second → first = second := by
  rintro (a | a) ha (b | b) hb same <;> simp_all

/-- A finite coordinate chain is reachable from its authored first position. -/
theorem source_of_fin_chain {Node : Type} {count : Nat} (graph : Graph Node) (roots : List Node)
    (point : Fin count → Node) (root : ∀ h : 0 < count, point ⟨0, h⟩ ∈ roots)
    (step : ∀ index (h : index + 1 < count),
      point ⟨index + 1, h⟩ ∈ graph.neighbors (point ⟨index, by omega⟩))
    (index : Fin count) : Source graph roots (point index) := by
  obtain ⟨index, within⟩ := index
  induction index with
  | zero => exact .root (root within)
  | succ index ih => exact .successor (ih (by omega)) (step index within)

/-- Each successful rank step publishes exactly one identity. The account
includes the retained prefix, so pausing does not reset its length. -/
theorem demand_published_length {Node : Type} [DecidableEq Node]
    (graph : Graph Node) (requested allowance : Nat) (state : State Node) :
    ((demandMachine graph requested).runSlice allowance state).1.published.length =
      state.published.length + ((demandMachine graph requested).runSlice allowance state).2 := by
  induction allowance generalizing state with
  | zero => simp [Mettapedia.Machines.MachineCore.runSlice]
  | succ allowance ih =>
      by_cases progress : state.published.length < requested ∧ state.frontier ≠ []
      · simp only [Mettapedia.Machines.MachineCore.runSlice, demandMachine, if_pos progress]
        change ((demandMachine graph requested).runSlice allowance (tick graph state)).1.published.length =
          state.published.length + (((demandMachine graph requested).runSlice allowance
            (tick graph state)).2 + 1)
        rw [ih, tick_publishes_one graph state progress.2]
        omega
      · simp [Mettapedia.Machines.MachineCore.runSlice, demandMachine, progress]

/-- Every fresh slice is a certified best prefix for its effective quota.
A result shorter than that quota exhausts the independently defined source. -/
theorem demand_prefix_correct {Node : Type} [DecidableEq Node]
    (graph : Graph Node) (increasing : MonotoneRankEnumeration.Monotone graph)
    (roots : List Node) (requested allowance : Nat) :
    Correct (min requested allowance) graph.cost (Source graph roots)
      ((demandMachine graph requested).runSlice allowance (initial roots)).1.published := by
  let result := (demandMachine graph requested).runSlice allowance (initial roots)
  have projection := congrArg Prod.fst (demand_is_prefix graph requested allowance (initial roots))
  change result.1 = run graph result.2 (initial roots) at projection
  have valid : Invariant graph roots result.1 := by
    rw [projection]; exact run_invariant graph roots _ _ (initial_invariant graph roots)
  have best : BestPrefix graph roots result.1.published := by
    rw [projection]; exact run_best graph increasing roots _
  have count := demand_published_length graph requested allowance (initial roots)
  change result.1.published.length = 0 + result.2 at count
  have used := Mettapedia.Machines.MachineCore.runSlice_used_le
    (demandMachine graph requested) allowance (initial roots)
  have within := demand_no_overshoot graph requested allowance (initial roots) (by simp [initial])
  change result.2 ≤ allowance at used
  change result.1.published.length ≤ requested at within
  have bounded : result.1.published.length ≤ min requested allowance := by omega
  refine ⟨(List.nodup_append.mp valid.distinct).1,
    fun node member => valid.sound node (List.mem_append.mpr (Or.inl member)), best.1, bounded, ?_⟩
  intro node source absent
  have live : result.1.frontier ≠ [] := fun closed =>
    absent ((closed_complete graph increasing roots result.1 valid closed node).2 source)
  refine ⟨?_, fun selected member => best.2 selected member node source absent⟩
  change result.1.published.length = min requested allowance
  by_cases full : result.1.published.length = requested
  · omega
  · have spent := demand_open_unsatisfied_spent graph requested allowance (initial roots)
      live (by change result.1.published.length < requested; omega)
    change result.2 = allowance at spent
    omega

theorem graph_prefix_correct {Node : Type} [DecidableEq Node]
    (graph : MonotoneRankEnumeration.Graph Node)
    (increasing : MonotoneRankEnumeration.Monotone graph) (roots : List Node)
    (allReachable : ∀ node, MonotoneRankEnumeration.Source graph roots node)
    (requested : Nat) :
    Correct requested graph.cost (fun _ => True)
      ((MonotoneRankEnumeration.demandMachine graph requested).runSlice requested
        (MonotoneRankEnumeration.initial roots)).1.published := by
  simpa only [Nat.min_self] using
    (demand_prefix_correct graph increasing roots requested requested).congr_source
      (fun node => ⟨fun _ => trivial, fun _ => allReachable node⟩)

end Mettapedia.Algorithms.DerivationPrefix
