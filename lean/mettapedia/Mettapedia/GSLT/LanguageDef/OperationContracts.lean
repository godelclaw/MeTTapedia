import Mettapedia.GSLT.LanguageDef.LayoutDeclarations
import Mettapedia.Machines.TraceObservationBoundary
import Mettapedia.GSLT.Contracts.AuthorityControls
import Mettapedia.GSLT.Core.ResourceAwareControl
import Mettapedia.GSLT.LanguageDef.ExportCounterTables

/-!
# Operation contracts

A native operation's contract declares, once, the facts a runtime otherwise
writes in many places: its call forms and the demand and ownership of each
argument, the footprint of its head (the resources it reads and writes), the
context it needs (blocking, branching, progress, cost charges), the columns a
runtime keeps for other reasons (static dispatch, type-level conversion,
speculation, replay) and the profiles it belongs to.

**Footprints.** A footprint is what the resource frontier of
`Machines.TraceObservationBoundary` sees: a write consumes and produces its
resource, a read reads it. Two results connect the existing models:
- `independent_iff`: the Boolean checker is the frontier's `Independent`;
- `independent_iff_separate`: two footprints are independent exactly when, at
  every resource, the two operations' `Access` rights
  (`GSLT.Contracts.AuthorityControls`) are separate.

**Conformance.** That a C handler touches only what its contract declares is
not proved here. `Conforms` states it for a concrete footprint through an
abstraction of concrete resources to declared ones. Under that hypothesis,
`concrete_independent` and `receipt_view_swap_of_declared` give the concrete
operations the commuting dependency views of `receipt_view_swap`.

**What independence does not give.** `independence_does_not_order_streams`:
two operations with independent footprints can still be told apart by an
ordered-stream observer (`ResourceAwareControl`), so a parallel admission
built on footprints needs a separate certificate for ordered output.

**Worker placement contribution.** `query_row_requires_coordinator` connects a
derived nonzero query row to coordinator placement advice. Unknown footprints
stay `unresolved`, never silently local. This is only the effect contribution:
current authority, progress/yield and ordered-output permission remain
separate obligations.

**Declared tables.** `tableOk` is the decidable check of a declared table;
`admitted_laws` states what it guarantees.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OperationContracts

open Mettapedia.Machines.CausalReceipt
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

/-! ## Footprints -/

/-- The resources an operation's head reads and writes. -/
structure Footprint (Resource : Type*) where
  reads : List Resource
  writes : List Resource
deriving DecidableEq, Repr

variable {Resource : Type*} [DecidableEq Resource]

namespace Footprint

/-- The operation's right to one resource. -/
def access (f : Footprint Resource) (r : Resource) : Access :=
  if r ∈ f.writes then .consume else if r ∈ f.reads then .read else .none

/-- No written resource of either operation is accessed by the other. -/
def independent (a b : Footprint Resource) : Bool :=
  a.writes.all (fun r => !(decide (r ∈ b.writes) || decide (r ∈ b.reads))) &&
    b.writes.all (fun r => !(decide (r ∈ a.writes) || decide (r ∈ a.reads)))

def pure (f : Footprint Resource) : Bool := f.reads.isEmpty && f.writes.isEmpty

theorem independent_symm (a b : Footprint Resource) : independent a b = independent b a := by
  unfold independent
  exact Bool.and_comm _ _

/-- The checker is the resource frontier's independence, with a write
consuming and producing its resource. -/
theorem independent_iff (a b : Footprint Resource) :
    independent a b = true ↔
      ResourceFrontier.Independent a.writes a.reads a.writes b.writes b.reads b.writes := by
  unfold independent ResourceFrontier.Independent
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨?_, ?_⟩
    · intro r hr hr'
      have hw : r ∈ a.writes := by simpa using hr
      have := ha r hw
      simp only [List.mem_append] at hr'
      tauto
    · intro r hr hr'
      have hw : r ∈ b.writes := by simpa using hr
      have := hb r hw
      simp only [List.mem_append] at hr'
      tauto
  · rintro ⟨h1, h2⟩
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · have := List.disjoint_left.mp h1 (List.mem_append.mpr (Or.inl hr))
      simp only [List.mem_append, not_or] at this
      exact ⟨this.1.1, this.1.2⟩
    · have := List.disjoint_left.mp h2 (List.mem_append.mpr (Or.inl hr))
      simp only [List.mem_append, not_or] at this
      exact ⟨this.1.1, this.1.2⟩

/-- Two footprints are independent exactly when the two operations' rights
are separate at every resource: reads share, a consume excludes everything. -/
theorem independent_iff_separate (a b : Footprint Resource) :
    independent a b = true ↔ ∀ r, access a r ## access b r := by
  unfold independent
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨ha, hb⟩ r
    show Access.separate (access a r) (access b r) = true
    unfold access
    by_cases aw : r ∈ a.writes
    · have := ha r aw
      simp [aw, this.1, this.2, Access.separate]
    · by_cases bw : r ∈ b.writes
      · have := hb r bw
        simp [aw, bw, this.2, Access.separate]
      · by_cases ar : r ∈ a.reads <;> by_cases br : r ∈ b.reads <;>
          simp [aw, bw, ar, br, Access.separate]
  · intro h
    have sep : ∀ r, Access.separate (access a r) (access b r) = true := h
    refine ⟨fun r aw => ?_, fun r bw => ?_⟩
    · have := sep r
      unfold access at this
      by_cases bw : r ∈ b.writes
      · simp [aw, bw, Access.separate] at this
      · by_cases br : r ∈ b.reads
        · simp [aw, bw, br, Access.separate] at this
        · exact ⟨bw, br⟩
    · have := sep r
      unfold access at this
      by_cases aw : r ∈ a.writes
      · simp [aw, bw, Access.separate] at this
      · by_cases ar : r ∈ a.reads
        · simp [aw, bw, ar, Access.separate] at this
        · exact ⟨aw, ar⟩

/-- An operation that reads and writes nothing is independent of every operation. -/
theorem pure_independent {a : Footprint Resource} (h : pure a = true) (b : Footprint Resource) :
    independent a b = true := by
  unfold pure at h
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h
  unfold independent
  simp [h.1, h.2]

end Footprint

/-! ## Conformance: concrete footprints within declared ones -/

/-- A concrete footprint over `Concrete` resources conforms to a declared one
when the abstraction of each resource it writes is declared written, and of
each resource it reads is declared read or written. This is the hypothesis a
C handler must meet; it is tested, never proved, for C. -/
def Conforms {Concrete : Type*} (abstract : Concrete → Resource)
    (concrete : Footprint Concrete) (declared : Footprint Resource) : Prop :=
  (∀ c ∈ concrete.writes, abstract c ∈ declared.writes) ∧
  (∀ c ∈ concrete.reads, abstract c ∈ declared.reads ∨ abstract c ∈ declared.writes)

/-- Independence of declared footprints carries to conforming concrete ones. -/
theorem concrete_independent {Concrete : Type*} [DecidableEq Concrete] (abstract : Concrete → Resource)
    {ca cb : Footprint Concrete} {da db : Footprint Resource}
    (conformA : Conforms abstract ca da) (conformB : Conforms abstract cb db)
    (declared : Footprint.independent da db = true) :
    ResourceFrontier.Independent ca.writes ca.reads ca.writes cb.writes cb.reads cb.writes := by
  rw [← Footprint.independent_iff]
  unfold Footprint.independent at declared ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    decide_eq_false_iff_not] at declared ⊢
  obtain ⟨da_ok, db_ok⟩ := declared
  refine ⟨fun c cw => ⟨fun cbw => ?_, fun cbr => ?_⟩, fun c cw => ⟨fun caw => ?_, fun car => ?_⟩⟩
  · exact (da_ok _ (conformA.1 c cw)).1 (conformB.1 c cbw)
  · rcases conformB.2 c cbr with h | h
    · exact (da_ok _ (conformA.1 c cw)).2 h
    · exact (da_ok _ (conformA.1 c cw)).1 h
  · exact (db_ok _ (conformB.1 c cw)).1 (conformA.1 c caw)
  · rcases conformA.2 c car with h | h
    · exact (db_ok _ (conformB.1 c cw)).2 h
    · exact (db_ok _ (conformB.1 c cw)).1 h

/-- Operations whose concrete footprints conform to independent declared
footprints have the same causal dependency view in either order, inside any
history. -/
theorem receipt_view_swap_of_declared {Action Identity Concrete : Type*} [DecidableEq Concrete]
    [DecidableEq Identity] (abstract : Concrete → Resource) (identity : Action → Identity)
    (concrete : Action → Footprint Concrete) (declared : Action → Footprint Resource)
    (conform : ∀ x, Conforms abstract (concrete x) (declared x))
    (earlier suffix : List Action) (left right : Action)
    (independent : Footprint.independent (declared left) (declared right) = true) :
    (ResourceFrontier.receipt identity (fun x => (concrete x).writes) (fun x => (concrete x).reads)
        (fun x => (concrete x).writes) (earlier ++ left :: right :: suffix)).dependencyView =
      (ResourceFrontier.receipt identity (fun x => (concrete x).writes) (fun x => (concrete x).reads)
        (fun x => (concrete x).writes) (earlier ++ right :: left :: suffix)).dependencyView :=
  ResourceFrontier.receipt_view_swap identity (fun x => (concrete x).writes) (fun x => (concrete x).reads)
    (fun x => (concrete x).writes) earlier suffix left right
    (concrete_independent abstract (conform left) (conform right) independent)

/-! ## What independence does not give -/

section Canary

open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Core.ResourceAwareControl.Canary

/-- A job of the resource-aware canary writes the tokens it demands. -/
def jobFootprint : Job → Footprint Token
  | .left => ⟨[], [.first]⟩
  | .right => ⟨[], [.second]⟩
  | .contested => ⟨[], [.first]⟩

theorem jobFootprint_writes (j : Job) : ((jobFootprint j).writes : Multiset Token) = demand j := by
  cases j <;> rfl

/-- Footprint independence admits the two jobs, yet an ordered-stream
observer tells their orders apart: ordered output needs its own certificate. -/
theorem independence_does_not_order_streams :
    Footprint.independent (jobFootprint .left) (jobFootprint .right) = true ∧
      Not (appendStreamSemantics.SerializesTo [] [.left, .right] [.left, .right]) :=
  ⟨by decide, resources_do_not_grant_stream_serializability.2⟩

/-- The contested job conflicts with the left one, as the canary's inventory says. -/
theorem contested_not_independent :
    Footprint.independent (jobFootprint .left) (jobFootprint .contested) = false := by decide

end Canary

/-! ## Declared contracts, as Cesta prints them

The vocabulary record names the resources (each a `"store"` a query observes,
or `"scratch"`), the cost charges and the profiles a table may use:

    (cesta-operation-vocabulary/1 NAME (Resources (R "store"|"scratch") …)
      (Charges C …) (Profiles P …))

An operation record:

    (cesta-operation/1 NAME "SPELLING" SYMBOL (Dispatch D)
      (Forms (Form (Arg EVALUATION DEMAND OWNERSHIP) …) …)
      (Footprint (Reads R …) (Writes R …)) | (Footprint "unknown")
      (Context BLOCKS BRANCHES PROGRESS (Charges C …))
      (Result RESULT)
      (Declared STATIC TYPE-PURE SPECULATIVE (Replay REPLAY) (Through N …))
      (Profiles P …))

A fact no one has established is written `"unknown"`; it is never read as a
default. In particular an unknown footprint is not an empty one. An empty
`(Forms)` leaves the arity unknown, and an empty `(Profiles)` the profiles.
-/

open Mettapedia.GSLT.LanguageDef.MacroExportPlan (Atom)
open Mettapedia.GSLT.LanguageDef.LayoutDeclarations (number)

structure Arg where
  evaluation : String
  demand : String
  ownership : String
deriving DecidableEq, Repr

structure Operation where
  name : String
  spelling : String
  symbol : String
  dispatch : String
  forms : List (List Arg)
  footprint : Option (Footprint String)
  blocks : Option Bool
  branches : Option Bool
  progress : String
  charges : List String
  result : String
  static : Bool
  typePure : Bool
  speculative : Bool
  replay : String
  through : List Nat
  profiles : List String
deriving DecidableEq, Repr

structure Vocabulary where
  name : String
  resources : List (String × String)
  charges : List String
  profiles : List String
deriving DecidableEq, Repr

def symbolOf : Atom → Option String
  | .symbol s => some s
  | _ => none

def yesNo : Atom → Option Bool
  | .text "yes" => some true
  | .text "no" => some false
  | _ => none

/-- `"yes"`, `"no"` or `"unknown"`. -/
def known : Atom → Option (Option Bool)
  | .text "unknown" => some none
  | a => (yesNo a).map some

def decodeArg : Atom → Option Arg
  | .list [.symbol "Arg", .text e, .text d, .text o] => some ⟨e, d, o⟩
  | _ => none

def decodeForm : Atom → Option (List Arg)
  | .list (.symbol "Form" :: args) => args.mapM decodeArg
  | _ => none

def decodeNames (head : String) : Atom → Option (List String)
  | .list (.symbol h :: names) => if h = head then names.mapM symbolOf else none
  | _ => none

def decodeFootprint : Atom → Option (Option (Footprint String))
  | .list [.symbol "Footprint", .text "unknown"] => some none
  | .list [.symbol "Footprint", reads, writes] => do
      pure (some ⟨← decodeNames "Reads" reads, ← decodeNames "Writes" writes⟩)
  | _ => none

def decodeResource : Atom → Option (String × String)
  | .list [.symbol r, .text kind] => some (r, kind)
  | _ => none

def decodeOperation : Atom → Option Operation
  | .list [.symbol "cesta-operation/1", .symbol name, .text spelling, .symbol symbol,
      .list [.symbol "Dispatch", .text dispatch],
      .list (.symbol "Forms" :: forms), footprint,
      .list [.symbol "Context", blocks, branches, .text progress, charges],
      .list [.symbol "Result", .text result],
      .list [.symbol "Declared", static, typePure, speculative, .list [.symbol "Replay", .text replay],
        .list (.symbol "Through" :: through)],
      profiles] => do
      pure ⟨name, spelling, symbol, dispatch, ← forms.mapM decodeForm, ← decodeFootprint footprint,
        ← known blocks, ← known branches, progress, ← decodeNames "Charges" charges, result,
        ← yesNo static, ← yesNo typePure, ← yesNo speculative, replay, ← through.mapM number,
        ← decodeNames "Profiles" profiles⟩
  | _ => none

def decodeVocabulary : Atom → Option Vocabulary
  | .list [.symbol "cesta-operation-vocabulary/1", .symbol name, .list (.symbol "Resources" :: resources),
      charges, profiles] => do
      pure ⟨name, ← resources.mapM decodeResource, ← decodeNames "Charges" charges,
        ← decodeNames "Profiles" profiles⟩
  | _ => none

/-! ## The laws of a declared table -/

def dispatches : List String := ["grounded", "control", "special", "unknown"]
def evaluations : List String := ["value", "atom", "unknown"]
def demands : List String := ["data", "whnf", "source-type", "shape", "value", "structure", "pattern", "unknown"]
def ownerships : List String := ["borrow", "consume", "unknown"]
def progresses : List String := ["single", "bounded", "steps", "suspends", "unknown"]
def results : List String := ["fresh", "shared", "borrowed", "unknown"]
def replays : List String := ["transparent", "refused"]

def argOk (a : Arg) : Bool :=
  evaluations.contains a.evaluation && demands.contains a.demand && ownerships.contains a.ownership

def Operation.arities (op : Operation) : List Nat := op.forms.map List.length

/-- The footprint is known to be empty. -/
def Operation.knownPure (op : Operation) : Bool :=
  match op.footprint with
  | some f => f.pure
  | none => false

/-- A grounded value operation whose footprint is known to be empty: the
runtime's list of operations audited free of ambient observation and mutation. -/
def Operation.pureRow (op : Operation) : Bool := op.dispatch == "grounded" && op.knownPure

/-- Admitted under speculation: by the pure list, or by its declared column. -/
def Operation.speculates (op : Operation) : Bool := op.pureRow || op.speculative

def Vocabulary.resourceNames (v : Vocabulary) : List String := v.resources.map Prod.fst

def Vocabulary.stores (v : Vocabulary) : List String :=
  (v.resources.filter fun r => r.2 = "store").map Prod.fst

def formsOk (op : Operation) : Bool :=
  dispatches.contains op.dispatch && op.forms.all (fun f => f.all argOk) && op.arities.Nodup

def footprintOk (v : Vocabulary) (op : Operation) : Bool :=
  match op.footprint with
  | some f => f.reads.Nodup && f.writes.Nodup && (f.reads ++ f.writes).all v.resourceNames.contains
  | none => true

def contextOk (v : Vocabulary) (op : Operation) : Bool :=
  progresses.contains op.progress && op.charges.Nodup && op.charges.all v.charges.contains

def declaredOk (op : Operation) : Bool :=
  results.contains op.result && replays.contains op.replay && op.through.all op.arities.contains

def profilesOk (v : Vocabulary) (op : Operation) : Bool :=
  op.profiles.Nodup && op.profiles.all v.profiles.contains

/-- A type-level licence never goes with a declared read or write, or with
branching or blocking. -/
def typePureOk (op : Operation) : Bool :=
  !op.typePure ||
    ((match op.footprint with | some f => f.pure | none => true) &&
      op.branches != some true && op.blocks != some true)

/-- The pure list is part of the type-level licence. -/
def pureTypeOk (op : Operation) : Bool := !op.pureRow || op.typePure

/-- No operation known to write is admitted under speculation. -/
def writerOk (op : Operation) : Bool :=
  match op.footprint with
  | some f => f.writes.isEmpty || !op.speculates
  | none => true

def operationOk (v : Vocabulary) (op : Operation) : Bool :=
  formsOk op && footprintOk v op && contextOk v op && declaredOk op && profilesOk v op &&
    typePureOk op && pureTypeOk op && writerOk op

def vocabularyOk (v : Vocabulary) : Bool :=
  v.resourceNames.Nodup && v.resources.all (fun r => ["store", "scratch"].contains r.2) &&
    v.charges.Nodup && v.profiles.Nodup

def tableOk (v : Vocabulary) (ops : List Operation) : Bool :=
  vocabularyOk v && (ops.map Operation.name).Nodup && (ops.map Operation.spelling).Nodup &&
    (ops.map Operation.symbol).Nodup && ops.all (operationOk v)

/-- The query effect a known footprint derives: the write bit for an
operation that writes a store, else the read bit for one that reads a store,
else pure. An unknown footprint derives none. -/
def queryEffect (v : Vocabulary) (op : Operation) : Option Nat :=
  op.footprint.map fun f =>
    if f.writes.any v.stores.contains then 2
    else if f.reads.any v.stores.contains then 1 else 0

/-! ### Effect-only worker placement advice

This is the contribution of the declared store footprint to worker placement,
not full admission. `local` still requires current authority, a suitable
progress/yield contract and permission to reorder any ordered observations.
`coordinator` says only that the store effect crosses this worker boundary.
`unresolved` preserves an unknown footprint as unknown. Handler conformance to
the declaration remains the separate `Conforms` obligation above. -/

inductive WorkerPlacementAdvice where
  | local
  | coordinator
  | unresolved
deriving DecidableEq, Repr

def workerPlacementAdvice (v : Vocabulary) (op : Operation) : WorkerPlacementAdvice :=
  match queryEffect v op with
  | none => .unresolved
  | some 0 => .local
  | some (_ + 1) => .coordinator

theorem workerPlacementAdvice_nonzero (v : Vocabulary) {op : Operation} {effect : Nat}
    (known : queryEffect v op = some effect) (nonzero : effect ≠ 0) :
    workerPlacementAdvice v op = .coordinator := by
  cases effect with
  | zero => contradiction
  | succ effect => simp [workerPlacementAdvice, known]

theorem workerPlacementAdvice_unresolved_iff (v : Vocabulary) (op : Operation) :
    workerPlacementAdvice v op = .unresolved ↔ op.footprint = none := by
  cases footprint : op.footprint with
  | none => simp [workerPlacementAdvice, queryEffect, footprint]
  | some value =>
      cases actual : queryEffect v op with
      | none => simp [queryEffect, footprint] at actual
      | some effect =>
          constructor
          · intro advice
            unfold workerPlacementAdvice at advice
            rw [actual] at advice
            cases effect <;> simp at advice
          · intro impossible; cases impossible

/-- What `tableOk` guarantees of each operation of the table. -/
structure Laws (v : Vocabulary) (op : Operation) : Prop where
  declared : ∀ f, op.footprint = some f → ∀ r ∈ f.reads ++ f.writes, r ∈ v.resourceNames
  typePure : op.typePure = true → (∀ f, op.footprint = some f → f.pure = true) ∧
    op.branches ≠ some true ∧ op.blocks ≠ some true
  pureType : op.pureRow = true → op.typePure = true
  writers : ∀ f, op.footprint = some f → f.writes ≠ [] → op.speculates = false
  forms : op.arities.Nodup
  through : ∀ n ∈ op.through, n ∈ op.arities

theorem laws_of_operationOk {v : Vocabulary} {op : Operation} (h : operationOk v op = true) : Laws v op := by
  simp only [operationOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hf, hfp⟩, _⟩, hd⟩, _⟩, ht⟩, hpt⟩, hw⟩ := h
  simp only [formsOk, Bool.and_eq_true, decide_eq_true_eq] at hf
  simp only [declaredOk, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hd
  refine ⟨fun f hfoot r hr => ?_, fun htp => ?_, fun hp => ?_, fun f hfoot hwr => ?_, hf.2,
    fun n hn => hd.2 n hn⟩
  · simp only [footprintOk, hfoot, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hfp
    exact hfp.2 r hr
  · simp only [typePureOk, htp, Bool.not_true, Bool.false_or, Bool.and_eq_true, bne_iff_ne, ne_eq] at ht
    refine ⟨fun f hfoot => ?_, ht.1.2, ht.2⟩
    have := ht.1.1
    rw [hfoot] at this
    exact this
  · simpa [pureTypeOk, hp] using hpt
  · simp only [writerOk, hfoot, Bool.or_eq_true, List.isEmpty_iff, Bool.not_eq_true'] at hw
    exact hw.resolve_left hwr

/-- Every operation of an admitted table keeps the laws. -/
theorem admitted_laws {v : Vocabulary} {ops : List Operation} (h : tableOk v ops = true) :
    ∀ op ∈ ops, Laws v op := by
  unfold tableOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact fun op hop => laws_of_operationOk (h.2 op hop)

/-- An operation on the pure list commutes with every operation of known footprint. -/
theorem pureRow_independent {a : Operation} (h : a.pureRow = true) {fa : Footprint String}
    (ha : a.footprint = some fa) (fb : Footprint String) : Footprint.independent fa fb = true := by
  unfold Operation.pureRow Operation.knownPure at h
  rw [ha] at h
  simp only [Bool.and_eq_true] at h
  exact Footprint.pure_independent h.2 fb

/-- An effect-free operation's derived query effect is pure. -/
theorem queryEffect_pure (v : Vocabulary) {op : Operation} {f : Footprint String} (hf : op.footprint = some f)
    (h : f.pure = true) : queryEffect v op = some 0 := by
  unfold Footprint.pure at h
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h
  simp [queryEffect, hf, h.1, h.2]

theorem workerPlacementAdvice_pure (v : Vocabulary) {op : Operation}
    {f : Footprint String} (hf : op.footprint = some f) (pure : f.pure = true) :
    workerPlacementAdvice v op = .local := by
  rw [workerPlacementAdvice, queryEffect_pure v hf pure]

/-- A known writer of a store gets the write bit, whatever it reads. -/
theorem queryEffect_writer (v : Vocabulary) {op : Operation} {f : Footprint String} (hf : op.footprint = some f)
    {r : String} (hr : r ∈ f.writes) (hs : r ∈ v.stores) : queryEffect v op = some 2 := by
  have : f.writes.any v.stores.contains = true := List.any_eq_true.mpr ⟨r, hr, by simpa using hs⟩
  simp only [queryEffect, hf, Option.map_some, this, if_true]

/-- An unknown footprint derives no query effect: it is never read as pure. -/
theorem queryEffect_unknown (v : Vocabulary) {op : Operation} (h : op.footprint = none) :
    queryEffect v op = none := by
  simp [queryEffect, h]

/-! ## Derived rows -/

/-- The lists and rows a runtime keeps, derived from the table. -/
structure Rows where
  static : List String
  pure : List String
  typePure : List String
  speculative : List String
  query : List (String × Nat)
  unknown : List String
deriving DecidableEq, Repr

/-- The type-level and speculative lists hold the operations beyond the pure
list, which the runtime adds to both. -/
def lowerRows (v : Vocabulary) (ops : List Operation) : Rows where
  static := (ops.filter Operation.static).map Operation.symbol
  pure := (ops.filter Operation.pureRow).map Operation.symbol
  typePure := (ops.filter fun op => op.typePure && !op.pureRow).map Operation.symbol
  speculative := (ops.filter fun op => op.speculative && !op.pureRow).map Operation.symbol
  query := ops.filterMap fun op =>
    match queryEffect v op with
    | some 0 => none
    | some e => some (op.symbol, e)
    | none => none
  unknown := (ops.filter fun op => op.footprint.isNone).map Operation.symbol

/-- A derived query row carries an operation's derived, nonzero effect. -/
theorem query_row_spec {v : Vocabulary} {ops : List Operation} {s : String} {e : Nat}
    (h : (s, e) ∈ (lowerRows v ops).query) :
    ∃ op ∈ ops, op.symbol = s ∧ queryEffect v op = some e ∧ e ≠ 0 := by
  simp only [lowerRows, List.mem_filterMap] at h
  obtain ⟨op, hop, hq⟩ := h
  refine ⟨op, hop, ?_⟩
  cases he : queryEffect v op with
  | none => rw [he] at hq; simp at hq
  | some e' =>
      rw [he] at hq
      cases e' with
      | zero => simp at hq
      | succ n =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hq
          exact ⟨hq.1, by rw [hq.2], by omega⟩

/-- Every generated nonzero query row contributes coordinator placement.
This theorem does not provide authority, progress/yield, ordered-output safety
or conformance of a native handler to its declaration. -/
theorem query_row_requires_coordinator {v : Vocabulary} {ops : List Operation}
    {symbol : String} {effect : Nat} (row : (symbol, effect) ∈ (lowerRows v ops).query) :
    ∃ op ∈ ops, op.symbol = symbol ∧ workerPlacementAdvice v op = .coordinator := by
  obtain ⟨op, member, spelling, known, nonzero⟩ := query_row_spec row
  exact ⟨op, member, spelling, workerPlacementAdvice_nonzero v known nonzero⟩

/-- Every operation the runtime admits under speculation (the pure list and
the speculative list) is not a known writer, in an admitted table. -/
theorem speculation_rows_not_writers {v : Vocabulary} {ops : List Operation} (h : tableOk v ops = true)
    {op : Operation} (hop : op ∈ ops) (hs : op.pureRow = true ∨ op.speculative = true)
    {f : Footprint String} (hf : op.footprint = some f) : f.writes = [] := by
  by_contra hw
  have := (admitted_laws h op hop).writers f hf hw
  unfold Operation.speculates at this
  rcases hs with hs | hs <;> simp [hs] at this

/-! ## Decoded tables and rows -/

def decodeTable (vocabulary : Atom) (operations : List Atom) : Option (Vocabulary × List Operation) := do
  pure (← decodeVocabulary vocabulary, ← operations.mapM decodeOperation)

/-- A printed table is admitted when it decodes and keeps its laws. -/
def tableAdmitted (vocabulary : Atom) (operations : List Atom) : Bool :=
  match decodeTable vocabulary operations with
  | some (v, ops) => tableOk v ops
  | none => false

theorem laws_of_admitted {va : Atom} {oas : List Atom} (h : tableAdmitted va oas = true) :
    ∃ v ops, decodeTable va oas = some (v, ops) ∧ tableOk v ops = true ∧ ∀ op ∈ ops, Laws v op := by
  unfold tableAdmitted at h
  cases hd : decodeTable va oas with
  | none => rw [hd] at h; simp at h
  | some p =>
      rw [hd] at h
      exact ⟨p.1, p.2, rfl, h, admitted_laws h⟩

def decodeQueryRow : Atom → Option (String × Nat)
  | .list [.symbol s, n] => do pure (s, ← number n)
  | _ => none

/-- `(cesta-operation-rows/1 (Static S …) (Pure S …) (TypePure S …) (Speculative S …)
(Query (S N) …) (Unknown S …))`, as `cesta operations rows` records them. -/
def decodeRows : Atom → Option Rows
  | .list [.symbol "cesta-operation-rows/1", static, pureRows, typePure, speculative,
      .list (.symbol "Query" :: query), unknown] => do
      pure ⟨← decodeNames "Static" static, ← decodeNames "Pure" pureRows, ← decodeNames "TypePure" typePure,
        ← decodeNames "Speculative" speculative, ← query.mapM decodeQueryRow, ← decodeNames "Unknown" unknown⟩
  | _ => none

/-- Recorded rows are admitted when the table is and they are exactly its derived rows. -/
def rowsAdmitted (vocabulary : Atom) (operations : List Atom) (rows : Atom) : Bool :=
  match decodeTable vocabulary operations, decodeRows rows with
  | some (v, ops), some r => tableOk v ops && r == lowerRows v ops
  | _, _ => false

theorem rows_of_admitted {va : Atom} {oas : List Atom} {ra : Atom} (h : rowsAdmitted va oas ra = true) :
    ∃ v ops r, decodeTable va oas = some (v, ops) ∧ decodeRows ra = some r ∧ tableOk v ops = true ∧
      r = lowerRows v ops := by
  unfold rowsAdmitted at h
  cases hd : decodeTable va oas with
  | none => rw [hd] at h; simp at h
  | some p =>
      cases hr : decodeRows ra with
      | none => rw [hd, hr] at h; simp at h
      | some r =>
          rw [hd, hr] at h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          exact ⟨p.1, p.2, r, rfl, rfl, h.1, h.2⟩

/-! ## Admission at scale

A table of hundreds of operations is decided in chunks, joined by the append
lemmas below. Names, spellings and symbols are compared through an injective
code into the natural numbers: the kernel decides distinct codes cheaply,
distinct strings expensively. -/

open Mettapedia.GSLT.LanguageDef.ExportCounterTables (Keys allDistinct allDistinct_sound)

def base : Nat := 2 ^ 32 + 1

/-- A list of characters as a numeral in `base` whose digits are the
characters' codes plus one, least significant first. -/
def code : List Char → Nat
  | [] => 0
  | c :: cs => (c.toNat + 1) + base * code cs

theorem digit_lt (c : Char) : c.toNat + 1 < base := by
  have : c.toNat < 2 ^ 32 := c.val.toNat_lt
  unfold base
  omega

theorem code_injective : ∀ {a b : List Char}, code a = code b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp only [code] at h; omega
  | _ :: _, [], h => by simp only [code] at h; omega
  | c :: cs, d :: ds, h => by
      simp only [code] at h
      have hc := digit_lt c
      have hd := digit_lt d
      have hbase : 0 < base := by unfold base; omega
      have hhead : c.toNat + 1 = d.toNat + 1 := by
        have : (c.toNat + 1 + base * code cs) % base = (d.toNat + 1 + base * code ds) % base := by rw [h]
        rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc,
          Nat.mod_eq_of_lt hd] at this
      have htail : code cs = code ds := by
        have : base * code cs = base * code ds := by omega
        exact Nat.eq_of_mul_eq_mul_left hbase this
      rw [Char.toNat_inj.mp (show c.toNat = d.toNat by omega), code_injective htail]

def strCode (s : String) : Nat := code s.toList

theorem strCode_injective {s t : String} (h : strCode s = strCode t) : s = t :=
  String.toList_injective (code_injective h)

def opCodes (op : Operation) : Nat × Nat × Nat := (strCode op.name, strCode op.spelling, strCode op.symbol)

/-- A chunk of printed operations decodes and keeps its laws; the result is the
codes of their names, spellings and symbols. -/
def chunkCodes (v : Vocabulary) (oas : List Atom) : Option (List (Nat × Nat × Nat)) :=
  (oas.mapM decodeOperation).bind fun ops => if ops.all (operationOk v) then some (ops.map opCodes) else none

theorem chunkCodes_spec {v : Vocabulary} {oas : List Atom} {cs : List (Nat × Nat × Nat)}
    (h : chunkCodes v oas = some cs) :
    ∃ ops, oas.mapM decodeOperation = some ops ∧ ops.all (operationOk v) = true ∧ cs = ops.map opCodes := by
  unfold chunkCodes at h
  cases hm : oas.mapM decodeOperation with
  | none => rw [hm] at h; simp at h
  | some ops =>
      rw [hm] at h
      simp only [Option.bind_some] at h
      split at h
      · rename_i hall
        exact ⟨ops, rfl, hall, (Option.some.inj h).symm⟩
      · simp at h

theorem chunkCodes_append {v : Vocabulary} {a b : List Atom} {x y : List (Nat × Nat × Nat)}
    (ha : chunkCodes v a = some x) (hb : chunkCodes v b = some y) : chunkCodes v (a ++ b) = some (x ++ y) := by
  obtain ⟨oa, hma, halla, rfl⟩ := chunkCodes_spec ha
  obtain ⟨ob, hmb, hallb, rfl⟩ := chunkCodes_spec hb
  have hall : (oa ++ ob).all (operationOk v) = true := by simp only [List.all_append, halla, hallb, Bool.and_self]
  have hm : (a ++ b).mapM decodeOperation = some (oa ++ ob) := by simp [List.mapM_append, hma, hmb]
  unfold chunkCodes
  rw [hm, Option.bind_some, if_pos hall, List.map_append]

/-- Chunks whose codes are distinct make an admitted table. -/
theorem tableAdmitted_of_codes {va : Atom} {oas : List Atom} {v : Vocabulary} {cs : List (Nat × Nat × Nat)}
    (hv : decodeVocabulary va = some v) (hvok : vocabularyOk v = true) (hc : chunkCodes v oas = some cs)
    (hn : allDistinct (cs.map (·.1)) .leaf = true) (hs : allDistinct (cs.map (·.2.1)) .leaf = true)
    (hy : allDistinct (cs.map (·.2.2)) .leaf = true) : tableAdmitted va oas = true := by
  obtain ⟨ops, hops, hall, rfl⟩ := chunkCodes_spec hc
  have distinct : ∀ {f : Operation → String}, (ops.map (fun op => strCode (f op))).Nodup → (ops.map f).Nodup := by
    intro f h
    have : ops.map (fun op => strCode (f op)) = (ops.map f).map strCode := by simp
    rw [this] at h
    exact List.Nodup.of_map strCode h
  have dn := (allDistinct_sound (t := .leaf) trivial hn).1
  have ds := (allDistinct_sound (t := .leaf) trivial hs).1
  have dy := (allDistinct_sound (t := .leaf) trivial hy).1
  simp only [List.map_map, Function.comp_def, opCodes] at dn ds dy
  have hd : decodeTable va oas = some (v, ops) := by simp [decodeTable, hv, hops]
  unfold tableAdmitted
  rw [hd]
  unfold tableOk
  simp only [hvok, hall, Bool.and_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨distinct dn, distinct ds⟩, distinct dy⟩

/-- The rows as codes. -/
def rowsCodes (r : Rows) : List Nat × List Nat × List Nat × List Nat × List (Nat × Nat) × List Nat :=
  (r.static.map strCode, r.pure.map strCode, r.typePure.map strCode, r.speculative.map strCode,
    r.query.map (fun q => (strCode q.1, q.2)), r.unknown.map strCode)

def appendCodes (x y : List Nat × List Nat × List Nat × List Nat × List (Nat × Nat) × List Nat) :
    List Nat × List Nat × List Nat × List Nat × List (Nat × Nat) × List Nat :=
  (x.1 ++ y.1, x.2.1 ++ y.2.1, x.2.2.1 ++ y.2.2.1, x.2.2.2.1 ++ y.2.2.2.1, x.2.2.2.2.1 ++ y.2.2.2.2.1,
    x.2.2.2.2.2 ++ y.2.2.2.2.2)

theorem lowerRows_append (v : Vocabulary) (a b : List Operation) :
    rowsCodes (lowerRows v (a ++ b)) = appendCodes (rowsCodes (lowerRows v a)) (rowsCodes (lowerRows v b)) := by
  simp [rowsCodes, lowerRows, appendCodes, List.filter_append, List.filterMap_append]

/-- A chunk's derived rows, as codes. -/
def chunkRowCodes (v : Vocabulary) (oas : List Atom) :
    Option (List Nat × List Nat × List Nat × List Nat × List (Nat × Nat) × List Nat) :=
  (oas.mapM decodeOperation).map fun ops => rowsCodes (lowerRows v ops)

theorem chunkRowCodes_append {v : Vocabulary} {a b : List Atom}
    {x y : List Nat × List Nat × List Nat × List Nat × List (Nat × Nat) × List Nat}
    (ha : chunkRowCodes v a = some x) (hb : chunkRowCodes v b = some y) :
    chunkRowCodes v (a ++ b) = some (appendCodes x y) := by
  unfold chunkRowCodes at ha hb ⊢
  cases hma : a.mapM decodeOperation with
  | none => rw [hma] at ha; simp at ha
  | some oa =>
      cases hmb : b.mapM decodeOperation with
      | none => rw [hmb] at hb; simp at hb
      | some ob =>
          rw [hma] at ha
          rw [hmb] at hb
          simp only [Option.map_some, Option.some.injEq] at ha hb
          simp [List.mapM_append, hma, hmb, lowerRows_append, ha, hb]

theorem rowsCodes_injective {r s : Rows} (h : rowsCodes r = rowsCodes s) : r = s := by
  have inj : Function.Injective strCode := fun _ _ h => strCode_injective h
  have injq : Function.Injective (fun q : String × Nat => (strCode q.1, q.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (strCode_injective h.1) h.2
  simp only [rowsCodes, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases r; cases s
  simp only [Rows.mk.injEq]
  exact ⟨List.map_injective_iff.mpr inj h1, List.map_injective_iff.mpr inj h2, List.map_injective_iff.mpr inj h3,
    List.map_injective_iff.mpr inj h4, List.map_injective_iff.mpr injq h5, List.map_injective_iff.mpr inj h6⟩

/-- Recorded rows whose codes are the chunks' derived codes are the table's derived rows. -/
theorem rowsAdmitted_of_codes {va ra : Atom} {oas : List Atom} {v : Vocabulary}
    {codes : List Nat × List Nat × List Nat × List Nat × List (Nat × Nat) × List Nat}
    (hv : decodeVocabulary va = some v) (hadm : tableAdmitted va oas = true)
    (hrows : chunkRowCodes v oas = some codes) (hrec : (decodeRows ra).map rowsCodes = some codes) :
    rowsAdmitted va oas ra = true := by
  obtain ⟨v', ops, hd, hok, _⟩ := laws_of_admitted hadm
  cases hm : oas.mapM decodeOperation with
  | none => simp [decodeTable, hv, hm] at hd
  | some ops' =>
      have heq : v = v' ∧ ops' = ops := by simpa [decodeTable, hv, hm] using hd
      obtain ⟨rfl, rfl⟩ := heq
      cases hr : decodeRows ra with
      | none => rw [hr] at hrec; simp at hrec
      | some r =>
          rw [hr] at hrec
          unfold chunkRowCodes at hrows
          rw [hm] at hrows
          simp only [Option.map_some, Option.some.injEq] at hrec hrows
          have hrv : r = lowerRows v ops' := rowsCodes_injective (hrec.trans hrows.symm)
          unfold rowsAdmitted
          rw [hd, hr]
          simp [hok, hrv]

/-! ## Examples -/

def exampleVocabulary : Atom :=
  .list [.symbol "cesta-operation-vocabulary/1", .symbol "Example",
    .list [.symbol "Resources", .list [.symbol "space", .text "store"], .list [.symbol "ledger", .text "store"]],
    .list [.symbol "Charges", .symbol "transition"], .list [.symbol "Profiles", .symbol "prime"]]

def exampleOperation (spelling name : String) (footprint : Atom) (typePure speculative : String) : Atom :=
  .list [.symbol "cesta-operation/1", .symbol name, .text spelling, .symbol name,
    .list [.symbol "Dispatch", .text "grounded"],
    .list [.symbol "Forms", .list [.symbol "Form", .list [.symbol "Arg", .text "value", .text "data", .text "borrow"]]],
    footprint,
    .list [.symbol "Context", .text "no", .text "no", .text "single", .list [.symbol "Charges"]],
    .list [.symbol "Result", .text "fresh"],
    .list [.symbol "Declared", .text "no", .text typePure, .text speculative, .list [.symbol "Replay", .text "refused"],
      .list [.symbol "Through"]],
    .list [.symbol "Profiles", .symbol "prime"]]

def footprintAtom (reads writes : List String) : Atom :=
  .list [.symbol "Footprint", .list (.symbol "Reads" :: reads.map .symbol), .list (.symbol "Writes" :: writes.map .symbol)]

def unknownFootprint : Atom := .list [.symbol "Footprint", .text "unknown"]

def examplePlacement (operation : Atom) : Option WorkerPlacementAdvice := do
  let vocabulary ← decodeVocabulary exampleVocabulary
  let decoded ← decodeOperation operation
  pure (workerPlacementAdvice vocabulary decoded)

/-- Positive read/write/pure controls and the negative unknown control. `size`
is a declared may-read here: this advice does not claim every dynamic call of
an overloaded head performs that read. -/
theorem workerPlacementAdvice_controls :
    examplePlacement
        (exampleOperation "size" "size" (footprintAtom ["space"] []) "no" "yes") =
          some .coordinator ∧
      examplePlacement
        (exampleOperation "space-push" "space_push" (footprintAtom [] ["space"]) "no" "no") =
          some .coordinator ∧
      examplePlacement
        (exampleOperation "car-atom" "car_atom" (footprintAtom [] []) "yes" "no") =
          some .local ∧
      examplePlacement
        (exampleOperation "py-call" "py_call" unknownFootprint "no" "no") =
          some .unresolved := by
  decide

example : tableAdmitted exampleVocabulary
    [exampleOperation "size" "size" (footprintAtom ["space"] []) "no" "yes",
     exampleOperation "space-push" "space_push" (footprintAtom [] ["space"]) "no" "no",
     exampleOperation "car-atom" "car_atom" (footprintAtom [] []) "yes" "no",
     exampleOperation "py-call" "py_call" unknownFootprint "no" "no"] = true := by decide

/-- A writer declared speculative is refused. -/
example : tableAdmitted exampleVocabulary
    [exampleOperation "space-push" "space_push" (footprintAtom [] ["space"]) "no" "yes"] = false := by decide

/-- A type-level licence that reads a space is refused. -/
example : tableAdmitted exampleVocabulary
    [exampleOperation "size" "size" (footprintAtom ["space"] []) "yes" "no"] = false := by decide

/-- A pure grounded operation without the type-level licence is refused. -/
example : tableAdmitted exampleVocabulary
    [exampleOperation "car-atom" "car_atom" (footprintAtom [] []) "no" "no"] = false := by decide

/-- A footprint naming an undeclared resource is refused. -/
example : tableAdmitted exampleVocabulary
    [exampleOperation "py-call" "py_call" (footprintAtom [] ["python"]) "no" "no"] = false := by decide

/-- The rows: the unknown footprint derives no query row and is listed as unknown. -/
example : (decodeTable exampleVocabulary
    [exampleOperation "size" "size" (footprintAtom ["space"] []) "no" "yes",
     exampleOperation "space-push" "space_push" (footprintAtom [] ["space"]) "no" "no",
     exampleOperation "car-atom" "car_atom" (footprintAtom [] []) "yes" "no",
     exampleOperation "py-call" "py_call" unknownFootprint "no" "no"]).map (fun p => lowerRows p.1 p.2) =
    some ⟨[], ["car_atom"], [], ["size"], [("size", 1), ("space_push", 2)], ["py_call"]⟩ := by decide

#print axioms workerPlacementAdvice_pure
#print axioms workerPlacementAdvice_nonzero
#print axioms workerPlacementAdvice_unresolved_iff
#print axioms query_row_requires_coordinator
#print axioms workerPlacementAdvice_controls

end Mettapedia.GSLT.LanguageDef.OperationContracts
