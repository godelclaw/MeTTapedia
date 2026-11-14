import Mettapedia.Languages.Prolog.SWI.SupervisorV1

set_option linter.unusedSectionVars false

/-! ## Supervisor-owned ClauseRefs (65455ce through 8f7019a)

The list reference and each unfreed owning version contribute to a clause's
lifetime. `cfreed` is derived from absence of both kinds of reference. Thus
unlinking a list reference need not free the clause, and freeing a version can
free its operands. No reader transition tests visibility or allocation.
-/

namespace Mettapedia.Languages.Prolog.SWI.Supervisor

open V1 (upd DetachMode Lock RPc Reader DPc Detacher WPc GPc)

structure Proto where
  detach : DetachMode
  validate : Bool
  cas : Bool
  hold : Bool
  own : Bool

def fixed : Proto := ⟨.inSection, true, true, true, true⟩
def noOwn : Proto := { fixed with own := false }
def noDetach : Proto := { fixed with detach := .none }
def lateDetach : Proto := { fixed with detach := .afterPublish }
def unvalidated : Proto := { fixed with validate := false }
def plainSwap : Proto := { fixed with cas := false }
def noHold : Proto := { fixed with hold := false }

inductive CPc where
  | idle | scanning | building | ready | checking | lingering
  deriving DecidableEq

def CPc.prototype : CPc → Bool
  | .ready | .checking => true
  | _ => false

def CPc.borrowed : CPc → Bool
  | .scanning | .building => true
  | _ => false

structure Creator (K : Type) where
  pc : CPc := .idle
  old : Option Nat := none
  found : List K := []
  ver : Nat := 0
  holds : Bool := false

structure St (R D K : Type) where
  G : Nat
  born : K → Nat
  erased : K → Option Nat
  cl_erased : K → Bool
  /-- The clause-list ClauseRef has not been dropped. -/
  linked : K → Bool
  embeds : Nat → List K
  /-- This version was built with its own ClauseRefs. -/
  owned : Nat → Bool
  next : Nat
  vfreed : Nat → Bool
  slot : Option Nat
  lingered : Nat → Option Nat
  dup : Bool
  lock : Lock
  wp : WPc
  cr : Creator K
  rd : R → Reader K
  dt : D → Detacher
  gpc : GPc
  start : Nat
  seen : R → Option (Option Nat)

variable {R D K : Type} [DecidableEq R] [DecidableEq D] [DecidableEq K]

def St.visAt (s : St R D K) (k : K) (g : Nat) : Prop :=
  s.born k ≤ g ∧ ∀ e, s.erased k = some e → g < e

instance (s : St R D K) (k : K) (g : Nat) : Decidable (s.visAt k g) :=
  match he : s.erased k with
  | none => decidable_of_iff (s.born k ≤ g) (by simp [St.visAt, he])
  | some e => decidable_of_iff (s.born k ≤ g ∧ g < e) (by simp [St.visAt, he])

def St.hasOwner (s : St R D K) (k : K) : Bool :=
  (List.range s.next).any fun v => s.owned v && !s.vfreed v && decide (k ∈ s.embeds v)

/-- Last-reference reclamation, not generation-based clause liveness. -/
def St.cfreed (s : St R D K) (k : K) : Bool := !(s.linked k || s.hasOwner k)

def St.touches (s : St R D K) : List K :=
  if s.cr.pc.borrowed then s.cr.found
  else if s.cr.pc.prototype then s.embeds s.cr.ver else []

def St.setR (s : St R D K) (r : R) (x : Reader K) : St R D K :=
  { s with rd := upd s.rd r x }

def St.setD (s : St R D K) (d : D) (x : Detacher) : St R D K :=
  { s with dt := upd s.dt d x }

def St.linger (s : St R D K) : Option Nat → St R D K
  | none => s
  | some v => { s with lingered := upd s.lingered v (some s.G),
                        dup := s.dup || (s.lingered v).isSome }

def St.writerDetach (s : St R D K) (pc : WPc) : St R D K :=
  ({ s with slot := none, wp := pc }).linger s.slot

def St.allocate (s : St R D K) (P : Proto) : St R D K :=
  { s with embeds := upd s.embeds s.next s.cr.found,
           owned := upd s.owned s.next P.own,
           vfreed := upd s.vfreed s.next false,
           lingered := upd s.lingered s.next none, next := s.next + 1,
           cr := { s.cr with pc := .ready, ver := s.next, holds := false } }

def St.installed (s : St R D K) : St R D K :=
  { s with slot := some s.cr.ver, lock := .free,
           cr := { s.cr with pc := .lingering } }

def St.creatorDone (s : St R D K) : St R D K :=
  { s.linger s.cr.old with cr := {} }

def St.detacherSwap (s : St R D K) (d : D) : St R D K :=
  { s.setD d { s.dt d with pc := .lingering } with slot := none }

def St.detacherDone (s : St R D K) (d : D) : St R D K :=
  (s.linger (s.dt d).old).setD d {}

inductive Step (P : Proto) : St R D K → St R D K → Prop where
  | stamp (s : St R D K) (r : R) (h : (s.rd r).pc = .idle) :
      Step P s (s.setR r { pc := .stamped, gen := s.G })
  | readSlot (s : St R D K) (r : R) (v : Nat)
      (h : (s.rd r).pc = .stamped) (hv : s.slot = some v) :
      Step P s (s.setR r { s.rd r with pc := .running, code := some v })
  | wait (s : St R D K) (r : R)
      (h : (s.rd r).pc = .stamped) (hv : s.slot = none) : Step P s s
  | run (s : St R D K) (r : R) (v : Nat) (k : K)
      (h : (s.rd r).pc = .running) (hv : (s.rd r).code = some v)
      (hk : k ∈ s.embeds v) :
      Step P s (s.setR r { s.rd r with run := some k })
  | exit (s : St R D K) (r : R) (h : (s.rd r).pc ≠ .idle) :
      Step P s (s.setR r {})
  | writerLock (s : St R D K) (h : s.lock = .free) (hw : s.wp = .idle) :
      Step P s { s with lock := .writer, wp := .marking }
  | mark (s : St R D K) (k : K) (h : s.lock = .writer)
      (hw : s.wp = .marking) (hk : s.visAt k s.G) (hf : s.cl_erased k = false) :
      Step P s { s with erased := upd s.erased k (some (s.G + 1)),
                        cl_erased := upd s.cl_erased k true }
  | writerDetach (s : St R D K) (hp : P.detach = .inSection)
      (h : s.lock = .writer) (hw : s.wp = .marking) :
      Step P s (s.writerDetach .detached)
  | skipDetach (s : St R D K) (hp : P.detach ≠ .inSection)
      (h : s.lock = .writer) (hw : s.wp = .marking) :
      Step P s { s with wp := .detached }
  | publish (s : St R D K) (h : s.lock = .writer) (hw : s.wp = .detached) :
      Step P s { s with G := s.G + 1, lock := .free,
                        wp := if P.detach = .afterPublish then .late else .idle }
  | lateDetach (s : St R D K) (hp : P.detach = .afterPublish) (hw : s.wp = .late) :
      Step P s (s.writerDetach .idle)
  /-- getClauses() has its own acquire_def2(), even in the no-outer-hold mutant. -/
  | creatorRead (s : St R D K) (h : s.cr.pc = .idle) :
      Step P s { s with cr := { pc := .scanning, old := s.slot, holds := true } }
  | scanClause (s : St R D K) (k : K) (h : s.cr.pc = .scanning)
      (hk : s.visAt k s.G) :
      Step P s { s with cr := { s.cr with found := s.cr.found ++ [k] } }
  /-- getClauses() returned; the outer hold covers the build/ownClause window. -/
  | finishScan (s : St R D K) (h : s.cr.pc = .scanning) :
      Step P s { s with cr := { s.cr with pc := .building, holds := P.hold } }
  /-- ownClause() while protected, then release_def2(); no hold at validation. -/
  | allocate (s : St R D K) (h : s.cr.pc = .building) : Step P s (s.allocate P)
  | creatorLock (s : St R D K) (h : s.lock = .free) (hc : s.cr.pc = .ready) :
      Step P s { s with lock := .creator, cr := { s.cr with pc := .checking } }
  | install (s : St R D K) (h : s.lock = .creator) (hc : s.cr.pc = .checking)
      (hv : P.validate = true → ∀ k ∈ s.embeds s.cr.ver, s.cl_erased k = false)
      (hs : P.cas = true → s.slot = s.cr.old) : Step P s s.installed
  | retry (s : St R D K) (h : s.lock = .creator) (hc : s.cr.pc = .checking)
      (hf : (P.validate = true ∧ ∃ k ∈ s.embeds s.cr.ver, s.cl_erased k = true) ∨
            (P.cas = true ∧ s.slot ≠ s.cr.old)) :
      Step P s { s with lock := .free, cr := {}, vfreed := upd s.vfreed s.cr.ver true }
  | creatorLinger (s : St R D K) (h : s.cr.pc = .lingering) :
      Step P s s.creatorDone
  | detacherRead (s : St R D K) (d : D) (h : (s.dt d).pc = .idle) :
      Step P s (s.setD d { pc := .loaded, old := s.slot })
  | detacherCas (s : St R D K) (d : D) (h : (s.dt d).pc = .loaded)
      (hs : P.cas = true → s.slot = (s.dt d).old) :
      Step P s (s.detacherSwap d)
  | detacherRetry (s : St R D K) (d : D) (hp : P.cas = true)
      (h : (s.dt d).pc = .loaded) (hs : s.slot ≠ (s.dt d).old) :
      Step P s (s.setD d {})
  | detacherLinger (s : St R D K) (d : D) (h : (s.dt d).pc = .lingering) :
      Step P s (s.detacherDone d)
  | gcStart (s : St R D K) (h : s.gpc = .idle) :
      Step P s { s with gpc := .scanning, start := s.G, seen := fun _ => none }
  | gcScan (s : St R D K) (r : R) (h : s.gpc = .scanning) (hn : s.seen r = none) :
      Step P s { s with seen := upd s.seen r
                          (some (if (s.rd r).pc = .idle then none else some (s.rd r).gen)) }
  /-- cleanDefinition() and gcClauseRefs() drop the list's reference only. -/
  | unlink (s : St R D K) (k : K) (e : Nat) (h : s.gpc = .scanning)
      (hall : ∀ r, s.seen r ≠ none) (he : s.erased k = some e)
      (hf : s.cl_erased k = true) (hlt : e < s.start)
      (hinv : ∀ r g, s.seen r = some (some g) → ¬ s.visAt k g)
      (hh : s.cr.holds = false) (hlist : s.linked k = true) :
      Step P s { s with linked := upd s.linked k false }
  /-- Releases every ClauseRef owned by the reclaimed supervisor version. -/
  | freeVersion (s : St R D K) (v d : Nat) (h : s.gpc = .scanning)
      (hall : ∀ r, s.seen r ≠ none) (hd : s.lingered v = some d) (hlt : d < s.start)
      (hinv : ∀ r g, s.seen r = some (some g) → d < g) (hnew : s.vfreed v = false) :
      Step P s { s with vfreed := upd s.vfreed v true }
  | gcEnd (s : St R D K) (h : s.gpc = .scanning) : Step P s { s with gpc := .idle }

inductive Reach (P : Proto) : St R D K → St R D K → Prop where
  | refl (s : St R D K) : Reach P s s
  | tail {s t u : St R D K} : Reach P s t → Step P t u → Reach P s u

def Init (s : St R D K) : Prop :=
  s.slot = none ∧ s.next = 0 ∧ s.dup = false ∧ s.lock = .free ∧ s.wp = .idle ∧
  s.cr = {} ∧ (∀ r, s.rd r = {}) ∧ (∀ d, s.dt d = {}) ∧
  s.gpc = .idle ∧ s.start ≤ s.G ∧ (∀ r, s.seen r = none) ∧
  (∀ k, s.erased k = none ∧ s.cl_erased k = false ∧ s.linked k = true) ∧
  (∀ v, s.embeds v = [] ∧ s.owned v = false ∧ s.vfreed v = false ∧ s.lingered v = none)

def Mem (s : St R D K) : Prop :=
  (∀ r, (∀ v, (s.rd r).code = some v → s.vfreed v = false) ∧
        (∀ k, (s.rd r).run = some k → s.cfreed k = false)) ∧
  (∀ k ∈ s.touches, s.cfreed k = false) ∧ s.dup = false ∧
  (∀ v, s.slot = some v → s.lingered v = none ∧ s.vfreed v = false)

def LudErase (s : St R D K) : Prop :=
  ∀ r k e, (s.rd r).run = some k → s.erased k = some e → (s.rd r).gen < e

/-! Reserved versions: a slot, a prototype, or a successful swap awaiting linger.
These are derived from program control. They are not transition preconditions. -/

inductive Loc (D : Type) where
  | slot | prototype | creator | detacher (d : D)
  deriving DecidableEq

def St.root (s : St R D K) : Loc D → Option Nat
  | .slot => s.slot
  | .prototype => if s.cr.pc.prototype then some s.cr.ver else none
  | .creator => if s.cr.pc = .lingering then s.cr.old else none
  | .detacher d => if (s.dt d).pc = .lingering then (s.dt d).old else none

structure Roots (f : Loc D → Option Nat) (n : Nat) (dead : Nat → Option Nat)
    (freed : Nat → Bool) : Prop where
  unique : ∀ a b v, f a = some v → f b = some v → a = b
  clean : ∀ a v, f a = some v → v < n ∧ dead v = none ∧ freed v = false

abbrev RootInv (s : St R D K) := Roots s.root s.next s.lingered s.vfreed

structure RInv (s : St R D K) (x : Reader K) : Prop where
  gen_le : x.gen ≤ s.G
  code_bound : ∀ v, x.code = some v → v < s.next
  code_proto : ∀ v, x.code = some v → s.root .prototype ≠ some v
  code_live : ∀ v, x.code = some v → s.vfreed v = false
  retired : ∀ v d, x.code = some v → s.lingered v = some d → x.gen ≤ d
  selected : ∀ k, x.run = some k → ∃ v, x.code = some v ∧ k ∈ s.embeds v
  code_pc : ∀ v, x.code = some v → x.pc = .running

structure Inv (s : St R D K) : Prop where
  roots : RootInv s
  start_le : s.start ≤ s.G
  flag : ∀ k, s.cl_erased k = false ↔ s.erased k = none
  unlinked_old : ∀ k, s.linked k = false → ∃ e, s.erased k = some e ∧ e < s.G
  borrowed_hold : s.cr.pc.borrowed = true → s.cr.holds = true
  borrowed_list : s.cr.pc.borrowed = true → ∀ k ∈ s.cr.found, s.linked k = true
  owned : ∀ v, v < s.next → s.owned v = true
  rd : ∀ r, RInv s (s.rd r)
  scanned : ∀ r, s.gpc = .scanning → s.seen r ≠ none → (s.rd r).pc ≠ .idle →
    s.start ≤ (s.rd r).gen ∨ s.seen r = some (some (s.rd r).gen)
  nodup : s.dup = false

structure EInv (s : St R D K) : Prop where
  writer : s.lock = .writer ↔ s.wp = .marking ∨ s.wp = .detached
  creator : s.lock = .creator ↔ s.cr.pc = .checking
  detached : s.wp = .detached → s.slot = none
  slot : ∀ v k e, s.slot = some v → k ∈ s.embeds v → s.erased k = some e → s.G < e
  reader : ∀ r v k e, (s.rd r).code = some v → k ∈ s.embeds v →
    s.erased k = some e → (s.rd r).gen < e

/-- An unfreed owning version keeps every embedded clause alive. -/
theorem owner_live {s : St R D K} {v : Nat} {k : K} (hb : v < s.next)
    (ho : s.owned v = true) (hf : s.vfreed v = false) (hk : k ∈ s.embeds v) :
    s.cfreed k = false := by
  have h : s.hasOwner k = true := by
    apply List.any_eq_true.mpr
    exact ⟨v, List.mem_range.mpr hb, by simp [ho, hf, hk]⟩
  simp [St.cfreed, h]

theorem linked_live {s : St R D K} {k : K} (hk : s.linked k = true) :
    s.cfreed k = false := by simp [St.cfreed, hk]

theorem Inv.mem {s : St R D K} (h : Inv s) : Mem s := by
  refine ⟨?_, ?_, h.nodup, ?_⟩
  · intro r
    refine ⟨(h.rd r).code_live, ?_⟩
    intro k hk
    obtain ⟨v, hv, he⟩ := (h.rd r).selected k hk
    exact owner_live ((h.rd r).code_bound v hv) (h.owned v ((h.rd r).code_bound v hv))
      ((h.rd r).code_live v hv) he
  · intro k hk
    unfold St.touches at hk
    split at hk
    · exact linked_live (h.borrowed_list (by assumption) k hk)
    · split at hk
      · have hr : s.root .prototype = some s.cr.ver := by simp [St.root, *]
        obtain ⟨hb, _, hf⟩ := h.roots.clean .prototype s.cr.ver hr
        exact owner_live hb (h.owned _ hb) hf hk
      · simp at hk
  · intro v hv
    exact (h.roots.clean .slot v hv).2

theorem EInv.lud {s : St R D K} (h : Inv s) (he : EInv s) : LudErase s := by
  intro r k e hk hd
  obtain ⟨v, hv, hm⟩ := (h.rd r).selected k hk
  exact he.reader r v k e hv hm hd

end Mettapedia.Languages.Prolog.SWI.Supervisor
