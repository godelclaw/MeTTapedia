namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: abstract fibration connectivity

This module contains the reusable graph-theoretic core for the frontier-state
composition plan.  It is deliberately independent of the particular
`tau`/mirror-`tau` tables: once a concrete chain proof supplies connected
fibers and lifted base moves, connectedness of the total graph follows from
connectedness of the base graph.
-/

namespace GoertzelLemma818Fibration

universe u v

/-- Reflexive transitive reachability for a directed step relation. -/
inductive Reach {α : Type u} (step : α → α → Prop) : α → α → Prop where
  | refl (x : α) : Reach step x x
  | tail {x y z : α} : Reach step x y → step y z → Reach step x z

namespace Reach

variable {α : Type u} {step : α → α → Prop}

theorem single {x y : α} (hxy : step x y) : Reach step x y :=
  Reach.tail (Reach.refl x) hxy

theorem trans {x y z : α}
    (hxy : Reach step x y) (hyz : Reach step y z) :
    Reach step x z := by
  induction hyz with
  | refl =>
      exact hxy
  | tail hyw hwz ih =>
      exact Reach.tail ih hwz

theorem map
    {β : Type v} {stepβ : β → β → Prop} {f : α → β}
    (hmap : ∀ {x y : α}, step x y → stepβ (f x) (f y))
    {x y : α} (hxy : Reach step x y) :
    Reach stepβ (f x) (f y) := by
  induction hxy with
  | refl =>
      exact Reach.refl (f x)
  | tail hpre hstep ih =>
      exact Reach.tail ih (hmap hstep)

theorem reverse_of_stepSymmetric
    (hsym : ∀ {x y : α}, step x y → step y x)
    {x y : α} (hxy : Reach step x y) :
    Reach step y x := by
  induction hxy with
  | refl =>
      exact Reach.refl x
  | tail hpre hstep ih =>
      exact Reach.trans (Reach.single (hsym hstep)) ih

end Reach

/-- A step relation is connected when every ordered pair is reachable. -/
def Connected {α : Type u} (step : α → α → Prop) : Prop :=
  ∀ x y, Reach step x y

/-- A step relation is symmetric when every directed step can be reversed. -/
def StepSymmetric {α : Type u} (step : α → α → Prop) : Prop :=
  ∀ {x y}, step x y → step y x

/--
A rooted connectivity certificate for a directed step relation.

Generated finite checks often produce this shape directly: every node can reach
a chosen root and the root can reach every node.
-/
structure RootedConnectedCertificate
    {α : Type u} (step : α → α → Prop) : Type u where
  root : α
  reachFromRoot : ∀ x, Reach step root x
  reachToRoot : ∀ x, Reach step x root

namespace RootedConnectedCertificate

variable {α : Type u} {step : α → α → Prop}

theorem connected (cert : RootedConnectedCertificate step) :
    Connected step := by
  intro x y
  exact Reach.trans (cert.reachToRoot x) (cert.reachFromRoot y)

end RootedConnectedCertificate

/--
A rooted certificate for a symmetric step relation.

For reversible finite graphs it is enough to emit the parent path from each
node to the root; symmetry supplies the reverse paths.
-/
structure SymmetricRootedConnectedCertificate
    {α : Type u} (step : α → α → Prop) : Type u where
  root : α
  stepSymmetric : StepSymmetric step
  reachToRoot : ∀ x, Reach step x root

namespace SymmetricRootedConnectedCertificate

variable {α : Type u} {step : α → α → Prop}

def toRooted (cert : SymmetricRootedConnectedCertificate step) :
    RootedConnectedCertificate step :=
  { root := cert.root
    reachFromRoot := fun x =>
      Reach.reverse_of_stepSymmetric cert.stepSymmetric (cert.reachToRoot x)
    reachToRoot := cert.reachToRoot }

theorem connected (cert : SymmetricRootedConnectedCertificate step) :
    Connected step :=
  cert.toRooted.connected

end SymmetricRootedConnectedCertificate

/--
A finite-list variant of a symmetric rooted certificate.

Generated quotient-base checks can emit a concrete list of base nodes, a cover
proof that every base node is on the list, and one root path for each listed
node.  This wrapper converts that finite witness surface to the universal
rooted certificate used by the fibration theorem.
-/
structure ListedSymmetricRootedConnectedCertificate
    {α : Type u} (step : α → α → Prop) : Type u where
  nodes : List α
  root : α
  stepSymmetric : StepSymmetric step
  covers : ∀ x, x ∈ nodes
  reachToRootOfMem : ∀ x, x ∈ nodes → Reach step x root

namespace ListedSymmetricRootedConnectedCertificate

variable {α : Type u} {step : α → α → Prop}

def toSymmetricRooted
    (cert : ListedSymmetricRootedConnectedCertificate step) :
    SymmetricRootedConnectedCertificate step :=
  { root := cert.root
    stepSymmetric := cert.stepSymmetric
    reachToRoot := fun x => cert.reachToRootOfMem x (cert.covers x) }

theorem connected (cert : ListedSymmetricRootedConnectedCertificate step) :
    Connected step :=
  cert.toSymmetricRooted.connected

end ListedSymmetricRootedConnectedCertificate

/-- Iterate a parent map a fixed number of steps toward a root. -/
def parentIter {α : Type u} (parent : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => parentIter parent n (parent x)

/--
A parent-map certificate for a finite symmetric rooted base graph.

This is the shape generated spanning-forest checks usually have: a finite list
of nodes covers the base, the parent map stays inside that list, non-root
parent rows are valid steps, stationary rows are explicit, and a bounded
parent iteration reaches the root.
-/
structure ParentMapSymmetricRootedConnectedCertificate
    {α : Type u} (step : α → α → Prop) : Type u where
  nodes : List α
  root : α
  parent : α → α
  maxDepth : Nat
  stepSymmetric : StepSymmetric step
  covers : ∀ x, x ∈ nodes
  parentStepOrSelfOfMem :
    ∀ x, x ∈ nodes → parent x = x ∨ step x (parent x)
  parentMemOfMem : ∀ x, x ∈ nodes → parent x ∈ nodes
  reachesRootOfMem :
    ∀ x, x ∈ nodes → parentIter parent maxDepth x = root

namespace ParentMapSymmetricRootedConnectedCertificate

variable {α : Type u} {step : α → α → Prop}

theorem reachParentIterOfMem
    (cert : ParentMapSymmetricRootedConnectedCertificate step) :
    ∀ (n : Nat) (x : α), x ∈ cert.nodes →
      Reach step x (parentIter cert.parent n x) := by
  intro n
  induction n with
  | zero =>
      intro x _hmem
      exact Reach.refl x
  | succ n ih =>
      intro x hmem
      have hfirst : Reach step x (cert.parent x) := by
        rcases cert.parentStepOrSelfOfMem x hmem with hself | hstep
        · simpa [hself] using (Reach.refl x : Reach step x x)
        · exact Reach.single hstep
      have htail :
          Reach step (cert.parent x)
            (parentIter cert.parent n (cert.parent x)) :=
        ih (cert.parent x) (cert.parentMemOfMem x hmem)
      simpa [parentIter] using Reach.trans hfirst htail

def toListed (cert : ParentMapSymmetricRootedConnectedCertificate step) :
    ListedSymmetricRootedConnectedCertificate step :=
  { nodes := cert.nodes
    root := cert.root
    stepSymmetric := cert.stepSymmetric
    covers := cert.covers
    reachToRootOfMem := fun x hmem => by
      have hreach := reachParentIterOfMem cert cert.maxDepth x hmem
      simpa [cert.reachesRootOfMem x hmem] using hreach }

def toSymmetricRooted
    (cert : ParentMapSymmetricRootedConnectedCertificate step) :
    SymmetricRootedConnectedCertificate step :=
  cert.toListed.toSymmetricRooted

theorem connected
    (cert : ParentMapSymmetricRootedConnectedCertificate step) :
    Connected step :=
  cert.toSymmetricRooted.connected

end ParentMapSymmetricRootedConnectedCertificate

/-- One generated parent row in a quotient-base spanning forest. -/
structure ParentMapRow {α : Type u} (step : α → α → Prop) : Type u where
  source : α
  parent : α
  stepOrSelf : parent = source ∨ step source parent

/-- Lookup the parent named by a row list, defaulting to the root off-list. -/
def parentFromRows {α : Type u} [DecidableEq α] {step : α → α → Prop}
    (root : α) : List (ParentMapRow step) → α → α
  | [], _ => root
  | row :: rows, x =>
      if row.source = x then row.parent else parentFromRows root rows x

namespace ParentMapRow

variable {α : Type u} [DecidableEq α] {step : α → α → Prop}

theorem parentFromRows_stepOrSelf_of_exists
    (root : α) :
    ∀ (rows : List (ParentMapRow step)) (x : α),
      (∃ row, row ∈ rows ∧ row.source = x) →
        parentFromRows root rows x = x ∨
          step x (parentFromRows root rows x) := by
  intro rows
  induction rows with
  | nil =>
      intro x hrow
      rcases hrow with ⟨row, hmem, _hsource⟩
      cases hmem
  | cons row rows ih =>
      intro x hrow
      unfold parentFromRows
      by_cases hsource : row.source = x
      · rw [if_pos hsource]
        cases hsource
        exact row.stepOrSelf
      · rw [if_neg hsource]
        apply ih
        rcases hrow with ⟨found, hmem, hfound⟩
        cases hmem with
        | head =>
          exact False.elim (hsource hfound)
        | tail _ htail =>
          exact ⟨found, htail, hfound⟩

theorem parentFromRows_mem_of_exists
    {nodes : List α} (root : α) :
    ∀ (rows : List (ParentMapRow step)) (x : α),
      (∀ row, row ∈ rows → row.parent ∈ nodes) →
      (∃ row, row ∈ rows ∧ row.source = x) →
        parentFromRows root rows x ∈ nodes := by
  intro rows
  induction rows with
  | nil =>
      intro x _hparent hrow
      rcases hrow with ⟨row, hmem, _hsource⟩
      cases hmem
  | cons row rows ih =>
      intro x hparent hrow
      unfold parentFromRows
      by_cases hsource : row.source = x
      · rw [if_pos hsource]
        exact hparent row List.mem_cons_self
      · rw [if_neg hsource]
        apply ih
        · intro found hfound
          exact hparent found (List.mem_cons_of_mem row hfound)
        · rcases hrow with ⟨found, hmem, hfound⟩
          cases hmem with
          | head =>
            exact False.elim (hsource hfound)
          | tail _ htail =>
            exact ⟨found, htail, hfound⟩

end ParentMapRow

/--
A row-list variant of the parent-map certificate.

Generated files can emit explicit parent rows and a coverage proof instead of
first defining a total parent function over the base type.
-/
structure ParentRowsSymmetricRootedConnectedCertificate
    {α : Type u} [DecidableEq α] (step : α → α → Prop) : Type u where
  nodes : List α
  root : α
  rows : List (ParentMapRow step)
  maxDepth : Nat
  stepSymmetric : StepSymmetric step
  covers : ∀ x, x ∈ nodes
  rowSourceMem : ∀ row, row ∈ rows → row.source ∈ nodes
  rowParentMem : ∀ row, row ∈ rows → row.parent ∈ nodes
  rowForNode : ∀ x, x ∈ nodes → ∃ row, row ∈ rows ∧ row.source = x
  reachesRootOfMem :
    ∀ x, x ∈ nodes →
      parentIter (parentFromRows root rows) maxDepth x = root

namespace ParentRowsSymmetricRootedConnectedCertificate

variable {α : Type u} [DecidableEq α] {step : α → α → Prop}

def toParentMap
    (cert : ParentRowsSymmetricRootedConnectedCertificate step) :
    ParentMapSymmetricRootedConnectedCertificate step :=
  { nodes := cert.nodes
    root := cert.root
    parent := parentFromRows cert.root cert.rows
    maxDepth := cert.maxDepth
    stepSymmetric := cert.stepSymmetric
    covers := cert.covers
    parentStepOrSelfOfMem := fun x hmem =>
      ParentMapRow.parentFromRows_stepOrSelf_of_exists cert.root
        cert.rows x (cert.rowForNode x hmem)
    parentMemOfMem := fun x hmem =>
      ParentMapRow.parentFromRows_mem_of_exists cert.root
        cert.rows x cert.rowParentMem (cert.rowForNode x hmem)
    reachesRootOfMem := cert.reachesRootOfMem }

def toListed
    (cert : ParentRowsSymmetricRootedConnectedCertificate step) :
    ListedSymmetricRootedConnectedCertificate step :=
  cert.toParentMap.toListed

def toSymmetricRooted
    (cert : ParentRowsSymmetricRootedConnectedCertificate step) :
    SymmetricRootedConnectedCertificate step :=
  cert.toParentMap.toSymmetricRooted

theorem connected
    (cert : ParentRowsSymmetricRootedConnectedCertificate step) :
    Connected step :=
  cert.toParentMap.connected

end ParentRowsSymmetricRootedConnectedCertificate

theorem connected_of_root_reachable_and_stepSymmetric
    {α : Type u} {step : α → α → Prop}
    (hsym : StepSymmetric step)
    (root : α)
    (hroot : ∀ x, Reach step x root) :
    Connected step := by
  intro x y
  exact Reach.trans (hroot x)
    (Reach.reverse_of_stepSymmetric hsym (hroot y))

/--
Data needed to lift base connectivity to total connectivity.

`fiberReach` connects points in the same fiber of `proj`; `liftStep` says every
one-step base move out of the projection of a total point can be realized by a
path in the total graph ending over the requested base point.
-/
structure Fibration
    {Total : Type u} {Base : Type v}
    (totalStep : Total → Total → Prop)
    (baseStep : Base → Base → Prop)
    (proj : Total → Base) : Prop where
  fiberReach :
    ∀ x y : Total, proj x = proj y → Reach totalStep x y
  liftStep :
    ∀ (x : Total) (b : Base), baseStep (proj x) b →
      ∃ y : Total, proj y = b ∧ Reach totalStep x y

namespace Fibration

variable {Total : Type u} {Base : Type v}
variable {totalStep : Total → Total → Prop}
variable {baseStep : Base → Base → Prop}
variable {proj : Total → Base}

theorem exists_reachable_over_base
    (h : Fibration totalStep baseStep proj)
    {x : Total} {b : Base}
    (hbase : Reach baseStep (proj x) b) :
    ∃ y : Total, proj y = b ∧ Reach totalStep x y := by
  induction hbase with
  | refl =>
      exact ⟨x, rfl, Reach.refl x⟩
  | tail hpre hstep ih =>
      rcases ih with ⟨z, hz, hxz⟩
      case tail bMid bNext =>
        have hstep' : baseStep (proj z) bNext := by
          simpa [hz] using hstep
        rcases h.liftStep z bNext hstep' with ⟨w, hw, hzw⟩
        exact ⟨w, hw, Reach.trans hxz hzw⟩

theorem totalReach_of_baseReach
    (h : Fibration totalStep baseStep proj)
    {x y : Total}
    (hbase : Reach baseStep (proj x) (proj y)) :
    Reach totalStep x y := by
  rcases h.exists_reachable_over_base hbase with ⟨z, hz, hxz⟩
  exact Reach.trans hxz (h.fiberReach z y hz)

theorem totalConnected_of_baseConnected
    (h : Fibration totalStep baseStep proj)
    (hbase : Connected baseStep) :
    Connected totalStep := by
  intro x y
  exact h.totalReach_of_baseReach (hbase (proj x) (proj y))

end Fibration

end GoertzelLemma818Fibration

end Mettapedia.GraphTheory.FourColor
