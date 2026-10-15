import Mettapedia.GSLT.Causality.DoCalculus.FrontDoorDerivation

/-!
# Shpitser-Pearl ID, relative to `idFragment`

`identify` tries the two branches of `idFragment` first. It then tries a
front-door mediator, the napkin checkers, a singleton back-door set, and a
direct latent bow. The napkin branch stands before the back door: on the
napkin graph the back-door checker accepts a vertex whose formula is not the
derived quotient.
What remains is the back-door sum over every observed covariate, or a recursion
on c-components. A hedge from that recursion has a trunk and a canopy that are
themselves c-components. Fuel only bounds the recursion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation
open scoped ENNReal

/-- Trunk inside a canopy. The trunk misses the intervention and the canopy meets it. -/
structure Hedge (V : Type) where
  trunk : Finset V
  canopy : Finset V
  intervention : Finset V
  trunk_subset_canopy : trunk ⊆ canopy
  trunk_misses : Disjoint trunk intervention
  canopy_hits : ∃ v, v ∈ canopy ∧ v ∈ intervention

/-- What ID returns: a do-free expression, or a hedge. -/
inductive IdOutcome (V : Type) where
  | doFree (expr : MassExpr V)
  | hedge (witness : Hedge V)

variable {V : Type} [Fintype V] [DecidableEq V]
variable (graph : DirectedGraph V) [DecidableRel graph.edges]

/-- Two distinct observed vertices share a parent in the latent set `L`. -/
def cNeighbor (L : Finset V) (a b : V) : Bool :=
  decide (a ≠ b ∧ a ∉ L ∧ b ∉ L ∧ ∃ u ∈ L, graph.edges u a ∧ graph.edges u b)

def cGrow (L scope acc : Finset V) : Finset V :=
  scope.filter fun v => v ∈ acc ∨ ∃ u ∈ acc, cNeighbor graph L u v = true

def cClose (L scope : Finset V) : Nat → Finset V → Finset V
  | 0, acc => acc
  | n + 1, acc =>
    let grown := cGrow graph L scope acc
    if grown = acc then acc else cClose L scope n grown

/-- The c-component of `seed` inside `scope`, closing under `cNeighbor`. -/
def cComponent (L scope : Finset V) (seed : V) : Finset V :=
  if seed ∈ scope then cClose graph L scope (scope.card + 1) {seed} else ∅

/-- The five checker premises of the smoking front-door derivation. -/
def frontDoorReady (s t c : Finset V) : Bool :=
  FiniteDSeparation.check (gout graph (∅ : Finset V) s)
      (rule2Profile t s ((∅ : Finset V) ∪ ∅)) &&
    FiniteDSeparation.check (gout graph s t)
      (rule2Profile c t (s ∪ (∅ : Finset V))) &&
    FiniteDSeparation.check (rule3Graph graph t s (∅ : Finset V))
      (rule3Profile c s (t ∪ (∅ : Finset V))) &&
    FiniteDSeparation.check (rule3Graph graph (∅ : Finset V) t (∅ : Finset V))
      (rule3Profile s t ((∅ : Finset V) ∪ ∅)) &&
    FiniteDSeparation.check (gout graph (∅ : Finset V) t)
      (rule2Profile c t ((∅ : Finset V) ∪ s))

/-- Rule 2 and rule 3 for a singleton back-door set. -/
def backDoorReady (x z y : Finset V) : Bool :=
  FiniteDSeparation.check (gout graph (∅ : Finset V) x)
      (rule2Profile y x ((∅ : Finset V) ∪ z)) &&
    FiniteDSeparation.check (rule3Graph graph (∅ : Finset V) x (∅ : Finset V))
      (rule3Profile z x ((∅ : Finset V) ∪ ∅))

def frontDoorShape (s t c : Finset V) : MassExpr V :=
  .sum t
    (.mul
      (.sum s
        (.mul
          (.cond ∅ ((∅ : Finset V) ∪ c ∪ t ∪ s) ((∅ : Finset V) ∪ t ∪ s))
          (.cond ∅ ((∅ : Finset V) ∪ s ∪ ∅) (∅ ∪ ∅))))
      (.cond ∅ ((∅ : Finset V) ∪ t ∪ s ∪ ∅) (∅ ∪ s ∪ ∅)))

def backDoorShape (x y z : Finset V) : MassExpr V :=
  .sum z
    (.mul
      (.cond (∅ : Finset V)
        ((∅ : Finset V) ∪ y ∪ x ∪ z)
        ((∅ : Finset V) ∪ x ∪ z))
      (.cond (∅ : Finset V)
        ((∅ : Finset V) ∪ z ∪ ∅)
        ((∅ : Finset V) ∪ ∅)))

/-- Insert `do(z)`, exchange `do(x)` for `x`, and adjust `Z` through `W`
on both `{X, Y}` and `X`. -/
def napkinReady (x z w y : Finset V) : Bool :=
  FiniteDSeparation.check
      (rule3Graph graph x z (∅ : Finset V))
      (rule3Profile y z (x ∪ (∅ : Finset V))) &&
    FiniteDSeparation.check (gout graph z x)
      (rule2Profile y x (z ∪ (∅ : Finset V))) &&
    FiniteDSeparation.check (gout graph (∅ : Finset V) z)
      (rule2Profile (x ∪ y) z ((∅ : Finset V) ∪ w)) &&
    FiniteDSeparation.check (gout graph (∅ : Finset V) z)
      (rule2Profile x z ((∅ : Finset V) ∪ w)) &&
    FiniteDSeparation.check
      (rule3Graph graph (∅ : Finset V) z (∅ : Finset V))
      (rule3Profile w z ((∅ : Finset V) ∪ (∅ : Finset V)))

/-- `Σ_w P(y, x | z, w) P(w) / Σ_w P(x | z, w) P(w)`. -/
def napkinShape (x z w y : Finset V) : MassExpr V :=
  .div
    (.sum w
      (.mul
        (.cond (∅ : Finset V)
          ((∅ : Finset V) ∪ (x ∪ y) ∪ z ∪ w)
          ((∅ : Finset V) ∪ z ∪ w))
        (.cond (∅ : Finset V)
          ((∅ : Finset V) ∪ w ∪ ∅)
          ((∅ : Finset V) ∪ ∅))))
    (.sum w
      (.mul
        (.cond (∅ : Finset V)
          ((∅ : Finset V) ∪ x ∪ z ∪ w)
          ((∅ : Finset V) ∪ z ∪ w))
        (.cond (∅ : Finset V)
          ((∅ : Finset V) ∪ w ∪ ∅)
          ((∅ : Finset V) ∪ ∅))))

def findVertex (enum : List V) (p : V → Bool) : Option V :=
  enum.find? p

/-- The do-free end of one `idFragment` exchange, as a derivation, when rule 2's
checker accepts the same sets. -/
def fragmentExchangeDeriv (outcome bound conditioning : Finset V)
    (hcheck : FiniteDSeparation.check (gout graph (∅ : Finset V) bound)
      (rule2Profile outcome bound ((∅ : Finset V) ∪ conditioning)) = true) :
    Deriv graph (exchangeSource outcome bound conditioning)
      (exchangeResult outcome bound conditioning) :=
  .rewriteEq (by simp [exchangeSource, Finset.empty_union])
    (by simp [exchangeResult, Finset.empty_union])
    (.rule2 (∅ : Finset V) outcome bound conditioning hcheck)

/-- The do-free end of one `idFragment` deletion, as a derivation, when rule 3's
checker accepts the same sets. -/
def fragmentDeleteDeriv (outcome bound conditioning : Finset V)
    (hcheck : FiniteDSeparation.check
      (rule3Graph graph (∅ : Finset V) bound conditioning)
      (rule3Profile outcome bound ((∅ : Finset V) ∪ conditioning)) = true) :
    Deriv graph (deleteSource outcome bound conditioning)
      (deleteResult outcome conditioning) :=
  .rewriteEq (by simp [deleteSource, Finset.empty_union])
    (by simp [deleteResult, Finset.empty_union])
    (.rule3 (∅ : Finset V) outcome bound conditioning hcheck)

def hedgeOfPair (y x : V) (intervention : Finset V)
    (hx : x ∈ intervention) (hnot : y ∉ intervention) : Hedge V where
  trunk := {y}
  canopy := {y, x}
  intervention := intervention
  trunk_subset_canopy := by
    intro vertex hmember
    simp only [Finset.mem_singleton] at hmember
    subst hmember
    simp
  trunk_misses := by
    rw [Finset.disjoint_left]
    intro vertex hmember hintervention
    simp only [Finset.mem_singleton] at hmember
    subst hmember
    exact hnot hintervention
  canopy_hits := ⟨x, by simp, hx⟩

/-- Parents of one vertex in the original graph. -/
def parentsOf (v : V) : Finset V :=
  Finset.univ.filter fun parent => graph.edges parent v

/-- Observational factor `P(v | parents(v))`. -/
def localFactor (v : V) : MassExpr V :=
  .cond (∅ : Finset V) ({v} ∪ parentsOf graph v) (parentsOf graph v)

def factorsOf (enum : List V) (scope : Finset V) : List (MassExpr V) :=
  enum.filterMap fun vertex =>
    if vertex ∈ scope then some (localFactor graph vertex) else none

def foldProd : List (MassExpr V) → MassExpr V
  | [] => .cond (∅ : Finset V) ∅ ∅
  | factor :: rest => rest.foldl (fun acc next => .mul acc next) factor

/-- Latent-free factorization: sum the parental factors of every non-intervened vertex. -/
def parentSum (enum : List V) (L outcome intervention : Finset V) : MassExpr V :=
  let scope := (Finset.univ \ L) \ intervention
  .sum (scope \ outcome) (foldProd (factorsOf graph enum scope))

/-- Every observed c-component is a singleton. -/
def allSingletonComponents (L : Finset V) : Bool :=
  decide (∀ vertex, vertex ∉ L →
    cComponent graph L (Finset.univ \ L) vertex = {vertex})

/-- A hedge whose trunk and canopy are the c-components of `seed`. The trunk is nonempty. -/
def tryComponentHedge (L intervention : Finset V) (seed : V) : Option (Hedge V) :=
  let observed := Finset.univ \ L
  let canopy := cComponent graph L observed seed
  let trunk := cComponent graph L (observed \ intervention) seed
  if hsub : trunk ⊆ canopy then
    if hmiss : Disjoint trunk intervention then
      if hhit : (canopy ∩ intervention).Nonempty then
        if htrunk : trunk.Nonempty then
          if hproper : trunk ≠ canopy then
            some {
              trunk := trunk
              canopy := canopy
              intervention := intervention
              trunk_subset_canopy := hsub
              trunk_misses := hmiss
              canopy_hits := by
                rcases hhit with ⟨vertex, hmember⟩
                simp only [Finset.mem_inter] at hmember
                exact ⟨vertex, hmember.1, hmember.2⟩
            }
          else none
        else none
      else none
    else none
  else none

def componentHedge (enum : List V) (L outcome intervention : Finset V) : Option (Hedge V) :=
  enum.findSome? fun seed =>
    if decide (seed ∈ outcome ∨ seed ∈ intervention) then
      tryComponentHedge graph L intervention seed
    else
      none

omit graph [DecidableRel graph.edges] in
def covariateSet (L outcome intervention conditioning : Finset V) : Finset V :=
  (((Finset.univ \ L) \ intervention) \ outcome) \ conditioning

omit graph [DecidableRel graph.edges] in
def componentScope (L intervention : Finset V) : Finset V :=
  (Finset.univ \ L) \ intervention

/-- One c-component for each seed in `scope` that an earlier component missed. -/
def queryComponents (enum : List V) (L scope : Finset V) : List (Finset V) :=
  enum.foldl (fun seen seed =>
    if decide (seed ∈ scope) && seen.all (fun comp => decide (seed ∉ comp)) then
      cComponent graph L scope seed :: seen
    else
      seen) []

omit graph [DecidableRel graph.edges] in
def attachFactor (acc : Option (MassExpr V)) (factor : MassExpr V) : Option (MassExpr V) :=
  match acc with
  | none => some factor
  | some prev => some (.mul prev factor)

/-- Fuel is spent. Multiply the parental factors, or return a c-component hedge. -/
def finishPending (enum : List V) (L intervention : Finset V)
    (acc : Option (MassExpr V)) : List (Finset V) → IdOutcome V
  | [] =>
    match acc with
    | none => .doFree (.cond (∅ : Finset V) ∅ ∅)
    | some expr => .doFree expr
  | comp :: rest =>
    match componentHedge graph enum L comp intervention with
    | some hedge => .hedge hedge
    | none =>
      finishPending enum L intervention
        (attachFactor acc (foldProd (factorsOf graph enum comp))) rest

/-- Recurse on the pending c-components. Each step uses a smaller fuel.
A returned hedge is the one `componentHedge` built from `cComponent`. -/
def descend (fuel : Nat) (enum : List V) (L intervention : Finset V)
    (acc : Option (MassExpr V)) (pending : List (Finset V)) : IdOutcome V :=
  match fuel with
  | 0 => finishPending graph enum L intervention acc pending
  | n + 1 =>
    match pending with
    | [] =>
      match acc with
      | none => .doFree (.cond (∅ : Finset V) ∅ ∅)
      | some expr => .doFree expr
    | comp :: rest =>
      match componentHedge graph enum L comp intervention with
      | some hedge => .hedge hedge
      | none =>
        let scope := comp ∩ componentScope L intervention
        let inner := queryComponents graph enum L scope
        if decide (inner.length ≤ 1) then
          descend n enum L intervention
            (attachFactor acc (foldProd (factorsOf graph enum comp))) rest
        else
          match descend n enum L (intervention ∪ (componentScope L intervention \ comp))
              none inner with
          | .hedge hedge => .hedge hedge
          | .doFree sub =>
            descend n enum L intervention (attachFactor acc sub) rest

/-- Sum the c-component recursion down to the queried outcome. -/
def descendQuery (fuel : Nat) (enum : List V) (L outcome intervention : Finset V) : IdOutcome V :=
  let scope := componentScope L intervention
  match descend graph fuel enum L intervention none (queryComponents graph enum L scope) with
  | .hedge hedge => .hedge hedge
  | .doFree expr => .doFree (.sum (scope \ outcome) expr)

def unresolved (fuel : Nat) (enum : List V) (L outcome intervention conditioning : Finset V) :
    IdOutcome V :=
  match componentHedge graph enum L outcome intervention with
  | some hedge => .hedge hedge
  | none =>
    match componentHedge graph enum L (Finset.univ \ L) intervention with
    | some hedge => .hedge hedge
    | none =>
      if allSingletonComponents graph L then
        .doFree (parentSum graph enum L outcome intervention)
      else if decide (intervention = ∅) then
        .doFree (deleteResult outcome conditioning)
      else
        descendQuery graph fuel enum L outcome intervention

/-- Vertices reached from `acc` by one outgoing edge, including `acc`. -/
def growForward (acc : Finset V) : Finset V :=
  Finset.univ.filter fun vertex =>
    decide (vertex ∈ acc ∨ ∃ parent ∈ acc, graph.edges parent vertex)

def closeForward : Nat → Finset V → Finset V
  | 0, acc => acc
  | n + 1, acc =>
    let grown := growForward graph acc
    if grown = acc then acc else closeForward n grown

/-- The forward closure of `seed`. Reachability is reflexive, so `seed` stays inside. -/
def forwardSet (seed : Finset V) : Finset V :=
  closeForward graph (Fintype.card V + 1) seed

/-- No vertex of `source` reaches a vertex of `target`. -/
def missesForward (source target : Finset V) : Bool :=
  decide (forwardSet graph source ∩ target = ∅)

/-- Back-door sum over every observed covariate. An intervention that reaches
neither the outcome nor the conditioning set is deleted. Otherwise recurse on
c-components. -/
def identifyRest (fuel : Nat) (enum : List V) (L outcome intervention conditioning : Finset V) :
    IdOutcome V :=
  let cov := covariateSet L outcome intervention conditioning
  if missesForward graph intervention (outcome ∪ conditioning) then
    .doFree (deleteResult outcome conditioning)
  else if conditioning = ∅ then
    if backDoorReady graph intervention cov outcome then
      .doFree (backDoorShape intervention outcome cov)
    else
      unresolved graph fuel enum L outcome intervention conditioning
  else
    unresolved graph fuel enum L outcome intervention conditioning

structure PairHit (intervention : Finset V) where
  y : V
  x : V
  x_mem : x ∈ intervention
  y_miss : y ∉ intervention

def bowPair (enum : List V) (L outcome intervention : Finset V) : Option (PairHit intervention) :=
  enum.findSome? fun y =>
    if hnot : y ∉ intervention then
      if _ : y ∈ outcome then
        enum.findSome? fun x =>
          if hx : x ∈ intervention then
            if _ : cNeighbor graph L y x = true then
              some ⟨y, x, hx, hnot⟩
            else
              none
          else
            none
      else
        none
    else
      none

/-- A search vertex is outside the latent set, the outcome, and the intervention. -/
def outsideQuery (L outcome intervention : Finset V) (vertex : V) : Bool :=
  decide (vertex ∉ L ∧ vertex ∉ outcome ∧ vertex ∉ intervention)

def findNapkin (enum : List V) (L outcome intervention : Finset V) : Option (V × V) :=
  enum.findSome? fun z =>
    if outsideQuery L outcome intervention z then
      enum.findSome? fun w =>
        if outsideQuery L outcome intervention w && decide (w ≠ z) &&
            napkinReady graph intervention {z} {w} outcome then
          some (z, w)
        else
          none
    else
      none

/-- ID. The first two branches are `idFragment`. A direct latent bow is a hedge
whose trunk and canopy are a pair of c-neighbors. Otherwise the answer is the
back-door sum over the remaining observed covariates, or the c-component
recursion. Fuel bounds that recursion; it is not turned into a hedge. -/
def identify (fuel : Nat) (enum : List V) (L outcome intervention conditioning : Finset V) :
    IdOutcome V :=
  match fuel with
  | 0 =>
    if parentsIn graph intervention ∅ conditioning then
      .doFree (exchangeResult outcome intervention conditioning)
    else if deleteOK graph outcome intervention conditioning then
      .doFree (deleteResult outcome conditioning)
    else
      identifyRest graph 0 enum L outcome intervention conditioning
  | fuel + 1 =>
    if parentsIn graph intervention ∅ conditioning then
      .doFree (exchangeResult outcome intervention conditioning)
    else if deleteOK graph outcome intervention conditioning then
      .doFree (deleteResult outcome conditioning)
    else if conditioning = ∅ then
      match findVertex enum fun v =>
          outsideQuery L outcome intervention v &&
            frontDoorReady graph intervention {v} outcome with
      | some mediator => .doFree (frontDoorShape intervention {mediator} outcome)
      | none =>
        match findNapkin graph enum L outcome intervention with
        | some pair =>
            .doFree (napkinShape intervention {pair.1} {pair.2} outcome)
        | none =>
          match findVertex enum fun v =>
              outsideQuery L outcome intervention v &&
                backDoorReady graph intervention {v} outcome with
          | some covariate => .doFree (backDoorShape intervention outcome {covariate})
          | none =>
            if missesForward graph intervention (outcome ∪ conditioning) then
              .doFree (deleteResult outcome conditioning)
            else
              match bowPair graph enum L outcome intervention with
              | some hit => .hedge (hedgeOfPair hit.y hit.x intervention hit.x_mem hit.y_miss)
              | none =>
                identifyRest graph fuel enum L outcome intervention conditioning
    else
      identifyRest graph fuel enum L outcome intervention conditioning

/-- A do-free answer of `idFragment` is the same do-free answer of `identify`. -/
theorem fragment_doFree_is_identify
    (fuel : Nat) (enum : List V) (L outcome bound conditioning : Finset V)
    {expr : MassExpr V}
    (hanswer : idFragment graph outcome bound conditioning = .doFree expr) :
    identify graph (fuel + 1) enum L outcome bound conditioning = .doFree expr := by
  simp only [idFragment] at hanswer
  split_ifs at hanswer with hparents hdelete
  · unfold identify
    split <;> (rw [if_pos hparents]; cases hanswer; rfl)
  · unfold identify
    split <;> (rw [if_neg hparents, if_pos hdelete]; cases hanswer; rfl)

theorem identify_fuel_exchange
    (fuel : Nat) (enum : List V) (L outcome bound conditioning : Finset V)
    (hparents : parentsIn graph bound ∅ conditioning = true) :
    identify graph (fuel + 1) enum L outcome bound conditioning =
      .doFree (exchangeResult outcome bound conditioning) := by
  unfold identify
  split <;> rw [if_pos hparents]

theorem identify_fuel_delete
    (fuel : Nat) (enum : List V) (L outcome bound conditioning : Finset V)
    (hparents : parentsIn graph bound ∅ conditioning = false)
    (hdelete : deleteOK graph outcome bound conditioning = true) :
    identify graph (fuel + 1) enum L outcome bound conditioning =
      .doFree (deleteResult outcome conditioning) := by
  unfold identify
  have hnot : ¬ parentsIn graph bound ∅ conditioning = true := by
    simp [hparents]
  split <;> rw [if_neg hnot, if_pos hdelete]

/-- On the bow, `Y` and `X` share the latent parent `U`. -/
theorem bow_c_neighbor :
    cNeighbor bowGraph {Bow.u} Bow.y Bow.x = true := by
  decide

/-- `idFragment` refuses the bow query. -/
theorem bow_fragment_refuses :
    idFragment bowGraph {Bow.y} {Bow.x} (∅ : Finset Bow) = .refuse := by
  decide

/-- `idFragment` refuses the front-door query. -/
theorem smoke_fragment_refuses :
    idFragment smokeGraph {Smoke.c} {Smoke.s} (∅ : Finset Smoke) = .refuse := by
  decide

/-- The smoking sets meet the five front-door checker premises. -/
theorem smoke_front_door_ready :
    frontDoorReady smokeGraph smokeS smokeT smokeC = true := by
  decide

theorem smoke_parents_fail :
    parentsIn smokeGraph smokeS (∅ : Finset Smoke) (∅ : Finset Smoke) = false := by
  decide

theorem smoke_delete_fail :
    deleteOK smokeGraph {Smoke.c} smokeS (∅ : Finset Smoke) = false := by
  decide

def smokeEnum : List Smoke := [Smoke.u, Smoke.s, Smoke.t, Smoke.c]

def bowEnum : List Bow := [Bow.u, Bow.x, Bow.y]

theorem frontDoorShape_eq_frontDoorExpr :
    frontDoorShape smokeS smokeT smokeC = frontDoorExpr := by
  unfold frontDoorShape frontDoorExpr cancerSumObs cancerSmokeObs
    cancerObservational smokeObservational tarGivenSmoke
  rfl

/-- The front-door query is an answer of ID and not of `idFragment`. -/
theorem front_door_separates_id :
    idFragment smokeGraph {Smoke.c} {Smoke.s} (∅ : Finset Smoke) = .refuse ∧
      identify smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS (∅ : Finset Smoke) =
        .doFree frontDoorExpr ∧
      doFree frontDoorExpr = true := by
  refine ⟨smoke_fragment_refuses, ?_, frontDoorExpr_doFree⟩
  unfold identify
  have hparents : ¬ parentsIn smokeGraph smokeS (∅ : Finset Smoke) (∅ : Finset Smoke) = true := by
    simp [smoke_parents_fail]
  have hdelete : ¬ deleteOK smokeGraph {Smoke.c} smokeS (∅ : Finset Smoke) = true := by
    simp [smoke_delete_fail]
  rw [if_neg hparents, if_neg hdelete]
  simp [smokeEnum, findVertex]
  rfl

theorem bow_parents_fail :
    parentsIn bowGraph {Bow.x} (∅ : Finset Bow) (∅ : Finset Bow) = false := by
  decide

theorem bow_delete_fail :
    deleteOK bowGraph {Bow.y} {Bow.x} (∅ : Finset Bow) = false := by
  decide

theorem bow_no_front_mediator :
    findVertex bowEnum (fun v =>
      outsideQuery {Bow.u} {Bow.y} {Bow.x} v &&
        frontDoorReady bowGraph {Bow.x} {v} {Bow.y}) = none := by
  decide

/-- The raw back-door checker accepts some bow vertex, so the search stays
outside the latent set, the outcome, and the intervention. -/
theorem bow_raw_back_door_hits :
    (findVertex bowEnum fun v => backDoorReady bowGraph {Bow.x} {v} {Bow.y}).isSome = true := by
  decide

theorem bow_no_back_covariate :
    findVertex bowEnum (fun v =>
      outsideQuery {Bow.u} {Bow.y} {Bow.x} v &&
        backDoorReady bowGraph {Bow.x} {v} {Bow.y}) = none := by
  decide

theorem bow_no_napkin :
    findNapkin bowGraph bowEnum {Bow.u} {Bow.y} {Bow.x} = none := by
  decide

theorem bow_misses_forward :
    missesForward bowGraph {Bow.x} ({Bow.y} ∪ (∅ : Finset Bow)) = false := by
  decide

theorem bow_pair_vertices :
    ((bowPair bowGraph bowEnum {Bow.u} {Bow.y} {Bow.x}).map fun hit => (hit.y, hit.x)) =
      some (Bow.y, Bow.x) := by
  decide

/-- ID returns the bow hedge: trunk `{Y}`, canopy `{Y, X}`. -/
theorem bow_id_returns_hedge :
    match identify bowGraph 2 bowEnum {Bow.u} {Bow.y} {Bow.x} (∅ : Finset Bow) with
    | .hedge witness =>
        witness.trunk = {Bow.y} ∧ witness.canopy = {Bow.y, Bow.x}
    | .doFree _ => False := by
  have hparents : ¬ parentsIn bowGraph {Bow.x} (∅ : Finset Bow) (∅ : Finset Bow) = true := by
    simp [bow_parents_fail]
  have hdelete : ¬ deleteOK bowGraph {Bow.y} {Bow.x} (∅ : Finset Bow) = true := by
    simp [bow_delete_fail]
  have hx : Bow.x ∈ ({Bow.x} : Finset Bow) := by simp
  have hyout : Bow.y ∉ ({Bow.x} : Finset Bow) := by simp
  have hcompute :
      identify bowGraph 2 bowEnum {Bow.u} {Bow.y} {Bow.x} (∅ : Finset Bow) =
        .hedge (hedgeOfPair Bow.y Bow.x {Bow.x} hx hyout) := by
    unfold identify
    split
    · rename_i hzero
      cases hzero
    · rw [if_neg hparents, if_neg hdelete, if_pos (rfl : (∅ : Finset Bow) = ∅)]
      rw [bow_no_front_mediator, bow_no_napkin, bow_no_back_covariate]
      have hmiss : ¬ missesForward bowGraph {Bow.x} ({Bow.y} ∪ (∅ : Finset Bow)) = true := by
        rw [bow_misses_forward]
        decide
      rw [if_neg hmiss]
      cases hpair : bowPair bowGraph bowEnum {Bow.u} {Bow.y} {Bow.x} with
      | none =>
          have hdata := bow_pair_vertices
          simp [hpair] at hdata
      | some hit =>
          have hdata := bow_pair_vertices
          simp [hpair] at hdata
          rcases hdata with ⟨hy, hxhit⟩
          dsimp
          simp [hy, hxhit, hedgeOfPair]
  rw [hcompute]
  unfold hedgeOfPair
  constructor <;> rfl

end Mettapedia.GSLT.Causality.DoCalculus
