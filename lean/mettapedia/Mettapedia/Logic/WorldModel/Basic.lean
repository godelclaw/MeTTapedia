/-!
# WorldModel: The Minimal General Interface and Hierarchy

The world-model class hierarchy, from most general to most specialized.

## Hierarchy

```
WorldModel (no laws)
  → MonoidalWorldModel (revision is a monoid)
    → AdditiveWorldModel (in PLNWorldModelGeneric.lean)
    → OverlapWorldModel (explicit overlap correction)
    → TrustGatedWorldModel (source-trust-weighted merge)
    → CoalitionWorldModel (semitopological consensus)
```

See `WorldModelClassWeb.md` for the full design rationale,
probability hypercube connection, and Pearl's SCM mapping.
-/

/-! ## Level 0: Minimal WorldModel (no laws) -/

/-- The minimal world-model interface: three typed operations, no laws.

    The relationship between `extract (revise W₁ W₂) q` and
    the individual extractions is NOT specified — it depends on
    the revision regime (additive, overlap, trust-gated, etc.). -/
class WorldModel (State : Type _) (Query : Type _) (V : Type _) where
  revise : State → State → State
  empty : State
  extract : State → Query → V

/-! ## Level 1: MonoidalWorldModel (revision is a monoid) -/

/-- Revision is associative with a unit (monoid structure). -/
class MonoidalWorldModel (State : Type _) (Query : Type _) (V : Type _)
    extends WorldModel State Query V where
  revise_assoc (a b c : State) : revise (revise a b) c = revise a (revise b c)
  revise_empty_left (a : State) : revise empty a = a
  revise_empty_right (a : State) : revise a empty = a

/-! ## Level 2a: OverlapWorldModel -/

/-- Extraction with explicit overlap/correlation correction.

    `extract(revise(W₁,W₂), q) = combine(extract W₁ q, extract W₂ q, overlap W₁ W₂ q)`

    This interface includes observation-identity overlap corrections. A
    Dempster-Shafer interpretation requires its own construction and laws. -/
class OverlapWorldModel (State : Type _) (Query : Type _) (V : Type _) (Ov : Type _)
    extends MonoidalWorldModel State Query V where
  overlap : State → State → Query → Ov
  combine : V → V → Ov → V
  extract_revise (W₁ W₂ : State) (q : Query) :
    extract (revise W₁ W₂) q = combine (extract W₁ q) (extract W₂ q) (overlap W₁ W₂ q)

/-! ## Level 2b: TrustGatedWorldModel -/

/-- Trust metadata and an additional candidate merge operation.

The inherited `revise` is monoidal. No law here identifies `gatedRevise`
with it or establishes monotonicity in trust; such laws belong to a concrete
interpretation. -/
class TrustGatedWorldModel (State : Type _) (Query : Type _) (V : Type _) (Trust : Type _)
    extends MonoidalWorldModel State Query V where
  trust : State → Trust
  gatedRevise : State → State → State

/-! ## Level 2c: CoalitionWorldModel -/

/-- A compatibility predicate and a merge defined on compatible pairs.

The relation to the inherited monoidal revision, or to a coalition topology,
is additional structure rather than an automatic consequence of these fields. -/
class CoalitionWorldModel (State : Type _) (Query : Type _) (V : Type _)
    extends MonoidalWorldModel State Query V where
  actionable : State → State → Prop
  coalitionRevise : (W₁ W₂ : State) → actionable W₁ W₂ → State
