import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Exchanging two walk tails at a shared vertex

Two walks that meet at a vertex can exchange their suffixes there.  The two
new walks preserve the sum of the original lengths.  This is the graph-level
uncrossing atom used by the geometry-sensitive L6 curvature pairing; it makes
no planar or simplicity claim by itself.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WalkTailExchange

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
  {firstStart firstFinish secondStart secondFinish common : V}

/-- Follow the first walk to the common vertex, then the second walk's tail. -/
def firstExchange
    (first : G.Walk firstStart firstFinish)
    (second : G.Walk secondStart secondFinish)
    (hfirst : common ∈ first.support) (hsecond : common ∈ second.support) :
    G.Walk firstStart secondFinish :=
  (first.takeUntil common hfirst).append (second.dropUntil common hsecond)

/-- Follow the second walk to the common vertex, then the first walk's tail. -/
def secondExchange
    (first : G.Walk firstStart firstFinish)
    (second : G.Walk secondStart secondFinish)
    (hfirst : common ∈ first.support) (hsecond : common ∈ second.support) :
    G.Walk secondStart firstFinish :=
  (second.takeUntil common hsecond).append (first.dropUntil common hfirst)

@[simp]
theorem firstExchange_length
    (first : G.Walk firstStart firstFinish)
    (second : G.Walk secondStart secondFinish)
    (hfirst : common ∈ first.support) (hsecond : common ∈ second.support) :
    (firstExchange first second hfirst hsecond).length =
      (first.takeUntil common hfirst).length +
        (second.dropUntil common hsecond).length := by
  simp [firstExchange]

@[simp]
theorem secondExchange_length
    (first : G.Walk firstStart firstFinish)
    (second : G.Walk secondStart secondFinish)
    (hfirst : common ∈ first.support) (hsecond : common ∈ second.support) :
    (secondExchange first second hfirst hsecond).length =
      (second.takeUntil common hsecond).length +
        (first.dropUntil common hfirst).length := by
  simp [secondExchange]

/-- Exchanging tails preserves the total length of the two walks exactly. -/
theorem firstExchange_length_add_secondExchange_length
    (first : G.Walk firstStart firstFinish)
    (second : G.Walk secondStart secondFinish)
    (hfirst : common ∈ first.support) (hsecond : common ∈ second.support) :
    (firstExchange first second hfirst hsecond).length +
        (secondExchange first second hfirst hsecond).length =
      first.length + second.length := by
  have hfirstSplit := congrArg Walk.length (first.take_spec hfirst)
  have hsecondSplit := congrArg Walk.length (second.take_spec hsecond)
  simp only [Walk.length_append] at hfirstSplit hsecondSplit
  simp only [firstExchange_length, secondExchange_length]
  omega

/-- A shared vertex gives the crossed endpoint pairing no greater total
distance than the lengths of the two displayed walks. -/
theorem dist_add_dist_le_length_add_length_of_shared_vertex
    (first : G.Walk firstStart firstFinish)
    (second : G.Walk secondStart secondFinish)
    (hfirst : common ∈ first.support) (hsecond : common ∈ second.support) :
    G.dist firstStart secondFinish + G.dist secondStart firstFinish ≤
      first.length + second.length := by
  calc
    G.dist firstStart secondFinish + G.dist secondStart firstFinish ≤
        (firstExchange first second hfirst hsecond).length +
          (secondExchange first second hfirst hsecond).length :=
      Nat.add_le_add (dist_le _) (dist_le _)
    _ = first.length + second.length :=
      firstExchange_length_add_secondExchange_length first second
        hfirst hsecond

/-- In particular, intersecting geodesics satisfy the metric uncrossing
inequality for the exchanged endpoint pairing. -/
theorem dist_add_dist_le_dist_add_dist_of_geodesics_shared_vertex
    (first : G.Walk firstStart firstFinish)
    (second : G.Walk secondStart secondFinish)
    (hfirst : common ∈ first.support) (hsecond : common ∈ second.support)
    (hfirstGeodesic : first.length = G.dist firstStart firstFinish)
    (hsecondGeodesic : second.length = G.dist secondStart secondFinish) :
    G.dist firstStart secondFinish + G.dist secondStart firstFinish ≤
      G.dist firstStart firstFinish + G.dist secondStart secondFinish := by
  simpa [hfirstGeodesic, hsecondGeodesic] using
    dist_add_dist_le_length_add_length_of_shared_vertex first second
      hfirst hsecond

end GoertzelV24WalkTailExchange

end Mettapedia.GraphTheory.FourColor
