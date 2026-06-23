import Mettapedia.GraphTheory.FourColor.RotationSystem

namespace Mettapedia.GraphTheory.FourColor.NoDigonsCounterexample

open RotationSystem

/-- Vertices of a theta graph: two poles joined by three internally disjoint
length-two paths. -/
inductive ThetaV
  | u
  | v
  | a
  | b
  | c
  deriving DecidableEq, Repr

instance : Fintype ThetaV where
  elems := {ThetaV.u, ThetaV.v, ThetaV.a, ThetaV.b, ThetaV.c}
  complete := by
    intro x
    cases x <;> simp

/-- Six edges of the theta graph. -/
inductive ThetaE
  | e1
  | e2
  | e3
  | e4
  | e5
  | e6
  deriving DecidableEq, Repr

instance : Fintype ThetaE where
  elems := {ThetaE.e1, ThetaE.e2, ThetaE.e3, ThetaE.e4, ThetaE.e5, ThetaE.e6}
  complete := by
    intro x
    cases x <;> simp

/-- Darts of the theta graph, named by edge and incident vertex. -/
inductive ThetaD
  | e1_u | e1_a
  | e2_a | e2_v
  | e3_u | e3_b
  | e4_b | e4_v
  | e5_u | e5_c
  | e6_c | e6_v
  deriving DecidableEq, Repr

instance : Fintype ThetaD where
  elems :=
    {ThetaD.e1_u, ThetaD.e1_a, ThetaD.e2_a, ThetaD.e2_v,
     ThetaD.e3_u, ThetaD.e3_b, ThetaD.e4_b, ThetaD.e4_v,
     ThetaD.e5_u, ThetaD.e5_c, ThetaD.e6_c, ThetaD.e6_v}
  complete := by
    intro x
    cases x <;> simp

open ThetaV ThetaE ThetaD

def thetaEdgeOf : ThetaD → ThetaE
  | e1_u => e1 | e1_a => e1
  | e2_a => e2 | e2_v => e2
  | e3_u => e3 | e3_b => e3
  | e4_b => e4 | e4_v => e4
  | e5_u => e5 | e5_c => e5
  | e6_c => e6 | e6_v => e6

def thetaVertOf : ThetaD → ThetaV
  | e1_u => u | e3_u => u | e5_u => u
  | e2_v => v | e4_v => v | e6_v => v
  | e1_a => a | e2_a => a
  | e3_b => b | e4_b => b
  | e5_c => c | e6_c => c

def thetaAlphaFn : ThetaD → ThetaD
  | e1_u => e1_a | e1_a => e1_u
  | e2_a => e2_v | e2_v => e2_a
  | e3_u => e3_b | e3_b => e3_u
  | e4_b => e4_v | e4_v => e4_b
  | e5_u => e5_c | e5_c => e5_u
  | e6_c => e6_v | e6_v => e6_c

def thetaAlpha : Equiv.Perm ThetaD where
  toFun := thetaAlphaFn
  invFun := thetaAlphaFn
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl

def thetaRhoFn : ThetaD → ThetaD
  | e1_u => e3_u | e3_u => e5_u | e5_u => e1_u
  | e2_v => e6_v | e6_v => e4_v | e4_v => e2_v
  | e1_a => e2_a | e2_a => e1_a
  | e3_b => e4_b | e4_b => e3_b
  | e5_c => e6_c | e6_c => e5_c

def thetaRhoInvFn : ThetaD → ThetaD
  | e1_u => e5_u | e3_u => e1_u | e5_u => e3_u
  | e2_v => e4_v | e6_v => e2_v | e4_v => e6_v
  | e1_a => e2_a | e2_a => e1_a
  | e3_b => e4_b | e4_b => e3_b
  | e5_c => e6_c | e6_c => e5_c

def thetaRho : Equiv.Perm ThetaD where
  toFun := thetaRhoFn
  invFun := thetaRhoInvFn
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl

theorem theta_edge_fiber_two (e : ThetaE) :
    (Finset.univ.filter (fun d => thetaEdgeOf d = e)).card = 2 := by
  cases e <;> decide

theorem theta_vert_rho : ∀ d, thetaVertOf (thetaRho d) = thetaVertOf d := by
  intro d
  cases d <;> rfl

theorem theta_no_self_loops :
    ∀ d, thetaVertOf d ≠ thetaVertOf (thetaAlpha d) := by
  intro d
  cases d <;> decide

/-- The theta graph as a bare rotation system. -/
def thetaRotationSystem : RotationSystem ThetaV ThetaE where
  D := ThetaD
  edgeOf := thetaEdgeOf
  vertOf := thetaVertOf
  alpha := thetaAlpha
  rho := thetaRho
  alpha_involutive := by intro d; cases d <;> rfl
  alpha_fixfree := by intro d; cases d <;> decide
  edge_alpha := by intro d; cases d <;> rfl
  edge_fiber_two := theta_edge_fiber_two
  vert_rho := theta_vert_rho
  outer := e1_u
  no_self_loops := theta_no_self_loops

/-- The theta graph refutes the naive claim that the bare rotation-system data
enforces no interior digons. -/
theorem theta_not_noInteriorDigons :
    ¬ thetaRotationSystem.NoInteriorDigons := by
  intro h_no_digons
  let RS := thetaRotationSystem
  let f1 := RS.faceEdges e3_u
  let f2 := RS.faceEdges e5_u

  have hf1_int : f1 ∈ RS.internalFaces := by decide
  have hf2_int : f2 ∈ RS.internalFaces := by decide
  have h_diff : f1 ≠ f2 := by decide

  have he3_f1 : e3 ∈ f1 := by decide
  have he3_f2 : e3 ∈ f2 := by decide
  have he4_f1 : e4 ∈ f1 := by decide
  have he4_f2 : e4 ∈ f2 := by decide

  have he3_int : e3 ∉ RS.boundaryEdges := by decide
  have he4_int : e4 ∉ RS.boundaryEdges := by decide
  have he3_ne_e4 : e3 ≠ e4 := by decide

  exact h_no_digons hf1_int hf2_int h_diff he3_ne_e4
    he3_int he4_int he3_f1 he3_f2 he4_f1 he4_f2

end Mettapedia.GraphTheory.FourColor.NoDigonsCounterexample
