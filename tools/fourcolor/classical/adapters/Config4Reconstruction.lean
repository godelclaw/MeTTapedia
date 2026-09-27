import FourColor.Pilot.EmbeddedReconstruction
import FourColor.Pilot.Cfg003
import FourColor.CfQuiz

/-!
# A contraction-dependent consumer of the reconstruction route

Configuration 4 of the classical catalogue has ring size eight and four
specified contract positions. Its checked certificate supplies the reducibility
field below. The geometry of its decoded map is supplied by `embeddable_cfquiz`.
Only the surrounding map, its embedding and a contract colouring remain inputs.
-/

namespace FourColor.Config4Reconstruction

open Hypermap
open Hypermap.EmbeddedReduction

theorem ring_size : cprsize cf004.prog = 8 := by decide +kernel

theorem contract_positions : cf004.contract = [1, 2, 12, 13] := rfl

theorem embeddable : (cfmap cf004).map.Embeddable (cfring cf004) :=
  embeddable_cfquiz (by exact ⟨trivial, trivial⟩)

theorem reducible : CfReducible cf004 :=
  Bulk.Cfg003.reducible 3 (by omega) (by omega)

variable {Dm : Type} [Finite Dm] {Gm : Hypermap Dm}
variable {h : (cfmap cf004).Dart → Dm}

omit [Finite Dm] in
/-- The semantic adapter consumes the actual checked classical certificate. -/
theorem reduction (hplan : Gm.Planar) (hplain : Gm.Plain)
    (hbridge : Gm.Bridgeless) (hconn : Gm.Connected) (hcubic : Gm.Cubic)
    (hbirk : Gm.BirkhoffRings) (hpent : Gm.Pentagonal)
    (hpre : Preembedding (cfmap cf004).map Gm h
      {z | (cfmap cf004).map.Kernel (cfring cf004) z}) :
    EmbeddedReduction (cfmap cf004).map Gm (cfring cf004) (cfcontract cf004) h :=
  ⟨embeddable, hplan, hplain, hbridge, hconn, hcubic, hbirk, hpent, hpre, reducible⟩

/-- A compatible construction route for configuration 4 in every admissible
surrounding map supplied with a contract colouring. -/
noncomputable def repair (hplan : Gm.Planar) (hplain : Gm.Plain)
    (hbridge : Gm.Bridgeless) (hconn : Gm.Connected) (hcubic : Gm.Cubic)
    (hbirk : Gm.BirkhoffRings) (hpent : Gm.Pentagonal)
    (hpre : Preembedding (cfmap cf004).map Gm h
      {z | (cfmap cf004).map.Kernel (cfring cf004) z})
    (k : ContractColor (Gc := (cfmap cf004).map) (Gm := Gm)
      (rc := cfring cf004) (cc := cfcontract cf004) (h := h)) :
    Σ z, (reduction hplan hplain hbridge hconn hcubic hbirk hpent hpre).semantics.Witness
      route k z :=
  let R := reduction hplan hplain hbridge hconn hcubic hbirk hpent hpre
  ⟨R.reconstruct k, R.routeWitness k⟩

#print axioms embeddable
#print axioms reducible
#print axioms repair

end FourColor.Config4Reconstruction
