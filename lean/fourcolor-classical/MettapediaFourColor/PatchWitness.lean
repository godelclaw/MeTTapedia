import FourColor.Patch

/-!
# Colouring witnesses retained by geometric gluing

This exposes the witness construction inside the classical patch theorem of
Gonthier and Werner, following Chris Emery's Lean formalization. The resulting
colour function reads back the supplied assignments on both pieces. It uses
the same geometric patch hypotheses and does not invoke the Four Colour Theorem.
-/

namespace FourColor

private theorem scanl_shift (c c₀ : Color) (l : List Color) :
    List.scanl (· + ·) (c + c₀) l = (List.scanl (· + ·) c₀ l).map (c + ·) := by
  induction l generalizing c₀ with
  | nil => rfl
  | cons x l ih => rw [List.scanl_cons, List.scanl_cons, List.map_cons, add_assoc, ih]

private theorem untrace_shift (c c₀ : Color) (et : List Color) :
    untrace (c + c₀) et = (untrace c₀ et).map (c + ·) := by
  match et with
  | [] => rfl
  | e :: t =>
    change List.scanl (· + ·) (c + c₀) (e :: t).dropLast =
      (List.scanl (· + ·) c₀ (e :: t).dropLast).map (c + ·)
    rw [scanl_shift]

/-- Equal edge traces determine vertex colours up to one constant shift. -/
theorem ringColors_eq_shift : ∀ {A B : List Color}, A.length = B.length →
    trace A = trace B → B = A.map ((A.headD 0 + B.headD 0) + ·)
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | a :: A', b :: B', _, h => by
    simp only [List.headD_cons]
    have hab : a + b + a = b := by
      rw [add_right_comm, Color.add_self, zero_add]
    calc b :: B' = untrace b (trace (b :: B')) := (untrace_trace b B').symm
      _ = untrace (a + b + a) (trace (a :: A')) := by rw [hab, h]
      _ = (untrace a (trace (a :: A'))).map ((a + b) + ·) := untrace_shift _ _ _
      _ = (a :: A').map ((a + b) + ·) := by rw [untrace_trace]

namespace Patch

variable {D Dd Dr : Type*}
variable {G : Hypermap D} {Gd : Hypermap Dd} {Gr : Hypermap Dr}
variable {hd : Dd → D} {hr : Dr → D} {bd : List Dd} {br : List Dr}

/-- Glue specified assignments, giving the remainder priority on the overlap.
The patch hypotheses and ring agreement will make this priority immaterial. -/
noncomputable def gluedColor (hd : Dd → D) (hr : Dr → D)
    (kd : Dd → Color) (kr : Dr → Color) (x : D) : Color := by
  classical
  exact if h : ∃ xr, hr xr = x then kr h.choose
    else if h' : ∃ xd, hd xd = x then kd h'.choose else 0

theorem gluedColor_remainder (P : Patch G Gd Gr hd hr bd br)
    (kd : Dd → Color) (kr : Dr → Color) (xr : Dr) :
    gluedColor hd hr kd kr (hr xr) = kr xr := by
  classical
  unfold gluedColor
  have hex : ∃ yr, hr yr = hr xr := ⟨xr, rfl⟩
  rw [dite_eq_left hex]
  exact congrArg kr (P.injr hex.choose_spec)

theorem gluedColor_disk (P : Patch G Gd Gr hd hr bd br)
    {kd : Dd → Color} {kr : Dr → Color}
    (hring : (bd.map kd).reverse = br.map kr) (xd : Dd) :
    gluedColor hd hr kd kr (hd xd) = kd xd := by
  classical
  unfold gluedColor
  by_cases hex : ∃ yr, hr yr = hd xd
  · rw [dite_eq_left hex]
    exact (P.eq_of_ring_eq hring hex.choose_spec.symm).symm
  · rw [dite_eq_right hex]
    have hex' : ∃ yd, hd yd = hd xd := ⟨xd, rfl⟩
    rw [dite_eq_left hex']
    exact congrArg kd (P.injd hex'.choose_spec)

/-- The explicit glued assignment is a colouring of the ambient map. -/
theorem gluedColor_valid [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br)
    {kd : Dd → Color} {kr : Dr → Color}
    (hkd : Gd.Coloring kd) (hkr : Gr.Coloring kr)
    (hring : (bd.map kd).reverse = br.map kr) :
    G.Coloring (gluedColor hd hr kd kr) := by
  classical
  have heq : ∀ xd xr, hd xd = hr xr → kd xd = kr xr :=
    fun xd xr hx => P.eq_of_ring_eq hring hx
  have hd_read := P.gluedColor_disk hring
  have hr_read := P.gluedColor_remainder kd kr
  constructor
  · intro x
    by_cases hxr : x ∈ Set.range hr
    · obtain ⟨xr, rfl⟩ := hxr
      rw [← P.edge_r, hr_read, hr_read]
      exact hkr.edge xr
    · obtain ⟨xd, rfl⟩ := (P.mem_range_or x).resolve_right hxr
      have hxd : xd ∉ bd := fun hb => hxr ((P.mem_bd_iff xd).mpr hb)
      rw [← P.edge_d hxd, hd_read, hd_read]
      exact hkd.edge xd
  · intro x
    by_cases hxr : x ∈ Set.range hr
    · obtain ⟨xr, rfl⟩ := hxr
      by_cases hfx : Gr.face xr ∈ br
      · obtain ⟨xd, h1, h2⟩ := P.face_hr_of_mem_br hfx
        rw [h2, hd_read, hkd.face, hr_read]
        exact (heq _ _ h1).trans (hkr.face xr)
      · rw [← P.face_r hfx, hr_read, hr_read]
        exact hkr.face xr
    · obtain ⟨xd, rfl⟩ := (P.mem_range_or x).resolve_right hxr
      have hxd : xd ∉ bd := fun hb => hxr ((P.mem_bd_iff xd).mpr hb)
      rw [← P.face_d hxd, hd_read, hd_read]
      exact hkd.face xd

/-- Gluing has at most one result once both assignments are fixed. -/
theorem gluedColor_unique (P : Patch G Gd Gr hd hr bd br)
    {kd : Dd → Color} {kr : Dr → Color}
    (hring : (bd.map kd).reverse = br.map kr) {k : D → Color}
    (hd_read : ∀ xd, k (hd xd) = kd xd) (hr_read : ∀ xr, k (hr xr) = kr xr) :
    k = gluedColor hd hr kd kr := by
  funext x
  rcases P.mem_range_or x with ⟨xd, rfl⟩ | ⟨xr, rfl⟩
  · exact (hd_read xd).trans (P.gluedColor_disk hring xd).symm
  · exact (hr_read xr).trans (P.gluedColor_remainder kd kr xr).symm

/-- A canonical shift aligning the two boundary assignments. -/
def ringShift (bd : List Dd) (br : List Dr) (kd : Dd → Color) (kr : Dr → Color) :
    Color := ((bd.map kd).reverse).headD 0 + (br.map kr).headD 0

theorem shifted_ring (P : Patch G Gd Gr hd hr bd br)
    {kd : Dd → Color} {kr : Dr → Color}
    (htrace : trace ((bd.map kd).reverse) = trace (br.map kr)) :
    (bd.map (fun xd => ringShift bd br kd kr + kd xd)).reverse = br.map kr := by
  have hlen : ((bd.map kd).reverse).length = (br.map kr).length := by
    simp [P.length_br]
  have same := ringColors_eq_shift hlen htrace
  have hmap : bd.map (fun xd => ringShift bd br kd kr + kd xd) =
      (bd.map kd).map (ringShift bd br kd kr + ·) := by rw [List.map_map]; rfl
  rw [hmap, ← List.map_reverse]
  exact same.symm

/-- Glue matching traces by aligning the disk with the supplied remainder. -/
noncomputable def gluedTraceColor (hd : Dd → D) (hr : Dr → D)
    (bd : List Dd) (br : List Dr) (kd : Dd → Color) (kr : Dr → Color) : D → Color :=
  gluedColor hd hr (fun xd => ringShift bd br kd kr + kd xd) kr

theorem gluedTraceColor_valid [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br)
    {kd : Dd → Color} {kr : Dr → Color}
    (hkd : Gd.Coloring kd) (hkr : Gr.Coloring kr)
    (htrace : trace ((bd.map kd).reverse) = trace (br.map kr)) :
    G.Coloring (gluedTraceColor hd hr bd br kd kr) :=
  P.gluedColor_valid (hkd.comp (add_right_injective (ringShift bd br kd kr)))
    hkr (P.shifted_ring htrace)

theorem gluedTraceColor_remainder (P : Patch G Gd Gr hd hr bd br)
    (kd : Dd → Color) (kr : Dr → Color) (xr : Dr) :
    gluedTraceColor hd hr bd br kd kr (hr xr) = kr xr :=
  P.gluedColor_remainder _ _ xr

theorem gluedTraceColor_disk (P : Patch G Gd Gr hd hr bd br)
    {kd : Dd → Color} {kr : Dr → Color}
    (htrace : trace ((bd.map kd).reverse) = trace (br.map kr)) (xd : Dd) :
    gluedTraceColor hd hr bd br kd kr (hd xd) = ringShift bd br kd kr + kd xd :=
  P.gluedColor_disk (P.shifted_ring htrace) xd

#print axioms gluedColor_valid
#print axioms gluedColor_unique
#print axioms gluedTraceColor_valid
#print axioms gluedTraceColor_remainder
#print axioms gluedTraceColor_disk

/-- The two actual assignments and their common boundary trace. -/
structure TraceMatch (Gd : Hypermap Dd) (Gr : Hypermap Dr)
    (bd : List Dd) (br : List Dr) where
  disk : Dd → Color
  remainder : Dr → Color
  disk_valid : Gd.Coloring disk
  remainder_valid : Gr.Coloring remainder
  boundary : trace ((bd.map disk).reverse) = trace (br.map remainder)

/-- Reconstruct an actual colouring while retaining its two source assignments. -/
noncomputable def TraceMatch.glue [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br) (m : TraceMatch Gd Gr bd br) :
    {k : D → Color // G.Coloring k} :=
  ⟨gluedTraceColor hd hr bd br m.disk m.remainder,
    P.gluedTraceColor_valid m.disk_valid m.remainder_valid m.boundary⟩

theorem TraceMatch.glue_remainder [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br) (m : TraceMatch Gd Gr bd br) (x : Dr) :
    (m.glue P).val (hr x) = m.remainder x :=
  P.gluedTraceColor_remainder m.disk m.remainder x

theorem TraceMatch.glue_disk [Finite D] [Finite Dd] [Finite Dr]
    (P : Patch G Gd Gr hd hr bd br) (m : TraceMatch Gd Gr bd br) (x : Dd) :
    (m.glue P).val (hd x) = ringShift bd br m.disk m.remainder + m.disk x :=
  P.gluedTraceColor_disk m.boundary x

end Patch
end FourColor
