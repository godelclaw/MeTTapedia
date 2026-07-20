import Mettapedia.GraphTheory.FourColor.ClassicalCertificateTraceTree

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateColorTrace

/-- Consecutive color differences, beginning with the supplied previous
color.  Addition is subtraction in the exponent-two Tait color group. -/
def differenceTail (previous : Color) : List Color → List Color
  | [] => []
  | current :: rest =>
      (previous + current) :: differenceTail current rest

/-- The linear trace of a color word. -/
def partialTrace : List Color → List Color
  | [] => []
  | first :: rest => differenceTail first rest

/-- Complete a linear trace to a cyclic trace by appending its group sum. -/
def completeTrace (tail : List Color) : List Color :=
  tail ++ [tail.sum]

/-- The cyclic boundary trace.  The empty color word has empty trace. -/
def trace : List Color → List Color
  | [] => []
  | first :: rest => completeTrace (partialTrace (first :: rest))

@[simp] theorem differenceTail_nil (previous : Color) :
    differenceTail previous [] = [] := rfl

@[simp] theorem differenceTail_cons (previous current : Color)
    (rest : List Color) :
    differenceTail previous (current :: rest) =
      (previous + current) :: differenceTail current rest := rfl

theorem length_differenceTail (previous : Color) (rest : List Color) :
    (differenceTail previous rest).length = rest.length := by
  induction rest generalizing previous with
  | nil => rfl
  | cons current rest ih => simp [differenceTail, ih]

theorem length_partialTrace : ∀ colors : List Color,
    (partialTrace colors).length = colors.length - 1
  | [] => rfl
  | first :: rest => by
      simp [partialTrace, length_differenceTail]

@[simp] theorem sum_completeTrace (tail : List Color) :
    (completeTrace tail).sum = 0 := by
  simp [completeTrace]

@[simp] theorem sum_trace (colors : List Color) :
    (trace colors).sum = 0 := by
  cases colors <;> simp [trace]

theorem length_completeTrace (tail : List Color) :
    (completeTrace tail).length = tail.length + 1 := by
  simp [completeTrace]

theorem length_trace : ∀ colors : List Color,
    (trace colors).length = colors.length
  | [] => rfl
  | first :: rest => by
      simp [trace, length_completeTrace, length_partialTrace]

/-- The sum of consecutive differences telescopes to the first plus last
color.  For a singleton word this is `first + first = 0`. -/
theorem sum_differenceTail (first : Color) : ∀ rest : List Color,
    (differenceTail first rest).sum = first + rest.getLastD first
  | [] => by simp
  | current :: rest => by
      rw [differenceTail_cons, List.sum_cons,
        sum_differenceTail current rest]
      simp only [List.getLastD_cons]
      calc
        first + current + (current + rest.getLastD current) =
            first + (current + current) + rest.getLastD current := by abel
        _ = first + rest.getLastD current := by simp

theorem sum_partialTrace_cons (first : Color) (rest : List Color) :
    (partialTrace (first :: rest)).sum = first + rest.getLastD first := by
  exact sum_differenceTail first rest

/-- Adjacent entries of a linear word are distinct. -/
def AdjacentDistinct : List Color → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      first ≠ second ∧ AdjacentDistinct (second :: rest)

theorem mem_differenceTail_ne_zero
    (first : Color) : ∀ {rest : List Color},
      AdjacentDistinct (first :: rest) →
      ∀ color ∈ differenceTail first rest, color ≠ 0
  | [], _, color, hmem => by simp at hmem
  | second :: rest, hadjacent, color, hmem => by
      simp only [AdjacentDistinct] at hadjacent
      simp only [differenceTail, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact add_ne_zero_of_ne hadjacent.1
      · exact mem_differenceTail_ne_zero second hadjacent.2 color htail

theorem mem_partialTrace_ne_zero
    {colors : List Color} (hadjacent : AdjacentDistinct colors) :
    ∀ color ∈ partialTrace colors, color ≠ 0 := by
  cases colors with
  | nil => intro color hmem; simp [partialTrace] at hmem
  | cons first rest =>
      exact mem_differenceTail_ne_zero first hadjacent

/-- A nonempty cyclic word is proper when consecutive colors differ and the
last color differs from the first. -/
def CyclicallyDistinct : List Color → Prop
  | [] => True
  | first :: rest =>
      AdjacentDistinct (first :: rest) ∧ rest.getLastD first ≠ first

theorem mem_completeTrace_ne_zero
    {first : Color} {rest : List Color}
    (hcyclic : CyclicallyDistinct (first :: rest)) :
    ∀ color ∈ completeTrace (partialTrace (first :: rest)), color ≠ 0 := by
  intro color hmem
  simp only [completeTrace, List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hpartial | rfl
  · exact mem_partialTrace_ne_zero hcyclic.1 color hpartial
  · rw [sum_partialTrace_cons]
    exact add_ne_zero_of_ne hcyclic.2.symm

theorem mem_trace_ne_zero {colors : List Color}
    (hcyclic : CyclicallyDistinct colors) :
    ∀ color ∈ trace colors, color ≠ 0 := by
  cases colors with
  | nil => intro color hmem; simp [trace] at hmem
  | cons first rest =>
      exact mem_completeTrace_ne_zero hcyclic

/-- A proper cyclic color word therefore has a unique normalized spelling over
the three trace symbols. -/
theorem existsUnique_traceSymbolWord {colors : List Color}
    (hcyclic : CyclicallyDistinct colors) :
    ∃! symbols : List ClassicalCertificateTraceTree.TraceSymbol,
      symbols.map
        ClassicalCertificateTraceTree.TraceSymbol.toColor = trace colors :=
  ClassicalCertificateTraceTree.TraceSymbol.existsUnique_word_toColor_eq
    (trace colors) (mem_trace_ne_zero hcyclic)

end ClassicalCertificateColorTrace

end Mettapedia.GraphTheory.FourColor
