import Mettapedia.Languages.C11.ReadExpressionExecution

/-!
# Plain data for retained integer-expression configurations

The data representation removes value-range proof fields and checks their
mathematical contents on decoding. Memory retains ordered allocation records,
initialized or indeterminate bytes, object metadata and lexical frames.
Expression and context codecs retain all branches and every continuation
field without a nesting limit. Configuration data includes remaining choices
and the next occurrence ordinal.

Decoding establishes representability, not C declaration validity, execution
history, external ownership or publication authority. Executable represented
choice operations are connected to the independent contextual reductions.
Full ordinary-C and Cesta expression elaboration remains a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ReadExpression

open ObjectAccessMemory

structure ScalarData where
  type : IntegerType IntegerExtension
  integer : Int
  deriving DecidableEq, Repr

def encodeScalar {layout : Layout} (scalar : IntegerScalar.Value layout.parameters) : ScalarData :=
  ⟨scalar.type, scalar.integer.value⟩

def decodeScalar (layout : Layout) (data : ScalarData) : Option (IntegerScalar.Value layout.parameters) :=
  (IntegerStep.decodeValue (data.type.format layout.parameters) data.integer).map fun value => ⟨data.type, value⟩

theorem decodeScalar_encode (layout : Layout) (scalar : IntegerScalar.Value layout.parameters) :
    decodeScalar layout (encodeScalar scalar) = some scalar := by
  cases scalar
  simp only [decodeScalar, encodeScalar, IntegerStep.decodeValue_encode, Option.map_some]

theorem encodeScalar_decode (layout : Layout) (data : ScalarData)
    (scalar : IntegerScalar.Value layout.parameters) (decoded : decodeScalar layout data = some scalar) :
    encodeScalar scalar = data := by
  obtain ⟨value, accepted, rfl⟩ := Option.map_eq_some_iff.mp decoded
  cases data
  exact congrArg (ScalarData.mk _) (IntegerStep.value_decode _ _ _ accepted)

inductive ExpressionData where
  | value (scalar : ScalarData)
  | read (name : String)
  | arithmetic (operation : IntegerBinaryOperator) (first second : ExpressionData)
  | cast (type : IntegerType IntegerExtension) (operand : ExpressionData)
  | truth (operand : ExpressionData)
  | logicalNot (operand : ExpressionData)
  | logicalAnd (first second : ExpressionData)
  | logicalOr (first second : ExpressionData)
  | conditional (type : IntegerType IntegerExtension) (test first second : ExpressionData)
  | comma (first second : ExpressionData)
  | fault (reason : Fault)
  deriving DecidableEq, Repr

def encodeExpression {layout : Layout} : Expression layout → ExpressionData
  | .value scalar => .value (encodeScalar scalar)
  | .read name => .read name
  | .arithmetic operation first second => .arithmetic operation (encodeExpression first) (encodeExpression second)
  | .cast type operand => .cast type (encodeExpression operand)
  | .truth operand => .truth (encodeExpression operand)
  | .logicalNot operand => .logicalNot (encodeExpression operand)
  | .logicalAnd first second => .logicalAnd (encodeExpression first) (encodeExpression second)
  | .logicalOr first second => .logicalOr (encodeExpression first) (encodeExpression second)
  | .conditional type test first second =>
      .conditional type (encodeExpression test) (encodeExpression first) (encodeExpression second)
  | .comma first second => .comma (encodeExpression first) (encodeExpression second)
  | .fault reason => .fault reason

def decodeExpression (layout : Layout) : ExpressionData → Option (Expression layout)
  | .value scalar => (decodeScalar layout scalar).map Expression.value
  | .read name => some (.read name)
  | .arithmetic operation first second => do
      let left ← decodeExpression layout first
      let right ← decodeExpression layout second
      some (.arithmetic operation left right)
  | .cast type operand => do some (.cast type (← decodeExpression layout operand))
  | .truth operand => do some (.truth (← decodeExpression layout operand))
  | .logicalNot operand => do some (.logicalNot (← decodeExpression layout operand))
  | .logicalAnd first second => do some (.logicalAnd (← decodeExpression layout first) (← decodeExpression layout second))
  | .logicalOr first second => do some (.logicalOr (← decodeExpression layout first) (← decodeExpression layout second))
  | .conditional type test first second => do
      some (.conditional type (← decodeExpression layout test) (← decodeExpression layout first) (← decodeExpression layout second))
  | .comma first second => do some (.comma (← decodeExpression layout first) (← decodeExpression layout second))
  | .fault reason => some (.fault reason)

theorem decodeExpression_encode (layout : Layout) (expression : Expression layout) :
    decodeExpression layout (encodeExpression expression) = some expression := by
  induction expression <;>
    simp_all only [encodeExpression, decodeExpression, decodeScalar_encode, Option.map_some, bind, Option.bind_some]

theorem encodeExpression_decode (layout : Layout) (data : ExpressionData)
    (expression : Expression layout) (decoded : decodeExpression layout data = some expression) :
    encodeExpression expression = data := by
  induction data generalizing expression with
  | value scalar =>
      obtain ⟨value, accepted, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg ExpressionData.value (encodeScalar_decode layout scalar value accepted)
  | read name => cases decoded; rfl
  | fault reason => cases decoded; rfl
  | arithmetic operation first second ihFirst ihSecond =>
      simp only [decodeExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨left, firstRead, right, secondRead, rfl⟩ := decoded
      simp only [encodeExpression, ihFirst left firstRead, ihSecond right secondRead]
  | cast type operand ih =>
      simp only [decodeExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨value, accepted, rfl⟩ := decoded
      simp only [encodeExpression, ih value accepted]
  | truth operand ih =>
      simp only [decodeExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨value, accepted, rfl⟩ := decoded
      simp only [encodeExpression, ih value accepted]
  | logicalNot operand ih =>
      simp only [decodeExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨value, accepted, rfl⟩ := decoded
      simp only [encodeExpression, ih value accepted]
  | logicalAnd first second ihFirst ihSecond =>
      simp only [decodeExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨left, firstRead, right, secondRead, rfl⟩ := decoded
      simp only [encodeExpression, ihFirst left firstRead, ihSecond right secondRead]
  | logicalOr first second ihFirst ihSecond =>
      simp only [decodeExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨left, firstRead, right, secondRead, rfl⟩ := decoded
      simp only [encodeExpression, ihFirst left firstRead, ihSecond right secondRead]
  | conditional type test first second ihTest ihFirst ihSecond =>
      simp only [decodeExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨guard, testRead, left, firstRead, right, secondRead, rfl⟩ := decoded
      simp only [encodeExpression, ihTest guard testRead, ihFirst left firstRead, ihSecond right secondRead]
  | comma first second ihFirst ihSecond =>
      simp only [decodeExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨left, firstRead, right, secondRead, rfl⟩ := decoded
      simp only [encodeExpression, ihFirst left firstRead, ihSecond right secondRead]

inductive FrameData where
  | arithmeticLeft (operation : IntegerBinaryOperator) (second : ExpressionData)
  | arithmeticRight (operation : IntegerBinaryOperator) (first : ExpressionData)
  | cast (type : IntegerType IntegerExtension)
  | truth
  | logicalNot
  | logicalAnd (second : ExpressionData)
  | logicalOr (second : ExpressionData)
  | conditional (type : IntegerType IntegerExtension) (first second : ExpressionData)
  | comma (second : ExpressionData)
  deriving DecidableEq, Repr

def encodeFrame {layout : Layout} : Frame layout → FrameData
  | .arithmeticLeft operation second => .arithmeticLeft operation (encodeExpression second)
  | .arithmeticRight operation first => .arithmeticRight operation (encodeExpression first)
  | .cast type => .cast type
  | .truth => .truth
  | .logicalNot => .logicalNot
  | .logicalAnd second => .logicalAnd (encodeExpression second)
  | .logicalOr second => .logicalOr (encodeExpression second)
  | .conditional type first second => .conditional type (encodeExpression first) (encodeExpression second)
  | .comma second => .comma (encodeExpression second)

def decodeFrame (layout : Layout) : FrameData → Option (Frame layout)
  | .arithmeticLeft operation second => do some (.arithmeticLeft operation (← decodeExpression layout second))
  | .arithmeticRight operation first => do some (.arithmeticRight operation (← decodeExpression layout first))
  | .cast type => some (.cast type)
  | .truth => some .truth
  | .logicalNot => some .logicalNot
  | .logicalAnd second => do some (.logicalAnd (← decodeExpression layout second))
  | .logicalOr second => do some (.logicalOr (← decodeExpression layout second))
  | .conditional type first second => do
      some (.conditional type (← decodeExpression layout first) (← decodeExpression layout second))
  | .comma second => do some (.comma (← decodeExpression layout second))

theorem decodeFrame_encode (layout : Layout) (frame : Frame layout) :
    decodeFrame layout (encodeFrame frame) = some frame := by
  cases frame <;> simp only [encodeFrame, decodeFrame, decodeExpression_encode, bind, Option.bind_some]

def encodeContext {layout : Layout} (context : Context layout) : List FrameData := context.map encodeFrame

def decodeContext (layout : Layout) (context : List FrameData) : Option (Context layout) := context.mapM (decodeFrame layout)

theorem decodeContext_encode (layout : Layout) (context : Context layout) :
    decodeContext layout (encodeContext context) = some context := by
  induction context with
  | nil => rfl
  | cons frame rest ih =>
      simp only [encodeContext, decodeContext, List.map_cons, List.mapM_cons, decodeFrame_encode, bind,
        Option.bind_some] at ih ⊢
      rw [ih]
      rfl

structure EventData where
  context : List FrameData
  observation : Observation
  deriving DecidableEq, Repr

def encodeEvent {layout : Layout} (observed : Event layout) : EventData :=
  ⟨encodeContext observed.context, observed.observation⟩

def decodeEvent (layout : Layout) (data : EventData) : Option (Event layout) :=
  (decodeContext layout data.context).map fun context => ⟨context, data.observation⟩

theorem decodeEvent_encode (layout : Layout) (observed : Event layout) :
    decodeEvent layout (encodeEvent observed) = some observed := by
  cases observed
  simp only [decodeEvent, encodeEvent, decodeContext_encode, Option.map_some]

structure OccurrenceData where
  ordinal : Nat
  event : EventData
  deriving DecidableEq, Repr

def encodeOccurrence {layout : Layout} (observed : Occurrence layout) : OccurrenceData :=
  ⟨observed.ordinal, encodeEvent observed.event⟩

def decodeOccurrence (layout : Layout) (data : OccurrenceData) : Option (Occurrence layout) :=
  (decodeEvent layout data.event).map fun observed => ⟨data.ordinal, observed⟩

theorem decodeOccurrence_encode (layout : Layout) (observed : Occurrence layout) :
    decodeOccurrence layout (encodeOccurrence observed) = some observed := by
  cases observed
  simp only [decodeOccurrence, encodeOccurrence, decodeEvent_encode, Option.map_some]

structure CoreData where
  storage : ByteStorageData.StorageData
  catalog : Catalog
  environment : ScopedLvalues.Environment
  expression : ExpressionData
  ordinal : Nat
  deriving DecidableEq, Repr

def encodeCore {layout : Layout} (configuration : CoreConfiguration layout) : CoreData :=
  ⟨ByteStorageData.encodeStorage configuration.memory.storage, configuration.memory.catalog,
    configuration.environment, encodeExpression configuration.expression, configuration.ordinal⟩

def decodeCore (layout : Layout) (data : CoreData) : Option (CoreConfiguration layout) := do
  let storage ← ByteStorageData.decodeStorage layout.representation.characters data.storage
  let expression ← decodeExpression layout data.expression
  some ⟨⟨storage, data.catalog⟩, data.environment, expression, data.ordinal⟩

theorem decodeCore_encode (layout : Layout) (configuration : CoreConfiguration layout) :
    decodeCore layout (encodeCore configuration) = some configuration := by
  cases configuration with
  | mk memory environment expression ordinal =>
      cases memory
      simp only [decodeCore, encodeCore, ByteStorageData.decodeStorage_encode, decodeExpression_encode, bind, Option.bind_some]

theorem encodeCore_decode (layout : Layout) (data : CoreData) (configuration : CoreConfiguration layout)
    (decoded : decodeCore layout data = some configuration) : encodeCore configuration = data := by
  simp only [decodeCore, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
  obtain ⟨storage, stored, expression, read, rfl⟩ := decoded
  cases data
  simp only [encodeCore, ByteStorageData.encodeStorage_decode _ _ _ stored, encodeExpression_decode _ _ _ read]

theorem encodeCore_injective (layout : Layout) : Function.Injective (@encodeCore layout) := by
  intro first second same
  have decoded := congrArg (decodeCore layout) same
  rw [decodeCore_encode, decodeCore_encode] at decoded
  exact Option.some.inj decoded

structure ConfigurationData where
  core : CoreData
  choices : List Nat
  deriving DecidableEq, Repr

def encodeConfiguration {layout : Layout} (configuration : Configuration layout) : ConfigurationData :=
  ⟨encodeCore configuration.core, configuration.choices⟩

def decodeConfiguration (layout : Layout) (data : ConfigurationData) : Option (Configuration layout) :=
  (decodeCore layout data.core).map fun core => ⟨core, data.choices⟩

theorem decodeConfiguration_encode (layout : Layout) (configuration : Configuration layout) :
    decodeConfiguration layout (encodeConfiguration configuration) = some configuration := by
  cases configuration
  simp only [encodeConfiguration, decodeConfiguration, decodeCore_encode, Option.map_some]

theorem encodeConfiguration_decode (layout : Layout) (data : ConfigurationData) (configuration : Configuration layout)
    (decoded : decodeConfiguration layout data = some configuration) : encodeConfiguration configuration = data := by
  obtain ⟨core, accepted, rfl⟩ := Option.map_eq_some_iff.mp decoded
  cases data
  simp only [encodeConfiguration, encodeCore_decode _ _ _ accepted]

def stepData (layout : Layout) (policy : SignedConversionPolicy) (data : CoreData)
    (index : Nat) : Option (OccurrenceData × CoreData) := do
  let before ← decodeCore layout data
  let selected ← choose layout policy before index
  some (encodeOccurrence selected.1, encodeCore selected.2)

theorem stepData_sound (layout : Layout) (policy : SignedConversionPolicy)
    (before after : CoreData) (index : Nat) (observed : OccurrenceData)
    (executed : stepData layout policy before index = some (observed, after)) :
    ∃ source target event, decodeCore layout before = some source ∧ decodeCore layout after = some target ∧
      decodeOccurrence layout observed = some event ∧ Advance layout policy source event target := by
  simp only [stepData, bind, Option.bind_eq_some_iff, Option.some.injEq] at executed
  obtain ⟨source, sourceRead, selected, chosen, same⟩ := executed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨source, selected.2, selected.1, sourceRead, decodeCore_encode _ _, decodeOccurrence_encode _ _,
    choose_sound _ _ _ _ _ _ chosen⟩

theorem stepData_complete (layout : Layout) (policy : SignedConversionPolicy)
    (before after : CoreConfiguration layout) (observed : Occurrence layout)
    (advanced : Advance layout policy before observed after) :
    ∃ index, stepData layout policy (encodeCore before) index = some (encodeOccurrence observed, encodeCore after) := by
  obtain ⟨index, chosen⟩ := choose_complete _ _ _ _ _ advanced
  exact ⟨index, by simp only [stepData, decodeCore_encode, chosen, bind, Option.bind_some]⟩

end Mettapedia.Languages.C11.ReadExpression
