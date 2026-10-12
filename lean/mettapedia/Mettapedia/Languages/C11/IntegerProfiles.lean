import Mettapedia.Languages.C11.IntegerTypes

/-!
# Named C integer value profiles

These profiles specify 8-bit characters, 16-bit short, 32-bit int, 64-bit
long long and the declared size of long. Signed formats use normal two's
complement minima. The explicit `int128` family is an extension profile,
not a C11 requirement. The standard ranks remain distinct even when widths
agree. All range/rank obligations of `IntegerTypeParameters` are constructed
and kernel-checked here.

The names describe value parameters only. They do not certify a compiler,
calling convention, pointer size, aggregate layout or native parser.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11

inductive IntegerDataModel where
  | ilp32
  | lp64
  | llp64
  deriving DecidableEq, Repr

inductive IntegerExtension where
  | int128
  deriving DecidableEq, Repr

private theorem integerFamily_cases (property : IntegerFamily IntegerExtension → Prop)
    (char : property (.standard .char)) (short : property (.standard .short))
    (int : property (.standard .int)) (long : property (.standard .long))
    (longLong : property (.standard .longLong)) (int128 : property (.extended .int128)) :
    ∀ family, property family := by
  intro family
  cases family with
  | standard family =>
      cases family with
      | char => exact char
      | short => exact short
      | int => exact int
      | long => exact long
      | longLong => exact longLong
  | extended extension => cases extension; exact int128

def profileSignedPrecision (model : IntegerDataModel) : IntegerFamily IntegerExtension → Nat
  | .standard .char => 7
  | .standard .short => 15
  | .standard .int => 31
  | .standard .long => if model = .lp64 then 63 else 31
  | .standard .longLong => 63
  | .extended .int128 => 127

def profileIntegerRank : IntegerFamily IntegerExtension → Nat
  | .standard .char => 10
  | .standard .short => 20
  | .standard .int => 30
  | .standard .long => 40
  | .standard .longLong => 50
  | .extended .int128 => 60

def integerValueProfile (model : IntegerDataModel) : IntegerTypeParameters IntegerExtension where
  name := match model with
    | .ilp32 => "C11 ILP32 integer values with int128 extension"
    | .lp64 => "C11 LP64 integer values with int128 extension"
    | .llp64 => "C11 LLP64 integer values with int128 extension"
  signedPrecision := profileSignedPrecision model
  unsignedPrecision := fun family => profileSignedPrecision model family + 1
  signedPositive := by cases model <;> apply integerFamily_cases <;> decide
  unsignedPositive := by cases model <;> apply integerFamily_cases <;> decide
  representation := fun _ => .twosComplement true
  rank := profileIntegerRank
  rankPositive := by apply integerFamily_cases <;> decide
  rankInjective := by
    change ∀ first second, profileIntegerRank first = profileIntegerRank second → first = second
    apply integerFamily_cases <;> apply integerFamily_cases <;> decide
  standardRanks := by decide
  standardMinimum := by cases model <;> decide
  signedRanges := by cases model <;> apply integerFamily_cases <;> apply integerFamily_cases <;> decide
  unsignedRanges := by cases model <;> apply integerFamily_cases <;> apply integerFamily_cases <;> decide
  correspondingRange := by cases model <;> apply integerFamily_cases <;> decide

end Mettapedia.Languages.C11
