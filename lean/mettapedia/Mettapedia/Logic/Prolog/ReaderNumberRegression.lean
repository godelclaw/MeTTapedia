import Mettapedia.Logic.Prolog.ReaderNumber

namespace Mettapedia.Logic.Prolog.ReaderNumberRegression

open ReaderNumber SourceSignature

#guard parse "123_456" = .ok (.integer 123456)
#guard parse "0xff" = .ok (.integer 255)
#guard parse "0o17" = .ok (.integer 15)
#guard parse "0b1010" = .ok (.integer 10)

def rejectsMalformedSeparators : Bool :=
  match parse "0x_ff", parse "1__2", parse "1_" with
  | .error _, .error _, .error _ => true
  | _, _, _ => false

#guard rejectsMalformedSeparators

#guard parse "0'\"" = .ok (.integer 34)
#guard parse "0'\\\\" = .ok (.integer 92)
#guard parse "0'\\n" = .ok (.integer 10)

#guard parse "1.5" = .ok (.floatBits (Float.ofScientific 15 true 1).toBits)
#guard parse "1e3" = .ok (.floatBits (Float.ofScientific 1 false 3).toBits)
#guard parse "1.5e-3" =
  .ok (.floatBits (Float.ofScientific 15 true 4).toBits)
#guard parse "1.0Inf" = .ok (.floatBits 0x7ff0000000000000)

def rationalIsExplicitlyUnsupported : Bool :=
  match parse "1r2" with
  | .error (.unsupportedRational "1r2") => true
  | _ => false

#guard rationalIsExplicitlyUnsupported

end Mettapedia.Logic.Prolog.ReaderNumberRegression
