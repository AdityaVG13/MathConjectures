import Vaserstein.Data.GL3

/-! Kernel checks of the chunks 0 to 0 of the `GL_3(2)` certificates. -/

namespace Vaserstein.Bits

theorem scan3_0 : scan 3 reps3 idc3 512 0 chunk3_0 = true := by
  decide +kernel

end Vaserstein.Bits
