import Vaserstein.Data.GL3Check0

/-! All chunks of the `GL_3(2)` certificates together. -/

namespace Vaserstein.Bits

theorem scan3 : scanAll 3 reps3 idc3 512 0 [chunk3_0] = true :=
  scanAll_cons_of scan3_0
    (scanAll_nil_of (by decide))

end Vaserstein.Bits
