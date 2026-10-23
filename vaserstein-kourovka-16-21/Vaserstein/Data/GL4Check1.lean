import Vaserstein.Data.GL4

/-! Kernel checks of the chunks 16 to 31 of the `GL_4(2)` certificates. -/

namespace Vaserstein.Bits

theorem scan4_16 : scan 4 reps4 idc4 1024 16384 chunk4_16 = true := by
  decide +kernel

theorem scan4_17 : scan 4 reps4 idc4 1024 17408 chunk4_17 = true := by
  decide +kernel

theorem scan4_18 : scan 4 reps4 idc4 1024 18432 chunk4_18 = true := by
  decide +kernel

theorem scan4_19 : scan 4 reps4 idc4 1024 19456 chunk4_19 = true := by
  decide +kernel

theorem scan4_20 : scan 4 reps4 idc4 1024 20480 chunk4_20 = true := by
  decide +kernel

theorem scan4_21 : scan 4 reps4 idc4 1024 21504 chunk4_21 = true := by
  decide +kernel

theorem scan4_22 : scan 4 reps4 idc4 1024 22528 chunk4_22 = true := by
  decide +kernel

theorem scan4_23 : scan 4 reps4 idc4 1024 23552 chunk4_23 = true := by
  decide +kernel

theorem scan4_24 : scan 4 reps4 idc4 1024 24576 chunk4_24 = true := by
  decide +kernel

theorem scan4_25 : scan 4 reps4 idc4 1024 25600 chunk4_25 = true := by
  decide +kernel

theorem scan4_26 : scan 4 reps4 idc4 1024 26624 chunk4_26 = true := by
  decide +kernel

theorem scan4_27 : scan 4 reps4 idc4 1024 27648 chunk4_27 = true := by
  decide +kernel

theorem scan4_28 : scan 4 reps4 idc4 1024 28672 chunk4_28 = true := by
  decide +kernel

theorem scan4_29 : scan 4 reps4 idc4 1024 29696 chunk4_29 = true := by
  decide +kernel

theorem scan4_30 : scan 4 reps4 idc4 1024 30720 chunk4_30 = true := by
  decide +kernel

theorem scan4_31 : scan 4 reps4 idc4 1024 31744 chunk4_31 = true := by
  decide +kernel

end Vaserstein.Bits
