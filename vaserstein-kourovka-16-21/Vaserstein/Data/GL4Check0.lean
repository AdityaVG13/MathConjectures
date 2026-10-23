import Vaserstein.Data.GL4

/-! Kernel checks of the chunks 0 to 15 of the `GL_4(2)` certificates. -/

namespace Vaserstein.Bits

theorem scan4_0 : scan 4 reps4 idc4 1024 0 chunk4_0 = true := by
  decide +kernel

theorem scan4_1 : scan 4 reps4 idc4 1024 1024 chunk4_1 = true := by
  decide +kernel

theorem scan4_2 : scan 4 reps4 idc4 1024 2048 chunk4_2 = true := by
  decide +kernel

theorem scan4_3 : scan 4 reps4 idc4 1024 3072 chunk4_3 = true := by
  decide +kernel

theorem scan4_4 : scan 4 reps4 idc4 1024 4096 chunk4_4 = true := by
  decide +kernel

theorem scan4_5 : scan 4 reps4 idc4 1024 5120 chunk4_5 = true := by
  decide +kernel

theorem scan4_6 : scan 4 reps4 idc4 1024 6144 chunk4_6 = true := by
  decide +kernel

theorem scan4_7 : scan 4 reps4 idc4 1024 7168 chunk4_7 = true := by
  decide +kernel

theorem scan4_8 : scan 4 reps4 idc4 1024 8192 chunk4_8 = true := by
  decide +kernel

theorem scan4_9 : scan 4 reps4 idc4 1024 9216 chunk4_9 = true := by
  decide +kernel

theorem scan4_10 : scan 4 reps4 idc4 1024 10240 chunk4_10 = true := by
  decide +kernel

theorem scan4_11 : scan 4 reps4 idc4 1024 11264 chunk4_11 = true := by
  decide +kernel

theorem scan4_12 : scan 4 reps4 idc4 1024 12288 chunk4_12 = true := by
  decide +kernel

theorem scan4_13 : scan 4 reps4 idc4 1024 13312 chunk4_13 = true := by
  decide +kernel

theorem scan4_14 : scan 4 reps4 idc4 1024 14336 chunk4_14 = true := by
  decide +kernel

theorem scan4_15 : scan 4 reps4 idc4 1024 15360 chunk4_15 = true := by
  decide +kernel

end Vaserstein.Bits
