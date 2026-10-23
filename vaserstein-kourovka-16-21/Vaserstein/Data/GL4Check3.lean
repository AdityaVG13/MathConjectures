import Vaserstein.Data.GL4

/-! Kernel checks of the chunks 48 to 63 of the `GL_4(2)` certificates. -/

namespace Vaserstein.Bits

theorem scan4_48 : scan 4 reps4 idc4 1024 49152 chunk4_48 = true := by
  decide +kernel

theorem scan4_49 : scan 4 reps4 idc4 1024 50176 chunk4_49 = true := by
  decide +kernel

theorem scan4_50 : scan 4 reps4 idc4 1024 51200 chunk4_50 = true := by
  decide +kernel

theorem scan4_51 : scan 4 reps4 idc4 1024 52224 chunk4_51 = true := by
  decide +kernel

theorem scan4_52 : scan 4 reps4 idc4 1024 53248 chunk4_52 = true := by
  decide +kernel

theorem scan4_53 : scan 4 reps4 idc4 1024 54272 chunk4_53 = true := by
  decide +kernel

theorem scan4_54 : scan 4 reps4 idc4 1024 55296 chunk4_54 = true := by
  decide +kernel

theorem scan4_55 : scan 4 reps4 idc4 1024 56320 chunk4_55 = true := by
  decide +kernel

theorem scan4_56 : scan 4 reps4 idc4 1024 57344 chunk4_56 = true := by
  decide +kernel

theorem scan4_57 : scan 4 reps4 idc4 1024 58368 chunk4_57 = true := by
  decide +kernel

theorem scan4_58 : scan 4 reps4 idc4 1024 59392 chunk4_58 = true := by
  decide +kernel

theorem scan4_59 : scan 4 reps4 idc4 1024 60416 chunk4_59 = true := by
  decide +kernel

theorem scan4_60 : scan 4 reps4 idc4 1024 61440 chunk4_60 = true := by
  decide +kernel

theorem scan4_61 : scan 4 reps4 idc4 1024 62464 chunk4_61 = true := by
  decide +kernel

theorem scan4_62 : scan 4 reps4 idc4 1024 63488 chunk4_62 = true := by
  decide +kernel

theorem scan4_63 : scan 4 reps4 idc4 1024 64512 chunk4_63 = true := by
  decide +kernel

end Vaserstein.Bits
