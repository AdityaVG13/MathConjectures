import Vaserstein.Data.GL4

/-! Kernel checks of the chunks 32 to 47 of the `GL_4(2)` certificates. -/

namespace Vaserstein.Bits

theorem scan4_32 : scan 4 reps4 idc4 1024 32768 chunk4_32 = true := by
  decide +kernel

theorem scan4_33 : scan 4 reps4 idc4 1024 33792 chunk4_33 = true := by
  decide +kernel

theorem scan4_34 : scan 4 reps4 idc4 1024 34816 chunk4_34 = true := by
  decide +kernel

theorem scan4_35 : scan 4 reps4 idc4 1024 35840 chunk4_35 = true := by
  decide +kernel

theorem scan4_36 : scan 4 reps4 idc4 1024 36864 chunk4_36 = true := by
  decide +kernel

theorem scan4_37 : scan 4 reps4 idc4 1024 37888 chunk4_37 = true := by
  decide +kernel

theorem scan4_38 : scan 4 reps4 idc4 1024 38912 chunk4_38 = true := by
  decide +kernel

theorem scan4_39 : scan 4 reps4 idc4 1024 39936 chunk4_39 = true := by
  decide +kernel

theorem scan4_40 : scan 4 reps4 idc4 1024 40960 chunk4_40 = true := by
  decide +kernel

theorem scan4_41 : scan 4 reps4 idc4 1024 41984 chunk4_41 = true := by
  decide +kernel

theorem scan4_42 : scan 4 reps4 idc4 1024 43008 chunk4_42 = true := by
  decide +kernel

theorem scan4_43 : scan 4 reps4 idc4 1024 44032 chunk4_43 = true := by
  decide +kernel

theorem scan4_44 : scan 4 reps4 idc4 1024 45056 chunk4_44 = true := by
  decide +kernel

theorem scan4_45 : scan 4 reps4 idc4 1024 46080 chunk4_45 = true := by
  decide +kernel

theorem scan4_46 : scan 4 reps4 idc4 1024 47104 chunk4_46 = true := by
  decide +kernel

theorem scan4_47 : scan 4 reps4 idc4 1024 48128 chunk4_47 = true := by
  decide +kernel

end Vaserstein.Bits
