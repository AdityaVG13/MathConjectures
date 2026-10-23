import Vaserstein.Data.GL3Scan
import Vaserstein.Data.GL4Scan

/-!
# The cases `n = 3` and `n = 4`

Every nonidentity element of `GL_3(2)` is a product of `3` conjugates of any given nonidentity
element, and the same holds in `GL_4(2)` with `4` conjugates. The certificates in
`Vaserstein.Data` are checked by kernel evaluation (`decide +kernel`, which adds no axioms), and
`Vaserstein.Bits.covers_of_certs` turns the checks into the statements.
-/

namespace Vaserstein.Bits

theorem hid3 : ofCode 3 idc3 = 1 := by decide
theorem reps3OK : repsOK 3 reps3 repinv3 idc3 = true := by decide +kernel
theorem wit3OK : witOK 3 reps3 idc3 wit3 = true := by decide +kernel

theorem hid4 : ofCode 4 idc4 = 1 := by decide
theorem reps4OK : repsOK 4 reps4 repinv4 idc4 = true := by decide +kernel
theorem wit4OK : witOK 4 reps4 idc4 wit4 = true := by decide +kernel

end Vaserstein.Bits

namespace Vaserstein

open Pointwise

theorem covers_three (α g : GL (Fin 3) (ZMod 2)) (hα : α ≠ 1) (hg : g ≠ 1) :
    g ∈ conjugatesOf α ^ 3 :=
  Bits.covers_of_certs Bits.hid3 rfl Bits.reps3OK Bits.scan3 Bits.wit3OK α g hα hg

theorem covers_four (α g : GL (Fin 4) (ZMod 2)) (hα : α ≠ 1) (hg : g ≠ 1) :
    g ∈ conjugatesOf α ^ 4 :=
  Bits.covers_of_certs Bits.hid4 rfl Bits.reps4OK Bits.scan4 Bits.wit4OK α g hα hg

end Vaserstein
