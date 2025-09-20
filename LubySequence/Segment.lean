import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Utils
import LubySequence.Basic

-- open Luby hiding Mathlib.Analysis

namespace LubySegment

#eval! List.range 8 |>.map (fun n ↦ (n, 2 ^ (n.size - 1), Luby.S₂ n, Luby.luby n))

/--
test
-/
partial
def segmentl (n : ℕ) : ℕ := match n with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | n =>
    let n' := 2 ^ (n.size - 1)
    if n = 2 * n' - 2 then n' else segmentl (n - 1) -- segment n'
#eval! List.range 6 |>.map (fun n ↦ (n, segmentl n, 2 ^ (n.size - 1)))

end LubySegment
