import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Utils
import LubySequence.Basic

namespace LubySegment

#eval! List.range 8 |>.map (fun n ↦ (n, 2 ^ (n.size - 1), Luby.S₂ n, Luby.luby n))

/--
Return the segment index for `n`.
- `n` starts from 0.
- segment index starts from 1.
-/
partial
def segment (n : ℕ) : ℕ := match n with
  | 0 => 1
  | n =>
    let n' := 2 ^ ((n + 2).size - 2)
    if n = 2 * n' - 2 then n' else n' + segment (n - (2 * n' - 2) - 1)
#eval! List.range 32 |>.map (fun n ↦ (n, LubySegment.segment n))

end LubySegment
