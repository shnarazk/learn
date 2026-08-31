import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

namespace Luby

-- Checks if (k + 1) is one less than a power of two
def isSpecial (k : Nat) : Bool :=
  let n := k + 1
  let m := n + 1
  (m &&& (m - 1)) == 0  -- m is a power of 2 ⇔ n = 2^i - 1

#eval isSpecial 0  -- true

-- Returns the largest power of 2 less than or equal to (k + 1)
partial def largestPowerOf2LE (k : Nat) : Nat :=
  let rec loop (i acc : Nat) :=
    if 2^i > k + 1 then acc else loop (i + 1) (2^i)
  loop 0 1

#eval List.map largestPowerOf2LE (List.range 16)  --

-- Well-founded version of the Luby sequence
partial def luby : Nat → Nat
  | 0 => 1
  | k =>
    if isSpecial k then
      largestPowerOf2LE k
    else
     luby (k +1 - (largestPowerOf2LE k))

end Luby

-- 🧪 Test output
#eval List.map Luby.luby (List.range 16)
-- Output: [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1]
