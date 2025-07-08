
def trailing_zero (n : Nat) : Nat :=
  if h : n < 2
  then (1 - n)
  else if n % 2 = 0 then 1 + trailing_zero (n / 2) else 0

#eval List.range 9 |>.map trailing_zero

def trailing_one (n : Nat) : Nat :=
  if h : n < 2
  then n
  else if n % 2 = 0 then 0 else 1 + trailing_one (n / 2)

#eval List.range 9 |>.map trailing_one

def scanList {α : Type _} (f : α → α) (init : α) (n : Nat) (start : Bool := true) : List α :=
  match n with
  | 0      => []
  | n' + 1 =>
    let nxt := f init
    if start
      then init :: nxt :: scanList f nxt n' false
      else nxt :: scanList f nxt n' false

#eval scanList (· + 1) 10 8
