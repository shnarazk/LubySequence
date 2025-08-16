#import "@preview/cetz:0.4.1": canvas, draw, tree
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(paper: "a4", numbering: "1")
#set par(justify: true)
#set text(
  font: (
    (name: "New Computer Modern", covers: "latin-in-cjk"), "Hiragino Mincho Pro"),
  size: 10pt)
#show raw: set text(font: "Monaspace Neon")
#set heading(numbering: "1.")
#show raw: it => {
  if it.block [ #block(width: 98%, inset: 8pt, radius: 2pt, fill: luma(245), it) ]
  else [ #it ]
}

// Luby implementation
#let allone(n) = {
  if n < 2 { n == 1 }
  else if calc.even(n) { false }
  else { allone(calc.quo(n, 2)) }
}
#let nat_size(n) = {
  if n < 2 { 1 }
  else { 1 + nat_size(calc.quo(n, 2)) }
}
#let Luby(n) = {
  assert(n >= 0)
  if allone(n) { calc.pow(2, nat_size(n) - 1) }
  else { Luby(n + 1 - calc.pow(2, nat_size(n) - 1)) }
}

= Luby sequence

The Luby sequence is a sequence of natural numbers defined recursively.
It is used in randomized algorithms and has applications in computer science.
However, outside of Boolean-satisfiability solvers, its applications
appear to be rare. It starts like this:

$
#range(1, 32).map(Luby).map(str).join(", ")
, dots.h.c
$

== Definition

In the paper @Luby1993, the sequence is defined as a recursive function:

$
  L u b y_1(k >= 1) = cases(
    2^(i-1)\, & " if" k = 2^i - 1 " for some " i >= 1,
    L u b y_1(k - 2^(i-1) + 1)\, & " if " 2^(i-1) <= k < 2^i - 1
  )
$

And we can illustrate its recursion property as a transition on triangle by natural number.

#figure(caption: [An interpretation on natural number triangle], gap: 16pt)[
#canvas({
  import draw: *
  let encircle(i) = {
    std.box(baseline: 2pt, std.circle(stroke: .5pt, radius: .5em)[#move(dx: -0.36em, dy: -1.1em, $#i$)])
  }

  set-style(content: (padding: 0.4em))
  tree.tree(
    ([ $15 = "b1111"$ #encircle(8) ],
      ([ $7 = "b111"$ #encircle(4) ],
        ([ $3 = "b11"$ #encircle(2) ],
          ([ $1 = "b1"$ #encircle(1) ]),
          ([ $2 arrow_(- 1) 1$ ]), ),
        ([ $6 arrow_(- 3) 3$ ],
          ([ $4 arrow_(- 3) 1$ ]),
          ([ $5 arrow_(- 3) 2$ ]), ),
      ),
      ([ $14 arrow_(- 7) 7$ ],
        ([ $10 arrow_(- 7) 3$ ],
          ([ $8 arrow_(- 7) 1$ ]),
          ([ $9 arrow_(- 7) 2$ ]), ),
        ([ $13 arrow_(- 7) 6$ ],
          ([ $11 arrow_(- 7) 4$ ]),
          ([ $12 arrow_(- 7) 5$ ]), ),
      ),
    ),
   spread: 0.2)
})]

== Another interpretation on a binary tree

Or you can map the function to a traverse on a binary graph.
The function has a strong relation to an operation on the binary representation of natural number.

#figure(caption: [Binary tree reprisenting `Nat`], gap: 16pt)[
#canvas({
  import draw: *
  let encircle(i) = {
    std.box(baseline: 2pt, std.circle(stroke: .5pt, radius: .5em)[#move(dx: -0.36em, dy: -1.1em, $#i$)])
  }

  set-style(content: (padding: 0.5em))
  line((8, -4), (6, -4), mark: (end: "stealth"), stroke: 6pt + blue)
  tree.tree(
    ([ [01]\*\* ],
      ([ 0[01]\* ],
        (
          [ 00[01] ],
          ([#encircle($0$)]),
          ([#encircle($1$)]),
        ),
        (
          [ 01[01] ],
          ([$2 arrow 0$]),
          ([#encircle($3$)]),
        ),
      ),
      ([ 1[01]\* ],
        (
          [ 10[01] ],
          ([$4 arrow 0$]),
          ([$5 arrow 1$]),
        ),
        (
          [ 11[01] ],
          ([$6 arrow 2$]),
          ([#encircle($7$)]),
        ),
      )
    ))
  // line((-0.5, 0), (4, 0))
  // line((0, -0.5), (0, 1))
})]

= An efficient implementation

Now we introduce a segmentation on Luby sequence.

== segments

We define *segments* as a monotone increasing subsequence in Luby sequence. Here are the first 16 segments. Each segment is alternately in red and blue.

#let luby = (1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 16)

$
#let even = true
#luby.insert(0, luby.at(0) - 1)
#for (p, n) in luby.windows(2) {
  even = if p < n { even } else { not even }
  text(fill: if even { red } else { blue }, str(n) + ", ")
}
$

As you see, the Luby value is equal to two powered by a local index in a segment. So we can define Luby sequence in another form.

#figure(caption: [local index and segment index on natural number triangle], gap: 16pt)[
#canvas({
  import draw: *
  let encircle(i) = {
    std.box(baseline: 2pt, std.circle(stroke: .5pt, radius: .5em)[#move(dx: -0.36em, dy: -1.1em, $#i$)])
  }

  set-style(content: (padding: 0.5em))
  tree.tree(
    (text(fill: blue, [$4="b100"$ #encircle(2)]),
      (
        text(fill: blue, [$2="b10"$ #encircle(1)]),
        (text(fill: red, [$1="b1"$ #encircle($0$)])),
        (text(fill: blue, [2 #encircle($0$)])),
      ),
      (
        text(fill: blue, [4 #encircle($1$)]),
        (text(fill: red, [$3="b11"$ #encircle($0$)])),
        (text(fill: blue, [4 #encircle($0$)])),
      ),
    ))
})]

== Luby state
#figure(caption: [The definition of Luby Status `S`])[
  #align(left)[
```lean
structure State where
  segIx : Nat  -- 単調増加部分数列(segment)の何番目か(1-based)
  locIx : Nat　-- 現在のsegment内で何番目(local index)か(0-based)

/-- O(1) -/
def State.next (s: State) : S := ...
/-- O(1) -/
def State.luby (s : State) : Nat = 2 ^ s.locIx
```
]]<def_S>

#figure(caption: [Generating Luby state], gap: 16pt)[
#diagram(cell-size: 12mm, {
  node((1, 0), $n$)
  edge((1, 0), (1, 2),  $O(log(n))$, label-pos: 25%, bend: -30deg, "-straight", stroke: red)
  edge((1, 0), (1, 1), "<-->")
  node((0, 1), $S_0$)
  edge((0, 1), (1, 1), "~>", stroke: luma(150))
  node((2, 0), $n + 1$)
  edge((2, 0), (2, 2), $O(log(n + 1))$, label-pos: 25%, bend: 30deg, "-straight", stroke: red)
  edge((2, 0), (2, 1), "<-->")
  node((1, 1), $S_n$)
  edge((1, 1), (2, 1), [ .next ], "->", stroke: blue)
  edge((1, 1), (1, 2), [ .luby ], label-side: left, "-straight", stroke: blue)
  node((2, 1), $S_(n + 1)$)
  edge((2, 1), (2, 2), [ .luby ], label-side: right, "-straight", stroke: blue)
	node((1, 2), $L u b y(n)$)
	node((2, 2), $L u b y(n + 1)$)
})]

= Equivalence of $L u b y$ and Luby state

#figure(caption: "Main goal")[
#align(left)[
```lean
-- the main goal
theorem S_is_luby : ∀ n ≥ 1, (↑ n : State).luby = Luby n := by
    sorry
```
]]<t1>

#bibliography("bib.yml")
