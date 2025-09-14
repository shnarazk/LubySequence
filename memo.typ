#import "@preview/cetz:0.4.2": canvas, draw, tree
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let title = [An Online Algorithm for Luby Sequence]

#set page(
  header: align(right + horizon, title),
  paper: "a4",
  numbering: "1"
)
#set par(justify: true)
#set text(
  font: ((name: "New Computer Modern", covers: "latin-in-cjk"), "Hiragino Mincho Pro"),
  size: 10pt)
#show raw: set text(font: "Monaspace Neon")
#set heading(numbering: "1.")
#show raw: it => {
  if it.block [ #block(width: 98%, inset: 8pt, radius: 2pt, fill: luma(245), it) ] else [ #it ]
}
#show math.equation: set text(font: "Euler Math")

// Luby implementation
#let allone(n) = {
  if n < 2 { n == 1 }
  else if calc.even(n) { false }
  else { allone(calc.quo(n, 2)) }
}
#let nat_size(n) = { if n < 2 { 1 } else { 1 + nat_size(calc.quo(n, 2)) } }
#let Luby(n) = {
  assert(n >= 0)
  if allone(n) { calc.pow(2, nat_size(n) - 1) }
  else { Luby(n + 1 - calc.pow(2, nat_size(n) - 1)) }
}

#align(center, text(17pt)[*#title*])

#grid(columns: (1fr),align(center)[`shnarazk` and gen. AIs])
#grid(columns: (1fr),align(center)[2025-0X-XX])

= Luby sequence

The Luby sequence is a sequence of natural numbers defined recursively.
It is used in randomized algorithms and has applications in computer science.
However, outside of Boolean-satisfiability solvers, its applications
appear to be rare. It starts like this:

$ #range(1, 32).map(Luby).map(str).join(", ") , dots.h.c $

== Definition

In the paper @Luby1993, @Luby1993-IPL, the sequence is defined as a recursive function:

#set math.equation(numbering: "(1)")
$
  L u b y_1(k >= 1) = cases(
    2^(i-1) & " if" k = 2^i - 1 " for some " i >= 1,
    L u b y_1(k - 2^(i-1) + 1) & " if " 2^(i-1) <= k < 2^i - 1
  )
$<def_1>
#set math.equation(numbering: none)

By introducing `Nat.size` operator which returns the length of bit vector representing a natural number `Nat`, we can eliminate $i$ and rewrite the definition as
#set math.equation(numbering: "(1)")
$
  L u b y_1(k >= 1) = cases(
    2^(k".size" - 1) & " if" k = 2^(k".size") - 1,
    L u b y_1(k - (2^(k".size"-1) - 1)). & " otherwise"
  )
$<def_2>
#set math.equation(numbering: none)

We can illustrate its recursive property as transitions on a triangle of natural numbers greater than zero.

#figure(caption: [An interpretation of the natural number triangle], gap: 16pt)[
#canvas({
  import draw: *
  let encircle(i) = {
    std.box(baseline: 2pt, std.circle(stroke: .5pt, radius: .5em)[#move(dx: -0.36em, dy: -1.1em, $#i$)])
  }

  set-style(content: (padding: 0.4em))
  tree.tree(
    spread: 0.4,
    ([ $15 = "b1111"$ #encircle(8) ],
      ([ $7 = "b111"$ #encircle(4) ],
        ([ $3 = "b11"$ #encircle(2) ],
          ([ $1 = "b1"$ #encircle(1) ]),
          ([ $2 arrow_(- 1) 1$ ]), ),
        ([ $6 arrow_(- 3) 3$ ],
          ([ $4 arrow_(- 3) 1$ ]),
          ([ $5 arrow_(- 3) 2$ ]), ), ),
      ([ $14 arrow_(- 7) 7$ ],
        ([ $10 arrow_(- 7) 3$ ],
          ([ $8 arrow_(- 7) 1$ ]),
          ([ $9 arrow_(- 7) 2$ ]), ),
        ([ $13 arrow_(- 7) 6$ ],
          ([ $11 arrow_(- 7) 4$ ]),
          ([ $12 arrow_(- 7) 5$ ]), ), ), ),)
})]

Here are some examples.

$
  L u b y_1(14) & arrow L u b y_1(7) = 4 \
  L u b y_1(13) & arrow L u b y_1(6) arrow L u b y_1(3) = 2 \
  L u b y_1(9) & arrow L u b y_1(2) arrow L u b y_1(1) = 1
$

- At the top of a tree or *_envelope_* which contains the target number as a node, the recursion stops.
- Otherwise, the right tree is folded to the left tree. By a simple calculation, we find that any number is placed to the top of a tree or in the right subtree.
- The worst recursion depth of $L u b y (N)$ would be $O(log(N))$.

/*
== Another interpretation using a binary tree

Or you can map the function to a traversal on a binary graph.
The function has a strong relation to an operation on the binary representation of a natural number.

#figure(caption: [A binary tree representing $"Nat" > 0$], gap: 16pt)[
#canvas({
  import draw: *
  let encircle(i) = {
    std.box(baseline: 2pt, std.circle(stroke: .5pt, radius: .5em)[#move(dx: -0.36em, dy: -1.1em, $#i$)])
  }

  set-style(content: (padding: 0.5em))
  line((1, -5), (5.7, -5),
    stroke: 18pt + rgb(240, 240, 255))
  line((6.5, -5), (11.5, -5),
    stroke: 18pt + rgb(240, 240, 255))
  bezier((9.5, -4.6), (2.5, -4.6), (8.5, -3), (3.5, -3),
    mark: (end: ">"),
    stroke: 4pt + rgb(250, 200, 200))
  tree.tree(
    spread: 0.6,
    ([ [01]\*\* ],
      ([ 0[01]\* ],
        ( [ 00[01] ],
          ([out of domain]),
          ([#encircle($1$)]), ), (
          [ 01[01] ],
          ([$2 arrow_(-1) 1$]),
          ([#encircle($3$)]), ), ),
      ([ 1[01]\* ],
        ( [ 10[01] ],
          ([$4 arrow_(-3) 1$]),
          ([$5 arrow_(-3) 1$]), ),
        ( [ 11[01] ],
          ([$6 arrow_(-3) 3$]),
          ([#encircle($7$)]), ), ) ))
})]
*/

= An efficient implementation

Now we introduce a segmentation on the Luby sequence.

== Segments

We define *segments* as a monotone increasing subsequence in the Luby sequence. Here are the first 16 segments. Each segment is alternately in red and blue.

#let luby = range(1, 32).map(Luby)

$
#let even = true
#luby.insert(0, luby.at(0) - 1)
#for (p, n) in luby.windows(2) {
  even = if p < n { even } else { not even }
  text(fill: if even { red } else { blue }, str(n) + ", ")
}
$

As you see, the Luby value is equal to two raised to the power of the local index in a segment. So we can define the Luby sequence in another form.

#figure(caption: [Local index and segment index on the natural number triangle], gap: 16pt)[
#canvas({
  import draw: *

  set-style(content: (padding: 0.4em))
  tree.tree(spread: 0.5,
    ( text(fill: blue, [$(8, 3)$]),
      ( text(fill: blue, [$(4, 2)$]),
        ( text(fill: blue, [$(2, 1)$]),
          (text(fill: red, [$(1, 0) \#1$])),
          (text(fill: blue, [$(2, 0) \#2$])), ),
        ( text(fill: blue, [$(4, 1)$]),
          (text(fill: red, [$(3, 0) \#4$])),
          (text(fill: blue, [$(4, 0) \#5$])), ), ),
      ( text(fill: blue, [$(8, 2)$]),
        ( text(fill: blue, [$(6, 1)$]),
          (text(fill: red, [$(5, 0) \#8$])),
          (text(fill: blue, [$(6, 0) \#9$])), ),
        ( text(fill: blue, [$(8, 1)$]),
          (text(fill: red, [$(7, 0) \#11$])),
          (text(fill: blue, [$(8, 0) \#12$])), ), )) )
})]

== Redefine the Luby sequence as a linear recursive function

+ At the start of a segment, the Luby value is one
+ Otherwise, the Luby value is twice the previous value

So we have the following equation.

#set math.equation(numbering: "(1)")
$
  L u b y_1(k >= 1) = cases(
    1\, & " if" k "is the beginning of a segment",
    2 times L u b y_1(k - 1)\, & " otherwise" )
$<def_2>
#set math.equation(numbering: none)

And segments start at the following $k$:

$
  k & = 1 + sum_(i>= 0) a_i |"envelope"_i| \
    & = 1 + sum_(i>= 0) a_i (2^i - 1)
$
where $a_i$ is 0 or 1.

This means any $2^i - 1 > 0$ is not the beginning of a segment.

== Luby state

#figure(caption: [The definition of Luby State])[
  #align(left)[
```lean
structure State where
  segIx : Nat  -- 単調増加部分数列(segment)の何番目か(1-based)
  locIx : Nat　-- 現在のsegment内で何番目(local index)か(0-based)

/-- O(1) -/
def State.next (s : State) : State := ...
/-- O(1) -/
def State.luby (s : State) : Nat := 2 ^ s.locIx
```
]]<def_S>

#figure(caption: [Generating the Luby state], gap: 16pt)[
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
theorem State_is_luby : ∀ n ≥ 1, (↑ n : State).luby = Luby n := by
    sorry
```
]]<t1>

#bibliography("bib.yml")
