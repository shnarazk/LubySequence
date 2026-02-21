#import "@preview/cetz:0.4.2" as cetz: canvas, draw, tree
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/touying:0.6.1": *
#import themes.simple: *
#import "@preview/pinit:0.2.2": *
#set par(justify: true)
#show: simple-theme.with(aspect-ratio: "16-9")
#set text(
  font: ((name: "New Computer Modern", covers: "latin-in-cjk"), "Hiragino Mincho Pro"),
  size: 20pt)
#show raw: set text(font: "Monaspace Neon", size: 16pt)
#set heading(numbering: "1.")
#show raw: it => {
  if it.block [ #block(width: 98%, inset: 8pt, radius: 2pt, fill: luma(245), it) ] else [ #it ]
}
#show math.equation: set text(font: "Euler Math", size: 18pt)
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
#let cetz-canvas = touying-reducer.with(reduce: cetz.canvas, cover: cetz.draw.hide.with(bounds: true))

#let title = [An Online Algorithm for Luby Sequence]
#align(center, text(30pt, [*#title*]))
#grid(columns: (1fr),align(center, [`shnarazk`]))
#grid(columns: (1fr),align(center, [2026-02-2X]))

= Luby sequence

$ #range(1, 32).map(Luby).map(str).join(", ") , dots.h.c $

#pause

$
  L u b y_1(k >= 1) = cases(
    2^(i-1) & " if" k = 2^i - 1 " for "exists i >= 1,
    L u b y_1(k - 2^(i-1) + 1) & " if " 2^(i-1) <= k < 2^i - 1
  )
$

#pause

$
  L u b y_1(k >= 1) = cases(
    2^(k".size" - 1) & " if" k = 2^(k".size") - 1,
    L u b y_1(k - (2^(k".size"-1) - 1)). & " otherwise"
  )
$

#pause

Luby, M. et al., Optimal Speedup of Las Vegas Algorithms,
In _The 2nd Israel Symp. on Theory and Comp. Sys._, pp. 127-133, 1993.

== Example on the natural number triangle
// We can illustrate its recursive property as transitions on a triangle of natural numbers greater than zero.

#let encircle(i) = {
  std.box(baseline: 2pt, fill: yellow, inset: 5pt)[ $#i$ ]
}

#cetz-canvas(length: 13pt, {
  draw.set-style(content: (padding: 0.4em))
  tree.tree(
    spread: 0.45,
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
  (pause, )
  draw.bezier((38, -8), (15, -8), (24, 1),
    stroke: 1pt + red, mark: (end: ">"))
  (pause, )
  draw.bezier((14, -8), (0, -8), (8, -3),
    stroke: 1pt + red, mark: (end: ">"))
})

$
  L u b y_1(13) & arrow L u b y_1(13-(2^3-1)=6) arrow L u b y_1(6-(2^2-1) = 3) = 2
$

//- The worst recursion depth of $L u b y (N)$ would be $O(log(N))$.

/* == Another interpretation using a binary tree

#cetz-canvas(length: 16pt, {
  draw.set-style(content: (padding: 0.5em))
  /*
  line((1, -5), (5.7, -5),
    stroke: 18pt + rgb(240, 240, 255))
  line((6.5, -5), (11.5, -5),
    stroke: 18pt + rgb(240, 240, 255))
  bezier((9.5, -4.6), (2.5, -4.6), (8.5, -3), (3.5, -3),
    mark: (end: ">"),
    stroke: 4pt + rgb(250, 200, 200))
    */
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
})

#pause
Remove the highest non-zero bits until . . .
*/

= Segment sequence

Segmentation of the Luby sequence

== Segments

Monotone increasing subsequences in the Luby sequence.

#let luby = range(1, 32).map(Luby)

$
#let even = true
#luby.insert(0, luby.at(0) - 1)
#for (p, n) in luby.windows(2) {
  even = if p < n { even } else { not even }
  text(fill: if even { red } else { blue }, str(n) + ", ")
}
$

#pause

$
  L u b y_1(k >= 1) = cases(
    1\, & " if" k "is the beginning of a segment",
    2 times L u b y_1(k - 1)\, & " otherwise" )
$

== Property: sizes of segments

#let luby = range(1, 32).map(Luby)

$
#let even = true
#luby.insert(0, luby.at(0) - 1)
#for (p, n) in luby.windows(2) {
  even = if p < n { even } else { not even }
  text(fill: if even { red } else { blue }, str(n) + ", ")
}
$

To sizes

$
1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3
$

#pause

$
  |s e g m e n t (t >= 1)| = "the number of trailing zeros of " t
$

== indices on the natural number triangle

#canvas(length: 10pt, {
  draw.set-style(content: (padding: (0.4em, 0.04em)))
  tree.tree(spread: 0.4,
    ( text(fill: blue, [$14 arrow (\#8, 3)$]),
      ( text(fill: blue, [$6 arrow (\#4, 2)$]),
        ( text(fill: blue, [$2 arrow (\#2, 1)$]),
          (text(fill: red, [$0 arrow (\#1, 0)$])),
          (text(fill: blue, [$1 arrow (\#2, 0)$])), ),
        ( text(fill: blue, [$(\#4, 1)$]),
          (text(fill: red, [$3 arrow (\#3, 0)$])),
          (text(fill: blue, [$4 arrow (\#4, 0)$])), ), ),
      ( text(fill: blue, [$(\#8, 2)$]),
        ( text(fill: blue, [$(\#6, 1)$]),
          (text(fill: red, [$7 arrow (\#5, 0)$])),
          (text(fill: blue, [$8 arrow (\#6, 0)$])), ),
        ( text(fill: blue, [$(\#8, 1)$]),
          (text(fill: red, [$10 arrow (\#7, 0)$])),
          (text(fill: blue, [$(\#8, 0)$])), ), )) )
})
#pad(top: -6mm)[
#align(center)[#text(size: 15pt)[sequence index $arrow$ (\#segment index, index in segment)]]
]

#text(size: 18pt, fill: green.darken(40%))[
The index of Luby sequence starts from 0; the index of segments starts from 1.]
#pause

Segments start at 1, 2, 4, 5, 8, 9, 11, 12 ...
/*
$
  "segment_beg"_i & = 1 + sum_(i>= 0) #pin(1) [ "use envelope"_i ]#pin(2) |"envelope"_i| \
    & = 1 + sum_(i>= 0)" " [ "use envelope"_i ] " " (2^i - 1),
$
#pinit-highlight(1, 2)

#pinit-point-from(2, offset-dx: 70pt, offset-dy: 20pt)[
  #text(size: 16pt, [Iverson's notation])
]
*/

= O(1) inprementation of Luby sequence

An Online algorithm on segment sequence

== From segment index to segment length to Luby value
#canvas(length: 10pt, {
  draw.set-style(content: (padding: 0.1em))
  tree.tree(spread: 0.3,
    ( text(fill: blue, [$l e n g t h = 4$]),
      ( text(fill: blue, [$l e n g t h = 3$]),
        ( text(fill: blue, [$l e n g t h = 2$]),
          (text(fill: red, [$\#1 = "b1"$])),
          (text(fill: blue, [$\#2 = "b10"$])), ),
        ( text(fill: blue, [$(\#4, 1)$]),
          (text(fill: red, [$\#3 = "b11"$])),
          (text(fill: blue, [$\#4 = "b100"$])), ), ),
      ( text(fill: blue, [$(\#8, 2)$]),
        ( text(fill: blue, [$l e n g t h = 2$]),
          (text(fill: red, [$\#5 = "b101"$])),
          (text(fill: blue, [$\#6 = "b110"$])), ),
        ( text(fill: blue, [$(\#8, 1)$]),
          (text(fill: red, [$\#7 = "b111"$])),
          (text(fill: blue, [$\#8 = "b1000"$])), ), )) )
})
$ "Luby value"(n) = 2 ^ "index_in_segment(n)" $

$ "segment_length"(s) = #pin(1)"trailing_zeros"(s)#pin(2) + 1 $

$ #pin(3)"segment_beg"(s) = "segment_beg"(s - 1)#pin(4) + "segment_length"(s - 1) $

$ "index_in_segment"(n) = n - "segment_beg"(#pin(5)"index_to_segment_index"(n)#pin(6)) $

#pinit-highlight(1, 2)

#pinit-point-from(2, pin-dy: -6mm, offset-dy: -14mm, body-dy: -6mm, fill: rgb("#aaf"))[
  #text(size: 16pt, fill: rgb("#77f"), [$"trailing_zero"(8) = 3$])
]
#pinit-highlight(3, 4)

#pinit-point-from(4, offset-dx: 55mm, offset-dy: -13mm, pin-dy: -6mm, body-dy: -6mm, fill: rgb("#aaf"))[#text(fill: rgb("#77f"))[_simple recursion_]]

#pinit-highlight(5, 6)

#pinit-point-from((5, 6), offset-dx: 0mm, offset-dy: 8mm, pin-dy: 3mm, pin-dx: -4mm, body-dx: -8mm, fill: rgb("#aaf"))[#text(fill: rgb("#77f"))[_based on $"segment_length"$_]]

== Segment state
- Save the last segment info
from $O(1)$ time to $O(1)$ time and $O(1)$ space implementation

```lean
structure State where
  segIx : ℕ  -- (one-based) segment index
  locIx : ℕ　-- (zero-based) local index in a segment

/-- O(1) -/
def State.next (s : State) : State := . . .
/-- O(1) -/
def State.luby (s : State) : ℕ := 2 ^ s.locIx
```

This is better than the original Luby $O(log n)$.

== Archievement

#align(center)[
#diagram(cell-size: 12mm, {
  node((1, 0), $n$)
  edge((1, 0), (1, 2), $O(log(n))$, label-pos: 25%, bend: -30deg, "-straight", stroke: red)
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
#pause
*only if $forall n, L u b y(n) = S_n.l u b y$*

= Equivalence of Luby and Luby state
_*Prove it in Lean4*_

== Outline in Lean4

```lean
theorem Luby_values : ∀ n : ℕ,
    luby n = if n.is_segment_beg
      then 1
      else 2 * Luby (n - 1) := by ...

theorem LubyState_values : ∀ n : ℕ,
    (↑ n : State).luby = if (↑ n : State).is_segment_beg
      then 1
      else 2 * (↑ n - 1 : State).luby := by ...
```

```lean
theorem segments_are_equivalent : ∀ n : ℕ,
    (↑ n : State).is_segment_beg = n.is_segment_beg := by ...
```

== contd.

```lean
theorem LubyState_eq_Luby : ∀ n : ℕ,
    (↑ n : State).luby = luby n := by ...
```
```lean
theorem LubyState_is_additive : ∀ n : ℕ,
    (↑ n + 1 : State) = (↑ n : State).next := by ...
```

== proved theorems

#image("graph-20260215.svg")

== trim unused theorems

#image("graph.svg", height: 75%)

#scale(75%)[
#box(fill: rgb("AED6F1"), inset: 1mm)[about bit length or `size`] /
#box(fill: rgb("F9E79F"), inset: 1mm)[about $"trailing_zeros"$] /
total 45 theorems (847 LoC)
]
