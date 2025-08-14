#import "@preview/cetz:0.4.1": canvas, draw, tree
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(paper: "a4", numbering: "1")
#set par(justify: true)
#set text(font: (
  (name: "New Computer Modern", covers: "latin-in-cjk"),
  "Hiragino Mincho Pro"
))
// #show raw: set text(font: "New Computer Modern Mono")
#show raw: set text(font: "Monaspace Argon")
#set heading(numbering: "1.")
#show raw: it => {
  if it.block [ #block(width: 98%, inset: 8pt, radius: 2pt, fill: luma(245), it) ] else [ #it ]
}

= Luby sequence

The Luby sequence is a sequence of natural numbers defined recursively.
It is used in randomized algorithms and has applications in computer science.
However, outside of Boolean-satisfiability solvers, its applications
appear to be rare.

$1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 16, 1, dots.h.c $

== Definition

The sequence is defined as follows:
$
  L u b y_1(k >= 1) = cases(
    2^(i-1)\, & " if" k = 2^i - 1 " for some " i >= 1,
    L u b y_1(k - 2^(i-1) + 1)\, & " if " 2^(i-1) <= k < 2^i - 1
  )
$
== An interpretation on binary trees

#figure(caption: [Binary tree reprisenting `Nat`], gap: 16pt)[
#canvas({
  import draw: *
  let encircle(i) = {
    std.box(baseline: 2pt, std.circle(stroke: .5pt, radius: .5em)[#move(dx: -0.36em, dy: -1.1em, $#i$)])
  }

  set-style(content: (padding: 0.5em))
  tree.tree(
    ([ ?\*\* ],
      ([ ?\* ],
        (
          [ ? ],
          ([#encircle($0$)]),
          ([#encircle($1$)]),
        ),
        (
          [ ? ],
          ([$2 arrow 0$]),
          ([#encircle($3$)]),
        ),
      ),
      ([ ?\* ],
        (
          [ ? ],
          ([$4 arrow 0$]),
          ([$5 arrow 1$]),
        ),
        (
          [ ? ],
          ([$6 arrow 2$]),
          ([#encircle($7$)]),
        ),
      )
    ))
})]

== An efficient implementation

=== segments

We define *segments* as a monotone increasing subsequence in Luby sequence. Here are the first 16 segments. Each segment is alternately in red and blue.

#let luby = (1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 16)

#let even = true
#luby.insert(0, luby.at(0) - 1)
#for (p, n) in luby.windows(2) {
  even = if p < n { even } else { not even }
  text(fill: if even { red } else { blue }, str(n) + ", ")
}

As you see, the Luby value is equal to two powered by a local index in a segment. So we can define Luby sequence in another form.

#figure(caption: [local index and segment index], gap: 16pt)[
#canvas({
  import draw: *
  let encircle(i) = {
    std.box(baseline: 2pt, std.circle(stroke: .5pt, radius: .5em)[#move(dx: -0.36em, dy: -1.1em, $#i$)])
  }

  set-style(content: (padding: 0.5em))
  tree.tree(
    ([$4="b100"$ #encircle(2)],
      (
        [$2="b10"$ #encircle(1)],
        ([$1="b1"$ #encircle($0$)]),
        ([2 #encircle($0$)]),
      ),
      (
        [4 #encircle($1$)],
        ([$3=b"11"$ #encircle($0$)]),
        ([4 #encircle($0$)]),
      ),
    ))
})]

=== Luby state `S`
#figure(caption: [The definition of Luby Status `S`])[
  #align(left)[
```lean
structure S where
  segIx : Nat  -- 単調増加部分数列(segment)の何番目か(1-based)
  locIx : Nat　-- 現在のsegment内で何番目(local index)か(0-based)

def S.next (self : S) : S := ...
def S.luby (self : S) : Nat = 2 ^ self.locIx
```
]]<def_S>

#figure(caption: [Generating Luby state], gap: 16pt)[
#diagram(cell-size: 12mm, {
  node((1, 0), $n$)
  edge((1, 0), (1, 2),  $O(log(n))$, label-pos: 25%, bend: -30deg, "-straight")
  edge((1, 0), (1, 1), "<-->")
  node((0, 1), $S_0$)
  edge((0, 1), (1, 1), "~>")
  node((2, 0), $n + 1$)
  edge((2, 0), (2, 2), $O(log(n + 1))$, label-pos: 25%, bend: 30deg, "-straight")
  edge((2, 0), (2, 1), "<-->")
  node((1, 1), $S_n$)
  edge((1, 1), (2, 1), $O(1)$, "->")
  edge((1, 1), (1, 2), $O(1)$, label-side: left, "-straight")
  node((2, 1), $S_(n + 1)$)
  edge((2, 1), (2, 2), $O(1)$, label-side: right, "-straight")
	node((1, 2), $L u b y(n)$)
	node((2, 2), $L u b y(n + 1)$)
})]

= Equivalence of $L u b y$ and Luby state `S`

#figure(caption: "Main goal")[
#align(left)[
```lean
-- the main goal
theorem S_is_luby : ∀ n ≥ 1, (↑ n : S).luby = Luby n := by
    sorry
```
]]<t1>
