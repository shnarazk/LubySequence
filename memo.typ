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

$1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 16, 1, dots.h.c $

== Definition

$
  L u b y_1(k >= 1) = cases(
    2^(i-1)\, & " if" k = 2^i - 1 " for some " i >= 1,
    L u b y_1(k - 2^(i-1) + 1)\, & " if " 2^(i-1) <= k < 2^i - 1
  )
$
== An interpretation on binary trees

#canvas({
  import draw: *
  let encircle(i) = {
    std.box(baseline: 2pt, std.circle(stroke: .5pt, radius: .5em)[#move(dx: -0.36em, dy: -1.1em, $#i$)])
  }

  set-style(content: (padding: 0.5em))
  tree.tree(
    ([ 6 = b110 #encircle($1$)],
      (
        [ 2 = b010 #encircle($1$)],
        ([ 0 = b000 #encircle($0$)]),
        ([ 1 = b001 #encircle($1$)]),
      ),
      (
        [ 5 = b101 #encircle($1$)],
        ([ 3 = b011 #encircle($0$)]),
        ([ 4 = b100 #encircle($1$)]),
      ),
    ))
})

#figure(caption: [Binary tree starting at one], gap: 16pt)[
#canvas({
  import draw: *
  let encircle(i) = {
    std.box(baseline: 2pt, std.circle(stroke: .5pt, radius: .5em)[#move(dx: -0.36em, dy: -1.1em, $#i$)])
  }

  set-style(content: (padding: 0.5em))
  tree.tree(
    ([ 7 = b111 #encircle($1$)],
      (
        [ 3 = b011 #encircle($1$)],
        ([ 1 = b001 #encircle($1$)]),
        ([ 2 = b010 #encircle($1$)]),
      ),
      (
        [ 6 = b110 #encircle($1$)],
        ([ 4 = b100 #encircle($0$)]),
        ([ 5 = b101 #encircle($1$)]),
      ),
    ))
})]

== An efficient implementation

=== segments

#let segs = (
  (1,), (1, 2), (1,), (1, 2, 4), (1,), (1, 2), (1,), (1, 2, 4, 8),
  (1,), (1, 2), (1,), (1, 2, 4), (1,), (1, 2), (1,), (1, 2, 4, 8, 16)
)
// | 1 | 1 2 | 1 | 1 2 4 | 1 | 1 2 | 1 | 1 2 4 8 16 | 1 )
#let even = true
#for seg in segs {
  let clr = if even { red } else { blue }
  even = not even
  text(fill: clr, seg.map(str).join(", ") + ", ")
}

#figure(caption: [The definition of Luby Status `S`])[
  #align(left)[
```lean
structure S where
  segIx : Nat  -- 単調増加部分数列(segment)の何番目か(0-based)
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

= Equality

#figure(caption: "Main goal")[
#align(left)[
```lean
-- the main goal
theorem S_is_luby : ∀ n ≥ 1, (↑ n : S).luby = Luby n := by
    sorry
```
]]<t1>
