#import "@preview/cetz:0.4.1": canvas, draw, tree
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#set page(paper: "a4", numbering: "1")
// #set text(font: ("Monaspace Argon", "Hiragino Maru Gothic Pro"))
#set par(justify: true)
#set text(font: ("New Computer Modern", "Hiragino Mincho Pro"))
// #show raw: set text(font: "New Computer Modern Mono")
#set heading(numbering: "1.")

= Introduction, 導入のこと<p>

In this report, we will explore the
various factors that influence fluid
dynamics in #text(style: "italic", [glacier]) and how they
contribute to the formation and
behaviour of these natural structures.

+ The climate
+ The topography
  + second level
  + part 2
+ The geology

#show raw: it => {
  if it.block [ #block(width: 98%, inset: 8pt, radius: 2pt, fill: luma(245), it) ] else [ #it ]
}

#figure(caption: "Main goal")[
```lean
-- a sample code
theorem luby_is_const : Constant Luby.eval := by sorry
```
]<t1>

This is a #highlight(fill: green, extent: 5pt, text(fill:red, [`code`])) . This is another one: #("foo(1, #baz)")

See #ref(<p>, form: "normal"), #ref(<p>, form: "page")

See #ref(<t1>, form: "normal"), #ref(<t1>, form: "page")

$
  L u b y_1(k >= 1) = cases(
    2^(i-1)\, & " if" k = 2^i - 1 " for some " i >= 1,
    L u b y_1(k - 2^(i-1) + 1)\, & " if " 2^(i-1) <= k < 2^i - 1
  )
$

```latex
\begin{equation}
  Luby_1(k \ge 1) =
  \begin{cases}
    2^{i-1}, & \text{if } k = 2^i - 1 \text{ for some } i \geq 1, \\
    Luby_1\left(k - 2^{i-1} + 1\right), & \text{if } 2^{i-1} \leq k < 2^i - 1
  \end{cases}
\end{equation}
```

#diagram(cell-size: 15mm, $
	G edge(f, ->) edge("d", pi, ->>) & im(f) \
	G slash ker(f) edge("ur", tilde(f), "hook-->")
$)

#canvas({
  import draw: *
  let encircle(i) = {
    std.box(baseline: 2pt, std.circle(stroke: .5pt, radius: .5em)[#move(dx: -0.36em, dy: -1.1em, $#i$)])
  }

  set-style(content: (padding: 0.5em))
  tree.tree(
    ([Expression #encircle($5$)], (
        [Expression #encircle($3$)],
        ([Expression #encircle($1$)], `Int(1)`),
        `Plus`,
        ([Expression #encircle($2$)], `Int(2)`),
      ),
      `Lt`,
      ([Expression #encircle($4$)], `Int(4)`),
    ))
})
