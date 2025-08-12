#set page(paper: "a4")
#set text(font: ("Monaspace Argon", "Hiragino Maru Gothic Pro"))
#set par(justify: true)

= Introduction, 導入のこと

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
  if it.block [ #block(width: 90%, inset: 8pt, radius: 2pt, fill: luma(235), it) ] else [ it.body ]
}

```lean
-- a sample code
theorem luby_is_const : Constant Luby.eval := by sorry
```

This is a #highlight(fill: green, extent: 5pt, text(fill:red, [`code`])) . This is another one: #("foo(1, #baz)")

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
