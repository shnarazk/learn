#!/usr/bin/env julia

using Plots
# %%

# Simple example: plot sin(x) over [0, 2π] and save to `sine.png` next to this script.

xs = range(0, 2π; length = 200)
ys = sin.(xs)

# %%

p = plot(
    xs,
    ys;
    label = "sin(x)",
    xlabel = "x (radians)",
    ylabel = "y",
    title = "Sine Wave",
    linewidth = 3,
    grid = :on,
)

# %%

scatter!(
    p,
    [π / 2, 3π / 2],
    sin.([π / 2, 3π / 2]);
    label = "peaks/troughs",
    marker = :circle,
    markersize = 5,
)

# %%
