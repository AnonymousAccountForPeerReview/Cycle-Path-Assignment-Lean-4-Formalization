# Gadget map: Appendix C and Figure 4 in Lean

This file maps the gadgets of paper (Appendix C, Steps 1–4,
drawn in Figure 4) to the constructors in `NPHardness/Gadgets.lean`. Every
correspondence stated here is also proved in `NPHardness/Paper.lean`, which is
built and axiom-checked with the rest of the library.

Edges are unordered and stored with the smaller endpoint first. For `k ≥ 6` a
subdivided edge becomes a path whose new vertices are numbered after the named
vertices, in link order.

## Variable gadget `γ_x` (Step 1, Figure 4(a))

The manuscript does not number these vertices. Lean numbers the corners of
Figure 4(a):

| Lean | Position in Figure 4(a) |
|---:|---|
| 0 | top left |
| 1 | top middle |
| 2 | top right |
| 3 | middle left |
| 4 | middle |
| 5 | bottom middle |
| 6 | bottom right |

| Appendix C | Lean | Lean name |
|---|---|---|
| `e_(x,True,1)` (blue) | `(2,6)` | `Paper.trueEdge`, `variablePorts[0]` |
| `e_(x,False,1)` (red, incident to `s_x`) | `(4,5)` | `Paper.falseEdge1`, `variablePorts[1]` |
| `e_(x,False,2)` (red) | `(0,3)` | `Paper.falseEdge2`, `variablePorts[2]` |
| `s_x` | `(1,4)` | `Paper.sharedEdge` |
| `C^α_x` before subdivision | `[0,1,4,3]` | `Paper.alphaCycle` |
| `C^β_x` before subdivision | `[1,2,6,5,4]` | `Paper.betaCycle` |
| the remaining cycle, length `2k−2` | `[0,1,2,6,5,4,3]` | `Paper.outerCycle` |

The dashed gray paths are the links `0–1`, `1–2`, `3–4` and `5–6`, of lengths
`⌊(k−1)/2⌋`, `⌊(k−3)/2⌋`, `⌊(k−2)/2⌋` and `⌊(k−2)/2⌋`. These are the Step 1
lengths: in `C^α_x`, path `3–4` joins `e_(x,False,2)` to the common endpoint 4
of `s_x` and `e_(x,False,1)`, and path `0–1` joins it to the other endpoint 1
of `s_x`; in `C^β_x`, path `5–6` joins `e_(x,False,1)` to `e_(x,True,1)`, and
path `1–2` joins `s_x` to `e_(x,True,1)`.

Proved in `Paper`: `step1_incidences`, `step1_lengths`, `step1_cycle_lengths`
(`k`, `k`, `2k−2`), `step1_cycles` (every simple cycle is one of the three),
`step1_k_cycles`, `observation_o1_2_variable` (ports at distance at least
`⌊(k−2)/2⌋`), and `step1_truth_states` (the two disjoint normalized states,
with "True" leaving `e_(x,True,1)` unused and "False" leaving both
`e_(x,False,j)` unused).

## Three-literal clause gadget `ζ_(c,3)` (Step 2, Figure 4(b))

Lean vertex `v` is Appendix C vertex `v + 1`. `clauseThreeLinks` is Step 2's
edge list in printed order, renumbered; `Paper.step2_links` proves this for
every `k`, and `Paper.step2_k5` checks the `k = 5` edge set literally.

| Appendix C | Lean | Position in Figure 4(b) |
|---:|---:|---|
| 1 | 0 | right endpoint of the upper purple edge |
| 2 | 1 | left endpoint of the upper purple edge |
| 3 | 2 | upper-left branch junction |
| 4 | 3 | left endpoint of the long horizontal edge |
| 5 | 4 | upper endpoint of the lower-left purple edge |
| 6 | 5 | lower endpoint of the lower-left purple edge |
| 7 | 6 | left endpoint of the bottom horizontal edge |
| 8 | 7 | right endpoint of the bottom horizontal edge |
| 9 | 8 | lower-right outer bend beside the inner horizontal edge |
| 10 | 9 | lower-right branch junction |
| 11 | 10 | right endpoint of the long horizontal edge |
| 12 | 11 | upper endpoint of the right purple edge |
| 13 | 12 | upper-right outer bend |
| 14 | 13 | middle vertex of the upper vertical path |
| 15 | 14 | upper central branch junction |
| 16 | 15 | lower central branch junction |
| 17 | 16 | left endpoint of the lower inner horizontal edge |
| 18 | 17 | right endpoint of the lower inner horizontal edge |

| Appendix C | Lean |
|---|---|
| `e_(c,1)`, `e_(c,2)`, `e_(c,3)` = `(1,2)`, `(5,6)`, `(11,12)` | `clausePorts` = `(0,1)`, `(4,5)`, `(10,11)` (slots 0, 1, 2) |
| green: `(1,13)`, `(2,3)`, `(3,4)`, `(6,7)`, `(8,9)`, `(9,10)`, `(10,11)` | `(0,12)`, `(1,2)`, `(2,3)`, `(5,6)`, `(7,8)`, `(8,9)`, `(9,10)`, each `k−5` times |

## Two-literal clause gadget `ζ_(c,2)` (Step 3, Figure 4(c))

`clauseTwoLinks` is `clauseThreeLinks` followed by Step 3's ten edges in
printed order, renumbered; `Paper.step3_links` proves this for every `k`, with
Step 3's subdivision rule (`Paper.step3Subdivisions`), and `Paper.step3_k5`
checks the `k = 5` edge set literally. The edge `e_(c,3)` stays an ordinary
edge, loaded by the auxiliary part.

| Appendix C | Lean | Position in Figure 4(c) |
|---:|---:|---|
| 19 | 18 | bend between the clause part and the auxiliary square |
| 20 | 19 | bottom left of the square |
| 21 | 20 | top left of the square |
| 22 | 21 | inner vertex of the square |
| 23 | 22 | bottom right of the square |
| 24 | 23 | top right of the square |

| Appendix C | Lean | Subdivisions |
|---|---|---|
| `(11,19)`, `(12,21)`, `(20,21)`, `(20,23)` | `(10,18)`, `(11,20)`, `(19,20)`, `(19,22)` | none |
| green `(19,20)` | `(18,19)` | `k−5` |
| orange `(21,22)`, `(21,24)` | `(20,21)`, `(20,23)` | `⌊(k−5)/2⌋`, none if `k = 6` (`orangeSubdivisions`) |
| blue `(22,23)`, `(23,24)` | `(21,22)`, `(22,23)` | `⌈(k−5)/2⌉`, none if `k = 6` (`blueSubdivisions`) |
| red `(22,24)` | `(21,23)` | none, once if `k = 6` (`redSubdivisions`) |

## Edge identification (Step 4, Definition 22)

Literals are processed in formula order. `PlacedLiteral.port` is 0 for a
positive literal and `j` for the `j`-th negative occurrence of its variable, so
port 0 is `e_(x,True,1)` and ports 1 and 2 are `e_(x,False,1)` and
`e_(x,False,2)`: the smallest index not yet used, as in Step 4. The literal in
slot `i` of a clause uses `e_(c,i+1)`. `Paper.step4_variable_port`,
`Paper.step4_port_edges` and `Paper.step4_identification` state this.

Definition 22 lets each identification order its endpoints arbitrarily.
`formulaGraph` uses `variableEndpoint` and `clauseEndpoint` (left to left,
right to right); `orientedFormulaGraph flips` reverses the identifications
selected by `flips`. Correctness holds for every choice
(`Paper.gadget_reduction_any_endpoints`), and some choice is planar when the incidence
graph is (`Paper.gadget_reduction_planar`). A fixed choice is not enough:
`Paper.fixed_endpoints_K33` exhibits a Planar-(≤1,≤2)-SAT formula whose fixed gluing
contains a subdivision of `K_{3,3}`.

## Edge counts

For every `k ≥ 5`: variable gadget `2k − 1`, three-literal gadget `7k − 11`,
two-literal gadget `10k − 16`, or `43` when `k = 6` (`Gadgets.lean`).
