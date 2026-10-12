module

public import Outerplanar

/-! Proofs of the sixteen compared theorems listed in `comparator.json`:
`STACS2027.outerplanar_block_structure` (`Outerplanar/OuterplanarCharacterization.lean`), `STACS2027.k23_perfect`
(`Outerplanar/PerfectK23.lean`), `STACS2027.k23_linear_ram` and `STACS2027.outerplanar_linear_ram`
(`Outerplanar/LinearK23.lean`), `STACS2027.common_neighbours_le_two` (`Outerplanar/Minors.lean`),
`STACS2027.IsPolygon.euler_face_count` (`Outerplanar/WeakDualFacts.lean`),
`STACS2027.IsPolygon.cycle_subtree_bij` and `STACS2027.IsPolygon.cycle_subtree_bij_simpleCycles`
(`Outerplanar/WeakDualBij.lean`), and `STACS2027.IsPolygon.face_cycle_bound` and
`STACS2027.IsPolygon.edge_cycle_bound` (`Outerplanar/WeakDualCount.lean`), and the paper bounds
`STACS2027.IsPolygon.enclosed_faces_bound` and `STACS2027.IsPolygon.enclosing_cycle_count_bound`
and `STACS2027.IsPolygon.cycle_child_dichotomy` (`Outerplanar/NamedHoles.lean`). The exact leaf deletion target `STACS2027.IsPolygon.leaf_face_deletion` is proved in
`Outerplanar/LeafFaceDeletion.lean`. Importing `Outerplanar`
brings in, and audits, the whole library. -/
