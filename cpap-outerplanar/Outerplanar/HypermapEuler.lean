module

public import Outerplanar.OuterplanarDef
public import Outerplanar.HypermapEulerMove
import Lean.Elab.Tactic.Omega

/-!
# Euler's inequality and the parity of the Euler characteristic for hypermaps

`hypermapEuler : HypermapEuler`: for every hypermap `G` (the NP-completeness foundation's
`Complexity.Hypermap`, with its counts `cycleCount`, `componentCount`),
`G.eulerRhs ≤ G.eulerLhs` and `G.eulerLhs - G.eulerRhs` is even. Consequently a hypermap is
`Planar` (genus `0`) exactly when `eulerLhs = eulerRhs` (`Hypermap.planar_iff_euler_eq`).

The proof is the algebraic form of ANONYMIZED's walkup induction. Write `EulerOK G` for the
statement. The edge transposition `moveE G b` of `Outerplanar/HypermapEulerMove.lean` (for a
dart `b` moved by `edge`) adds one edge cycle, keeps `node`, and either adds one face cycle
and at most one component, or removes one face cycle and adds no component; in both cases
`eulerLhs - eulerRhs` does not increase and keeps its parity, so `EulerOK (moveE G b)`
implies `EulerOK G` (`eulerOK_of_moveE`). Since `moveE` moves fewer darts by `edge`,
induction reduces `EulerOK G` to the hypermaps with the same `node` and identity `edge`
(`eulerOK_induct`). Two rounds of this reduction, with the cyclic rotation
`(edge, node, face) ↦ (face, edge, node)` (`rot`, which preserves all the counts) in
between, reduce everything to the hypermap whose three permutations are the identity, where
`eulerLhs = eulerRhs = 3n`.
-/

@[expose] public section

namespace STACS2027.HypEuler

open Complexity Complexity.Planar STACS2027.PlanarGluing

variable {n : Nat}

/-- The conclusion of `HypermapEuler` for one hypermap. -/
def EulerOK (G : Hypermap n) : Prop :=
  G.eulerRhs ≤ G.eulerLhs ∧ (G.eulerLhs - G.eulerRhs) % 2 = 0

/-- **The step**: Euler's inequality and parity pass from the edge transposition back to the
hypermap. -/
theorem eulerOK_of_moveE (G : Hypermap n) (b : Fin n) (hb : G.edge b ≠ b)
    (h : EulerOK (moveE G b)) : EulerOK G := by
  have hE := moveE_edge_cycles G b hb
  have hC1 := moveE_components_le_add_one G b
  have hN : cycleCount (moveE G b).node = cycleCount G.node := rfl
  unfold EulerOK Hypermap.eulerLhs Hypermap.eulerRhs at h ⊢
  by_cases hc : cmin G.face (G.edge (G.edge b)) = cmin G.face (G.edge b)
  · have hF := moveE_face_split G b hb hc
    omega
  · have hF := moveE_face_merge G b hc
    have hC := moveE_components_le_of_faces_ne G b hc
    omega

/-- **Reduction to an identity `edge`**: to prove `EulerOK G` it suffices to prove it for the
hypermaps with the node permutation of `G` and the identity edge permutation. -/
theorem eulerOK_induct (G : Hypermap n)
    (hbase : ∀ G' : Hypermap n, G'.node = G.node → (∀ x, G'.edge x = x) → EulerOK G') :
    EulerOK G := by
  suffices h : ∀ m, ∀ G' : Hypermap n, G'.node = G.node → nonFixed G'.edge ≤ m → EulerOK G'
    from h _ G rfl (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro G' hn hm
    by_cases hall : ∀ x, G'.edge x = x
    · exact hbase G' hn hall
    · obtain ⟨b, hb⟩ := Classical.not_forall.mp hall
      have := moveE_nonFixed_lt G' b hb
      omega
  | succ m ih =>
    intro G' hn hm
    by_cases hall : ∀ x, G'.edge x = x
    · exact hbase G' hn hall
    · obtain ⟨b, hb⟩ := Classical.not_forall.mp hall
      have := moveE_nonFixed_lt G' b hb
      exact eulerOK_of_moveE G' b hb (ih (moveE G' b) hn (by omega))

/-! ## The identity hypermap -/

theorem iterate_of_forall_fixed {p : Fin n → Fin n} (hp : ∀ x, p x = x) (k : Nat) (x : Fin n) :
    iterate p k x = x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [iterate, hp, ih]

theorem cycleCount_of_forall_fixed {p : Fin n → Fin n} (hp : ∀ x, p x = x) :
    cycleCount p = n := by
  rw [cycleCount_eq, List.countP_eq_length.mpr, List.length_finRange]
  intro x _
  simp [CycleMin, iterate_of_forall_fixed hp]

theorem linked_of_forall_fixed (G : Hypermap n) (he : ∀ x, G.edge x = x) (hn : ∀ x, G.node x = x)
    (hf : ∀ x, G.face x = x) (k : Nat) (x y : Fin n) (h : G.linked k x y = true) : x = y := by
  induction k generalizing y with
  | zero => exact (Linked.linked_zero G x y).mp h
  | succ k ih =>
    rcases (Linked.linked_succ G k x y).mp h with h | ⟨z, hz, hs⟩
    · exact ih y h
    · rcases hs with hs | hs | hs
      · rw [← hs, he]; exact ih z hz
      · rw [← hs, hn]; exact ih z hz
      · rw [← hs, hf]; exact ih z hz

/-- The hypermap whose three permutations are the identity: `eulerLhs = eulerRhs = 3n`. -/
theorem eulerOK_of_fixed (G : Hypermap n) (he : ∀ x, G.edge x = x) (hn : ∀ x, G.node x = x) :
    EulerOK G := by
  have hf : ∀ x, G.face x = x := by
    intro x
    have := G.edgeK x
    rwa [he, hn] at this
  have hC : G.componentCount = n := by
    unfold Hypermap.componentCount
    rw [List.countP_eq_length.mpr, List.length_finRange]
    intro x _
    simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
      Bool.not_eq_true', Nat.ble_eq]
    intro y
    by_cases h : G.linked n x y = true
    · right; rw [linked_of_forall_fixed G he hn hf n x y h]; exact Nat.le_refl _
    · left; simpa using h
  unfold EulerOK Hypermap.eulerLhs Hypermap.eulerRhs
  rw [cycleCount_of_forall_fixed he, cycleCount_of_forall_fixed hn,
    cycleCount_of_forall_fixed hf, hC]
  omega

/-! ## The cyclic rotation -/

/-- The cyclic rotation of a hypermap: `(edge, node, face) ↦ (face, edge, node)`. -/
def rot (G : Hypermap n) : Hypermap n where
  edge := G.face
  node := G.edge
  face := G.node
  edgeK x := by
    obtain ⟨z, rfl⟩ := hm_edge_surj G x
    rw [G.edgeK]

theorem rot_linked (G : Hypermap n) (k : Nat) (x y : Fin n) :
    (rot G).linked k x y = G.linked k x y := by
  have hs : ∀ z y, Linked.Step (rot G) z y ↔ Linked.Step G z y := by
    intro z y
    unfold Linked.Step
    simp only [rot]
    constructor
    · rintro (h | h | h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rintro (h | h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    apply Bool.eq_iff_iff.mpr
    rw [Linked.linked_succ, Linked.linked_succ]
    simp only [ih, hs]

theorem rot_eulerOK (G : Hypermap n) : EulerOK (rot G) ↔ EulerOK G := by
  have hC : (rot G).componentCount = G.componentCount := by
    unfold Hypermap.componentCount
    simp only [rot_linked]
  have hR : (rot G).eulerRhs = G.eulerRhs := by
    unfold Hypermap.eulerRhs
    simp only [rot]
    omega
  unfold EulerOK Hypermap.eulerLhs at *
  rw [hC, hR]

/-! ## Euler's inequality and parity -/

theorem eulerOK_of_node_fixed (G : Hypermap n) (hn : ∀ x, G.node x = x) : EulerOK G :=
  eulerOK_induct G fun G' hn' he' => eulerOK_of_fixed G' he' (fun x => by rw [hn']; exact hn x)

theorem eulerOK_of_edge_fixed (G : Hypermap n) (he : ∀ x, G.edge x = x) : EulerOK G :=
  (rot_eulerOK G).mp (eulerOK_of_node_fixed (rot G) he)

theorem eulerOK (G : Hypermap n) : EulerOK G :=
  eulerOK_induct G fun G' _ he' => eulerOK_of_edge_fixed G' he'

end STACS2027.HypEuler

namespace STACS2027

/-- **Euler's inequality and the parity of the Euler characteristic for hypermaps**
(ANONYMIZED): for every hypermap `G`, `G.eulerRhs ≤ G.eulerLhs` and
`G.eulerLhs - G.eulerRhs` is even. -/
theorem hypermapEuler : HypermapEuler := fun _ G => HypEuler.eulerOK G

end STACS2027

namespace Complexity.Hypermap

/-- Given Euler's inequality and parity, a hypermap is planar (genus `0`) exactly when
`eulerLhs = eulerRhs`. -/
theorem planar_iff_eq (hE : STACS2027.HypermapEuler) {n : Nat} (G : Hypermap n) :
    G.Planar ↔ G.eulerLhs = G.eulerRhs := by
  obtain ⟨h1, h2⟩ := hE n G
  unfold Planar genus
  omega

/-- A hypermap is planar (genus `0`) exactly when `eulerLhs = eulerRhs`. -/
theorem planar_iff_euler_eq {n : Nat} (G : Hypermap n) : G.Planar ↔ G.eulerLhs = G.eulerRhs :=
  planar_iff_eq STACS2027.hypermapEuler G

end Complexity.Hypermap
