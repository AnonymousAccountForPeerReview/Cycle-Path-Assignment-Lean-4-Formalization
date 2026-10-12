module

public import NPHardness.PlanarSourceEmbedding

/-! Component-count preservation for the explicit implication-ring expansion.
Original dart paths are simulated by paths in the expanded hypermap. Every
new dart reaches the old variable-side dart in its six-dart block. Mapping
component minima back to original darts therefore gives an injection into
the original component minima. -/

@[expose] public section
namespace STACS2027.PlanarSource.Embedding
open Complexity Complexity.Planar

/-- Unbounded reachability, using the registered finite-step predicate. -/
def Reaches {n : Nat} (G : Hypermap n) (x y : Fin n) : Prop :=
  ∃ k, G.linked k x y = true

theorem Reaches.refl {n : Nat} (G : Hypermap n) (x : Fin n) : Reaches G x x :=
  ⟨0, Linked.linked_refl G 0 x⟩

theorem Reaches.trans {n : Nat} {G : Hypermap n} {x y z : Fin n}
    (h : Reaches G x y) (h' : Reaches G y z) : Reaches G x z := by
  obtain ⟨k,hk⟩ := h
  obtain ⟨l,hl⟩ := h'
  exact ⟨k+l, Linked.linked_trans G hk hl⟩

theorem Reaches.step {n : Nat} (G : Hypermap n) {x y : Fin n}
    (h : Linked.Step G x y) : Reaches G x y :=
  ⟨1, Linked.linked_step G (Linked.linked_refl G 0 x) h⟩

theorem Reaches.edge {n : Nat} (G : Hypermap n) (x : Fin n) : Reaches G x (G.edge x) :=
  Reaches.step G (Or.inl rfl)

theorem Reaches.node {n : Nat} (G : Hypermap n) (x : Fin n) : Reaches G x (G.node x) :=
  Reaches.step G (Or.inr (Or.inl rfl))

theorem Reaches.face {n : Nat} (G : Hypermap n) (x : Fin n) : Reaches G x (G.face x) :=
  Reaches.step G (Or.inr (Or.inr rfl))

namespace BipartiteRotation
variable {E : Nat} (B : BipartiteRotation E)

def liftOriginal (d : Fin (2*E)) : Fin (6*E) :=
  if d.val % 2 = 0 then d6 (index 2 (by decide) d) 0 else d6 (index 2 (by decide) d) 1

@[simp] theorem liftOriginal_zero (i : Fin E) : liftOriginal (d2 i 0) = d6 i 0 := by
  simp [liftOriginal, d2]

theorem expanded_ring_reaches (i : Fin E) :
    Reaches B.expanded (d6 i 0) (d6 (B.varRot.toFun i) 0) := by
  have h02 : Reaches B.expanded (d6 i 0) (d6 i 2) := by
    simpa [expanded, newNode, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using Reaches.node B.expanded (d6 i 0)
  have h23 : Reaches B.expanded (d6 i 2) (d6 i 3) := by
    simpa [expanded, newEdge, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using Reaches.edge B.expanded (d6 i 2)
  have h34 : Reaches B.expanded (d6 i 3) (d6 i 4) := by
    simpa [expanded, newNode, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using Reaches.node B.expanded (d6 i 3)
  have h45 : Reaches B.expanded (d6 i 4) (d6 i 5) := by
    simpa [expanded, newEdge, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using Reaches.edge B.expanded (d6 i 4)
  have h50 : Reaches B.expanded (d6 i 5) (d6 (B.varRot.toFun i) 0) := by
    simpa [expanded, newNode, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using Reaches.node B.expanded (d6 i 5)
  exact h02.trans (h23.trans (h34.trans (h45.trans h50)))

theorem expanded_to_block (d : Fin (6*E)) :
    Reaches B.expanded d (d6 (index 6 (by decide) d) 0) := by
  apply six_cases (fun d => Reaches B.expanded d (d6 (index 6 (by decide) d) 0)) ?_ d
  intro i
  have h10 : Reaches B.expanded (d6 i 1) (d6 i 0) := by
    simpa [expanded, newEdge, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using Reaches.edge B.expanded (d6 i 1)
  have h30 : Reaches B.expanded (d6 i 3) (d6 i 0) := by
    simpa [expanded, newFace, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using Reaches.face B.expanded (d6 i 3)
  have h23 : Reaches B.expanded (d6 i 2) (d6 i 3) := by
    simpa [expanded, newEdge, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using Reaches.edge B.expanded (d6 i 2)
  have h43 : Reaches B.expanded (d6 i 4) (d6 i 3) := by
    simpa [expanded, newNode, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using Reaches.node B.expanded (d6 i 4)
  have h53 : Reaches B.expanded (d6 i 5) (d6 i 3) := by
    simpa [expanded, newFace, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using Reaches.face B.expanded (d6 i 5)
  simpa [d6] using And.intro (Reaches.refl B.expanded (d6 i 0))
    ⟨h10,h23.trans h30,h30,h43.trans h30,h53.trans h30⟩

theorem lift_original_edge (d : Fin (2*E)) :
    Reaches B.expanded (liftOriginal d) (liftOriginal (B.original.edge d)) := by
  apply two_cases (fun d => Reaches B.expanded (liftOriginal d) (liftOriginal (B.original.edge d))) ?_ d
  intro i
  constructor
  · simpa [original, oldEdge, expanded, newEdge, liftOriginal, d2, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using
      Reaches.edge B.expanded (d6 i 0)
  · simpa [original, oldEdge, expanded, newEdge, liftOriginal, d2, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using
      Reaches.edge B.expanded (d6 i 1)

theorem lift_original_node (d : Fin (2*E)) :
    Reaches B.expanded (liftOriginal d) (liftOriginal (B.original.node d)) := by
  apply two_cases (fun d => Reaches B.expanded (liftOriginal d) (liftOriginal (B.original.node d))) ?_ d
  intro i
  constructor
  · simpa [original, oldNode, liftOriginal, d2, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using B.expanded_ring_reaches i
  · simpa [original, oldNode, expanded, newNode, liftOriginal, d2, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using
      Reaches.node B.expanded (d6 i 1)

theorem lift_original_face (d : Fin (2*E)) :
    Reaches B.expanded (liftOriginal d) (liftOriginal (B.original.face d)) := by
  apply two_cases (fun d => Reaches B.expanded (liftOriginal d) (liftOriginal (B.original.face d))) ?_ d
  intro i
  constructor
  · simpa [original, oldFace, expanded, newFace, liftOriginal, d2, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using
      Reaches.face B.expanded (d6 i 0)
  · have h15 : Reaches B.expanded (d6 i 1) (d6 (B.varRot.invFun i) 5) := by
      simpa [expanded, newFace, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using Reaches.face B.expanded (d6 i 1)
    have h50 := B.expanded_to_block (d6 (B.varRot.invFun i) 5)
    simpa [original, oldFace, liftOriginal, d2, d6, show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
      show (5 : Fin 6).val = 5 from rfl] using h15.trans h50

theorem lift_original_linked {k : Nat} {x y : Fin (2*E)}
    (h : B.original.linked k x y = true) :
    Reaches B.expanded (liftOriginal x) (liftOriginal y) := by
  induction k generalizing y with
  | zero =>
    have he := (Linked.linked_zero B.original x y).mp h
    subst y
    exact Reaches.refl _ _
  | succ k ih =>
    rcases (Linked.linked_succ B.original k x y).mp h with h | ⟨z,hz,hs⟩
    · exact ih h
    · have hr := ih hz
      rcases hs with h | h | h
      · rw [← h]; exact hr.trans (B.lift_original_edge z)
      · rw [← h]; exact hr.trans (B.lift_original_node z)
      · rw [← h]; exact hr.trans (B.lift_original_face z)

/-- The registered Boolean predicate selecting a component's least dart. -/
def componentMinimum {n : Nat} (G : Hypermap n) (x : Fin n) : Bool :=
  (List.finRange n).all fun y => !G.linked n x y || Nat.ble x.val y.val

theorem componentMinimum_spec {n : Nat} (G : Hypermap n) (x : Fin n) :
    componentMinimum G x = true ↔ ∀ y, Reaches G x y → x.val ≤ y.val := by
  constructor
  · intro h y hy
    obtain ⟨k,hk⟩ := hy
    have hs := Linked.linked_stable G hk
    have h' := List.all_eq_true.mp h y (List.mem_finRange y)
    simpa only [hs, Bool.not_true, Bool.false_or, Nat.ble_eq] using h'
  · intro h
    apply List.all_eq_true.mpr
    intro y _
    cases he : G.linked n x y with
    | false => simp
    | true => simpa only [Bool.not_true, Bool.false_or, Nat.ble_eq] using h y ⟨n,he⟩

theorem expanded_minimum_block {d : Fin (6*E)}
    (hd : componentMinimum B.expanded d = true) :
    d6 (index 6 (by decide) d) 0 = d := by
  have hle := (componentMinimum_spec B.expanded d).mp hd _ (B.expanded_to_block d)
  apply Fin.ext
  change 6 * (d.val / 6) + 0 = d.val
  change d.val ≤ 6 * (d.val / 6) + 0 at hle
  have hdiv := Nat.div_add_mod d.val 6
  omega

theorem expanded_minimum_original {i : Fin E}
    (hi : componentMinimum B.expanded (d6 i 0) = true) :
    componentMinimum B.original (d2 i 0) = true := by
  apply (componentMinimum_spec B.original (d2 i 0)).mpr
  intro y hy
  obtain ⟨k,hk⟩ := hy
  have hr := B.lift_original_linked hk
  rw [liftOriginal_zero] at hr
  have hle := (componentMinimum_spec B.expanded (d6 i 0)).mp hi _ hr
  change 2 * i.val + 0 ≤ y.val
  unfold liftOriginal at hle
  split at hle
  all_goals
    change 6*i.val+0 ≤ 6*(y.val/2)+_ at hle
    have hdiv := Nat.div_add_mod y.val 2
    have hmod := Nat.mod_lt y.val (by decide : 0 < 2)
    omega

def componentBack (d : Fin (6*E)) : Fin (2*E) := d2 (index 6 (by decide) d) 0

theorem componentBack_minimum {d : Fin (6*E)}
    (hd : componentMinimum B.expanded d = true) :
    componentMinimum B.original (componentBack d) = true := by
  have hblock := B.expanded_minimum_block hd
  unfold componentBack
  apply B.expanded_minimum_original
  rwa [hblock]

theorem componentBack_injective_on_minima {d e : Fin (6*E)}
    (hd : componentMinimum B.expanded d = true)
    (he : componentMinimum B.expanded e = true)
    (hde : componentBack d = componentBack e) : d = e := by
  have hindex := congrArg (index 2 (by decide)) hde
  simp only [componentBack, d2, index_dart] at hindex
  exact (B.expanded_minimum_block hd).symm.trans
    ((congrArg (fun i => d6 i 0) hindex).trans (B.expanded_minimum_block he))

/-- Replacing every variable node by the explicit implication ring introduces
no connected component. No assumption about component labels is needed. -/
theorem expanded_componentCount_le :
    B.expanded.componentCount ≤ B.original.componentCount := by
  let xs := (List.finRange (6*E)).filter (componentMinimum B.expanded)
  have hn : (xs.map componentBack).Nodup := by
    apply nodup_map_of_injOn _ (nodup_filter_finRange _ _)
    intro d hd e he hde
    exact B.componentBack_injective_on_minima (List.mem_filter.mp hd).2
      (List.mem_filter.mp he).2 hde
  have hP : ∀ x ∈ xs.map componentBack, componentMinimum B.original x = true := by
    intro x hx
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hx
    exact B.componentBack_minimum (List.mem_filter.mp hd).2
  have hc := length_le_countP (componentMinimum B.original) (xs.map componentBack) hn hP
  change (List.finRange (6*E)).countP (componentMinimum B.expanded) ≤
    (List.finRange (2*E)).countP (componentMinimum B.original)
  simpa only [List.length_map, xs, List.countP_eq_length_filter] using hc

end BipartiteRotation
end STACS2027.PlanarSource.Embedding
