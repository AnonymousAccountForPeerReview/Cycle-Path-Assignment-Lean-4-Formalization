module

public import NPHardness.PlanarSourceEmbedding

/-! Cycle accounting for the explicit incidence ring expansion. -/

@[expose] public section
namespace STACS2027.PlanarSource.Embedding
open Complexity Complexity.Planar STACS2027.PlanarGluing

@[simp] theorem fin6_val_three : (3 : Fin 6).val = 3 := rfl
@[simp] theorem fin6_val_four : (4 : Fin 6).val = 4 := rfl
@[simp] theorem fin6_val_five : (5 : Fin 6).val = 5 := rfl

theorem dart_injective {E k : Nat} (hk : 0 < k) (t : Fin k) {i j : Fin E}
    (h : dart k hk i t = dart k hk j t) : i = j := by
  have := congrArg (index k hk) h
  simpa only [index_dart] using this

theorem dart_tags_ne {E k : Nat} (hk : 0 < k) {t u : Fin k} (htu : t ≠ u)
    (i j : Fin E) : dart k hk i t ≠ dart k hk j u := by
  intro he
  have := congrArg (fun d : Fin (k * E) => d.val % k) he
  simp only [dart_mod] at this
  exact htu (Fin.ext this)

theorem dart_map_nodup {E k : Nat} (hk : 0 < k) (t : Fin k) {xs : List (Fin E)}
    (h : xs.Nodup) : (xs.map fun i => dart k hk i t).Nodup :=
  nodup_map_of_injOn' _ h (fun _ _ _ _ he => dart_injective hk t he)

theorem dart_maps_disjoint {E k : Nat} (hk : 0 < k) {t u : Fin k} (htu : t ≠ u)
    (xs ys : List (Fin E)) :
    ∀ x ∈ xs.map (fun i => dart k hk i t),
      ∀ y ∈ ys.map (fun i => dart k hk i u), x ≠ y := by
  intro x hx y hy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
  exact dart_tags_ne hk htu i j

theorem reaches_map {α β : Type} (p : α → α) (q : β → β) (f : α → β)
    (hs : ∀ x, Reaches q (f x) (f (p x))) {x y : α} (h : Reaches p x y) :
    Reaches q (f x) (f y) := by
  obtain ⟨k, rfl⟩ := h
  induction k generalizing x with
  | zero => exact Reaches.refl _ _
  | succ k ih => exact (hs x).trans (ih (x := p x))

/-- Representatives reached from every dart give an upper bound on cycles. -/
theorem cycleCount_le_representatives {n : Nat} {p : Fin n → Fin n}
    (hp : ∀ a b, p a = p b → a = b) (rep : Fin n → Fin n) (xs : List (Fin n))
    (hr : ∀ x, Reaches p x (rep x)) (hm : ∀ x, rep x ∈ xs) :
    cycleCount p ≤ xs.length := by
  have hnd : ((cycleRoots p).map rep).Nodup := by
    apply nodup_map_of_injOn' _ (cycleRoots_nodup p)
    intro x hx y hy he
    have hx' := hr x
    rw [he] at hx'
    exact cycleRoots_eq_of_reaches hp hx hy (hx'.trans ((hr y).symm hp))
  have h := List.Nodup.length_le_of_subset hnd (l₂ := xs) (by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact hm y)
  simpa only [List.length_map, cycleRoots_length] using h

namespace BipartiteRotation
variable {E : Nat} (B : BipartiteRotation E)

noncomputable def oldNodeRep (d : Fin (2 * E)) : Fin (2 * E) :=
  if d.val % 2 = 0 then d2 (cmin B.varRot.toFun (index 2 (by decide) d)) 0
  else d2 (cmin B.clause.toFun (index 2 (by decide) d)) 1

def oldNodeReps : List (Fin (2 * E)) :=
  (cycleRoots B.varRot.toFun).map (fun i => d2 i 0) ++
    (cycleRoots B.clause.toFun).map (fun i => d2 i 1)

theorem oldNode_reaches_rep : ∀ d, Reaches B.oldNode d (B.oldNodeRep d) := by
  apply two_cases
  intro i
  constructor
  · simp only [oldNodeRep, d2, dart_mod, Fin.val_zero, ↓reduceIte, index_dart]
    apply reaches_map B.varRot.toFun B.oldNode (fun j => d2 j 0) _ (reaches_cmin _ i)
    intro j
    refine ⟨1, ?_⟩
    simp [iterate, oldNode, d2]
  · simp only [oldNodeRep, d2, dart_mod, Fin.val_one, Nat.one_ne_zero,
      ↓reduceIte, index_dart]
    apply reaches_map B.clause.toFun B.oldNode (fun j => d2 j 1) _ (reaches_cmin _ i)
    intro j
    refine ⟨1, ?_⟩
    simp [iterate, oldNode, d2]

theorem oldNodeRep_mem : ∀ d, B.oldNodeRep d ∈ B.oldNodeReps := by
  apply two_cases
  intro i
  constructor
  · simp only [oldNodeRep, d2, dart_mod, Fin.val_zero, ↓reduceIte, index_dart]
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨_, cmin_mem_cycleRoots (fun _ _ h => B.varRot.injective h) i, rfl⟩
  · simp only [oldNodeRep, d2, dart_mod, Fin.val_one, Nat.one_ne_zero,
      ↓reduceIte, index_dart]
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨_, cmin_mem_cycleRoots (fun _ _ h => B.clause.injective h) i, rfl⟩

theorem original_node_count_le :
    cycleCount B.original.node ≤ cycleCount B.varRot.toFun + cycleCount B.clause.toFun := by
  have h := cycleCount_le_representatives (hm_node_inj B.original) B.oldNodeRep B.oldNodeReps
    B.oldNode_reaches_rep B.oldNodeRep_mem
  simpa only [oldNodeReps, List.length_append, List.length_map, cycleRoots_length] using h

noncomputable def newNodeRep (d : Fin (6 * E)) : Fin (6 * E) :=
  let i := index 6 (by decide) d
  match d.val % 6 with
  | 0 => d6 i 0
  | 1 => d6 (cmin B.clause.toFun i) 1
  | 2 => d6 i 0
  | 3 => d6 i 3
  | 4 => d6 i 3
  | _ => d6 (B.varRot.toFun i) 0

def newNodeReps : List (Fin (6 * E)) :=
  (List.finRange E).map (fun i => d6 i 0) ++
    ((List.finRange E).map (fun i => d6 i 3) ++
      (cycleRoots B.clause.toFun).map (fun i => d6 i 1))

theorem newNodeRep_step : ∀ d, B.newNodeRep (B.newNode d) = B.newNodeRep d := by
  apply six_cases
  intro i
  simp [newNodeRep, newNode, d6, B.varRot.right_inv,
    cmin_step (fun _ _ h => B.clause.injective h)]

theorem newNodeReps_nodup : B.newNodeReps.Nodup := by
  apply List.nodup_append.mpr
  refine ⟨dart_map_nodup _ _ (List.nodup_finRange E), ?_, ?_⟩
  · apply List.nodup_append.mpr
    exact ⟨dart_map_nodup _ _ (List.nodup_finRange E),
      dart_map_nodup _ _ (cycleRoots_nodup _),
      dart_maps_disjoint (by decide) (by decide : (3 : Fin 6) ≠ 1) _ _⟩
  · intro x hx y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact dart_maps_disjoint (by decide) (by decide : (0 : Fin 6) ≠ 3) _ _ x hx y hy
    · exact dart_maps_disjoint (by decide) (by decide : (0 : Fin 6) ≠ 1) _ _ x hx y hy

theorem newNodeReps_fixed : ∀ d ∈ B.newNodeReps, B.newNodeRep d = d := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
    simp [newNodeRep, d6]
  · rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
      simp [newNodeRep, d6]
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
      simp [newNodeRep, d6, (mem_cycleRoots (fun _ _ h => B.clause.injective h) i).mp hi]

theorem expanded_node_count_ge :
    2 * E + cycleCount B.clause.toFun ≤ cycleCount B.expanded.node := by
  change 2 * E + cycleCount B.clause.toFun ≤ cycleCount B.newNode
  have he : B.newNodeReps.map B.newNodeRep = B.newNodeReps := by
    conv => rhs; rw [← List.map_id B.newNodeReps]
    exact List.map_congr_left B.newNodeReps_fixed
  have h := cycleCount_ge B.newNode B.newNodeRep B.newNodeRep_step B.newNodeReps
    (by rw [he]; exact B.newNodeReps_nodup)
  simpa only [newNodeReps, List.length_append, List.length_map, List.length_finRange,
    cycleRoots_length, Nat.two_mul, Nat.add_assoc] using h

def liftOriginalFace (d : Fin (2 * E)) : Fin (6 * E) :=
  if d.val % 2 = 0 then d6 (index 2 (by decide) d) 0
  else d6 (index 2 (by decide) d) 1

noncomputable def newFaceLabel (d : Fin (6 * E)) : Sum (Fin E) (Fin (2 * E)) :=
  let i := index 6 (by decide) d
  match d.val % 6 with
  | 1 => .inr (cmin B.original.face (d2 i 1))
  | 2 => .inl (cmin B.varRot.toFun i)
  | 4 => .inl (cmin B.varRot.toFun i)
  | _ => .inr (cmin B.original.face (d2 i 0))

theorem newFaceLabel_lift : ∀ d, B.newFaceLabel (liftOriginalFace d) = .inr (cmin B.original.face d) := by
  apply two_cases
  intro i
  constructor <;> simp [newFaceLabel, liftOriginalFace, d2, d6]

theorem newFaceLabel_step : ∀ d, B.newFaceLabel (B.newFace d) = B.newFaceLabel d := by
  apply six_cases
  intro i
  have h0 := cmin_step (hm_face_inj B.original) (d2 i 0)
  have h1 := cmin_step (hm_face_inj B.original) (d2 i 1)
  have hf0 : B.original.face (d2 i 0) = d2 (B.clause.invFun i) 1 := by
    simp [original, oldFace, d2]
  have hf1 : B.original.face (d2 i 1) = d2 (B.varRot.invFun i) 0 := by
    simp [original, oldFace, d2]
  rw [hf0] at h0
  rw [hf1] at h1
  simp [newFaceLabel, newFace, d6, h0, h1,
    cmin_step (fun _ _ h => B.varRot.injective h)]

def newFaceReps : List (Fin (6 * E)) :=
  (cycleRoots B.varRot.toFun).map (fun i => d6 i 2) ++
    (cycleRoots B.original.face).map liftOriginalFace

theorem newFaceReps_labels :
    B.newFaceReps.map B.newFaceLabel =
      (cycleRoots B.varRot.toFun).map Sum.inl ++ (cycleRoots B.original.face).map Sum.inr := by
  rw [newFaceReps, List.map_append, List.map_map, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    simp [newFaceLabel, d6,
      (mem_cycleRoots (fun _ _ h => B.varRot.injective h) i).mp hi]
  · apply List.map_congr_left
    intro d hd
    simp only [Function.comp_apply, B.newFaceLabel_lift,
      (mem_cycleRoots (hm_face_inj B.original) d).mp hd]

theorem expanded_face_count_ge :
    cycleCount B.varRot.toFun + cycleCount B.original.face ≤ cycleCount B.expanded.face := by
  have hnd : (B.newFaceReps.map B.newFaceLabel).Nodup := by
    rw [B.newFaceReps_labels]
    apply List.nodup_append.mpr
    refine ⟨nodup_map_of_injOn' _ (cycleRoots_nodup _) ?_,
      nodup_map_of_injOn' _ (cycleRoots_nodup _) ?_, ?_⟩
    · intro x _ y _ he; exact Sum.inl.inj he
    · intro x _ y _ he; exact Sum.inr.inj he
    · intro x hx y hy he
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
      cases he
  have h := cycleCount_ge B.newFace B.newFaceLabel B.newFaceLabel_step B.newFaceReps hnd
  change cycleCount B.varRot.toFun + cycleCount B.original.face ≤ cycleCount B.newFace
  simpa only [newFaceReps, List.length_append, List.length_map, cycleRoots_length] using h

theorem original_edge_count_le : cycleCount B.original.edge ≤ E := by
  apply cycleCount_graphEdge_le
  apply two_cases
  intro i
  constructor <;> simp [original, oldEdge, d2] <;> simp [dart]

theorem expanded_edge_pairing : ∀ d : Fin (6 * E),
    (B.expanded.edge d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1) := by
  apply six_cases
  intro i
  simp [expanded, newEdge, d6]
  simp [dart, Nat.add_mod, Nat.mul_mod]

theorem expanded_edge_count_ge : 3 * E ≤ cycleCount B.expanded.edge := by
  have helper : ∀ {n e : Nat} (hn : n = 2 * e) (p : Fin n → Fin n),
      (∀ d, (p d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1)) →
      e ≤ cycleCount p := by
    intro n e hn p hp
    subst n
    exact cycleCount_graphEdge_ge hp
  exact helper (by omega) B.expanded.edge B.expanded_edge_pairing

end BipartiteRotation
end STACS2027.PlanarSource.Embedding
