module

public import NPHardness.PlanarGluingCycles
public import Complexity.Planar.EmbedComplete
import Lean.Elab.Tactic.Omega

/-!
Dart relabelling for the registered hypermap notion of planarity.
The constructions preserve actual node orbits and all Euler counts.
-/

@[expose] public section
namespace STACS2027.PlanarGluing
open Complexity Complexity.Planar

structure DartEquiv (n m : Nat) where
  toFun : Fin n → Fin m
  invFun : Fin m → Fin n
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

namespace DartEquiv
variable {n m l : Nat}

def refl (n : Nat) : DartEquiv n n := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
def symm (e : DartEquiv n m) : DartEquiv m n :=
  ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩
def trans (e : DartEquiv n m) (f : DartEquiv m l) : DartEquiv n l where
  toFun x := f.toFun (e.toFun x)
  invFun y := e.invFun (f.invFun y)
  left_inv x := by rw [f.left_inv, e.left_inv]
  right_inv y := by rw [e.right_inv, f.right_inv]

theorem injective (e : DartEquiv n m) {x y : Fin n} (h : e.toFun x = e.toFun y) : x = y := by
  have := congrArg e.invFun h
  simpa only [e.left_inv] using this

theorem card_le (e : DartEquiv n m) : n ≤ m := by
  have hnd := nodup_map_of_injOn' e.toFun (List.nodup_finRange n)
    (fun _ _ _ _ h => e.injective h)
  have h := List.Nodup.length_le_of_subset hnd (l₂ := List.finRange m)
    (fun x _ => List.mem_finRange x)
  simpa using h

theorem card_eq (e : DartEquiv n m) : n = m :=
  Nat.le_antisymm e.card_le e.symm.card_le

def conjugate (e : DartEquiv n m) (p : Fin n → Fin n) : Fin m → Fin m :=
  fun y => e.toFun (p (e.invFun y))

@[simp] theorem conjugate_toFun (e : DartEquiv n m) (p : Fin n → Fin n) (x : Fin n) :
    e.conjugate p (e.toFun x) = e.toFun (p x) := by simp [conjugate, e.left_inv]

@[simp] theorem inv_conjugate (e : DartEquiv n m) (p : Fin n → Fin n) (y : Fin m) :
    e.invFun (e.conjugate p y) = p (e.invFun y) := by simp [conjugate, e.left_inv]

theorem iterate_conjugate (e : DartEquiv n m) (p : Fin n → Fin n) (k : Nat) (y : Fin m) :
    iterate (e.conjugate p) k y = e.toFun (iterate p k (e.invFun y)) := by
  induction k generalizing y with
  | zero => exact (e.right_inv y).symm
  | succ k ih => simpa only [iterate, inv_conjugate] using ih (e.conjugate p y)

theorem conjugate_injective (e : DartEquiv n m) {p : Fin n → Fin n}
    (hp : ∀ a b, p a = p b → a = b) :
    ∀ a b, e.conjugate p a = e.conjugate p b → a = b := by
  intro a b h
  have he := hp _ _ (e.injective h)
  have := congrArg e.toFun he
  simpa only [e.right_inv] using this

theorem cycles_le (e : DartEquiv n m) {p : Fin n → Fin n}
    (hp : ∀ a b, p a = p b → a = b) : cycleCount p ≤ cycleCount (e.conjugate p) := by
  let φ : Fin m → Fin n := fun y => cmin p (e.invFun y)
  have hφ : ∀ y, φ (e.conjugate p y) = φ y := by
    intro y; simp only [φ, inv_conjugate, cmin_step hp]
  have hnd : (((cycleRoots p).map e.toFun).map φ).Nodup := by
    have he : ((cycleRoots p).map e.toFun).map φ = cycleRoots p := by
      rw [List.map_map]
      conv => rhs; rw [← List.map_id (cycleRoots p)]
      apply List.map_congr_left
      intro x hx
      simp only [Function.comp_apply, φ, e.left_inv, id]
      exact (mem_cycleRoots hp x).mp hx
    rw [he]; exact cycleRoots_nodup p
  have := cycleCount_ge (e.conjugate p) φ hφ ((cycleRoots p).map e.toFun) hnd
  simpa only [List.length_map, cycleRoots_length] using this

theorem cycles_eq (e : DartEquiv n m) {p : Fin n → Fin n}
    (hp : ∀ a b, p a = p b → a = b) : cycleCount (e.conjugate p) = cycleCount p := by
  have h := e.symm.cycles_le (e.conjugate_injective hp)
  have he : e.symm.conjugate (e.conjugate p) = p := by
    funext x; simp [conjugate, symm, e.left_inv]
  rw [he] at h
  exact Nat.le_antisymm h (e.cycles_le hp)

def hypermap (e : DartEquiv n m) (G : Hypermap n) : Hypermap m where
  edge := e.conjugate G.edge
  node := e.conjugate G.node
  face := e.conjugate G.face
  edgeK y := by simp [conjugate, e.left_inv, G.edgeK, e.right_inv]

theorem linked_map (e : DartEquiv n m) (G : Hypermap n) (k : Nat) (x y : Fin n)
    (h : G.linked k x y = true) :
    (e.hypermap G).linked k (e.toFun x) (e.toFun y) = true := by
  induction k generalizing y with
  | zero =>
    rw [Linked.linked_zero] at h ⊢
    exact congrArg e.toFun h
  | succ k ih =>
    rw [Linked.linked_succ] at h ⊢
    rcases h with h | ⟨z, hz, hs⟩
    · exact Or.inl (ih y h)
    · refine Or.inr ⟨e.toFun z, ih z hz, ?_⟩
      rcases hs with hs | hs | hs
      · exact Or.inl (by simpa only [hypermap, conjugate_toFun] using congrArg e.toFun hs)
      · exact Or.inr (Or.inl (by simpa only [hypermap, conjugate_toFun] using congrArg e.toFun hs))
      · exact Or.inr (Or.inr (by simpa only [hypermap, conjugate_toFun] using congrArg e.toFun hs))

end DartEquiv

def ComponentRoot {n : Nat} (G : Hypermap n) (x : Fin n) : Bool :=
  (List.finRange n).all fun y => !G.linked n x y || Nat.ble x.val y.val

theorem componentRoot_iff {n : Nat} (G : Hypermap n) (x : Fin n) :
    ComponentRoot G x = true ↔ compMin G x = x.val := by
  simp only [ComponentRoot, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq]
  constructor
  · intro h
    obtain ⟨⟨y, hy, hl⟩, hm⟩ := compMin_spec G x
    have hxy : x.val ≤ y.val := by simpa [hl] using h y
    have hmin := hm x (Linked.linked_refl G n x)
    omega
  · intro h y
    by_cases hl : G.linked n x y = true
    · right; rw [← h]; exact (compMin_spec G x).2 y hl
    · left; exact Bool.eq_false_iff.mpr hl

theorem componentRoot_le {n : Nat} (G : Hypermap n) {x y : Fin n}
    (hx : ComponentRoot G x = true) {k : Nat} (h : G.linked k x y = true) : x.val ≤ y.val := by
  have hx' := (componentRoot_iff G x).mp hx
  rw [← hx']
  exact (compMin_spec G x).2 y (Linked.linked_stable G h)

theorem componentRoot_eq {n : Nat} (G : Hypermap n) {x y : Fin n}
    (hx : ComponentRoot G x = true) (hy : ComponentRoot G y = true)
    {k : Nat} (h : G.linked k x y = true) : x = y := by
  obtain ⟨r, hr⟩ := hm_linked_symm G h
  exact Fin.ext (Nat.le_antisymm (componentRoot_le G hx h) (componentRoot_le G hy hr))

theorem compMin_linked {n : Nat} (G : Hypermap n) {x y : Fin n} {k : Nat}
    (h : G.linked k x y = true) : compMin G y = compMin G x := by
  induction k generalizing y with
  | zero => rw [Linked.linked_zero] at h; subst y; rfl
  | succ k ih =>
    rcases (Linked.linked_succ G k x y).mp h with h | ⟨z, hz, hs⟩
    · exact ih h
    · exact (compMin_step G hs).trans (ih hz)

noncomputable def componentRep {n : Nat} (G : Hypermap n) (x : Fin n) : Fin n :=
  ⟨compMin G x, compMin_lt G x⟩

theorem componentRep_linked {n : Nat} (G : Hypermap n) (x : Fin n) :
    G.linked n x (componentRep G x) = true := by
  obtain ⟨y, hy, hl⟩ := (compMin_spec G x).1
  have he : y = componentRep G x := Fin.ext hy
  simpa [he] using hl

theorem componentRep_root {n : Nat} (G : Hypermap n) (x : Fin n) :
    ComponentRoot G (componentRep G x) = true := by
  rw [componentRoot_iff]
  exact compMin_linked G (componentRep_linked G x)

theorem linked_of_componentRep_eq {n : Nat} (G : Hypermap n) {x y : Fin n}
    (h : componentRep G x = componentRep G y) : ∃ k, G.linked k x y = true := by
  obtain ⟨r, hr⟩ := hm_linked_symm G (componentRep_linked G y)
  have hx := componentRep_linked G x
  rw [h] at hx
  exact ⟨n + r, Linked.linked_trans G hx hr⟩

namespace DartEquiv
variable {n m : Nat}

theorem components_le (e : DartEquiv n m) (G : Hypermap n) :
    (e.hypermap G).componentCount ≤ G.componentCount := by
  let xs := (List.finRange m).filter (ComponentRoot (e.hypermap G))
  let f : Fin m → Fin n := fun x => componentRep G (e.invFun x)
  have hnd : (xs.map f).Nodup := by
    apply nodup_map_of_injOn' f (List.Pairwise.filter _ (List.nodup_finRange m))
    intro x hx y hy h
    have hx' : ComponentRoot (e.hypermap G) x = true := (List.mem_filter.mp hx).2
    have hy' : ComponentRoot (e.hypermap G) y = true := (List.mem_filter.mp hy).2
    obtain ⟨k, hk⟩ := linked_of_componentRep_eq G h
    have ht := e.linked_map G k _ _ hk
    rw [e.right_inv, e.right_inv] at ht
    exact componentRoot_eq _ hx' hy' ht
  have h := length_le_countP (ComponentRoot G) (xs.map f) hnd (by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact componentRep_root G (e.invFun y))
  change (List.finRange m).countP (ComponentRoot (e.hypermap G)) ≤
    (List.finRange n).countP (ComponentRoot G)
  simpa only [List.length_map, xs, ← List.countP_eq_length_filter] using h

theorem planar (e : DartEquiv n m) (G : Hypermap n) (h : G.Planar) :
    (e.hypermap G).Planar := by
  rw [planar_iff] at h ⊢
  have hc := e.components_le G
  have he := e.cycles_eq (hm_edge_inj G)
  have hn := e.cycles_eq (hm_node_inj G)
  have hf := e.cycles_eq (hm_face_inj G)
  have hm := e.card_eq
  unfold Hypermap.eulerRhs at h ⊢
  change 2 * (e.hypermap G).componentCount + m ≤
    cycleCount (e.conjugate G.edge) + cycleCount (e.conjugate G.node) +
      cycleCount (e.conjugate G.face) + 1
  omega

end DartEquiv

/-- The canonical partner of a dart in an edge-list graph. -/
def graphEdge {E : Nat} (d : Fin (2 * E)) : Fin (2 * E) :=
  ⟨ed d.val, by
    have := d.isLt
    rcases Nat.mod_two_eq_zero_or_one d.val with h | h <;> simp [ed, h] <;> omega⟩

/-- Actual dart isomorphism: the edge pairing and vertex ends are preserved. -/
structure GraphDartEquiv {V : Type} (es ts : List (V × V)) where
  darts : DartEquiv (2 * es.length) (2 * ts.length)
  edge : ∀ d, darts.toFun (graphEdge d) = graphEdge (darts.toFun d)
  ends : ∀ d, halfEdgeEnd ts (darts.toFun d).val = halfEdgeEnd es d.val

theorem GraphDartEquiv.planar {V : Type} {es ts : List (V × V)}
    (e : GraphDartEquiv es ts) (h : PlanarGraph es) : PlanarGraph ts := by
  obtain ⟨G, hE, hN, hP⟩ := h
  have he : ∀ d, G.edge d = graphEdge d := fun d => Fin.ext (hE d)
  refine ⟨e.darts.hypermap G, ?_, ?_, e.darts.planar G hP⟩
  · intro y
    change (e.darts.toFun (G.edge (e.darts.invFun y))).val = _
    rw [he, e.edge, e.darts.right_inv]
    rfl
  · intro y y'
    have hn : (∃ k, iterate (e.darts.conjugate G.node) k y = y') ↔
        ∃ k, iterate G.node k (e.darts.invFun y) = e.darts.invFun y' := by
      constructor
      · rintro ⟨k, hk⟩
        rw [e.darts.iterate_conjugate] at hk
        exact ⟨k, by have := congrArg e.darts.invFun hk; simpa only [e.darts.left_inv] using this⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, by rw [e.darts.iterate_conjugate, hk, e.darts.right_inv]⟩
    change (∃ k, iterate (e.darts.conjugate G.node) k y = y') ↔ _
    rw [hn, hN]
    have hy := e.ends (e.darts.invFun y)
    have hy' := e.ends (e.darts.invFun y')
    rw [e.darts.right_inv] at hy hy'
    rw [← hy, ← hy']

end STACS2027.PlanarGluing
