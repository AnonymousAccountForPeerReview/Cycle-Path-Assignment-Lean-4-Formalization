module

public import NPHardness.PlanarSphericalGadgets

/-!
Mirror an actual graph embedding without changing its edge list. Node cycles
run backwards; the reflected outer-face dart of d is its edge partner.
Euler counts and connected components are preserved, including the strict
spherical inequality used when assembling disjoint gadgets.
-/

@[expose] public section
namespace STACS2027.PlanarGluing.Reflection
open Complexity Complexity.Planar

variable {n : Nat}

theorem inverse_iterate (p q : Fin n → Fin n) (hpq : ∀ x, q (p x) = x)
    (k : Nat) (x : Fin n) : iterate q k (iterate p k x) = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ' p,iterate,hpq]; exact ih

theorem inverse_reaches (p q : Fin n → Fin n)
    (hp : ∀ a b, p a = p b → a = b) (hq : ∀ a b, q a = q b → a = b)
    (hpq : ∀ x, q (p x) = x) (hqp : ∀ x, p (q x) = x) (x y : Fin n) :
    Reaches p x y ↔ Reaches q x y := by
  constructor
  · rintro ⟨k,rfl⟩
    exact (show Reaches q (iterate p k x) x from ⟨k,inverse_iterate p q hpq k x⟩).symm hq
  · rintro ⟨k,rfl⟩
    exact (show Reaches p (iterate q k x) x from ⟨k,inverse_iterate q p hqp k x⟩).symm hp

theorem cycles_of_same_orbits (p q : Fin n → Fin n)
    (hp : ∀ a b, p a = p b → a = b) (hq : ∀ a b, q a = q b → a = b)
    (h : ∀ x y, Reaches p x y ↔ Reaches q x y) : cycleCount p = cycleCount q := by
  have hc : ∀ x, cmin p x = cmin q x := by
    intro x
    obtain ⟨a,ha⟩ := (h x (cmin p x)).mp (reaches_cmin p x)
    obtain ⟨b,hb⟩ := (h x (cmin q x)).mpr (reaches_cmin q x)
    have h1 := cmin_le hq x a
    have h2 := cmin_le hp x b
    rw [ha] at h1
    rw [hb] at h2
    exact Fin.ext (by omega)
  rw [cycleCount_eq,cycleCount_eq]
  congr 1
  funext x
  apply Bool.eq_iff_iff.mpr
  rw [← cmin_eq_iff hp,← cmin_eq_iff hq,hc]

def mirror (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d) : Hypermap n where
  edge := G.edge
  node d := G.face (G.edge d)
  face d := G.node (G.edge d)
  edgeK d := by
    rw [he]
    exact nodePredecessor_node G d

theorem mirror_node_inverse (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d) (d : Fin n) :
    (mirror G he).node (G.node d) = d := nodePredecessor_node G d

theorem node_mirror_inverse (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d) (d : Fin n) :
    G.node ((mirror G he).node d) = d := G.edgeK d

theorem mirror_node_orbits (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d) (x y : Fin n) :
    Reaches (mirror G he).node x y ↔ Reaches G.node x y :=
  (inverse_reaches G.node (mirror G he).node (hm_node_inj G) (hm_node_inj (mirror G he))
    (mirror_node_inverse G he) (node_mirror_inverse G he) x y).symm

theorem mirror_face_edge_step (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d) (d : Fin n) :
    (mirror G he).face (G.edge (G.face d)) = G.edge d := by
  change G.node (G.edge (G.edge (G.face d))) = G.edge d
  rw [he]
  simpa only [he] using G.edgeK (G.edge d)

/-- Exact reverse traversal, with no unbounded search for a return time. -/
theorem mirror_face_reverse (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d)
    (k : Nat) (d : Fin n) :
    iterate (mirror G he).face k (G.edge (iterate G.face k d)) = G.edge d := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ' G.face,iterate,mirror_face_edge_step]
    exact ih

def edgeEquiv (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d) : DartEquiv n n :=
  ⟨G.edge,G.edge,he,he⟩

def faceInv (G : Hypermap n) (d : Fin n) : Fin n := G.edge (G.node d)

theorem face_faceInv (G : Hypermap n) (d : Fin n) : G.face (faceInv G d) = d :=
  hm_node_inj G _ _ (G.edgeK (G.node d))

theorem faceInv_face (G : Hypermap n) (d : Fin n) : faceInv G (G.face d) = d :=
  hm_face_inj G _ _ (face_faceInv G (G.face d))

theorem faceInv_injective (G : Hypermap n) (a b : Fin n) (h : faceInv G a = faceInv G b) : a = b := by
  have hh := congrArg G.face h
  simpa only [face_faceInv] using hh

theorem mirror_cycles_node (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d) :
    cycleCount (mirror G he).node = cycleCount G.node :=
  cycles_of_same_orbits _ _ (hm_node_inj _) (hm_node_inj _) (mirror_node_orbits G he)

theorem mirror_cycles_face (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d) :
    cycleCount (mirror G he).face = cycleCount G.face := by
  have hconj : (mirror G he).face = (edgeEquiv G he).conjugate (faceInv G) := by
    funext d
    change G.node (G.edge d) = G.edge (G.edge (G.node (G.edge d)))
    rw [he]
  rw [hconj,(edgeEquiv G he).cycles_eq (faceInv_injective G)]
  apply cycles_of_same_orbits _ _ (faceInv_injective G) (hm_face_inj G)
  intro x y
  exact inverse_reaches _ _ (faceInv_injective G) (hm_face_inj G)
    (face_faceInv G) (faceInv_face G) x y

theorem path_simulation (G H : Hypermap n)
    (hs : ∀ x y, Linked.Step G x y → LinkedPath H x y)
    {x y : Fin n} (h : LinkedPath G x y) : LinkedPath H x y := by
  obtain ⟨k,hk⟩ := h
  induction k generalizing y with
  | zero => rw [Linked.linked_zero] at hk; subst y; exact LinkedPath.refl H x
  | succ k ih =>
    rcases (Linked.linked_succ G k x y).mp hk with h | ⟨z,hz,hzy⟩
    · exact ih h
    · exact (ih hz).trans (hs z y hzy)

theorem mirror_path (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d) (x y : Fin n) :
    LinkedPath (mirror G he) x y ↔ LinkedPath G x y := by
  constructor
  · apply path_simulation
    intro a b h
    rcases h with h | h | h
    · exact LinkedPath.step G (Or.inl h)
    · have hh := (LinkedPath.step G (x := a) (Or.inl rfl)).trans
        (LinkedPath.step G (x := G.edge a) (Or.inr (Or.inr rfl)))
      change G.face (G.edge a) = b at h
      rw [h] at hh
      exact hh
    · have hh := (LinkedPath.step G (x := a) (Or.inl rfl)).trans
        (LinkedPath.step G (x := G.edge a) (Or.inr (Or.inl rfl)))
      change G.node (G.edge a) = b at h
      rw [h] at hh
      exact hh
  · apply path_simulation
    intro a b h
    rcases h with h | h | h
    · exact LinkedPath.step (mirror G he) (Or.inl h)
    · have hh := (LinkedPath.step (mirror G he) (x := a) (Or.inl rfl)).trans
        (LinkedPath.step (mirror G he) (x := G.edge a) (Or.inr (Or.inr rfl)))
      change LinkedPath (mirror G he) a (G.node (G.edge (G.edge a))) at hh
      rw [he,h] at hh
      exact hh
    · have hh := (LinkedPath.step (mirror G he) (x := a) (Or.inl rfl)).trans
        (LinkedPath.step (mirror G he) (x := G.edge a) (Or.inr (Or.inl rfl)))
      change LinkedPath (mirror G he) a (G.face (G.edge (G.edge a))) at hh
      rw [he,h] at hh
      exact hh

theorem mirror_linked (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d) (x y : Fin n) :
    (mirror G he).linked n x y = G.linked n x y := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    obtain ⟨k,hk⟩ := (mirror_path G he x y).mp ⟨n,h⟩
    exact Linked.linked_stable G hk
  · intro h
    obtain ⟨k,hk⟩ := (mirror_path G he x y).mpr ⟨n,h⟩
    exact Linked.linked_stable (mirror G he) hk

theorem mirror_components (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d) :
    (mirror G he).componentCount = G.componentCount := by
  simp only [Hypermap.componentCount,mirror_linked]

theorem mirror_euler (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d) :
    (mirror G he).eulerRhs = G.eulerRhs := by
  simp only [Hypermap.eulerRhs,mirror_cycles_node,mirror_cycles_face]
  rfl

theorem mirror_planar (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d) (hp : G.Planar) :
    (mirror G he).Planar := by
  rw [planar_iff,mirror_components,mirror_euler]
  exact (planar_iff G).mp hp

theorem mirror_spherical (G : Hypermap n) (he : ∀ d, G.edge (G.edge d) = d)
    (hs : 2*G.componentCount+n ≤ G.eulerRhs) :
    2*(mirror G he).componentCount+n ≤ (mirror G he).eulerRhs := by
  simpa only [mirror_components,mirror_euler] using hs

theorem mirror_embedding {V : Type} {es : List (V×V)} {G : Hypermap (2*es.length)}
    (h : IsGraphEmbedding es G) (he : ∀ d, G.edge (G.edge d) = d) :
    IsGraphEmbedding es (mirror G he) := by
  refine ⟨h.1,?_,mirror_planar G he h.2.2⟩
  intro x y
  exact (mirror_node_orbits G he x y).trans (h.2.1 x y)

theorem embedding_edge_twice {V : Type} {es : List (V×V)} {G : Hypermap (2*es.length)}
    (h : IsGraphEmbedding es G) (d : Fin (2*es.length)) : G.edge (G.edge d) = d := by
  have hE : ∀ d, G.edge d = graphEdge d := fun d => Fin.ext (h.1 d)
  rw [hE,hE,graphEdge_twice]

end STACS2027.PlanarGluing.Reflection
