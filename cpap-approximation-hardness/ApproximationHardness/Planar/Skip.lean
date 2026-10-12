module

public import NPHardness.PlanarAssemblyLocalOrder
public import NPHardness.PlanarAssemblySourceNode
import Lean.Elab.Tactic.Omega

/-!
# First-hit walks along a fixed cyclic port profile

A gadget embedding with a prescribed boundary profile gives, for every port `i`, a first-hit
walk on the outer face from port `i` to port `next i`. When only some of the ports are used by
the source rotation, the walk between two consecutive used ports is a concatenation of such
walks (`NextSelected.chain`, `NextSelected.skip`). For a cyclic profile on two or three ports
this is enough to realize the source order of every node with at most two used ports, and the
three-port case is decided by one comparison (`cyclic_skip`, `three_cycle_sign`).
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing

/-- Concatenated first-hit walks: `s + 1` profile steps from `a` are one face walk, whose
intermediate selected darts are exactly the intermediate profile steps. -/
theorem NextSelected.chain {n m : Nat} {p : Fin n → Fin n} {port : Fin m → Fin n}
    {next : Fin m → Fin m} (hnext : ∀ i, NextSelected p port i (next i))
    (hinj : ∀ i j, port i = port j → i = j) :
    ∀ s a, ∃ K, 0 < K ∧ iterate p K (port a) = port (iterate next (s + 1) a) ∧
      ∀ r, 0 < r → r < K → ∀ t, iterate p r (port a) = port t →
        ∃ s', 0 < s' ∧ s' ≤ s ∧ t = iterate next s' a := by
  intro s
  induction s with
  | zero =>
    intro a
    obtain ⟨K, hK, he, hn⟩ := hnext a
    exact ⟨K, hK, he, fun r hr hrK t ht => absurd ht (hn r hr hrK t)⟩
  | succ s ih =>
    intro a
    obtain ⟨K1, hK1, he1, hn1⟩ := hnext a
    obtain ⟨K2, hK2, he2, hn2⟩ := ih (next a)
    refine ⟨K1 + K2, by omega, ?_, ?_⟩
    · rw [iterate_add, he1, he2]
      rfl
    · intro r hr hrK t ht
      by_cases h1 : r < K1
      · exact absurd ht (hn1 r hr h1 t)
      · by_cases h2 : r = K1
        · subst h2
          rw [he1] at ht
          exact ⟨1, by omega, by omega, hinj _ _ ht.symm⟩
        · have hr' : r = K1 + (r - K1) := by omega
          rw [hr', iterate_add, he1] at ht
          obtain ⟨s', hs', hs's, hts⟩ := hn2 (r - K1) (by omega) (by omega) t ht
          exact ⟨s' + 1, by omega, by omega, hts⟩

/-- Restrict a profile to the used ports: the next used port after `use i` is reached after
`s + 1` profile steps without meeting another used port. -/
theorem NextSelected.skip {n m r : Nat} {p : Fin n → Fin n} {port : Fin m → Fin n}
    {next : Fin m → Fin m} (hnext : ∀ i, NextSelected p port i (next i))
    (hinj : ∀ i j, port i = port j → i = j)
    (use : Fin r → Fin m) (i j : Fin r) (s : Nat)
    (he : iterate next (s + 1) (use i) = use j)
    (hskip : ∀ s', 0 < s' → s' ≤ s → ∀ t, iterate next s' (use i) ≠ use t) :
    NextSelected p (fun t => port (use t)) i j := by
  obtain ⟨K, hK, hKe, hn⟩ := NextSelected.chain hnext hinj s (use i)
  refine ⟨K, hK, ?_, ?_⟩
  · dsimp only
    rw [hKe, he]
  · intro r' hr hrK t ht
    obtain ⟨s', hs', hs's, hts⟩ := hn r' hr hrK (use t) ht
    exact hskip s' hs' hs's t hts.symm

/-- The arithmetic of a cyclic shift on two or three ports. -/
theorem cyclic_values {m : Nat} (hm2 : 2 ≤ m) (hm3 : m ≤ 3) (fw : Bool)
    (next : Fin m → Fin m)
    (hnext : ∀ a, (next a).val = if fw then (a.val + 1) % m else (a.val + m - 1) % m)
    (x : Fin m) :
    (next x).val ≠ x.val ∧
    (m = 2 → (next (next x)).val = x.val) ∧
    (m = 3 → (next (next x)).val ≠ x.val ∧ (next (next x)).val ≠ (next x).val ∧
      (next (next (next x))).val = x.val) := by
  have hx := x.isLt
  have h1 := hnext x
  have h2 := hnext (next x)
  have h3 := hnext (next (next x))
  rcases (show m = 2 ∨ m = 3 by omega) with h | h <;> subst h <;> cases fw <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2 h3 <;> omega

/-- The source order of a node with at most three used ports, realized by a cyclic profile.
A fixed point of the order means that only one port is used; with all three ports used, the
profile is assumed to match the order exactly. -/
theorem cyclic_skip {m r : Nat} (hm2 : 2 ≤ m) (hm3 : m ≤ 3) (fw : Bool)
    (next : Fin m → Fin m)
    (hnext : ∀ a, (next a).val = if fw then (a.val + 1) % m else (a.val + m - 1) % m)
    (use : Fin r → Fin m) (huse : ∀ a b, use a = use b → a = b)
    (q : Fin r → Fin r)
    (hfix : ∀ i, q i = i → ∀ t, t = i)
    (hfull : m = 3 → (∀ c : Fin m, ∃ t, use t = c) → ∀ i, use (q i) = next (use i))
    (i : Fin r) :
    ∃ s, iterate next (s + 1) (use i) = use (q i) ∧
      ∀ s', 0 < s' → s' ≤ s → ∀ t, iterate next s' (use i) ≠ use t := by
  have hv := cyclic_values hm2 hm3 fw next hnext
  have it1 : ∀ x, iterate next 1 x = next x := fun _ => rfl
  have it2 : ∀ x, iterate next 2 x = next (next x) := fun _ => rfl
  have it3 : ∀ x, iterate next 3 x = next (next (next x)) := fun _ => rfl
  by_cases hq : q i = i
  · rw [hq]
    have hall := hfix i hq
    obtain ⟨n1, n2, n3⟩ := hv (use i)
    rcases (show m = 2 ∨ m = 3 by omega) with h | h
    · refine ⟨1, ?_, ?_⟩
      · rw [it2]; exact Fin.ext (n2 h)
      · intro s' hs' hs's t ht
        rw [hall t, show s' = 1 by omega, it1] at ht
        exact n1 (congrArg Fin.val ht)
    · obtain ⟨m1, m2, m3⟩ := n3 h
      refine ⟨2, ?_, ?_⟩
      · rw [it3]; exact Fin.ext m3
      · intro s' hs' hs's t ht
        rw [hall t] at ht
        rcases (show s' = 1 ∨ s' = 2 by omega) with e | e <;> subst e
        · rw [it1] at ht; exact n1 (congrArg Fin.val ht)
        · rw [it2] at ht; exact m1 (congrArg Fin.val ht)
  · have hne : use (q i) ≠ use i := fun h => hq (huse _ _ h)
    by_cases h1 : use (q i) = next (use i)
    · exact ⟨0, by rw [it1, h1], fun s' hs' hs's => absurd hs's (by omega)⟩
    · obtain ⟨n1, n2, n3⟩ := hv (use i)
      have hq3 := (use (q i)).isLt
      have hu3 := (use i).isLt
      have hn3 := (next (use i)).isLt
      have hm : m = 3 := by
        rcases (show m = 2 ∨ m = 3 by omega) with hm2' | hm2'
        · have a1 : (use (q i)).val ≠ (use i).val := fun h => hne (Fin.ext h)
          have a2 : (use (q i)).val ≠ (next (use i)).val := fun h => h1 (Fin.ext h)
          subst hm2'
          omega
        · exact hm2'
      obtain ⟨m1, m2, m3⟩ := n3 hm
      have hnn := (next (next (use i))).isLt
      have hqv : (use (q i)).val = (next (next (use i))).val := by
        have a1 : (use (q i)).val ≠ (use i).val := fun h => hne (Fin.ext h)
        have a2 : (use (q i)).val ≠ (next (use i)).val := fun h => h1 (Fin.ext h)
        subst hm
        omega
      refine ⟨1, by rw [it2]; exact (Fin.ext hqv).symm, ?_⟩
      intro s' hs' hs's t ht
      rw [show s' = 1 by omega, it1] at ht
      apply h1
      apply hfull hm
      intro c
      have hc := c.isLt
      by_cases e1 : c.val = (use i).val
      · exact ⟨i, Fin.ext e1.symm⟩
      · by_cases e2 : c.val = (next (use i)).val
        · exact ⟨t, by rw [← ht]; exact Fin.ext e2.symm⟩
        · refine ⟨q i, Fin.ext ?_⟩
          rw [hqv]
          subst hm
          omega

/-- With all three ports used, one comparison decides the direction of a three-port source
order: the predecessor of the dart `t` is the port-0 dart `t0`, and `t` has port 2 exactly in
the forward case. -/
theorem three_cycle_sign {m r : Nat} (hm : m = 3) (use : Fin r → Fin m)
    (huse : ∀ a b, use a = use b → a = b)
    (q : Fin r → Fin r) (hq : ∀ a b, q a = q b → a = b)
    (hfix : ∀ i, q i = i → ∀ t, t = i)
    (hfull : ∀ c : Fin m, ∃ t, use t = c)
    (fw : Bool) (t t0 : Fin r) (ht0 : (use t0).val = 0) (hqt : q t = t0)
    (hsign : (use t).val = 2 ↔ fw = true) (i : Fin r) :
    (use (q i)).val = if fw then ((use i).val + 1) % 3 else ((use i).val + 2) % 3 := by
  subst hm
  obtain ⟨u0, h0⟩ := hfull 0
  obtain ⟨u1, h1⟩ := hfull 1
  obtain ⟨u2, h2⟩ := hfull 2
  have hidx : ∀ x : Fin r, x = u0 ∨ x = u1 ∨ x = u2 := by
    intro x
    have hx := (use x).isLt
    rcases (show (use x).val = 0 ∨ (use x).val = 1 ∨ (use x).val = 2 by omega) with e | e | e
    · exact Or.inl (huse _ _ (Fin.ext (by rw [e, h0]; rfl)))
    · exact Or.inr (Or.inl (huse _ _ (Fin.ext (by rw [e, h1]; rfl))))
    · exact Or.inr (Or.inr (huse _ _ (Fin.ext (by rw [e, h2]; rfl))))
  have v0 : (use u0).val = 0 := by rw [h0]; rfl
  have v1 : (use u1).val = 1 := by rw [h1]; rfl
  have v2 : (use u2).val = 2 := by rw [h2]; rfl
  -- no fixed points
  have nofix : ∀ x : Fin r, (use (q x)).val ≠ (use x).val := by
    intro x hx
    have hqx : q x = x := huse _ _ (Fin.ext hx)
    have e01 : u0 = u1 := (hfix x hqx u0).trans (hfix x hqx u1).symm
    rw [e01] at v0
    omega
  have dist : ∀ x y : Fin r, (use (q x)).val = (use (q y)).val → x = y :=
    fun x y h => hq _ _ (huse _ _ (Fin.ext h))
  have a0 := (use (q u0)).isLt
  have a1 := (use (q u1)).isLt
  have a2 := (use (q u2)).isLt
  have f0 := nofix u0
  have f1 := nofix u1
  have f2 := nofix u2
  have d01 : (use (q u0)).val ≠ (use (q u1)).val := fun h => by
    have := congrArg (fun x => (use x).val) (dist _ _ h); simp only [v0, v1] at this; omega
  have d02 : (use (q u0)).val ≠ (use (q u2)).val := fun h => by
    have := congrArg (fun x => (use x).val) (dist _ _ h); simp only [v0, v2] at this; omega
  have d12 : (use (q u1)).val ≠ (use (q u2)).val := fun h => by
    have := congrArg (fun x => (use x).val) (dist _ _ h); simp only [v1, v2] at this; omega
  have ht0' : t0 = u0 := huse _ _ (Fin.ext (by rw [h0]; exact ht0))
  -- the comparison
  have key : (if fw then (use (q u2)).val = 0 else (use (q u1)).val = 0) := by
    cases fw
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have ht2 : (use t).val ≠ 2 := fun h => by simpa using hsign.mp h
      rcases hidx t with e | e | e
      · subst e
        rw [hqt] at f0
        exact absurd (by rw [ht0', v0]) f0
      · subst e; rw [hqt, ht0']; exact v0
      · subst e; exact absurd v2 ht2
    · simp only [↓reduceIte]
      have ht2 : (use t).val = 2 := hsign.mpr rfl
      rcases hidx t with e | e | e
      · subst e; rw [v0] at ht2; exact absurd ht2 (by decide)
      · subst e; rw [v1] at ht2; exact absurd ht2 (by decide)
      · subst e; rw [hqt, ht0']; exact v0
  rcases hidx i with e | e | e <;> subst e <;> cases fw <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at key ⊢ <;> omega

namespace NodeDartIndex

theorem iterate_fixed {n : Nat} (p : Fin n → Fin n) (x : Fin n) (h : p x = x) :
    ∀ k, iterate p k x = x := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterate, h, ih]

/-- A fixed point of the local source order means that the node has a single dart. -/
theorem order_fixed {n m : Nat} {V : Type} {label : Fin n → V} {v : V}
    (D : NodeDartIndex label v m) (I : Hypermap n)
    (hnode : ∀ a b, Reaches I.node a b ↔ label a = label b)
    (i : Fin m) (h : D.order I hnode i = i) : ∀ t, t = i := by
  intro t
  have hp := D.order_spec I hnode i
  rw [h] at hp
  have hn : I.node (D.dart i) = D.dart i := by
    have := I.edgeK (D.dart i)
    rw [← hp] at this
    exact this
  obtain ⟨k, hk⟩ := (hnode (D.dart i) (D.dart t)).mpr ((D.vertex i).trans (D.vertex t).symm)
  rw [iterate_fixed I.node _ hn k] at hk
  exact D.injective _ _ hk.symm

/-- The predecessor of a node step is the original dart. -/
theorem face_edge_node {n : Nat} (I : Hypermap n) (d : Fin n) : I.face (I.edge (I.node d)) = d :=
  hm_node_inj I _ _ (I.edgeK (I.node d))

/-- The local order sends the index of `I.node d` back to the index of `d`. -/
theorem order_of_node {n m : Nat} {V : Type} {label : Fin n → V} {v : V}
    (D : NodeDartIndex label v m) (I : Hypermap n)
    (hnode : ∀ a b, Reaches I.node a b ↔ label a = label b)
    (i t : Fin m) (h : D.dart t = I.node (D.dart i)) : D.order I hnode t = i := by
  apply D.injective
  rw [D.order_spec, h, face_edge_node]

/-- The node step stays at the same vertex. -/
theorem node_vertex {n : Nat} {V : Type} {label : Fin n → V} (I : Hypermap n)
    (hnode : ∀ a b, Reaches I.node a b ↔ label a = label b) (d : Fin n) :
    label (I.node d) = label d :=
  ((hnode d (I.node d)).mp ⟨1, rfl⟩).symm

end NodeDartIndex
end STACS2027.PlanarAssembly
