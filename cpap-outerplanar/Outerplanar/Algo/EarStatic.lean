module

public import Outerplanar.Algo.EarInv
import Outerplanar.Algo.EarCorrect
import Mathlib.Tactic

/-!
# Ear elimination: the adjacency queries are static

The elimination of `Outerplanar/Algo/Ear.lean` asks one adjacency question per eliminated vertex
`v`: is `u w` an edge of the current graph, `u`, `w` the two alive neighbours of `v`? The
current graph contains the *virtual* edges added by earlier eliminations. Here: **while more
than three vertices are alive, the answer is the adjacency in the original graph `L`**
(`query_static`), provided `L` has an outerplanar Hamiltonian cycle through all its vertices.
So the machine can answer the query from `L` alone (`RAM/EarProg.lean`: through the
orientation of `L` computed by the peeling of `Outerplanar/Algo/EarPeel.lean`), and needs no
adjacency matrix.

The argument runs along the ghost Hamiltonian cycle `H` of the invariant `Inv`
(`Outerplanar/Algo/EarInv.lean`):

* `Consec K a b`: `a` and `b` are consecutive on the cycle `K` (stated as: every relation that
  holds between the cyclically consecutive entries of `K` relates them); it is invariant under
  rotation (`Consec.isRotated`), the ends of a list are consecutive on it (`consec_ends`), and
  deleting a third vertex keeps two vertices consecutive (`Consec.drop_head`);
* `Static L s H`: the current graph contains `L`, and every current edge between two alive
  vertices that is not an edge of `L` joins two vertices consecutive on the ghost. It holds
  initially (`static_init`) and is kept by every iteration together with `Inv`
  (`Inv.step_static`): a virtual edge is created between the two ghost neighbours of the
  eliminated vertex, which become consecutive on the new ghost;
* the two ghost neighbours `u`, `w` of a vertex `v` on a ghost of length at least four are not
  consecutive (`not_consec_ends`), so a current edge `u w` is an edge of `L`
  (`query_static`).
-/

@[expose] public section

namespace STACS2027.Ear

/-! ### Consecutive vertices of a cycle -/

/-- `a` and `b` are consecutive on the cycle `K` (in one of the two directions): every relation
that holds between the cyclically consecutive entries of `K` relates them. -/
def Consec (K : List ℕ) (a b : ℕ) : Prop := ∀ A : ℕ → ℕ → Prop, CycAdj A K → A a b ∨ A b a

theorem Consec.symm {K : List ℕ} {a b : ℕ} (h : Consec K a b) : Consec K b a :=
  fun A hA => (h A hA).symm

theorem Consec.isRotated {K K' : List ℕ} {a b : ℕ} (h : Consec K a b) (hr : K ~r K') :
    Consec K' a b := fun A hA => h A (hA.isRotated hr.symm)

/-- The two ends of a list are consecutive on it (as a cycle). -/
theorem consec_ends (C : List ℕ) : Consec C (C.getD 0 0) (C.getD (C.length - 1) 0) :=
  fun _ hA => Or.inr hA.2

/-- Deleting a third vertex keeps two vertices consecutive. -/
theorem Consec.drop_head {v a b : ℕ} {C : List ℕ} (h : Consec (v :: C) a b) (ha : a ≠ v)
    (hb : b ≠ v) : Consec C a b := by
  intro A hA
  have hA' : CycAdj (fun x y => A x y ∨ x = v ∨ y = v) (v :: C) := by
    refine ⟨fun j hj => ?_, Or.inr (Or.inr (by simp))⟩
    cases j with
    | zero => exact Or.inr (Or.inl (by simp))
    | succ i =>
      simp only [List.getD_cons_succ]
      simp only [List.length_cons] at hj
      exact Or.inl (hA.1 i (by omega))
  rcases h _ hA' with (h1 | h1 | h1) | (h1 | h1 | h1)
  · exact Or.inl h1
  · exact absurd h1 ha
  · exact absurd h1 hb
  · exact Or.inr h1
  · exact absurd h1 hb
  · exact absurd h1 ha

/-- On a cycle `v :: C` with `|C| ≥ 3`, the two neighbours of `v` are not consecutive. -/
theorem not_consec_ends {v : ℕ} {C : List ℕ} (hnd : (v :: C).Nodup) (h3 : 3 ≤ C.length) :
    ¬ Consec (v :: C) (C.getD 0 0) (C.getD (C.length - 1) 0) := by
  intro h
  have hvC : v ∉ C := (List.nodup_cons.mp hnd).1
  have hC : C.Nodup := (List.nodup_cons.mp hnd).2
  have hvu : v ≠ C.getD 0 0 := fun e => hvC (e ▸ getD_mem_of_lt (by omega))
  have hvw : v ≠ C.getD (C.length - 1) 0 := fun e => hvC (e ▸ getD_mem_of_lt (by omega))
  have hA : CycAdj (fun x y => ¬ ((x = C.getD 0 0 ∧ y = C.getD (C.length - 1) 0) ∨
      (x = C.getD (C.length - 1) 0 ∧ y = C.getD 0 0))) (v :: C) := by
    refine ⟨fun j hj => ?_, ?_⟩
    · cases j with
      | zero =>
        simp only [List.getD_cons_zero]
        rintro (⟨h1, -⟩ | ⟨h1, -⟩)
        · exact hvu h1
        · exact hvw h1
      | succ i =>
        simp only [List.getD_cons_succ]
        simp only [List.length_cons] at hj
        rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
        · have e1 := (hC.getD_inj (by omega) (by omega)).mp h1
          have e2 := (hC.getD_inj (by omega) (by omega)).mp h2
          omega
        · have e1 := (hC.getD_inj (by omega) (by omega)).mp h1
          omega
    · have e : (v :: C).getD ((v :: C).length - 1) 0 = C.getD (C.length - 1) 0 := by
        obtain ⟨k, hk⟩ : ∃ k, C.length = k + 1 := ⟨C.length - 1, by omega⟩
        simp [hk]
      simp only [e, List.getD_cons_zero]
      rintro (⟨-, h2⟩ | ⟨-, h2⟩)
      · exact hvw h2
      · exact hvu h2
  rcases h _ hA with h1 | h1
  · exact h1 (Or.inl ⟨rfl, rfl⟩)
  · exact h1 (Or.inr ⟨rfl, rfl⟩)

/-! ### The invariant -/

/-- **Static adjacency** on the edge list `L`, with the ghost `H`: the current graph contains
`L`, and every current edge between alive vertices that is not an edge of `L` joins two vertices
consecutive on the ghost. -/
structure Static (L : List Edge) (s : State) (H : List ℕ) : Prop where
  sub : ∀ a b, Adj L a b → s.mat a b = true
  virt : ∀ a ∈ H, ∀ b ∈ H, s.mat a b = true → Adj L a b ∨ Consec H a b

theorem static_init {N : ℕ} {L : List Edge} (hL : ∀ e ∈ L, e.1 < e.2) (H : List ℕ) :
    Static L (init N L) H :=
  ⟨fun a b h => (init_mat hL a b).mpr h, fun a _ b _ h => Or.inl ((init_mat hL a b).mp h)⟩

/-- **The invariants hold initially**, with the ghost `ham0`. -/
theorem inv_static_init {N : ℕ} {L : List Edge} (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N)
    (hnd : L.Nodup) {ham0 : List ℕ} (h0 : OuterplanarHam L ham0)
    (hv : ∀ v, v < N → v ∈ ham0) : Inv N ham0 (init N L) ham0 ∧ Static L (init N L) ham0 :=
  ⟨inv_init hL hnd h0 hv, static_init (fun e he => (hL e he).1) ham0⟩

section Step

variable {N : ℕ} {ham0 : List ℕ} {L : List Edge} {s : State} {H : List ℕ}

/-- An elimination keeps `Static`, with the new ghost `C`. -/
theorem ElimCtx.static {v u w : ℕ} {C : List ℕ} (E : ElimCtx N ham0 s H v C u w)
    (rest : List ℕ) (hS : Static L s H) : Static L (elim { s with stack := rest } v u w) C := by
  have hmat := E.mat_new rest
  refine ⟨fun a b h => (hmat a b).mpr (Or.inl (hS.sub a b h)), fun a ha b hb h => ?_⟩
  have haH := E.memC.mp ha
  have hbH := E.memC.mp hb
  rcases (hmat a b).mp h with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hS.virt a haH.1 b hbH.1 h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ((h2.isRotated E.rot).drop_head haH.2 hbH.2)
  · right
    rcases E.ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact consec_ends C
    · exact (consec_ends C).symm
  · right
    rcases E.ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (consec_ends C).symm
    · exact consec_ends C

/-- **One iteration keeps both invariants** (with a new ghost). -/
theorem Inv.step_static (hI : Inv N ham0 s H) (hS : Static L s H)
    (hc : s.stack ≠ [] ∧ 3 < s.cnt) : ∃ H', Inv N ham0 (Ear.step s) H' ∧ Static L (Ear.step s) H' := by
  obtain ⟨v, rest, hsv⟩ := List.exists_cons_of_ne_nil hc.1
  by_cases hv : s.dead v = false ∧ s.deg v = 2
  · obtain ⟨C, E⟩ := hI.elimCtx hc.2 hsv hv
    rw [step_elim hsv hv]
    exact ⟨C, E.inv_elim hsv, E.static rest hS⟩
  · rw [step_skip hsv hv]
    exact ⟨H, hI.skip hsv hv, ⟨hS.sub, hS.virt⟩⟩

/-- **The query is static**: when the popped vertex `v` (alive, degree two) is eliminated with
more than three alive vertices, its two neighbours `u`, `w` (the first two alive entries of its
list) are different, and `u w` is an edge of the current graph iff it is an edge of `L`. -/
theorem query_static (hI : Inv N ham0 s H) (hS : Static L s H) (hc : 3 < s.cnt) {v : ℕ}
    {rest : List ℕ} (hsv : s.stack = v :: rest) (hv : s.dead v = false ∧ s.deg v = 2) :
    (nbrs s v).getD 0 0 ≠ (nbrs s v).getD 1 0 ∧
      (s.mat ((nbrs s v).getD 0 0) ((nbrs s v).getD 1 0) = true ↔
        Adj L ((nbrs s v).getD 0 0) ((nbrs s v).getD 1 0)) := by
  obtain ⟨C, E⟩ := hI.elimCtx hc hsv hv
  refine ⟨E.u_ne_w, fun h => ?_, hS.sub _ _⟩
  rcases hS.virt _ (E.memC.mp E.uw_mem.1).1 _ (E.memC.mp E.uw_mem.2).1 h with h1 | h1
  · exact h1
  · have h2 := h1.isRotated E.rot
    exfalso
    rcases E.ends with ⟨hu, hw⟩ | ⟨hu, hw⟩
    · rw [hu, hw] at h2
      exact not_consec_ends E.ham.2.1 E.len h2
    · rw [hu, hw] at h2
      exact not_consec_ends E.ham.2.1 E.len h2.symm

end Step

end STACS2027.Ear
