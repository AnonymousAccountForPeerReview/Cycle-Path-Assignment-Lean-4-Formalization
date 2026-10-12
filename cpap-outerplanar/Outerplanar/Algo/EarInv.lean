module

public import Outerplanar.Algo.EarState
public import Outerplanar.Algo.EarCycle
import Outerplanar.Degenerate
import Mathlib.Tactic

/-!
# Ear elimination: the loop invariant (a "ghost" Hamiltonian cycle)

The current graph of a state `s` of the ear elimination has the alive vertices and the
pairs `a ≠ b` with `s.mat a b`. The invariant `Inv N ham0 s H` says that the *ghost* `H`
lists exactly the alive vertices and is a Hamiltonian cycle of the current graph without
crossings (`OHam`), that `cnt`, the degrees, the alive entries of the adjacency lists
(`nbrs`) and the stack are faithful, and that every successor function following `H`
becomes, after the reinsertions of the log, a successor function following `ham0`.

* `Inv.stack_ne_nil`: the stack is never empty — some alive vertex has degree two, by
  `outerplanarHam_degenerate` (at most two) and its two neighbours on the ghost (at least
  two).
* `Inv.step`: one iteration (with more than three alive vertices) preserves the invariant.
  An eliminated vertex `v` of degree two has as its only neighbours its two neighbours on
  the ghost (`Inv.elimCtx`: the elimination context `ElimCtx`, also used by
  `Outerplanar/Algo/EarStatic.lean`); the new ghost is the old one without `v` (`OHam.drop_head`
  of `Outerplanar/OuterplanarSym.lean`: the new edge joins two consecutive vertices and crosses
  nothing). A skipped entry keeps the ghost (`Inv.skip`).
* `Inv.loop`: hence the invariant holds after the loop.
-/

@[expose] public section

namespace STACS2027.Ear

/-- The alive entries of the adjacency list of `a` (as scanned by `step`). -/
def nbrs (s : State) (a : ℕ) : List ℕ := (s.adj a).filter fun x => s.dead x = false

/-- **The loop invariant**, with the ghost Hamiltonian cycle `H`. -/
structure Inv (N : ℕ) (ham0 : List ℕ) (s : State) (H : List ℕ) : Prop where
  mem : ∀ a, a ∈ H ↔ a < N ∧ s.dead a = false
  cnt : s.cnt = H.length
  symm : ∀ a b, s.mat a b = s.mat b a
  irrefl : ∀ a, s.mat a a = false
  ham : OHam (fun a b => s.mat a b = true) H
  nodup : ∀ a ∈ H, (nbrs s a).Nodup
  nbrs_iff : ∀ a ∈ H, ∀ x, x ∈ nbrs s a ↔ x ∈ H ∧ s.mat a x = true
  deg : ∀ a ∈ H, s.deg a = (nbrs s a).length
  stack : ∀ a ∈ H, s.deg a = 2 → a ∈ s.stack
  stack_lt : ∀ a ∈ s.stack, a < N
  log : ∀ succ, Rep succ H → Rep (s.log.foldl reinsert succ) ham0

/-! ### Lists and cycles -/

theorem two_le_length {l : List ℕ} {x y : ℕ} (hx : x ∈ l) (hy : y ∈ l) (hxy : x ≠ y) :
    2 ≤ l.length := by
  match l, hx, hy with
  | [], hx, _ => simp at hx
  | [z], hx, hy =>
    simp only [List.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  | _ :: _ :: _, _, _ => simp

theorem eq_pair_of_length_two {l : List ℕ} {x y : ℕ} (hl : l.length = 2) (hx : x ∈ l)
    (hy : y ∈ l) (hxy : x ≠ y) : l = [x, y] ∨ l = [y, x] := by
  match l, hl with
  | [p, q], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hxy

/-! ### The current graph as an edge list -/

/-- The edges between the vertices of `H` recorded by `m`. -/
def matGraph (m : ℕ → ℕ → Bool) (H : List ℕ) : Graph :=
  H.flatMap fun a => (H.filter fun b => m a b).map fun b => edge a b

theorem adj_matGraph {m : ℕ → ℕ → Bool} {H : List ℕ} (hm : ∀ a b, m a b = m b a) {a b : ℕ} :
    Adj (matGraph m H) a b ↔ a ≠ b ∧ a ∈ H ∧ b ∈ H ∧ m a b = true := by
  constructor
  · rintro ⟨hab, he⟩
    obtain ⟨a', ha', he'⟩ := List.mem_flatMap.mp he
    obtain ⟨b', hb', hee⟩ := List.mem_map.mp he'
    obtain ⟨hb'H, hm'⟩ := List.mem_filter.mp hb'
    rcases (edge_eq_iff _ _ _ _).mp hee with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hab, ha', hb'H, hm'⟩
    · exact ⟨hab, hb'H, ha', by rw [hm]; exact hm'⟩
  · rintro ⟨hab, ha, hb, hm'⟩
    exact ⟨hab, List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr
      ⟨b, List.mem_filter.mpr ⟨hb, hm'⟩, rfl⟩⟩⟩

/-! ### Progress -/

section Progress

variable {N : ℕ} {ham0 : List ℕ} {s : State} {H : List ℕ}

theorem Inv.matSymm (hI : Inv N ham0 s H) :
    ∀ a b, s.mat a b = true → s.mat b a = true := fun a b h => by rw [hI.symm]; exact h

/-- Every alive vertex has at least two alive neighbours. -/
theorem Inv.two_le_deg (hI : Inv N ham0 s H) {a : ℕ} (ha : a ∈ H) : 2 ≤ s.deg a := by
  obtain ⟨C, hr, hC⟩ := hI.ham.rotate_to hI.matSymm ha
  obtain ⟨e1, e2⟩ := hC.ends
  have hCnd : C.Nodup := (List.nodup_cons.mp hC.2.1).2
  have hlen : 2 ≤ C.length := by have := hC.1; simp at this; omega
  have hne : C.getD 0 0 ≠ C.getD (C.length - 1) 0 :=
    getD_ne_of_ne hCnd (by omega) (by omega) (by omega)
  have hmemH : ∀ i, i < C.length → C.getD i 0 ∈ H := fun i hi =>
    hr.mem_iff.mpr (List.mem_cons_of_mem _ (getD_mem_of_lt hi))
  have m1 : C.getD 0 0 ∈ nbrs s a := (hI.nbrs_iff a ha _).mpr ⟨hmemH 0 (by omega), e1⟩
  have m2 : C.getD (C.length - 1) 0 ∈ nbrs s a :=
    (hI.nbrs_iff a ha _).mpr ⟨hmemH _ (by omega), hI.matSymm _ _ e2⟩
  rw [hI.deg a ha]
  exact two_le_length m1 m2 hne

/-- Some alive vertex has degree two. -/
theorem Inv.exists_deg_two (hI : Inv N ham0 s H) : ∃ a ∈ H, s.deg a = 2 := by
  have hadj : ∀ a b, Adj (matGraph s.mat H) a b ↔ a ≠ b ∧ a ∈ H ∧ b ∈ H ∧ s.mat a b = true :=
    fun a b => adj_matGraph hI.symm
  have hO : OHam (Adj (matGraph s.mat H)) H :=
    hI.ham.congr (fun a ha b hb hab => by rw [hadj]; tauto)
  have hOH : OuterplanarHam (matGraph s.mat H) H :=
    hO.outerplanarHam (fun v ⟨u, huv⟩ => ((hadj u v).mp huv).2.2.1)
  have hne : H ≠ [] := by
    intro h
    have := hI.ham.1
    simp [h] at this
  obtain ⟨a, ha, hmax⟩ := outerplanarHam_degenerate hOH hne (fun u hu => hu)
  refine ⟨a, ha, le_antisymm ?_ (hI.two_le_deg ha)⟩
  rw [hI.deg a ha]
  by_contra hlt
  simp only [not_le] at hlt
  have hnd := hI.nodup a ha
  have hmem : ∀ i (hi : i < (nbrs s a).length), (nbrs s a)[i] ∈ H ∧
      s.mat a (nbrs s a)[i] = true := fun i hi =>
    (hI.nbrs_iff a ha _).mp (List.getElem_mem hi)
  have hA : ∀ i (hi : i < (nbrs s a).length), Adj (matGraph s.mat H) a (nbrs s a)[i] := by
    intro i hi
    refine (hadj _ _).mpr ⟨fun e => ?_, ha, (hmem i hi).1, (hmem i hi).2⟩
    have := (hmem i hi).2
    rw [← e, hI.irrefl] at this
    exact Bool.false_ne_true this
  rcases hmax _ _ _ (hmem 0 (by omega)).1 (hmem 1 (by omega)).1 (hmem 2 (by omega)).1
    (hA 0 (by omega)) (hA 1 (by omega)) (hA 2 (by omega)) with e | e | e
  · have := hnd.getElem_inj_iff.mp e; omega
  · have := hnd.getElem_inj_iff.mp e; omega
  · have := hnd.getElem_inj_iff.mp e; omega

/-- **Progress**: the stack is never empty. -/
theorem Inv.stack_ne_nil (hI : Inv N ham0 s H) : s.stack ≠ [] := by
  obtain ⟨a, ha, hd⟩ := hI.exists_deg_two
  intro h
  have := hI.stack a ha hd
  rw [h] at this
  exact List.not_mem_nil this

end Progress

/-! ### One elimination -/

theorem filter_kill (l : List ℕ) (dead : ℕ → Bool) (v : ℕ) :
    l.filter (fun x => Function.update dead v true x = false) =
      (l.filter fun x => dead x = false).filter (fun x => x ≠ v) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  by_cases hx : x = v
  · subst hx; simp
  · simp [hx]

theorem length_filter_ne {l : List ℕ} (hl : l.Nodup) {v : ℕ} (hv : v ∈ l) :
    (l.filter fun x => x ≠ v).length + 1 = l.length := by
  have h := List.length_erase_of_mem hv
  rw [hl.erase_eq_filter] at h
  have hpos : 0 < l.length := List.length_pos_of_mem hv
  have he : (l.filter fun x => x != v) = l.filter fun x => x ≠ v := by
    apply List.filter_congr
    intro x _
    by_cases hx : x = v <;> simp [hx]
  rw [he] at h
  omega

theorem filter_ne_of_not_mem {l : List ℕ} {v : ℕ} (hv : v ∉ l) :
    (l.filter fun x => x ≠ v) = l :=
  List.filter_eq_self.mpr fun x hx => by
    simp only [ne_eq, decide_eq_true_eq]
    rintro rfl
    exact hv hx

/-- The situation of an elimination of `v` with logged neighbours `u`, `w`: `v :: C` is a
rotation of the ghost and `u`, `w` are the two ends of `C`, the only neighbours of `v`. -/
structure ElimCtx (N : ℕ) (ham0 : List ℕ) (s : State) (H : List ℕ) (v : ℕ) (C : List ℕ)
    (u w : ℕ) : Prop where
  inv : Inv N ham0 s H
  rot : H ~r v :: C
  len : 3 ≤ C.length
  ham : OHam (fun a b => s.mat a b = true) (v :: C)
  ends : (u = C.getD 0 0 ∧ w = C.getD (C.length - 1) 0) ∨
    (u = C.getD (C.length - 1) 0 ∧ w = C.getD 0 0)
  nbv : ∀ x ∈ H, s.mat v x = true → x = u ∨ x = w

namespace ElimCtx

variable {N : ℕ} {ham0 : List ℕ} {s : State} {H : List ℕ} {v : ℕ} {C : List ℕ} {u w : ℕ}

theorem nodupC (E : ElimCtx N ham0 s H v C u w) : C.Nodup :=
  (List.nodup_cons.mp E.ham.2.1).2

theorem v_notMem (E : ElimCtx N ham0 s H v C u w) : v ∉ C :=
  (List.nodup_cons.mp E.ham.2.1).1

theorem memH (E : ElimCtx N ham0 s H v C u w) {x : ℕ} : x ∈ H ↔ x = v ∨ x ∈ C := by
  rw [E.rot.mem_iff, List.mem_cons]

theorem memC (E : ElimCtx N ham0 s H v C u w) {x : ℕ} : x ∈ C ↔ x ∈ H ∧ x ≠ v := by
  rw [E.memH]
  constructor
  · intro hx
    exact ⟨Or.inr hx, fun e => E.v_notMem (e ▸ hx)⟩
  · rintro ⟨hx | hx, hne⟩
    · exact absurd hx hne
    · exact hx

theorem uw_mem (E : ElimCtx N ham0 s H v C u w) : u ∈ C ∧ w ∈ C := by
  have h0 : C.getD 0 0 ∈ C := getD_mem_of_lt (by have := E.len; omega)
  have h1 : C.getD (C.length - 1) 0 ∈ C := getD_mem_of_lt (by have := E.len; omega)
  rcases E.ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨h0, h1⟩
  · exact ⟨h1, h0⟩

theorem u_ne_w (E : ElimCtx N ham0 s H v C u w) : u ≠ w := by
  have hne : C.getD 0 0 ≠ C.getD (C.length - 1) 0 :=
    getD_ne_of_ne E.nodupC (by have := E.len; omega) (by have := E.len; omega)
      (by have := E.len; omega)
  rcases E.ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hne
  · exact hne.symm

theorem mat_vu (E : ElimCtx N ham0 s H v C u w) : s.mat v u = true ∧ s.mat v w = true := by
  obtain ⟨e1, e2⟩ := E.ham.ends
  have e2' := E.inv.matSymm _ _ e2
  rcases E.ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨e1, e2'⟩
  · exact ⟨e2', e1⟩

theorem mat_av (E : ElimCtx N ham0 s H v C u w) {a : ℕ} (ha : a ∈ H) :
    s.mat a v = true ↔ a = u ∨ a = w := by
  constructor
  · intro h
    exact E.nbv a ha (E.inv.matSymm _ _ h)
  · rintro (rfl | rfl)
    · exact E.inv.matSymm _ _ E.mat_vu.1
    · exact E.inv.matSymm _ _ E.mat_vu.2

/-- The adjacency matrix after the elimination. -/
theorem mat_new (E : ElimCtx N ham0 s H v C u w) (rest : List ℕ) (a b : ℕ) :
    (elim { s with stack := rest } v u w).mat a b = true ↔
      s.mat a b = true ∨ (a = u ∧ b = w) ∨ (a = w ∧ b = u) := by
  cases h : s.mat u w
  · rw [elim_mat_false (s := { s with stack := rest }) v h]
    simp only [update2]
    split_ifs with h1 h2 <;> simp_all
  · rw [elim_mat_true (s := { s with stack := rest }) v h]
    have h' : s.mat w u = true := E.inv.matSymm _ _ h
    constructor
    · exact Or.inl
    · rintro (h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact h1
      · exact h
      · exact h'

/-- The alive neighbours of a vertex after the elimination, from those before: `E'` are the
new ones (the other end of the new edge). -/
theorem nbrs_new (E : ElimCtx N ham0 s H v C u w) {s' : State} {a : ℕ} (ha : a ∈ C)
    (Ex : List ℕ) (hdead : s'.dead = Function.update s.dead v true)
    (hadj : s'.adj a = Ex ++ s.adj a) (hEx : ∀ q ∈ Ex, q ∈ C ∧ s.mat a q = false)
    (hExnd : Ex.Nodup) (hmat : ∀ x, s'.mat a x = true ↔ s.mat a x = true ∨ x ∈ Ex)
    (hdeg : s'.deg a + (if s.mat a v = true then 1 else 0) = s.deg a + Ex.length) :
    (nbrs s' a).Nodup ∧ (∀ x, x ∈ nbrs s' a ↔ x ∈ C ∧ s'.mat a x = true) ∧
      s'.deg a = (nbrs s' a).length := by
  have haH : a ∈ H := (E.memC.mp ha).1
  have hI := E.inv
  have hEq : nbrs s' a = Ex ++ (nbrs s a).filter (fun x => x ≠ v) := by
    have hEx' : ∀ q ∈ Ex, s.dead q = false ∧ q ≠ v := by
      intro q hq
      obtain ⟨hqH, hqv⟩ := E.memC.mp (hEx q hq).1
      exact ⟨((hI.mem q).mp hqH).2, hqv⟩
    simp only [nbrs, hadj, hdead, List.filter_append, filter_kill]
    congr 1
    have h1 : Ex.filter (fun x => decide (s.dead x = false)) = Ex :=
      List.filter_eq_self.mpr (fun q hq => by simpa using (hEx' q hq).1)
    have h2 : Ex.filter (fun x => decide (x ≠ v)) = Ex :=
      List.filter_eq_self.mpr (fun q hq => by simpa using (hEx' q hq).2)
    rw [h1, h2]
  rw [hEq]
  refine ⟨?_, ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨hExnd, (hI.nodup a haH).filter _, ?_⟩
    rintro q hq x hx rfl
    have := ((hI.nbrs_iff a haH q).mp (List.mem_filter.mp hx).1).2
    rw [(hEx q hq).2] at this
    exact Bool.false_ne_true this
  · intro x
    rw [List.mem_append, List.mem_filter, hmat, hI.nbrs_iff a haH, E.memC]
    simp only [ne_eq, decide_eq_true_eq]
    constructor
    · rintro (hx | ⟨⟨hxH, hm⟩, hxv⟩)
      · exact ⟨E.memC.mp (hEx x hx).1, Or.inr hx⟩
      · exact ⟨⟨hxH, hxv⟩, Or.inl hm⟩
    · rintro ⟨⟨hxH, hxv⟩, hm | hx⟩
      · exact Or.inr ⟨⟨hxH, hm⟩, hxv⟩
      · exact Or.inl hx
  · rw [List.length_append]
    have hd := hI.deg a haH
    by_cases hav : s.mat a v = true
    · have hvn : v ∈ nbrs s a := (hI.nbrs_iff a haH v).mpr ⟨E.memH.mpr (Or.inl rfl), hav⟩
      have := length_filter_ne (hI.nodup a haH) hvn
      simp only [hav, ite_true] at hdeg
      omega
    · have hvn : v ∉ nbrs s a := fun h => hav ((hI.nbrs_iff a haH v).mp h).2
      rw [filter_ne_of_not_mem hvn]
      simp only [hav, Bool.false_eq_true, ite_false] at hdeg
      omega

/-- **One elimination preserves the invariant**, with the ghost `C`. -/
theorem inv_elim (E : ElimCtx N ham0 s H v C u w) {rest : List ℕ}
    (hsv : s.stack = v :: rest) : Inv N ham0 (elim { s with stack := rest } v u w) C := by
  have hI := E.inv
  have huw := E.u_ne_w
  have huC := E.uw_mem.1
  have hwC := E.uw_mem.2
  have huH := (E.memC.mp huC).1
  have hwH := (E.memC.mp hwC).1
  have hdead : (elim { s with stack := rest } v u w).dead = Function.update s.dead v true :=
    elim_dead _ _ _ _
  have hlenH : H.length = C.length + 1 := by
    rw [E.rot.perm.length_eq, List.length_cons]
  have hmat := E.mat_new rest
  have hdegu : 1 ≤ s.deg u := by have := hI.two_le_deg huH; omega
  have hdegw : 1 ≤ s.deg w := by have := hI.two_le_deg hwH; omega
  -- the alive neighbours, the degrees
  have hnb : ∀ a ∈ C, (nbrs (elim { s with stack := rest } v u w) a).Nodup ∧
      (∀ x, x ∈ nbrs (elim { s with stack := rest } v u w) a ↔
        x ∈ C ∧ (elim { s with stack := rest } v u w).mat a x = true) ∧
      (elim { s with stack := rest } v u w).deg a =
        (nbrs (elim { s with stack := rest } v u w) a).length := by
    intro a ha
    have haH : a ∈ H := (E.memC.mp ha).1
    have hav := E.mat_av haH
    cases h : s.mat u w
    · -- a new edge `u w`
      have hdeg' := elim_deg_false (s := { s with stack := rest }) v h
      have hadj' := elim_adj_false (s := { s with stack := rest }) v h huw
      by_cases hau : a = u
      · subst hau
        refine E.nbrs_new ha [w] hdead ?_ ?_ (List.nodup_singleton _) ?_ ?_
        · rw [hadj', Function.update_of_ne huw, Function.update_self]; rfl
        · intro q hq
          rw [List.mem_singleton.mp hq]
          exact ⟨hwC, h⟩
        · intro x
          rw [hmat, List.mem_singleton]
          constructor
          · rintro (h1 | ⟨-, rfl⟩ | ⟨h2, -⟩)
            · exact Or.inl h1
            · exact Or.inr rfl
            · exact absurd h2 huw
          · rintro (h1 | rfl)
            · exact Or.inl h1
            · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · rw [hdeg', (hav).mpr (Or.inl rfl)]
          simp
      by_cases haw : a = w
      · subst haw
        refine E.nbrs_new ha [u] hdead ?_ ?_ (List.nodup_singleton _) ?_ ?_
        · rw [hadj', Function.update_self]; rfl
        · intro q hq
          rw [List.mem_singleton.mp hq]
          refine ⟨huC, ?_⟩
          rw [hI.symm]
          exact h
        · intro x
          rw [hmat, List.mem_singleton]
          constructor
          · rintro (h1 | ⟨h2, -⟩ | ⟨-, rfl⟩)
            · exact Or.inl h1
            · exact absurd h2.symm huw
            · exact Or.inr rfl
          · rintro (h1 | rfl)
            · exact Or.inl h1
            · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · rw [hdeg', (hav).mpr (Or.inr rfl)]
          simp
      · refine E.nbrs_new ha [] hdead ?_ (by simp) List.nodup_nil ?_ ?_
        · rw [hadj', Function.update_of_ne haw, Function.update_of_ne hau]; rfl
        · intro x
          rw [hmat]
          simp [hau, haw]
        · have : s.mat a v = false := by
            cases hh : s.mat a v
            · rfl
            · rcases hav.mp hh with e | e
              · exact absurd e hau
              · exact absurd e haw
          rw [hdeg', this]
          simp
    · -- the edge `u w` exists already
      have hdeg' := elim_deg_true (s := { s with stack := rest }) v h huw
      have hadj' := elim_adj_true (s := { s with stack := rest }) v h
      have hmat' := elim_mat_true (s := { s with stack := rest }) v h
      refine E.nbrs_new ha [] hdead (by rw [hadj']; rfl) (by simp) List.nodup_nil ?_ ?_
      · intro x
        rw [hmat']
        simp
      · rw [hdeg']
        by_cases hau : a = u
        · subst hau
          rw [Function.update_of_ne huw, Function.update_self, (hav).mpr (Or.inl rfl)]
          simp only [ite_true, List.length_nil]
          show s.deg a - 1 + 1 = s.deg a + 0
          omega
        by_cases haw : a = w
        · subst haw
          rw [Function.update_self, (hav).mpr (Or.inr rfl)]
          simp only [ite_true, List.length_nil]
          show s.deg a - 1 + 1 = s.deg a + 0
          omega
        · have : s.mat a v = false := by
            cases hh : s.mat a v
            · rfl
            · rcases hav.mp hh with e | e
              · exact absurd e hau
              · exact absurd e haw
          rw [Function.update_of_ne haw, Function.update_of_ne hau, this]
          simp only [Bool.false_eq_true, ite_false, List.length_nil]
  refine
    { mem := ?_, cnt := ?_, symm := ?_, irrefl := ?_, ham := ?_, nodup := ?_,
      nbrs_iff := ?_, deg := ?_, stack := ?_, stack_lt := ?_, log := ?_ }
  · intro a
    rw [E.memC, hI.mem, hdead]
    by_cases hav : a = v
    · subst hav
      simp
    · simp [hav]
  · rw [elim_cnt]
    show s.cnt - 1 = C.length
    rw [hI.cnt, hlenH]
    rfl
  · intro a b
    apply Bool.eq_iff_iff.mpr
    rw [hmat, hmat, hI.symm]
    tauto
  · intro a
    cases h : (elim { s with stack := rest } v u w).mat a a
    · rfl
    · rcases (hmat a a).mp h with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hI.irrefl] at h1; exact absurd h1 Bool.false_ne_true
      · exact absurd rfl huw
      · exact absurd rfl huw
  · refine E.ham.drop_head E.len fun a _ b _ => ?_
    rw [hmat]
    rcases E.ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · tauto
  · exact fun a ha => (hnb a ha).1
  · exact fun a ha => (hnb a ha).2.1
  · exact fun a ha => (hnb a ha).2.2
  · intro a ha hd2
    have hav : a ≠ v := (E.memC.mp ha).2
    have haH : a ∈ H := (E.memC.mp ha).1
    have hrest : s.deg a = 2 → a ∈ rest := by
      intro h2
      have := hI.stack a haH h2
      rw [hsv] at this
      rcases List.mem_cons.mp this with e | e
      · exact absurd e hav
      · exact e
    cases h : s.mat u w
    · rw [elim_deg_false (s := { s with stack := rest }) v h] at hd2
      rw [elim_stack_false (s := { s with stack := rest }) v h]
      exact hrest hd2
    · rw [elim_deg_true (s := { s with stack := rest }) v h huw] at hd2
      by_cases haw : a = w
      · subst haw
        rw [Function.update_self] at hd2
        exact elim_stack_w (s := { s with stack := rest }) v huw h hd2
      by_cases hau : a = u
      · subst hau
        rw [Function.update_of_ne huw, Function.update_self] at hd2
        exact elim_stack_u (s := { s with stack := rest }) v huw h hd2
      · rw [Function.update_of_ne haw, Function.update_of_ne hau] at hd2
        exact mem_elim_stack (s := { s with stack := rest }) v huw (hrest hd2)
  · intro x hx
    rcases elim_stack_sub (s := { s with stack := rest }) v huw hx with hx | rfl | rfl
    · exact hI.stack_lt x (by rw [hsv]; exact List.mem_cons_of_mem _ hx)
    · exact ((hI.mem _).mp huH).1
    · exact ((hI.mem _).mp hwH).1
  · intro succ hrep
    rw [elim_log, List.foldl_cons]
    apply hI.log
    exact (rep_reinsert E.nodupC E.len E.v_notMem E.ends hrep).isRotated E.rot.symm

end ElimCtx

/-! ### One step, the loop -/

section Step

variable {N : ℕ} {ham0 : List ℕ} {s : State} {H : List ℕ}

/-- **The situation of an elimination**: with more than three alive vertices, a popped alive
vertex `v` of degree two is eliminated with its two ghost neighbours, the first two alive
entries of its list. -/
theorem Inv.elimCtx (hI : Inv N ham0 s H) (hc : 3 < s.cnt) {v : ℕ} {rest : List ℕ}
    (hsv : s.stack = v :: rest) (hv : s.dead v = false ∧ s.deg v = 2) :
    ∃ C, ElimCtx N ham0 s H v C ((nbrs s v).getD 0 0) ((nbrs s v).getD 1 0) := by
  have hvH : v ∈ H := (hI.mem v).mpr ⟨hI.stack_lt v (by rw [hsv]; simp), hv.1⟩
  obtain ⟨C, hr, hC⟩ := hI.ham.rotate_to hI.matSymm hvH
  have hlenH : H.length = C.length + 1 := by rw [hr.perm.length_eq, List.length_cons]
  have hC3 : 3 ≤ C.length := by have := hI.cnt; omega
  obtain ⟨e1, e2⟩ := hC.ends
  have hCnd : C.Nodup := (List.nodup_cons.mp hC.2.1).2
  have hne : C.getD 0 0 ≠ C.getD (C.length - 1) 0 :=
    getD_ne_of_ne hCnd (by omega) (by omega) (by omega)
  have hmemH : ∀ i, i < C.length → C.getD i 0 ∈ H := fun i hi =>
    hr.mem_iff.mpr (List.mem_cons_of_mem _ (getD_mem_of_lt hi))
  have m1 : C.getD 0 0 ∈ nbrs s v := (hI.nbrs_iff v hvH _).mpr ⟨hmemH 0 (by omega), e1⟩
  have m2 : C.getD (C.length - 1) 0 ∈ nbrs s v :=
    (hI.nbrs_iff v hvH _).mpr ⟨hmemH _ (by omega), hI.matSymm _ _ e2⟩
  have hl2 : (nbrs s v).length = 2 := by rw [← hI.deg v hvH]; exact hv.2
  have hpair := eq_pair_of_length_two hl2 m1 m2 hne
  have hends : ((nbrs s v).getD 0 0 = C.getD 0 0 ∧
      (nbrs s v).getD 1 0 = C.getD (C.length - 1) 0) ∨
      ((nbrs s v).getD 0 0 = C.getD (C.length - 1) 0 ∧
        (nbrs s v).getD 1 0 = C.getD 0 0) := by
    rcases hpair with h | h <;> rw [h] <;> simp
  have hnbv : ∀ x ∈ H, s.mat v x = true →
      x = (nbrs s v).getD 0 0 ∨ x = (nbrs s v).getD 1 0 := by
    intro x hx hm
    have hxn := (hI.nbrs_iff v hvH x).mpr ⟨hx, hm⟩
    rcases hpair with h | h <;> rw [h] at hxn ⊢ <;> simpa using hxn
  exact ⟨C, hI, hr, hC3, hC, hends, hnbv⟩

/-- A skipped entry (dead, or not of degree two) keeps the invariant with the same ghost. -/
theorem Inv.skip (hI : Inv N ham0 s H) {v : ℕ} {rest : List ℕ} (hsv : s.stack = v :: rest)
    (hv : ¬ (s.dead v = false ∧ s.deg v = 2)) : Inv N ham0 { s with stack := rest } H := by
  refine { hI with stack := ?_, stack_lt := ?_ }
  · intro a ha hd
    have := hI.stack a ha hd
    rw [hsv] at this
    rcases List.mem_cons.mp this with rfl | h
    · exact absurd ⟨((hI.mem a).mp ha).2, hd⟩ hv
    · exact h
  · intro a ha
    exact hI.stack_lt a (by rw [hsv]; exact List.mem_cons_of_mem _ ha)

/-- **One iteration preserves the invariant** (with a new ghost). -/
theorem Inv.step (hI : Inv N ham0 s H) (hc : s.stack ≠ [] ∧ 3 < s.cnt) :
    ∃ H', Inv N ham0 (step s) H' := by
  obtain ⟨v, rest, hsv⟩ := List.exists_cons_of_ne_nil hc.1
  by_cases hv : s.dead v = false ∧ s.deg v = 2
  · obtain ⟨C, E⟩ := hI.elimCtx hc.2 hsv hv
    rw [step_elim hsv hv]
    exact ⟨C, E.inv_elim hsv⟩
  · rw [step_skip hsv hv]
    exact ⟨H, hI.skip hsv hv⟩

/-- The invariant holds after the loop. -/
theorem Inv.loop (hI : Inv N ham0 s H) (f : ℕ) : ∃ H', Inv N ham0 (loop f s) H' := by
  induction f generalizing s H with
  | zero => exact ⟨H, hI⟩
  | succ f ih =>
    unfold Ear.loop
    split
    · next hc =>
      obtain ⟨H', hI'⟩ := hI.step hc
      exact ih hI'
    · exact ⟨H, hI⟩

end Step

end STACS2027.Ear
