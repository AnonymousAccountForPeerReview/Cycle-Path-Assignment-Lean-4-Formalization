module

public import Outerplanar.Algo.EarState
import Mathlib.Tactic

/-!
# The ear elimination on the machine, abstract side

Facts about `Ear.earHam` (`Outerplanar/Algo/Ear.lean`) used by the machine of `EarProg.lean`:

* **The loop.** `fin s = loop (pot s + 1) s` is the state where the elimination loop started in
  `s` stops; it does not depend on the fuel beyond the potential (`loop_eq_fin`), it is kept by
  a running step (`fin_step`), it is `s` itself for a stopped state (`fin_stop`), and
  `loop (4 N + 1) (init N L) = fin (init N L)` (`loop_init`). The machine's `while` loop thus
  ends in the state of `earHam`.
* **Bounds kept by the loop** (`Good`): stack entries, adjacency entries and logged vertices are
  below `N`, `|log| + cnt = N`, `pot ≤ 4 N` (`good_init`, `good_step`).
* **The amortization**: `asum N s`, the total length of the adjacency lists of the alive
  vertices; an elimination of `v` lowers it by `|adj v|` up to `2` (`asum_elim`);
  initially it is at most `2 |L|` (`asum_init_le`).
* **Prefix forms** of the initialization (`initAdj_take_succ`, `stackPre_succ`), of the scans
  for the first two (three) alive entries (`getD_snoc`), of the reinsertion fold
  (`foldl_take_succ`) and of the final walk (`walk_getElem`).
-/

@[expose] public section

namespace STACS2027.RAM.EarR

open STACS2027 STACS2027.Ear

/-! ### The loop and its final state -/

/-- The guard of the elimination loop. -/
def Running (s : State) : Prop := s.stack ≠ [] ∧ 3 < s.cnt

instance (s : State) : Decidable (Running s) := inferInstanceAs (Decidable (_ ∧ _))

theorem loop_eq_loop : ∀ (f f' : ℕ) (s : State), pot s < f → pot s < f' → loop f s = loop f' s
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, f' + 1, s, h, h' => by
    simp only [loop]
    split
    · next hc =>
      have := pot_step s hc
      exact loop_eq_loop f f' (step s) (by omega) (by omega)
    · rfl

/-- The state in which the elimination loop started in `s` stops. -/
def fin (s : State) : State := loop (pot s + 1) s

theorem loop_eq_fin {f : ℕ} {s : State} (h : pot s < f) : loop f s = fin s :=
  loop_eq_loop f _ s h (by omega)

theorem fin_step {s : State} (h : Running s) : fin (step s) = fin s := by
  have hp := pot_step s h
  have h' : s.stack ≠ [] ∧ 3 < s.cnt := h
  rw [fin, fin]
  conv_rhs => rw [loop]
  simp only [h'.1, h'.2, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
  exact loop_eq_loop _ _ _ (by omega) (by omega)

theorem fin_stop {s : State} (h : ¬ Running s) : fin s = s := by
  have h' : ¬ (s.stack ≠ [] ∧ 3 < s.cnt) := h
  rw [fin, loop]
  simp only [h', ↓reduceIte]

theorem loop_init (N : ℕ) (L : List Edge) : loop (4 * N + 1) (init N L) = fin (init N L) :=
  loop_eq_fin (by have := pot_init_le N L; omega)

/-! ### Bounds kept by the loop -/

/-- The bounds the machine needs, kept by every running step. -/
structure Good (N : ℕ) (s : State) : Prop where
  stack_lt : ∀ v ∈ s.stack, v < N
  adj_lt : ∀ v, ∀ x ∈ s.adj v, x < N
  log_lt : ∀ e ∈ s.log, e.1 < N ∧ e.2.1 < N ∧ e.2.2 < N
  log_len : s.log.length + s.cnt = N
  pot_le : pot s ≤ 4 * N

theorem getD_lt {l : List ℕ} {N : ℕ} (h : ∀ x ∈ l, x < N) (hN : 0 < N) (i : ℕ) : l.getD i 0 < N := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simpa using hN
  | some x => simpa using h x (List.mem_of_getElem? hi)

theorem mem_decDeg_stack {s : State} {u x : ℕ} (hx : x ∈ (decDeg s u).stack) : x ∈ s.stack ∨ x = u := by
  rw [decDeg_stack] at hx
  split_ifs at hx with h
  · rcases List.mem_cons.mp hx with h | h
    · exact Or.inr h
    · exact Or.inl h
  · exact Or.inl hx

theorem mem_elim_stack {s : State} {v u w x : ℕ} (hx : x ∈ (elim s v u w).stack) :
    x ∈ s.stack ∨ x = u ∨ x = w := by
  cases h : s.mat u w
  · simp only [elim, h, Bool.false_eq_true, ite_false] at hx
    exact Or.inl hx
  · simp only [elim, h, ite_true] at hx
    rcases mem_decDeg_stack hx with h | h
    · rcases mem_decDeg_stack h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem mem_elim_adj {s : State} {v u w y x : ℕ} (hx : x ∈ (elim s v u w).adj y) :
    x ∈ s.adj y ∨ x = u ∨ x = w := by
  cases h : s.mat u w
  · simp only [elim, h, Bool.false_eq_true, ite_false, Function.update_apply] at hx
    split_ifs at hx <;> subst_vars <;> (try simp only [List.mem_cons] at hx) <;> tauto
  · simp only [elim, h, ite_true, decDeg_adj] at hx
    exact Or.inl hx

/-- The two neighbours chosen by `step` for the popped vertex `v`. -/
def nbOf (s : State) (v : ℕ) : List ℕ := (s.adj v).filter fun x => s.dead x = false

theorem nbOf_lt {N : ℕ} {s : State} (hs : ∀ v, ∀ x ∈ s.adj v, x < N) (hN : 0 < N) (v i : ℕ) :
    (nbOf s v).getD i 0 < N :=
  getD_lt (fun x hx => hs v x (List.mem_filter.mp hx).1) hN i

theorem good_step {N : ℕ} {s : State} (hG : Good N s) (hN : 0 < N) (hR : Running s) :
    Good N (step s) := by
  obtain ⟨hs, hc⟩ := hR
  obtain ⟨v, rest, hsv⟩ := List.exists_cons_of_ne_nil hs
  have hpot := pot_step s ⟨hs, hc⟩
  have hv : v < N := hG.stack_lt v (by simp [hsv])
  have hrest : ∀ x ∈ rest, x < N := fun x hx => hG.stack_lt x (by simp [hsv, hx])
  by_cases h : s.dead v = false ∧ s.deg v = 2
  · rw [step_elim hsv h] at hpot ⊢
    have hu := nbOf_lt hG.adj_lt hN v 0
    have hw := nbOf_lt hG.adj_lt hN v 1
    simp only [nbOf] at hu hw
    refine ⟨fun x hx => ?_, fun y x hx => ?_, fun e he => ?_, ?_, by have := hG.pot_le; omega⟩
    · rcases mem_elim_stack hx with h | h | h
      · exact hrest x h
      · rw [h]; exact hu
      · rw [h]; exact hw
    · rcases mem_elim_adj hx with h | h | h
      · exact hG.adj_lt y x h
      · rw [h]; exact hu
      · rw [h]; exact hw
    · rw [elim_log] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨hv, hu, hw⟩
      · exact hG.log_lt e he
    · rw [elim_log, elim_cnt]
      have := hG.log_len
      simp only [List.length_cons]
      omega
  · rw [step_skip hsv h] at hpot ⊢
    exact ⟨hrest, hG.adj_lt, hG.log_lt, hG.log_len, by have := hG.pot_le; omega⟩

/-! ### The initial state -/

/-- The initial adjacency matrix of the edges `l` (a field of the abstract state only: the machine
does not store it). -/
def matInit (l : List Edge) : ℕ → ℕ → Bool :=
  l.foldl (fun m e => update2 (update2 m e.1 e.2 true) e.2 e.1 true) (fun _ _ => false)

/-- The vertices below `j` of degree two, in increasing order. -/
def stackPre (L : List Edge) (j : ℕ) : List ℕ :=
  (List.range j).filter fun v => (initAdj L v).length = 2

theorem init_adj (N : ℕ) (L : List Edge) : (init N L).adj = initAdj L := rfl
theorem init_deg (N : ℕ) (L : List Edge) : (init N L).deg = fun v => (initAdj L v).length := rfl
theorem init_dead (N : ℕ) (L : List Edge) : (init N L).dead = fun _ => false := rfl
theorem init_stack (N : ℕ) (L : List Edge) : (init N L).stack = (stackPre L N).reverse := rfl
theorem init_log (N : ℕ) (L : List Edge) : (init N L).log = [] := rfl
theorem init_cnt (N : ℕ) (L : List Edge) : (init N L).cnt = N := rfl

theorem take_succ_eq {α : Type*} (l : List α) (j : ℕ) (hj : j < l.length) :
    l.take (j + 1) = l.take j ++ [l[j]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]

theorem initAdj_append (l : List Edge) (e : Edge) :
    initAdj (l ++ [e]) = Function.update (Function.update (initAdj l) e.1 (e.2 :: initAdj l e.1)) e.2
      (e.1 :: Function.update (initAdj l) e.1 (e.2 :: initAdj l e.1) e.2) := by
  simp only [initAdj, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem initAdj_take_succ (L : List Edge) (j : ℕ) (hj : j < L.length) :
    initAdj (L.take (j + 1)) = Function.update (Function.update (initAdj (L.take j)) L[j].1
      (L[j].2 :: initAdj (L.take j) L[j].1)) L[j].2
      (L[j].1 :: Function.update (initAdj (L.take j)) L[j].1
        (L[j].2 :: initAdj (L.take j) L[j].1) L[j].2) := by
  rw [take_succ_eq L j hj, initAdj_append]

@[simp] theorem initAdj_nil : initAdj [] = fun _ => [] := rfl

theorem stackPre_succ (L : List Edge) (j : ℕ) :
    stackPre L (j + 1) = stackPre L j ++ (if (initAdj L j).length = 2 then [j] else []) := by
  simp only [stackPre, List.range_succ, List.filter_append, List.filter_singleton]
  split_ifs with h <;> simp [h]

theorem stackPre_lt (L : List Edge) (j : ℕ) : ∀ x ∈ stackPre L j, x < j := fun x hx => by
  simp only [stackPre, List.mem_filter, List.mem_range] at hx
  exact hx.1

theorem length_stackPre_le (L : List Edge) (j : ℕ) : (stackPre L j).length ≤ j := by
  have := List.length_filter_le (fun v => decide ((initAdj L v).length = 2)) (List.range j)
  simpa [stackPre] using this

theorem mem_update_cons {f : ℕ → List ℕ} {a b y x : ℕ} (hx : x ∈ Function.update f a (b :: f a) y) :
    x = b ∨ x ∈ f y := by
  by_cases h : y = a
  · subst h
    simpa using hx
  · rw [Function.update_of_ne h] at hx
    exact Or.inr hx

theorem initAdj_lt {N : ℕ} {l : List Edge} (h : ∀ e ∈ l, e.1 < N ∧ e.2 < N) :
    ∀ v, ∀ x ∈ initAdj l v, x < N := by
  induction l using List.reverseRecOn with
  | nil => intro v x hx; simp at hx
  | append_singleton l e ih =>
    have ih' := ih fun e' he' => h e' (by simp [he'])
    have he := h e (by simp)
    intro v x hx
    rw [initAdj_append] at hx
    rcases mem_update_cons hx with rfl | hx
    · exact he.1
    rcases mem_update_cons hx with rfl | hx
    · exact he.2
    exact ih' _ _ hx

theorem length_update_cons (f : ℕ → List ℕ) (a b x : ℕ) :
    (Function.update f a (b :: f a) x).length = (f x).length + if x = a then 1 else 0 := by
  by_cases h : x = a
  · subst h; simp
  · simp [h]

theorem sum_initAdj {N : ℕ} {l : List Edge} (h : ∀ e ∈ l, e.1 < N ∧ e.2 < N) :
    ∑ x ∈ Finset.range N, (initAdj l x).length = 2 * l.length := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l e ih =>
    have ih' := ih fun e' he' => h e' (by simp [he'])
    have he := h e (by simp)
    rw [initAdj_append]
    have hpt : ∀ x, (Function.update (Function.update (initAdj l) e.1 (e.2 :: initAdj l e.1)) e.2
        (e.1 :: Function.update (initAdj l) e.1 (e.2 :: initAdj l e.1) e.2) x).length =
        (initAdj l x).length + (if x = e.1 then 1 else 0) + (if x = e.2 then 1 else 0) := by
      intro x
      rw [length_update_cons, length_update_cons]
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range, he.1, he.2,
      ↓reduceIte, ih', List.length_append, List.length_singleton]
    ring

/-! ### The amortization -/

/-- The total length of the adjacency lists of the alive vertices below `N`. -/
def asum (N : ℕ) (s : State) : ℕ :=
  ∑ x ∈ Finset.range N, if s.dead x = true then 0 else (s.adj x).length

theorem length_elim_adj (s : State) (v u w y : ℕ) :
    ((elim s v u w).adj y).length ≤
      (s.adj y).length + (if y = u then 1 else 0) + (if y = w then 1 else 0) := by
  cases h : s.mat u w
  · simp only [elim, h, Bool.false_eq_true, ite_false, Function.update_apply]
    by_cases hyw : y = w
    · subst hyw
      by_cases hwu : y = u
      · subst hwu; simp
      · simp [hwu]
    · by_cases hyu : y = u
      · subst hyu; simp [hyw]
      · simp [hyw, hyu]
  · simp only [elim, h, ite_true, decDeg_adj]
    omega

theorem asum_elim {N : ℕ} (s : State) {v : ℕ} (u w : ℕ) (hv : v < N) (hd : s.dead v = false) :
    asum N (elim s v u w) + (s.adj v).length ≤ asum N s + 2 := by
  have hpt : ∀ x ∈ Finset.range N,
      (if (elim s v u w).dead x = true then 0 else ((elim s v u w).adj x).length) +
        (if x = v then (s.adj v).length else 0) ≤
      (if s.dead x = true then 0 else (s.adj x).length) + ((if x = u then 1 else 0) +
        (if x = w then 1 else 0)) := by
    intro x _
    have hl := length_elim_adj s v u w x
    rw [elim_dead]
    by_cases hx : x = v
    · subst hx; simp [hd]
    · simp only [Function.update_of_ne hx, hx, ↓reduceIte]
      split_ifs at hl ⊢ <;> omega
  have := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range, hv, ↓reduceIte] at this
  unfold asum
  have h1 : (if u < N then 1 else 0) ≤ 1 := by split <;> omega
  have h2 : (if w < N then 1 else 0) ≤ 1 := by split <;> omega
  omega

theorem asum_init_le {N : ℕ} {L : List Edge} (h : ∀ e ∈ L, e.1 < N ∧ e.2 < N) :
    asum N (init N L) ≤ 2 * L.length := by
  rw [← sum_initAdj h]
  unfold asum
  refine Finset.sum_le_sum fun x _ => ?_
  split
  · exact Nat.zero_le _
  · exact le_rfl

/-! ### Scans for the first alive entries -/

theorem getD_snoc (l : List ℕ) (a i : ℕ) :
    (l ++ [a]).getD i 0 = if i < l.length then l.getD i 0 else if i = l.length then a else 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp only [Option.getD_none]

theorem filter_take_succ (l : List ℕ) (p : ℕ → Bool) (j : ℕ) (hj : j < l.length) :
    (l.take (j + 1)).filter p = (l.take j).filter p ++ (if p l[j] then [l[j]] else []) := by
  rw [take_succ_eq l j hj, List.filter_append, List.filter_singleton]
  split <;> simp_all

/-! ### The reconstruction -/

theorem foldl_take_succ {α β : Type*} (f : β → α → β) (b : β) (l : List α) (i : ℕ) (hi : i < l.length) :
    (l.take (i + 1)).foldl f b = f ((l.take i).foldl f b) l[i] := by
  rw [take_succ_eq l i hi, List.foldl_append]
  rfl

theorem reinsert_lt {N : ℕ} {f : ℕ → ℕ} (hf : ∀ y, f y < N) {e : ℕ × ℕ × ℕ}
    (he : e.1 < N ∧ e.2.1 < N ∧ e.2.2 < N) : ∀ y, reinsert f e y < N := by
  intro y
  obtain ⟨v, u, w⟩ := e
  obtain ⟨hv, hu, hw⟩ := he
  simp only at hv hu hw
  simp only [reinsert]
  split_ifs <;> simp only [Function.update_apply] <;> split_ifs <;> first | exact hf y | omega

theorem foldl_reinsert_lt {N : ℕ} {f : ℕ → ℕ} (hf : ∀ y, f y < N) {l : List (ℕ × ℕ × ℕ)}
    (hl : ∀ e ∈ l, e.1 < N ∧ e.2.1 < N ∧ e.2.2 < N) : ∀ y, l.foldl reinsert f y < N := by
  induction l generalizing f with
  | nil => exact hf
  | cons e l ih =>
    exact ih (reinsert_lt hf (hl e (by simp))) fun e' he' => hl e' (by simp [he'])

@[simp] theorem length_walk (f : ℕ → ℕ) (n x : ℕ) : (walk f n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [walk, ih]

theorem walk_getElem (f : ℕ → ℕ) : ∀ (n x i : ℕ) (hi : i < (walk f n x).length),
    (walk f n x)[i] = f^[i] x
  | 0, _, _, hi => by simp at hi
  | n + 1, x, 0, _ => rfl
  | n + 1, x, i + 1, hi => by
    simp only [walk, List.getElem_cons_succ]
    rw [walk_getElem f n (f x) i (by simpa [walk] using hi), Function.iterate_succ_apply]

theorem iterate_lt {N : ℕ} {f : ℕ → ℕ} (hf : ∀ y, f y < N) {x : ℕ} (hx : x < N) :
    ∀ i, f^[i] x < N
  | 0 => hx
  | i + 1 => by rw [Function.iterate_succ_apply']; exact hf _

end STACS2027.RAM.EarR
