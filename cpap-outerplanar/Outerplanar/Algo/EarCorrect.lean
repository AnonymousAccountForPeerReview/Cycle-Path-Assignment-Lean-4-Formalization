module

public import Outerplanar.Algo.EarInv
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Ear elimination finds an outerplanar Hamiltonian cycle

`earHam_correct`: on the vertices `0, …, N - 1` and an edge list `L` (each edge once,
smaller end first) with an outerplanar Hamiltonian cycle `ham0`, `earHam N L` is an
outerplanar Hamiltonian cycle of `L`.

* The initial state satisfies the invariant of `Outerplanar/Algo/EarInv.lean` with the ghost
  `ham0` (`inv_init`): its matrix and its adjacency lists are those of `L`.
* After the loop (which has stopped, `loop_stopped`, while the stack is never empty) exactly
  three vertices `x < y < z` are alive, so the successor function `x → y → z → x` follows
  the final ghost; by the invariant, after the reinsertions it follows `ham0` in one of the
  two directions (`rep_three`, `Inv.log`).
* Following it from `x` reads off a rotation of `ham0` or of its reversal
  (`outerplanarHam_walk`), an outerplanar Hamiltonian cycle (`OuterplanarHam.rotate`,
  `OuterplanarHam.reverse`).
-/

@[expose] public section

namespace STACS2027.Ear

/-! ### The initial state -/

/-- The entry contributed by an edge to the adjacency list of `a`. -/
def adjEntry (a : ℕ) (e : Edge) : Option ℕ :=
  if e.1 = a then some e.2 else if e.2 = a then some e.1 else none

theorem adjEntry_eq_some {a x : ℕ} {e : Edge} (he : e.1 < e.2) :
    adjEntry a e = some x ↔ e = (a, x) ∨ e = (x, a) := by
  obtain ⟨p, q⟩ := e
  simp only at he
  simp only [adjEntry, Prod.mk.injEq]
  split_ifs with h1 h2
  · subst h1
    simp only [Option.some.injEq, true_and]
    constructor
    · exact Or.inl
    · rintro (h | ⟨rfl, rfl⟩)
      · exact h
      · omega
  · subst h2
    simp only [Option.some.injEq, and_true]
    constructor
    · exact Or.inr
    · rintro (⟨rfl, -⟩ | h)
      · exact absurd rfl h1
      · exact h
  · simp only [false_iff, not_or, not_and]
    exact ⟨fun h => absurd h h1, fun _ h => h2 h⟩

theorem initAdj_foldl (L : List Edge) (hL : ∀ e ∈ L, e.1 < e.2) (a : ℕ) :
    ∀ f : ℕ → List ℕ, (L.foldl (fun (f : ℕ → List ℕ) (e : Edge) =>
      let f1 := Function.update f e.1 (e.2 :: f e.1)
      Function.update f1 e.2 (e.1 :: f1 e.2)) f) a =
        (L.filterMap (adjEntry a)).reverse ++ f a := by
  induction L with
  | nil => intro f; rfl
  | cons e L ih =>
    intro f
    rw [List.foldl_cons, ih (fun e he => hL e (List.mem_cons_of_mem _ he))]
    have he : e.1 < e.2 := hL e (List.mem_cons_self ..)
    have hne : e.2 ≠ e.1 := by omega
    rw [List.filterMap_cons]
    simp only [adjEntry]
    by_cases h2 : e.2 = a
    · subst h2
      have h1 : e.1 ≠ e.2 := by omega
      simp only [h1, ite_false, ite_true]
      rw [Function.update_self, Function.update_of_ne hne]
      simp
    · by_cases h1 : e.1 = a
      · subst h1
        simp only [ite_true]
        rw [Function.update_of_ne (Ne.symm h2), Function.update_self]
        simp
      · simp only [h1, h2, ite_false]
        rw [Function.update_of_ne (Ne.symm h2), Function.update_of_ne (Ne.symm h1)]

theorem initAdj_eq (L : List Edge) (hL : ∀ e ∈ L, e.1 < e.2) (a : ℕ) :
    initAdj L a = (L.filterMap (adjEntry a)).reverse := by
  rw [initAdj, initAdj_foldl L hL a]
  simp

theorem mem_initAdj {L : List Edge} (hL : ∀ e ∈ L, e.1 < e.2) {a x : ℕ} :
    x ∈ initAdj L a ↔ (a, x) ∈ L ∨ (x, a) ∈ L := by
  rw [initAdj_eq L hL, List.mem_reverse, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hs⟩
    rcases (adjEntry_eq_some (hL e he)).mp hs with rfl | rfl
    · exact Or.inl he
    · exact Or.inr he
  · rintro (h | h)
    · exact ⟨_, h, (adjEntry_eq_some (hL _ h)).mpr (Or.inl rfl)⟩
    · exact ⟨_, h, (adjEntry_eq_some (hL _ h)).mpr (Or.inr rfl)⟩

theorem nodup_filterMap_adjEntry (a : ℕ) :
    ∀ L : List Edge, (∀ e ∈ L, e.1 < e.2) → L.Nodup → (L.filterMap (adjEntry a)).Nodup
  | [], _, _ => List.nodup_nil
  | e :: L, hL, hnd => by
    have hL' : ∀ e ∈ L, e.1 < e.2 := fun e he => hL e (List.mem_cons_of_mem _ he)
    have hnd' := (List.nodup_cons.mp hnd)
    have ih := nodup_filterMap_adjEntry a L hL' hnd'.2
    rw [List.filterMap_cons]
    cases hx : adjEntry a e with
    | none => exact ih
    | some x =>
      refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih⟩
      obtain ⟨e', he', hs⟩ := List.mem_filterMap.mp hmem
      have h1 := (adjEntry_eq_some (hL e (List.mem_cons_self ..))).mp hx
      have h2 := (adjEntry_eq_some (hL' e' he')).mp hs
      have hlt := hL e (List.mem_cons_self ..)
      have hlt' := hL' e' he'
      apply hnd'.1
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact he'
      · simp only at hlt hlt'; omega
      · simp only at hlt hlt'; omega
      · exact he'

theorem nodup_initAdj {L : List Edge} (hL : ∀ e ∈ L, e.1 < e.2) (hnd : L.Nodup) (a : ℕ) :
    (initAdj L a).Nodup := by
  rw [initAdj_eq L hL]
  exact List.nodup_reverse.mpr (nodup_filterMap_adjEntry a L hL hnd)

theorem foldl_mat (L : List Edge) (a b : ℕ) :
    ∀ m : ℕ → ℕ → Bool,
      (L.foldl (fun m e => update2 (update2 m e.1 e.2 true) e.2 e.1 true) m) a b = true ↔
        m a b = true ∨ (a, b) ∈ L ∨ (b, a) ∈ L := by
  induction L with
  | nil => intro m; simp
  | cons e L ih =>
    intro m
    rw [List.foldl_cons, ih]
    obtain ⟨p, q⟩ := e
    simp only [update2, List.mem_cons, Prod.mk.injEq]
    split_ifs <;> simp_all
    tauto

theorem adj_iff_mem {L : List Edge} (hL : ∀ e ∈ L, e.1 < e.2) {a b : ℕ} :
    Adj L a b ↔ (a, b) ∈ L ∨ (b, a) ∈ L := by
  constructor
  · rintro ⟨hab, he⟩
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · left
      rwa [show edge a b = (a, b) by simp [edge, Nat.min_eq_left h.le, Nat.max_eq_right h.le]]
        at he
    · right
      rwa [show edge a b = (b, a) by simp [edge, Nat.min_eq_right h.le, Nat.max_eq_left h.le]]
        at he
  · rintro (h | h)
    · have hlt := hL _ h
      simp only at hlt
      refine ⟨by omega, ?_⟩
      rwa [show edge a b = (a, b) by simp [edge, Nat.min_eq_left hlt.le, Nat.max_eq_right hlt.le]]
    · have hlt := hL _ h
      simp only at hlt
      refine ⟨by omega, ?_⟩
      rwa [show edge a b = (b, a) by simp [edge, Nat.min_eq_right hlt.le, Nat.max_eq_left hlt.le]]

theorem init_mat {N : ℕ} {L : List Edge} (hL : ∀ e ∈ L, e.1 < e.2) (a b : ℕ) :
    (init N L).mat a b = true ↔ Adj L a b := by
  rw [adj_iff_mem hL]
  simp only [init]
  rw [foldl_mat]
  simp

theorem nbrs_init (N : ℕ) (L : List Edge) (a : ℕ) : nbrs (init N L) a = initAdj L a := by
  simp [nbrs, init]

/-- **The invariant holds initially**, with the ghost `ham0`. -/
theorem inv_init {N : ℕ} {L : List Edge} (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N)
    (hnd : L.Nodup) {ham0 : List ℕ} (h0 : OuterplanarHam L ham0)
    (hv : ∀ v, v < N → v ∈ ham0) : Inv N ham0 (init N L) ham0 := by
  have hL1 : ∀ e ∈ L, e.1 < e.2 := fun e he => (hL e he).1
  have hmat := init_mat (N := N) hL1
  have hadjN : ∀ a b, Adj L a b → a < N ∧ b < N := by
    intro a b hab
    rcases (adj_iff_mem hL1).mp hab with h | h
    · have := hL _ h; simp only at this; omega
    · have := hL _ h; simp only at this; omega
  have hO := h0.oham
  have hmem : ∀ a, a ∈ ham0 ↔ a < N := by
    intro a
    refine ⟨fun ha => ?_, hv a⟩
    obtain ⟨C, -, hC⟩ := hO.rotate_to (fun _ _ h => h.symm) ha
    exact (hadjN _ _ hC.ends.1).1
  have hlen : ham0.length = N := by
    have hp : ham0.Perm (List.range N) :=
      (List.perm_ext_iff_of_nodup hO.2.1 List.nodup_range).mpr fun a => by
        rw [hmem, List.mem_range]
    rw [hp.length_eq, List.length_range]
  refine
    { mem := ?_, cnt := ?_, symm := ?_, irrefl := ?_, ham := ?_, nodup := ?_,
      nbrs_iff := ?_, deg := ?_, stack := ?_, stack_lt := ?_, log := ?_ }
  · intro a
    rw [hmem]
    simp [init]
  · rw [hlen]; rfl
  · intro a b
    apply Bool.eq_iff_iff.mpr
    rw [hmat, hmat]
    exact ⟨Adj.symm, Adj.symm⟩
  · intro a
    cases h : (init N L).mat a a
    · rfl
    · exact absurd rfl ((hmat a a).mp h).1
  · exact hO.congr fun a _ b _ _ => (hmat a b).symm
  · intro a _
    rw [nbrs_init]
    exact nodup_initAdj hL1 hnd a
  · intro a _ x
    rw [nbrs_init, mem_initAdj hL1, hmat, adj_iff_mem hL1, hmem]
    constructor
    · intro h
      exact ⟨(hadjN _ _ ((adj_iff_mem hL1).mpr h)).2, h⟩
    · exact fun h => h.2
  · intro a _
    rw [nbrs_init]
    rfl
  · intro a ha hd
    simp only [init, List.mem_reverse, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨(hmem a).mp ha, hd⟩
  · intro a ha
    simp only [init, List.mem_reverse, List.mem_filter, List.mem_range] at ha
    exact ha.1
  · intro succ h
    exact h

/-! ### Reconstruction -/

theorem getD_rotate_idxOf {K : List ℕ} {x : ℕ} (hx : x ∈ K) :
    (K.rotate (K.idxOf x)).getD 0 0 = x := by
  have hi : K.idxOf x < K.length := List.idxOf_lt_length_iff.mpr hx
  have hl : 0 < (K.rotate (K.idxOf x)).length := by rw [List.length_rotate]; omega
  rw [List.getD_eq_getElem _ _ hl, List.getElem_rotate]
  simp only [Nat.zero_add, Nat.mod_eq_of_lt hi]
  exact List.getElem_idxOf hi

/-- Following a successor function that follows an outerplanar Hamiltonian cycle `K`
(in one of the two directions), from any vertex of `K`, gives an outerplanar Hamiltonian
cycle. -/
theorem outerplanarHam_walk {g : Graph} {K : List ℕ} {succ : ℕ → ℕ} (hK : OuterplanarHam g K)
    (h : Rep succ K) {x : ℕ} (hx : x ∈ K) : OuterplanarHam g (walk succ K.length x) := by
  rcases h with h | h
  · have hf : Fwd succ (K.rotate (K.idxOf x)) := h.isRotated ⟨_, rfl⟩
    have hw := walk_fwd_length hf
    rw [getD_rotate_idxOf hx, List.length_rotate] at hw
    rw [hw]
    exact hK.rotate _
  · have hx' : x ∈ K.reverse := List.mem_reverse.mpr hx
    have hf : Fwd succ (K.reverse.rotate (K.reverse.idxOf x)) := h.isRotated ⟨_, rfl⟩
    have hw := walk_fwd_length hf
    rw [getD_rotate_idxOf hx', List.length_rotate, List.length_reverse] at hw
    rw [hw]
    exact hK.reverse.rotate _

/-- The reconstruction phase of `earHam` on the final state `s`. -/
def recon (N : ℕ) (s : State) : List ℕ :=
  let tri := (List.range N).filter fun v => s.dead v = false
  let x := tri.getD 0 0
  let y := tri.getD 1 0
  let z := tri.getD 2 0
  let succ0 : ℕ → ℕ :=
    Function.update (Function.update (Function.update (fun _ => 0) x y) y z) z x
  walk (s.log.foldl reinsert succ0) N x

theorem earHam_eq_recon (N : ℕ) (L : List Edge) :
    earHam N L = recon N (loop (4 * N + 1) (init N L)) := rfl

theorem recon_correct {N : ℕ} {L : List Edge} {ham0 : List ℕ} (h0 : OuterplanarHam L ham0)
    (hlen : ham0.length = N) (hv : ∀ v, v < N → v ∈ ham0) {s : State} {H : List ℕ}
    (hI : Inv N ham0 s H)
    (hstop : ¬ (s.stack ≠ [] ∧ 3 < s.cnt)) : OuterplanarHam L (recon N s) := by
  have h3 : H.length = 3 := by
    have := hI.ham.1
    have := hI.cnt
    have := hI.stack_ne_nil
    simp only [not_and, not_lt] at hstop
    have := hstop hI.stack_ne_nil
    omega
  have htnd : ((List.range N).filter fun v => s.dead v = false).Nodup :=
    List.nodup_range.filter _
  have htmem : ∀ a, a ∈ (List.range N).filter (fun v => s.dead v = false) ↔ a ∈ H := by
    intro a
    rw [hI.mem]
    simp
  have hp : ((List.range N).filter fun v => s.dead v = false).Perm H :=
    (List.perm_ext_iff_of_nodup htnd hI.ham.2.1).mpr htmem
  have htlen := hp.length_eq
  rw [h3] at htlen
  unfold recon
  dsimp only
  generalize hT : (List.range N).filter (fun v => s.dead v = false) = T at htnd htmem htlen
  match T, htlen with
  | [x, y, z], _ =>
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    have hxy : x ≠ y := by rintro rfl; simp at htnd
    have hxz : x ≠ z := by rintro rfl; simp at htnd
    have hyz : y ≠ z := by rintro rfl; simp at htnd
    have hrep := hI.log _ (rep_three hxy hxz hyz hI.ham.2.1 h3 fun a => by
      rw [← htmem]; simp)
    have hxH : x ∈ H := (htmem x).mp (by simp)
    have hx0 : x ∈ ham0 := hv x ((hI.mem x).mp hxH).1
    rw [← hlen]
    exact outerplanarHam_walk h0 hrep hx0

/-! ### Correctness -/

/-- **Ear elimination finds an outerplanar Hamiltonian cycle.** -/
theorem earHam_correct {N : ℕ} {L : List Edge} (hL : ∀ e ∈ L, e.1 < e.2 ∧ e.2 < N)
    (hnd : L.Nodup) (hN : 3 ≤ N) {ham0 : List ℕ} (h0 : OuterplanarHam L ham0)
    (hv : ∀ v, v < N → v ∈ ham0) : OuterplanarHam L (earHam N L) := by
  -- `3 ≤ N` follows from the other hypotheses
  have _ := hN
  have hI0 := inv_init hL hnd h0 hv
  obtain ⟨H, hI⟩ := hI0.loop (4 * N + 1)
  rw [earHam_eq_recon]
  exact recon_correct h0 hI0.cnt.symm hv hI (loop_stopped N L)

end STACS2027.Ear
