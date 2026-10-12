module

public import ApproximationHardness.Embed.DFSInv
import Lean.Elab.Tactic.Omega

/-!
# The search halts with a depth-first forest

Every step of the search before it halts decreases `mu` (`mu_step`), so after `10E + 1` steps the
search has halted (`halted_final`). The forest of the final state is then valid
(`valid_final`): every vertex is visited and finished, and every dart outside the forest joins an
ancestor and a descendant. Its `post` lists every vertex and every top node, each after all the
vertices below it (`post_final`).
-/

@[expose] public section

namespace STACS2027.Embed

open Complexity Complexity.Planar

theorem length_le_of_nodup_lt : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n
  | 0, l, _, h => by
    cases l with
    | nil => simp
    | cons a l => exact absurd (h a (by simp)) (by omega)
  | n + 1, l, hnd, h => by
    have h1 := length_le_of_nodup_lt n (l.erase n) (hnd.erase n) (fun x hx => by
      have := (hnd.mem_erase_iff).mp hx
      have := h x this.2
      omega)
    have h2 : l.length ≤ (l.erase n).length + 1 := by rw [List.length_erase]; split <;> omega
    omega

namespace DG

variable (G : DG)

/-- The measure of the search. -/
def mu (s : DS) : Nat :=
  (2 * G.E + 1 - s.r) + (2 * G.E - s.ex.length) + (2 * G.E - s.vl.length) + (4 * G.E - s.post.length)

variable {G}

theorem step_halted {s : DS} (h : G.Halted s) : G.step s = s := by
  rw [step, ite_eq_right (by rw [h.1]; simp), ite_eq_right (by have := h.2; omega)]

theorem iterate_halted {s : DS} (h : G.Halted s) : ∀ n, iterate G.step n s = s := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => show iterate G.step n (G.step s) = s; rw [step_halted h, ih]

section ok

variable (hG : G.Ok)
include hG

omit hG in
theorem bounds {s : DS} (hI : G.Inv s) :
    s.ex.length ≤ 2 * G.E ∧ s.vl.length ≤ 2 * G.E ∧ s.post.length ≤ 4 * G.E := by
  refine ⟨length_le_of_nodup_lt _ _ hI.ex_nd fun d hd => ?_, length_le_of_nodup_lt _ _ hI.vl_nd fun u hu => ?_,
    length_le_of_nodup_lt _ _ hI.post_nd fun x hx => ?_⟩
  · obtain ⟨u, hu, k, hk, rfl⟩ := (hI.ex_mem d).mp hd
    have := hI.ptr_le u
    exact (mem_darts.mp (getD_mem (by omega))).1
  · exact (hI.vert u ((hI.vl_mem u).mp hu)).1
  · rcases (hI.post_mem x).mp hx with ⟨h, _⟩ | ⟨h1, h2, _⟩
    · omega
    · have := (hI.vert (x - 2 * G.E) (by omega)).1; omega

/-- **The measure decreases** at every step before the search halts. -/
theorem mu_step {s : DS} (hI : G.Inv s) (hh : ¬ G.Halted s) : G.mu (G.step s) < G.mu s := by
  have hI' := inv_step hG hI
  obtain ⟨b1, b2, b3⟩ := bounds hI'
  unfold mu
  by_cases hi : s.inner = true
  · by_cases hp : s.ptr s.cur < (G.darts s.cur).length
    · by_cases hw : s.st (G.nw s) = 0
      · have e : G.step s = { s with
            ptr := upd s.ptr s.cur (s.ptr s.cur + 1)
            ex := s.ex ++ [G.nd s]
            st := upd s.st (G.nw s) 1
            par := upd s.par (G.nw s) (pair (G.nd s))
            depth := upd s.depth (G.nw s) (s.depth s.cur + 1)
            H := max s.H (s.depth s.cur + 2)
            cur := G.nw s
            vl := s.vl ++ [G.nw s] } := by rw [step, ite_eq_left hi, ite_eq_left hp, ite_eq_left hw]
        rw [e] at b1 b2 b3 ⊢
        simp only [List.length_append, List.length_singleton] at b1 b2 b3 ⊢
        omega
      · have e : G.step s = { s with
            ptr := upd s.ptr s.cur (s.ptr s.cur + 1)
            ex := s.ex ++ [G.nd s] } := by rw [step, ite_eq_left hi, ite_eq_left hp, ite_eq_right hw]
        rw [e] at b1 b2 b3 ⊢
        simp only [List.length_append, List.length_singleton] at b1 b2 b3 ⊢
        omega
    · by_cases hr : 2 * G.E ≤ s.par s.cur
      · have e : G.step s = { s with
            st := upd s.st s.cur 2
            post := s.post ++ [s.cur, 2 * G.E + s.cur]
            inner := false
            r := s.r + 1 } := by rw [step, ite_eq_left hi, ite_eq_right hp, ite_eq_left hr]
        have := (hI.scanR hi).1
        rw [e] at b1 b2 b3 ⊢
        simp only [List.length_append, List.length_cons, List.length_nil] at b1 b2 b3 ⊢
        omega
      · have e : G.step s = { s with
            st := upd s.st s.cur 2
            post := s.post ++ [s.cur]
            cur := G.rep (pair (s.par s.cur)) } := by rw [step, ite_eq_left hi, ite_eq_right hp, ite_eq_right hr]
        rw [e] at b1 b2 b3 ⊢
        simp only [List.length_append, List.length_singleton] at b1 b2 b3 ⊢
        omega
  · have hi' : s.inner = false := by simpa using hi
    have hr : s.r < 2 * G.E := by
      apply Classical.byContradiction; intro h; exact hh ⟨hi', by omega⟩
    by_cases hv : G.rep s.r = s.r ∧ s.st s.r = 0
    · have e : G.step s = { s with
          st := upd s.st s.r 1
          par := upd s.par s.r (2 * G.E)
          depth := upd s.depth s.r 0
          cur := s.r
          inner := true
          vl := s.vl ++ [s.r]
          H := max s.H 1 } := by rw [step, ite_eq_right hi, ite_eq_left hr, ite_eq_left hv]
      rw [e] at b1 b2 b3 ⊢
      simp only [List.length_append, List.length_singleton] at b1 b2 b3 ⊢
      omega
    · have e : G.step s = { s with r := s.r + 1 } := by rw [step, ite_eq_right hi, ite_eq_left hr, ite_eq_right hv]
      rw [e]
      simp only
      omega

theorem halted_of_mu : ∀ n s, G.Inv s → G.mu s ≤ n → G.Halted (iterate G.step n s) := by
  intro n
  induction n with
  | zero =>
    intro s hI hmu
    show G.Halted s
    unfold mu at hmu
    have hr : 2 * G.E + 1 ≤ s.r := by omega
    refine ⟨?_, by omega⟩
    cases h : s.inner
    · rfl
    · have := (hI.scanR h).1; omega
  | succ n ih =>
    intro s hI hmu
    by_cases hh : G.Halted s
    · rw [iterate_halted hh]; exact hh
    · show G.Halted (iterate G.step n (G.step s))
      exact ih _ (inv_step hG hI) (by have := mu_step hG hI hh; omega)

/-- The final state of the search. -/
def final (G : DG) : DS := iterate G.step (10 * G.E + 1) DG.init

omit hG in
theorem mu_init : G.mu DG.init ≤ 10 * G.E + 1 := by
  simp [mu, init]; omega

theorem halted_final : G.Halted G.final :=
  halted_of_mu hG _ _ inv_init mu_init

theorem inv_final : G.Inv G.final := inv_iterate hG _

/-- After the search, every vertex is finished. -/
theorem final_fin {u : Nat} (hu : u < 2 * G.E) (hr : G.rep u = u) : G.final.st u = 2 := by
  have hI := inv_final hG
  have hh := halted_final hG
  have h1 := hI.scan u (by have := hh.2; omega) hu hr
  have h2 := hI.closed hh.1 u
  have h3 := hI.st_le u
  omega

/-- **The search finds a depth-first forest.** -/
theorem valid_final : (G.fd G.final).Valid := by
  have hI := inv_final hG
  have hfin : ∀ u, u < 2 * G.E → G.rep u = u → G.final.st u ≠ 0 := fun u hu hr => by
    have := final_fin hG hu hr; omega
  refine ⟨hG.rep_lt, hG.rep_rep, hG.rep_le, hG.noloop, hG.deg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r _ hroot
    show G.final.par r < 2 * G.E
    have : ¬ 2 * G.E ≤ G.final.par r := hroot
    omega
  · intro r hr hroot
    exact hI.parv r (hfin r hr.1 hr.2) (by have : ¬ 2 * G.E ≤ G.final.par r := hroot; omega)
  · intro r hr hroot
    exact ((hI.tree r (hfin r hr.1 hr.2)).2 hroot).2
  · intro r hr hroot
    exact (hI.tree r (hfin r hr.1 hr.2)).1 hroot
  · intro r hr
    exact hI.hbound r (hfin r hr.1 hr.2)
  · intro d hd hnt
    have hu := hG.rep_lt d hd
    have hur := hG.rep_rep d hd
    have h2 := final_fin hG hu hur
    have hlen := hI.ptr2 _ h2
    obtain ⟨k, hk, hke⟩ := exists_getD (mem_darts.mpr ⟨hd, rfl⟩ : d ∈ G.darts (G.rep d))
    rcases hI.back (G.rep d) (by omega) k (by omega) with h | h | h
    · rw [hke] at h; exact absurd h hnt
    · rw [hke] at h; exact Or.inl h
    · rw [hke] at h; exact Or.inr h

/-- **The order of the search**: `post` lists every vertex and every top node once, each after the
vertices below it. -/
theorem post_final :
    G.final.post.Nodup ∧
    (∀ x, x ∈ G.final.post ↔ (x < 2 * G.E ∧ G.rep x = x) ∨
      (2 * G.E ≤ x ∧ x - 2 * G.E < 2 * G.E ∧ G.rep (x - 2 * G.E) = x - 2 * G.E ∧
        (G.fd G.final).IsRoot (x - 2 * G.E))) ∧
    (∀ u c, u < 2 * G.E → G.rep u = u → (G.fd G.final).Desc u c → c < 2 * G.E → G.rep c = c → c ≠ u →
      Before G.final.post c u) ∧
    (∀ u c, u < 2 * G.E → G.rep u = u → (G.fd G.final).IsRoot u → (G.fd G.final).Desc u c →
      c < 2 * G.E → G.rep c = c → Before G.final.post c (2 * G.E + u)) := by
  have hI := inv_final hG
  refine ⟨hI.post_nd, fun x => ?_, fun u c hu hur hd hc hcr hne => ?_, fun u c hu hur hroot hd hc hcr => ?_⟩
  · rw [hI.post_mem]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
      · exact Or.inl ⟨h1, (hI.vert x (by omega)).2⟩
      · obtain ⟨h4, h5⟩ := hI.vert (x - 2 * G.E) (by omega)
        exact Or.inr ⟨h1, h4, h5, h3⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩)
      · exact Or.inl ⟨h1, final_fin hG h1 h2⟩
      · exact Or.inr ⟨h1, final_fin hG h2 h3, h4⟩
  · have hup : u ∈ G.final.post := (hI.post_mem u).mpr (Or.inl ⟨hu, final_fin hG hu hur⟩)
    exact hI.post_desc u c hup hu (by have := final_fin hG hc hcr; omega) hd hne
  · have hup : 2 * G.E + u ∈ G.final.post := (hI.post_mem _).mpr (Or.inr ⟨by omega,
      by rw [show 2 * G.E + u - 2 * G.E = u by omega]; exact final_fin hG hu hur,
      by rw [show 2 * G.E + u - 2 * G.E = u by omega]; exact hroot⟩)
    exact hI.post_top u c hup (by have := final_fin hG hc hcr; omega) hd

end ok

end DG

end STACS2027.Embed
