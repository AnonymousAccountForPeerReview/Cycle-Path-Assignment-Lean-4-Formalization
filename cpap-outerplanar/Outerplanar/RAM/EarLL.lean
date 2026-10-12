module

public import Outerplanar.RAM.Lib
public import Outerplanar.Algo.Ear
import Mathlib.Tactic

/-!
# Linked lists in memory; loops with a ghost-indexed invariant

General tools for the ear-elimination machine (`EarProg.lean`):

* `LL m V X n p l`: the list `l` is stored as a singly linked list starting at node `p`; node
  `q ≥ 1` holds its value at `V + q` and the next node at `X + q`, `0` is the empty list, all
  nodes are below `n` (allocated). Lists survive stores outside their nodes (`LL.congr`) and the
  allocation of more nodes (`LL.mono`).
* `AdjRep m H V X N n adj`: the lists `adj v` (`v < N`) with head pointers at `H + v`; prepending
  an entry is three stores (`AdjRep.prepend`), the stores elsewhere keep it
  (`AdjRep.upd_of_disjoint`).
* `HT.loopG`, `HT.whileG`: loops whose invariant is indexed by a ghost value `x` (an abstract
  state) with a potential `Φ x`: every round goes from `Inv x` to some `Inv y` and costs at most
  `Φ x - Φ y - 1` steps. `HT.toG` builds such a round from an ordinary triple; `HT.of_false`
  is the triple of an impossible case (the machine uses their twins `HTB.loopG`, `HTB.whileG`,
  `HTB.toG`, `HTB.of_false` of `BoundedLib.lean`).
-/

@[expose] public section

namespace STACS2027.RAM.EarR

/-! ### Linked lists -/

/-- The list `l` stored as a linked list from node `p` (values at `V + q`, next pointers at
`X + q`, `0` = end, all nodes in `[1, n)`). -/
def LL (m : ℕ → ℕ) (V X n : ℕ) : ℕ → List ℕ → Prop
  | p, [] => p = 0
  | p, x :: l => 0 < p ∧ p < n ∧ m (V + p) = x ∧ LL m V X n (m (X + p)) l

@[simp] theorem LL_nil {m : ℕ → ℕ} {V X n p : ℕ} : LL m V X n p [] ↔ p = 0 := Iff.rfl

theorem LL_cons {m : ℕ → ℕ} {V X n p x : ℕ} {l : List ℕ} :
    LL m V X n p (x :: l) ↔ 0 < p ∧ p < n ∧ m (V + p) = x ∧ LL m V X n (m (X + p)) l := Iff.rfl

theorem LL.congr {m m' : ℕ → ℕ} {V X n : ℕ}
    (hm : ∀ q, 0 < q → q < n → m' (V + q) = m (V + q) ∧ m' (X + q) = m (X + q)) :
    ∀ {p : ℕ} {l : List ℕ}, LL m V X n p l → LL m' V X n p l
  | _, [], h => h
  | p, _ :: _, ⟨h0, hn, hv, hl⟩ =>
    ⟨h0, hn, (hm p h0 hn).1.trans hv, by rw [(hm p h0 hn).2]; exact LL.congr hm hl⟩

theorem LL.mono {m : ℕ → ℕ} {V X n n' : ℕ} (hn : n ≤ n') :
    ∀ {p : ℕ} {l : List ℕ}, LL m V X n p l → LL m V X n' p l
  | _, [], h => h
  | _, _ :: _, ⟨h0, hp, hv, hl⟩ => ⟨h0, by omega, hv, LL.mono hn hl⟩

theorem LL.eq_zero_iff {m : ℕ → ℕ} {V X n p : ℕ} {l : List ℕ} (h : LL m V X n p l) :
    p = 0 ↔ l = [] := by
  cases l with
  | nil => simpa using h
  | cons x l => exact ⟨fun hp => absurd hp (by have := h.1; omega), fun h' => by simp at h'⟩

/-- Stores outside the nodes keep a list. -/
theorem LL.upd {m : ℕ → ℕ} {V X n p a v : ℕ} {l : List ℕ} (h : LL m V X n p l)
    (hV : a ≤ V ∨ V + n ≤ a) (hX : a ≤ X ∨ X + n ≤ a) : LL (RAM.upd m a v) V X n p l :=
  h.congr fun q hq hqn => ⟨upd_ne m v (by omega), upd_ne m v (by omega)⟩

/-! ### Adjacency lists -/

/-- The lists `adj v` (`v < N`), head pointers at `H + v`, nodes below `n`. -/
def AdjRep (m : ℕ → ℕ) (H V X N n : ℕ) (adj : ℕ → List ℕ) : Prop :=
  ∀ v, v < N → LL m V X n (m (H + v)) (adj v)

theorem AdjRep.upd_of_disjoint {m : ℕ → ℕ} {H V X N n a v : ℕ} {adj : ℕ → List ℕ}
    (h : AdjRep m H V X N n adj) (hH : a < H ∨ H + N ≤ a) (hV : a ≤ V ∨ V + n ≤ a)
    (hX : a ≤ X ∨ X + n ≤ a) : AdjRep (RAM.upd m a v) H V X N n adj := fun x hx => by
  rw [upd_ne m v (show H + x ≠ a by omega)]
  exact (h x hx).upd hV hX

theorem AdjRep.mono {m : ℕ → ℕ} {H V X N n n' : ℕ} {adj : ℕ → List ℕ} (h : AdjRep m H V X N n adj)
    (hn : n ≤ n') : AdjRep m H V X N n' adj := fun x hx => (h x hx).mono hn

/-- **Prepending** `y` to the list of `x`: the new node `n` gets the value `y` and the old head
of `x` as its successor, and becomes the head of `x`. -/
theorem AdjRep.prepend {m : ℕ → ℕ} {H V X N n : ℕ} {adj : ℕ → List ℕ} (h : AdjRep m H V X N n adj)
    {x y : ℕ} (hx : x < N) (hn : 0 < n) (hHV : H + N ≤ V) (hVX : V + n ≤ X) :
    AdjRep (RAM.upd (RAM.upd (RAM.upd m (V + n) y) (X + n) (m (H + x))) (H + x) n) H V X N (n + 1)
      (Function.update adj x (y :: adj x)) := by
  have hc : ∀ q, 0 < q → q < n →
      RAM.upd (RAM.upd (RAM.upd m (V + n) y) (X + n) (m (H + x))) (H + x) n (V + q) = m (V + q) ∧
      RAM.upd (RAM.upd (RAM.upd m (V + n) y) (X + n) (m (H + x))) (H + x) n (X + q) = m (X + q) := by
    intro q hq hqn
    simp only [upd_apply]
    constructor <;> split_ifs <;> first | rfl | omega
  intro v hv
  by_cases hvx : v = x
  · subst hvx
    rw [Function.update_self, upd_same]
    refine ⟨hn, by omega, ?_, ?_⟩
    · simp only [upd_apply]
      split_ifs <;> first | rfl | omega
    · have e : RAM.upd (RAM.upd (RAM.upd m (V + n) y) (X + n) (m (H + v))) (H + v) n (X + n) =
          m (H + v) := by
        simp only [upd_apply]
        split_ifs <;> first | rfl | omega
      rw [e]
      exact ((h v hv).congr hc).mono (by omega)
  · rw [Function.update_of_ne hvx]
    have e : RAM.upd (RAM.upd (RAM.upd m (V + n) y) (X + n) (m (H + x))) (H + x) n (H + v) =
        m (H + v) := by
      simp only [upd_apply]
      split_ifs <;> first | rfl | omega
    rw [e]
    exact ((h v hv).congr hc).mono (by omega)

/-! ### Loops with a ghost-indexed invariant -/

namespace HT

/-- An impossible case. -/
theorem of_false {s : Stmt} {P Q : Config → Prop} {b : ℕ} (h : ∀ c, P c → False) : HT s P Q b :=
  fun c hc => absurd (h c hc) id

/-- **Loop with a ghost-indexed invariant**: every round from `Inv x` (test register nonzero)
ends in some `Inv y` and costs at most `Φ x - Φ y - 1` steps. -/
theorem loopG {a : ℕ} {body : Stmt} {α : Type*} (Inv : α → Config → Prop) (Φ : α → ℕ)
    (hbody : ∀ x, HTt body (fun c => Inv x c ∧ c.reg a ≠ 0)
      (fun c' t => ∃ y, Inv y c' ∧ Φ y + t + 1 ≤ Φ x)) (x : α) :
    HT (.loop a body) (Inv x) (fun c => ∃ y, Inv y c ∧ c.reg a = 0) (Φ x + 1) := by
  suffices key : ∀ v x c, Φ x = v → Inv x c →
      ∃ c' t, Exec (.loop a body) c t c' ∧ (∃ y, Inv y c' ∧ c'.reg a = 0) ∧ t ≤ Φ x + 1 from
    fun c hc => key _ x c rfl hc
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro x c hv hc
  by_cases ha : c.reg a = 0
  · exact ⟨c, 1, Exec.loopDone ha, ⟨x, hc, ha⟩, by omega⟩
  · obtain ⟨c₁, t₁, he₁, y, hi₁, hΦ⟩ := hbody x c ⟨hc, ha⟩
    obtain ⟨c', t₂, he₂, hq, ht⟩ := ih (Φ y) (by omega) y c₁ rfl hi₁
    exact ⟨c', t₁ + t₂ + 1, Exec.loopNext ha he₁ he₂, hq, by omega⟩

/-- **`while` loop with a ghost-indexed invariant** (`Inv x` holds after every evaluation of
the test). -/
theorem whileG {cond body : Stmt} {α : Type*} {P : Config → Prop} (Inv : α → Config → Prop)
    (Φ : α → ℕ) (x₀ : α) {Tc : ℕ} (hinit : HT cond P (Inv x₀) Tc)
    (hstep : ∀ x, HTt (.seq body cond) (fun c => Inv x c ∧ c.reg rT ≠ 0)
      (fun c' t => ∃ y, Inv y c' ∧ Φ y + t + 1 ≤ Φ x)) :
    HT (whileC cond body) P (fun c => ∃ y, Inv y c ∧ c.reg rT = 0) (Tc + (Φ x₀ + 1)) :=
  hinit.seq (loopG Inv Φ hstep x₀)

/-- A round of a ghost-indexed loop from an ordinary triple. -/
theorem toG {s : Stmt} {P : Config → Prop} {α : Type*} {Inv : α → Config → Prop} {Φ : α → ℕ}
    {y : α} {b v : ℕ} (h : HT s P (Inv y) b) (hb : Φ y + b + 1 ≤ v) :
    HTt s P (fun c' t => ∃ y, Inv y c' ∧ Φ y + t + 1 ≤ v) := fun c hc => by
  obtain ⟨c', t, he, hq, ht⟩ := h c hc
  exact ⟨c', t, he, y, hq, by omega⟩

end HT

end STACS2027.RAM.EarR
