module

public import Outerplanar.Polygon
public import Mathlib.Data.List.Rotate
import Outerplanar.Transfer
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Outerplanar Hamiltonian cycles under rotation and reversal

`OuterplanarHam g ham` depends only on the cyclic order of `ham` up to orientation. To
prove it, and to reason about Hamiltonian cycles of relations other than the adjacency of
an edge list (the current graphs of the ear elimination), the conditions are stated for an
arbitrary relation `A` on the entries of a list `K`:

* `CycAdj A K`: cyclically consecutive entries are related;
* `NoCross A K`: no two related pairs of entries cross with respect to the positions on `K`;
* `OHam A K`: `K` has at least three entries, no repetitions, and both properties.

Both properties are invariant under rotation (`CycAdj.isRotated`, `NoCross.isRotated`) and,
for a symmetric relation, reversal (`CycAdj.reverse`, `NoCross.reverse`). For the adjacency
`Adj g` of an edge list, `OHam` together with the vertex condition is exactly
`OuterplanarHam` (`OuterplanarHam.oham`, `OHam.outerplanarHam`); hence
`OuterplanarHam.isRotated` and `OuterplanarHam.reverse`.

For the ear elimination: any vertex can be rotated to the front (`OHam.rotate_to`), its two
neighbours on the cycle are related to it (`OHam.ends`), and deleting it while relating its
two neighbours keeps a cycle without crossings (`OHam.drop_head`: the new pair joins two
consecutive vertices and crosses nothing).
-/

@[expose] public section

namespace STACS2027

/-- Cyclically consecutive entries of `K` are related by `A`. -/
def CycAdj (A : ℕ → ℕ → Prop) (K : List ℕ) : Prop :=
  (∀ j, j + 1 < K.length → A (K.getD j 0) (K.getD (j + 1) 0)) ∧
    A (K.getD (K.length - 1) 0) (K.getD 0 0)

/-- No two `A`-related pairs of entries of `K` cross with respect to the positions on `K`. -/
def NoCross (A : ℕ → ℕ → Prop) (K : List ℕ) : Prop :=
  ∀ i j k l, i < j → j < k → k < l → l < K.length →
    ¬ (A (K.getD i 0) (K.getD k 0) ∧ A (K.getD j 0) (K.getD l 0))

/-- `K` is a Hamiltonian cycle of the relation `A` on its entries with respect to whose
cyclic order no two related pairs cross. -/
def OHam (A : ℕ → ℕ → Prop) (K : List ℕ) : Prop :=
  3 ≤ K.length ∧ K.Nodup ∧ CycAdj A K ∧ NoCross A K

theorem getD_snoc_of_lt {T : List ℕ} {a j : ℕ} (h : j < T.length) :
    (T ++ [a]).getD j 0 = T.getD j 0 :=
  List.getD_append _ _ _ _ h

theorem getD_snoc_length (T : List ℕ) (a : ℕ) : (T ++ [a]).getD T.length 0 = a := by
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem getD_mem_of_lt {K : List ℕ} {i : ℕ} (h : i < K.length) : K.getD i 0 ∈ K := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem getD_ne_of_ne {K : List ℕ} (hK : K.Nodup) {i j : ℕ} (hi : i < K.length)
    (hj : j < K.length) (hij : i ≠ j) : K.getD i 0 ≠ K.getD j 0 := fun h =>
  hij ((hK.getD_inj hi hj).mp h)

section

variable {A : ℕ → ℕ → Prop}

/-! ### Rotation -/

theorem CycAdj.rotate_one {a : ℕ} {T : List ℕ} (h : CycAdj A (a :: T)) :
    CycAdj A (T ++ [a]) := by
  obtain ⟨h1, h2⟩ := h
  simp only [List.length_cons, Nat.add_sub_cancel, List.getD_cons_zero] at h2
  refine ⟨fun j hj => ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton] at hj
    rw [getD_snoc_of_lt (by omega)]
    rcases Nat.lt_or_ge (j + 1) T.length with hj' | hj'
    · rw [getD_snoc_of_lt hj']
      have := h1 (j + 1) (by simp; omega)
      simpa using this
    · have hj2 : j + 1 = T.length := by omega
      rw [hj2, getD_snoc_length]
      rw [← hj2, List.getD_cons_succ] at h2
      exact h2
  · simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    rw [getD_snoc_length]
    cases T with
    | nil => simpa using h2
    | cons b T =>
      have := h1 0 (by simp)
      simpa using this

theorem CycAdj.rotate {K : List ℕ} (h : CycAdj A K) (n : ℕ) : CycAdj A (K.rotate n) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [← List.rotate_rotate]
    generalize K.rotate n = K' at ih ⊢
    cases K' with
    | nil => simpa using ih
    | cons a T =>
      rw [List.rotate_cons_succ, List.rotate_zero]
      exact ih.rotate_one

theorem CycAdj.isRotated {K K' : List ℕ} (h : CycAdj A K) (hr : K ~r K') : CycAdj A K' := by
  obtain ⟨n, rfl⟩ := hr
  exact h.rotate n

theorem NoCross.rotate_one (hA : ∀ a b, A a b → A b a) {a : ℕ} {T : List ℕ}
    (h : NoCross A (a :: T)) : NoCross A (T ++ [a]) := by
  intro i j k l hij hjk hkl hl ⟨h1, h2⟩
  simp only [List.length_append, List.length_singleton] at hl
  rw [getD_snoc_of_lt (by omega), getD_snoc_of_lt (by omega)] at h1
  rw [getD_snoc_of_lt (by omega)] at h2
  rcases Nat.lt_or_ge l T.length with hl' | hl'
  · rw [getD_snoc_of_lt hl'] at h2
    apply h (i + 1) (j + 1) (k + 1) (l + 1) (by omega) (by omega) (by omega) (by simp; omega)
    simp only [List.getD_cons_succ]
    exact ⟨h1, h2⟩
  · have hlT : l = T.length := by omega
    subst hlT
    rw [getD_snoc_length] at h2
    apply h 0 (i + 1) (j + 1) (k + 1) (by omega) (by omega) (by omega) (by simp; omega)
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨hA _ _ h2, h1⟩

theorem NoCross.rotate (hA : ∀ a b, A a b → A b a) {K : List ℕ} (h : NoCross A K) (n : ℕ) :
    NoCross A (K.rotate n) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [← List.rotate_rotate]
    generalize K.rotate n = K' at ih ⊢
    cases K' with
    | nil => simpa using ih
    | cons a T =>
      rw [List.rotate_cons_succ, List.rotate_zero]
      exact ih.rotate_one hA

theorem NoCross.isRotated (hA : ∀ a b, A a b → A b a) {K K' : List ℕ} (h : NoCross A K)
    (hr : K ~r K') : NoCross A K' := by
  obtain ⟨n, rfl⟩ := hr
  exact h.rotate hA n

/-! ### Reversal -/

theorem CycAdj.reverse (hA : ∀ a b, A a b → A b a) {K : List ℕ} (h : CycAdj A K) :
    CycAdj A K.reverse := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [List.length_reverse] at hj
    rw [List.getD_reverse _ (by omega), List.getD_reverse _ (by omega)]
    have := h1 (K.length - 1 - (j + 1)) (by omega)
    rw [show K.length - 1 - (j + 1) + 1 = K.length - 1 - j by omega] at this
    exact hA _ _ this
  · rcases Nat.eq_zero_or_pos K.length with h0 | h0
    · rw [List.length_eq_zero_iff.mp h0] at h2 ⊢
      exact h2
    · rw [List.length_reverse, List.getD_reverse _ (by omega), List.getD_reverse _ h0]
      rw [show K.length - 1 - (K.length - 1) = 0 by omega, Nat.sub_zero]
      exact hA _ _ h2

theorem NoCross.reverse (hA : ∀ a b, A a b → A b a) {K : List ℕ} (h : NoCross A K) :
    NoCross A K.reverse := by
  intro i j k l hij hjk hkl hl ⟨h1, h2⟩
  rw [List.length_reverse] at hl
  rw [List.getD_reverse _ (by omega), List.getD_reverse _ (by omega)] at h1 h2
  exact h (K.length - 1 - l) (K.length - 1 - k) (K.length - 1 - j) (K.length - 1 - i)
    (by omega) (by omega) (by omega) (by omega) ⟨hA _ _ h2, hA _ _ h1⟩

/-! ### `OHam` -/

theorem OHam.isRotated (hA : ∀ a b, A a b → A b a) {K K' : List ℕ} (h : OHam A K)
    (hr : K ~r K') : OHam A K' :=
  ⟨hr.perm.length_eq ▸ h.1, hr.nodup_iff.mp h.2.1, h.2.2.1.isRotated hr,
    h.2.2.2.isRotated hA hr⟩

theorem OHam.reverse (hA : ∀ a b, A a b → A b a) {K : List ℕ} (h : OHam A K) :
    OHam A K.reverse :=
  ⟨by rw [List.length_reverse]; exact h.1, List.nodup_reverse.mpr h.2.1, h.2.2.1.reverse hA,
    h.2.2.2.reverse hA⟩

/-- `OHam` depends only on the relation between distinct entries. -/
theorem OHam.congr {B : ℕ → ℕ → Prop} {K : List ℕ} (h : OHam A K)
    (hAB : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → (A a b ↔ B a b)) : OHam B K := by
  obtain ⟨h3, hnd, ⟨h1, h2⟩, hx⟩ := h
  have key : ∀ i j, i < K.length → j < K.length → i ≠ j →
      (A (K.getD i 0) (K.getD j 0) ↔ B (K.getD i 0) (K.getD j 0)) := fun i j hi hj hij =>
    hAB _ (getD_mem_of_lt hi) _ (getD_mem_of_lt hj) (getD_ne_of_ne hnd hi hj hij)
  refine ⟨h3, hnd, ⟨fun j hj => (key j (j + 1) (by omega) hj (by omega)).mp (h1 j hj), ?_⟩, ?_⟩
  · exact (key _ _ (by omega) (by omega) (by omega)).mp h2
  · intro i j k l hij hjk hkl hl ⟨hb1, hb2⟩
    exact hx i j k l hij hjk hkl hl ⟨(key i k (by omega) (by omega) (by omega)).mpr hb1,
      (key j l (by omega) (by omega) (by omega)).mpr hb2⟩

/-! ### Rotating a vertex to the front, deleting it -/

theorem OHam.rotate_to (hA : ∀ a b, A a b → A b a) {H : List ℕ}
    (h : OHam A H) {a : ℕ} (ha : a ∈ H) : ∃ C, H ~r a :: C ∧ OHam A (a :: C) := by
  obtain ⟨xs, ys, rfl⟩ := List.mem_iff_append.mp ha
  have hr : xs ++ a :: ys ~r a :: (ys ++ xs) := by
    have := List.isRotated_append (l := xs) (l' := a :: ys)
    simpa using this
  exact ⟨ys ++ xs, hr, h.isRotated hA hr⟩

/-- The two neighbours of the first vertex on the cycle. -/
theorem OHam.ends {a : ℕ} {C : List ℕ} (h : OHam A (a :: C)) :
    A a (C.getD 0 0) ∧ A (C.getD (C.length - 1) 0) a := by
  obtain ⟨h3, -, ⟨h1, h2⟩, -⟩ := h
  simp only [List.length_cons] at h3
  refine ⟨by simpa using h1 0 (by simp; omega), ?_⟩
  have hc : (a :: C).getD C.length 0 = C.getD (C.length - 1) 0 := by
    cases C with
    | nil => simp at h3
    | cons b t => simp
  simp only [List.length_cons, Nat.add_sub_cancel, List.getD_cons_zero] at h2
  rwa [hc] at h2

/-- Deleting the first vertex `v` of a cycle without crossings and joining its two
neighbours gives a cycle without crossings. -/
theorem OHam.drop_head {A' : ℕ → ℕ → Prop} {v : ℕ} {C : List ℕ} (h : OHam A (v :: C))
    (h3 : 3 ≤ C.length)
    (hA' : ∀ a ∈ C, ∀ b ∈ C, A' a b ↔ A a b ∨
      (a = C.getD 0 0 ∧ b = C.getD (C.length - 1) 0) ∨
      (a = C.getD (C.length - 1) 0 ∧ b = C.getD 0 0)) : OHam A' C := by
  obtain ⟨-, hnd, ⟨h1, -⟩, hx⟩ := h
  have hCnd : C.Nodup := (List.nodup_cons.mp hnd).2
  have hinj : ∀ i j, i < C.length → j < C.length → C.getD i 0 = C.getD j 0 → i = j :=
    fun i j hi hj e => (hCnd.getD_inj hi hj).mp e
  have hmem : ∀ i, i < C.length → C.getD i 0 ∈ C := fun i hi => getD_mem_of_lt hi
  refine ⟨h3, hCnd, ⟨fun j hj => ?_, ?_⟩, ?_⟩
  · have := h1 (j + 1) (by simp; omega)
    simp only [List.getD_cons_succ] at this
    exact (hA' _ (hmem j (by omega)) _ (hmem (j + 1) hj)).mpr (Or.inl this)
  · exact (hA' _ (hmem _ (by omega)) _ (hmem 0 (by omega))).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · intro i j k l hij hjk hkl hl ⟨hik, hjl⟩
    rcases (hA' _ (hmem i (by omega)) _ (hmem k (by omega))).mp hik with hik | ⟨e1, e2⟩ |
      ⟨e1, e2⟩
    · rcases (hA' _ (hmem j (by omega)) _ (hmem l hl)).mp hjl with hjl | ⟨e3, e4⟩ | ⟨e3, e4⟩
      · apply hx (i + 1) (j + 1) (k + 1) (l + 1) (by omega) (by omega) (by omega)
          (by simp; omega)
        simp only [List.getD_cons_succ]
        exact ⟨hik, hjl⟩
      · have := hinj j 0 (by omega) (by omega) e3; omega
      · have := hinj l 0 hl (by omega) e4; omega
    · have := hinj k (C.length - 1) (by omega) (by omega) e2; omega
    · have := hinj k 0 (by omega) (by omega) e2; omega

end

/-! ### Edge lists -/

theorem OuterplanarHam.oham {g : Graph} {ham : List ℕ} (h : OuterplanarHam g ham) :
    OHam (Adj g) ham :=
  ⟨h.1.1, h.1.2.2.1, ⟨fun _ hj => h.adj_succ hj, h.adj_wrap.symm⟩, h.2.2⟩

theorem OHam.isCycle {g : Graph} {ham : List ℕ} (h : OHam (Adj g) ham) :
    IsCycle g ham.length ham := by
  refine ⟨h.1, rfl, h.2.1, fun e he => ?_⟩
  obtain ⟨xs, a, b, ys, hsplit, rfl⟩ := mem_pathEdges_iff.mp he
  have hn : 0 < ham.length := by have := h.1; omega
  have htake : ham.take 1 = [ham.getD 0 0] := by
    cases ham with
    | nil => simp at hn
    | cons x t => simp
  rw [htake] at hsplit
  have hlen := congrArg List.length hsplit
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  have ha : (ham ++ [ham.getD 0 0]).getD xs.length 0 = a := by
    rw [hsplit, List.getD_append_right _ _ _ _ le_rfl]
    simp
  have hb : (ham ++ [ham.getD 0 0]).getD (xs.length + 1) 0 = b := by
    rw [hsplit, List.getD_append_right _ _ _ _ (by omega)]
    simp
  rw [getD_snoc_of_lt (by omega)] at ha
  rcases Nat.lt_or_ge (xs.length + 1) ham.length with hlt | hge
  · rw [getD_snoc_of_lt hlt] at hb
    rw [← ha, ← hb]
    exact (h.2.2.1.1 _ hlt).2
  · have hx : xs.length + 1 = ham.length := by omega
    rw [hx, getD_snoc_length] at hb
    have ha' : ham.getD (ham.length - 1) 0 = a := by
      rw [← ha]
      congr 1
      omega
    rw [← ha', ← hb]
    exact h.2.2.1.2.2

theorem OHam.outerplanarHam {g : Graph} {ham : List ℕ} (h : OHam (Adj g) ham)
    (hv : ∀ v, IsVertex g v → v ∈ ham) : OuterplanarHam g ham :=
  ⟨h.isCycle, hv, h.2.2.2⟩

/-- **Rotation invariance** of outerplanar Hamiltonian cycles. -/
theorem OuterplanarHam.isRotated {g : Graph} {K K' : List ℕ} (h : OuterplanarHam g K)
    (hr : K ~r K') : OuterplanarHam g K' :=
  (h.oham.isRotated (fun _ _ hab => hab.symm) hr).outerplanarHam
    fun v hv => hr.mem_iff.mp (h.2.1 v hv)

theorem OuterplanarHam.rotate {g : Graph} {K : List ℕ} (h : OuterplanarHam g K) (n : ℕ) :
    OuterplanarHam g (K.rotate n) :=
  h.isRotated ⟨n, rfl⟩

/-- **Reversal invariance** of outerplanar Hamiltonian cycles. -/
theorem OuterplanarHam.reverse {g : Graph} {K : List ℕ} (h : OuterplanarHam g K) :
    OuterplanarHam g K.reverse :=
  (h.oham.reverse (fun _ _ hab => hab.symm)).outerplanarHam
    fun v hv => List.mem_reverse.mpr (h.2.1 v hv)

end STACS2027
