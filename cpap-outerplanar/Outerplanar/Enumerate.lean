module

public import Outerplanar.RegionPaths
public import Outerplanar.DPCorrect
import Mathlib.Tactic

/-!
# Enumerating region paths (Lemma 29, the recursion over the faces)

The face decomposition (`IsPolygon.isRPath_iff_joins`, our form of Appendix F, Lemma 29)
turns into a recursive enumeration of the region paths of an edge `(a, b)` with a given
number `L` of entries (`rpaths g n a b L`):

* `[a, b]` itself when `L = 2`;
* if `(a, b)` is a segment, every concatenation of region paths between consecutive vertices
  of the face below `(a, b)` with `L - 1` edges in total (`joinPaths`), each piece
  enumerated recursively (the pieces span shorter intervals, `infix_faceVerts_lt`).

The recursion is structural in a fuel parameter, set to `b - a` (`rpathsAux`).

* `mem_rpaths`: the members are exactly the region paths from `a` to `b` with `L` entries;
* `nodup_rpaths`: each is listed once;
* `length_rpaths_le`: their number is at most `rpathBound L`, a function of `L` alone
  (crude, in place of the paper's `4^k`): a face contributing to a path with `L` entries
  has at most `L` vertices, and each of its slots carries fewer than `L` entries;
* `mem_rpaths_iff_convex`: for `L = k ≥ 3` these are the convex `k`-cycles (`convexList`)
  with top segment `(a, b)`.
-/

@[expose] public section

namespace STACS2027

open IsPolygon

/-- The concatenations, along consecutive entries of `vs`, of paths listed by `f`
(`f x y l`: paths from `x` to `y` with `l` entries), with `m` edges in total: every slot
gets at least one edge (the first slot `l ≥ 1` edges, leaving one for each later slot), and
the repeated junction vertices are dropped. -/
def joinPaths (f : ℕ → ℕ → ℕ → List (List ℕ)) : List ℕ → ℕ → List (List ℕ)
  | [], _ => []
  | [x], m => if m = 0 then [[x]] else []
  | x :: y :: rest, m =>
    (List.range' 1 (m - rest.length)).flatMap fun l =>
      (f x y (l + 1)).flatMap fun p => (joinPaths f (y :: rest) (m - l)).map fun q => p ++ q.tail

/-- The region paths from `a` to `b` with `L` entries, with recursion fuel: `[a, b]` when
`L = 2`, and, if `(a, b)` is a segment, the concatenations of region paths along the face
below `(a, b)` with `L - 1` edges. -/
def rpathsAux (g : Graph) (n : ℕ) : ℕ → ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _, _ => []
  | fuel + 1, a, b, L =>
    (if L = 2 ∧ a < b ∧ Adj g a b then [[a, b]] else []) ++
      (if (a, b) ∈ segs g n then
        joinPaths (rpathsAux g n fuel) (faceVerts g n (a, b)) (L - 1) else [])

/-- **The region paths of `(a, b)` with `L` entries** (computable), by recursion on
`b - a` over the faces of the polygon. -/
def rpaths (g : Graph) (n a b L : ℕ) : List (List ℕ) := rpathsAux g n (b - a) a b L

/-- The bound on the number of region paths with `L` entries. -/
def rpathBound : ℕ → ℕ
  | 0 => 2
  | L + 1 => 1 + (L * rpathBound L + 1) ^ L

variable {g : Graph} {n : ℕ}

/-! ### Concatenations -/

/-- The first two entries of a list are consecutive. -/
theorem infix_pair_head (x y : ℕ) (rest : List ℕ) : [x, y] <:+: x :: y :: rest :=
  ⟨[], rest, rfl⟩

/-- Soundness of `joinPaths`. -/
theorem sound_joinPaths {f : ℕ → ℕ → ℕ → List (List ℕ)} : ∀ {vs : List ℕ},
    (∀ x y, [x, y] <:+: vs → ∀ l, ∀ p ∈ f x y l, IsRPath g x y p ∧ p.length = l) →
    ∀ {m : ℕ} {u : List ℕ}, u ∈ joinPaths f vs m → Joins g vs u ∧ u.length = m + 1
  | [], _, _, _, h => by simp [joinPaths] at h
  | [x], _, m, u, h => by
    simp only [joinPaths] at h
    by_cases hm : m = 0
    · simp only [hm, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact ⟨rfl, by simp [hm]⟩
    · simp [hm] at h
  | x :: y :: rest, hf, m, u, h => by
    simp only [joinPaths, List.mem_flatMap, List.mem_map, List.mem_range'_1] at h
    obtain ⟨l, ⟨hl1, hl2⟩, p, hp, q, hq, rfl⟩ := h
    have hp' := hf x y (infix_pair_head x y rest) _ p hp
    have hq' := sound_joinPaths (fun x' y' h => hf x' y' (List.infix_cons h)) hq
    refine ⟨⟨p, q, hp'.1, hq'.1, rfl⟩, ?_⟩
    simp only [List.length_append, List.length_tail, hp'.2, hq'.2]
    omega

/-- Completeness of `joinPaths`. -/
theorem complete_joinPaths {f : ℕ → ℕ → ℕ → List (List ℕ)} : ∀ {vs : List ℕ},
    vs.Pairwise (· < ·) →
    (∀ x y, [x, y] <:+: vs → ∀ l, ∀ p, IsRPath g x y p → p.length = l → p ∈ f x y l) →
    ∀ {m : ℕ} {u : List ℕ}, Joins g vs u → u.length = m + 1 → u ∈ joinPaths f vs m
  | [], _, _, _, _, h, _ => h.elim
  | [_], _, _, m, u, h, hl => by
    simp only [Joins] at h
    subst h
    have hm : m = 0 := by simp at hl; omega
    simp [joinPaths, hm]
  | x :: y :: rest, hs, hf, m, _, h, hl => by
    obtain ⟨p, q, hp, hq, rfl⟩ := h
    have hxy : x < y := (List.pairwise_cons.mp hs).1 y (by simp)
    have hp2 := hp.two_le_length hxy
    have hq2 : (y :: rest).length ≤ q.length := hq.length_le (List.pairwise_cons.mp hs).2
    simp only [List.length_append, List.length_tail, List.length_cons] at hl hq2
    simp only [joinPaths, List.mem_flatMap, List.mem_map, List.mem_range'_1]
    exact ⟨p.length - 1, ⟨by omega, by omega⟩, p,
      hf x y (infix_pair_head x y rest) _ p hp (by omega), q,
      complete_joinPaths (List.pairwise_cons.mp hs).2
        (fun x' y' h => hf x' y' (List.infix_cons h)) hq (by omega), rfl⟩

/-- The junction `y` sits at position `p.length - 1` of `p ++ r`, for a region path `p` to
`y`. -/
theorem idxOf_append_of_isRPath {x y : ℕ} {p : List ℕ} (hp : IsRPath g x y p)
    (r : List ℕ) : (p ++ r).idxOf y = p.length - 1 := by
  obtain ⟨p₀, rfl⟩ := List.getLast?_eq_some_iff.mp hp.2.1
  have hps := hp.pairwise
  have hy : y ∉ p₀ := by
    intro h
    have := (List.pairwise_append.mp hps).2.2 y h y (by simp)
    omega
  rw [List.append_assoc, List.singleton_append, List.idxOf_append_of_notMem hy,
    List.idxOf_cons_self]
  simp

/-- `joinPaths` lists each concatenation once. -/
theorem nodup_joinPaths {f : ℕ → ℕ → ℕ → List (List ℕ)} : ∀ {vs : List ℕ},
    (∀ x y, [x, y] <:+: vs → ∀ l,
      (f x y l).Nodup ∧ ∀ p ∈ f x y l, IsRPath g x y p ∧ p.length = l) →
    ∀ {m : ℕ}, (joinPaths f vs m).Nodup
  | [], _, _ => by simp [joinPaths]
  | [_], _, m => by
    simp only [joinPaths]
    by_cases hm : m = 0 <;> simp [hm]
  | x :: y :: rest, hf, m => by
    have hf' : ∀ x' y', [x', y'] <:+: y :: rest → ∀ l,
        (f x' y' l).Nodup ∧ ∀ p ∈ f x' y' l, IsRPath g x' y' p ∧ p.length = l :=
      fun x' y' h => hf x' y' (List.infix_cons h)
    have hsound : ∀ l, ∀ q ∈ joinPaths f (y :: rest) l,
        Joins g (y :: rest) q ∧ q.length = l + 1 :=
      fun _ _ hq => sound_joinPaths (fun x' y' h l p hp => (hf' x' y' h l).2 p hp) hq
    have hxy := hf x y (infix_pair_head x y rest)
    simp only [joinPaths]
    rw [List.nodup_flatMap]
    refine ⟨fun l _ => ?_, ?_⟩
    · rw [List.nodup_flatMap]
      refine ⟨fun p _ => ?_, ?_⟩
      · refine List.Nodup.map_on ?_ (nodup_joinPaths hf')
        intro q₁ hq₁ q₂ hq₂ he
        obtain ⟨t₁, rfl⟩ := List.head?_eq_some_iff.mp (hsound _ q₁ hq₁).1.head?
        obtain ⟨t₂, rfl⟩ := List.head?_eq_some_iff.mp (hsound _ q₂ hq₂).1.head?
        simp only [List.tail_cons] at he
        rw [List.append_cancel_left he]
      · refine List.Pairwise.imp_of_mem ?_ (hxy (l + 1)).1
        intro p₁ p₂ hp₁ hp₂ hne w hw₁ hw₂
        simp only [List.mem_map] at hw₁ hw₂
        obtain ⟨q₁, -, rfl⟩ := hw₁
        obtain ⟨q₂, -, he⟩ := hw₂
        have hl₁ := ((hxy (l + 1)).2 p₁ hp₁).2
        have hl₂ := ((hxy (l + 1)).2 p₂ hp₂).2
        exact hne (List.append_inj he.symm (by rw [hl₁, hl₂])).1
    · refine List.Pairwise.imp_of_mem ?_ List.nodup_range'
      intro l₁ l₂ _ _ hne w hw₁ hw₂
      simp only [List.mem_flatMap, List.mem_map] at hw₁ hw₂
      obtain ⟨p₁, hp₁, q₁, -, rfl⟩ := hw₁
      obtain ⟨p₂, hp₂, q₂, -, he⟩ := hw₂
      have h₁ := (hxy _).2 p₁ hp₁
      have h₂ := (hxy _).2 p₂ hp₂
      have e₁ := idxOf_append_of_isRPath h₁.1 q₁.tail
      have e₂ := idxOf_append_of_isRPath h₂.1 q₂.tail
      rw [he] at e₂
      apply hne
      omega

/-- A sum of `l.length` terms, each at most `c`, is at most `l.length * c`. -/
theorem sum_map_le_mul {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ)
    (h : ∀ x ∈ l, f x ≤ c) : (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, add_one_mul]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    omega

/-- The number of concatenations: at most `(m K + 1)^m` when every slot path list called
has at most `K` members. -/
theorem length_joinPaths_le (f : ℕ → ℕ → ℕ → List (List ℕ)) (K : ℕ) :
    ∀ (vs : List ℕ) (m : ℕ), (∀ x y l, l + vs.length ≤ m + 3 → (f x y l).length ≤ K) →
      (joinPaths f vs m).length ≤ (m * K + 1) ^ m
  | [], m, _ => by simp [joinPaths]
  | [_], m, _ => by
    simp only [joinPaths]
    by_cases hm : m = 0 <;> simp [hm]
  | x :: y :: rest, m, hK => by
    simp only [joinPaths, List.length_flatMap, List.length_map]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hB : 0 < (m' + 1) * K + 1 := by omega
    calc _ ≤ (List.range' 1 (m' + 1 - rest.length)).length *
          (K * ((m' + 1) * K + 1) ^ m') := by
          apply sum_map_le_mul
          intro l hl
          rw [List.mem_range'_1] at hl
          have hJ := length_joinPaths_le f K (y :: rest) (m' + 1 - l)
            (fun x' y' l' h => hK x' y' l' (by simp only [List.length_cons] at h ⊢; omega))
          have hf := hK x y (l + 1) (by simp only [List.length_cons]; omega)
          calc _ ≤ (f x y (l + 1)).length * (joinPaths f (y :: rest) (m' + 1 - l)).length :=
                sum_map_le_mul _ _ _ (fun _ _ => le_rfl)
            _ ≤ K * (((m' + 1 - l) * K + 1) ^ (m' + 1 - l)) := Nat.mul_le_mul hf hJ
            _ ≤ K * ((m' + 1) * K + 1) ^ m' := by
                apply Nat.mul_le_mul_left
                calc ((m' + 1 - l) * K + 1) ^ (m' + 1 - l)
                    ≤ ((m' + 1) * K + 1) ^ (m' + 1 - l) := by
                      apply Nat.pow_le_pow_left
                      have := Nat.mul_le_mul_right K (Nat.sub_le (m' + 1) l)
                      omega
                  _ ≤ ((m' + 1) * K + 1) ^ m' := Nat.pow_le_pow_right hB (by omega)
      _ ≤ (m' + 1) * (K * ((m' + 1) * K + 1) ^ m') := by
          apply Nat.mul_le_mul_right
          simp only [List.length_range']
          omega
      _ = ((m' + 1) * K) * ((m' + 1) * K + 1) ^ m' := by ring
      _ ≤ ((m' + 1) * K + 1) * ((m' + 1) * K + 1) ^ m' :=
          Nat.mul_le_mul_right _ (Nat.le_succ _)
      _ = ((m' + 1) * K + 1) ^ (m' + 1) := by ring

/-! ### Region paths -/

/-- `rpathBound` is nondecreasing (one step). -/
theorem rpathBound_le_succ (L : ℕ) : rpathBound L ≤ rpathBound (L + 1) := by
  cases L with
  | zero => simp [rpathBound]
  | succ L =>
    show rpathBound (L + 1) ≤ 1 + ((L + 1) * rpathBound (L + 1) + 1) ^ (L + 1)
    have h1 : rpathBound (L + 1) ≤ (L + 1) * rpathBound (L + 1) + 1 := by
      have := Nat.le_mul_of_pos_left (rpathBound (L + 1)) (by omega : 0 < L + 1)
      omega
    have h2 : (L + 1) * rpathBound (L + 1) + 1 ≤
        ((L + 1) * rpathBound (L + 1) + 1) ^ (L + 1) := Nat.le_self_pow (by omega) _
    omega

/-- `rpathBound` is monotone. -/
theorem rpathBound_mono : Monotone rpathBound := monotone_nat_of_le_succ rpathBound_le_succ

/-- Soundness of the enumeration (for any graph). -/
theorem sound_rpathsAux : ∀ {fuel a b L : ℕ} {u : List ℕ}, u ∈ rpathsAux g n fuel a b L →
    IsRPath g a b u ∧ u.length = L
  | 0, _, _, _, _, h => by simp [rpathsAux] at h
  | fuel + 1, a, b, L, u, h => by
    simp only [rpathsAux, List.mem_append] at h
    rcases h with h | h
    · by_cases hc : L = 2 ∧ a < b ∧ Adj g a b
      · simp only [hc, and_self, ↓reduceIte, List.mem_singleton] at h
        subst h
        exact ⟨isRPath_pair.mpr ⟨hc.2.1, hc.2.2⟩, by simp [hc.1]⟩
      · simp [hc] at h
    · by_cases hs : (a, b) ∈ segs g n
      · simp only [hs, ↓reduceIte] at h
        have hs' := of_mem_segs hs
        obtain ⟨hj, hl⟩ := sound_joinPaths (fun _ _ _ _ _ hp => sound_rpathsAux hp) h
        have hr : IsRPath g a b u :=
          hj.isRPath (faceVerts_head? (by simp only at hs' ⊢; omega))
            (faceVerts_getLast? (by simp only at hs' ⊢; omega))
        have h2 := hr.two_le_length (by simp only at hs'; omega)
        exact ⟨hr, by omega⟩
      · simp [hs] at h

namespace IsPolygon

/-- Correctness of the enumeration with enough fuel. -/
theorem mem_rpathsAux (hP : IsPolygon g n) : ∀ {fuel a b : ℕ}, b - a ≤ fuel → a < b →
    Adj g a b → ∀ {L : ℕ} {u : List ℕ},
      u ∈ rpathsAux g n fuel a b L ↔ IsRPath g a b u ∧ u.length = L
  | 0, _, _, hf, hab, _, _, _ => by omega
  | fuel + 1, a, b, hf, hab, hadj, L, u => by
    refine ⟨sound_rpathsAux, ?_⟩
    rintro ⟨hu, hl⟩
    simp only [rpathsAux, List.mem_append]
    by_cases hs : (a, b) ∈ segs g n
    · rcases (hP.isRPath_iff_joins hs).mp hu with h | h
      · left
        subst h
        simp only [List.length_cons, List.length_nil] at hl
        subst hl
        simp [hab, hadj]
      · right
        simp only [hs, ↓reduceIte]
        have h3 := h.length_le faceVerts_pairwise
        have h3' := hP.three_le_length_faceVerts hs
        refine complete_joinPaths faceVerts_pairwise ?_ h (by omega)
        intro x y hxy l p hp hpl
        have hlt := hP.infix_faceVerts_lt hs hxy
        exact (hP.mem_rpathsAux (by simp only at hlt; omega) hlt.2.1
          (hP.adj_of_infix_faceVerts hs hxy)).mpr ⟨hp, hpl⟩
    · have hb : b = a + 1 := by
        by_contra h
        exact hs (hP.mem_segs.mpr ⟨hadj, by simp only; omega⟩)
      subst hb
      obtain ⟨rfl, -⟩ := isRPath_side_iff.mp hu
      left
      simp only [List.length_cons, List.length_nil] at hl
      subst hl
      simp [hadj]

/-- The enumeration lists each region path once. -/
theorem nodup_rpathsAux (hP : IsPolygon g n) : ∀ {fuel a b L : ℕ},
    (rpathsAux g n fuel a b L).Nodup
  | 0, _, _, _ => by simp [rpathsAux]
  | fuel + 1, a, b, L => by
    simp only [rpathsAux]
    rw [List.nodup_append]
    refine ⟨by split_ifs <;> simp, ?_, ?_⟩
    · split_ifs
      · exact nodup_joinPaths fun _ _ _ _ =>
          ⟨hP.nodup_rpathsAux, fun _ hp => sound_rpathsAux hp⟩
      · simp
    · intro w hw w' hw' he
      subst he
      by_cases hc : L = 2 ∧ a < b ∧ Adj g a b
      · simp only [hc, and_self, ↓reduceIte, List.mem_singleton] at hw
        subst hw
        by_cases hs : (a, b) ∈ segs g n
        · simp only [hs, ↓reduceIte] at hw'
          obtain ⟨hj, -⟩ := sound_joinPaths (fun _ _ _ _ _ hp => sound_rpathsAux hp) hw'
          have h3 := hj.length_le faceVerts_pairwise
          have h3' := hP.three_le_length_faceVerts hs
          simp at h3
          omega
        · simp [hs] at hw'
      · simp [hc] at hw

/-- The enumeration has at most `rpathBound L` members. -/
theorem length_rpathsAux_le (hP : IsPolygon g n) : ∀ (fuel a b L : ℕ),
    (rpathsAux g n fuel a b L).length ≤ rpathBound L
  | 0, _, _, L => by simp [rpathsAux]
  | fuel + 1, a, b, L => by
    simp only [rpathsAux, List.length_append]
    have hA : (if L = 2 ∧ a < b ∧ Adj g a b then [[a, b]] else
        ([] : List (List ℕ))).length ≤ 1 := by
      split_ifs <;> simp
    have hB : (if (a, b) ∈ segs g n then
        joinPaths (rpathsAux g n fuel) (faceVerts g n (a, b)) (L - 1) else []).length ≤
        ((L - 1) * rpathBound (L - 1) + 1) ^ (L - 1) := by
      split_ifs with hs
      · apply length_joinPaths_le
        intro x y l hl
        have h3 := hP.three_le_length_faceVerts hs
        exact (hP.length_rpathsAux_le fuel x y l).trans (rpathBound_mono (by omega))
      · simp
    have hL : 1 + ((L - 1) * rpathBound (L - 1) + 1) ^ (L - 1) ≤ rpathBound L := by
      cases L with
      | zero => simp [rpathBound]
      | succ L => simp [rpathBound]
    omega

/-- **Enumeration of region paths**: for an edge `(a, b)`, `a < b`, of a polygon, the members
of `rpaths g n a b L` are exactly the region paths from `a` to `b` with `L` entries. -/
theorem mem_rpaths (hP : IsPolygon g n) {a b : ℕ} (hadj : Adj g a b) (hab : a < b)
    {L : ℕ} {u : List ℕ} : u ∈ rpaths g n a b L ↔ IsRPath g a b u ∧ u.length = L :=
  hP.mem_rpathsAux le_rfl hab hadj

/-- **The enumeration lists each region path once.** -/
theorem nodup_rpaths (hP : IsPolygon g n) (a b L : ℕ) : (rpaths g n a b L).Nodup :=
  hP.nodup_rpathsAux

/-- **Counting bound**: there are at most `rpathBound L` region paths with `L` entries
between the ends of any edge, a bound depending on `L` alone. -/
theorem length_rpaths_le (hP : IsPolygon g n) (a b L : ℕ) :
    (rpaths g n a b L).length ≤ rpathBound L :=
  hP.length_rpathsAux_le _ _ _ _

/-- For `k ≥ 3`, `rpaths g n a b k` lists the convex `k`-cycles with top segment `(a, b)`:
first entry `a` and last entry `b`. -/
theorem mem_rpaths_iff_convex (hP : IsPolygon g n) {a b : ℕ} (hadj : Adj g a b)
    (hab : a < b) {k : ℕ} (hk : 3 ≤ k) {u : List ℕ} :
    u ∈ rpaths g n a b k ↔ u ∈ convexList g n k ∧ u.head? = some a ∧ u.getLast? = some b := by
  rw [hP.mem_rpaths hadj hab, hP.mem_convexList]
  constructor
  · rintro ⟨hu, rfl⟩
    have := (convexCycle_iff_isRPath hadj).mpr ⟨hu, hk⟩
    exact ⟨⟨this.1, rfl⟩, this.2⟩
  · rintro ⟨⟨hc, hl⟩, h1, h2⟩
    exact ⟨((convexCycle_iff_isRPath hadj).mp ⟨hc, h1, h2⟩).1, hl⟩

end IsPolygon

end STACS2027
