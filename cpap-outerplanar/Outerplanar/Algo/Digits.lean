module

public import Outerplanar.Algo.Poly
import Mathlib.Tactic

/-!
# Base-`k` configurations and the first strict minimum

Facts about the configurations of the polygon solver (`Outerplanar.Algo.Poly`), written as
base-`k` numbers:

* `cfg k L x` lists the `L` lowest base-`k` digits of `x` (`getElem_cfg`, `cfg_succ`), each
  below `k` (`cfg_lt`);
* `enc k ds` is the number with the digits `ds`: below `k ^ ds.length` (`enc_lt`), and
  `cfg` reads the digits back (`cfg_enc`, `enc_cfg`);
* `argmin_fold`: the fold of `tabArg` over `List.range' 1 (m - 1)`, starting from
  `(0, f 0)` and keeping the first strict minimum, returns an index `β < m` with `f β`
  least among `f 0, …, f (m - 1)`.
-/

@[expose] public section

namespace STACS2027.Poly

/-! ### Digits -/

@[simp] theorem length_cfg (k L x : ℕ) : (cfg k L x).length = L := by simp [cfg]

@[simp] theorem getElem_cfg (k L x i : ℕ) (hi : i < (cfg k L x).length) :
    (cfg k L x)[i] = x / k ^ i % k := by simp [cfg]

theorem getD_cfg {k L x i : ℕ} (hi : i < L) : (cfg k L x).getD i 0 = x / k ^ i % k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi), Option.getD_some,
    getElem_cfg]

theorem cfg_lt {k : ℕ} (hk : 0 < k) (L x : ℕ) : ∀ d ∈ cfg k L x, d < k := by
  intro d hd
  simp only [cfg, List.mem_map] at hd
  obtain ⟨t, -, rfl⟩ := hd
  exact Nat.mod_lt _ hk

theorem cfg_zero (k x : ℕ) : cfg k 0 x = [] := rfl

/-- The lowest digit, then the digits of the quotient. -/
theorem cfg_succ (k L x : ℕ) : cfg k (L + 1) x = x % k :: cfg k L (x / k) := by
  simp only [cfg, List.range_succ_eq_map, List.map_cons, List.map_map, pow_zero, Nat.div_one,
    List.cons.injEq, true_and]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, pow_succ', Nat.div_div_eq_div_mul]

theorem enc_lt {k : ℕ} (hk : 0 < k) : ∀ ds : List ℕ, (∀ d ∈ ds, d < k) → enc k ds < k ^ ds.length
  | [], _ => by simp [enc]
  | d :: ds, h => by
    have h1 : d < k := h d (by simp)
    have h2 := enc_lt hk ds (fun d hd => h d (by simp [hd]))
    simp only [enc, List.length_cons, pow_succ']
    calc d + k * enc k ds < k + k * enc k ds := by omega
      _ = k * (enc k ds + 1) := by ring
      _ ≤ k * k ^ ds.length := Nat.mul_le_mul_left k h2

/-- `cfg` reads back the digits of `enc`. -/
theorem cfg_enc {k : ℕ} : ∀ ds : List ℕ, (∀ d ∈ ds, d < k) → cfg k ds.length (enc k ds) = ds
  | [], _ => rfl
  | d :: ds, h => by
    have h1 : d < k := h d (by simp)
    have hk : 0 < k := by omega
    rw [List.length_cons, cfg_succ]
    simp only [enc]
    have hmod : (d + k * enc k ds) % k = d := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
    have hdiv : (d + k * enc k ds) / k = enc k ds := by
      rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt h1, zero_add]
    rw [hmod, hdiv, cfg_enc ds (fun d hd => h d (by simp [hd]))]

/-- `enc` reads back the number of `cfg`. -/
theorem enc_cfg {k : ℕ} : ∀ (L x : ℕ), x < k ^ L → enc k (cfg k L x) = x
  | 0, x, h => by simp only [pow_zero] at h; simp [cfg_zero, enc]; omega
  | L + 1, x, h => by
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; simp at h
      · exact h0
    rw [cfg_succ]
    simp only [enc]
    have hx : x / k < k ^ L := by
      rw [Nat.div_lt_iff_lt_mul hk, ← pow_succ]; exact h
    rw [enc_cfg L (x / k) hx]
    exact Nat.mod_add_div x k

/-! ### The first strict minimum -/

/-- One step of the minimization of `tabArg`: keep the first strict minimum. -/
theorem foldl_min (f : ℕ → ℕ) : ∀ (l : List ℕ) (b : ℕ), ∃ r,
    l.foldl (fun bv β => if f β < bv.2 then (β, f β) else bv) (b, f b) = (r, f r) ∧
      (r = b ∨ r ∈ l) ∧ f r ≤ f b ∧ ∀ β ∈ l, f r ≤ f β
  | [], b => ⟨b, rfl, Or.inl rfl, le_rfl, by simp⟩
  | x :: l, b => by
    have hstep : (if f x < (b, f b).2 then (x, f x) else (b, f b)) =
        (if f x < f b then x else b, f (if f x < f b then x else b)) := by
      by_cases h : f x < f b <;> simp [h]
    obtain ⟨r, hr, hmem, hle, hall⟩ := foldl_min f l (if f x < f b then x else b)
    refine ⟨r, by rw [List.foldl_cons, hstep, hr], ?_, ?_, ?_⟩
    · rcases hmem with h | h
      · by_cases hx : f x < f b
        · simp only [hx, ↓reduceIte] at h; exact Or.inr (h ▸ List.mem_cons_self)
        · simp only [hx, ↓reduceIte] at h; exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · by_cases hx : f x < f b
      · simp only [hx, ↓reduceIte] at hle; omega
      · simp only [hx, ↓reduceIte] at hle; exact hle
    · intro β hβ
      rcases List.mem_cons.mp hβ with rfl | h
      · by_cases hx : f β < f b
        · simp only [hx, ↓reduceIte] at hle; exact hle
        · simp only [hx, ↓reduceIte] at hle; omega
      · exact hall β h

/-- **The minimization of `tabArg`**: folding over `1, …, m - 1` from `(0, f 0)` and keeping
the first strict minimum gives an index `β < m` whose value `f β` is the least of
`f 0, …, f (m - 1)`. -/
theorem argmin_fold (f : ℕ → ℕ) {m : ℕ} (hm : 0 < m) :
    let r := (List.range' 1 (m - 1)).foldl (fun bv β => if f β < bv.2 then (β, f β) else bv)
      (0, f 0)
    r.1 < m ∧ r.2 = f r.1 ∧ ∀ β < m, r.2 ≤ f β := by
  obtain ⟨r, hr, hmem, hle, hall⟩ := foldl_min f (List.range' 1 (m - 1)) 0
  simp only [hr, true_and]
  refine ⟨?_, ?_⟩
  · rcases hmem with h | h
    · omega
    · rw [List.mem_range'_1] at h; omega
  · intro β hβ
    rcases Nat.eq_zero_or_pos β with h | h
    · subst h; exact hle
    · exact hall β (List.mem_range'_1.mpr ⟨h, by omega⟩)

end STACS2027.Poly
