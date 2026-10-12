module

public import Runtimes.C4.Output
public import Mathlib.Algebra.Order.Chebyshev
import Outerplanar.Algo.Combine
import Outerplanar.Algo.LowPoint
import Mathlib.Tactic

/-!
# Four-cycle listing: supersaturation (`2 D |E| ≤ 4 X + 9 t` for `X³ ≥ |E|⁴`)

`D = degen g` is the largest out-degree of the peeling orientation, `t` the number of
4-cycles. Let `v*` have out-degree `D` and let `W` be the vertices removed no
earlier than `v*`. By the minimum-degree property of the peeling (`peel_minDeg`), every vertex
of `W` has at least `D` neighbours in `W` (S0), so `|W| D ≤ 2 |E|` (S1).

* **Case A** (`D³ ≤ 8 |E|`): `(D |E|)³ ≤ 8 |E|⁴ ≤ (2X)³`.
* **Case B** (`8 |E| < D³`): count, over the ordered pairs `(u, v)` of distinct vertices of `W`,
  the common neighbours `c(u, v)` in `W`. Cherries (`cherries`, S2): `S = Σ c(u, v) =
  Σ_{z ∈ W} d(z) (d(z) - 1) ≥ |W| D (D - 1)`. Cauchy–Schwarz (S3): `S² ≤ |W|(|W| - 1) Σ c²`, and
  `Σ c² = Q + S` (S4) where `Q` counts the configurations `(u, v, z, z')` (`z ≠ z'` common
  neighbours of `u ≠ v`). Each configuration is a 4-cycle `u z v z'`, and each 4-cycle arises
  from at most 8 configurations (two diagonals, two orders each; `card_cfg_le`, S5–S6):
  `Q ≤ 8 t`. The arithmetic (`caseB'`) gives `D² (D - 1)² ≤ 16 t`, and then `2 D |E| ≤ 9 t`
  (`final_bound`).

Main result: **`degen_bound`**.
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo Finset

/-! ### Arithmetic -/

/-- The arithmetic of case B (all naturals): from `8 e < D³`, `n D ≤ 2 e`, `n ≥ 1`, the cherry
bound `n D (D - 1) ≤ S` and Cauchy–Schwarz `S² ≤ n (n - 1) (8 t + S)`, conclude
`D² (D - 1)² ≤ 16 t`. -/
theorem caseB' (D e n t S Np : ℕ) (hB : 8 * e < D ^ 3) (hn : n * D ≤ 2 * e) (hn1 : 1 ≤ n)
    (hS : n * (D * (D - 1)) ≤ S) (hN : Np = n * (n - 1))
    (hCS : S ^ 2 ≤ Np * (8 * t + S)) : D ^ 2 * (D - 1) ^ 2 ≤ 16 * t := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hN
  subst hN
  have hD : 1 ≤ D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · subst h; simp at hB
    · exact h
  obtain ⟨E, rfl⟩ : ∃ E, D = E + 1 := ⟨D - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hS ⊢
  have ha : 4 * (k + 1) < (E + 1) ^ 2 := by
    by_contra h
    simp only [not_lt] at h
    have : 4 * (k + 1) * (E + 1) ≥ (E + 1) ^ 3 := by nlinarith
    nlinarith
  have hb : 2 * ((k + 1) * k) ≤ S := by nlinarith
  have hc : S ^ 2 ≤ 16 * ((k + 1) * k) * t := by nlinarith
  have h1 : ((k + 1) * ((E + 1) * E)) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hS 2
  have h3 : 0 < (k + 1) ^ 2 := by positivity
  have : (k + 1) ^ 2 * ((E + 1) ^ 2 * E ^ 2) ≤ (k + 1) ^ 2 * (16 * t) := by nlinarith
  exact Nat.le_of_mul_le_mul_left this h3

/-- Both cases: if `e⁴ ≤ X³` and case B gives `D² (D - 1)² ≤ 16 t`, then
`2 D e ≤ 4 X + 9 t`. -/
theorem final_bound (D e t X : ℕ) (hX : e ^ 4 ≤ X ^ 3)
    (hsat : 8 * e < D ^ 3 → D ^ 2 * (D - 1) ^ 2 ≤ 16 * t) : 2 * (D * e) ≤ 4 * X + 9 * t := by
  by_cases hB : 8 * e < D ^ 3
  · have hd := hsat hB
    rcases Nat.eq_zero_or_pos e with he0 | he0
    · subst he0; simp
    have hD3 : 3 ≤ D := by
      by_contra h
      simp only [not_le] at h
      interval_cases D <;> norm_num at hB <;> omega
    obtain ⟨E, rfl⟩ : ∃ E, D = E + 1 := ⟨D - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hd
    have he : 4 * (E + 1) ^ 4 ≤ 9 * ((E + 1) ^ 2 * E ^ 2) := by
      have h0 : 2 * (E + 1) ≤ 3 * E := by omega
      have h1 := Nat.pow_le_pow_left h0 2
      have h2 : 4 * (E + 1) ^ 2 ≤ 9 * E ^ 2 := by nlinarith
      have h3 := Nat.mul_le_mul_left ((E + 1) ^ 2) h2
      nlinarith
    nlinarith
  · simp only [not_lt] at hB
    have h : (D * e) ^ 3 ≤ (2 * X) ^ 3 := by
      calc (D * e) ^ 3 = D ^ 3 * e ^ 3 := by ring
        _ ≤ 8 * e * e ^ 3 := by gcongr
        _ = 8 * e ^ 4 := by ring
        _ ≤ 8 * X ^ 3 := by gcongr
        _ = (2 * X) ^ 3 := by ring
    have := le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h
    omega

/-! ### Cherries and Cauchy–Schwarz, for a symmetric relation on a finite set -/

section Cherries

variable (A : ℕ → ℕ → Prop) [DecidableRel A] (W : Finset ℕ)

/-- The neighbours of `z` inside `W`. -/
def nbW (z : ℕ) : Finset ℕ := W.filter (A z)

/-- The common neighbours of `u` and `v` inside `W`. -/
def codW (u v : ℕ) : Finset ℕ := W.filter fun z => A u z ∧ A z v

/-- **S2.** Ordered cherries, counted at the ends or at the centre. -/
theorem cherries (hs : ∀ u v, A u v → A v u) :
    ∑ p ∈ W.offDiag, (codW A W p.1 p.2).card = ∑ z ∈ W, ((nbW A W z).offDiag).card := by
  simp only [card_eq_sum_ones]
  rw [Finset.sum_comm' (t' := W) (s' := fun z => (nbW A W z).offDiag)]
  intro p z
  simp only [mem_offDiag, nbW, mem_filter, codW]
  constructor
  · rintro ⟨⟨hu, hv, hne⟩, hz, h1, h2⟩
    exact ⟨⟨⟨hu, hs _ _ h1⟩, ⟨hv, h2⟩, hne⟩, hz⟩
  · rintro ⟨⟨⟨hu, h1⟩, ⟨hv, h2⟩, hne⟩, hz⟩
    exact ⟨⟨hu, hv, hne⟩, hz, hs _ _ h1, h2⟩

theorem sum_codW_ge (hs : ∀ u v, A u v → A v u) {D : ℕ} (hD : ∀ w ∈ W, D ≤ (nbW A W w).card) :
    W.card * (D * (D - 1)) ≤ ∑ p ∈ W.offDiag, (codW A W p.1 p.2).card := by
  rw [cherries A W hs]
  have := card_nsmul_le_sum W (fun z => ((nbW A W z).offDiag).card) (D * (D - 1)) fun z hz => by
    have h := hD z hz
    rw [offDiag_card]
    calc D * (D - 1) ≤ (nbW A W z).card * ((nbW A W z).card - 1) :=
          Nat.mul_le_mul h (Nat.sub_le_sub_right h 1)
      _ = _ := Nat.mul_sub_one _ _
  simpa using this

/-- **S3–S4.** Cauchy–Schwarz on the common-neighbour counts. -/
theorem sum_codW_sq :
    (∑ p ∈ W.offDiag, (codW A W p.1 p.2).card) ^ 2 ≤ (W.card * W.card - W.card) *
      (∑ p ∈ W.offDiag, ((codW A W p.1 p.2).offDiag).card +
        ∑ p ∈ W.offDiag, (codW A W p.1 p.2).card) := by
  have h := sq_sum_le_card_mul_sum_sq (s := W.offDiag) (f := fun p => (codW A W p.1 p.2).card)
  rw [offDiag_card] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  congr 1
  rw [← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  rw [offDiag_card, sq]
  have := Nat.le_mul_self (codW A W p.1 p.2).card
  omega

end Cherries

/-! ### Configurations are 4-cycles -/

variable {g : Graph}

/-- A closed walk `a b c d` of the id graph without repetitions is, in labels, a simple 4-cycle
of `g`. -/
theorem isCycle_of_nb {a b c d : ℕ} (ha : a < numV g) (hab : b ∈ nb g a) (hbc : c ∈ nb g b)
    (hcd : d ∈ nb g c) (hda : a ∈ nb g d) (hnd : [a, b, c, d].Nodup) :
    IsCycle g 4 [labelOf g a, labelOf g b, labelOf g c, labelOf g d] := by
  have hok := nbOk g
  have hb := hok.lt _ _ hab
  have hc := hok.lt _ _ hbc
  have hd := hok.lt _ _ hcd
  refine ⟨by norm_num, rfl, ?_, ?_⟩
  · have := hnd.map_on (f := labelOf g) fun x hx y hy h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      exact Comb.labelOf_inj x (by rcases hx with rfl | rfl | rfl | rfl <;> assumption)
        y (by rcases hy with rfl | rfl | rfl | rfl <;> assumption) h
    simpa using this
  · intro e he
    rw [cycleEdges4] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact edge_mem_of_nb ha hab
    · exact edge_mem_of_nb hb hbc
    · exact edge_mem_of_nb hc hcd
    · exact edge_mem_of_nb hd hda

/-- The adjacency of the id graph, as a relation. -/
abbrev adjR (g : Graph) (u v : ℕ) : Prop := v ∈ nb g u

/-- The configurations `((u, v), (z, z'))`: `u ≠ v` in `W`, `z ≠ z'` common neighbours of `u`
and `v` in `W`. -/
def cfg (g : Graph) (W : Finset ℕ) : Finset ((_ : ℕ × ℕ) × (ℕ × ℕ)) :=
  W.offDiag.sigma fun p => (codW (adjR g) W p.1 p.2).offDiag

/-- The 4-cycle of a configuration, in labels, canonical. -/
def cfgCycle (g : Graph) (x : (_ : ℕ × ℕ) × (ℕ × ℕ)) : Cycle :=
  canon4 (labelOf g x.1.1) (labelOf g x.2.1) (labelOf g x.1.2) (labelOf g x.2.2)

theorem mem_cfg {W : Finset ℕ} {u v z z' : ℕ} :
    (⟨(u, v), (z, z')⟩ : (_ : ℕ × ℕ) × (ℕ × ℕ)) ∈ cfg g W ↔
      (u ∈ W ∧ v ∈ W ∧ u ≠ v) ∧ (z ∈ W ∧ z ∈ nb g u ∧ v ∈ nb g z) ∧
        (z' ∈ W ∧ z' ∈ nb g u ∧ v ∈ nb g z') ∧ z ≠ z' := by
  simp [cfg, codW, mem_sigma, mem_offDiag]

theorem cfg_nodup {W : Finset ℕ} {u v z z' : ℕ}
    (h : (⟨(u, v), (z, z')⟩ : (_ : ℕ × ℕ) × (ℕ × ℕ)) ∈ cfg g W) : [u, z, v, z'].Nodup := by
  obtain ⟨⟨-, -, huv⟩, ⟨-, h1, h2⟩, ⟨-, h3, h4⟩, hzz⟩ := mem_cfg.mp h
  have hok := nbOk g
  have a1 : z ≠ u := fun e => hok.noloop u (e ▸ h1)
  have a2 : z ≠ v := fun e => hok.noloop z (e ▸ h2)
  have a3 : z' ≠ u := fun e => hok.noloop u (e ▸ h3)
  have a4 : z' ≠ v := fun e => hok.noloop z' (e ▸ h4)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true]
  omega

theorem cfg_isCycle {W : Finset ℕ} (hW : W ⊆ range (numV g)) {u v z z' : ℕ}
    (h : (⟨(u, v), (z, z')⟩ : (_ : ℕ × ℕ) × (ℕ × ℕ)) ∈ cfg g W) :
    IsCycle g 4 [labelOf g u, labelOf g z, labelOf g v, labelOf g z'] := by
  have hnd := cfg_nodup h
  obtain ⟨⟨hu, -, -⟩, ⟨-, h1, h2⟩, ⟨-, h3, h4⟩, -⟩ := mem_cfg.mp h
  have hok := nbOk g
  exact isCycle_of_nb (mem_range.mp (hW hu)) h1 h2 (hok.symm _ _ h4) (hok.symm _ _ h3) hnd

theorem cfgCycle_mem {W : Finset ℕ} (hW : W ⊆ range (numV g))
    {x : (_ : ℕ × ℕ) × (ℕ × ℕ)} (hx : x ∈ cfg g W) : cfgCycle g x ∈ cycles g 4 := by
  obtain ⟨⟨u, v⟩, ⟨z, z'⟩⟩ := x
  have hc := cfg_isCycle hW hx
  exact mem_cycles4.mpr ⟨isCycle_canon4 hc, canon4_isCanon hc.2.2.1⟩

/-- **S5–S6.** Each 4-cycle arises from at most 8 configurations, so there are at most `8 t`
configurations. -/
theorem card_cfg_le {W : Finset ℕ} (hW : W ⊆ range (numV g)) :
    (cfg g W).card ≤ 8 * (cycles g 4).length := by
  have hok := nbOk g
  calc (cfg g W).card ≤ 8 * ((cfg g W).image (cfgCycle g)).card := by
        refine card_le_mul_card_image _ 8 fun C hC => ?_
        obtain ⟨⟨⟨u₀, v₀⟩, ⟨z₀, w₀⟩⟩, hx₀, rfl⟩ := mem_image.mp hC
        let L : List ((_ : ℕ × ℕ) × (ℕ × ℕ)) :=
          [⟨(u₀, v₀), (z₀, w₀)⟩, ⟨(u₀, v₀), (w₀, z₀)⟩, ⟨(v₀, u₀), (z₀, w₀)⟩,
            ⟨(v₀, u₀), (w₀, z₀)⟩, ⟨(z₀, w₀), (u₀, v₀)⟩, ⟨(z₀, w₀), (v₀, u₀)⟩,
            ⟨(w₀, z₀), (u₀, v₀)⟩, ⟨(w₀, z₀), (v₀, u₀)⟩]
        refine le_trans (card_le_card ?_) (List.toFinset_card_le L)
        intro x hx
        obtain ⟨hx, hxe⟩ := mem_filter.mp hx
        obtain ⟨⟨u, v⟩, ⟨z, w⟩⟩ := x
        -- the label cycles have the same edges
        have s1 := canon4_same (labelOf g u) (labelOf g z) (labelOf g v) (labelOf g w)
        have s2 := canon4_same (labelOf g u₀) (labelOf g z₀) (labelOf g v₀) (labelOf g w₀)
        have s : SameCycle [labelOf g u, labelOf g z, labelOf g v, labelOf g w]
            [labelOf g u₀, labelOf g z₀, labelOf g v₀, labelOf g w₀] := by
          refine s1.trans ?_
          change SameCycle (cfgCycle g ⟨(u, v), (z, w)⟩) _
          rw [hxe]
          exact s2.symm
        have s' := sameCycle_map (idOf g) s
        have bound : ∀ {a b c d : ℕ},
            (⟨(a, b), (c, d)⟩ : (_ : ℕ × ℕ) × (ℕ × ℕ)) ∈ cfg g W →
              a < numV g ∧ b < numV g ∧ c < numV g ∧ d < numV g := by
          intro a b c d h
          obtain ⟨⟨ha, hb, -⟩, ⟨hc, -, -⟩, ⟨hd, -, -⟩, -⟩ := mem_cfg.mp h
          exact ⟨mem_range.mp (hW ha), mem_range.mp (hW hb), mem_range.mp (hW hc),
            mem_range.mp (hW hd)⟩
        obtain ⟨b1, b2, b3, b4⟩ := bound hx
        obtain ⟨c1, c2, c3, c4⟩ := bound hx₀
        simp only [List.map_cons, List.map_nil, idOf_labelOf b1, idOf_labelOf b2,
          idOf_labelOf b3, idOf_labelOf b4, idOf_labelOf c1, idOf_labelOf c2, idOf_labelOf c3,
          idOf_labelOf c4] at s'
        have hd := diagonals (cfg_nodup hx) (cfg_nodup hx₀) s'
        simp only [L, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
        rcases hd with ⟨hk, hc⟩ | ⟨hk, hc⟩ <;>
          rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp
    _ ≤ 8 * (cycles g 4).toFinset.card := by
        gcongr
        intro C hC
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hC
        exact List.mem_toFinset.mpr (cfgCycle_mem hW hx)
    _ = 8 * (cycles g 4).length := by rw [List.toFinset_card_of_nodup (cycles_nodup g 4)]

/-! ### The minimum-degree core -/

theorem symm_adjR (g : Graph) : ∀ u v, adjR g u v → adjR g v u :=
  fun u v h => (nbOk g).symm u v h

/-- The neighbours inside the core `W = {w : peelPos v ≤ peelPos w}`, as a list filter. -/
theorem card_nbW_core (g : Graph) (v w : ℕ) :
    (nbW (adjR g) ((range (numV g)).filter fun u => peelPos g v ≤ peelPos g u) w).card =
      ((nb g w).filter fun u => peelPos g v ≤ peelPos g u).length := by
  rw [← List.toFinset_card_of_nodup ((nodup_nb g w).filter _)]
  congr 1
  ext u
  simp only [nbW, mem_filter, mem_range, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨-, h⟩, h'⟩; exact ⟨h', h⟩
  · rintro ⟨h', h⟩; exact ⟨⟨(nbOk g).lt w u h', h⟩, h'⟩

theorem card_nbW_le (W : Finset ℕ) (w : ℕ) : (nbW (adjR g) W w).card ≤ (nb g w).length := by
  calc (nbW (adjR g) W w).card ≤ (nb g w).toFinset.card := by
        refine card_le_card fun u hu => ?_
        simp only [nbW, mem_filter] at hu
        exact List.mem_toFinset.mpr hu.2
    _ ≤ _ := List.toFinset_card_le _

/-- **Case B** of the supersaturation bound. -/
theorem supersat_caseB (g : Graph) (hB : 8 * (idEdges g).length < degen g ^ 3) :
    degen g ^ 2 * (degen g - 1) ^ 2 ≤ 16 * (cycles g 4).length := by
  have hN : (range (numV g)).Nonempty := by
    rw [nonempty_range_iff]
    intro h
    have : degen g = 0 := by simp [degen, h]
    rw [this] at hB
    simp at hB
  obtain ⟨vs, hvs, hD⟩ := exists_mem_eq_sup _ hN fun v => (outL g (peelPos g) v).length
  have hvsN := mem_range.mp hvs
  set D := degen g with hDdef
  change D = (outL g (peelPos g) vs).length at hD
  set W := (range (numV g)).filter fun u => peelPos g vs ≤ peelPos g u with hW
  have hWsub : W ⊆ range (numV g) := filter_subset _ _
  have hvW : vs ∈ W := mem_filter.mpr ⟨hvs, le_rfl⟩
  have hn1 : 1 ≤ W.card := card_pos.mpr ⟨vs, hvW⟩
  -- S0: minimum degree in the core
  have hS0 : ∀ w ∈ W, D ≤ (nbW (adjR g) W w).card := by
    intro w hw
    obtain ⟨hwN, hle⟩ := mem_filter.mp hw
    rw [hW, card_nbW_core, hD]
    exact peel_minDeg g hvsN (mem_range.mp hwN) hle
  -- S1
  have hS1 : W.card * D ≤ 2 * (idEdges g).length := by
    have h1 := card_nsmul_le_sum W (fun w => (nbW (adjR g) W w).card) D hS0
    have h2 : ∑ w ∈ W, (nbW (adjR g) W w).card ≤ ∑ w ∈ W, (nb g w).length :=
      sum_le_sum fun w _ => card_nbW_le W w
    have h3 : ∑ w ∈ W, (nb g w).length ≤ ∑ w ∈ range (numV g), (nb g w).length :=
      sum_le_sum_of_subset hWsub
    rw [sum_length_nb] at h3
    simp only [smul_eq_mul] at h1
    omega
  -- S2–S6
  have hS2 := sum_codW_ge (adjR g) W (symm_adjR g) hS0
  have hS3 := sum_codW_sq (adjR g) W
  have hQ : ∑ p ∈ W.offDiag, ((codW (adjR g) W p.1 p.2).offDiag).card ≤
      8 * (cycles g 4).length := by
    have := card_cfg_le hWsub
    rwa [cfg, card_sigma] at this
  refine caseB' D (idEdges g).length W.card (cycles g 4).length
    (∑ p ∈ W.offDiag, (codW (adjR g) W p.1 p.2).card) (W.card * W.card - W.card) hB hS1 hn1
    hS2 (by rw [Nat.mul_sub_one]) ?_
  refine hS3.trans (Nat.mul_le_mul_left _ ?_)
  omega

/-- **Supersaturation**: `2 D |E| ≤ 4 X + 9 t` whenever `|E|⁴ ≤ X³`, for the
degeneracy `D` of the peeling orientation and the number `t` of 4-cycles. -/
theorem degen_bound (g : Graph) {X : ℕ} (hX : (idEdges g).length ^ 4 ≤ X ^ 3) :
    2 * (degen g * (idEdges g).length) ≤ 4 * X + 9 * (cycles g 4).length :=
  final_bound _ _ _ _ hX (supersat_caseB g)

end STACS2027.Runtimes.C4
