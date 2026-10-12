module

public import Outerplanar.RAM.Poly3Main
import Mathlib.Tactic

/-!
# Phase P3 of the polygon solver: the first pass

* `toffInit_spec`: the table offsets `TOFF = tabOffs` (prefix sums of `k ^ |bnd s|`, the
  powers by `pow`), and the allocation of the tables `TAB`, `ARG` (`toffAt NS` cells each); a
  bounded triple (`HTB S`) for `S` at or above the end of `TOFF`.
-/

@[expose] public section

namespace STACS2027.RAM.P3

open STACS2027.Poly STACS2027.RAM.P1

variable {pg : Graph} {n k : ℕ}

/-! ### The table offsets -/

/-- The state of the offset loop after `x` segments. -/
def TInv (pg : Graph) (n k F₂ b : ℕ) (m₂ : ℕ → ℕ) (x : ℕ) (c : Config) : Prop :=
  (c.reg gTOFF = F₂ ∧ c.reg rFREE = F₂ + ((segOrder pg n).length + 1) ∧ c.reg rK = k ∧
    c.reg gBOFF = b ∧ c.reg rACC2 = toffAt pg n k x) ∧
  Arr c.mem F₂ ((tabOffs pg n k).take (x + 1)) ∧ SameOn (· < F₂) m₂ c.mem ∧
    ZeroFrom c.mem (F₂ + ((segOrder pg n).length + 1))

/-- The bound of one table offset. -/
def tToff (k : ℕ) : ℕ := Rb k * (5 * k + 10) + 14

theorem toffBody_spec {S F₂ b : ℕ} {m₂ : ℕ → ℕ} (hP : IsPolygon pg n)
    (hb : Arr m₂ b (bndOffs pg n k)) (hbF : b + ((segOrder pg n).length + 1) ≤ F₂)
    (hSz : F₂ + ((segOrder pg n).length + 1) ≤ S)
    (x : ℕ) (hx : x < (segOrder pg n).length) :
    HTB S toffBody
      (fun c => TInv pg n k F₂ b m₂ x c ∧ c.reg rX2 = x ∧ c.reg gNS = (segOrder pg n).length)
      (fun c => TInv pg n k F₂ b m₂ (x + 1) c ∧ c.reg rX2 = x ∧ c.reg gNS = (segOrder pg n).length)
      (tToff k) := by
  have hbo : (bndOffs pg n k).length = (segOrder pg n).length + 1 := by
    rw [bndOffs, length_prefixSums, List.length_map]
  have h₁ : HTB S toffRd
      (fun c => TInv pg n k F₂ b m₂ x c ∧ c.reg rX2 = x ∧ c.reg gNS = (segOrder pg n).length)
      (fun c => ((TInv pg n k F₂ b m₂ x c ∧ c.reg rX2 = x ∧ c.reg gNS = (segOrder pg n).length) ∧
        c.reg rN1 = x + 1) ∧ c.reg rPE = (bnd pg n k (segOrder pg n)[x]).length) 7 := by
    refine HTB.run_le (by decide) (by decide) fun c hc => ?_
    obtain ⟨⟨⟨_, _, _, hB, _⟩, _, hs, _⟩, hx2, _⟩ := id hc
    refine ⟨by addr_ok [toffRd, hB, hx2], ?_⟩
    have hag : Agree (wregs toffRd) c (RAM.run toffRd c) := agree_run (by decide) rfl rfl (by decide) c
    have hc' := (show Indep (wregs toffRd) (fun c => TInv pg n k F₂ b m₂ x c ∧ c.reg rX2 = x ∧
      c.reg gNS = (segOrder pg n).length) by unfold TInv; indep) c _ hag hc
    have hb' : Arr c.mem b (bndOffs pg n k) := hb.of_below hs (by rw [hbo]; exact hbF)
    have e1 : c.mem (b + x) = (((segOrder pg n).take x).map fun t => (bnd pg n k t).length).sum :=
      arr_prefixSums_seg_read _ hb' hx.le
    have e2 : c.mem (b + (x + 1)) =
        (((segOrder pg n).take x).map fun t => (bnd pg n k t).length).sum + (bnd pg n k (segOrder pg n)[x]).length := by
      rw [arr_prefixSums_seg_read _ hb' hx, sum_take_succ_seg _ hx]
    refine ⟨⟨hc', ?_⟩, ?_⟩
    all_goals simp +decide only [toffRd, run_seq', run_ld, run_addc, run_sub, setReg_reg,
      ↓reduceIte, setReg_mem, hB, hx2, e1, e2, Nat.add_sub_cancel_left]
  have h₂ := HTB.of_HT (S := S) rfl <|
    pow_spec (k := k) (e := (bnd pg n k (segOrder pg n)[x]).length)
    (fun c => ((TInv pg n k F₂ b m₂ x c ∧ c.reg rX2 = x ∧ c.reg gNS = (segOrder pg n).length) ∧
      c.reg rN1 = x + 1) ∧ c.reg rPE = (bnd pg n k (segOrder pg n)[x]).length)
    (by unfold TInv; indep) (fun c hc => ⟨hc.1.1.1.1.2.2.1, hc.2⟩)
  have h₃ : HTB S toffSt
      (fun c => (((TInv pg n k F₂ b m₂ x c ∧ c.reg rX2 = x ∧ c.reg gNS = (segOrder pg n).length) ∧
        c.reg rN1 = x + 1) ∧ c.reg rPE = (bnd pg n k (segOrder pg n)[x]).length) ∧ c.reg rPR = k ^ (bnd pg n k (segOrder pg n)[x]).length)
      (fun c => TInv pg n k F₂ b m₂ (x + 1) c ∧ c.reg rX2 = x ∧ c.reg gNS = (segOrder pg n).length) 3 := by
    refine HTB.run_le (by decide) (by decide) fun c hc => ?_
    obtain ⟨⟨⟨⟨⟨⟨hT, hF, hK, hB, hA⟩, ha, hs, hz⟩, hx2, hns⟩, hn1⟩, _⟩, hpr⟩ := hc
    refine ⟨by addr_ok [toffSt, hT, hn1], ?_⟩
    have hsucc := toffAt_succ (pg := pg) (n := n) (k := k) hx
    have htake : (tabOffs pg n k).take (x + 1 + 1) =
        (tabOffs pg n k).take (x + 1) ++ [toffAt pg n k (x + 1)] := by
      rw [List.take_succ_eq_append_getElem (by rw [length_tabOffs]; omega), ← getD_of_lt
        (by rw [length_tabOffs]; omega), getD_tabOffs (by omega)]
    simp only [toffSt, run_seq']
    rw [run_st (by decide)]
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
    all_goals simp +decide only [run_add, setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd,
      ↓reduceIte, hT, hF, hK, hB, hA, hpr, hn1, hx2, hns, hsucc]
    · rw [htake, hsucc]
      exact ha.upd_snoc (by rw [List.length_take, length_tabOffs]; omega)
    · exact hs.upd_of_ge (by omega) _
    · exact hz.upd (by omega)
  have := h₁.seq (h₂.seq h₃)
  refine this.weaken ?_
  have : (bnd pg n k (segOrder pg n)[x]).length * (5 * k + 10) ≤ Rb k * (5 * k + 10) :=
    Nat.mul_le_mul_right _ (length_bnd_le' hP (mem_segOrder.mp (List.getElem_mem hx)))
  unfold tToff; omega

/-- **The table offsets** and the allocation of the tables. -/
theorem toffInit_spec {S : ℕ} (hP : IsPolygon pg n) (F₂ b : ℕ) (m₂ : ℕ → ℕ)
    (hb : Arr m₂ b (bndOffs pg n k)) (hbF : b + ((segOrder pg n).length + 1) ≤ F₂)
    (hSz : F₂ + ((segOrder pg n).length + 1) ≤ S) :
    HTB S toffInit (fun c => (c.reg gNS = (segOrder pg n).length ∧ c.reg rK = k ∧ c.reg gBOFF = b) ∧
        c.reg rFREE = F₂ ∧ c.mem = m₂ ∧ ZeroFrom m₂ F₂)
      (fun c => (c.reg gTOFF = F₂ ∧ c.reg gTAB = F₂ + ((segOrder pg n).length + 1) ∧
        c.reg gARG = F₂ + ((segOrder pg n).length + 1) + toffAt pg n k (segOrder pg n).length ∧
        c.reg rFREE = F₂ + ((segOrder pg n).length + 1) + toffAt pg n k (segOrder pg n).length +
          toffAt pg n k (segOrder pg n).length) ∧
        Arr c.mem F₂ (tabOffs pg n k) ∧ SameOn (· < F₂) m₂ c.mem ∧ ZeroFrom c.mem (c.reg rFREE))
      ((segOrder pg n).length * (tToff k + 4) + 15) := by
  have h₀ : HTB S toffAlloc (fun c => (c.reg gNS = (segOrder pg n).length ∧ c.reg rK = k ∧
        c.reg gBOFF = b) ∧ c.reg rFREE = F₂ ∧ c.mem = m₂ ∧ ZeroFrom m₂ F₂)
      (fun c => TInv pg n k F₂ b m₂ 0 c ∧ c.reg gNS = (segOrder pg n).length) 6 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨⟨hns, hk, hB⟩, hF, hm, hz⟩ => ?_
    simp only [toffAlloc, run_seq']
    rw [run_alloc (by decide) (by decide)]
    have h0 : (tabOffs pg n k).take 1 = [0] := by
      have := getD_tabOffs (pg := pg) (n := n) (k := k) (j := 0) (by omega)
      rw [List.take_succ_eq_append_getElem (by rw [length_tabOffs]; omega), ← getD_of_lt
        (by rw [length_tabOffs]; omega), this]
      simp [toffAt]
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
    all_goals simp +decide only [run_addc, run_const, setReg_reg, setReg_mem, ↓reduceIte, hns, hk,
      hB, hF, hm, h0]
    · simp [toffAt]
    · exact arr_singleton.mpr (hz F₂ le_rfl)
    · exact SameOn.refl _ _
    · exact hz.mono (by omega)
  have hl := HTB.forUpC (S := S) (i := rX2) (n := gNS) (N := (segOrder pg n).length)
    (body := toffBody)
    (TInv pg n k F₂ b m₂) (tToff k) (by decide) (by decide) (by decide)
    (fun x => by unfold TInv; indep) (fun x hx => toffBody_spec hP hb hbF hSz x hx)
  have h₂ : HTB S tabAlloc (fun c => TInv pg n k F₂ b m₂ (segOrder pg n).length c ∧
        c.reg rX2 = (segOrder pg n).length ∧ c.reg gNS = (segOrder pg n).length)
      (fun c => (c.reg gTOFF = F₂ ∧ c.reg gTAB = F₂ + ((segOrder pg n).length + 1) ∧
        c.reg gARG = F₂ + ((segOrder pg n).length + 1) + toffAt pg n k (segOrder pg n).length ∧
        c.reg rFREE = F₂ + ((segOrder pg n).length + 1) + toffAt pg n k (segOrder pg n).length +
          toffAt pg n k (segOrder pg n).length) ∧
        Arr c.mem F₂ (tabOffs pg n k) ∧ SameOn (· < F₂) m₂ c.mem ∧ ZeroFrom c.mem (c.reg rFREE)) 6 := by
    refine HTB.of_HT rfl <| HT.run_le (by decide) (by decide)
      fun c ⟨⟨⟨hT, hF, _, _, hA⟩, ha, hs, hz⟩, _, _⟩ => ?_
    simp only [tabAlloc, run_seq']
    rw [run_alloc (by decide) (by decide), run_alloc (by decide) (by decide)]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, hs, ?_⟩
    all_goals simp +decide only [setReg_reg, setReg_mem, ↓reduceIte, hT, hF, hA]
    · rw [← length_tabOffs (pg := pg) (n := n) (k := k), List.take_length] at ha; exact ha
    · exact hz.mono (by omega)
  exact (h₀.seq (hl.seq h₂)).weaken (by omega)

end STACS2027.RAM.P3
