module

public import Outerplanar.RAM.Poly3Sel
import Mathlib.Tactic

/-!
# Phase P3 of the polygon solver: the odometer and the powers of `k`

* `odo_spec`: the odometer `odo` replaces the base-`k` digits `ds` at `rOB` (`rOL` of them) by
  `odoL k ds` (one more, `odoL_cfg`). The memory is described by an assertion `Fr ds m` on the
  digits that survives every store into the digits (`Fr (ds.set t v) (upd m (ob + t) v)`), so
  that the caller keeps its other memory facts;
* `pow_spec`: `pow` computes `k ^ reg rPE` into `rPR` by repeated multiplication (memory-free:
  an `HT` triple, lifted by `HTB.of_HT`).

The odometer accesses only its digits: a bounded triple (`HTB S`) for `ob + |ds| ≤ S`.
-/

@[expose] public section

namespace STACS2027.RAM.P3

open STACS2027.Poly STACS2027.RAM.P1

/-! ### The odometer -/

/-- The state of the odometer after `t` digits. -/
def OdoSt (k : ℕ) (Fr : List ℕ → (ℕ → ℕ) → Prop) (ds : List ℕ) (t : ℕ) (c : Config) : Prop :=
  ∃ pre cy, pre.length = t ∧ Fr (pre ++ ds.drop t) c.mem ∧ pre ++ odoc k cy (ds.drop t) = odoL k ds ∧
    c.reg rCY = cy ∧ (cy = 0 ∨ cy = 1)

theorem odoBody_spec {S k ob : ℕ} {ds : List ℕ} (G : Config → Prop) (hG : RegIndep (wregs odo) G)
    (hGr : ∀ c, G c → c.reg rOB = ob ∧ c.reg rK = k)
    (Fr : List ℕ → (ℕ → ℕ) → Prop) (hrd : ∀ l m, Fr l m → Arr m ob l)
    (hupd : ∀ l m t v, Fr l m → t < l.length → Fr (l.set t v) (upd m (ob + t) v))
    (hS : ob + ds.length ≤ S) (t : ℕ) (ht : t < ds.length) :
    HTB S odoBody (fun c => (G c ∧ OdoSt k Fr ds t c) ∧ c.reg rOT = t ∧ c.reg rOL = ds.length)
      (fun c => (G c ∧ OdoSt k Fr ds (t + 1) c) ∧ c.reg rOT = t ∧ c.reg rOL = ds.length) 15 := by
  refine HTB.run_le (by decide) (by decide)
    fun c ⟨⟨hg, pre, cy, hl, hfr, heq, hcy, hc01⟩, hot, hol⟩ => ?_
  obtain ⟨hob, hk⟩ := hGr c hg
  refine ⟨by addr_ok [odoBody, hob, hot], ?_⟩
  have hdrop : ds.drop t = ds[t] :: ds.drop (t + 1) := List.drop_eq_getElem_cons ht
  have hd : c.mem (c.reg rOB + c.reg rOT) = ds[t] := by
    rw [hob, hot, (hrd _ _ hfr).get (by simp [hl]; omega)]
    rw [List.getElem_append_right (by omega), List.getElem_drop]
    congr 1; omega
  have hsub : ∀ r ∈ wregs odoBody, r ∈ wregs odo := by decide +kernel
  have hreg : ∀ r, r ∉ wregs odo → (RAM.run odoBody c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) (fun h => hr (hsub r h)) c
  refine ⟨⟨hG c _ hreg hg, ?_⟩, by rw [run_reg_of_not_mem (by decide) (by decide) c]; exact hot,
    by rw [run_reg_of_not_mem (by decide) (by decide) c]; exact hol⟩
  rcases hc01 with rfl | rfl
  · -- no carry: nothing changes
    have hrun : RAM.run odoBody c = c := by simp [odoBody, hcy]
    rw [hrun]
    refine ⟨pre ++ [ds[t]], 0, by simp [hl], ?_, ?_, hcy, Or.inl rfl⟩
    · rw [List.append_assoc, List.singleton_append, ← hdrop]; exact hfr
    · rw [← heq, hdrop, odoc_zero, odoc_zero, List.append_assoc, List.singleton_append]
  · have hrun : RAM.run odoBody c = RAM.run (.seq (ld rOD rOB rOT) (.seq (inc rOD)
        (.seq (ifEq rOD rK (.const rOD 0) (.const rCY 0)) (st rOB rOT rOD)))) c := by
      simp [odoBody, hcy]
    rw [hrun]
    simp only [run_seq']
    rw [run_ifEq (by decide) (by decide)]
    simp +decide only [run_ld, run_inc, setReg_reg, ↓reduceIte, hd, hk]
    have hset : (pre ++ ds.drop t).set t = fun v => (pre ++ [v]) ++ ds.drop (t + 1) := by
      funext v
      rw [hdrop]
      have := set_middle pre (ds.drop (t + 1)) ds[t] v
      rw [hl] at this
      exact this
    by_cases hdk : ds[t] + 1 = k
    · simp +decide only [hdk, ↓reduceIte, run_const, run_st, setReg_reg, hob, hot]
      refine ⟨pre ++ [0], 1, by simp [hl], ?_, ?_, ?_, Or.inr rfl⟩
      · have := hupd _ _ t 0 hfr (by simp [hl]; omega)
        rw [hset] at this; exact this
      · rw [← heq, hdrop]; simp [odoc, odoL, hdk]
      · simp +decide [hcy]
    · simp +decide only [hdk, ↓reduceIte, run_const, run_st, setReg_reg, hob, hot]
      refine ⟨pre ++ [ds[t] + 1], 0, by simp [hl], ?_, ?_, ?_, Or.inl rfl⟩
      · have := hupd _ _ t (ds[t] + 1) hfr (by simp [hl]; omega)
        rw [hset] at this; exact this
      · rw [← heq, hdrop]; simp [odoc, odoL, hdk]
      · simp +decide

/-- **The odometer**: the digits `ds` at `rOB` become `odoL k ds`. -/
theorem odo_spec {S k ob : ℕ} {ds : List ℕ} (G : Config → Prop) (hG : RegIndep (wregs odo) G)
    (hGr : ∀ c, G c → c.reg rOB = ob ∧ c.reg rOL = ds.length ∧ c.reg rK = k)
    (Fr : List ℕ → (ℕ → ℕ) → Prop) (hrd : ∀ l m, Fr l m → Arr m ob l)
    (hupd : ∀ l m t v, Fr l m → t < l.length → Fr (l.set t v) (upd m (ob + t) v))
    (hS : ob + ds.length ≤ S) :
    HTB S odo (fun c => G c ∧ Fr ds c.mem) (fun c => G c ∧ Fr (odoL k ds) c.mem)
      (ds.length * 19 + 4) := by
  have hGi : Indep [rOT, rT] G := hG.indep.mono (by decide +kernel)
  have hl := HTB.forUpC (S := S) (i := rOT) (n := rOL) (N := ds.length) (body := odoBody)
    (fun t c => G c ∧ OdoSt k Fr ds t c) 15 (by decide) (by decide) (by decide)
    (fun t c c' hA ⟨hg, pre, cy, h1, h2, h3, h4, h5⟩ =>
      ⟨hGi c c' hA hg, pre, cy, h1, by rw [hA.mem]; exact h2, h3,
        by rw [hA.reg _ (by decide)]; exact h4, h5⟩)
    (fun t ht => odoBody_spec G hG (fun c hc => ⟨(hGr c hc).1, (hGr c hc).2.2⟩) Fr hrd hupd hS t ht)
  have h₀ : HTB S (.const rCY 1) (fun c => G c ∧ Fr ds c.mem)
      (fun c => (G c ∧ OdoSt k Fr ds 0 c) ∧ c.reg rOL = ds.length) 1 :=
    HTB.of_HT rfl <| HT.run_le (by decide) le_rfl fun c ⟨hg, hfr⟩ => by
      refine ⟨⟨hG.setReg (by decide) _ hg, [], 1, rfl, by simpa using hfr, by simp [odoc], by simp,
        Or.inr rfl⟩, ?_⟩
      simp +decide [(hGr c hg).2.1]
  refine (h₀.seq hl).mono (fun _ h => h) ?_ (by omega)
  rintro c ⟨⟨hg, pre, cy, h1, h2, h3, -, -⟩, -, -⟩
  refine ⟨hg, ?_⟩
  rw [List.drop_length, odoc_nil, List.append_nil] at h3
  rw [List.drop_length, List.append_nil, h3] at h2
  exact h2

/-! ### Powers of `k` -/

/-- **Powers**: `pow` computes `k ^ reg rPE` into `rPR`. -/
theorem pow_spec {k e : ℕ} (G : Config → Prop) (hG : Indep (wregs pow) G)
    (hGr : ∀ c, G c → c.reg rK = k ∧ c.reg rPE = e) :
    HT pow G (fun c => G c ∧ c.reg rPR = k ^ e) (e * (5 * k + 10) + 4) := by
  have hl := HT.forUp (i := rPT) (n := rPE) (N := e) (body := powBody)
    (fun t c => G c ∧ c.reg rPR = k ^ t) (fun _ => 5 * k + 6) (by decide) (by decide) (by decide)
    (fun t => by indepG hG) (fun t _ => by
      have h₁ := HT.mul (P := fun c => (G c ∧ c.reg rPR = k ^ t) ∧ c.reg rPT = t ∧ c.reg rPE = e)
        (d := rM) (a := rPR) (b := rK) (k := rMK) (x := k ^ t) (y := k) (by decide) (by indepG hG)
        (fun c hc => hc.1.2) (fun c hc => (hGr c hc.1.1).1)
      have h₂ : HT (mov rPR rM) (fun c => ((G c ∧ c.reg rPR = k ^ t) ∧ c.reg rPT = t ∧ c.reg rPE = e) ∧
          c.reg rM = k ^ t * k)
          (fun c => (G c ∧ c.reg rPR = k ^ (t + 1)) ∧ c.reg rPT = t ∧ c.reg rPE = e) 2 := by
        refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hg, _⟩, hpt, hpe⟩, hm⟩ => ?_
        have hag : Agree (wregs pow) c (RAM.run (mov rPR rM) c) :=
          agree_run (by decide) rfl rfl (by decide) c
        refine ⟨⟨hG c _ hag hg, ?_⟩, ?_, ?_⟩
        all_goals simp +decide only [run_mov, setReg_reg, ↓reduceIte, hm, hpt, hpe, pow_succ]
      exact (h₁.seq h₂).weaken (by omega))
  have h₀ : HT (.const rPR 1) G (fun c => (G c ∧ c.reg rPR = k ^ 0) ∧ c.reg rPE = e) 1 :=
    HT.run_le (by decide) le_rfl fun c hg => by
      have hag : Agree (wregs pow) c (RAM.run (.const rPR 1) c) :=
        agree_run (by decide) rfl rfl (by decide) c
      refine ⟨⟨hG c _ hag hg, by simp +decide⟩, ?_⟩
      simp +decide [(hGr c hg).2]
  refine (h₀.seq hl).mono (fun _ h => h) (fun c h => h.1) ?_
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have : e * (5 * k + 6 + 4) = e * (5 * k + 10) := by ring
  omega

/-- **`dst := k ^ reg src`.** -/
theorem powTo_spec {k e dst src : ℕ} (G : Config → Prop)
    (hG : Indep (rT :: rPE :: dst :: wregs pow) G)
    (hGr : ∀ c, G c → c.reg rK = k ∧ c.reg src = e) (hsrc : src ≠ rT)
    (hdst : dst ≠ rT) (hdst' : dst ≠ rPR) :
    HT (powTo dst src) G (fun c => G c ∧ c.reg dst = k ^ e) (e * (5 * k + 10) + 8) := by
  have h₁ := HT.mov (P := G) (d := rPE) (a := src) (x := e) hsrc
    (hG.mono fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)
    (fun c hc => (hGr c hc).2)
  have h₂ := pow_spec (k := k) (e := e) (fun c => G c ∧ c.reg rPE = e)
    (fun c c' hA ⟨hg, he⟩ => ⟨hG c c' (hA.mono fun r hr => List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) hg,
      by rw [hA.reg _ (by decide)]; exact he⟩)
    (fun c hc => ⟨(hGr c hc.1).1, hc.2⟩)
  have h₃ : HT (mov dst rPR) (fun c => (G c ∧ c.reg rPE = e) ∧ c.reg rPR = k ^ e)
      (fun c => G c ∧ c.reg dst = k ^ e) 2 := by
    refine HT.run_le (by simp) (by simp) fun c ⟨⟨hg, _⟩, hp⟩ => ?_
    have hag : Agree (rT :: rPE :: dst :: wregs pow) c (RAM.run (mov dst rPR) c) :=
      agree_run (by simp) rfl rfl (fun r hr => by
        simp only [wregs_mov, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) c
    refine ⟨hG c _ hag hg, ?_⟩
    rw [run_mov (by decide)]
    simp [hp]
  exact (h₁.seq (h₂.seq h₃)).weaken (by omega)

end STACS2027.RAM.P3
