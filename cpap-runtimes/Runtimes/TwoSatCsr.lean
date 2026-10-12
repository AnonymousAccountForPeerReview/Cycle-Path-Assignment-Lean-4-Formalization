module

public import Runtimes.TwoSatProg
import Mathlib.Tactic

/-!
# Linear-time 2-SAT on the RAM: the out-neighbour lists (CSR)

From the arcs `AU[k] → AV[k]` (`k < M`) of `A = arcsOfCodes cl`, the machine builds the
out-neighbour lists `outOf A u` (`u < N`) in compressed sparse row form, as phase R1 of the
outerplanar package machine does for undirected edges:

* `stepDeg`: `DEG[AU[k]]++` for every arc (after `k` arcs `DEG` holds `cnt A k`, the
  out-degrees in `A.take k`);
* `stepPre`: `OFF[u + 1] := OFF[u] + DEG[u]`, so `OFF` holds the prefix sums `ps A`;
* `stepFill`: `ADJ[OFF[a] + FIL[a]++] := b` for every arc `a → b`; after `k` arcs the segment
  of `u` (from `ADJ + ps A u`) holds `outOf (A.take k) u`.

Abstract side: `outOf_take_succ`, `cnt_succ`, the prefix sums `ps` (`ps_succ`, `ps_mono`,
`ps_total`). Machine side: `stepCsr_spec`, ending in `CsrMem` (offsets and lists), with the
search arrays still zero.
-/

@[expose] public section

namespace STACS2027.Runtimes.TwoSat

open STACS2027.RAM

variable {S : ℕ}

/-! ### Out-neighbour lists of prefixes -/

theorem outOf_append (A₁ A₂ : List (ℕ × ℕ)) (u : ℕ) :
    outOf (A₁ ++ A₂) u = outOf A₁ u ++ outOf A₂ u := by
  simp [outOf, List.flatMap_append]

/-- `w` appended to the list of `u`. -/
def app (L : ℕ → List ℕ) (u w : ℕ) : ℕ → List ℕ := Function.update L u (L u ++ [w])

/-- The cell `u` incremented. -/
def bmp (f : ℕ → ℕ) (u : ℕ) : ℕ → ℕ := Function.update f u (f u + 1)

theorem outOf_take_succ {A : List (ℕ × ℕ)} {k : ℕ} (hk : k < A.length) :
    outOf (A.take (k + 1)) = app (outOf (A.take k)) A[k].1 A[k].2 := by
  funext u
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, outOf_append]
  simp only [app]
  by_cases h : u = A[k].1
  · subst h; simp [outOf]
  · rw [Function.update_of_ne h]; simp [outOf, Ne.symm h]

/-- The out-degree of `u` among the first `k` arcs. -/
def cnt (A : List (ℕ × ℕ)) (k u : ℕ) : ℕ := (outOf (A.take k) u).length

theorem cnt_zero (A : List (ℕ × ℕ)) : cnt A 0 = fun _ => 0 := by
  funext u; simp [cnt, outOf]

theorem length_outOf_take_le (A : List (ℕ × ℕ)) (k u : ℕ) :
    (outOf (A.take k) u).length ≤ (outOf A u).length := by
  have h := congrArg List.length (congrFun (congrArg outOf (List.take_append_drop k A)) u)
  rw [outOf_append, List.length_append] at h
  omega

theorem length_app (L : ℕ → List ℕ) (u w v : ℕ) :
    (app L u w v).length = bmp (fun x => (L x).length) u v := by
  simp only [app, bmp]
  by_cases h : v = u
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem cnt_succ {A : List (ℕ × ℕ)} {k : ℕ} (hk : k < A.length) :
    cnt A (k + 1) = bmp (cnt A k) A[k].1 := by
  funext u
  simp only [cnt, outOf_take_succ hk, length_app]
  rfl

/-! ### Prefix sums of the out-degrees -/

/-- The start of the list of `u` in the CSR array: the out-degrees below `u`, summed. -/
def ps (A : List (ℕ × ℕ)) (u : ℕ) : ℕ := ((List.range u).map fun v => (outOf A v).length).sum

theorem ps_succ (A : List (ℕ × ℕ)) (u : ℕ) : ps A (u + 1) = ps A u + (outOf A u).length := by
  simp [ps, List.range_succ]

theorem ps_mono (A : List (ℕ × ℕ)) {u v : ℕ} (h : u ≤ v) : ps A u ≤ ps A v := by
  induction v, h using Nat.le_induction with
  | base => exact le_rfl
  | succ v _ ih => rw [ps_succ]; omega

theorem ps_add_le (A : List (ℕ × ℕ)) {u v : ℕ} (h : u < v) : ps A u + (outOf A u).length ≤ ps A v := by
  rw [← ps_succ]; exact ps_mono A h

theorem sum_indicator (a N : ℕ) :
    ((List.range N).map fun u => if a = u then 1 else 0).sum = if a < N then 1 else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split_ifs <;> omega

/-- The out-degrees below `N` sum to the number of arcs (all tails below `N`). -/
theorem ps_total {A : List (ℕ × ℕ)} {N : ℕ} (h : ∀ e ∈ A, e.1 < N) : ps A N = A.length := by
  induction A with
  | nil => simp [ps, outOf]
  | cons e A ih =>
    have he := h e (by simp)
    have ih' := ih fun e' he' => h e' (by simp [he'])
    have hsplit : ∀ u, (outOf (e :: A) u).length = (if e.1 = u then 1 else 0) + (outOf A u).length := by
      intro u
      rw [show e :: A = [e] ++ A from rfl, outOf_append, List.length_append]
      by_cases h1 : e.1 = u <;> simp [outOf, h1]
    unfold ps at ih' ⊢
    simp only [hsplit, List.sum_map_add, sum_indicator] at ih' ⊢
    rw [ih']
    simp only [List.length_cons, he, ↓reduceIte]
    omega

/-- The CSR array from the segments. -/
theorem arr_csr {mm : ℕ → ℕ} {b : ℕ} {A : List (ℕ × ℕ)} {N : ℕ}
    (h : ∀ u, u < N → Arr mm (b + ps A u) (outOf A u)) :
    Arr mm b ((List.range N).flatMap (outOf A)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, arr_append]
    refine ⟨ih fun u hu => h u (by omega), ?_⟩
    have hl : ((List.range N).flatMap (outOf A)).length = ps A N := by
      simp [List.length_flatMap, ps]
    simpa [hl] using h N (by omega)

/-! ### The arcs of the codes -/

theorem au_eq {cl : List ℕ} {k : ℕ} (hk : k < (arcsOfCodes cl).length) :
    au cl k = (arcsOfCodes cl)[k].1 := by
  simp [au, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem av_eq {cl : List ℕ} {k : ℕ} (hk : k < (arcsOfCodes cl).length) :
    av cl k = (arcsOfCodes cl)[k].2 := by
  simp [av, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

/-! ### The program -/

/-- One arc of the degree pass: `DEG[AU[i]]++`. -/
def degBody : Stmt := .seq (ld sU tAU sI) (.seq (ld sX tDEG sU) (.seq (inc sX) (st tDEG sU sX)))
/-- Step 4a: the out-degrees. -/
def stepDeg : Stmt := forUp sI tM2 degBody

/-- One node of the prefix sums: `sAcc += DEG[i]; OFF[i + 1] := sAcc`. -/
def preBody : Stmt :=
  .seq (ld sX tDEG sI) (.seq (.add sAcc sAcc sX) (.seq (addc sP sI 1) (st tOFF sP sAcc)))
/-- Step 4b: the offsets. -/
def stepPre : Stmt := .seq (.const sAcc 0) (forUp sI tN2 preBody)

/-- One arc `a → b` of the fill pass: `ADJ[OFF[a] + FIL[a]] := b; FIL[a]++`. -/
def fillBody : Stmt :=
  .seq (ld sU tAU sI) (.seq (ld sV tAV sI) (.seq (ld sX tFIL sU) (.seq (ld sY tOFF sU)
    (.seq (.add sY sY sX) (.seq (st tADJ sY sV) (.seq (inc sX) (st tFIL sU sX)))))))
/-- Step 4c: the CSR array. -/
def stepFill : Stmt := forUp sI tM2 fillBody

/-- Step 4: the out-neighbour lists. -/
def stepCsr : Stmt := .seq stepDeg (.seq stepPre stepFill)

/-! ### Step 4a: the degrees -/

section csr

variable {n m : ℕ} {cl : List ℕ} {c₀ : Config}

/-- The memory during the degree pass, with the degree counts `f`. -/
structure DegMem (n m : ℕ) (cl : List ℕ) (c₀ : Config) (f : ℕ → ℕ) (mm : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem mm
  tau : Tab mm (bAU n (c₀.reg rFREE)) (2 * m) (au cl)
  tav : Tab mm (bAV n m (c₀.reg rFREE)) (2 * m) (av cl)
  tdeg : Tab mm (bDEG n m (c₀.reg rFREE)) (2 * n) f
  zero : ZeroFrom mm (bOFF n m (c₀.reg rFREE))

/-- The invariant of the degree pass after `k` arcs. -/
def DegInv (n m : ℕ) (cl : List ℕ) (c₀ : Config) (k : ℕ) (c : Config) : Prop :=
  Glob n m c₀ c ∧ DegMem n m cl c₀ (cnt (arcsOfCodes cl) k) c.mem

theorem DegMem.bmp {f : ℕ → ℕ} {mm : ℕ → ℕ} (h : DegMem n m cl c₀ f mm) {u : ℕ} (hu : u < 2 * n) :
    DegMem n m cl c₀ (TwoSat.bmp f u) (upd mm (bDEG n m (c₀.reg rFREE) + u) (f u + 1)) := by
  have hL := layout_eqs n m (c₀.reg rFREE)
  exact ⟨h.same.upd_of_ge (by omega) _, h.tau.upd_of_disjoint (by omega),
    h.tav.upd_of_disjoint (by omega), h.tdeg.upd rfl, h.zero.upd (by omega)⟩

theorem degBody_spec (hcl : cl.length = 2 * m) (hok : CodesOk n cl)
    (hS : endL n m (c₀.reg rFREE) ≤ S) (k : ℕ) (hk : k < 2 * m) :
    HTB S degBody (fun c => DegInv n m cl c₀ k c ∧ c.reg sI = k ∧ c.reg tM2 = 2 * m)
      (fun c => DegInv n m cl c₀ (k + 1) c ∧ c.reg sI = k ∧ c.reg tM2 = 2 * m) 8 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hM⟩, hi, hm⟩ => ?_
  have hA := length_arcsOfCodes m cl hcl
  have hu : au cl k < 2 * n := by
    rw [au_eq (by omega)]; exact (mem_arcsOfCodes hok _ (List.getElem_mem _)).1
  have hau := hM.tau.get (i := k) (by omega)
  have hdeg := hM.tdeg.get hu
  refine ⟨by
    have := fits hS
    addr_ok [degBody, hG.rau, hG.rdeg, hi, hau], ?_⟩
  refine ⟨⟨(Glob.regIndep n m c₀).run_of_sub (by decide) (by decide) hG, ?_⟩, ?_, ?_⟩ <;>
    simp only [degBody, run_seq', run_ld, run_inc (show sX ≠ rT by decide),
      run_st (show sX ≠ rT by decide)]
  · have := hM.bmp hu
    have e : cnt (arcsOfCodes cl) (k + 1) = bmp (cnt (arcsOfCodes cl) k) (au cl k) := by
      rw [cnt_succ (by omega), au_eq (by omega)]
    rw [← e] at this
    simpa +decide [hG.rau, hG.rdeg, hi, hau, hdeg] using this
  · simp +decide [hi]
  · simp +decide [hm]

theorem stepDeg_spec (hcl : cl.length = 2 * m) (hok : CodesOk n cl)
    (hS : endL n m (c₀.reg rFREE) ≤ S) :
    HTB S stepDeg (fun c => DegInv n m cl c₀ 0 c ∧ c.reg tM2 = 2 * m)
      (fun c => DegInv n m cl c₀ (2 * m) c ∧ c.reg sI = 2 * m ∧ c.reg tM2 = 2 * m)
      (2 * m * 12 + 3) :=
  HTB.forUpC (i := sI) (n := tM2) (N := 2 * m) (body := degBody) (DegInv n m cl c₀) 8
    (by decide) (by decide) (by decide) (fun j => by indep [DegInv, glob_iff])
    (fun j hj => degBody_spec hcl hok hS j hj)

/-! ### Step 4b: the offsets -/

/-- The memory during the prefix sums, after `v` nodes. -/
structure PreMem (n m : ℕ) (cl : List ℕ) (c₀ : Config) (v : ℕ) (mm : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem mm
  tau : Tab mm (bAU n (c₀.reg rFREE)) (2 * m) (au cl)
  tav : Tab mm (bAV n m (c₀.reg rFREE)) (2 * m) (av cl)
  tdeg : Tab mm (bDEG n m (c₀.reg rFREE)) (2 * n) fun u => (outOf (arcsOfCodes cl) u).length
  toff : Tab mm (bOFF n m (c₀.reg rFREE)) (2 * n + 1)
    fun i => if i ≤ v then ps (arcsOfCodes cl) i else 0
  zero : ZeroFrom mm (bFIL n m (c₀.reg rFREE))

/-- The invariant of the prefix sums after `v` nodes. -/
def PreInv (n m : ℕ) (cl : List ℕ) (c₀ : Config) (v : ℕ) (c : Config) : Prop :=
  Glob n m c₀ c ∧ c.reg sAcc = ps (arcsOfCodes cl) v ∧ PreMem n m cl c₀ v c.mem

theorem PreMem.snoc {v : ℕ} {mm : ℕ → ℕ} (h : PreMem n m cl c₀ v mm) (hv : v < 2 * n) :
    PreMem n m cl c₀ (v + 1)
      (upd mm (bOFF n m (c₀.reg rFREE) + (v + 1))
        (ps (arcsOfCodes cl) v + (outOf (arcsOfCodes cl) v).length)) := by
  have hL := layout_eqs n m (c₀.reg rFREE)
  refine ⟨h.same.upd_of_ge (by omega) _, h.tau.upd_of_disjoint (by omega),
    h.tav.upd_of_disjoint (by omega), h.tdeg.upd_of_disjoint (by omega), ?_,
    h.zero.upd (by omega)⟩
  refine (h.toff.upd rfl).congr_fun fun i _ => ?_
  rw [← ps_succ]
  by_cases hi : i = v + 1
  · subst hi; simp
  · rw [Function.update_of_ne hi]
    by_cases hiv : i ≤ v
    · simp [hiv, show i ≤ v + 1 by omega]
    · simp [hiv, show ¬ i ≤ v + 1 by omega]

theorem preBody_spec (hS : endL n m (c₀.reg rFREE) ≤ S) (v : ℕ) (hv : v < 2 * n) :
    HTB S preBody (fun c => PreInv n m cl c₀ v c ∧ c.reg sI = v ∧ c.reg tN2 = 2 * n)
      (fun c => PreInv n m cl c₀ (v + 1) c ∧ c.reg sI = v ∧ c.reg tN2 = 2 * n) 7 :=
  HTB.of_HT_addrOK (by decide) (fun c ⟨⟨hG, _, _⟩, hi, _⟩ => by
    have := fits hS
    addr_ok [preBody, hG.rdeg, hG.roff, hi]) <| by
  refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hacc, hM⟩, hi, hn⟩ => ?_
  have hd := hM.tdeg.get hv
  refine ⟨⟨(Glob.regIndep n m c₀).run_of_sub (by decide) (by decide) hG, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [preBody, run_seq', run_ld, run_add, run_addc (show sI ≠ rT by decide),
      run_st (show sAcc ≠ rT by decide)]
  · simp +decide [hd, hacc, ps_succ, hG.rdeg, hi]
  · simpa +decide [hd, hacc, hG.roff, hG.rdeg, hi] using hM.snoc hv
  · simp +decide [hi]
  · simp +decide [hn]

theorem stepPre_spec (hcl : cl.length = 2 * m) (hS : endL n m (c₀.reg rFREE) ≤ S) :
    HTB S stepPre (fun c => DegInv n m cl c₀ (2 * m) c ∧ c.reg sI = 2 * m ∧ c.reg tM2 = 2 * m)
      (fun c => PreInv n m cl c₀ (2 * n) c ∧ c.reg sI = 2 * n ∧ c.reg tN2 = 2 * n)
      (1 + (2 * n * 11 + 3)) := by
  have h0 : HTB S (.const sAcc 0) (fun c => DegInv n m cl c₀ (2 * m) c ∧ c.reg sI = 2 * m ∧
      c.reg tM2 = 2 * m) (fun c => PreInv n m cl c₀ 0 c ∧ c.reg tN2 = 2 * n) 1 :=
      HTB.of_HT rfl <| by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨hG, hM⟩, _, _⟩ => ?_
    have hL := layout_eqs n m (c₀.reg rFREE)
    have hA := length_arcsOfCodes m cl hcl
    simp only [run_const]
    refine ⟨⟨(Glob.regIndep n m c₀).setReg (by decide) _ hG, by simp +decide [ps], ?_⟩, by
      simp +decide [hG.rn2]⟩
    simp only [setReg_mem]
    refine ⟨hM.same, hM.tau, hM.tav, ?_, ?_, hM.zero.mono (by omega)⟩
    · refine hM.tdeg.congr_fun fun u _ => ?_
      rw [← hA, cnt, List.take_length]
    · intro i hi
      rw [hM.zero.get (by omega)]
      by_cases h : i ≤ 0
      · simp [show i = 0 by omega, ps]
      · simp [h]
  have hl := HTB.forUpC (i := sI) (n := tN2) (N := 2 * n) (body := preBody) (PreInv n m cl c₀) 7
    (by decide) (by decide) (by decide) (fun j => by indep [PreInv, glob_iff])
    (fun j hj => preBody_spec hS j hj)
  exact h0.seq hl

/-! ### Step 4c: the CSR array -/

/-- The memory during the fill pass, with the lists `L` filled in so far. -/
structure FillMem (n m : ℕ) (cl : List ℕ) (c₀ : Config) (L : ℕ → List ℕ) (mm : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem mm
  tau : Tab mm (bAU n (c₀.reg rFREE)) (2 * m) (au cl)
  tav : Tab mm (bAV n m (c₀.reg rFREE)) (2 * m) (av cl)
  toff : Tab mm (bOFF n m (c₀.reg rFREE)) (2 * n + 1) (ps (arcsOfCodes cl))
  tfil : Tab mm (bFIL n m (c₀.reg rFREE)) (2 * n) fun u => (L u).length
  adj : ∀ u, u < 2 * n → Arr mm (bADJ n m (c₀.reg rFREE) + ps (arcsOfCodes cl) u) (L u)
  len : ∀ u, u < 2 * n → (L u).length ≤ (outOf (arcsOfCodes cl) u).length
  zero : ZeroFrom mm (bLAB n m (c₀.reg rFREE))

/-- The invariant of the fill pass after `k` arcs. -/
def FillInv (n m : ℕ) (cl : List ℕ) (c₀ : Config) (k : ℕ) (c : Config) : Prop :=
  Glob n m c₀ c ∧ FillMem n m cl c₀ (outOf ((arcsOfCodes cl).take k)) c.mem

theorem FillMem.app {L : ℕ → List ℕ} {mm : ℕ → ℕ} (h : FillMem n m cl c₀ L mm)
    (hcl : cl.length = 2 * m) (hok : CodesOk n cl) {u : ℕ} (hu : u < 2 * n)
    (hlt : (L u).length < (outOf (arcsOfCodes cl) u).length) (w : ℕ) :
    FillMem n m cl c₀ (TwoSat.app L u w)
      (upd (upd mm (bADJ n m (c₀.reg rFREE) + (ps (arcsOfCodes cl) u + (L u).length)) w)
        (bFIL n m (c₀.reg rFREE) + u) ((L u).length + 1)) := by
  have hL := layout_eqs n m (c₀.reg rFREE)
  have hA := length_arcsOfCodes m cl hcl
  have hps : ps (arcsOfCodes cl) (2 * n) = 2 * m := by
    rw [ps_total (fun e he => (mem_arcsOfCodes hok e he).1), hA]
  have hu1 := ps_add_le (arcsOfCodes cl) (show u < u + 1 by omega)
  have huN := ps_mono (arcsOfCodes cl) (show u + 1 ≤ 2 * n by omega)
  rw [ps_succ] at huN
  refine ⟨(h.same.upd_of_ge (by omega) _).upd_of_ge (by omega) _,
    (h.tau.upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    (h.tav.upd_of_disjoint (by omega)).upd_of_disjoint (by omega),
    (h.toff.upd_of_disjoint (by omega)).upd_of_disjoint (by omega), ?_, ?_, ?_,
    (h.zero.upd (by omega)).upd (by omega)⟩
  · refine ((h.tfil.upd_of_disjoint (by omega)).upd rfl).congr_fun fun v _ => ?_
    rw [length_app]; rfl
  · intro v hv
    by_cases hvu : v = u
    · subst hvu
      simp only [TwoSat.app, Function.update_self]
      exact (h.adj v hv).upd_snoc (by omega) |>.upd_of_disjoint (by simp; omega)
    · simp only [TwoSat.app, Function.update_of_ne hvu]
      have hlv := h.len v hv
      refine ((h.adj v hv).upd_of_disjoint ?_).upd_of_disjoint (by omega)
      rcases Nat.lt_or_gt_of_ne hvu with hvu' | hvu'
      · have := ps_add_le (arcsOfCodes cl) hvu'
        right; omega
      · have := ps_mono (arcsOfCodes cl) (show u + 1 ≤ v by omega)
        rw [ps_succ] at this
        left; omega
  · intro v hv
    by_cases hvu : v = u
    · subst hvu; simp only [TwoSat.app, Function.update_self, List.length_append,
        List.length_singleton]; omega
    · simp only [TwoSat.app, Function.update_of_ne hvu]; exact h.len v hv

theorem fillBody_spec (hcl : cl.length = 2 * m) (hok : CodesOk n cl)
    (hS : endL n m (c₀.reg rFREE) ≤ S) (k : ℕ) (hk : k < 2 * m) :
    HTB S fillBody (fun c => FillInv n m cl c₀ k c ∧ c.reg sI = k ∧ c.reg tM2 = 2 * m)
      (fun c => FillInv n m cl c₀ (k + 1) c ∧ c.reg sI = k ∧ c.reg tM2 = 2 * m) 16 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hM⟩, hi, hm⟩ => ?_
  have hA := length_arcsOfCodes m cl hcl
  have hkA : k < (arcsOfCodes cl).length := by omega
  have hu : (arcsOfCodes cl)[k].1 < 2 * n := (mem_arcsOfCodes hok _ (List.getElem_mem _)).1
  have hau := hM.tau.get (i := k) (by omega)
  have hav := hM.tav.get (i := k) (by omega)
  rw [au_eq hkA] at hau
  rw [av_eq hkA] at hav
  have hfil := hM.tfil.get hu
  have hoff := hM.toff.get (i := (arcsOfCodes cl)[k].1) (by omega)
  have hsucc := outOf_take_succ hkA
  have hlt : (outOf ((arcsOfCodes cl).take k) (arcsOfCodes cl)[k].1).length <
      (outOf (arcsOfCodes cl) (arcsOfCodes cl)[k].1).length := by
    have h1 := length_outOf_take_le (arcsOfCodes cl) (k + 1) (arcsOfCodes cl)[k].1
    rw [hsucc] at h1
    simp only [TwoSat.app, Function.update_self, List.length_append, List.length_singleton] at h1
    omega
  refine ⟨by
    have := fits hS
    have hps : ps (arcsOfCodes cl) (2 * n) = 2 * m := by
      rw [ps_total (fun e he => (mem_arcsOfCodes hok e he).1), hA]
    have hu1 := ps_mono (arcsOfCodes cl) (show (arcsOfCodes cl)[k].1 + 1 ≤ 2 * n by omega)
    rw [ps_succ] at hu1
    have hlen := hM.len _ hu
    addr_ok [fillBody, hG.rau, hG.rav, hG.rfil, hG.roff, hG.radj, hi, hau, hav, hfil, hoff], ?_⟩
  refine ⟨⟨(Glob.regIndep n m c₀).run_of_sub (by decide) (by decide) hG, ?_⟩, ?_, ?_⟩ <;>
    simp only [fillBody, run_seq', run_ld, run_add, run_inc (show sX ≠ rT by decide),
      run_st (show sV ≠ rT by decide), run_st (show sX ≠ rT by decide)]
  · have := hM.app hcl hok hu hlt (arcsOfCodes cl)[k].2
    rw [← hsucc] at this
    simpa +decide [hG.rau, hG.rav, hG.rfil, hG.roff, hG.radj, hi, hau, hav, hfil, hoff] using this
  · simp +decide [hi]
  · simp +decide [hm]

theorem stepFill_spec (hcl : cl.length = 2 * m) (hok : CodesOk n cl)
    (hS : endL n m (c₀.reg rFREE) ≤ S) :
    HTB S stepFill (fun c => FillInv n m cl c₀ 0 c ∧ c.reg tM2 = 2 * m)
      (fun c => FillInv n m cl c₀ (2 * m) c ∧ c.reg sI = 2 * m ∧ c.reg tM2 = 2 * m)
      (2 * m * 20 + 3) :=
  HTB.forUpC (i := sI) (n := tM2) (N := 2 * m) (body := fillBody) (FillInv n m cl c₀) 16
    (by decide) (by decide) (by decide) (fun j => by indep [FillInv, glob_iff])
    (fun j hj => fillBody_spec hcl hok hS j hj)

/-! ### Step 4 -/

/-- The CSR arrays, fixed from the end of step 4 on. -/
structure CsrMem (n m : ℕ) (cl : List ℕ) (c₀ : Config) (mm : ℕ → ℕ) : Prop where
  same : SameOn (· < c₀.reg rFREE) c₀.mem mm
  toff : Tab mm (bOFF n m (c₀.reg rFREE)) (2 * n + 1) (ps (arcsOfCodes cl))
  adj : ∀ u, u < 2 * n → Arr mm (bADJ n m (c₀.reg rFREE) + ps (arcsOfCodes cl) u)
    (outOf (arcsOfCodes cl) u)

/-- Stores into the arrays of the search keep the CSR arrays. -/
theorem CsrMem.upd {mm : ℕ → ℕ} (h : CsrMem n m cl c₀ mm) (hcl : cl.length = 2 * m)
    (hok : CodesOk n cl) {a : ℕ} (ha : bLAB n m (c₀.reg rFREE) ≤ a) (v : ℕ) :
    CsrMem n m cl c₀ (RAM.upd mm a v) := by
  have hL := layout_eqs n m (c₀.reg rFREE)
  have hA := length_arcsOfCodes m cl hcl
  have hps : ps (arcsOfCodes cl) (2 * n) = 2 * m := by
    rw [ps_total (fun e he => (mem_arcsOfCodes hok e he).1), hA]
  refine ⟨h.same.upd_of_ge (by omega) _, h.toff.upd_of_disjoint (by omega), fun u hu => ?_⟩
  have := ps_mono (arcsOfCodes cl) (show u + 1 ≤ 2 * n by omega)
  rw [ps_succ] at this
  exact (h.adj u hu).upd_of_disjoint (by omega)

/-- **Step 4**: the out-neighbour lists, from the arcs. -/
theorem stepCsr_spec (hcl : cl.length = 2 * m) (hok : CodesOk n cl)
    (hS : endL n m (c₀.reg rFREE) ≤ S) :
    HTB S stepCsr (fun c => ArcInv n m cl c₀ m c ∧ c.reg tM = m)
      (fun c => Glob n m c₀ c ∧ CsrMem n m cl c₀ c.mem ∧ ZeroFrom c.mem (bLAB n m (c₀.reg rFREE)))
      (2 * m * 12 + 3 + (1 + (2 * n * 11 + 3) + (2 * m * 20 + 3))) := by
  have h0 := (stepDeg_spec (c₀ := c₀) hcl hok hS).pre (P' := fun c => ArcInv n m cl c₀ m c ∧
      c.reg tM = m) fun c ⟨⟨hG, hM⟩, _⟩ => by
    have hL := layout_eqs n m (c₀.reg rFREE)
    refine ⟨⟨hG, hM.same, hM.tau, hM.tav, ?_, hM.zero.mono (by omega)⟩, hG.rm2⟩
    rw [cnt_zero]; exact hM.zero.tab (by omega) _
  have h3 := (stepPre_spec (n := n) (c₀ := c₀) hcl hS).post (Q' := fun c => FillInv n m cl c₀ 0 c ∧
      c.reg tM2 = 2 * m) fun c ⟨⟨hG, _, hM⟩, _, _⟩ => by
    have hL := layout_eqs n m (c₀.reg rFREE)
    refine ⟨⟨hG, hM.same, hM.tau, hM.tav, hM.toff.congr_fun fun i hi => by
      simp [show i ≤ 2 * n by omega], ?_, fun v _ => by simp [outOf], fun v _ => by simp [outOf],
      hM.zero.mono (by omega)⟩, hG.rm2⟩
    simpa [outOf] using hM.zero.tab (b := bFIL n m (c₀.reg rFREE)) le_rfl (2 * n)
  have h4 := (stepFill_spec (c₀ := c₀) hcl hok hS).post (Q' := fun c => Glob n m c₀ c ∧
      CsrMem n m cl c₀ c.mem ∧ ZeroFrom c.mem (bLAB n m (c₀.reg rFREE))) fun c ⟨⟨hG, hM⟩, _, _⟩ => by
    have hA := length_arcsOfCodes m cl hcl
    rw [← hA, List.take_length] at hM
    exact ⟨hG, ⟨hM.same, hM.toff, hM.adj⟩, hM.zero⟩
  exact h0.seq (h3.seq h4)

end csr

end STACS2027.Runtimes.TwoSat
