module

public import Outerplanar.RAM.Poly1Enum
import Mathlib.Tactic

/-!
# Phase P1 of the polygon solver, stages C and D: the segment order and the segment ids

* Stage C (`stageC`): a stable counting sort of the enumerated segments by size
  (`ord3 pg n`, at `rORD3`), so that reading the enumerated fields through it gives
  `segOrder pg n` (`getD_ord3`); the ends of the segments in this order are gathered into the
  interface arrays `gSA`, `gSB` (`stageC_spec`).
* Stage D (`stageD`): the inverse permutation of `ord3`, shifted by one: `POS[0] = 0` and
  `POS[e + 1] = 1 +` the index in `segOrder` of the enumerated segment `e` (`posId`), at `rPOS`
  (`|segOrder| + 1` fresh cells, `POS[ORD3[t] + 1] := t + 1`, `posPart_succ`); it translates the
  enumeration ids of stage B into segment ids (`stageD_spec`).
-/

@[expose] public section

namespace STACS2027.RAM.P1

open STACS2027.Poly

/-! ### Registers and programs -/

/-- Base of the indices of the enumerated segments in `segOrder` order. -/
abbrev rORD3 : ℕ := 98
/-- Base of the segment ids of the enumerated segments (`|segOrder| + 1` cells). -/
abbrev rPOS : ℕ := 97
/-- Loop counter of stage D. -/
abbrev rDT : ℕ := 134
/-- Temporary. -/
abbrev rDX : ℕ := 135
/-- Temporary. -/
abbrev rDY : ℕ := 136

/-- The arguments of the third sort. -/
def sort3Args : Stmt := .seq (mov rKB rSEK) (.seq (mov rKL gNS) (mov rKN gPN))
/-- Sort the segments by size. -/
def sort3 : Stmt := .seq sort3Args (.seq csort (mov rORD3 rKO))
/-- The arguments of the gather of the first ends. -/
def gathAArgs : Stmt := .seq (mov rGI rORD3) (.seq (mov rGF rSEA) (mov rGL gNS))
/-- The first ends in `segOrder` order. -/
def gathA : Stmt := .seq gathAArgs (.seq gather (mov gSA rGO))
/-- The arguments of the gather of the second ends. -/
def gathBArgs : Stmt := .seq (mov rGI rORD3) (.seq (mov rGF rSEB) (mov rGL gNS))
/-- The second ends in `segOrder` order. -/
def gathB : Stmt := .seq gathBArgs (.seq gather (mov gSB rGO))
/-- **Stage C**: the segment order. -/
def stageC : Stmt := .seq sort3 (.seq gathA gathB)

/-- One segment: `POS[ORD3[t] + 1] := t + 1`. -/
def posBody : Stmt :=
  .seq (ld rDX rORD3 rDT) (.seq (inc rDX) (.seq (addc rDY rDT 1) (st rPOS rDX rDY)))
/-- Allocate `POS` (`|segOrder| + 1` cells). -/
def posAlloc : Stmt := .seq (addc rDX gNS 1) (alloc rPOS rDX)
/-- **Stage D**: the segment ids of the enumerated segments. -/
def stageD : Stmt := .seq posAlloc (forUp rDT gNS posBody)

/-- The registers written by stage C. -/
abbrev WC : List ℕ := wregs stageC
/-- The registers written by stage D. -/
abbrev WD : List ℕ := wregs stageD

/-! ### The order -/

/-- The indices of the enumerated segments, stably sorted by size. -/
abbrev ord3 (pg : Graph) (n : ℕ) : List ℕ := bucketIdx ((segEnum pg n).map sizeOf) n

variable {pg : Graph} {n : ℕ} {S : ℕ}

theorem keys_size_lt : ∀ x ∈ (segEnum pg n).map sizeOf, x < n := by
  intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sizeOf_lt hy

theorem length_ord3 : (ord3 pg n).length = (segOrder pg n).length := by
  rw [ord3, length_bucketIdx _ _ keys_size_lt, List.length_map, length_segOrder]

theorem lt_of_mem_ord3 {i : ℕ} (hi : i ∈ ord3 pg n) : i < (segEnum pg n).length := by
  have := lt_of_mem_bucketIdx hi; simpa using this

theorem getD_ord3_mem {t : ℕ} (ht : t < (segOrder pg n).length) : (ord3 pg n).getD t 0 ∈ ord3 pg n := by
  rw [getD_of_lt (by rw [length_ord3]; exact ht)]
  exact List.getElem_mem _

/-- Every enumerated segment is sorted. -/
theorem mem_ord3 {e : ℕ} (he : e < (segEnum pg n).length) : e ∈ ord3 pg n := by
  simp only [ord3, bucketIdx, List.mem_flatMap, List.mem_range, mem_bkt, List.length_map]
  refine ⟨((segEnum pg n).map sizeOf).getD e 0, ?_, he, rfl⟩
  rw [getD_map_lt he (0, 0), getD_of_lt he]
  exact sizeOf_lt (List.getElem_mem he)

/-- Reading a field of the enumerated segments through `ord3`. -/
theorem getD_ord3 (g : ℕ × ℕ → ℕ) {t : ℕ} (ht : t < (segOrder pg n).length) :
    ((segEnum pg n).map g).getD ((ord3 pg n).getD t 0) 0 = g ((segOrder pg n)[t]) := by
  have h := congrArg (fun l => l.getD t 0) (map_bucketIdx_segEnum (pg := pg) (n := n) g)
  beta_reduce at h
  rw [getD_map_lt (by rw [length_ord3]; exact ht) 0, getD_map_lt ht (0, 0), getD_of_lt ht] at h
  exact h

/-- The enumerated segment at `ord3[t]` is `segOrder[t]`. -/
theorem getD_segEnum_ord3 {t : ℕ} (ht : t < (segOrder pg n).length) :
    (segEnum pg n).getD ((ord3 pg n).getD t 0) (0, 0) = (segOrder pg n)[t] := by
  have hlt := lt_of_mem_ord3 (getD_ord3_mem (pg := pg) (n := n) ht)
  have h1 := getD_ord3 Prod.fst ht
  have h2 := getD_ord3 Prod.snd ht
  rw [getD_map_lt hlt (0, 0)] at h1 h2
  exact Prod.ext h1 h2

/-- The segment id of `ord3[t]`. -/
theorem posId_ord3 {t : ℕ} (ht : t < (segOrder pg n).length) :
    posId pg n ((ord3 pg n).getD t 0 + 1) = t + 1 := by
  simp only [posId, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  rw [getD_segEnum_ord3 ht, segId_getElem ht]

/-! ### Stage C -/

/-- The state after stage C. -/
def OrdSt (pg : Graph) (n : ℕ) (c : Config) : Prop :=
  ArrAt rORD3 (ord3 pg n) c ∧ ArrAt gSA ((segOrder pg n).map Prod.fst) c ∧
    ArrAt gSB ((segOrder pg n).map Prod.snd) c

theorem stable_ordSt {W : List ℕ} (h : rORD3 ∉ W ∧ gSA ∉ W ∧ gSB ∉ W) : Stable W (OrdSt pg n) :=
  (Stable.arrAt h.1 _).and ((Stable.arrAt h.2.1 _).and (Stable.arrAt h.2.2 _))

theorem sort3_spec :
    HGMB S sort3 WC (fun c => (EnumSt pg n c ∧ Zf c) ∧ c.reg gPN = n)
      (fun c => (ArrAt rORD3 (ord3 pg n) c ∧ Zf c) ∧ (EnumSt pg n c ∧ c.reg gPN = n))
      (28 * pg.length + 15 * n + 28) (2 * n + 1 + pg.length) := by
  have hF : Stable (wregs csort) (fun c => EnumSt pg n c ∧ c.reg gPN = n) :=
    (stable_enumSt (by decide)).and (Stable.regEq (by decide) _)
  have h₁ : HGMB S sort3Args WC (fun c => (EnumSt pg n c ∧ Zf c) ∧ c.reg gPN = n)
      (fun c => CsIn ((segEnum pg n).map sizeOf) n c ∧ (EnumSt pg n c ∧ c.reg gPN = n)) 6 0 := by
    refine HGMB.zeroRun (by decide) rfl (by decide) (fun c ⟨⟨hE, hZ⟩, hN⟩ =>
      ⟨?_, grow_movs (by decide) rfl rfl (by decide) (by decide) c⟩) (by decide)
    obtain ⟨hm, hf⟩ := movs_mem (s := sort3Args) (by decide) rfl (by decide) c
    refine ⟨⟨?_, ?_, hE.2.2.2.2.1.of_reg ?_ hm hf, by unfold Zf at hZ; rw [hm, hf]; exact hZ⟩,
      ((stable_enumSt (by decide)).and (Stable.regEq (by decide) _)) c _ ⟨hE, hN⟩
        (grow_movs (by decide) rfl rfl (by decide) (fun _ h => h) c)⟩
    · simp +decide [sort3Args, run_mov, hE.1]
    · simp +decide [sort3Args, run_mov, hN]
    · simp +decide [sort3Args, run_mov]
  have h₂ := ((csort_specMB (S := S) _ n (keys_size_lt (pg := pg))).frame hF).mono (W' := WC) (by decide) (fun _ h => h)
    (fun _ h => h) le_rfl le_rfl
  have h₃ : HGMB S (mov rORD3 rKO) WC
      (fun c => (CsOut ((segEnum pg n).map sizeOf) n c ∧ ZeroFrom c.mem (c.reg rFREE)) ∧
        (EnumSt pg n c ∧ c.reg gPN = n))
      (fun c => (ArrAt rORD3 (ord3 pg n) c ∧ Zf c) ∧ (EnumSt pg n c ∧ c.reg gPN = n)) 2 0 := by
    refine HGMB.zeroRun (by decide) rfl (by decide) (fun c ⟨⟨hO, hZ⟩, hE⟩ =>
      ⟨⟨⟨?_, ?_⟩, ?_⟩, grow_movs (by decide) rfl rfl (by decide) (by decide) c⟩) (by decide)
    · exact hO.1.of_reg (by simp +decide [run_mov]) (by simp [run_mov]) (by simp +decide [run_mov])
    · unfold Zf; simpa +decide [run_mov] using hZ
    · exact ((stable_enumSt (by decide)).and (Stable.regEq (by decide) _)) c _ hE
        (grow_movs (by decide) rfl rfl (by decide) (fun _ h => h) c)
  have := length_segEnum_le (pg := pg) (n := n)
  refine (h₁.seq (h₂.seq h₃)).weaken ?_ ?_
  all_goals simp only [List.length_map]; omega

theorem gathA_spec :
    HGMB S gathA WC (fun c => (ArrAt rORD3 (ord3 pg n) c ∧ Zf c) ∧ (EnumSt pg n c ∧ c.reg gPN = n))
      (fun c => (ArrAt gSA ((segOrder pg n).map Prod.fst) c ∧ Zf c) ∧
        (ArrAt rORD3 (ord3 pg n) c ∧ EnumSt pg n c ∧ c.reg gPN = n))
      (10 * pg.length + 14) pg.length := by
  have hidx : ∀ i ∈ ord3 pg n, i < ((segEnum pg n).map Prod.fst).length := fun i hi => by
    rw [List.length_map]; exact lt_of_mem_ord3 hi
  have hF : ∀ W : List ℕ, rORD3 ∉ W → gNS ∉ W ∧ rSEA ∉ W ∧ rSEB ∉ W ∧ rSEP ∉ W ∧
      rSEK ∉ W ∧ rLAST ∉ W ∧ rLSEG ∉ W → gPN ∉ W →
      Stable W (fun c => ArrAt rORD3 (ord3 pg n) c ∧ EnumSt pg n c ∧ c.reg gPN = n) :=
    fun W h1 h2 h3 => (Stable.arrAt h1 _).and ((stable_enumSt h2).and (Stable.regEq h3 _))
  have h₁ : HGMB S gathAArgs WC
      (fun c => (ArrAt rORD3 (ord3 pg n) c ∧ Zf c) ∧ (EnumSt pg n c ∧ c.reg gPN = n))
      (fun c => GaIn (ord3 pg n) ((segEnum pg n).map Prod.fst) c ∧
        (ArrAt rORD3 (ord3 pg n) c ∧ EnumSt pg n c ∧ c.reg gPN = n)) 6 0 := by
    refine HGMB.zeroRun (by decide) rfl (by decide) (fun c ⟨⟨hO, hZ⟩, hE, hN⟩ =>
      ⟨?_, grow_movs (by decide) rfl rfl (by decide) (by decide) c⟩) (by decide)
    obtain ⟨hm, hf⟩ := movs_mem (s := gathAArgs) (by decide) rfl (by decide) c
    refine ⟨⟨?_, hO.of_reg ?_ hm hf, hE.2.1.of_reg ?_ hm hf,
      by unfold Zf at hZ; rw [hm, hf]; exact hZ⟩,
      hF _ (by decide) (by decide) (by decide) c _ ⟨hO, hE, hN⟩
        (grow_movs (by decide) rfl rfl (by decide) (fun _ h => h) c)⟩
    · simp +decide [gathAArgs, run_mov, hE.1, length_ord3, length_segOrder]
    · simp +decide [gathAArgs, run_mov]
    · simp +decide [gathAArgs, run_mov]
  have h₂ := ((gather_spec (S := S) (ord3 pg n) _ hidx).frame
    (hF _ (by decide) (by decide) (by decide))).mono (W' := WC) (by decide) (fun _ h => h)
    (fun _ h => h) le_rfl le_rfl
  have h₃ : HGMB S (mov gSA rGO) WC
      (fun c => (ArrAt rGO ((ord3 pg n).map fun i => ((segEnum pg n).map Prod.fst).getD i 0) c ∧
        ZeroFrom c.mem (c.reg rFREE)) ∧ (ArrAt rORD3 (ord3 pg n) c ∧ EnumSt pg n c ∧ c.reg gPN = n))
      (fun c => (ArrAt gSA ((segOrder pg n).map Prod.fst) c ∧ Zf c) ∧
        (ArrAt rORD3 (ord3 pg n) c ∧ EnumSt pg n c ∧ c.reg gPN = n)) 2 0 := by
    refine HGMB.zeroRun (by decide) rfl (by decide) (fun c ⟨⟨hG, hZ⟩, hE⟩ =>
      ⟨⟨⟨?_, ?_⟩, ?_⟩, grow_movs (by decide) rfl rfl (by decide) (by decide) c⟩) (by decide)
    · rw [← map_bucketIdx_segEnum]
      exact hG.of_reg (by simp +decide [run_mov]) (by simp [run_mov]) (by simp +decide [run_mov])
    · unfold Zf; simpa +decide [run_mov] using hZ
    · exact hF _ (by decide) (by decide) (by decide) c _ hE
        (grow_movs (by decide) rfl rfl (by decide) (fun _ h => h) c)
  have := length_segEnum_le (pg := pg) (n := n)
  refine (h₁.seq (h₂.seq h₃)).weaken ?_ ?_
  all_goals rw [length_ord3, length_segOrder]; omega

theorem gathB_spec :
    HGMB S gathB WC (fun c => (ArrAt gSA ((segOrder pg n).map Prod.fst) c ∧ Zf c) ∧
        (ArrAt rORD3 (ord3 pg n) c ∧ EnumSt pg n c ∧ c.reg gPN = n))
      (fun c => (OrdSt pg n c ∧ Zf c) ∧ (EnumSt pg n c ∧ c.reg gPN = n))
      (10 * pg.length + 14) pg.length := by
  have hidx : ∀ i ∈ ord3 pg n, i < ((segEnum pg n).map Prod.snd).length := fun i hi => by
    rw [List.length_map]; exact lt_of_mem_ord3 hi
  have hF : ∀ W : List ℕ, gSA ∉ W → rORD3 ∉ W → gNS ∉ W ∧ rSEA ∉ W ∧ rSEB ∉ W ∧
      rSEP ∉ W ∧ rSEK ∉ W ∧ rLAST ∉ W ∧ rLSEG ∉ W → gPN ∉ W →
      Stable W (fun c => ArrAt gSA ((segOrder pg n).map Prod.fst) c ∧
        (ArrAt rORD3 (ord3 pg n) c ∧ EnumSt pg n c ∧ c.reg gPN = n)) :=
    fun W h0 h1 h2 h3 =>
      (Stable.arrAt h0 _).and ((Stable.arrAt h1 _).and ((stable_enumSt h2).and (Stable.regEq h3 _)))
  have h₁ : HGMB S gathBArgs WC (fun c => (ArrAt gSA ((segOrder pg n).map Prod.fst) c ∧ Zf c) ∧
        (ArrAt rORD3 (ord3 pg n) c ∧ EnumSt pg n c ∧ c.reg gPN = n))
      (fun c => GaIn (ord3 pg n) ((segEnum pg n).map Prod.snd) c ∧
        (ArrAt gSA ((segOrder pg n).map Prod.fst) c ∧
          (ArrAt rORD3 (ord3 pg n) c ∧ EnumSt pg n c ∧ c.reg gPN = n))) 6 0 := by
    refine HGMB.zeroRun (by decide) rfl (by decide) (fun c ⟨⟨hA, hZ⟩, hO, hE, hN⟩ =>
      ⟨?_, grow_movs (by decide) rfl rfl (by decide) (by decide) c⟩) (by decide)
    obtain ⟨hm, hf⟩ := movs_mem (s := gathBArgs) (by decide) rfl (by decide) c
    refine ⟨⟨?_, hO.of_reg ?_ hm hf, hE.2.2.1.of_reg ?_ hm hf,
      by unfold Zf at hZ; rw [hm, hf]; exact hZ⟩,
      hF _ (by decide) (by decide) (by decide) (by decide) c _ ⟨hA, hO, hE, hN⟩
        (grow_movs (by decide) rfl rfl (by decide) (fun _ h => h) c)⟩
    · simp +decide [gathBArgs, run_mov, hE.1, length_ord3, length_segOrder]
    · simp +decide [gathBArgs, run_mov]
    · simp +decide [gathBArgs, run_mov]
  have h₂ := ((gather_spec (S := S) (ord3 pg n) _ hidx).frame
    (hF _ (by decide) (by decide) (by decide) (by decide))).mono (W' := WC) (by decide)
    (fun _ h => h) (fun _ h => h) le_rfl le_rfl
  have h₃ : HGMB S (mov gSB rGO) WC
      (fun c => (ArrAt rGO ((ord3 pg n).map fun i => ((segEnum pg n).map Prod.snd).getD i 0) c ∧
        ZeroFrom c.mem (c.reg rFREE)) ∧ (ArrAt gSA ((segOrder pg n).map Prod.fst) c ∧
          (ArrAt rORD3 (ord3 pg n) c ∧ EnumSt pg n c ∧ c.reg gPN = n)))
      (fun c => (OrdSt pg n c ∧ Zf c) ∧ (EnumSt pg n c ∧ c.reg gPN = n)) 2 0 := by
    refine HGMB.zeroRun (by decide) rfl (by decide) (fun c ⟨⟨hG, hZ⟩, hE⟩ => ⟨?_, grow_movs (by decide) rfl rfl
      (by decide) (by decide) c⟩) (by decide)
    have hE' := hF _ (by decide) (by decide) (by decide) (by decide) c _ hE
      (grow_movs (s := mov gSB rGO) (by decide) rfl rfl (by decide) (fun _ h => h) c)
    refine ⟨⟨⟨hE'.2.1, hE'.1, ?_⟩, ?_⟩, hE'.2.2⟩
    · rw [← map_bucketIdx_segEnum]
      exact hG.of_reg (by simp +decide [run_mov]) (by simp [run_mov]) (by simp +decide [run_mov])
    · unfold Zf; simpa +decide [run_mov] using hZ
  have := length_segEnum_le (pg := pg) (n := n)
  refine (h₁.seq (h₂.seq h₃)).weaken ?_ ?_
  all_goals rw [length_ord3, length_segOrder]; omega

/-- **Stage C**: the segments in `segOrder` order. -/
theorem stageC_spec :
    HGMB S stageC WC (fun c => (EnumSt pg n c ∧ Zf c) ∧ c.reg gPN = n)
      (fun c => (OrdSt pg n c ∧ Zf c) ∧ (EnumSt pg n c ∧ c.reg gPN = n))
      (48 * pg.length + 15 * n + 56) (3 * pg.length + 2 * n + 1) :=
  (sort3_spec.seq (gathA_spec.seq gathB_spec)).weaken (by omega) (by omega)

/-! ### Stage D -/

/-- The table `POS` after the first `t` segments of `segOrder`. -/
def posPart (pg : Graph) (n t i : ℕ) : ℕ :=
  if i ≠ 0 ∧ i - 1 ∈ (ord3 pg n).take t then posId pg n i else 0

theorem posPart_zero : posPart pg n 0 = fun _ => 0 := by
  funext i; simp [posPart]

theorem posPart_succ {t : ℕ} (ht : t < (segOrder pg n).length) :
    posPart pg n (t + 1) =
      Function.update (posPart pg n t) ((ord3 pg n).getD t 0 + 1) (t + 1) := by
  have htake : (ord3 pg n).take (t + 1) = (ord3 pg n).take t ++ [(ord3 pg n).getD t 0] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_ord3]; exact ht),
      getD_of_lt (by rw [length_ord3]; exact ht)]
    rfl
  funext i
  by_cases hi : i = (ord3 pg n).getD t 0 + 1
  · subst hi
    simp only [Function.update_self, posPart, htake, ne_eq, Nat.add_one_ne_zero, not_false_eq_true,
      Nat.add_sub_cancel, List.mem_append, List.mem_singleton, or_true, and_self, ↓reduceIte]
    exact posId_ord3 ht
  · rw [Function.update_of_ne hi]
    simp only [posPart, htake, List.mem_append, List.mem_singleton]
    have : ¬ (i ≠ 0 ∧ i - 1 = (ord3 pg n).getD t 0) := by omega
    by_cases h0 : i ≠ 0 ∧ i - 1 ∈ (ord3 pg n).take t
    · simp [h0]
    · rw [ite_eq_right (by tauto), ite_eq_right h0]

theorem posPart_full {i : ℕ} (hi : i < (segOrder pg n).length + 1) :
    posPart pg n (segOrder pg n).length i = posId pg n i := by
  unfold posPart
  split_ifs with h
  · rfl
  · rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; rfl
    · exfalso
      apply h
      refine ⟨by omega, ?_⟩
      rw [← length_ord3, List.take_length]
      exact mem_ord3 (by rw [← length_segOrder]; omega)

/-- The result of stage D. -/
def PosSt (pg : Graph) (n : ℕ) (c : Config) : Prop :=
  TabAt rPOS ((segOrder pg n).length + 1) (posId pg n) c

/-- The invariant of stage D after `t` segments. -/
@[mk_iff] structure PosInv (pg : Graph) (n F₀ : ℕ) (m₀ : ℕ → ℕ) (t : ℕ) (c : Config) : Prop where
  pos : c.reg rPOS = F₀
  free : c.reg rFREE = F₀ + ((segOrder pg n).length + 1)
  ns : c.reg gNS = (segOrder pg n).length
  ord : Arr c.mem (c.reg rORD3) (ord3 pg n)
  bord : c.reg rORD3 + (ord3 pg n).length ≤ F₀
  tab : Tab c.mem F₀ ((segOrder pg n).length + 1) (posPart pg n t)
  zero : ZeroFrom c.mem (F₀ + ((segOrder pg n).length + 1))
  same : SameOn (· < F₀) m₀ c.mem

theorem posBody_spec (F₀ : ℕ) (m₀ : ℕ → ℕ) (hS : F₀ + ((segOrder pg n).length + 1) ≤ S) (t : ℕ)
    (ht : t < (segOrder pg n).length) :
    HTB S posBody (fun c => PosInv pg n F₀ m₀ t c ∧ c.reg rDT = t ∧
        c.reg gNS = (segOrder pg n).length)
      (fun c => PosInv pg n F₀ m₀ (t + 1) c ∧ c.reg rDT = t ∧
        c.reg gNS = (segOrder pg n).length) 8 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨hI, hT, hN⟩ => ?_
  have hi : c.mem (c.reg rORD3 + t) = (ord3 pg n).getD t 0 :=
    hI.ord.getD (by rw [length_ord3]; exact ht)
  have hilt : (ord3 pg n).getD t 0 < (segOrder pg n).length := by
    rw [length_segOrder]; exact lt_of_mem_ord3 (getD_ord3_mem ht)
  refine ⟨by have := hI.bord; rw [length_ord3] at this; addr_ok [posBody, hT, hi, hI.pos], ?_⟩
  have hrr : ∀ r, r ∉ wregs posBody → (RAM.run posBody c).reg r = c.reg r :=
    fun r hr => run_reg_of_not_mem (by decide) hr c
  have hmem : (RAM.run posBody c).mem =
      upd c.mem (F₀ + ((ord3 pg n).getD t 0 + 1)) (t + 1) := by
    simp +decide only [posBody, run_seq', run_ld, run_inc (show rDX ≠ rT by decide),
      run_addc (show rDT ≠ rT by decide), run_st (show rDY ≠ rT by decide), setReg_reg,
      ↓reduceIte, setReg_mem, setMem_mem_upd, hT, hi, hI.pos]
  have hb1 := hI.bord
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals try rw [hrr _ (by decide)]
  all_goals try rw [hmem]
  · exact hI.pos
  · exact hI.free
  · exact hI.ns
  · exact hI.ord.upd_of_disjoint (by omega)
  · exact hI.bord
  · rw [posPart_succ ht]; exact hI.tab.upd rfl
  · exact hI.zero.upd (by omega)
  · exact hI.same.upd_of_ge (by omega) _
  · exact hT
  · exact hN

/-- **Stage D** (with its layout): the table `POS` at `F₀`, `|segOrder| + 1` cells. -/
theorem stageD_core (F₀ : ℕ) (m₀ : ℕ → ℕ) (hS : F₀ + ((segOrder pg n).length + 1) ≤ S) :
    HTB S stageD (fun c => ((OrdSt pg n c ∧ Zf c) ∧ (EnumSt pg n c ∧ c.reg gPN = n)) ∧
        c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => (PosSt pg n c ∧ Zf c) ∧ SameOn (· < F₀) m₀ c.mem ∧ F₀ ≤ c.reg rFREE ∧
        c.reg rFREE = F₀ + ((segOrder pg n).length + 1))
      (12 * (segOrder pg n).length + 9) := by
  have h₀ : HT posAlloc (fun c => ((OrdSt pg n c ∧ Zf c) ∧ (EnumSt pg n c ∧
        c.reg gPN = n)) ∧ c.reg rFREE = F₀ ∧ c.mem = m₀)
      (fun c => PosInv pg n F₀ m₀ 0 c ∧ c.reg gNS = (segOrder pg n).length) 6 := by
    refine HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hO, hZ⟩, hE, hN⟩, hF, hm⟩ => ?_
    simp only [posAlloc, run_seq']
    rw [run_alloc (by decide) (by decide)]
    have h1 := hO.1.2
    have hns : c.reg gNS = (segOrder pg n).length := by rw [hE.1, length_segOrder]
    unfold Zf at hZ
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals simp +decide only [run_addc (show gNS ≠ rT by decide), setReg_reg, ↓reduceIte,
      setReg_mem, hF, hns, posPart_zero] at h1 ⊢
    all_goals try omega
    · exact hO.1.1
    · rw [hF] at hZ; exact hZ.tab le_rfl _
    · rw [hF] at hZ; exact hZ.mono (by omega)
    · rw [hm]; exact SameOn.refl _ _
  have hl := HTB.forUpC (i := rDT) (n := gNS) (N := (segOrder pg n).length) (body := posBody)
    (PosInv pg n F₀ m₀) 8 (by decide) (by decide) (by decide) (fun t => by indep [posInv_iff])
    (fun t ht => posBody_spec F₀ m₀ hS t ht)
  refine ((HTB.of_HT rfl h₀).seq hl).mono (fun _ h => h) ?_ (by omega)
  rintro c ⟨hI, -, -⟩
  refine ⟨⟨⟨by rw [hI.pos]; exact hI.tab.congr_fun fun i hi => posPart_full hi,
    by rw [hI.pos, hI.free]⟩, ?_⟩, hI.same, by rw [hI.free]; omega, hI.free⟩
  unfold Zf; rw [hI.free]; exact hI.zero

/-- **Stage D**: the segment ids of the enumerated segments. -/
theorem stageD_spec :
    HGMB S stageD WD (fun c => (OrdSt pg n c ∧ Zf c) ∧ (EnumSt pg n c ∧ c.reg gPN = n))
      (fun c => PosSt pg n c ∧ Zf c) (12 * pg.length + 9) (pg.length + 1) := by
  refine HGMB.ofGhost (by decide) (fun _ h => h) fun F₀ m₀ hS => ?_
  have := length_segEnum_le (pg := pg) (n := n)
  have := length_segOrder (pg := pg) (n := n)
  refine (stageD_core F₀ m₀ (by omega)).mono (fun _ h => h)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, by rw [h.2.2.2]; omega⟩) ?_
  omega

end STACS2027.RAM.P1
