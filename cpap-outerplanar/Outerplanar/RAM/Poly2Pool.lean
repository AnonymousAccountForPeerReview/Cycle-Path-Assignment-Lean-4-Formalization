module

public import Outerplanar.RAM.Poly2Reg
import Mathlib.Tactic

/-!
# Phase P2 of the polygon solver, stage P: the pool

After stage R, the final partial paths of every segment are stored (`DataB`). Stage P
(`stageP`) allocates the table `gTST` (`|segOrder| + 1` cells) and pushes the pool at
`gPOOL`: for each segment `t` (in `segOrder`), it records the number of cycles so far in
`gTST[t]` and pushes the entries of the final partial paths of `t` with `k - 1` edges, which
are the cycles with top `t` (`rpF_seg`). Finally `gTST[|segOrder|]` is the size of the pool
(`stageP_spec`): `gTST` holds `topStarts`, `gPOOL` the flattened pool, `gNP` its size. The
triples are bounded (`HTB S`, `HGB S`) for `S` at or above the end of the pool.
-/

@[expose] public section

namespace STACS2027.RAM.P2

open STACS2027.Poly P1

/-! ### Abstract side -/

/-- The cycles of the final partial paths: those with `k - 1` edges. -/
def sel (k : ℕ) (pe : List ℕ × ℕ) : List (List ℕ) := if pe.2 = k - 1 then [pe.1] else []

/-- The cycles with top among the first `t` segments. -/
def cycPre (pg : Graph) (n k t : ℕ) : List (List ℕ) :=
  ((segOrder pg n).take t).flatMap fun s => rpF pg n k n s.1 s.2 k

variable {pg : Graph} {n k : ℕ}

theorem cycPre_zero : cycPre pg n k 0 = [] := rfl

theorem cycPre_succ (hP : IsPolygon pg n) (hk : 3 ≤ k) {t : ℕ} (ht : t < (segOrder pg n).length) :
    cycPre pg n k (t + 1) = cycPre pg n k t ++ (fin pg n k (segOrder pg n)[t]).flatMap (sel k) := by
  rw [cycPre, take_succ_eq ht, List.flatMap_append, List.flatMap_singleton,
    rpF_seg hP hk (List.getElem_mem ht)]
  rfl

theorem cycPre_full : cycPre pg n k (segOrder pg n).length = pool pg n k := by
  rw [cycPre, List.take_length]; rfl

/-- The entries of a prefix of a flattened list of lists. -/
theorem flatten_flatMap_take_le {α β : Type*} (M : List α) (f : α → List (List β)) {i j : ℕ}
    (hij : i ≤ j) :
    ((M.take i).flatMap f).flatten.length ≤ ((M.take j).flatMap f).flatten.length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [List.take_add, List.flatMap_append, List.flatten_append, List.length_append]
  omega

theorem cycPre_le_pool {t : ℕ} (ht : t ≤ (segOrder pg n).length) :
    (cycPre pg n k t).flatten.length ≤ (pool pg n k).flatten.length := by
  rw [← cycPre_full]
  exact flatten_flatMap_take_le _ _ ht

theorem topStarts_eq :
    topStarts pg n k = (List.range ((segOrder pg n).length + 1)).map fun t => (cycPre pg n k t).length := by
  rw [topStarts, prefixSums, List.length_map]
  apply List.map_congr_left
  intro t _
  rw [cycPre, List.length_flatMap, List.map_take]

/-! ### The data kept below a bound -/

/-- The data kept below `F` after stage R: the first and second ends of the segments, and the
final partial paths of all segments with their tables. -/
structure DataB (pg : Graph) (n k : ℕ) (L : Lay) (m : ℕ → ℕ) (F : ℕ) : Prop where
  sa : Arr m L.sa ((segOrder pg n).map Prod.fst)
  sb : Arr m L.sb ((segOrder pg n).map Prod.snd)
  fin : ∀ t (ht : t < (segOrder pg n).length), L.fr ≤ m (L.fb + t) ∧
    Arr m (m (L.fb + t)) (enc (fin pg n k (segOrder pg n)[t])) ∧
    m (L.fb + t) + (enc (fin pg n k (segOrder pg n)[t])).length ≤ F ∧
    m (L.fc + t) = (fin pg n k (segOrder pg n)[t]).length
  le : L.fr ≤ F

theorem DataB.of_below {L : Lay} (hL : LayOK pg n L) {m m' : ℕ → ℕ} {F : ℕ}
    (h : DataB pg n k L m F) (hS : SameOn (· < F) m m') : DataB pg n k L m' F := by
  have hfc := hL.fc
  have hfr := hL.fr
  have hle := h.le
  refine ⟨h.sa.of_below hS (by simpa using (show L.sa + (segOrder pg n).length ≤ F by
      have := hL.sa; omega)),
    h.sb.of_below hS (by simpa using (show L.sb + (segOrder pg n).length ≤ F by
      have := hL.sb; omega)), fun t ht => ?_, h.le⟩
  obtain ⟨h1, h2, h3, h4⟩ := h.fin t ht
  have e1 : m' (L.fb + t) = m (L.fb + t) := hS _ (show L.fb + t < F by omega)
  have e2 : m' (L.fc + t) = m (L.fc + t) := hS _ (show L.fc + t < F by omega)
  rw [e1, e2]
  exact ⟨h1, h2.of_below hS h3, h3, h4⟩

/-- After stage R. -/
theorem SegInv.dataB {L : Lay} {m₁ : ℕ → ℕ} {c : Config}
    (h : SegInv pg n k L m₁ (segOrder pg n).length c) : DataB pg n k L c.mem (c.reg rFREE) :=
  ⟨h.1.1.sa, h.1.1.sb, fun t ht => by
    obtain ⟨h1, h2, h3⟩ := h.1.2.1.2 t ht ht
    exact ⟨h1, h2.1, h2.2, h3⟩, h.1.1.fr⟩

/-- The constant registers of stage P and the data below `F`. -/
@[mk_iff] structure QCtx (pg : Graph) (n k : ℕ) (L : Lay) (F : ℕ) (c : Config) : Prop where
  rk : c.reg rK = k
  rkm : c.reg rKm1 = k - 1
  pn : c.reg gPN = n
  ns : c.reg gNS = (segOrder pg n).length
  rsa : c.reg gSA = L.sa
  rsb : c.reg gSB = L.sb
  rfb : c.reg rFB = L.fb
  rfc : c.reg rFC = L.fc
  data : DataB pg n k L c.mem F
  le : F ≤ c.reg rFREE

theorem QCtx.of_below {L : Lay} (hL : LayOK pg n L) {F : ℕ} {c c' : Config} (h : QCtx pg n k L F c)
    (hreg : ∀ r ∈ [rK, rKm1, gPN, gNS, gSA, gSB, rFB, rFC], c'.reg r = c.reg r)
    (hS : SameOn (· < F) c.mem c'.mem) (hF : F ≤ c'.reg rFREE) : QCtx pg n k L F c' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hreg
  exact ⟨hreg.1.trans h.rk, hreg.2.1.trans h.rkm, hreg.2.2.1.trans h.pn, hreg.2.2.2.1.trans h.ns,
    hreg.2.2.2.2.1.trans h.rsa, hreg.2.2.2.2.2.1.trans h.rsb, hreg.2.2.2.2.2.2.1.trans h.rfb,
    hreg.2.2.2.2.2.2.2.trans h.rfc, h.data.of_below hL hS, hF⟩

theorem QCtx.stable {L : Lay} (hL : LayOK pg n L) {F : ℕ} {W : List ℕ}
    (hW : ∀ r ∈ [rK, rKm1, gPN, gNS, gSA, gSB, rFB, rFC], r ∉ W) :
    Stable W (QCtx pg n k L F) := fun c c' h hg =>
  h.of_below hL (fun r hr => hg.reg r (hW r hr))
    (hg.mem.mono fun a (ha : a < F) => show a < c.reg rFREE by have := h.le; omega)
    (h.le.trans hg.free)

/-! ### Programs -/

/-- Allocate `gTST`; the pool starts at the free pointer. -/
def poInit : Stmt :=
  .seq (addc rW gNS 1) (.seq (alloc gTST rW) (.seq (mov gPOOL rFREE) (.const gNP 0)))
/-- Read the record and compare its edges with `k - 1`. -/
def prTest : Stmt :=
  .seq (.load rER rCP) (.seq (.sub rW rER rKm1) (.seq (.sub rW3 rKm1 rER) (.add rW rW rW3)))
/-- Prepare copying the `k` entries of the record. -/
def prCpA : Stmt := .seq (addc rCS rCP 1) (mov rCL rK)
/-- Push the cycle of the record, count. -/
def prCp : Stmt := .seq prCpA (.seq copy (inc gNP))
/-- One record. -/
def prBody : Stmt := .seq prTest (.seq (.ifz rW prCp .skip) cAdv)
/-- The records of a segment. -/
def prLoop : Stmt := forUp rCJ2 rCN prBody
/-- Find the records of the segment `t`. -/
def poRd : Stmt := .seq (ld rCP rFB rSt) (ld rCN rFC rSt)
/-- One segment: record the start of its cycles, push them. -/
def poBody : Stmt := .seq (st gTST rSt gNP) (.seq poRd prLoop)
/-- The size of the pool. -/
def poFin : Stmt := st gTST gNS gNP
/-- **Stage P**: the pool. -/
def stageP : Stmt := .seq poInit (.seq (forUp rSt gNS poBody) poFin)

/-- Steps for one record. -/
def TPr (k : ℕ) : ℕ := 9 * k + 17
/-- Steps for one segment. -/
def TPo (k : ℕ) : ℕ := Poly.partsBound k * (TPr k + 4) + 9

/-! ### The records of a segment -/

/-- The frame of stage P: the constants, `u` entries of `gTST`. -/
def PoFr (pg : Graph) (n k : ℕ) (L : Lay) (F : ℕ) (m₂ : ℕ → ℕ) (u : ℕ) (c : Config) : Prop :=
  QCtx pg n k L F c ∧ c.reg gTST = F ∧ c.reg gPOOL = F + ((segOrder pg n).length + 1) ∧
    SameOn (· < F) m₂ c.mem ∧ Tab c.mem F u (fun t' => (cycPre pg n k t').length) ∧
    F + ((segOrder pg n).length + 1) ≤ c.reg rFREE

theorem PoFr.stable {L : Lay} (hL : LayOK pg n L) {F : ℕ} (m₂ : ℕ → ℕ) {u : ℕ}
    (hu : u ≤ (segOrder pg n).length + 1) {W : List ℕ}
    (hW : ∀ r ∈ [rK, rKm1, gPN, gNS, gSA, gSB, rFB, rFC, gTST, gPOOL], r ∉ W) :
    Stable W (PoFr pg n k L F m₂ u) := fun c c' h hg => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hW
  obtain ⟨hQ, hT, hPl, hS, hTab, hle⟩ := h
  refine ⟨QCtx.stable hL (by simp [hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1,
      hW.2.2.2.2.2.1, hW.2.2.2.2.2.2.1, hW.2.2.2.2.2.2.2.1]) c c' hQ hg,
    by rw [hg.reg _ hW.2.2.2.2.2.2.2.2.1, hT], by rw [hg.reg _ hW.2.2.2.2.2.2.2.2.2, hPl],
    hg.sameOn hS (by have := hQ.le; omega), hTab.of_below hg.mem (by omega),
    by have := hg.free; omega⟩

/-- The cycles of the first `j` records of `s`. -/
abbrev prJ (k : ℕ) (rs : List (List ℕ × ℕ)) (j : ℕ) : List (List ℕ) := (rs.take j).flatMap (sel k)

@[simp] theorem prJ_zero (k : ℕ) (rs : List (List ℕ × ℕ)) : prJ k rs 0 = [] := rfl

/-- The invariant of the records of the segment `t` (at `b`), after `j` records. -/
def PrInv (pg : Graph) (n k : ℕ) (L : Lay) (F : ℕ) (m₂ : ℕ → ℕ) (t b j : ℕ) (c : Config) : Prop :=
  PoFr pg n k L F m₂ (t + 1) c ∧ c.reg rSt = t ∧ c.mem (L.fb + t) = b ∧
    Strm (F + ((segOrder pg n).length + 1))
      (cycPre pg n k t ++ prJ k (fin pg n k ((segOrder pg n).getD t (0, 0))) j).flatten c ∧
    c.reg gNP = (cycPre pg n k t ++ prJ k (fin pg n k ((segOrder pg n).getD t (0, 0))) j).length ∧
    c.reg rCP = b + encOff (fin pg n k ((segOrder pg n).getD t (0, 0))) j

theorem prInv_iff {L : Lay} {F : ℕ} {m₂ : ℕ → ℕ} {t b j : ℕ} (ht : t < (segOrder pg n).length)
    {c : Config} : PrInv pg n k L F m₂ t b j c ↔
      PoFr pg n k L F m₂ (t + 1) c ∧ c.reg rSt = t ∧ c.mem (L.fb + t) = b ∧
      Strm (F + ((segOrder pg n).length + 1))
        (cycPre pg n k t ++ prJ k (fin pg n k (segOrder pg n)[t]) j).flatten c ∧
      c.reg gNP = (cycPre pg n k t ++ prJ k (fin pg n k (segOrder pg n)[t]) j).length ∧
      c.reg rCP = b + encOff (fin pg n k (segOrder pg n)[t]) j := by
  rw [PrInv, getD_of_lt ht]

theorem PrInv.indep (L : Lay) (F : ℕ) (m₂ : ℕ → ℕ) (t b j : ℕ) :
    Indep [rT, rCJ2, rER, rW, rW3] (PrInv pg n k L F m₂ t b j) := by
  indep [PrInv, PoFr, qCtx_iff, Strm]

theorem prBody_spec {S : ℕ} (hP : IsPolygon pg n) {L : Lay} (hL : LayOK pg n L) (hk : 1 ≤ k)
    (F : ℕ) (m₂ : ℕ → ℕ) {t : ℕ} (ht : t < (segOrder pg n).length) (b j : ℕ)
    (hj : j < (fin pg n k (segOrder pg n)[t]).length)
    (hSz : F + ((segOrder pg n).length + 1) +
      (cycPre pg n k t ++ prJ k (fin pg n k (segOrder pg n)[t]) (j + 1)).flatten.length ≤ S) :
    HGB S prBody (wregs prLoop)
      (fun c => PrInv pg n k L F m₂ t b j c ∧ c.reg rCJ2 = j ∧
        c.reg rCN = (fin pg n k (segOrder pg n)[t]).length)
      (fun c => PrInv pg n k L F m₂ t b (j + 1) c ∧ c.reg rCJ2 = j ∧
        c.reg rCN = (fin pg n k (segOrder pg n)[t]).length) (TPr k) := by
  set rs := fin pg n k (segOrder pg n)[t] with hrs
  obtain ⟨hrk, hrl⟩ := (fin_bound hP (segOrder pg n)[t]).2 rs[j] (List.getElem_mem hj)
  set PB := F + ((segOrder pg n).length + 1) with hPB
  have hiff : ∀ {j : ℕ} {c : Config}, PrInv pg n k L F m₂ t b j c ↔
      PoFr pg n k L F m₂ (t + 1) c ∧ c.reg rSt = t ∧ c.mem (L.fb + t) = b ∧
      Strm PB (cycPre pg n k t ++ prJ k rs j).flatten c ∧
      c.reg gNP = (cycPre pg n k t ++ prJ k rs j).length ∧ c.reg rCP = b + encOff rs j :=
    fun {j c} => prInv_iff ht
  have hsuc : prJ k rs (j + 1) = prJ k rs j ++ sel k rs[j] := by
    simp only [prJ, take_succ_eq hj, List.flatMap_append, List.flatMap_singleton]
  -- the records of `s` below the free pointer
  have hrec : ∀ c, PoFr pg n k L F m₂ (t + 1) c → c.mem (L.fb + t) = b →
      Bel (b + encOff rs j) (rs[j].2 :: rs[j].1) c := by
    intro c hF hb
    obtain ⟨-, h2, h3, -⟩ := hF.1.data.fin t ht
    rw [hb] at h2 h3
    exact Bel.rec ⟨h2, by have := hF.1.le; omega⟩ hj
  have hlen : (cycPre pg n k t ++ prJ k rs (j + 1)).flatten.length =
      (cycPre pg n k t ++ prJ k rs j).flatten.length + (sel k rs[j]).flatten.length := by
    rw [hsuc, ← List.append_assoc, List.flatten_append, List.length_append]
  -- the test
  have h₁ : HGB S prTest (wregs prLoop)
      (fun c => PrInv pg n k L F m₂ t b j c ∧ c.reg rCJ2 = j ∧ c.reg rCN = rs.length)
      (fun c => (PrInv pg n k L F m₂ t b j c ∧ c.reg rCJ2 = j ∧ c.reg rCN = rs.length) ∧
        c.reg rER = rs[j].2 ∧ (c.reg rW = 0 ↔ rs[j].2 = k - 1)) 4 := by
    refine (HGB.runR (s := prTest) (by decide) (by decide) (by decide) (by decide) (by decide)
      fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rER, rW, rW3] c (RAM.run prTest c) :=
      agree_run (by decide) rfl rfl (by decide) c
    obtain ⟨hI, hj', hn⟩ := hc
    obtain ⟨hF, -, hb, hS, -, hcp⟩ := hiff.mp hI
    have hrB := (hrec c hF hb).2
    have hfr := hS.2.1
    simp only [List.length_cons] at hrB
    refine ⟨by addr_ok [prTest, hcp], ?_⟩
    have hm := (hrec c hF hb).cons.1
    refine ⟨⟨(PrInv.indep L F m₂ t b j).mono (by decide) c _ hA hI,
      by rw [hA.reg _ (by decide), hj'], by rw [hA.reg _ (by decide), hn]⟩, ?_, ?_⟩
    · simp +decide [prTest, hcp, hm]
    · simp +decide [prTest, hcp, hm, hF.1.rkm]; omega
  -- the branch
  let G : Config → Prop := fun c => PoFr pg n k L F m₂ (t + 1) c ∧ c.reg rSt = t ∧
    c.mem (L.fb + t) = b ∧ c.reg rCP = b + encOff rs j ∧ c.reg rCJ2 = j ∧ c.reg rCN = rs.length ∧
    c.reg rER = rs[j].2
  have hGs : ∀ W : List ℕ, (∀ r ∈ [rK, rKm1, gPN, gNS, gSA, gSB, rFB, rFC, gTST, gPOOL], r ∉ W) →
      rSt ∉ W → rCP ∉ W → rCJ2 ∉ W → rCN ∉ W → rER ∉ W → Stable W G := by
    intro W hW h1 h2 h3 h4 h5 c c' h hg
    obtain ⟨hF, hst, hb, hcp, hj', hn, her⟩ := h
    have hFr := hF.1.data.le
    have hle := hF.1.le
    refine ⟨PoFr.stable hL m₂ (by omega) hW c c' hF hg, by rw [hg.reg _ h1, hst], ?_,
      by rw [hg.reg _ h2, hcp], by rw [hg.reg _ h3, hj'], by rw [hg.reg _ h4, hn],
      by rw [hg.reg _ h5, her]⟩
    rw [hg.mem _ (show L.fb + t < c.reg rFREE by have := hL.fc; have := hL.fr; omega), hb]
  have h₂ : HGB S (.ifz rW prCp .skip) (wregs prLoop)
      (fun c => (PrInv pg n k L F m₂ t b j c ∧ c.reg rCJ2 = j ∧ c.reg rCN = rs.length) ∧
        c.reg rER = rs[j].2 ∧ (c.reg rW = 0 ↔ rs[j].2 = k - 1))
      (fun c => G c ∧ Strm PB (cycPre pg n k t ++ prJ k rs (j + 1)).flatten c ∧
        c.reg gNP = (cycPre pg n k t ++ prJ k rs (j + 1)).length) (9 * k + 10) := by
    refine HGB.ifz ?_ ?_
    · refine HGB.of_pre (fun c h => h.1.2.2.mp h.2) fun hl => ?_
      have hsel : sel k rs[j] = [rs[j].1] := by simp [sel, hl]
      have hl1 : rs[j].1.length = k := by omega
      have hA : HGB S prCpA (wregs prCp)
          (fun c => ((PrInv pg n k L F m₂ t b j c ∧ c.reg rCJ2 = j ∧ c.reg rCN = rs.length) ∧
            c.reg rER = rs[j].2 ∧ (c.reg rW = 0 ↔ rs[j].2 = k - 1)) ∧ c.reg rW = 0)
          (fun c => (Strm PB (cycPre pg n k t ++ prJ k rs j).flatten c ∧
            Bel (b + encOff rs j + 1) rs[j].1 c ∧ c.reg rCS = b + encOff rs j + 1 ∧
            c.reg rCL = rs[j].1.length) ∧ (G c ∧ c.reg gNP = (cycPre pg n k t ++ prJ k rs j).length))
          4 := by
        refine (HGB.runM (s := prCpA) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
        have hAg : Agree [rT, rCS, rCL] c (RAM.run prCpA c) :=
          agree_run (by decide) rfl rfl (by decide) c
        have hGr := grow_of_agree (W := [rT, rCS, rCL]) hAg (by decide) (by decide)
        obtain ⟨⟨⟨hI, hj', hn⟩, her, -⟩, -⟩ := hc
        obtain ⟨hF, hst, hb, hS, hnp, hcp⟩ := hiff.mp hI
        refine ⟨⟨strm_agree hAg (by decide) hS, stable_bel _ _ _ c _ (hrec c hF hb).cons.2 hGr,
          ?_, ?_⟩, hGs [rT, rCS, rCL] (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) c _ ⟨hF, hst, hb, hcp, hj', hn, her⟩ hGr, by rw [hAg.reg _ (by decide), hnp]⟩
        · simp +decide [prCpA, run_addc, run_mov, hcp]
        · simp +decide [prCpA, run_addc, run_mov, hF.1.rk, hl1]
      have hB := HGB.frame (copy_spec (S := S) PB (b + encOff rs j + 1)
        (cycPre pg n k t ++ prJ k rs j).flatten rs[j].1
        (by rw [hsel, List.flatten_singleton] at hlen; rw [List.length_append]; omega))
        (F := fun c => G c ∧ c.reg gNP = (cycPre pg n k t ++ prJ k rs j).length)
        ((hGs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).and
          (by stab))
      have hC : HGB S (inc gNP) (wregs prCp)
          (fun c => Strm PB ((cycPre pg n k t ++ prJ k rs j).flatten ++ rs[j].1) c ∧
            (G c ∧ c.reg gNP = (cycPre pg n k t ++ prJ k rs j).length))
          (fun c => G c ∧ Strm PB (cycPre pg n k t ++ prJ k rs (j + 1)).flatten c ∧
            c.reg gNP = (cycPre pg n k t ++ prJ k rs (j + 1)).length) 2 := by
        refine (HGB.runM (s := inc gNP) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
        have hAg : Agree [rT, gNP] c (RAM.run (inc gNP) c) :=
          agree_run (by decide) rfl rfl (by decide) c
        obtain ⟨hS, hG, hnp⟩ := hc
        rw [hsuc, hsel, ← List.append_assoc, List.flatten_append, List.flatten_singleton]
        refine ⟨hGs [rT, gNP] (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          c _ hG (grow_of_agree hAg (by decide) (by decide)), strm_agree hAg (by decide) hS, ?_⟩
        simp +decide [run_inc, hnp]
        omega
      exact ((hA.seq ((hB.mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl).seq hC)).mono
        (by decide) (fun _ h => h) (fun _ h => h) (by omega))
    · refine HGB.of_pre (fun c h => show ¬ rs[j].2 = k - 1 from fun h' => h.2 (h.1.2.2.mpr h'))
        fun hl => ?_
      have hsel : sel k rs[j] = [] := by simp [sel, hl]
      refine (HGB.skip' (W := wregs prLoop)).mono (by decide) (fun _ h => h) ?_ (by omega)
      rintro c ⟨⟨⟨hI, hj', hn⟩, her, -⟩, -⟩
      obtain ⟨hF, hst, hb, hS, hnp, hcp⟩ := hiff.mp hI
      rw [hsuc, hsel, List.append_nil]
      exact ⟨⟨hF, hst, hb, hcp, hj', hn, her⟩, hS, hnp⟩
  -- advancing
  have h₃ : HGB S cAdv (wregs prLoop)
      (fun c => G c ∧ Strm PB (cycPre pg n k t ++ prJ k rs (j + 1)).flatten c ∧
        c.reg gNP = (cycPre pg n k t ++ prJ k rs (j + 1)).length)
      (fun c => PrInv pg n k L F m₂ t b (j + 1) c ∧ c.reg rCJ2 = j ∧ c.reg rCN = rs.length) 3 := by
    refine (HGB.runM (s := cAdv) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rT, rCP] c (RAM.run cAdv c) := agree_run (by decide) rfl rfl (by decide) c
    have hGr := grow_of_agree (W := [rT, rCP]) hA (by decide) (by decide)
    obtain ⟨⟨hF, hst, hb, hcp, hj', hn, her⟩, hS, hnp⟩ := hc
    refine ⟨hiff.mpr ⟨PoFr.stable hL m₂ (by omega) (by decide) c _ hF hGr,
      by rw [hA.reg _ (by decide), hst], by rw [hA.mem, hb], strm_agree hA (by decide) hS,
      by rw [hA.reg _ (by decide), hnp], ?_⟩, by rw [hA.reg _ (by decide), hj'],
      by rw [hA.reg _ (by decide), hn]⟩
    simp +decide only [cAdv, run_seq', run_add, run_addc (show rCP ≠ rT by decide), setReg_reg,
      ↓reduceIte, hcp, her, encOff_succ hj, hrl]
    omega
  exact (h₁.seq (h₂.seq h₃)).weaken (by unfold TPr; omega)

theorem prLoop_spec {S : ℕ} (hP : IsPolygon pg n) {L : Lay} (hL : LayOK pg n L) (hk : 1 ≤ k)
    (F : ℕ) (m₂ : ℕ → ℕ) {t : ℕ} (ht : t < (segOrder pg n).length) (b : ℕ)
    (hSz : F + ((segOrder pg n).length + 1) + (cycPre pg n k t ++
      prJ k (fin pg n k (segOrder pg n)[t]) (fin pg n k (segOrder pg n)[t]).length).flatten.length
      ≤ S) :
    HGB S prLoop (wregs prLoop)
      (fun c => PrInv pg n k L F m₂ t b 0 c ∧ c.reg rCN = (fin pg n k (segOrder pg n)[t]).length)
      (fun c => PrInv pg n k L F m₂ t b (fin pg n k (segOrder pg n)[t]).length c ∧
        c.reg rCJ2 = (fin pg n k (segOrder pg n)[t]).length ∧
        c.reg rCN = (fin pg n k (segOrder pg n)[t]).length)
      (Poly.partsBound k * (TPr k + 4) + 3) :=
  HGB.forUpCle (W := wregs prLoop) (i := rCJ2) (n := rCN) (body := prBody)
    (PrInv pg n k L F m₂ t b) (TPr k) _ (fin_bound hP _).1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (fun j => (PrInv.indep L F m₂ t b j).mono (by decide))
    (fun j hj => prBody_spec hP hL hk F m₂ ht b j hj (by
      have : (prJ k (fin pg n k (segOrder pg n)[t]) (j + 1)).flatten.length ≤
          (prJ k (fin pg n k (segOrder pg n)[t])
            (fin pg n k (segOrder pg n)[t]).length).flatten.length :=
        flatten_flatMap_take_le _ _ (by omega)
      simp only [List.flatten_append, List.length_append] at hSz ⊢
      omega))

/-! ### One segment -/

/-- The invariant of stage P before the segment `t`. -/
def PoInv (pg : Graph) (n k : ℕ) (L : Lay) (F : ℕ) (m₂ : ℕ → ℕ) (t : ℕ) (c : Config) : Prop :=
  PoFr pg n k L F m₂ t c ∧ Strm (F + ((segOrder pg n).length + 1)) (cycPre pg n k t).flatten c ∧
    c.reg gNP = (cycPre pg n k t).length

theorem PoInv.indep (L : Lay) (F : ℕ) (m₂ : ℕ → ℕ) (t : ℕ) :
    Indep [rSt, rT] (PoInv pg n k L F m₂ t) := by
  indep [PoInv, PoFr, qCtx_iff, Strm]

theorem poBody_spec {S : ℕ} (hP : IsPolygon pg n) {L : Lay} (hL : LayOK pg n L) (hk : 3 ≤ k)
    (F : ℕ) (m₂ : ℕ → ℕ) {t : ℕ} (ht : t < (segOrder pg n).length)
    (hSz : F + ((segOrder pg n).length + 1) + (cycPre pg n k (t + 1)).flatten.length ≤ S) :
    HTB S poBody
      (fun c => PoInv pg n k L F m₂ t c ∧ c.reg rSt = t ∧ c.reg gNS = (segOrder pg n).length)
      (fun c => PoInv pg n k L F m₂ (t + 1) c ∧ c.reg rSt = t ∧
        c.reg gNS = (segOrder pg n).length) (TPo k) := by
  set PB := F + ((segOrder pg n).length + 1) with hPB
  -- recording the start of the cycles of `t`
  have he : cycPre pg n k t ++ prJ k (fin pg n k (segOrder pg n)[t])
      (fin pg n k (segOrder pg n)[t]).length = cycPre pg n k (t + 1) := by
    rw [cycPre_succ hP hk ht, prJ, List.take_length]
  have h₁ : HTB S (st gTST rSt gNP)
      (fun c => PoInv pg n k L F m₂ t c ∧ c.reg rSt = t ∧ c.reg gNS = (segOrder pg n).length)
      (fun c => PoFr pg n k L F m₂ (t + 1) c ∧ c.reg rSt = t ∧
        Strm PB (cycPre pg n k t).flatten c ∧ c.reg gNP = (cycPre pg n k t).length) 2 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hF, hS, hnp⟩, hst, _⟩ => ?_
    obtain ⟨hQ, hT, hPl, hm₂, hTab, hle⟩ := hF
    refine ⟨by addr_ok [hT, hst], ?_⟩
    have hrun : RAM.run (st gTST rSt gNP) c = (c.setMem (F + t) (cycPre pg n k t).length).setReg rT
        (F + t) := by
      rw [run_st (by decide), hT, hst, hnp]
    have hreg : ∀ r, r ≠ rT → (RAM.run (st gTST rSt gNP) c).reg r = c.reg r := by
      intro r hr; rw [hrun]; simp [hr]
    have hmem : (RAM.run (st gTST rSt gNP) c).mem = upd c.mem (F + t) (cycPre pg n k t).length := by
      rw [hrun]; simp
    have hFr := hQ.le
    have hSm : SameOn (· < F) c.mem (RAM.run (st gTST rSt gNP) c).mem := by
      rw [hmem]; exact (SameOn.refl _ _).upd_of_ge (by omega) _
    have hfree := hS.2.1
    refine ⟨⟨hQ.of_below hL (fun r hr => hreg r (by simp at hr; rcases hr with h | h | h | h | h | h |
        h | h <;> (subst h; decide))) hSm (by rw [hreg _ (by decide)]; exact hFr),
      by rw [hreg _ (by decide), hT], by rw [hreg _ (by decide), hPl], hm₂.trans hSm, ?_,
      by rw [hreg _ (by decide)]; exact hle⟩, by rw [hreg _ (by decide), hst], ?_,
      by rw [hreg _ (by decide), hnp]⟩
    · rw [hmem]
      exact (hTab.upd_of_disjoint (by omega)).snoc (by simp)
    · obtain ⟨h1, h2, h3⟩ := hS
      refine ⟨by rw [hmem]; exact h1.upd_of_disjoint (by omega), by rw [hreg _ (by decide)]; exact h2,
        by rw [hreg _ (by decide), hmem]; exact h3.upd (by omega)⟩
  -- finding the records
  have h₂ : HGB S poRd (wregs poBody)
      (fun c => PoFr pg n k L F m₂ (t + 1) c ∧ c.reg rSt = t ∧
        Strm PB (cycPre pg n k t).flatten c ∧ c.reg gNP = (cycPre pg n k t).length)
      (fun c => ∃ b, PrInv pg n k L F m₂ t b 0 c ∧ c.reg rCN = (fin pg n k (segOrder pg n)[t]).length) 4 := by
    refine (HGB.runR (s := poRd) (by decide) (by decide) (by decide) (by decide) (by decide)
      fun c hc => ?_).mono (by decide) (fun _ h => h) (fun _ h => h) le_rfl
    have hA : Agree [rCP, rCN] c (RAM.run poRd c) := agree_run (by decide) rfl rfl (by decide) c
    have hGr := grow_of_agree (W := [rCP, rCN]) hA (by decide) (by decide)
    obtain ⟨hF, hst, hS, hnp⟩ := hc
    have := hF.1.data.le; have := hL.fc; have := hL.fr
    refine ⟨by addr_ok [poRd, hF.1.rfb, hF.1.rfc, hst], ?_⟩
    obtain ⟨-, -, -, h4⟩ := hF.1.data.fin t ht
    refine ⟨c.mem (L.fb + t), (prInv_iff ht).mpr ⟨PoFr.stable hL m₂ (by omega) (by decide) c _ hF hGr,
      by rw [hA.reg _ (by decide), hst], by rw [hA.mem], by simpa [prJ_zero] using strm_agree hA (by decide) hS,
      by rw [hA.reg _ (by decide), hnp]; simp, ?_⟩, ?_⟩
    · simp +decide [poRd, hF.1.rfb, hst, encOff]
    · simp +decide [poRd, hF.1.rfc, hst, h4]
  have h₃ : HGB S prLoop (wregs poBody)
      (fun c => ∃ b, PrInv pg n k L F m₂ t b 0 c ∧ c.reg rCN = (fin pg n k (segOrder pg n)[t]).length)
      (fun c => PoInv pg n k L F m₂ (t + 1) c ∧ c.reg rSt = t ∧
        c.reg gNS = (segOrder pg n).length) (Poly.partsBound k * (TPr k + 4) + 3) := by
    refine HGB.exists_pre fun b => ?_
    refine (prLoop_spec hP hL (by omega) F m₂ ht b (by rw [he]; exact hSz)).mono (by decide)
      (fun _ h => h) ?_ le_rfl
    rintro c ⟨hI, -, -⟩
    obtain ⟨hF, hst, -, hS, hnp, -⟩ := (prInv_iff ht).mp hI
    rw [he] at hS hnp
    exact ⟨⟨hF, hS, hnp⟩, hst, hF.1.ns⟩
  exact (h₁.seq (h₂.seq h₃).toHTB).weaken (by unfold TPo; omega)

/-! ### Stage P -/

/-- After stage P: the pool, its size, `topStarts` at `F`, the constants and data. -/
def PoOut (pg : Graph) (n k : ℕ) (L : Lay) (F : ℕ) (m₂ : ℕ → ℕ) (c : Config) : Prop :=
  QCtx pg n k L F c ∧ c.reg gTST = F ∧ c.reg gPOOL = F + ((segOrder pg n).length + 1) ∧
    SameOn (· < F) m₂ c.mem ∧ Arr c.mem F (topStarts pg n k) ∧
    Strm (F + ((segOrder pg n).length + 1)) (pool pg n k).flatten c ∧
    c.reg gNP = (pool pg n k).length

/-- **Stage P**: from the state after stage R (with `k - 1` in `rKm1`), the pool and
`topStarts`, in `O(|segOrder| * k * partsBound k)` steps. -/
theorem stageP_spec {S : ℕ} (hP : IsPolygon pg n) {L : Lay} (hL : LayOK pg n L) (hk : 3 ≤ k)
    (m₁ : ℕ → ℕ) (F : ℕ) (m₂ : ℕ → ℕ)
    (hSz : F + ((segOrder pg n).length + 1) + (pool pg n k).flatten.length ≤ S) :
    HTB S stageP
      (fun c => SegInv pg n k L m₁ (segOrder pg n).length c ∧ c.reg rKm1 = k - 1 ∧
        c.reg rFREE = F ∧ c.mem = m₂)
      (PoOut pg n k L F m₂) ((segOrder pg n).length * (TPo k + 4) + 13) := by
  have h₀ : HTB S poInit
      (fun c => SegInv pg n k L m₁ (segOrder pg n).length c ∧ c.reg rKm1 = k - 1 ∧
        c.reg rFREE = F ∧ c.mem = m₂)
      (fun c => PoInv pg n k L F m₂ 0 c ∧ c.reg gNS = (segOrder pg n).length) 8 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨hI, hkm, hF, hm⟩ => ?_
    refine ⟨by addr_ok [poInit], ?_⟩
    have hD := hI.dataB
    have hR := hI.1.1
    rw [hF, hm] at hD
    have hreg : ∀ r ∈ [rK, rKm1, gPN, gNS, gSA, gSB, rFB, rFC],
        (RAM.run poInit c).reg r = c.reg r := fun r hr =>
      run_reg_of_not_mem (by decide) (by simp at hr; rcases hr with h | h | h | h | h | h | h | h <;>
        (subst h; decide)) c
    have hmem : (RAM.run poInit c).mem = c.mem := run_mem_of_stores (by decide) rfl c
    have hfree : (RAM.run poInit c).reg rFREE = F + ((segOrder pg n).length + 1) := by
      simp +decide [poInit, run_addc, run_alloc, run_mov, hR.ns, hF]
    have hQ : QCtx pg n k L F (RAM.run poInit c) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hmem, hm]; exact hD, by omega⟩
      all_goals rw [hreg _ (by simp)]
      exacts [hR.rk, hkm, hR.pn, hR.ns, hR.rsa, hR.rsb, hR.rfb, hR.rfc]
    refine ⟨⟨⟨hQ, ?_, ?_, by rw [hmem, hm]; exact SameOn.refl _ _, by simp, by omega⟩,
      ⟨by simp [cycPre_zero], by rw [hfree]; simp [cycPre_zero], ?_⟩, ?_⟩, by rw [hreg _ (by simp), hR.ns]⟩
    · simp +decide [poInit, run_addc, run_alloc, run_mov, hF]
    · simp +decide [poInit, run_addc, run_alloc, run_mov, hR.ns, hF]
    · rw [hfree, hmem]
      have := hI.2
      unfold Zf at this
      rw [hF] at this
      exact this.mono (by omega)
    · simp +decide [poInit, cycPre_zero]
  have hl := HTB.forUp (S := S) (i := rSt) (n := gNS) (N := (segOrder pg n).length)
    (body := poBody) (PoInv pg n k L F m₂) (fun _ => TPo k) (by decide) (by decide) (by decide)
    (fun t => PoInv.indep L F m₂ t)
    (fun t ht => poBody_spec hP hL hk F m₂ ht (by
      have := cycPre_le_pool (pg := pg) (n := n) (k := k) (show t + 1 ≤ (segOrder pg n).length by
        omega)
      omega))
  have h₂ : HTB S poFin (fun c => PoInv pg n k L F m₂ (segOrder pg n).length c ∧
      c.reg rSt = (segOrder pg n).length ∧ c.reg gNS = (segOrder pg n).length)
      (PoOut pg n k L F m₂) 2 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hF, hS, hnp⟩, _, hns⟩ => ?_
    obtain ⟨hQ, hT, hPl, hm₂, hTab, hle⟩ := hF
    refine ⟨by addr_ok [poFin, hT, hns], ?_⟩
    have hrun : RAM.run poFin c = (c.setMem (F + (segOrder pg n).length)
        (cycPre pg n k (segOrder pg n).length).length).setReg rT (F + (segOrder pg n).length) := by
      rw [poFin, run_st (by decide), hT, hns, hnp]
    have hreg : ∀ r, r ≠ rT → (RAM.run poFin c).reg r = c.reg r := by
      intro r hr; rw [hrun]; simp [hr]
    have hmem : (RAM.run poFin c).mem =
        upd c.mem (F + (segOrder pg n).length) (cycPre pg n k (segOrder pg n).length).length := by
      rw [hrun]; simp
    have hFr := hQ.le
    have hSm : SameOn (· < F) c.mem (RAM.run poFin c).mem := by
      rw [hmem]; exact (SameOn.refl _ _).upd_of_ge (by omega) _
    have hfree := hS.2.1
    rw [cycPre_full] at hS hnp
    refine ⟨hQ.of_below hL (fun r hr => hreg r (by simp at hr; rcases hr with h | h | h | h | h | h |
        h | h <;> (subst h; decide))) hSm (by rw [hreg _ (by decide)]; exact hFr),
      by rw [hreg _ (by decide), hT], by rw [hreg _ (by decide), hPl], hm₂.trans hSm, ?_, ?_,
      by rw [hreg _ (by decide), hnp]⟩
    · rw [topStarts_eq, hmem]
      exact ((hTab.upd_of_disjoint (by omega)).snoc (by simp)).toArr
    · obtain ⟨h1, h2, h3⟩ := hS
      refine ⟨by rw [hmem]; exact h1.upd_of_disjoint (by omega), by rw [hreg _ (by decide)]; exact h2,
        by rw [hreg _ (by decide), hmem]; exact h3.upd (by omega)⟩
  refine (h₀.seq ((hl.pre fun c h => h).seq h₂)).weaken ?_
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

end STACS2027.RAM.P2