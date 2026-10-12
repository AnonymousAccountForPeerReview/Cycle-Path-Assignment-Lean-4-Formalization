module

public import Runtimes.ConvexQP.RAM.KmoLayout
import Mathlib.Tactic

/-!
# Phases K, M, O on the RAM: two generic loops

* `cpLoop`: `dst_j := ±src_j` for `j < n`, source at `kPS` with stride `kSS` (stride `0` fills
  from one cell), destination at `kPD` with stride `kSD ≥ 2`, sign `−` iff `kNG ≠ 0`
  (`cpLoop_spec`: `c.mem = wrArr m₀ pd sd (sgnMul ng ∘ f) n`, `27 n + 3` steps).
* `gather`: `dst_a := (pair at mem[pt + a] + off)` for `a < n`, destination contiguous at `kPD`
  (`gather_spec`: `c.mem = wrArr m₀ pd 2 g n`, `17 n + 3` steps).
-/

@[expose] public section

namespace STACS2027.Runtimes.QPRam.Kmo

open STACS2027 STACS2027.RAM STACS2027.Runtimes.Arith STACS2027.Runtimes.ConvexQP

/-- `z` (`ng = 0`) or `−z`. -/
def sgnMul (ng : ℕ) (z : ℤ) : ℤ := if ng = 0 then z else -z

/-- A triple with an unsatisfiable precondition. -/
theorem HT.of_false {s : Stmt} {P Q : Config → Prop} {b : ℕ} (h : ∀ c, P c → False) :
    HT s P Q b := fun c hc => (h c hc).elim

variable {S : ℕ}

/-! ### The copy loop -/

/-- One element: `dst := ±src`, advance both pointers. -/
def cpBody : Stmt :=
  .seq (sload kX kPS) (.seq (.ifz kNG .skip (sneg kX kX)) (.seq (sstore kPD kX)
    (.seq (.add kPS kPS kSS) (.add kPD kPD kSD))))

/-- `dst_j := ±src_j` for `j < reg kN`. -/
def cpLoop : Stmt := forUp kJ kN cpBody

/-- The registers written by `cpLoop`. -/
def cpW : List ℕ := kJ :: kPS :: kPD :: kX :: (kX + 1) :: arithW

theorem wregs_cpLoop : ∀ r ∈ wregs cpLoop, r ∈ cpW := by decide

/-- The fixed registers of a copy step. -/
def CG (R : Config → Prop) (ss sd ng : ℕ) (c : Config) : Prop :=
  R c ∧ c.reg kSS = ss ∧ c.reg kSD = sd ∧ c.reg kNG = ng

theorem CG_regIndep {R : Config → Prop} (hR : RegIndep cpW R) (ss sd ng : ℕ) :
    RegIndep cpW (CG R ss sd ng) :=
  hR.and (by indep)

/-- **One copy step** (the source pair and the destination pair below `S`). -/
theorem cpBody_spec {R : Config → Prop} (hR : RegIndep cpW R) (m : ℕ → ℕ) (ps ss pd sd ng : ℕ)
    (z : ℤ) (hz : SMem m ps z) (hSs : ps + 1 < S) (hSd : pd + 1 < S) :
    HTB S cpBody (fun c => CG R ss sd ng c ∧ c.mem = m ∧ c.reg kPS = ps ∧ c.reg kPD = pd)
      (fun c => CG R ss sd ng c ∧ c.mem = sw m pd (sgnMul ng z) ∧ c.reg kPS = ps + ss ∧
        c.reg kPD = pd + sd) 23 := by
  have hG := CG_regIndep hR ss sd ng
  let P : Config → Prop := fun c => CG R ss sd ng c ∧ c.mem = m ∧ c.reg kPD = pd ∧ c.reg kPS = ps
  have hP : ∀ {W : List ℕ}, (∀ r ∈ W, r ∈ arithW ∨ r = kX ∨ r = kX + 1) → Indep W P :=
    fun hW => ((hG.mono fun r hr => by
      rcases hW r hr with h | h | h
      · simp only [cpW, List.mem_cons]; tauto
      · subst h; decide
      · subst h; decide).indep).and
      ((Indep.mem (· = m)).and ((Indep.reg (r := kPD) (fun h => by
        rcases hW _ h with h | h | h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact absurd h (by decide)) (· = pd)).and (Indep.reg (r := kPS) (fun h => by
        rcases hW _ h with h | h | h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact absurd h (by decide)) (· = ps))))
  have h1 := HTB.sload (P := P) (d := kX) (p := kPS) (a := ps) (z := z) (by decide) (by decide)
    (by decide) (hP (by decide)) hSs
  have h2 : HTB S (.ifz kNG .skip (sneg kX kX)) (fun c => P c ∧ SReg c kX z)
      (fun c => P c ∧ SReg c kX (sgnMul ng z)) 13 := HTB.of_HT rfl <| by
    have hneg := HT.sneg (P := P) (d := kX) (x := kX) (u := z) (by decide) (by decide)
      (hP (fun r hr => by
        simp only [List.mem_cons] at hr
        rcases hr with rfl | rfl | hr
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl hr))
    by_cases hng : ng = 0
    · refine (HT.ifz (P := fun c => P c ∧ SReg c kX z) ?_ ?_).weaken le_rfl
      · exact (HT.skip.weaken (by omega)).mono (fun c h => h)
          (fun c ⟨⟨hc, hx⟩, _⟩ => ⟨hc, by simpa [sgnMul, hng] using hx⟩) le_rfl
      · exact HT.of_false fun c ⟨⟨hc, _⟩, h0⟩ => h0 (hc.1.2.2.2.trans hng)
    · refine (HT.ifz (P := fun c => P c ∧ SReg c kX z) ?_ ?_).weaken le_rfl
      · exact HT.of_false fun c ⟨⟨hc, _⟩, h0⟩ => hng (hc.1.2.2.2.symm.trans h0)
      · exact hneg.mono (fun c ⟨hc, _⟩ => hc)
          (fun c ⟨hc, hx⟩ => ⟨hc, by simpa [sgnMul, hng] using hx⟩) le_rfl
  have h3 := HTB.sstore (F := fun c => CG R ss sd ng c ∧ c.reg kPS = ps) (p := kPD) (x := kX)
    (a := pd) (z := sgnMul ng z) (m := m) (by decide) (by decide) (by decide)
    ((hG.mono (by decide)).and (by indep)) hSd
  have h4 : HTB S (.seq (.add kPS kPS kSS) (.add kPD kPD kSD))
      (fun c => ((CG R ss sd ng c ∧ c.reg kPS = ps) ∧ SReg c kX (sgnMul ng z) ∧ c.reg kPD = pd ∧
        c.mem = upd (upd m pd (sgnBit (sgnMul ng z))) (pd + 1) (sgnMul ng z).natAbs))
      (fun c => CG R ss sd ng c ∧ c.mem = sw m pd (sgnMul ng z) ∧ c.reg kPS = ps + ss ∧
        c.reg kPD = pd + sd) 2 :=
    HTB.of_HT rfl <| HT.run_le (by decide) (by decide) fun c ⟨⟨⟨hRc, hss, hsd, hng⟩, hps⟩, _, hpd, hm⟩ => by
      refine ⟨⟨(hR.mono (by decide)).run (by decide) hRc, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
      simp +decide only [run_seq', run_add, setReg_reg, setReg_mem, ↓reduceIte, hss, hsd, hng, hps,
        hpd, hm]
      rfl
  refine ((h1.pre fun c ⟨hc, hm, hps, hpd⟩ => ⟨⟨hc, hm, hpd, hps⟩, hps, by rw [hm]; exact hz⟩).seq
    (h2.seq ((h3.pre fun c ⟨⟨hc, _, hpd, hps⟩, hx⟩ => ⟨⟨hc, hps⟩, hx, hpd, by assumption⟩).seq
      h4))).weaken (by omega)

/-- The state of the copy loop after `j` elements. -/
def CInv (R : Config → Prop) (m₀ : ℕ → ℕ) (ps ss pd sd ng : ℕ) (f : ℕ → ℤ) (j : ℕ)
    (c : Config) : Prop :=
  CG R ss sd ng c ∧ c.mem = wrArr m₀ pd sd (fun j => sgnMul ng (f j)) j ∧
    c.reg kPS = ps + j * ss ∧ c.reg kPD = pd + j * sd

/-- **The copy loop** `dst_j := ±src_j` (`j < n`): source `f` at `ps + j ss` (readable in every
memory that agrees with `m₀` outside the destination block), destination `pd + j sd`
(`sd ≥ 2`), sign `−` iff `ng ≠ 0`; `27 n + 3` steps. `R`: any register-only assertion not about
`cpW`. Space: the source pairs (`hSs`) and the destination block (`hSd`) below `S`. -/
theorem cpLoop_spec {R : Config → Prop} (hR : RegIndep cpW R) (m₀ : ℕ → ℕ) (n ps ss pd sd ng : ℕ)
    (f : ℕ → ℤ) (hsd : 2 ≤ sd)
    (hf : ∀ m, SameOn (fun a => ¬ (pd ≤ a ∧ a < pd + n * sd)) m₀ m →
      ∀ j < n, SMem m (ps + j * ss) (f j))
    (hSs : ∀ j < n, ps + j * ss + 1 < S) (hSd : pd + n * sd ≤ S) :
    HTB S cpLoop (fun c => R c ∧ c.mem = m₀ ∧ c.reg kN = n ∧ c.reg kPS = ps ∧ c.reg kSS = ss ∧
        c.reg kPD = pd ∧ c.reg kSD = sd ∧ c.reg kNG = ng)
      (fun c => R c ∧ c.mem = wrArr m₀ pd sd (fun j => sgnMul ng (f j)) n) (n * 27 + 3) := by
  have hl := HTB.forUpC (S := S) (i := kJ) (n := kN) (N := n) (body := cpBody)
    (CInv R m₀ ps ss pd sd ng f) 23 (by decide) (by decide) (by decide)
    (fun j => ((CG_regIndep hR ss sd ng).mono (by decide)).indep.and (by indep))
    (fun j hj => by
      have hsame : SameOn (fun a => ¬ (pd ≤ a ∧ a < pd + n * sd)) m₀
          (wrArr m₀ pd sd (fun j => sgnMul ng (f j)) j) := fun a ha =>
        sameOn_wrArr hsd j a (by
          have : j * sd ≤ n * sd := Nat.mul_le_mul_right sd (by omega)
          omega)
      have hb := (cpBody_spec hR (wrArr m₀ pd sd (fun j => sgnMul ng (f j)) j) (ps + j * ss) ss
        (pd + j * sd) sd ng (f j) (hf _ hsame j hj) (hSs j hj)
        (lt_of_lt_of_le (entry_lt hsd hj) hSd)).frameReg
        (F := fun c => c.reg kJ = j ∧ c.reg kN = n) (by indep)
      refine hb.mono (fun c ⟨⟨hc, hm, hps, hpd⟩, hk, hn⟩ => ⟨⟨hc, hm, hps, hpd⟩, hk, hn⟩)
        (fun c ⟨⟨hc, hm, hps, hpd⟩, hk, hn⟩ => ⟨⟨hc, ?_, by rw [hps]; ring, by rw [hpd]; ring⟩,
          hk, hn⟩) le_rfl
      rw [hm, wrArr_succ])
  refine (hl.pre fun c ⟨hc, hm, hn, hps, hss, hpd, hsd', hng⟩ =>
    ⟨⟨⟨hc, hss, hsd', hng⟩, hm, by simpa using hps, by simpa using hpd⟩, hn⟩).mono
    (fun _ h => h) (fun c ⟨⟨hc, hm, _⟩, _⟩ => ⟨hc.1, hm⟩) le_rfl

/-! ### The gather loop -/

/-- One element: `dst := (pair at mem[pt + j] + off)`, advance the destination. -/
def gaBody : Stmt :=
  .seq (ld kA kPS kJ) (.seq (.add kA kA kSS) (.seq (sload kX kA) (.seq (sstore kPD kX)
    (addc kPD kPD 2))))

/-- `dst_a := (pair at mem[pt + a] + off)` for `a < reg kN`. -/
def gather : Stmt := forUp kJ kN gaBody

/-- The registers written by `gather`. -/
def gaW : List ℕ := [kJ, kA, kPD, kX, kX + 1, rT]

theorem wregs_gather : ∀ r ∈ wregs gather, r ∈ gaW := by decide

/-- The state of the gather loop after `j` elements. -/
def GInv (R : Config → Prop) (m₀ : ℕ → ℕ) (pt off pd : ℕ) (g : ℕ → ℤ) (j : ℕ) (c : Config) :
    Prop :=
  R c ∧ c.reg kPS = pt ∧ c.reg kSS = off ∧ c.mem = wrArr m₀ pd 2 g j ∧ c.reg kPD = pd + j * 2

/-- **The gather loop** `dst_a := (pair at P a + off)` with `P a = mem[pt + a]` (`a < n`),
destination contiguous at `pd`; `17 n + 3` steps. Space: the table (`hSt`), the source pairs
(`hSg`) and the destination block (`hSd`) below `S`. -/
theorem gather_spec {R : Config → Prop} (hR : RegIndep gaW R) (m₀ : ℕ → ℕ) (n pt off pd : ℕ)
    (P : ℕ → ℕ) (g : ℕ → ℤ)
    (hg : ∀ m, SameOn (fun a => ¬ (pd ≤ a ∧ a < pd + n * 2)) m₀ m →
      ∀ a < n, m (pt + a) = P a ∧ SMem m (P a + off) (g a))
    (hSt : pt + n ≤ S) (hSg : ∀ a < n, P a + off + 1 < S) (hSd : pd + n * 2 ≤ S) :
    HTB S gather (fun c => R c ∧ c.mem = m₀ ∧ c.reg kN = n ∧ c.reg kPS = pt ∧ c.reg kSS = off ∧
        c.reg kPD = pd)
      (fun c => R c ∧ c.mem = wrArr m₀ pd 2 g n) (n * 17 + 3) := by
  have hl := HTB.forUpC (S := S) (i := kJ) (n := kN) (N := n) (body := gaBody)
    (GInv R m₀ pt off pd g) 13 (by decide) (by decide) (by decide)
    (fun j => (hR.mono (by decide)).indep.and (by indep))
    (fun j hj => by
      set mj := wrArr m₀ pd 2 g j with hmj
      have hsame : SameOn (fun a => ¬ (pd ≤ a ∧ a < pd + n * 2)) m₀ mj := fun a ha =>
        sameOn_wrArr (le_refl 2) j a (by omega)
      obtain ⟨hP, hv⟩ := hg mj hsame j hj
      refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hc, hpt, hoff, hm, hpd⟩, hk, hn⟩ => ?_
      have hA : AddrOK S gaBody c := by
        have h1 := hSg j hj
        have h2 := lt_of_lt_of_le (entry_lt (b := pd) (le_refl 2) hj) hSd
        have hP' : wrArr m₀ pd 2 g j (pt + j) = P j := hP
        addr_ok [gaBody, sload, sstore, hpt, hk, hoff, hm, hpd, hP']
      refine ⟨hA, ?_⟩
      have hsw : (RAM.run gaBody c).mem = wrArr m₀ pd 2 g (j + 1) := by
        rw [wrArr_succ]
        simp +decide only [gaBody, sload, sstore, run_seq', run_ld, run_add, run_load, run_addc,
          run_store, setReg_reg, setReg_mem, setMem_reg, setMem_mem_upd, ↓reduceIte, hpt, hk, hoff,
          hm, hpd]
        rw [← hmj, hP, hv.1, hv.2]
        rfl
      refine ⟨⟨(hR.mono (by decide)).run (by decide) hc, ?_, ?_, hsw, ?_⟩, ?_, ?_⟩ <;>
      simp +decide only [gaBody, sload, sstore, run_seq', run_ld, run_add, run_load, run_addc,
        run_store, setReg_reg, setReg_mem, setMem_reg, ↓reduceIte, hpt, hk, hoff, hpd, hn]
      ring)
  refine (hl.pre fun c ⟨hc, hm, hn, hpt, hoff, hpd⟩ =>
    ⟨⟨hc, hpt, hoff, hm, by simpa using hpd⟩, hn⟩).mono
    (fun _ h => h) (fun c ⟨⟨hc, _, _, hm, _⟩, _⟩ => ⟨hc, hm⟩) le_rfl

end STACS2027.Runtimes.QPRam.Kmo
