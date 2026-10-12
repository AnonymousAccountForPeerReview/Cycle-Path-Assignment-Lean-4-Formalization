module

public import Runtimes.C4.OrientRAM
public import Outerplanar.RAM.BoundedLib
import Mathlib.Tactic

/-!
# Phase SIZE: the number of inserted 2-paths

From an `OrientPost g` configuration, the program `sizeP` computes
`gP = Σ_{v<N} Σ_{a<|out v|} (|out (out v)[a]| + a)`, which is `numPaths g (peelPos g)`
(`numPaths_eq`), by two nested counted loops reading `ODEG` and `OADJ`. It neither stores nor
allocates.

**`size_spec`**: `SizePost g` within `CS · (m + 1)` steps, reading only below the initial
`rFREE`. Also the readers
`OrientPost.odegR`, `OrientPost.oadjR` (the out-degrees and out-lists in a later memory that
agrees below the initial `rFREE`), used by ENUM.
-/

@[expose] public section

namespace STACS2027.Runtimes.C4

open STACS2027 STACS2027.Algo STACS2027.RAM Finset

/-! ### The program -/

/-- The `a`-th out-neighbour `j` of `v`: `P += ODEG[j] + a`. -/
def sizeInner : Stmt :=
  .seq (.add xQ xOv xA) (.seq (ld xW gOADJ xQ) (.seq (ld xD gODEG xW) (.seq (.add gP gP xD)
    (.add gP gP xA))))

/-- One vertex `v = xV`. -/
def sizeOuter : Stmt := .seq (.seq (ld xOv gOFF xV) (ld xDv gODEG xV)) (forUp xA xDv sizeInner)

/-- **Phase SIZE.** -/
def sizeP : Stmt := .seq (.const gP 0) (forUp xV gN sizeOuter)

/-! ### Reading the out-lists -/

section read

variable {g : Graph} {c₀ : Config} {m : ℕ → ℕ}

theorem OrientPost.odegR (h : OrientPost g c₀) (hS : SameOn (· < c₀.reg rFREE) c₀.mem m)
    {v : ℕ} (hv : v < numV g) : m (c₀.reg gODEG + v) = (outL g (peelPos g) v).length :=
  (h.odeg.of_below hS h.below.1).get hv

theorem OrientPost.oadjR (h : OrientPost g c₀) (hS : SameOn (· < c₀.reg rFREE) c₀.mem m)
    {v a : ℕ} (hv : v < numV g) (ha : a < (outL g (peelPos g) v).length) :
    m (c₀.reg gOADJ + (R1.ps (idEdges g) v + a)) = (outL g (peelPos g) v).getD a 0 := by
  have h1 := R1.ps_add_le (idEdges g) (show v < numV g from hv)
  have h2 := R1.idEdges_ps g
  have h3 : (outL g (peelPos g) v).length ≤ (nbOf (idEdges g) v).length := length_outL_le _ _ _
  have hA := (h.oadj v hv).of_below hS (by have := h.below.2; omega)
  rw [← Nat.add_assoc]
  exact hA.getD ha

end read

/-! ### The sums -/

/-- The contribution of the `a`-th out-neighbour of `v`. -/
def term (g : Graph) (v a : ℕ) : ℕ :=
  (outL g (peelPos g) ((outL g (peelPos g) v).getD a 0)).length + a

/-- The contribution of `v`. -/
def rowSum (g : Graph) (v : ℕ) : ℕ := ∑ a ∈ range (outL g (peelPos g) v).length, term g v a

theorem numPaths_eq_rowSum (g : Graph) :
    numPaths g (peelPos g) = ∑ v ∈ range (numV g), rowSum g v := numPaths_eq g (peelPos g)

/-! ### Invariants -/

/-- The registers and memory fixed during SIZE. -/
@[mk_iff] structure SGlob (g : Graph) (c₀ c : Config) : Prop where
  n : c.reg gN = numV g
  off : c.reg gOFF = c₀.reg gOFF
  odeg : c.reg gODEG = c₀.reg gODEG
  oadj : c.reg gOADJ = c₀.reg gOADJ
  mem : c.mem = c₀.mem

theorem SGlob.indep (g : Graph) (c₀ : Config) :
    Indep [rT, xV, xA, xOv, xDv, xQ, xW, xD, gP] (SGlob g c₀) := by
  indep [sGlob_iff]

/-- The outer invariant: the vertices `u < v` are summed. -/
def SOInv (g : Graph) (c₀ : Config) (v : ℕ) (c : Config) : Prop :=
  SGlob g c₀ c ∧ c.reg gP = ∑ u ∈ range v, rowSum g u

/-- The inner invariant: vertex `v`, its first `a` out-neighbours summed. -/
def SIInv (g : Graph) (c₀ : Config) (v a : ℕ) (c : Config) : Prop :=
  SGlob g c₀ c ∧ c.reg gP = ∑ u ∈ range v, rowSum g u + ∑ a' ∈ range a, term g v a' ∧
    c.reg xOv = R1.ps (idEdges g) v ∧ c.reg xV = v

section

variable {g : Graph} {c₀ : Config} {S : ℕ}

theorem sizeInner_spec (hO : OrientPost g c₀) (hSp : c₀.reg rFREE ≤ S) {v a : ℕ}
    (hv : v < numV g) (ha : a < (outL g (peelPos g) v).length) :
    HTB S sizeInner (fun c => SIInv g c₀ v a c ∧ c.reg xA = a ∧
        c.reg xDv = (outL g (peelPos g) v).length)
      (fun c => SIInv g c₀ v (a + 1) c ∧ c.reg xA = a ∧
        c.reg xDv = (outL g (peelPos g) v).length) 7 := by
  refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hP, hOv, hV⟩, hA, hD⟩ => ?_
  obtain ⟨j, hj⟩ : ∃ j, (outL g (peelPos g) v).getD a 0 = j := ⟨_, rfl⟩
  have hjN : j < numV g := lt_of_mem_outL (pos := peelPos g) (v := v)
    (by rw [← hj, getD_eq_getElem' ha]; exact List.getElem_mem _)
  have hS : SameOn (· < c₀.reg rFREE) c₀.mem c.mem := by rw [hG.mem]; exact SameOn.refl _ _
  have hoa := hO.oadjR hS hv ha
  rw [hj] at hoa
  have hod := hO.odegR hS hjN
  have ht : term g v a = (outL g (peelPos g) j).length + a := by rw [term, hj]
  have hAd : AddrOK S sizeInner c := by
    have hb := hO.below
    have h1 : R1.ps (idEdges g) v + (nb g v).length ≤ R1.ps (idEdges g) (numV g) :=
      R1.ps_add_le (idEdges g) hv
    have h2 : (outL g (peelPos g) v).length ≤ (nb g v).length := length_outL_le _ _ _
    rw [R1.idEdges_ps] at h1
    addr_ok [sizeInner, hG.oadj, hG.odeg, hOv, hA, hoa]
  refine ⟨hAd, ?_⟩
  have hG' : SGlob g c₀ (run sizeInner c) :=
    (SGlob.indep g c₀).mono (W' := [xQ, xW, xD, gP]) (by decide) c _
      (agree_run (by decide) rfl rfl (by decide) c) hG
  refine ⟨⟨hG', ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [sizeInner, run_seq', run_add, run_ld, setReg_reg, setReg_mem]
    simp +decide only [↓reduceIte, hG.oadj, hG.odeg, hOv, hA, hP, hoa, hod, sum_range_succ, ht]
    ring
  all_goals simp +decide [sizeInner, hOv, hA, hV, hD]

theorem sizeOuter_spec (hO : OrientPost g c₀) (hSp : c₀.reg rFREE ≤ S) {v : ℕ}
    (hv : v < numV g) :
    HTB S sizeOuter (fun c => SOInv g c₀ v c ∧ c.reg xV = v ∧ c.reg gN = numV g)
      (fun c => SOInv g c₀ (v + 1) c ∧ c.reg xV = v ∧ c.reg gN = numV g)
      (4 + ((outL g (peelPos g) v).length * (7 + 4) + 3)) := by
  have h₁ : HTB S (.seq (ld xOv gOFF xV) (ld xDv gODEG xV))
      (fun c => SOInv g c₀ v c ∧ c.reg xV = v ∧ c.reg gN = numV g)
      (fun c => SIInv g c₀ v 0 c ∧ c.reg xDv = (outL g (peelPos g) v).length) 4 := by
    refine HTB.run_le (by decide) (by decide) fun c ⟨⟨hG, hP⟩, hV, _⟩ => ?_
    have hb := hO.below
    have hb' := hO.peel.base.bounds
    refine ⟨by addr_ok [hG.off, hG.odeg, hV], ?_⟩
    have hS : SameOn (· < c₀.reg rFREE) c₀.mem c.mem := by rw [hG.mem]; exact SameOn.refl _ _
    have hof := hO.peel.base.offR hS (show v ≤ numV g by omega)
    have hod := hO.odegR hS hv
    have hG' : SGlob g c₀ (run (.seq (ld xOv gOFF xV) (ld xDv gODEG xV)) c) :=
      (SGlob.indep g c₀).mono (W' := [xOv, xDv]) (by decide) c _
        (agree_run (by decide) rfl rfl (by decide) c) hG
    refine ⟨⟨hG', ?_, ?_, ?_⟩, ?_⟩
    all_goals simp +decide [hG.off, hG.odeg, hV, hP, hof, hod]
  have h₂ := HTB.forUpC (S := S) (i := xA) (n := xDv) (N := (outL g (peelPos g) v).length)
    (body := sizeInner) (SIInv g c₀ v) 7 (by decide) (by decide) (by decide)
    (fun a => by
      unfold SIInv
      exact ((SGlob.indep g c₀).mono (by decide)).and
        ((Indep.reg (W := [xA, rT]) (r := gP) (by decide)
          (· = ∑ u ∈ range v, rowSum g u + ∑ a' ∈ range a, term g v a')).and
          ((Indep.reg (W := [xA, rT]) (r := xOv) (by decide) (· = R1.ps (idEdges g) v)).and
            (Indep.reg (W := [xA, rT]) (r := xV) (by decide) (· = v)))))
    (fun a ha => sizeInner_spec hO hSp hv ha)
  refine (h₁.seq (h₂.post (Q' := fun c => SOInv g c₀ (v + 1) c ∧ c.reg xV = v ∧
    c.reg gN = numV g) fun c ⟨⟨hG, hP, _, hV⟩, _, _⟩ => ⟨⟨hG, ?_⟩, hV, hG.n⟩))
  rw [hP, sum_range_succ, rowSum]

theorem size_wregs : ∀ r ∈ wregs sizeP, r = rT ∨ (36 ≤ r ∧ r < 50) ∨ (100 ≤ r ∧ r < 150) := by
  decide

theorem size_stores : stores sizeP = false := by decide

theorem size_writes : writes sizeP = false := by decide

/-- The constant of the running time of SIZE. -/
def CS : ℕ := 60

/-- **Phase SIZE**: from an `OrientPost g` configuration, `sizeP` computes
`gP = numPaths g (peelPos g)` (`SizePost g`) within `CS · (m + 1)` steps, without stores and
without output, reading only below the initial `rFREE` (`≤ S`). -/
theorem size_spec (g : Graph) (c₀ : Config) (hSp : c₀.reg rFREE ≤ S) :
    HTB S sizeP (fun c => OrientPost g c ∧ c = c₀)
      (fun c => SizePost g c ∧ c.out = c₀.out ∧ c.mem = c₀.mem ∧ c.reg rFREE = c₀.reg rFREE)
      (CS * (g.length + 1)) := by
  intro c ⟨hO, hc⟩
  subst hc
  have hn := hO.peel.base.r1.base.n
  have h₀ : HTB S (.const gP 0) (fun c' => c' = c) (fun c' => SOInv g c 0 c' ∧ c'.reg gN = numV g)
      1 := HTB.of_HT rfl <| HT.run_le trivial le_rfl fun c' hc' => by
    subst hc'
    exact ⟨⟨⟨by simp +decide [hn], by simp +decide, by simp +decide, by simp +decide, rfl⟩,
      by simp⟩, by simp +decide [hn]⟩
  have hl := HTB.forUp (S := S) (i := xV) (n := gN) (N := numV g) (body := sizeOuter) (SOInv g c)
    (fun v => 4 + ((outL g (peelPos g) v).length * (7 + 4) + 3)) (by decide) (by decide)
    (by decide)
    (fun v => by
      unfold SOInv
      exact ((SGlob.indep g c).mono (by decide)).and
        (Indep.reg (W := [xV, rT]) (r := gP) (by decide) (· = ∑ u ∈ range v, rowSum g u)))
    (fun v hv => sizeOuter_spec hO hSp hv)
  have h := h₀.seq hl
  obtain ⟨c', t, he, ⟨⟨⟨hG, hP⟩, _, _⟩, hfr⟩, ht⟩ := h.withFrame c c ⟨rfl, rfl⟩
  have hreg : ∀ r, r < 36 → r ≠ rT → r ≠ rFREE → c'.reg r = c.reg r := fun r hr h1 _ =>
    hfr.reg r fun hm => by rcases size_wregs r hm with h | h | h <;> omega
  have hF : c'.reg rFREE = c.reg rFREE := hfr.reg rFREE (fun hm => by
    rcases size_wregs rFREE hm with h | h | h <;> revert h <;> decide)
  refine ⟨c', t, he, ⟨⟨hO.transfer hreg (by rw [hG.mem]; exact SameOn.refl _ _) (by omega)
    (by rw [hG.mem, hF]; exact hO.peel.base.r1.base.free), by rw [hP, numPaths_eq_rowSum]⟩,
    hfr.out size_writes, hG.mem, hF⟩, ?_⟩
  have hs : ∑ v ∈ range (numV g), (4 + ((outL g (peelPos g) v).length * (7 + 4) + 3) + 4) =
      11 * numV g + 11 * ∑ v ∈ range (numV g), (outL g (peelPos g) v).length := by
    rw [← sum_affine]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hs] at ht
  have h1 := numV_le g
  have h2 := length_idEdges_le g
  have h3 := sum_length_outL_le g (peelPos g)
  simp only [CS]
  omega

end

end STACS2027.Runtimes.C4
