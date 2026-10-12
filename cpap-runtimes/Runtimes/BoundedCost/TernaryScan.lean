module

public import Outerplanar.RAM.Poly3Odo
public import Runtimes.BoundedCost.SearchPaths
import Mathlib.Tactic

/-! The uniform RAM loop over all ternary branch vectors. The exponent is supplied
in a register, so this is one finite program for all deletion budgets. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3

abbrev wordIndex : ℕ := 180
abbrev wordCount : ℕ := 181

/-- Scan every vector, advancing its in-memory digits with the verified odometer. -/
def ternaryLoop (body : Stmt) : Stmt :=
  forUp wordIndex wordCount (.seq body odo)

/-- Compute the vector count from the input exponent, then perform the scan. -/
def ternaryScan (body : Stmt) : Stmt :=
  .seq (powTo wordCount rOL) (ternaryLoop body)

def ternaryFold {α : Type*} (F : α → List ℕ → α) (depth count : ℕ) (a : α) : α :=
  (List.range count).foldl (fun a word => F a (Poly.cfg 3 depth word)) a

theorem ternaryFold_zero {α : Type*} (F : α → List ℕ → α) (depth : ℕ) (a : α) :
    ternaryFold F depth 0 a = a := rfl

theorem ternaryFold_succ {α : Type*} (F : α → List ℕ → α) (depth count : ℕ) (a : α) :
    ternaryFold F depth (count + 1) a = F (ternaryFold F depth count a) (Poly.cfg 3 depth count) := by
  simp [ternaryFold, List.range_succ, List.foldl_append]

/-- Bounded execution of the complete branch-vector loop. The supplied body is an
ordinary RAM subprogram with a bounded Hoare proof, rather than a host-language oracle. -/
theorem ternaryLoop_spec {α : Type*} {S ob depth B : ℕ} {body : Stmt}
    (G : Config → Prop)
    (hG : RegIndep (wordIndex :: rT :: wregs odo) G)
    (hGr : ∀ c, G c → c.reg rOB = ob ∧ c.reg rOL = depth ∧ c.reg rK = 3)
    (Fr : α → List ℕ → (ℕ → ℕ) → Prop)
    (hrd : ∀ a ds memory, Fr a ds memory → Arr memory ob ds)
    (hupd : ∀ a ds memory i v, Fr a ds memory → i < ds.length →
      Fr a (ds.set i v) (upd memory (ob + i) v))
    (F : α → List ℕ → α) (a : α) (hS : ob + depth ≤ S)
    (hbody : ∀ word < 3 ^ depth, ∀ state,
      HTB S body
        (fun c => (G c ∧ Fr state (Poly.cfg 3 depth word) c.mem) ∧
          c.reg wordIndex = word ∧ c.reg wordCount = 3 ^ depth)
        (fun c => (G c ∧ Fr (F state (Poly.cfg 3 depth word)) (Poly.cfg 3 depth word) c.mem) ∧
          c.reg wordIndex = word ∧ c.reg wordCount = 3 ^ depth) B) :
    HTB S (ternaryLoop body)
      (fun c => (G c ∧ Fr a (Poly.cfg 3 depth 0) c.mem) ∧ c.reg wordCount = 3 ^ depth)
      (fun c => (G c ∧ Fr (ternaryFold F depth (3 ^ depth) a) (Poly.cfg 3 depth 0) c.mem) ∧
        c.reg wordIndex = 3 ^ depth ∧ c.reg wordCount = 3 ^ depth)
      (3 ^ depth * (B + depth * 19 + 8) + 3) := by
  let Inv := fun word c => G c ∧
    Fr (ternaryFold F depth word a) (Poly.cfg 3 depth word) c.mem
  have hloop := HTB.forUpC (S := S) (i := wordIndex) (n := wordCount) (N := 3 ^ depth)
    (body := .seq body odo) Inv (B + depth * 19 + 4)
    (by decide) (by decide) (by decide)
    (fun word => by
      intro c c' ha ⟨hg, hf⟩
      refine ⟨hG.indep.mono (by simp) c c' ha hg, ?_⟩
      rw [ha.mem]
      exact hf)
    (fun word hw => by
      have hb := hbody word hw (ternaryFold F depth word a)
      let state := F (ternaryFold F depth word a) (Poly.cfg 3 depth word)
      let Gr := fun c => G c ∧ c.reg wordIndex = word ∧ c.reg wordCount = 3 ^ depth
      have hodo := odo_spec (S := S) (k := 3) (ob := ob) (ds := Poly.cfg 3 depth word)
        Gr (by
          intro c c' ha ⟨hg, hi, hn⟩
          refine ⟨hG c c' (fun r hr => ha r (by
            intro hm
            exact hr (by simp [hm]))) hg, ?_, ?_⟩
          · rw [ha _ (by decide)]; exact hi
          · rw [ha _ (by decide)]; exact hn)
        (fun c hc => ⟨(hGr c hc.1).1,
          by rw [(hGr c hc.1).2.1, Poly.length_cfg], (hGr c hc.1).2.2⟩)
        (Fr state) (hrd state) (hupd state) (by simpa using hS)
      have ho : HTB S odo
          (fun c => (G c ∧ Fr state (Poly.cfg 3 depth word) c.mem) ∧
            c.reg wordIndex = word ∧ c.reg wordCount = 3 ^ depth)
          (fun c => Inv (word + 1) c ∧
            c.reg wordIndex = word ∧ c.reg wordCount = 3 ^ depth)
          (depth * 19 + 4) := by
        refine hodo.mono (fun c hc => ⟨⟨hc.1.1, hc.2.1, hc.2.2⟩, hc.1.2⟩) ?_ (by simp)
        rintro c ⟨⟨hg, hi, hn⟩, hf⟩
        rw [odoL_cfg (by decide)] at hf
        exact ⟨⟨hg, by simpa [Inv, state, ternaryFold_succ] using hf⟩, hi, hn⟩
      exact (hb.seq ho).weaken (by omega))
  refine hloop.mono (fun c hc => by simpa [Inv, ternaryFold_zero] using hc) ?_
    (by rw [show B + depth * 19 + 4 + 4 = B + depth * 19 + 8 by omega])
  intro c hc
  simpa [Inv, cfg_pow (k := 3) (by decide) depth] using hc

/-- The vector count is computed by RAM arithmetic, so the scan needs no exponential
integer supplied from outside the machine. -/
theorem ternaryScan_spec {α : Type*} {S ob depth B : ℕ} {body : Stmt}
    (G : Config → Prop)
    (hG : RegIndep ((wordIndex :: rT :: wregs odo) ++
      (rT :: rPE :: wordCount :: wregs pow)) G)
    (hGr : ∀ c, G c → c.reg rOB = ob ∧ c.reg rOL = depth ∧ c.reg rK = 3)
    (Fr : α → List ℕ → (ℕ → ℕ) → Prop)
    (hrd : ∀ a ds memory, Fr a ds memory → Arr memory ob ds)
    (hupd : ∀ a ds memory i v, Fr a ds memory → i < ds.length →
      Fr a (ds.set i v) (upd memory (ob + i) v))
    (F : α → List ℕ → α) (a : α) (hS : ob + depth ≤ S)
    (hbody : ∀ word < 3 ^ depth, ∀ state,
      HTB S body
        (fun c => (G c ∧ Fr state (Poly.cfg 3 depth word) c.mem) ∧
          c.reg wordIndex = word ∧ c.reg wordCount = 3 ^ depth)
        (fun c => (G c ∧ Fr (F state (Poly.cfg 3 depth word)) (Poly.cfg 3 depth word) c.mem) ∧
          c.reg wordIndex = word ∧ c.reg wordCount = 3 ^ depth) B) :
    HTB S (ternaryScan body)
      (fun c => G c ∧ Fr a (Poly.cfg 3 depth 0) c.mem)
      (fun c => (G c ∧ Fr (ternaryFold F depth (3 ^ depth) a) (Poly.cfg 3 depth 0) c.mem) ∧
        c.reg wordIndex = 3 ^ depth ∧ c.reg wordCount = 3 ^ depth)
      (depth * 25 + 8 + (3 ^ depth * (B + depth * 19 + 8) + 3)) := by
  have hGpow : Indep (rT :: rPE :: wordCount :: wregs pow) G :=
    hG.indep.mono (fun r hr => List.mem_append_right _ hr)
  have hp := powTo_spec (k := 3) (e := depth) (dst := wordCount) (src := rOL)
    G hGpow (fun c hc => ⟨(hGr c hc).2.2, (hGr c hc).2.1⟩)
    (by decide) (by decide) (by decide)
  have hpf := (HTB.of_HT (S := S) (by decide) hp).frameIndep (by decide) (by decide)
    (F := fun c => Fr a (Poly.cfg 3 depth 0) c.mem)
    (by intro c c' ha hf; rw [ha.mem]; exact hf)
  have hprefix : HTB S (powTo wordCount rOL)
      (fun c => G c ∧ Fr a (Poly.cfg 3 depth 0) c.mem)
      (fun c => (G c ∧ Fr a (Poly.cfg 3 depth 0) c.mem) ∧ c.reg wordCount = 3 ^ depth)
      (depth * 25 + 8) :=
    hpf.mono (fun _ hc => hc) (fun _ hc => ⟨⟨hc.1.1, hc.2⟩, hc.1.2⟩) (by omega)
  have hl := ternaryLoop_spec G
    (hG.mono (fun r hr => List.mem_append_left _ hr)) hGr Fr hrd hupd F a hS hbody
  exact hprefix.seq hl

end STACS2027.Runtimes.BoundedCost
