module

public import Runtimes.BoundedCost.TernaryScan
public import Runtimes.BoundedCost.CallerRegisters
import Mathlib.Tactic

/-! Renamed ternary controls permit an actual separator subprogram to be inserted
between iterations without renaming its reserved workspace registers. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3

def renamedTernaryLoop (φ : ℕ → ℕ) (body : Stmt) : Stmt :=
  forUp (φ wordIndex) (φ wordCount) (.seq body (renameRegisters φ odo))

def renamedTernaryScan (φ : ℕ → ℕ) (body : Stmt) : Stmt :=
  .seq (renameRegisters φ (powTo wordCount rOL)) (renamedTernaryLoop φ body)

theorem not_mem_renameRegisters_wregs {φ : ℕ → ℕ} (hφ : Function.Injective φ)
    {program : Stmt} {r : ℕ} (h : r ∉ wregs program) :
    φ r ∉ wregs (renameRegisters φ program) := by
  rw [renameRegisters_wregs]
  rintro hm
  obtain ⟨s, hs, he⟩ := List.mem_map.mp hm
  exact h (hφ he ▸ hs)

theorem renamedTernaryLoop_spec {α : Type*} {S ob depth B : ℕ} {body : Stmt}
    (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (hindex : φ wordIndex ≠ rT) (hcount : φ wordCount ≠ rT)
    (G : Config → Prop)
    (hG : RegIndep (φ wordIndex :: rT :: wregs (renameRegisters φ odo)) G)
    (hGr : ∀ c, G c → c.reg (φ rOB) = ob ∧ c.reg (φ rOL) = depth ∧ c.reg (φ rK) = 3)
    (Fr : α → List ℕ → (ℕ → ℕ) → Prop)
    (hrd : ∀ a ds memory, Fr a ds memory → Arr memory ob ds)
    (hupd : ∀ a ds memory i v, Fr a ds memory → i < ds.length →
      Fr a (ds.set i v) (upd memory (ob + i) v))
    (F : α → List ℕ → α) (a : α) (hS : ob + depth ≤ S)
    (hbody : ∀ word < 3 ^ depth, ∀ state,
      HTB S body
        (fun c => (G c ∧ Fr state (Poly.cfg 3 depth word) c.mem) ∧
          c.reg (φ wordIndex) = word ∧ c.reg (φ wordCount) = 3 ^ depth)
        (fun c => (G c ∧ Fr (F state (Poly.cfg 3 depth word)) (Poly.cfg 3 depth word) c.mem) ∧
          c.reg (φ wordIndex) = word ∧ c.reg (φ wordCount) = 3 ^ depth) B) :
    HTB S (renamedTernaryLoop φ body)
      (fun c => (G c ∧ Fr a (Poly.cfg 3 depth 0) c.mem) ∧ c.reg (φ wordCount) = 3 ^ depth)
      (fun c => (G c ∧ Fr (ternaryFold F depth (3 ^ depth) a) (Poly.cfg 3 depth 0) c.mem) ∧
        c.reg (φ wordIndex) = 3 ^ depth ∧ c.reg (φ wordCount) = 3 ^ depth)
      (3 ^ depth * (B + depth * 19 + 8) + 3) := by
  let Inv := fun word c => G c ∧
    Fr (ternaryFold F depth word a) (Poly.cfg 3 depth word) c.mem
  have hloop := HTB.forUpC (S := S) (i := φ wordIndex) (n := φ wordCount) (N := 3 ^ depth)
    (body := .seq body (renameRegisters φ odo)) Inv (B + depth * 19 + 4)
    hindex hcount (fun h => (by decide : wordCount ≠ wordIndex) (hφ h))
    (fun word => by
      intro c c' ha ⟨hg, hf⟩
      refine ⟨hG.indep.mono (by simp) c c' ha hg, ?_⟩
      rw [ha.mem]
      exact hf)
    (fun word hw => by
      have hb := hbody word hw (ternaryFold F depth word a)
      let state := F (ternaryFold F depth word a) (Poly.cfg 3 depth word)
      let Logical := fun c : Config => c.reg rOB = ob ∧
        c.reg rOL = (Poly.cfg 3 depth word).length ∧ c.reg rK = 3
      have hodo := odo_spec (S := S) (k := 3) (ob := ob) (ds := Poly.cfg 3 depth word)
        Logical (by indep [Logical, odo, odoBody, forUp, upLoop, wregs, ld, st, inc, addc, ifEq])
        (fun c hc => hc) (Fr state) (hrd state) (hupd state) (by simpa using hS)
      let Physical := fun c : Config => G c ∧ c.reg (φ wordIndex) = word ∧
        c.reg (φ wordCount) = 3 ^ depth
      have hPhysical : RegIndep (wregs (renameRegisters φ odo)) Physical := by
        intro c c' hag ⟨hg, hi, hn⟩
        refine ⟨hG.mono (fun r hr => List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ hr)) c c' hag hg, ?_, ?_⟩
        · rw [hag _ (not_mem_renameRegisters_wregs hφ (by decide))]; exact hi
        · rw [hag _ (not_mem_renameRegisters_wregs hφ (by decide))]; exact hn
      have ho := (renameRegisters_htb hφ hodo).frameReg hPhysical
      have ho' : HTB S (renameRegisters φ odo)
          (fun c => (G c ∧ Fr state (Poly.cfg 3 depth word) c.mem) ∧
            c.reg (φ wordIndex) = word ∧ c.reg (φ wordCount) = 3 ^ depth)
          (fun c => Inv (word + 1) c ∧ c.reg (φ wordIndex) = word ∧
            c.reg (φ wordCount) = 3 ^ depth) (depth * 19 + 4) := by
        refine ho.mono ?_ ?_ (by simp)
        · rintro c ⟨⟨hg, hf⟩, hi, hn⟩
          obtain ⟨hob, hol, hk⟩ := hGr c hg
          refine ⟨⟨?_, hf⟩, hg, hi, hn⟩
          exact ⟨hob, by simpa [registerView] using hol, hk⟩
        · rintro c ⟨⟨_, hf⟩, hg, hi, hn⟩
          rw [odoL_cfg (by decide)] at hf
          exact ⟨⟨hg, by simpa [Inv, state, ternaryFold_succ, registerView] using hf⟩, hi, hn⟩
      exact (hb.seq ho').weaken (by omega))
  refine hloop.mono (fun c hc => by simpa [Inv, ternaryFold_zero] using hc) ?_
    (by rw [show B + depth * 19 + 4 + 4 = B + depth * 19 + 8 by omega])
  intro c hc
  simpa [Inv, cfg_pow (k := 3) (by decide) depth] using hc

theorem renamedTernaryScan_spec {α : Type*} {S ob depth B : ℕ} {body : Stmt}
    (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (hindex : φ wordIndex ≠ rT) (hcount : φ wordCount ≠ rT)
    (G : Config → Prop)
    (hG : RegIndep ((φ wordIndex :: rT :: wregs (renameRegisters φ odo)) ++
      wregs (renameRegisters φ (powTo wordCount rOL))) G)
    (hGr : ∀ c, G c → c.reg (φ rOB) = ob ∧ c.reg (φ rOL) = depth ∧ c.reg (φ rK) = 3)
    (Fr : α → List ℕ → (ℕ → ℕ) → Prop)
    (hrd : ∀ a ds memory, Fr a ds memory → Arr memory ob ds)
    (hupd : ∀ a ds memory i v, Fr a ds memory → i < ds.length →
      Fr a (ds.set i v) (upd memory (ob + i) v))
    (F : α → List ℕ → α) (a : α) (hS : ob + depth ≤ S)
    (hbody : ∀ word < 3 ^ depth, ∀ state,
      HTB S body
        (fun c => (G c ∧ Fr state (Poly.cfg 3 depth word) c.mem) ∧
          c.reg (φ wordIndex) = word ∧ c.reg (φ wordCount) = 3 ^ depth)
        (fun c => (G c ∧ Fr (F state (Poly.cfg 3 depth word)) (Poly.cfg 3 depth word) c.mem) ∧
          c.reg (φ wordIndex) = word ∧ c.reg (φ wordCount) = 3 ^ depth) B) :
    HTB S (renamedTernaryScan φ body)
      (fun c => G c ∧ Fr a (Poly.cfg 3 depth 0) c.mem)
      (fun c => (G c ∧ Fr (ternaryFold F depth (3 ^ depth) a) (Poly.cfg 3 depth 0) c.mem) ∧
        c.reg (φ wordIndex) = 3 ^ depth ∧ c.reg (φ wordCount) = 3 ^ depth)
      (depth * 25 + 8 + (3 ^ depth * (B + depth * 19 + 8) + 3)) := by
  let Logical := fun c : Config => c.reg rK = 3 ∧ c.reg rOL = depth
  have hp := powTo_spec (k := 3) (e := depth) (dst := wordCount) (src := rOL)
    Logical (by indep [Logical, pow, powBody, forUp, upLoop])
    (fun c hc => hc) (by decide) (by decide) (by decide)
  have hpr := renameRegisters_htb hφ (HTB.of_HT (S := S) (by decide) hp)
  have hg := hpr.frameReg (hG.mono (fun r hr => List.mem_append_right _ hr))
  have hpf := hg.frameIndep (by simp [renameRegisters_stores]; decide)
    (by simp [renameRegisters_writes]; decide)
    (F := fun c => Fr a (Poly.cfg 3 depth 0) c.mem)
    (by intro c c' ha hf; rw [ha.mem]; exact hf)
  have hprefix : HTB S (renameRegisters φ (powTo wordCount rOL))
      (fun c => G c ∧ Fr a (Poly.cfg 3 depth 0) c.mem)
      (fun c => (G c ∧ Fr a (Poly.cfg 3 depth 0) c.mem) ∧ c.reg (φ wordCount) = 3 ^ depth)
      (depth * 25 + 8) := by
    refine hpf.mono ?_ ?_ (by omega)
    · intro c ⟨hc, hf⟩
      exact ⟨⟨⟨(hGr c hc).2.2, (hGr c hc).2.1⟩, hc⟩, hf⟩
    · intro c ⟨⟨⟨_, hcount⟩, hc⟩, hf⟩
      exact ⟨⟨hc, hf⟩, hcount⟩
  exact hprefix.seq (renamedTernaryLoop_spec φ hφ hindex hcount G
    (hG.mono (fun r hr => List.mem_append_left _ hr)) hGr Fr hrd hupd F a hS hbody)

end STACS2027.Runtimes.BoundedCost
