module

public import Runtimes.BoundedCost.TernaryControl
import Mathlib.Tactic

/-! The complete ternary control loop preserves state assertions involving both
registers and memory; in particular it carries the concrete success flag. -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost

open STACS2027 STACS2027.RAM STACS2027.RAM.P3

theorem renamedOdo_state_spec {α : Type*} {S ob : ℕ} (φ : ℕ → ℕ)
    (hφ : Function.Injective φ) (Rep : α → List ℕ → Config → Prop)
    (hindep : ∀ a ds, Indep (wregs (renameRegisters φ odo)) (Rep a ds))
    (hrep : ∀ a ds c, Rep a ds c → c.reg (φ rOB) = ob ∧ c.reg (φ rOL) = ds.length ∧
      c.reg (φ rK) = 3 ∧ Arr c.mem ob ds)
    (hupd : ∀ a ds c i v, Rep a ds c → i < ds.length →
      Rep a (ds.set i v) (c.setMem (ob + i) v))
    (a : α) (ds : List ℕ) (hS : ob + ds.length ≤ S) :
    HTB S (renameRegisters φ odo) (Rep a ds) (Rep a (odoL 3 ds)) (ds.length * 19 + 4) := by
  intro c hc
  let Fr := fun digits memory => Rep a digits (⟨c.reg, memory, c.out⟩ : Config)
  let Logical := fun C : Config => C.reg rOB = ob ∧ C.reg rOL = ds.length ∧ C.reg rK = 3
  have hLogical : RegIndep (wregs odo) Logical := by
    indep [Logical, odo, odoBody, forUp, upLoop, wregs, ld, st, inc, addc, ifEq]
  have ho := odo_spec (S := S) (k := 3) (ob := ob) (ds := ds) Logical hLogical
    (fun C hC => hC) Fr (fun digits memory h => (hrep a digits _ h).2.2.2)
    (fun digits memory i v h hi => hupd a digits _ i v h hi) hS
  have hop := renameRegisters_htb hφ ho
  obtain ⟨hob, hol, hk, ht⟩ := hrep a ds c hc
  obtain ⟨d, time, he, hd, htime⟩ := hop c ⟨⟨hob, hol, hk⟩, hc⟩
  have hstate : Rep a (odoL 3 ds) d := by
    apply hindep a (odoL 3 ds) (⟨c.reg, d.mem, c.out⟩ : Config) d
    · refine ⟨fun r hr => he.reg_frame hr, rfl, ?_⟩
      exact he.out_frame (by simp [renameRegisters_writes]; decide)
    · exact hd.2
  exact ⟨d, time, he, hstate, htime⟩

theorem renamedTernaryLoop_state_spec {α : Type*} {S ob depth B : ℕ} {body : Stmt}
    (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (hindex : φ wordIndex ≠ rT) (hcount : φ wordCount ≠ rT)
    (Rep : α → List ℕ → Config → Prop)
    (hindep : ∀ a ds, Indep (φ wordIndex :: rT :: wregs (renameRegisters φ odo)) (Rep a ds))
    (hrep : ∀ a ds c, Rep a ds c → c.reg (φ rOB) = ob ∧ c.reg (φ rOL) = ds.length ∧
      c.reg (φ rK) = 3 ∧ Arr c.mem ob ds)
    (hupd : ∀ a ds c i v, Rep a ds c → i < ds.length →
      Rep a (ds.set i v) (c.setMem (ob + i) v))
    (F : α → List ℕ → α) (a : α) (hS : ob + depth ≤ S)
    (hbody : ∀ word < 3 ^ depth, ∀ state,
      HTB S body
        (fun c => Rep state (Poly.cfg 3 depth word) c ∧
          c.reg (φ wordIndex) = word ∧ c.reg (φ wordCount) = 3 ^ depth)
        (fun c => Rep (F state (Poly.cfg 3 depth word)) (Poly.cfg 3 depth word) c ∧
          c.reg (φ wordIndex) = word ∧ c.reg (φ wordCount) = 3 ^ depth) B) :
    HTB S (renamedTernaryLoop φ body)
      (fun c => Rep a (Poly.cfg 3 depth 0) c ∧ c.reg (φ wordCount) = 3 ^ depth)
      (fun c => Rep (ternaryFold F depth (3 ^ depth) a) (Poly.cfg 3 depth 0) c ∧
        c.reg (φ wordIndex) = 3 ^ depth ∧ c.reg (φ wordCount) = 3 ^ depth)
      (3 ^ depth * (B + depth * 19 + 8) + 3) := by
  let Inv := fun word c => Rep (ternaryFold F depth word a) (Poly.cfg 3 depth word) c
  have hl := HTB.forUpC (S := S) (i := φ wordIndex) (n := φ wordCount)
    (N := 3 ^ depth) (body := .seq body (renameRegisters φ odo)) Inv (B + depth * 19 + 4)
    hindex hcount (fun h => (by decide : wordCount ≠ wordIndex) (hφ h))
    (fun word => (hindep _ _).mono (by simp)) (fun word hw => by
      have hb := hbody word hw (ternaryFold F depth word a)
      let state := F (ternaryFold F depth word a) (Poly.cfg 3 depth word)
      have ho := renamedOdo_state_spec φ hφ Rep
        (fun a ds => (hindep a ds).mono (fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
        hrep
        hupd state (Poly.cfg 3 depth word) (by simpa using hS)
      have hof := ho.frameReg (F := fun c => c.reg (φ wordIndex) = word ∧
          c.reg (φ wordCount) = 3 ^ depth) (by
            intro c d hag ⟨hi, hn⟩
            refine ⟨?_, ?_⟩
            · rw [hag _ (not_mem_renameRegisters_wregs hφ (by decide))]; exact hi
            · rw [hag _ (not_mem_renameRegisters_wregs hφ (by decide))]; exact hn)
      have ho' : HTB S (renameRegisters φ odo)
            (fun c => Rep state (Poly.cfg 3 depth word) c ∧
              c.reg (φ wordIndex) = word ∧ c.reg (φ wordCount) = 3 ^ depth)
            (fun c => Inv (word + 1) c ∧ c.reg (φ wordIndex) = word ∧
              c.reg (φ wordCount) = 3 ^ depth) (depth * 19 + 4) := by
        refine hof.mono (fun c hc => ⟨hc.1, hc.2⟩) ?_ (by simp)
        intro c ⟨hr, hi, hn⟩
        rw [odoL_cfg (by decide)] at hr
        exact ⟨by simpa [Inv, state, ternaryFold_succ] using hr, hi, hn⟩
      exact (hb.seq ho').weaken (by omega))
  refine hl.mono (fun c hc => by simpa [Inv, ternaryFold_zero] using hc) ?_
    (by rw [show B + depth * 19 + 4 + 4 = B + depth * 19 + 8 by omega])
  intro c hc
  simpa [Inv, cfg_pow (k := 3) (by decide) depth] using hc

theorem renamedTernaryScan_state_spec {α : Type*} {S ob depth B : ℕ} {body : Stmt}
    (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (hindex : φ wordIndex ≠ rT) (hcount : φ wordCount ≠ rT)
    (Rep : α → List ℕ → Config → Prop)
    (hindep : ∀ a ds, Indep ((φ wordIndex :: rT :: wregs (renameRegisters φ odo)) ++
      wregs (renameRegisters φ (powTo wordCount rOL))) (Rep a ds))
    (hrep : ∀ a ds c, Rep a ds c → c.reg (φ rOB) = ob ∧ c.reg (φ rOL) = ds.length ∧
      c.reg (φ rK) = 3 ∧ Arr c.mem ob ds)
    (hupd : ∀ a ds c i v, Rep a ds c → i < ds.length →
      Rep a (ds.set i v) (c.setMem (ob + i) v))
    (F : α → List ℕ → α) (a : α) (hS : ob + depth ≤ S)
    (hbody : ∀ word < 3 ^ depth, ∀ state,
      HTB S body
        (fun c => Rep state (Poly.cfg 3 depth word) c ∧
          c.reg (φ wordIndex) = word ∧ c.reg (φ wordCount) = 3 ^ depth)
        (fun c => Rep (F state (Poly.cfg 3 depth word)) (Poly.cfg 3 depth word) c ∧
          c.reg (φ wordIndex) = word ∧ c.reg (φ wordCount) = 3 ^ depth) B) :
    HTB S (renamedTernaryScan φ body)
      (Rep a (Poly.cfg 3 depth 0))
      (fun c => Rep (ternaryFold F depth (3 ^ depth) a) (Poly.cfg 3 depth 0) c ∧
        c.reg (φ wordIndex) = 3 ^ depth ∧ c.reg (φ wordCount) = 3 ^ depth)
      (depth * 25 + 8 + (3 ^ depth * (B + depth * 19 + 8) + 3)) := by
  let Logical := fun c : Config => c.reg rK = 3 ∧ c.reg rOL = depth
  have hp := powTo_spec (k := 3) (e := depth) (dst := wordCount) (src := rOL)
    Logical (by indep [Logical, pow, powBody, forUp, upLoop]) (fun c hc => hc)
    (by decide) (by decide) (by decide)
  have hpr := renameRegisters_htb hφ (HTB.of_HT (S := S) (by decide) hp)
  have hpf := hpr.frameIndep (by simp [renameRegisters_stores]; decide)
    (by simp [renameRegisters_writes]; decide)
    (F := Rep a (Poly.cfg 3 depth 0))
    ((hindep a _).mono (fun r hr => List.mem_append_right _ hr))
  have hprefix : HTB S (renameRegisters φ (powTo wordCount rOL))
      (Rep a (Poly.cfg 3 depth 0))
      (fun c => Rep a (Poly.cfg 3 depth 0) c ∧ c.reg (φ wordCount) = 3 ^ depth)
      (depth * 25 + 8) := by
    refine hpf.mono ?_ ?_ (by omega)
    · intro c hc
      obtain ⟨_, hdepth, hk, _⟩ := hrep a _ c hc
      exact ⟨⟨hk, by simpa [registerView] using hdepth⟩, hc⟩
    · intro c ⟨⟨_, hcount⟩, hc⟩
      exact ⟨hc, hcount⟩
  exact hprefix.seq (renamedTernaryLoop_state_spec φ hφ hindex hcount Rep
    (fun a ds => (hindep a ds).mono (fun r hr => List.mem_append_left _ hr))
    hrep hupd F a hS hbody)

end STACS2027.Runtimes.BoundedCost
