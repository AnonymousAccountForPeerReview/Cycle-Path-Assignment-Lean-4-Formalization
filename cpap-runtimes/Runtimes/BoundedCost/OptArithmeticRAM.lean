module

public import Runtimes.BoundedCost.CallerRegisters
public import Outerplanar.RAM.BoundedLib
public import Runtimes.BoundedCost.OptPowerRAM
import Mathlib.Tactic

/-! # Register arithmetic with finite verified value tables -/

@[expose] public section

namespace STACS2027.Runtimes.BoundedCost.OptSpanRAM

open STACS2027.RAM

def Known (values : List (Nat×Nat)) (c : Config) : Prop :=
  ∀ v,v∈values → c.reg v.1=v.2

theorem Known.cons {values : List (Nat×Nat)} {c : Config} {r v : Nat}
    (h : Known values c) (hv : c.reg r=v) : Known ((r,v)::values) c := by
  intro rv hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hv
  · exact h rv hm

theorem known_indep (values : List (Nat×Nat)) (W : List Nat)
    (h : ∀ v,v∈values → v.1∉W) : Indep W (Known values) := by
  intro c d hd hc v hv
  rw [hd.reg v.1 (h v hv)]
  exact hc v hv

theorem const_known {S r v : Nat} {values : List (Nat×Nat)}
    (h : ∀ rv,rv∈values → rv.1≠r) :
    HTB S (.const r v) (Known values) (Known ((r,v)::values)) 1 := by
  exact (HTB.const (known_indep _ _ (by simpa using h))).post
    (fun _ hc=>Known.cons hc.1 hc.2)

theorem add_known {S r a b x y : Nat} {values : List (Nat×Nat)}
    (h : ∀ rv,rv∈values → rv.1≠r)
    (ha : (a,x)∈values) (hb : (b,y)∈values) :
    HTB S (.add r a b) (Known values) (Known ((r,x+y)::values)) 1 := by
  exact (HTB.add (known_indep _ _ (by simpa using h))
    (fun _ hc=>hc _ ha) (fun _ hc=>hc _ hb)).post
    (fun _ hc=>Known.cons hc.1 hc.2)

theorem addc_known {S r a x n : Nat} {values : List (Nat×Nat)}
    (_hr : r≠rT) (ha' : a≠rT)
    (h : ∀ rv,rv∈values → rv.1≠r ∧ rv.1≠rT)
    (ha : (a,x)∈values) :
    HTB S (addc r a n) (Known values) (Known ((r,x+n)::values)) 2 := by
  exact (HTB.addc ha' (known_indep _ _ (by simpa [and_comm] using h))
    (fun _ hc=>hc _ ha)).post (fun _ hc=>Known.cons hc.1 hc.2)

theorem mul_known {S r a b count x y : Nat} {values : List (Nat×Nat)}
    (hreg : r≠count ∧ r≠rT ∧ count≠rT ∧ a≠r ∧ a≠count ∧ a≠rT ∧
      b≠r ∧ b≠count ∧ b≠rT)
    (h : ∀ rv,rv∈values → rv.1≠r ∧ rv.1≠count ∧ rv.1≠rT)
    (ha : (a,x)∈values) (hb : (b,y)∈values) :
    HTB S (RAM.mul r a b count) (Known values)
      (Known ((r,x*y)::values)) (5*y+4) := by
  exact (HTB.mul hreg (known_indep _ _ (by simpa using h))
    (fun _ hc=>hc _ ha) (fun _ hc=>hc _ hb)).post
    (fun _ hc=>Known.cons hc.1 hc.2)

theorem pow_known {S p : Nat} {values : List (Nat×Nat)}
    (h : ∀ rv,rv∈values → rv.1≠663 ∧ rv.1≠671 ∧ rv.1≠672 ∧ rv.1≠rT)
    (hp : (622,p)∈values) :
    HTB S OptPowerRAM.program (Known values) (Known ((663,15^p)::values))
      (100*(p+1)) := by
  intro c hc
  obtain ⟨d,t,he,hd,ht⟩ := OptPowerRAM.program_spec (S:=S) c (hc _ hp) c rfl
  refine ⟨d,t,he,Known.cons ?_ hd.1,ht⟩
  intro rv hv
  rw [OptPowerRAM.program_registerFrame he (h rv hv)]
  exact hc rv hv

end STACS2027.Runtimes.BoundedCost.OptSpanRAM
