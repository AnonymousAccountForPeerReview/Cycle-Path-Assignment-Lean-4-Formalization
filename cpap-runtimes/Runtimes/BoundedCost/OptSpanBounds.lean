module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Pure bounds for the optimization wrapper's computed memory span. -/

@[expose] public section
namespace STACS2027.Runtimes.BoundedCost.OptSpanRAM

/-- The formula-size polynomial used by the cited bounded-cost search. -/
def z (k t p : Nat) : Nat := (p+1)*k*k*t+k*t*t

/-- The unscaled work bound, including the supplied cycle incidence input. -/
def Q (k t p : Nat) : Nat := 15^p*p*(z k t p)^3+k*k*t+k*t*t+k*t+1

/-- The computed span used for every optimization call. -/
def span (C k t p : Nat) : Nat := 8*(C+1)*Q k t p

theorem Q_positive (k t p : Nat) : 0<Q k t p := by unfold Q;omega

theorem span_positive (C k t p : Nat) : 0<span C k t p := by
  unfold span
  exact Nat.mul_pos (by omega) (Q_positive k t p)

theorem Q_le_span (C k t p : Nat) : Q k t p≤span C k t p := by
  exact Nat.le_mul_of_pos_left _ (by omega : 0<8*(C+1))

theorem span_scale_lower (C k t p : Nat) : 8*Q k t p≤span C k t p := by
  exact Nat.mul_le_mul_right (Q k t p) (by omega : 8≤8*(C+1))

/-- The base branch needs only factors already bounded by the nonexponential terms. -/
theorem base_components_le {k t : Nat} (hk : 0<k) (ht : 0<t) (p : Nat) :
    k≤Q k t p ∧ t≤Q k t p ∧ k*k≤Q k t p ∧ k*t≤Q k t p ∧
      k*k*t≤Q k t p ∧ k*t*t≤Q k t p ∧
      k*k*t+k*t*t+k*t+1≤Q k t p := by
  have hktk : k≤k*t := Nat.le_mul_of_pos_right _ ht
  have hktt : t≤k*t := Nat.le_mul_of_pos_left _ hk
  have hkk : k*k≤k*k*t := Nat.le_mul_of_pos_right _ ht
  unfold Q
  omega

theorem z_positive {k t : Nat} (hk : 0<k) (ht : 0<t) (p : Nat) : 0<z k t p := by
  have h : 0<(p+1)*k*k*t := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) hk) hk) ht
  unfold z;omega

/-- Every positive-exponent arithmetic operand is bounded by the unscaled work bound. -/
theorem positive_components_le {k t p : Nat} (hk : 0<k) (ht : 0<t) (hp : 0<p) :
    k≤Q k t p ∧ t≤Q k t p ∧ z k t p≤Q k t p ∧ (z k t p)^3≤Q k t p ∧
      p*(z k t p)^3≤Q k t p ∧ p≤Q k t p ∧ 15^p≤Q k t p ∧ p+1≤Q k t p := by
  have hz := z_positive hk ht p
  have hpow : 1≤15^p := one_le_pow_of_one_le' (by decide : 1≤(15:Nat)) p
  have hcube : 0<(z k t p)^3 := Nat.pow_pos hz
  have hzc : z k t p≤(z k t p)^3 := le_self_pow (by omega) (by decide : (3:Nat)≠0)
  have hcp : (z k t p)^3≤p*(z k t p)^3 := Nat.le_mul_of_pos_left _ hp
  have hcf : p*(z k t p)^3≤15^p*p*(z k t p)^3 := by
    calc p*(z k t p)^3≤15^p*(p*(z k t p)^3) := Nat.le_mul_of_pos_left _ (by omega)
         _=15^p*p*(z k t p)^3 := by rw [Nat.mul_assoc]
  have hpp : p≤p*(z k t p)^3 := Nat.le_mul_of_pos_right _ hcube
  have hpf : 15^p≤15^p*p*(z k t p)^3 := by
    exact (Nat.le_mul_of_pos_right _ hp).trans (Nat.le_mul_of_pos_right _ hcube)
  have hb := base_components_le hk ht p
  have hf : 15^p*p*(z k t p)^3+1≤Q k t p := by unfold Q;omega
  exact ⟨hb.1,hb.2.1,by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- Zero exponent suppresses the exponential branch entirely. -/
theorem Q_zero_exponent (k t : Nat) : Q k t 0=k*k*t+k*t*t+k*t+1 := by simp [Q]

/-- Zero cycles require a constant span, independently of the cycle length. -/
theorem span_zero_cycles (C k p : Nat) : span C k 0 p=8*(C+1) := by simp [span,Q,z]

/-- The formula-size polynomial grows with the permitted cost. -/
theorem z_mono {k t p q : Nat} (hpq : p≤q) : z k t p≤z k t q := by
  unfold z
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right t (Nat.mul_le_mul_right k (Nat.mul_le_mul_right k (by omega)))) _

/-- The computed work bound grows with the permitted cost. -/
theorem Q_mono {k t p q : Nat} (hpq : p≤q) : Q k t p≤Q k t q := by
  have hpow : 15^p≤15^q := pow_le_pow_right' (by decide : 1≤(15:Nat)) hpq
  have hcube := pow_le_pow_left' (z_mono (k:=k) (t:=t) hpq) 3
  have hf := Nat.mul_le_mul (Nat.mul_le_mul hpow hpq) hcube
  unfold Q
  omega

theorem span_mono {C k t p q : Nat} (hpq : p≤q) : span C k t p≤span C k t q :=
  Nat.mul_le_mul_left _ (Q_mono hpq)

/-- Input-header construction fits inside the computed memory span. -/
theorem header_le_span (C k t p : Nat) : 3*k*t+5≤span C k t p := by
  have hbase : k*t+1≤Q k t p := by unfold Q;omega
  have hscale := span_scale_lower C k t p
  rw [Nat.mul_assoc]
  omega

/-- The finite arithmetic macros fit within a constant multiple of the computed span. -/
theorem arithmetic_cost_bound {C k t p : Nat} (hk : 0<k) (ht : 0<t) (hp : 0<p) :
    60*(k+t+z k t p+(z k t p)^3+p*(z k t p)^3+p+Q k t p+1)≤
      500*(span C k t p+1) := by
  obtain ⟨hk',ht',hz,hc,hpc,hp',_,_⟩ := positive_components_le hk ht hp
  have hspan := Q_le_span C k t p
  omega

end STACS2027.Runtimes.BoundedCost.OptSpanRAM
