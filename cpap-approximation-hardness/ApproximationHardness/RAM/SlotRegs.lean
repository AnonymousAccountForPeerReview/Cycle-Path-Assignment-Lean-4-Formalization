module

public import ApproximationHardness.RAM.PassV
import Lean.Elab.Tactic.Omega

/-! Disequalities between the slot registers and the named registers (generated). -/

@[expose] public section

namespace STACS2027.RAM

@[simp] theorem eReg_ne_p (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.p := by
  unfold eReg; simp only [Reg.p]; split <;> omega
@[simp] theorem p_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.p ≠ eReg i b := (eReg_ne_p i b hi).symm
@[simp] theorem bReg_ne_p (i : Nat) (hi : i < 3) : bReg i ≠ Reg.p := by
  unfold bReg; simp only [Reg.p]; omega
@[simp] theorem p_ne_bReg (i : Nat) (hi : i < 3) : Reg.p ≠ bReg i := (bReg_ne_p i hi).symm
@[simp] theorem eReg_ne_m (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.m := by
  unfold eReg; simp only [Reg.m]; split <;> omega
@[simp] theorem m_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.m ≠ eReg i b := (eReg_ne_m i b hi).symm
@[simp] theorem bReg_ne_m (i : Nat) (hi : i < 3) : bReg i ≠ Reg.m := by
  unfold bReg; simp only [Reg.m]; omega
@[simp] theorem m_ne_bReg (i : Nat) (hi : i < 3) : Reg.m ≠ bReg i := (bReg_ne_m i hi).symm
@[simp] theorem eReg_ne_len (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.len := by
  unfold eReg; simp only [Reg.len]; split <;> omega
@[simp] theorem len_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.len ≠ eReg i b := (eReg_ne_len i b hi).symm
@[simp] theorem bReg_ne_len (i : Nat) (hi : i < 3) : bReg i ≠ Reg.len := by
  unfold bReg; simp only [Reg.len]; omega
@[simp] theorem len_ne_bReg (i : Nat) (hi : i < 3) : Reg.len ≠ bReg i := (bReg_ne_len i hi).symm
@[simp] theorem eReg_ne_v (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.v := by
  unfold eReg; simp only [Reg.v]; split <;> omega
@[simp] theorem v_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.v ≠ eReg i b := (eReg_ne_v i b hi).symm
@[simp] theorem bReg_ne_v (i : Nat) (hi : i < 3) : bReg i ≠ Reg.v := by
  unfold bReg; simp only [Reg.v]; omega
@[simp] theorem v_ne_bReg (i : Nat) (hi : i < 3) : Reg.v ≠ bReg i := (bReg_ne_v i hi).symm
@[simp] theorem eReg_ne_sg (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.sg := by
  unfold eReg; simp only [Reg.sg]; split <;> omega
@[simp] theorem sg_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.sg ≠ eReg i b := (eReg_ne_sg i b hi).symm
@[simp] theorem bReg_ne_sg (i : Nat) (hi : i < 3) : bReg i ≠ Reg.sg := by
  unfold bReg; simp only [Reg.sg]; omega
@[simp] theorem sg_ne_bReg (i : Nat) (hi : i < 3) : Reg.sg ≠ bReg i := (bReg_ne_sg i hi).symm
@[simp] theorem eReg_ne_n (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.n := by
  unfold eReg; simp only [Reg.n]; split <;> omega
@[simp] theorem n_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.n ≠ eReg i b := (eReg_ne_n i b hi).symm
@[simp] theorem bReg_ne_n (i : Nat) (hi : i < 3) : bReg i ≠ Reg.n := by
  unfold bReg; simp only [Reg.n]; omega
@[simp] theorem n_ne_bReg (i : Nat) (hi : i < 3) : Reg.n ≠ bReg i := (bReg_ne_n i hi).symm
@[simp] theorem eReg_ne_t (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.t := by
  unfold eReg; simp only [Reg.t]; split <;> omega
@[simp] theorem t_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.t ≠ eReg i b := (eReg_ne_t i b hi).symm
@[simp] theorem bReg_ne_t (i : Nat) (hi : i < 3) : bReg i ≠ Reg.t := by
  unfold bReg; simp only [Reg.t]; omega
@[simp] theorem t_ne_bReg (i : Nat) (hi : i < 3) : Reg.t ≠ bReg i := (bReg_ne_t i hi).symm
@[simp] theorem eReg_ne_one (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.one := by
  unfold eReg; simp only [Reg.one]; split <;> omega
@[simp] theorem one_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.one ≠ eReg i b := (eReg_ne_one i b hi).symm
@[simp] theorem bReg_ne_one (i : Nat) (hi : i < 3) : bReg i ≠ Reg.one := by
  unfold bReg; simp only [Reg.one]; omega
@[simp] theorem one_ne_bReg (i : Nat) (hi : i < 3) : Reg.one ≠ bReg i := (bReg_ne_one i hi).symm
@[simp] theorem eReg_ne_N (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.N := by
  unfold eReg; simp only [Reg.N]; split <;> omega
@[simp] theorem N_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.N ≠ eReg i b := (eReg_ne_N i b hi).symm
@[simp] theorem bReg_ne_N (i : Nat) (hi : i < 3) : bReg i ≠ Reg.N := by
  unfold bReg; simp only [Reg.N]; omega
@[simp] theorem N_ne_bReg (i : Nat) (hi : i < 3) : Reg.N ≠ bReg i := (bReg_ne_N i hi).symm
@[simp] theorem eReg_ne_B (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.B := by
  unfold eReg; simp only [Reg.B]; split <;> omega
@[simp] theorem B_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.B ≠ eReg i b := (eReg_ne_B i b hi).symm
@[simp] theorem bReg_ne_B (i : Nat) (hi : i < 3) : bReg i ≠ Reg.B := by
  unfold bReg; simp only [Reg.B]; omega
@[simp] theorem B_ne_bReg (i : Nat) (hi : i < 3) : Reg.B ≠ bReg i := (bReg_ne_B i hi).symm
@[simp] theorem eReg_ne_vb (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.vb := by
  unfold eReg; simp only [Reg.vb]; split <;> omega
@[simp] theorem vb_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.vb ≠ eReg i b := (eReg_ne_vb i b hi).symm
@[simp] theorem bReg_ne_vb (i : Nat) (hi : i < 3) : bReg i ≠ Reg.vb := by
  unfold bReg; simp only [Reg.vb]; omega
@[simp] theorem vb_ne_bReg (i : Nat) (hi : i < 3) : Reg.vb ≠ bReg i := (bReg_ne_vb i hi).symm
@[simp] theorem eReg_ne_cv (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.cv := by
  unfold eReg; simp only [Reg.cv]; split <;> omega
@[simp] theorem cv_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.cv ≠ eReg i b := (eReg_ne_cv i b hi).symm
@[simp] theorem bReg_ne_cv (i : Nat) (hi : i < 3) : bReg i ≠ Reg.cv := by
  unfold bReg; simp only [Reg.cv]; omega
@[simp] theorem cv_ne_bReg (i : Nat) (hi : i < 3) : Reg.cv ≠ bReg i := (bReg_ne_cv i hi).symm
@[simp] theorem eReg_ne_vi (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.vi := by
  unfold eReg; simp only [Reg.vi]; split <;> omega
@[simp] theorem vi_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.vi ≠ eReg i b := (eReg_ne_vi i b hi).symm
@[simp] theorem bReg_ne_vi (i : Nat) (hi : i < 3) : bReg i ≠ Reg.vi := by
  unfold bReg; simp only [Reg.vi]; omega
@[simp] theorem vi_ne_bReg (i : Nat) (hi : i < 3) : Reg.vi ≠ bReg i := (bReg_ne_vi i hi).symm
@[simp] theorem eReg_ne_W (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.W := by
  unfold eReg; simp only [Reg.W]; split <;> omega
@[simp] theorem W_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.W ≠ eReg i b := (eReg_ne_W i b hi).symm
@[simp] theorem bReg_ne_W (i : Nat) (hi : i < 3) : bReg i ≠ Reg.W := by
  unfold bReg; simp only [Reg.W]; omega
@[simp] theorem W_ne_bReg (i : Nat) (hi : i < 3) : Reg.W ≠ bReg i := (bReg_ne_W i hi).symm
@[simp] theorem eReg_ne_cb (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.cb := by
  unfold eReg; simp only [Reg.cb]; split <;> omega
@[simp] theorem cb_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.cb ≠ eReg i b := (eReg_ne_cb i b hi).symm
@[simp] theorem bReg_ne_cb (i : Nat) (hi : i < 3) : bReg i ≠ Reg.cb := by
  unfold bReg; simp only [Reg.cb]; omega
@[simp] theorem cb_ne_bReg (i : Nat) (hi : i < 3) : Reg.cb ≠ bReg i := (bReg_ne_cb i hi).symm
@[simp] theorem eReg_ne_addr (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.addr := by
  unfold eReg; simp only [Reg.addr]; split <;> omega
@[simp] theorem addr_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.addr ≠ eReg i b := (eReg_ne_addr i b hi).symm
@[simp] theorem bReg_ne_addr (i : Nat) (hi : i < 3) : bReg i ≠ Reg.addr := by
  unfold bReg; simp only [Reg.addr]; omega
@[simp] theorem addr_ne_bReg (i : Nat) (hi : i < 3) : Reg.addr ≠ bReg i := (bReg_ne_addr i hi).symm
@[simp] theorem eReg_ne_cc (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.cc := by
  unfold eReg; simp only [Reg.cc]; split <;> omega
@[simp] theorem cc_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.cc ≠ eReg i b := (eReg_ne_cc i b hi).symm
@[simp] theorem bReg_ne_cc (i : Nat) (hi : i < 3) : bReg i ≠ Reg.cc := by
  unfold bReg; simp only [Reg.cc]; omega
@[simp] theorem cc_ne_bReg (i : Nat) (hi : i < 3) : Reg.cc ≠ bReg i := (bReg_ne_cc i hi).symm
@[simp] theorem eReg_ne_x (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.x := by
  unfold eReg; simp only [Reg.x]; split <;> omega
@[simp] theorem x_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.x ≠ eReg i b := (eReg_ne_x i b hi).symm
@[simp] theorem bReg_ne_x (i : Nat) (hi : i < 3) : bReg i ≠ Reg.x := by
  unfold bReg; simp only [Reg.x]; omega
@[simp] theorem x_ne_bReg (i : Nat) (hi : i < 3) : Reg.x ≠ bReg i := (bReg_ne_x i hi).symm
@[simp] theorem eReg_ne_zero (i : Nat) (b : Bool) (hi : i < 3) : eReg i b ≠ Reg.zero := by
  unfold eReg; simp only [Reg.zero]; split <;> omega
@[simp] theorem zero_ne_eReg (i : Nat) (b : Bool) (hi : i < 3) : Reg.zero ≠ eReg i b := (eReg_ne_zero i b hi).symm
@[simp] theorem bReg_ne_zero (i : Nat) (hi : i < 3) : bReg i ≠ Reg.zero := by
  unfold bReg; simp only [Reg.zero]; omega
@[simp] theorem zero_ne_bReg (i : Nat) (hi : i < 3) : Reg.zero ≠ bReg i := (bReg_ne_zero i hi).symm

theorem bReg_ne_eReg (i i' : Nat) (b : Bool) (hi : i < 3) : bReg i ≠ eReg i' b := by
  unfold bReg eReg; split <;> omega
theorem eReg_ne_bReg (i i' : Nat) (b : Bool) (hi : i < 3) : eReg i' b ≠ bReg i := (bReg_ne_eReg i i' b hi).symm
theorem eReg_inj {i i' : Nat} {b b' : Bool} (h : eReg i b = eReg i' b') : i = i' ∧ b = b' := by
  unfold eReg at h
  cases b <;> cases b' <;> simp at h <;> first | exact ⟨by omega, rfl⟩ | omega
theorem eReg_side (i : Nat) : eReg i false ≠ eReg i true := by unfold eReg; simp
theorem bReg_inj {i i' : Nat} (h : bReg i = bReg i') : i = i' := by unfold bReg at h; omega

end STACS2027.RAM
