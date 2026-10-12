module

public import NPHardness.PlanarAssemblyLocalOrder
public import NPHardness.PlanarOperationsPortsSubdivision

/-!
Plain subdivisions preserve exact first-hit port order. The old face walk
is expanded by inserting darts, and each inserted dart is proved distinct
from every old dart. This transports the absence of intervening ports, not
merely the existence of a common face orbit.
-/

@[expose] public section
namespace STACS2027.PlanarAssembly
open Complexity Complexity.Planar PlanarGluing

/-- Lift a face segment that avoids all selected ports before its endpoint
through a subdivision whose inserted intermediate darts are all new. -/
theorem lift_avoiding_walk {α β : Type} {m : Nat} (f : α→α) (g : β→β)
    (emb : α→β) (hinj : ∀a b,emb a=emb b→a=b) (port : Fin m→α)
    (hstep : ∀x,∃s,0<s ∧ iterate g s (emb x)=emb (f x) ∧
      ∀r,0<r→r<s→∀y,iterate g r (emb x)≠emb y)
    (k : Nat) (x : α) (havoid : ∀r,r<k→∀i,iterate f r x≠port i) :
    ∃t,k≤t ∧ iterate g t (emb x)=emb (iterate f k x) ∧
      ∀r,r<t→∀i,iterate g r (emb x)≠emb (port i) := by
  induction k generalizing x with
  | zero => exact ⟨0,Nat.le_refl _,rfl,by intro r hr; omega⟩
  | succ k ih =>
    obtain ⟨s,hs,hend,hinside⟩ := hstep x
    obtain ⟨t,ht,htend,htinside⟩ := ih (f x) (fun r hr i=>havoid (r+1) (by omega) i)
    refine ⟨s+t,by omega,?_,?_⟩
    · rw [iterate_add,hend,htend]
      rfl
    · intro r hr i he
      by_cases hrs:r<s
      · by_cases hr0:r=0
        · subst r
          exact havoid 0 (by omega) i (hinj _ _ he)
        · exact hinside r (by omega) hrs (port i) he
      · have hre : r=s+(r-s) := by omega
        rw [hre,iterate_add,hend] at he
        exact htinside (r-s) (by omega) i he

/-- Exact first-hit order is preserved when each old face step is expanded
without introducing any old dart strictly between its endpoints. -/
theorem NextSelected.lift {n r m : Nat} {f : Fin n→Fin n} {g : Fin r→Fin r}
    (emb : Fin n→Fin r) (hinj : ∀a b,emb a=emb b→a=b) {port : Fin m→Fin n}
    (hstep : ∀x,∃s,0<s ∧ iterate g s (emb x)=emb (f x) ∧
      ∀r,0<r→r<s→∀y,iterate g r (emb x)≠emb y)
    {i j : Fin m} (h : NextSelected f port i j) :
    NextSelected g (fun i=>emb (port i)) i j := by
  obtain ⟨k,hk,hend,hinside⟩ := h
  obtain ⟨s,hs,hstart,hnew⟩ := hstep (port i)
  obtain ⟨t,ht,htend,htinside⟩ := lift_avoiding_walk f g emb hinj port hstep
    (k-1) (f (port i)) (by
      intro r hr a
      exact hinside (r+1) (by omega) (by omega) a)
  refine ⟨s+t,by omega,?_,?_⟩
  · rw [iterate_add,hstart,htend]
    have he : k=(k-1)+1 := by omega
    rw [he] at hend
    exact congrArg emb hend
  · intro r hr hrs a he
    by_cases hsmall:r<s
    · exact hnew r hr hsmall (port a) he
    · have hre:r=s+(r-s) := by omega
      rw [hre,iterate_add,hstart] at he
      exact htinside (r-s) (by omega) a he

end STACS2027.PlanarAssembly

namespace STACS2027.PlanarOperations.Subdivision
open Complexity Complexity.Planar PlanarAssembly
open Complexity.Planar.Subdiv (gF)
variable {E0 E1 A T : Nat} (G : Hypermap (2*E0))
  (hn:2*E0=A+2*T) (hN:2*E1=A+4*T) (hA:A%2=0)
  (hedge:∀d,(G.edge d).val=ed d.val)

theorem iotaF_injective {a b : Fin (2*E0)}
    (h:iotaF hn hN a=iotaF hn hN b) : a=b := by
  have hv := congrArg Fin.val h
  have hs := congrArg (sig A) hv
  simp only [iotaF,sig_iota] at hs
  exact Fin.ext hs

include hedge

/-- Every expanded face step contains only new internal darts in its strict
interior. This is the additional fact needed for exact first-hit transport. -/
theorem face_step_new_interior (y : Fin (2*E0)) :
    ∃s,0<s ∧ iterate (G' G hn hN hA).face s (iotaF hn hN y)=iotaF hn hN (G.face y) ∧
      ∀r,0<r→r<s→∀z,iterate (G' G hn hN hA).face r (iotaF hn hN y)≠iotaF hn hN z := by
  have hy:=y.isLt
  have hf:(G.face y).val=gF G y.val := by unfold gF;rw [dite_eq_left hy]
  have hiv:∀x:Fin (2*E0),(iotaF hn hN x).val=iota A x.val := fun _=>rfl
  rcases Nat.lt_or_ge y.val A with hlt|hge
  · refine ⟨1,by decide,Fin.ext ?_,by intro r hr hrs;omega⟩
    rw [iterate_face_val,hiv,hiv,hf]
    change fc G A (iota A y.val)=_
    rw [show iota A y.val=y.val by unfold iota;rw [ite_eq_left hlt],fc_low G hn hA hedge hlt]
  · obtain ⟨u,s,hys,hu,hs⟩:∃u s,y.val=A+2*u+s ∧ u<T ∧ s<2 :=
      ⟨(y.val-A)/2,(y.val-A)%2,by omega,by omega,by omega⟩
    refine ⟨2,by decide,Fin.ext ?_,?_⟩
    · rw [iterate_face_val,hiv,hiv,hf,hys,iota_r u s hs]
      change fc G A (fc G A (A+4*u+2*s))=iota A (gF G (A+2*u+s))
      rcases Nat.lt_or_ge s 1 with hs0|hs1
      · have he:s=0:=by omega
        subst s
        simp only [Nat.mul_zero,Nat.add_zero]
        rw [fc_r0 G hn hA,fc_r3 G hn hA hedge hu]
      · have he:s=1:=by omega
        subst s
        simp only [Nat.mul_one]
        rw [fc_r2 G hn hA,fc_r1 G hn hA hedge hu]
    · intro r hr hrs z he
      have hr1:r=1:=by omega
      subst r
      have hv:=congrArg Fin.val he
      rw [iterate_face_val,hiv,hiv] at hv
      change fc G A (iota A y.val)=iota A z.val at hv
      rw [hys,iota_r u s hs] at hv
      have hz:=isOld_iota A z.val
      rw [←hv] at hz
      rcases Nat.lt_or_ge s 1 with hs0|hs1
      · have he:s=0:=by omega
        subst s
        simp only [Nat.mul_zero,Nat.add_zero] at hz
        rw [fc_r0 G hn hA] at hz
        rcases hz with hz|hz|hz <;> omega
      · have he:s=1:=by omega
        subst s
        simp only [Nat.mul_one] at hz
        rw [fc_r2 G hn hA] at hz
        rcases hz with hz|hz|hz <;> omega

/-- Original first-hit port order is preserved by the actual splitMap. -/
theorem nextSelected_subdivide {m : Nat} {port : Fin m→Fin (2*E0)} {i j : Fin m}
    (h:NextSelected G.face port i j) :
    NextSelected (G' G hn hN hA).face (fun a=>iotaF hn hN (port a)) i j :=
  h.lift (iotaF hn hN) (fun _ _ he=>iotaF_injective hn hN he)
    (face_step_new_interior G hn hN hA hedge)

end STACS2027.PlanarOperations.Subdivision
