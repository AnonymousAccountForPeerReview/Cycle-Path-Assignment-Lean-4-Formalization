module

public import ApproximationHardness.Embed.DefaultRotationRAM
import Lean.Elab.Tactic.Omega

/-! # Exact local cache-reader interpretation -/

@[expose] public section

namespace STACS2027.Embed.RAMSolver

open RAM

theorem rotationRead_values (F : ForestData) (v : Nat) (c : Config)
    (hz : c.reg 0=0) (ho : c.reg 1=1) (hD : c.reg 140=2*F.E)
    (hv : c.mem (c.reg 160+c.reg 240)=v)
    (hp : c.mem (c.reg 166+v)=F.par v)
    (hd : c.mem (c.reg 162+v)=(F.dartsAt v).length)
    (hn : c.mem (c.reg 66+v)=(F.parts v).length)
    (hlt : c.mem (c.reg 67+v)=itemType ((F.parts v).getD 0 (.node 0)))
    (hlv : c.mem (c.reg 68+v)=itemValue ((F.parts v).getD 0 (.node 0)))
    (hrt : c.mem (c.reg 69+v)=itemType ((F.parts v).getD 1 (.node 0)))
    (hrv : c.mem (c.reg 70+v)=itemValue ((F.parts v).getD 1 (.node 0)))
    (hZ : c.mem (c.reg 280+v)=F.zOf v)
    (hlen : (F.parts v).length≤2)
    (hchild : ∀ w,Item.node w∈F.parts v →
      c.mem (c.reg 166+w)=F.par w ∧
      c.mem (c.reg 161+F.par w)=STACS2027.Embed.pair (F.par w)) :
    (run rotationRead c).reg 242=v ∧
    (run rotationRead c).reg 244=(F.dartsAt v).length ∧
    (run rotationRead c).reg 258=(cycleSlots F v).1 ∧
    (run rotationRead c).reg 259=(cycleSlots F v).2.1 ∧
    (run rotationRead c).reg 260=(cycleSlots F v).2.2 ∧
    (run rotationRead c).reg 265=2 := by
  have hroot : (2*F.E-F.par v=0) ↔ F.IsRoot v := by
    simp [ForestData.IsRoot,Nat.sub_eq_zero_iff_le]
  cases he : F.parts v with
  | nil =>
    simp [rotationRead,readBothParts,seqs,run,cycleSlots,hz,hD,hv,hp,hd,hn,
      hZ,he,hroot]; split_ifs <;> simp
  | cons a as =>
    cases as with
    | nil =>
      cases a with
      | node w =>
        rcases hchild w (by simp [he]) with ⟨hw,hq⟩
        simp [rotationRead,readBothParts,readLeftPart,decodePart,seqs,run,cycleSlots,
          ForestData.itemDart,itemType,itemValue,hz,ho,hD,hv,hp,hd,hn,hlt,hlv,
          hZ,he,hroot,hw,hq]; split_ifs <;> simp
      | dart e =>
        simp [rotationRead,readBothParts,readLeftPart,decodePart,seqs,run,cycleSlots,
          ForestData.itemDart,itemType,itemValue,hz,ho,hD,hv,hp,hd,hn,hlt,hlv,
          hZ,he,hroot]; split_ifs <;> simp
    | cons b bs =>
      have hbs : bs=[] := by simp only [he,List.length_cons] at hlen; exact List.eq_nil_of_length_eq_zero (by omega)
      subst bs
      cases a with
      | node w =>
        rcases hchild w (by simp [he]) with ⟨hw,hq⟩
        cases b with
        | node x =>
          rcases hchild x (by simp [he]) with ⟨hx,hqx⟩
          simp [rotationRead,readBothParts,readLeftPart,readRightPart,decodePart,seqs,run,
            cycleSlots,ForestData.itemDart,itemType,itemValue,hz,ho,hD,hv,hp,hd,hn,
            hlt,hlv,hrt,hrv,hZ,he,hroot,hw,hq,hx,hqx]; split_ifs <;> simp
        | dart e =>
          simp [rotationRead,readBothParts,readLeftPart,readRightPart,decodePart,seqs,run,
            cycleSlots,ForestData.itemDart,itemType,itemValue,hz,ho,hD,hv,hp,hd,hn,
            hlt,hlv,hrt,hrv,hZ,he,hroot,hw,hq]; split_ifs <;> simp
      | dart e =>
        cases b with
        | node x =>
          rcases hchild x (by simp [he]) with ⟨hx,hqx⟩
          simp [rotationRead,readBothParts,readLeftPart,readRightPart,decodePart,seqs,run,
            cycleSlots,ForestData.itemDart,itemType,itemValue,hz,ho,hD,hv,hp,hd,hn,
            hlt,hlv,hrt,hrv,hZ,he,hroot,hx,hqx]; split_ifs <;> simp
        | dart e' =>
          simp [rotationRead,readBothParts,readLeftPart,readRightPart,decodePart,seqs,run,
            cycleSlots,ForestData.itemDart,itemType,itemValue,hz,ho,hD,hv,hp,hd,hn,
            hlt,hlv,hrt,hrv,hZ,he,hroot]; split_ifs <;> simp


/-- Every indirect read uses a represented table or a represented child dart. -/
theorem rotationRead_addrOK (F : ForestData) (v S : Nat) (c : Config)
    (hz : c.reg 0=0) (ho : c.reg 1=1)
    (hv : c.mem (c.reg 160+c.reg 240)=v)
    (hp : c.mem (c.reg 166+v)=F.par v)
    (hn : c.mem (c.reg 66+v)=(F.parts v).length)
    (hlt : c.mem (c.reg 67+v)=itemType ((F.parts v).getD 0 (.node 0)))
    (hlv : c.mem (c.reg 68+v)=itemValue ((F.parts v).getD 0 (.node 0)))
    (hrt : c.mem (c.reg 69+v)=itemType ((F.parts v).getD 1 (.node 0)))
    (hrv : c.mem (c.reg 70+v)=itemValue ((F.parts v).getD 1 (.node 0)))
    (hlen : (F.parts v).length≤2)
    (hrep : c.reg 160+c.reg 240<S)
    (hpar : c.reg 166+v<S) (hdeg : c.reg 162+v<S) (hcount : c.reg 66+v<S)
    (hleftType : c.reg 67+v<S) (hleftValue : c.reg 68+v<S)
    (hrightType : c.reg 69+v<S) (hrightValue : c.reg 70+v<S)
    (hZ : c.reg 280+v<S)
    (hchild : ∀ w,Item.node w∈F.parts v →
      c.mem (c.reg 166+w)=F.par w ∧
      c.reg 166+w<S ∧ c.reg 161+F.par w<S) :
    AddrOK S rotationRead c := by
  cases he : F.parts v with
  | nil =>
    simp [rotationRead,readBothParts,seqs,run,AddrOK,hz,hv,hp,hn,he,hrep,hpar,hdeg,hcount,hZ]
  | cons a as =>
    cases as with
    | nil =>
      cases a with
      | node w =>
        rcases hchild w (by simp [he]) with ⟨hw,hwa,hqa⟩
        simp [rotationRead,readBothParts,readLeftPart,decodePart,seqs,run,AddrOK,
          itemType,itemValue,hz,ho,hv,hp,hn,hlt,hlv,he,hrep,hpar,hdeg,hcount,
          hleftType,hleftValue,hZ,hw,hwa,hqa]
      | dart e =>
        simp [rotationRead,readBothParts,readLeftPart,decodePart,seqs,run,AddrOK,
          itemType,itemValue,hz,ho,hv,hp,hn,hlt,hlv,he,hrep,hpar,hdeg,hcount,
          hleftType,hleftValue,hZ]
    | cons b bs =>
      have hbs : bs=[] := by simp only [he,List.length_cons] at hlen; exact List.eq_nil_of_length_eq_zero (by omega)
      subst bs
      cases a with
      | node w =>
        rcases hchild w (by simp [he]) with ⟨hw,hwa,hqa⟩
        cases b with
        | node x =>
          rcases hchild x (by simp [he]) with ⟨hx,hxa,hqx⟩
          simp [rotationRead,readBothParts,readLeftPart,readRightPart,decodePart,seqs,run,AddrOK,
            itemType,itemValue,hz,ho,hv,hp,hn,hlt,hlv,hrt,hrv,he,hrep,hpar,hdeg,hcount,
            hleftType,hleftValue,hrightType,hrightValue,hZ,hw,hwa,hqa,hx,hxa,hqx]
        | dart e =>
          simp [rotationRead,readBothParts,readLeftPart,readRightPart,decodePart,seqs,run,AddrOK,
            itemType,itemValue,hz,ho,hv,hp,hn,hlt,hlv,hrt,hrv,he,hrep,hpar,hdeg,hcount,
            hleftType,hleftValue,hrightType,hrightValue,hZ,hw,hwa,hqa]
      | dart e =>
        cases b with
        | node x =>
          rcases hchild x (by simp [he]) with ⟨hx,hxa,hqx⟩
          simp [rotationRead,readBothParts,readLeftPart,readRightPart,decodePart,seqs,run,AddrOK,
            itemType,itemValue,hz,ho,hv,hp,hn,hlt,hlv,hrt,hrv,he,hrep,hpar,hdeg,hcount,
            hleftType,hleftValue,hrightType,hrightValue,hZ,hx,hxa,hqx]
        | dart e' =>
          simp [rotationRead,readBothParts,readLeftPart,readRightPart,decodePart,seqs,run,AddrOK,
            itemType,itemValue,hz,ho,hv,hp,hn,hlt,hlv,hrt,hrv,he,hrep,hpar,hdeg,hcount,
            hleftType,hleftValue,hrightType,hrightValue,hZ]

end STACS2027.Embed.RAMSolver
