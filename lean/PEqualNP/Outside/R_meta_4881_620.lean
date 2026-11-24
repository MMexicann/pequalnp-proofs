import PEqualNP.Defs

-- Work backwards from the first occurrence of the desired column.
-- Duplicate columns, zero and all-ones contribute nothing at positive minimum cost.
-- For a final OR, neither operand can contain a zero row; the final AND is dual.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_4881_620
    (clean : ∀ seed ws : List (BitVec 24),
      (∀ i : Fin ws.length, let old := seed ++ ws.take i.val
        ∃ a ∈ old, ∃ b ∈ old, ws.get i = a &&& b ∨ ws.get i = a ||| b) →
      ∃ ys : List (BitVec 24), ys.length ≤ ws.length ∧
        (∀ i : Fin ys.length, let old := seed ++ ys.take i.val
          ys.get i ∉ old ∧ ys.get i ≠ 0 ∧ ys.get i ≠ BitVec.allOnes 24 ∧
            ∃ a ∈ old, ∃ b ∈ old, ys.get i = a &&& b ∨ ys.get i = a ||| b) ∧
        ∀ v ∈ seed ++ ws, v = 0 ∨ v = BitVec.allOnes 24 ∨ v ∈ seed ++ ys)
    (orEnd : ∀ (ys : List (BitVec 24)), ys.length ≤ 12 →
      let seed : List (BitVec 24) :=
        [202052,276515,549652,1097833,101010,10616859,4456668,2624736,13635328,751444,12288]
      let target : BitVec 24 := 16773120
      (∀ i : Fin ys.length, let old := seed ++ ys.take i.val
        ys.get i ∉ old ∧ ys.get i ≠ 0 ∧ ys.get i ≠ BitVec.allOnes 24 ∧
          ∃ a ∈ old, ∃ b ∈ old, ys.get i = a &&& b ∨ ys.get i = a ||| b) →
      target ∉ seed ++ ys →
      ∀ a ∈ seed ++ ys, ∀ b ∈ seed ++ ys, a ≠ b →
        (a &&& target = a ∧ b &&& target = b) →
        target ≠ a ||| b)
    (andEnd : ∀ (ys : List (BitVec 24)), ys.length ≤ 12 →
      let seed : List (BitVec 24) :=
        [202052,276515,549652,1097833,101010,10616859,4456668,2624736,13635328,751444,12288]
      let target : BitVec 24 := 16773120
      (∀ i : Fin ys.length, let old := seed ++ ys.take i.val
        ys.get i ∉ old ∧ ys.get i ≠ 0 ∧ ys.get i ≠ BitVec.allOnes 24 ∧
          ∃ a ∈ old, ∃ b ∈ old, ys.get i = a &&& b ∨ ys.get i = a ||| b) →
      target ∉ seed ++ ys →
      ∀ a ∈ seed ++ ys, ∀ b ∈ seed ++ ys, a ≠ b →
        (a &&& target = target ∧ b &&& target = target) →
        target ≠ a &&& b) :
    ∀ x1 ∈ [(12288 : BitVec (24 : ℕ))],   ∀ (x3 : List (BitVec (24 : ℕ))),     have x4 : List (BitVec (24 : ℕ)) := [(202052 : BitVec (24 : ℕ)), (276515 : BitVec (24 : ℕ)), (549652 : BitVec (24 : ℕ)), (1097833 : BitVec (24 : ℕ)), (101010 : BitVec (24 : ℕ)), (10616859 : BitVec (24 : ℕ)), (4456668 : BitVec (24 : ℕ)), (2624736 : BitVec (24 : ℕ)), (13635328 : BitVec (24 : ℕ)), (751444 : BitVec (24 : ℕ))] ++ [x1];     (16773120 : BitVec (24 : ℕ)) ∈ x4 ++ x3 →       (∀ (x6 : Fin x3.length),           have x7 : List (BitVec (24 : ℕ)) := x4 ++ List.take (↑x6) x3;           ∃ x8 ∈ x7, ∃ x9 ∈ x7, x3.get x6 = x8 &&& x9 ∨ x3.get x6 = x8 ||| x9) →         (14 : ℕ) ≤ x3.length := by
  intro bonus hbonus xs
  have eqBonus : bonus = (12288 : BitVec 24) := by simpa only [List.mem_singleton] using hbonus
  subst bonus
  dsimp only
  intro present legal
  let seed : List (BitVec 24) :=
    [202052,276515,549652,1097833,101010,10616859,4456668,2624736,13635328,751444,12288]
  let target : BitVec 24 := 16773120
  let one := BitVec.allOnes 24
  let valid (ws : List (BitVec 24)) := ∀ i : Fin ws.length,
    let old := seed ++ ws.take i.val
    ws.get i ∉ old ∧ ws.get i ≠ 0 ∧ ws.get i ≠ one ∧
      ∃ a ∈ old, ∃ b ∈ old, ws.get i = a &&& b ∨ ws.get i = a ||| b
  have freshTarget : target ∉ seed := by decide
  have nonzero : target ≠ 0 := by decide
  have notOne : target ≠ one := by decide
  have hx : ∀ i : Fin xs.length, let old := seed ++ xs.take i.val
      ∃ a ∈ old, ∃ b ∈ old, xs.get i = a &&& b ∨ xs.get i = a ||| b := legal
  obtain ⟨zs,leZ,validZ,contains⟩ := clean seed xs hx
  have targetZ : target ∈ seed ++ zs :=
    ((contains _ present).resolve_left nonzero).resolve_left notOne
  have someZ := (List.mem_append.mp targetZ).resolve_left freshTarget
  obtain ⟨j,jlt,jval⟩ := List.mem_iff_getElem.mp someZ
  let ys := zs.take j
  have lenY : ys.length = j := by simp [ys,Nat.min_eq_left jlt.le]
  have goodY : valid ys := by
    intro i
    have hi : i.val < j := lenY ▸ i.isLt
    have zi : i.val < zs.length := hi.trans jlt
    have fromZ := validZ ⟨i.val,zi⟩
    have same : ys.get i = zs.get ⟨i.val,zi⟩ := by
      simp only [ys,List.get_eq_getElem,List.getElem_take]
    change ys.get i ∉ seed ++ ys.take i.val ∧ ys.get i ≠ 0 ∧ ys.get i ≠ one ∧
      ∃ a ∈ seed ++ ys.take i.val, ∃ b ∈ seed ++ ys.take i.val, ys.get i = a &&& b ∨ ys.get i = a ||| b
    rw [same,show ys.take i.val = zs.take i.val by
      simp only [ys,List.take_take]
      congr 1
      omega]
    exact fromZ
  have top := validZ ⟨j,jlt⟩
  change zs[j] ∉ seed ++ ys ∧ zs[j] ≠ 0 ∧ zs[j] ≠ one ∧
    ∃ a ∈ seed ++ ys, ∃ b ∈ seed ++ ys, zs[j] = a &&& b ∨ zs[j] = a ||| b at top
  rw [jval] at top
  obtain ⟨notIn,_,_,a,ha,b,hb,op⟩ := top
  have ab : a ≠ b := by
    intro h
    subst b
    apply notIn
    rcases op with e|e <;> simpa [e] using ha
  by_contra! small
  have smallY : ys.length ≤ 12 := by omega
  rcases op with e | e
  · apply andEnd ys smallY goodY notIn a ha b hb ab _ e
    change a &&& target = target ∧ b &&& target = target
    rw [e]
    constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i _ <;>
      simp only [BitVec.getLsbD_and] <;> cases a.getLsbD i <;> cases b.getLsbD i <;> decide
  · apply orEnd ys smallY goodY notIn a ha b hb ab _ e
    change a &&& target = a ∧ b &&& target = b
    rw [e]
    constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i _ <;>
      simp only [BitVec.getLsbD_and,BitVec.getLsbD_or] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> decide
