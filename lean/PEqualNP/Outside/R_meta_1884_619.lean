import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Reindex the ordinary inputs and normalize the unary hint to the negative literal.
-- A binary gate bound of fifteen leaves at most three NOT gates in the suffix.
theorem PEqualNP.Outside.R_meta_1884_619
    (normalize : ∀ (n : ℕ) (i : Fin n) (f : Bool → Bool) (C : Circuit), FanInTwo C →
      C.output ≠ n → ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x ++ [!x i]) =
          C.eval (List.ofFn x ++ [f (x i)]))
    (nonNotBound : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
          x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) →
      15 ≤ C.gates.countP (fun g => GateOp.rec Bool.true Bool.true Bool.false
        (fun _ => Bool.true) Bool.true g.op))
    (core : ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
      15 ≤ C.gates.countP (fun g => GateOp.rec Bool.true Bool.true Bool.false
        (fun _ => Bool.true) Bool.true g.op) → ∃ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [!x 0]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
          x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ))
      (x3 : Bool → Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) →
      ∃ (x6 : Fin (10 : ℕ) → Bool),
        x1.eval (List.ofFn (x6 ∘ x2) ++ [x3 (x6 (0 : Fin (10 : ℕ)))]) ≠
          (fun (x7 : Fin (10 : ℕ) → Bool) =>
            x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) ||
            x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) ||
            x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) ||
            x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) ||
            x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) ||
            x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) ||
            x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) ||
            x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) ||
            x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) ||
            x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) ||
            x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) ||
            x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) ||
            x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) ||
            x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) ||
            x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C p f hC hsz
  -- The wire simulation follows R_meta_1886_74 and also permits repeated input coordinates.
  let r (i : ℕ) : ℕ := if hi : i < 10 then (p ⟨i, hi⟩).val else i
  let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩
  let D : Circuit := ⟨C.gates.map mapGate, r C.output⟩
  have hD : FanInTwo D := by
    intro a ha
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
    exact ⟨(hC g hg).1, by simpa [mapGate] using (hC g hg).2⟩
  have hszD : D.size = C.size := List.length_map mapGate
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have snoc (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    rcases lt_trichotomy i w.length with h | h | h
    · rw [ite_eq_right h.ne, List.getD_append _ _ _ _ h]
    · subst i; simp
    · rw [ite_eq_right h.ne', List.getD_eq_default (w ++ [b]) false (by simp; omega),
        List.getD_eq_default w false (by omega)]
  have simulate (gs : List Gate) : ∀ u v : List Bool, u.length = v.length → 10 ≤ v.length →
      (∀ i, u.getD (r i) false = v.getD i false) → ∀ i,
      ((gs.map mapGate).foldl step u).getD (r i) false = (gs.foldl step v).getD i false := by
    induction gs with
    | nil => intro u v _ _ h; exact h
    | cons g gs ih =>
      intro u v hlen h10 hv
      simp only [List.map_cons, List.foldl_cons]
      have hbit : (mapGate g).op.eval ((mapGate g).inputs.map fun i => u.getD i false) =
          g.op.eval (g.inputs.map fun i => v.getD i false) := by
        simp only [mapGate, List.map_map]
        congr 1
        exact List.map_congr_left (fun i _ => hv i)
      apply ih
      · simp [step, hlen]
      · simp [step]; omega
      · intro i
        simp only [step, hbit, snoc, hlen]
        have hr : r i = v.length ↔ i = v.length := by
          by_cases hi : i < 10
          · have hp := (p ⟨i, hi⟩).isLt
            simp [r, hi]
            constructor <;> omega
          · simp [r, hi]
        by_cases h : i = v.length
        · rw [ite_eq_left h, ite_eq_left (hr.mpr h)]
        · rw [ite_eq_right h, ite_eq_right (fun he => h (hr.mp he)), hv]
  have rel (x : Fin 10 → Bool) (b : Bool) :
      D.eval (List.ofFn x ++ [b]) = C.eval (List.ofFn (x ∘ p) ++ [b]) := by
    apply simulate C.gates
    · simp
    · simp
    · intro i
      by_cases hi : i < 10
      · rw [show r i = (p ⟨i,hi⟩).val by simp [r, hi],
          List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simpa using hi),
          List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hi)]
        simp only [List.getElem_ofFn, Function.comp_apply, Fin.eta]
      · rw [show r i = i by simp [r, hi],
          List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega)]
        simp
  let G := fun x : Fin 10 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  by_contra! same
  have good (x : Fin 10 → Bool) : D.eval (List.ofFn x ++ [f (x 0)]) = G x :=
    (rel x (f (x 0))).trans (same x)
  have hout : D.output ≠ 10 := by
    intro ho
    have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hi
    have onlyHint (x : Fin 10 → Bool) : D.eval (List.ofFn x ++ [f (x 0)]) = f (x 0) := by
      change (D.gates.foldl step (List.ofFn x ++ [f (x 0)])).getD D.output false = f (x 0)
      rw [ho]
      rw [keep _ _ _ (by simp)]
      simp
    let z : Fin 10 → Bool := fun _ => false
    let e : Fin 10 → Bool := fun i => decide (i = 1 ∨ i = 2)
    have noEdge : G z = false := by decide
    have anEdge : G e = true := by decide
    have ev0 := good z
    have ev1 := good e
    rw [onlyHint, noEdge] at ev0
    rw [onlyHint, anEdge] at ev1
    have a : z 0 = false := rfl
    have b : e 0 = false := by decide
    rw [a] at ev0
    rw [b, ev0] at ev1
    exact Bool.noConfusion ev1
  obtain ⟨E, hE, szE, norm⟩ := normalize 10 0 f D hD hout
  have hEs : E.size ≤ 18 := szE.trans (hszD.le.trans hsz)
  have eq (x : Fin 10 → Bool) : E.eval (List.ofFn x ++ [!x 0]) = G x :=
    (norm x).trans (good x)
  let g : Gate := ⟨.not,[0]⟩
  let prefixed : Circuit := ⟨g :: E.gates, E.output⟩
  have prefFan : FanInTwo prefixed := by
    intro a ha
    change a ∈ g :: E.gates at ha
    rcases List.mem_cons.mp ha with rfl | h
    · simp [g]
    · exact hE a h
  have prefEval (x : Fin 10 → Bool) : prefixed.eval (List.ofFn x) = G x := by
    have h0 : (List.ofFn x).getD 0 false = x 0 := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
      simp
    change (E.gates.foldl (fun w a => w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)])
      (List.ofFn x ++ [GateOp.not.eval [((List.ofFn x).getD 0 false)]])).getD E.output false = _
    rw [h0]
    exact eq x
  have bound := nonNotBound prefixed prefFan prefEval
  have boundE : 15 ≤ E.gates.countP (fun a => GateOp.rec Bool.true Bool.true Bool.false
      (fun _ => Bool.true) Bool.true a.op) := by simpa [prefixed,g] using bound
  obtain ⟨x,hbad⟩ := core E hE hEs boundE
  exact hbad (eq x)
