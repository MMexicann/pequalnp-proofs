import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4320

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := List.foldl_append

lemma run_one (g : Gate) (w : List Bool) : run [g] w = step w g := rfl

lemma run_len (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma getD_new (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp

def Safe (gs : List Gate) (w : List Bool) (P : Prop) : Prop :=
  ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and →
    (run gs w).getD (w.length + j) false = true → P

lemma safe_append {gs hs : List Gate} {w : List Bool} {P : Prop}
    (hgs : Safe gs w P) (hhs : Safe hs (run gs w) P) : Safe (gs ++ hs) w P := by
  intro j g hj hAnd hval
  by_cases h : j < gs.length
  · rw [List.getElem?_append_left h] at hj
    rw [run_append, run_keep _ _ _ (by rw [run_len]; omega)] at hval
    exact hgs j g hj hAnd hval
  · rw [List.getElem?_append_right (by omega)] at hj
    have hi : w.length + j = (run gs w).length + (j - gs.length) := by
      rw [run_len]
      omega
    rw [run_append, hi] at hval
    exact hhs _ _ hj hAnd hval

lemma safe_one {g : Gate} {w : List Bool} {P : Prop}
    (h : g.op = GateOp.and → g.op.eval (g.inputs.map fun i => w.getD i false) = true → P) :
    Safe [g] w P := by
  intro j g' hj hg hval
  cases j with
  | zero =>
    have he : g = g' := by simpa using hj
    subst g'
    apply h hg
    simpa only [Nat.add_zero, run_one, step, getD_new] using hval
  | succ j => simp at hj

def Ops (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def Bld (n : ℕ) (P : (Fin n → Bool) → Prop) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (o : ℕ), Ops gs ∧ gs.length ≤ s ∧
    o < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (run gs w).getD o false = F (fun i => w.getD i false) ∧
      Safe gs w (P (fun i => w.getD i false))

lemma bld_le {n : ℕ} {P : (Fin n → Bool) → Prop} {F : (Fin n → Bool) → Bool} {s s' : ℕ}
    (h : Bld n P F s) (hs : s ≤ s') : Bld n P F s' := by
  intro m hm
  obtain ⟨gs, o, ho, hl, hlt, he⟩ := h m hm
  exact ⟨gs, o, ho, hl.trans hs, hlt, he⟩

lemma bld_eq {n : ℕ} {P : (Fin n → Bool) → Prop} {F H : (Fin n → Bool) → Bool} {s : ℕ}
    (h : Bld n P F s) (e : ∀ x, F x = H x) : Bld n P H s := by
  intro m hm
  obtain ⟨gs, o, ho, hl, hlt, he⟩ := h m hm
  refine ⟨gs, o, ho, hl, hlt, fun w hw => ?_⟩
  obtain ⟨hev, hsafe⟩ := he w hw
  exact ⟨hev.trans (e _), hsafe⟩

lemma bld_var {n : ℕ} (P : (Fin n → Bool) → Prop) (i : Fin n) :
    Bld n P (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i.val, by simp [Ops], by simp, by simpa using i.isLt.trans_le hm, ?_⟩
  intro w _
  refine ⟨rfl, ?_⟩
  intro j g hj
  simp at hj

lemma bld_bin {n : ℕ} {P : (Fin n → Bool) → Prop}
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ}
    (h1 : Bld n P F s1) (h2 : Bld n P H s2)
    (hAnd : op = GateOp.and → ∀ x, c (F x) (H x) = true → P x) :
    Bld n P (fun x => c (F x) (H x)) (s1+s2+1) := by
  intro m hm
  obtain ⟨gs1, o1, ops1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ops2, len2, ho2, ev2⟩ := h2 (m+gs1.length) (by omega)
  let g : Gate := ⟨op, [o1,o2]⟩
  refine ⟨gs1 ++ gs2 ++ [g], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with (hg' | hg') | rfl
    · exact ops1 _ hg'
    · exact ops2 _ hg'
    · exact ⟨hop, by simp [g]⟩
  · simp; omega
  · simp; omega
  · intro w hw
    let v := run gs1 w
    let u := run gs2 v
    have hv : v.length = m + gs1.length := by simp [v, run_len, hw]
    have hu : u.length = m + gs1.length + gs2.length := by simp [u, run_len, hv]
    have hp : (fun i : Fin n => v.getD i false) = (fun i : Fin n => w.getD i false) := by
      funext i
      exact run_keep _ _ _ (by rw [hw]; exact i.isLt.trans_le hm)
    obtain ⟨eq1, safe1⟩ := ev1 w hw
    have ev2' := ev2 v hv
    rw [hp] at ev2'
    obtain ⟨eq2, safe2⟩ := ev2'
    have a1 : u.getD o1 false = F (fun i => w.getD i false) := by
      change (run gs2 v).getD o1 false = _
      rw [run_keep _ _ _ (by omega)]
      exact eq1
    have a2 : u.getD o2 false = H (fun i => w.getD i false) := eq2
    have out_eq : g.op.eval (g.inputs.map fun i => u.getD i false) =
        c (F (fun i => w.getD i false)) (H (fun i => w.getD i false)) := by
      simp only [g, List.map_cons, List.map_nil, hc, a1, a2]
    constructor
    · rw [run_append, run_append]
      change (run [g] u).getD (m + gs1.length + gs2.length) false = _
      rw [← hu, run_one, step, getD_new]
      exact out_eq
    · apply safe_append (safe_append safe1 safe2)
      rw [run_append]
      exact safe_one (fun hg hgval => hAnd hg _ (out_eq ▸ hgval))

lemma bld_or {n : ℕ} {P : (Fin n → Bool) → Prop} {F H : (Fin n → Bool) → Bool} {s t : ℕ}
    (h : Bld n P F s) (h' : Bld n P H t) :
    Bld n P (fun x => F x || H x) (s+t+1) :=
  bld_bin .or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h h'
    (by intro he; cases he)

lemma bld_and {n : ℕ} {P : (Fin n → Bool) → Prop} {F H : (Fin n → Bool) → Bool} {s t : ℕ}
    (h : Bld n P F s) (h' : Bld n P H t) (hs : ∀ x, (F x && H x) = true → P x) :
    Bld n P (fun x => F x && H x) (s+t+1) :=
  bld_bin .and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h h' (fun _ => hs)

lemma bld_anyList {n : ℕ} (P : (Fin n → Bool) → Prop) (vs : List (Fin n)) :
    ∀ v : Fin n, Bld n P (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_eq (bld_var P v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have h := bld_or (bld_var P v) (ih w)
    refine bld_eq (bld_le h (by simp)) ?_
    intro x
    rfl

lemma bld_anyFinset {n : ℕ} (P : (Fin n → Bool) → Prop) (S : Finset (Fin n))
    (hS : S.Nonempty) :
    Bld n P (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_eq (bld_le (bld_anyList P vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in
lemma bld_edges (n : ℕ) (T : Finset (Fin n)) (P : (Fin n → Bool) → Prop) :
    ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
      (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
      (∀ x : Fin n → Bool, ∀ e ∈ E, (∀ v ∈ e, x v = true) → P x) →
      Bld n P (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc _
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc hs
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    have s2 : ∀ x : Fin n → Bool, ∀ e ∈ E2, (∀ v ∈ e, x v = true) → P x :=
      fun x e he hx => hs x e (Finset.mem_filter.mp he).1 hx
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n P (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have heq (x : Fin n → Bool) :
          (x t && decide (∃ v ∈ S, x v = true)) =
            decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) := by
        rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
        constructor
        · rintro ⟨ht, v, hv, hxv⟩
          refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
          intro u hu
          rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
        · rintro ⟨e, he, hall⟩
          have he' := he
          rw [hE1, Finset.mem_filter] at he'
          obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
          subst hb
          exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
            hall b (Sym2.mem_mk_right _ _)⟩
      have safe : ∀ x, (x t && decide (∃ v ∈ S, x v = true)) = true → P x := by
        intro x hx
        rw [heq, decide_eq_true_eq] at hx
        obtain ⟨e,he,hx⟩ := hx
        exact hs x e (Finset.mem_filter.mp he).1 hx
      have hb := bld_and (bld_var P t) (bld_anyFinset P S hSne) safe
      have hpos := hSne.card_pos
      exact bld_eq (bld_le hb (by omega)) heq
    have key (x : Fin n → Bool) : decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) ||
          decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have hp := h2.card_pos
        exact bld_eq (bld_le (bld_or (star h1) (ih E2 h2 c2 s2)) (by omega))
          (fun x => (key x).symm)
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_eq (bld_le (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra he
        rw [Finset.not_nonempty_iff_eq_empty] at he
        have := hE.card_pos
        rw [h1, he] at hsplit
        simp at hsplit
        omega
      refine bld_eq (bld_le (ih E2 h2 c2 s2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

lemma edge_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    (∃ e ∈ G.edgeFinset, ∀ v ∈ e, x v = true) ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨e, he, h⟩
    revert he h
    refine Sym2.ind (fun a b => ?_) e
    intro he h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨s(i, j), by simpa using hij, ?_⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption

open Classical in
lemma covered (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (hT : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) ∧
      C.size ≤ G.edgeFinset.card + T.card - 1 ∧
      ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
        ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+j) false = true →
          ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  by_cases hE : G.edgeFinset.Nonempty
  · have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
      intro e
      refine Sym2.ind (fun a b => ?_) e
      intro he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rcases hT a b he with h | h
      · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
      · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
    let P (x : Fin n → Bool) := ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
    have hs : ∀ x : Fin n → Bool, ∀ e ∈ G.edgeFinset, (∀ v ∈ e, x v = true) → P x :=
      fun x e he hx => (edge_iff G x).mp ⟨e,he,hx⟩
    obtain ⟨gs,o,hops,hsize,_,hev⟩ := bld_edges n T P G.edgeFinset hE cov hs n le_rfl
    let C : Circuit := ⟨gs,o⟩
    have inputs (x : Fin n → Bool) : (fun i : Fin n => (List.ofFn x).getD i false) = x := by
      funext i
      simp
    refine ⟨C, ?_, ?_, hsize, ?_⟩
    · simpa [C, PEqualNP.MetaComplexity.Monotone2, Ops] using hops
    · intro x
      have h := (hev (List.ofFn x) (List.length_ofFn)).1
      rw [inputs] at h
      change (run gs (List.ofFn x)).getD o false = _
      rw [h, decide_eq_decide]
      exact edge_iff G x
    · intro j g hj hg x hx
      have h := (hev (List.ofFn x) (List.length_ofFn)).2
      rw [inputs] at h
      have heval : (run gs (List.ofFn x)).getD (n+j) false = true := hx
      exact h j g hj hg (by rw [List.length_ofFn]; exact heval)
  · refine ⟨⟨[],n⟩, by simp [PEqualNP.MetaComplexity.Monotone2], ?_, Nat.zero_le _, ?_⟩
    · intro x
      have hnone : ¬ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
        rintro ⟨u,v,hu,_,_⟩
        exact hE ⟨s(u,v), by simpa using hu⟩
      change (List.ofFn x).getD n false = _
      rw [decide_eq_false hnone, List.getD_eq_default]
      simp
    · intro j g hj
      simp at hj

end PEqualNP.Outside.L_meta_4320

theorem PEqualNP.Outside.L_meta_4320 :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)),
      (∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4) →
        ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧
          (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = Decidable.decide
            (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) ∧
          x6.size ≤ x2.edgeFinset.card + x4.card - (1 : ℕ) ∧
          ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate),
            x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and →
              ∀ (x11 : Fin x1 → Bool), (x6.wires (List.ofFn x11)).getD (x1 + x7) Bool.false = Bool.true →
                ∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x11 x14 = Bool.true := by
  intro n G _ T hT
  exact PEqualNP.Outside.L_meta_4320.covered n G T hT
