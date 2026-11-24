import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3081

/-- The wires a gate reads for its value: a NOT gate reads only its first input. -/
def reads (g : Gate) (v : ℕ) : Prop :=
  (g.op = GateOp.not ∧ g.inputs.head? = some v) ∨ (g.op ≠ GateOp.not ∧ v ∈ g.inputs)

/-- A NOT gate with only its first input kept; the value of the gate does not change. -/
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem mem_take1 {α : Type} (l : List α) (a : α) : a ∈ l.take 1 ↔ l.head? = some a := by
  cases l with
  | nil => simp
  | cons b l => simp [List.take, eq_comm]

theorem reads_iff_norm (g : Gate) (v : ℕ) : reads g v ↔ v ∈ (normGate g).inputs := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp [reads, normGate, mem_take1]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_eq' {α : Type} (L : List α) (S d : α) (k : ℕ) (h : k = L.length) :
    (L ++ [S]).getD k d = S := by
  subst h; exact getD_snoc_eq L S d

theorem getD_snoc2' {α : Type} (L : List α) (S T d : α) (k : ℕ) (h : k = L.length) :
    (L ++ [S] ++ [T]).getD k d = S := by
  subst h; simp


/-- Run a gate list on a wire list. -/
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := by simp [wiresFrom]

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have h : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [h, ht]; simp

/-- The value of a wire the gate list has not touched yet is the value of the input wire. -/
theorem getD_wiresFrom_of_lt (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (wiresFrom gs w).getD j false = w.getD j false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht]
  have h1 := List.getD_append w t false j
  rw [h1]
  simp [hj]

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

/-- Two wire lists that agree on the entries of `l` give the same list of entries read. -/
theorem map_getD_congr (l : List ℕ) (w w' : List Bool) (n : ℕ)
    (hin : ∀ i ∈ l, i < n → w.getD i false = w'.getD i false)
    (hin' : ∀ i ∈ l, n ≤ i → w.getD i false = w'.getD i false) :
    l.map (fun i => w.getD i false) = l.map (fun i => w'.getD i false) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons]
    have ha : w.getD a false = w'.getD a false := by
      by_cases hi1 : a < n
      · exact hin a (List.mem_cons_self) hi1
      · exact hin' a (List.mem_cons_self) (by omega)
    rw [ha, ih (fun i hi => hin i (List.mem_cons_of_mem _ hi))
      (fun i hi => hin' i (List.mem_cons_of_mem _ hi))]

/-- The value of a gate is fixed by the values of the wires it reads. -/
theorem gate_value_congr (g : Gate) (w w' : List Bool) (n : ℕ)
    (hin : ∀ i ∈ g.inputs, i < n → w.getD i false = w'.getD i false)
    (hin' : ∀ i ∈ g.inputs, n ≤ i → w.getD i false = w'.getD i false) :
    g.op.eval (g.inputs.map fun i => w.getD i false)
      = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  rw [map_getD_congr g.inputs w w' n hin hin']

/-- The heart: if no gate of the list reads wire `0`, and the two wire lists agree everywhere
  except possibly at `0`, then the values of the wires the list produces agree.  The two lists
already carry the value of the gate that came before, as `v` and `v'`. -/
theorem getD_ofFn (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  simp [List.getD_eq_getElem, List.getElem_ofFn, h]

theorem wiresFrom_agree (p : ℕ) (gs : List Gate) :
    ∀ (w w' : List Bool) (n : ℕ) (v v' : Bool),
      w.length = n → w'.length = n → v = v' →
      (∀ j, j ≠ p → j < n → w.getD j false = w'.getD j false) →
      (∀ g ∈ gs, p ∉ g.inputs) →
      (∀ j, n ≤ j → (wiresFrom gs (w ++ [v])).getD j false
          = (wiresFrom gs (w' ++ [v'])).getD j false) := by
  induction gs with
  | nil =>
      intro w w' n v v' hw hw' hv hag hno j hj
      have hj' : j = n ∨ n < j := by omega
      rcases hj' with hjEq | hj'
      · rw [hjEq]
        rw [wiresFrom_nil, wiresFrom_nil,
          getD_snoc_eq' w v false n hw.symm, getD_snoc_eq' w' v' false n hw'.symm, hv]
      · rw [wiresFrom_nil, wiresFrom_nil,
          List.getD_eq_default _ _ (by simp [hw]; omega),
          List.getD_eq_default _ _ (by simp [hw']; omega)]
  | cons g gs ih =>
      intro w w' n v v' hw hw' hv hag hno j hj
      have hgsno : ∀ h ∈ gs, p ∉ h.inputs := fun h hh => hno h (List.mem_cons_of_mem _ hh)
      have hgno : p ∉ g.inputs := hno g (List.mem_cons_self)
      set vg := g.op.eval (g.inputs.map fun i => (w ++ [v]).getD i false) with hvg
      set vg' := g.op.eval (g.inputs.map fun i => (w' ++ [v']).getD i false) with hvg'
      have hvg_eq : vg = vg' := by
        apply gate_value_congr g (w ++ [v]) (w' ++ [v']) n
        · intro i hi hi1
          have hne : i ≠ w.length := by omega
          have hne' : i ≠ w'.length := by omega
          rw [getD_snoc_ne w v false i hne, getD_snoc_ne w' v' false i hne']
          have hip : i ≠ p := by
            intro e
            exact hgno (e ▸ hi)
          exact hag i hip hi1
        · intro i hi hi1
          rcases hi1 with rfl | hi1
          · rw [getD_snoc_eq' w v false n hw.symm, getD_snoc_eq' w' v' false n hw'.symm, hv]
          · rw [List.getD_eq_default _ _ (by simp [hw]; omega),
              List.getD_eq_default _ _ (by simp [hw']; omega)]
      have hcons : wiresFrom (g :: gs) (w ++ [v])
          = wiresFrom gs ((w ++ [v]) ++ [vg]) := by
        simp only [wiresFrom, List.foldl_cons]
        rw [hvg]
      have hcons' : wiresFrom (g :: gs) (w' ++ [v'])
          = wiresFrom gs ((w' ++ [v']) ++ [vg']) := by
        simp only [wiresFrom, List.foldl_cons]
        rw [hvg']
      rw [hcons, hcons']
      have hj' : j = n ∨ n < j := by omega
      rcases hj' with hjEq | hj'
      · rw [hjEq]
        rw [getD_wiresFrom_of_lt gs _ n (by simp [hw]),
            getD_wiresFrom_of_lt gs _ n (by simp [hw'])]
        rw [getD_snoc2' w v vg false n hw.symm, getD_snoc2' w' v' vg' false n hw'.symm]
        exact hv
      · have hag' : ∀ k, k ≠ p → k < n + 1 →
            (w ++ [v]).getD k false = (w' ++ [v']).getD k false := by
          intro k hkp hk2
          by_cases hk3 : k < n
          · have hne : k ≠ w.length := by omega
            have hne' : k ≠ w'.length := by omega
            rw [getD_snoc_ne w v false k hne, getD_snoc_ne w' v' false k hne']
            exact hag k hkp hk3
          · have hk4 : k = n := by omega
            rw [hk4]
            rw [getD_snoc_eq' w v false n hw.symm, getD_snoc_eq' w' v' false n hw'.symm]
            exact hv
        have hrest := ih (w ++ [v]) (w' ++ [v']) (n + 1) vg vg'
          (by simp [hw]) (by simp [hw']) hvg_eq hag' hgsno
        have hval := hrest j (by omega)
        have hne : (w ++ [v]).length = n + 1 := by simp [hw]
        have hne' : (w' ++ [v']).length = n + 1 := by simp [hw']
        simpa [hne, hne'] using hval

/-- If the output wire is one of the input wires, the value of the circuit is that input. -/
theorem eval_of_output (C : Circuit) (x : List Bool) (hj : C.output < x.length) :
    C.eval x = x.getD C.output false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start C.gates x
  rw [Circuit.eval, wires_eq, ht]
  simp only [List.getD_append, hj]

/-- The edge function of the Petersen graph minus a vertex, written exactly as the
recorded statement writes it, so that the two are the same function. -/
def edgeFun : (Fin 9 → Bool) → Bool :=
  fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))

theorem edgeFun_singleton (j : Fin 9) : edgeFun (fun i => decide (i = j)) = false := by
  fin_cases j <;> decide

theorem edgeFun_A : edgeFun (fun i => decide (i.val = 0 || i.val = 2 || i.val = 4)) = true := by
  decide

theorem edgeFun_B : edgeFun (fun i => decide (i.val = 2 || i.val = 4)) = false := by
  decide

theorem edgeFun_A' : edgeFun (fun i => decide (i.val = 0 || i.val = 2)) = false := by
  decide

/-- A circuit that computes the edge function and whose first gate is `x_0 OR x_2` has, below
that gate, a gate that reads input `0`. -/
theorem reader_zero (C : Circuit)
    (hfirst : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (hfun : circuitFun 9 C = edgeFun) :
    ∃ g ∈ C.gates.drop 1, reads g 0 := by
  by_contra hcon
  have hno : ∀ g ∈ C.gates.drop 1, ¬ reads g 0 := by
    intro g hg hr
    exact hcon ⟨g, hg, hr⟩
  have hne : C.gates ≠ [] := by
    intro he
    let xt : Fin 9 → Bool := fun i => decide (i.val = 0)
    have h := hfirst xt
    rw [wires_eq, he, wiresFrom_nil] at h
    have hlen : (List.ofFn xt).length = 9 := by simp
    rw [List.getD_eq_default _ _ (by simp [hlen])] at h
    simp [xt] at h
  obtain ⟨g0, gs, hgs⟩ := List.exists_cons_of_ne_nil hne
  have hno' : ∀ g ∈ gs.map normGate, 0 ∉ g.inputs := by
    intro g hg
    have hgmem : ∃ g', g' ∈ gs ∧ normGate g' = g := by
      simpa [List.mem_map] using hg
    obtain ⟨g', hg', rfl⟩ := hgmem
    have hnmem : g' ∈ C.gates.drop 1 := by
      rw [hgs]
      simp only [List.drop_succ_cons, List.drop_zero]
      exact hg'
    exact fun hmem => (hno g' hnmem) ((reads_iff_norm g' 0).mpr hmem)
  have hfun' : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeFun x := by
    intro x
    have := congrFun hfun x
    simpa [circuitFun] using this
  have hout : 10 ≤ C.output := by
    by_contra hlt
    have hlt' : C.output < 10 := by omega
    by_cases hlt2 : C.output < 9
    · obtain ⟨jj, hjj⟩ : ∃ jj : Fin 9, jj.val = C.output := ⟨⟨C.output, by omega⟩, rfl⟩
      have hx : C.eval (List.ofFn (fun i : Fin 9 => decide (i = jj))) = true := by
        rw [eval_of_output _ _ (by simp <;> omega)]
        rw [← hjj]
        have h3 := getD_ofFn (fun i : Fin 9 => decide (i = jj)) jj.val (by omega)
        rw [h3]
        simp
      rw [hfun'] at hx
      have h2 := edgeFun_singleton jj
      simp only [h2] at hx
      exact Bool.noConfusion hx
    · have hEq : C.output = 9 := by omega
      have hx : C.eval (List.ofFn (fun i : Fin 9 => decide (i.val = 0 || i.val = 2))) = true := by
        rw [Circuit.eval, hEq]
        have h := hfirst (fun i : Fin 9 => decide (i.val = 0 || i.val = 2))
        simp at h
        exact h
      rw [hfun'] at hx
      have h2 := edgeFun_A'
      simp only [h2] at hx
      exact Bool.noConfusion hx
  set A : Fin 9 → Bool := fun i => decide (i.val = 0 || i.val = 2 || i.val = 4) with hA
  set B : Fin 9 → Bool := fun i => decide (i.val = 2 || i.val = 4) with hB
  have hagABfin : ∀ j : Fin 9, j.val ≠ 0 →
      (List.ofFn A).getD j.val false = (List.ofFn B).getD j.val false := by
    intro j hj0
    have hA' : (List.ofFn A).getD j.val false = A ⟨j.val, by omega⟩ := getD_ofFn A j.val (by omega)
    have hB' : (List.ofFn B).getD j.val false = B ⟨j.val, by omega⟩ := getD_ofFn B j.val (by omega)
    rw [hA', hB']
    simp only [hA, hB]
    simp [hj0]
  have hagAB : ∀ j : ℕ, j ≠ 0 → j < 9 →
      (List.ofFn A).getD j false = (List.ofFn B).getD j false := by
    intro j hj1 hj2
    exact hagABfin ⟨j, by omega⟩ hj1
  have hvA : (C.wires (List.ofFn A)).getD 9 false = (C.wires (List.ofFn B)).getD 9 false := by
    have h1 := hfirst A
    have h2 := hfirst B
    rw [h1, h2]
    simp [hA, hB]
  have hag := wiresFrom_agree 0 (gs.map normGate) (List.ofFn A) (List.ofFn B) 9
    ((C.wires (List.ofFn A)).getD 9 false) ((C.wires (List.ofFn B)).getD 9 false)
    (by simp) (by simp) hvA hagAB hno'
  have houtA : (C.wires (List.ofFn A)).getD C.output false
      = (C.wires (List.ofFn B)).getD C.output false := by
    have hA' : C.wires (List.ofFn A)
        = wiresFrom (gs.map normGate) ((List.ofFn A) ++ [(C.wires (List.ofFn A)).getD 9 false]) := by
      have hv : (C.wires (List.ofFn A)).getD 9 false = (normGate g0).op.eval ((normGate g0).inputs.map fun i => (List.ofFn A).getD i false) := by
        rw [normGate_eval]
        have hsplit : wiresFrom (g0 :: gs) (List.ofFn A)
            = wiresFrom gs ((List.ofFn A) ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn A).getD i false)]) := rfl
        rw [wires_eq, hgs, hsplit]
        have h1 := getD_wiresFrom_of_lt gs ((List.ofFn A) ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn A).getD i false)]) 9 (by simp)
        rw [h1]
        rw [getD_snoc_eq' (List.ofFn A) (g0.op.eval (g0.inputs.map fun i => (List.ofFn A).getD i false)) false 9 (by simp)]
      rw [hv]
      have hwn : wiresFrom C.gates (List.ofFn A)
          = wiresFrom (C.gates.map normGate) (List.ofFn A) := (wiresFrom_norm C.gates _).symm
      rw [wires_eq, hwn]
      simp only [hgs, List.map_cons]
      have hsplit : wiresFrom (normGate g0 :: gs.map normGate) (List.ofFn A)
          = wiresFrom (gs.map normGate) ((List.ofFn A) ++ [(normGate g0).op.eval ((normGate g0).inputs.map fun i => (List.ofFn A).getD i false)]) := rfl
      rw [hsplit]
    have hB' : C.wires (List.ofFn B)
        = wiresFrom (gs.map normGate) ((List.ofFn B) ++ [(C.wires (List.ofFn B)).getD 9 false]) := by
      have hv : (C.wires (List.ofFn B)).getD 9 false = (normGate g0).op.eval ((normGate g0).inputs.map fun i => (List.ofFn B).getD i false) := by
        rw [normGate_eval]
        have hsplit : wiresFrom (g0 :: gs) (List.ofFn B)
            = wiresFrom gs ((List.ofFn B) ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn B).getD i false)]) := rfl
        rw [wires_eq, hgs, hsplit]
        have h1 := getD_wiresFrom_of_lt gs ((List.ofFn B) ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn B).getD i false)]) 9 (by simp)
        rw [h1]
        rw [getD_snoc_eq' (List.ofFn B) (g0.op.eval (g0.inputs.map fun i => (List.ofFn B).getD i false)) false 9 (by simp)]
      rw [hv]
      have hwn : wiresFrom C.gates (List.ofFn B)
          = wiresFrom (C.gates.map normGate) (List.ofFn B) := (wiresFrom_norm C.gates _).symm
      rw [wires_eq, hwn]
      simp only [hgs, List.map_cons]
      have hsplit : wiresFrom (normGate g0 :: gs.map normGate) (List.ofFn B)
          = wiresFrom (gs.map normGate) ((List.ofFn B) ++ [(normGate g0).op.eval ((normGate g0).inputs.map fun i => (List.ofFn B).getD i false)]) := rfl
      rw [hsplit]
    rw [hA', hB']
    exact hag C.output (by omega)
  have h1 := hfun' A
  have h2 := hfun' B
  rw [Circuit.eval] at h1 h2
  simp only [hA, hB] at h1 h2
  have hA1 : edgeFun A = true := by rw [hA]; exact edgeFun_A
  have hB1 : edgeFun B = false := by rw [hB]; exact edgeFun_B
  rw [h1, h2] at houtA
  rw [hA1, hB1] at houtA
  exact Bool.noConfusion houtA


/-- The edge function is true on the input `{x_0, x_2, x_3}` and false on `{x_0, x_3}`. -/
theorem edgeFun_A2 : edgeFun (fun i => decide (i.val = 0 || i.val = 2 || i.val = 3)) = true := by
  decide

theorem edgeFun_B2 : edgeFun (fun i => decide (i.val = 0 || i.val = 3)) = false := by
  decide

/-- A circuit that computes the edge function and whose first gate is `x_0 OR x_2` has, below
that gate, a gate that reads input `0`. -/
theorem reader_two (C : Circuit)
    (hfirst : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (hfun : circuitFun 9 C = edgeFun) :
    ∃ g ∈ C.gates.drop 1, reads g 2 := by
  by_contra hcon
  have hno : ∀ g ∈ C.gates.drop 1, ¬ reads g 2 := by
    intro g hg hr
    exact hcon ⟨g, hg, hr⟩
  have hne : C.gates ≠ [] := by
    intro he
    let xt : Fin 9 → Bool := fun i => decide (i.val = 0)
    have h := hfirst xt
    rw [wires_eq, he, wiresFrom_nil] at h
    have hlen : (List.ofFn xt).length = 9 := by simp
    rw [List.getD_eq_default _ _ (by simp [hlen])] at h
    simp [xt] at h
  obtain ⟨g0, gs, hgs⟩ := List.exists_cons_of_ne_nil hne
  have hno' : ∀ g ∈ gs.map normGate, 2 ∉ g.inputs := by
    intro g hg
    have hgmem : ∃ g', g' ∈ gs ∧ normGate g' = g := by
      simpa [List.mem_map] using hg
    obtain ⟨g', hg', rfl⟩ := hgmem
    have hnmem : g' ∈ C.gates.drop 1 := by
      rw [hgs]
      simp only [List.drop_succ_cons, List.drop_zero]
      exact hg'
    exact fun hmem => (hno g' hnmem) ((reads_iff_norm g' 2).mpr hmem)
  have hfun' : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeFun x := by
    intro x
    have := congrFun hfun x
    simpa [circuitFun] using this
  have hout : 10 ≤ C.output := by
    by_contra hlt
    have hlt' : C.output < 10 := by omega
    by_cases hlt2 : C.output < 9
    · obtain ⟨jj, hjj⟩ : ∃ jj : Fin 9, jj.val = C.output := ⟨⟨C.output, by omega⟩, rfl⟩
      have hx : C.eval (List.ofFn (fun i : Fin 9 => decide (i = jj))) = true := by
        rw [eval_of_output _ _ (by simp <;> omega)]
        rw [← hjj]
        have h3 := getD_ofFn (fun i : Fin 9 => decide (i = jj)) jj.val (by omega)
        rw [h3]
        simp
      rw [hfun'] at hx
      have h2 := edgeFun_singleton jj
      simp only [h2] at hx
      exact Bool.noConfusion hx
    · have hEq : C.output = 9 := by omega
      have hx : C.eval (List.ofFn (fun i : Fin 9 => decide (i.val = 0 || i.val = 2))) = true := by
        rw [Circuit.eval, hEq]
        have h := hfirst (fun i : Fin 9 => decide (i.val = 0 || i.val = 2))
        simp at h
        exact h
      rw [hfun'] at hx
      have h2 := edgeFun_A'
      simp only [h2] at hx
      exact Bool.noConfusion hx
  set A : Fin 9 → Bool := fun i => decide (i.val = 0 || i.val = 2 || i.val = 3) with hA
  set B : Fin 9 → Bool := fun i => decide (i.val = 0 || i.val = 3) with hB
  have hagABfin : ∀ j : Fin 9, j.val ≠ 2 →
      (List.ofFn A).getD j.val false = (List.ofFn B).getD j.val false := by
    intro j hj0'
    have hA' : (List.ofFn A).getD j.val false = A ⟨j.val, by omega⟩ := getD_ofFn A j.val (by omega)
    have hB' : (List.ofFn B).getD j.val false = B ⟨j.val, by omega⟩ := getD_ofFn B j.val (by omega)
    rw [hA', hB']
    simp only [hA, hB]
    simp [hj0']
  have hagAB : ∀ j : ℕ, j ≠ 2 → j < 9 →
      (List.ofFn A).getD j false = (List.ofFn B).getD j false := by
    intro j hj1 hj2
    exact hagABfin ⟨j, by omega⟩ hj1
  have hvA : (C.wires (List.ofFn A)).getD 9 false = (C.wires (List.ofFn B)).getD 9 false := by
    have h1 := hfirst A
    have h2 := hfirst B
    rw [h1, h2]
    simp [hA, hB]
  have hag := wiresFrom_agree 2 (gs.map normGate) (List.ofFn A) (List.ofFn B) 9
    ((C.wires (List.ofFn A)).getD 9 false) ((C.wires (List.ofFn B)).getD 9 false)
    (by simp) (by simp) hvA hagAB hno'
  have houtA : (C.wires (List.ofFn A)).getD C.output false
      = (C.wires (List.ofFn B)).getD C.output false := by
    have hA' : C.wires (List.ofFn A)
        = wiresFrom (gs.map normGate) ((List.ofFn A) ++ [(C.wires (List.ofFn A)).getD 9 false]) := by
      have hv : (C.wires (List.ofFn A)).getD 9 false = (normGate g0).op.eval ((normGate g0).inputs.map fun i => (List.ofFn A).getD i false) := by
        rw [normGate_eval]
        have hsplit : wiresFrom (g0 :: gs) (List.ofFn A)
            = wiresFrom gs ((List.ofFn A) ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn A).getD i false)]) := rfl
        rw [wires_eq, hgs, hsplit]
        have h1 := getD_wiresFrom_of_lt gs ((List.ofFn A) ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn A).getD i false)]) 9 (by simp)
        rw [h1]
        rw [getD_snoc_eq' (List.ofFn A) (g0.op.eval (g0.inputs.map fun i => (List.ofFn A).getD i false)) false 9 (by simp)]
      rw [hv]
      have hwn : wiresFrom C.gates (List.ofFn A)
          = wiresFrom (C.gates.map normGate) (List.ofFn A) := (wiresFrom_norm C.gates _).symm
      rw [wires_eq, hwn]
      simp only [hgs, List.map_cons]
      have hsplit : wiresFrom (normGate g0 :: gs.map normGate) (List.ofFn A)
          = wiresFrom (gs.map normGate) ((List.ofFn A) ++ [(normGate g0).op.eval ((normGate g0).inputs.map fun i => (List.ofFn A).getD i false)]) := rfl
      rw [hsplit]
    have hB' : C.wires (List.ofFn B)
        = wiresFrom (gs.map normGate) ((List.ofFn B) ++ [(C.wires (List.ofFn B)).getD 9 false]) := by
      have hv : (C.wires (List.ofFn B)).getD 9 false = (normGate g0).op.eval ((normGate g0).inputs.map fun i => (List.ofFn B).getD i false) := by
        rw [normGate_eval]
        have hsplit : wiresFrom (g0 :: gs) (List.ofFn B)
            = wiresFrom gs ((List.ofFn B) ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn B).getD i false)]) := rfl
        rw [wires_eq, hgs, hsplit]
        have h1 := getD_wiresFrom_of_lt gs ((List.ofFn B) ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn B).getD i false)]) 9 (by simp)
        rw [h1]
        rw [getD_snoc_eq' (List.ofFn B) (g0.op.eval (g0.inputs.map fun i => (List.ofFn B).getD i false)) false 9 (by simp)]
      rw [hv]
      have hwn : wiresFrom C.gates (List.ofFn B)
          = wiresFrom (C.gates.map normGate) (List.ofFn B) := (wiresFrom_norm C.gates _).symm
      rw [wires_eq, hwn]
      simp only [hgs, List.map_cons]
      have hsplit : wiresFrom (normGate g0 :: gs.map normGate) (List.ofFn B)
          = wiresFrom (gs.map normGate) ((List.ofFn B) ++ [(normGate g0).op.eval ((normGate g0).inputs.map fun i => (List.ofFn B).getD i false)]) := rfl
      rw [hsplit]
    rw [hA', hB']
    exact hag C.output (by omega)
  have h1 := hfun' A
  have h2 := hfun' B
  rw [Circuit.eval] at h1 h2
  simp only [hA, hB] at h1 h2
  have hA1 : edgeFun A = true := by rw [hA]; exact edgeFun_A2
  have hB1 : edgeFun B = false := by rw [hB]; exact edgeFun_B2
  rw [h1, h2] at houtA
  rw [hA1, hB1] at houtA
  exact Bool.noConfusion houtA

end PEqualNP.Outside.L_meta_3081

theorem PEqualNP.Outside.L_meta_3081 :
    let reads := fun (g : PEqualNP.CircuitLowerBounds.Gate) (v : ℕ) =>
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some v) ∨
        (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ v ∈ g.inputs)
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (∀ v : ℕ, v = 0 ∨ v = 2 → ∃ g ∈ x1.gates.drop 1, reads g v) := by
  intro rd x1 hfirst hfun v hv
  rcases hv with rfl | rfl
  · exact PEqualNP.Outside.L_meta_3081.reader_zero x1 hfirst hfun
  · exact PEqualNP.Outside.L_meta_3081.reader_two x1 hfirst hfun
