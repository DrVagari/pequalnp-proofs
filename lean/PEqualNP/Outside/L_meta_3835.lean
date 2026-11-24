import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_meta_3835

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma eval_cons (g : Gate) (gs : List Gate) (o : ℕ) (x : List Bool) :
    (Circuit.mk (g :: gs) o).eval x =
      (Circuit.mk gs o).eval
        (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

lemma last_getD (n : ℕ) (x : List Bool) (hx : x.length = n) :
    x.getD (↑(Fin.last n)) false = false := by
  apply List.getD_eq_default
  simp [hx]

lemma gate_rep (n : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    (∃ (i : Fin (n + 1)) (b : Bool), ∀ (x : List Bool), x.length = n →
      g.op.eval (g.inputs.map fun k => x.getD k false) = (b != x.getD (↑i) false)) ∨
    ∃ (i j : Fin n) (b : Bool), i < j ∧ ∀ (x : List Bool), x.length = n →
      g.op.eval (g.inputs.map fun k => x.getD k false) =
        if b = Bool.true then x.getD (↑i) false || x.getD (↑j) false
        else x.getD (↑i) false && x.getD (↑j) false := by
  obtain ⟨op, inputs⟩ := g
  have hop := hg.1
  have hlen := hg.2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · cases inputs with
    | nil =>
      exact Or.inl ⟨Fin.last n, true, fun x hx => by
        change true = (true != x.getD (↑(Fin.last n)) false)
        rw [last_getD n x hx]
        rfl⟩
    | cons i rest =>
      cases rest with
      | nil =>
        by_cases hi : i < n
        · exact Or.inl ⟨⟨i, Nat.lt_succ_of_lt hi⟩, false, fun x hx => by
            simp [GateOp.eval]⟩
        · exact Or.inl ⟨Fin.last n, false, fun x hx => by
            have hxi : x.getD i false = false := List.getD_eq_default _ _ (by omega)
            change (x.getD i false && true) = (false != x.getD (↑(Fin.last n)) false)
            rw [hxi, last_getD n x hx]
            rfl⟩
      | cons j rest =>
        cases rest with
        | cons k rest =>
          simp only [List.length_cons] at hlen
          omega
        | nil =>
          by_cases hi : i < n
          · by_cases hj : j < n
            · by_cases hij : i = j
              · subst j
                exact Or.inl ⟨⟨i, Nat.lt_succ_of_lt hi⟩, false, fun x hx => by
                  simp [GateOp.eval]⟩
              · rcases lt_or_gt_of_ne hij with hijlt | hjilt
                · exact Or.inr ⟨⟨i, hi⟩, ⟨j, hj⟩, false, hijlt, fun x hx => by
                    simp [GateOp.eval]⟩
                · exact Or.inr ⟨⟨j, hj⟩, ⟨i, hi⟩, false, hjilt, fun x hx => by
                    simp [GateOp.eval, Bool.and_comm]⟩
            · exact Or.inl ⟨Fin.last n, false, fun x hx => by
                have hxj : x.getD j false = false := List.getD_eq_default _ _ (by omega)
                change (x.getD i false && (x.getD j false && true)) =
                  (false != x.getD (↑(Fin.last n)) false)
                rw [hxj, last_getD n x hx]
                simp⟩
          · exact Or.inl ⟨Fin.last n, false, fun x hx => by
              have hxi : x.getD i false = false := List.getD_eq_default _ _ (by omega)
              change (x.getD i false && (x.getD j false && true)) =
                (false != x.getD (↑(Fin.last n)) false)
              rw [hxi, last_getD n x hx]
              simp⟩
  · cases inputs with
    | nil =>
      exact Or.inl ⟨Fin.last n, false, fun x hx => by
        change false = (false != x.getD (↑(Fin.last n)) false)
        rw [last_getD n x hx]
        rfl⟩
    | cons i rest =>
      cases rest with
      | nil =>
        by_cases hi : i < n
        · exact Or.inl ⟨⟨i, Nat.lt_succ_of_lt hi⟩, false, fun x hx => by
            simp [GateOp.eval]⟩
        · exact Or.inl ⟨Fin.last n, false, fun x hx => by
            have hxi : x.getD i false = false := List.getD_eq_default _ _ (by omega)
            change (x.getD i false || false) = (false != x.getD (↑(Fin.last n)) false)
            rw [hxi, last_getD n x hx]
            rfl⟩
      | cons j rest =>
        cases rest with
        | cons k rest =>
          simp only [List.length_cons] at hlen
          omega
        | nil =>
          by_cases hi : i < n
          · by_cases hj : j < n
            · by_cases hij : i = j
              · subst j
                exact Or.inl ⟨⟨i, Nat.lt_succ_of_lt hi⟩, false, fun x hx => by
                  simp [GateOp.eval]⟩
              · rcases lt_or_gt_of_ne hij with hijlt | hjilt
                · exact Or.inr ⟨⟨i, hi⟩, ⟨j, hj⟩, true, hijlt, fun x hx => by
                    simp [GateOp.eval]⟩
                · exact Or.inr ⟨⟨j, hj⟩, ⟨i, hi⟩, true, hjilt, fun x hx => by
                    simp [GateOp.eval, Bool.or_comm]⟩
            · exact Or.inl ⟨⟨i, Nat.lt_succ_of_lt hi⟩, false, fun x hx => by
                have hxj : x.getD j false = false := List.getD_eq_default _ _ (by omega)
                change (x.getD i false || (x.getD j false || false)) =
                  (false != x.getD i false)
                rw [hxj]
                simp⟩
          · by_cases hj : j < n
            · exact Or.inl ⟨⟨j, Nat.lt_succ_of_lt hj⟩, false, fun x hx => by
                have hxi : x.getD i false = false := List.getD_eq_default _ _ (by omega)
                change (x.getD i false || (x.getD j false || false)) =
                  (false != x.getD j false)
                rw [hxi]
                simp⟩
            · exact Or.inl ⟨Fin.last n, false, fun x hx => by
                have hxi : x.getD i false = false := List.getD_eq_default _ _ (by omega)
                have hxj : x.getD j false = false := List.getD_eq_default _ _ (by omega)
                change (x.getD i false || (x.getD j false || false)) =
                  (false != x.getD (↑(Fin.last n)) false)
                rw [hxi, hxj, last_getD n x hx]
                rfl⟩
  · cases inputs with
    | nil =>
      exact Or.inl ⟨Fin.last n, true, fun x hx => by
        change true = (true != x.getD (↑(Fin.last n)) false)
        rw [last_getD n x hx]
        rfl⟩
    | cons i rest =>
      by_cases hi : i < n
      · exact Or.inl ⟨⟨i, Nat.lt_succ_of_lt hi⟩, true, fun x hx => by
          simp [GateOp.eval]⟩
      · exact Or.inl ⟨Fin.last n, true, fun x hx => by
          have hxi : x.getD i false = false := List.getD_eq_default _ _ (by omega)
          change (!x.getD i false) = (true != x.getD (↑(Fin.last n)) false)
          rw [hxi, last_getD n x hx]
          rfl⟩

end PEqualNP.Outside.L_meta_3835

theorem PEqualNP.Outside.L_meta_3835 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (0 : ℕ) < x2.size → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size + (1 : ℕ) = x2.size ∧ ((∃ (x6 : Fin (x1 + (1 : ℕ))) (x7 : Bool), ∀ (x8 : List Bool), x8.length = x1 → x2.eval x8 = x5.eval (x8 ++ [x7 != x8.getD (↑x6) Bool.false])) ∨ ∃ (x6 : Fin x1) (x7 : Fin x1) (x8 : Bool), x6 < x7 ∧ ∀ (x9 : List Bool), x9.length = x1 → x2.eval x9 = x5.eval (x9 ++ [if x8 = Bool.true then x9.getD (↑x6) Bool.false || x9.getD (↑x7) Bool.false else x9.getD (↑x6) Bool.false && x9.getD (↑x7) Bool.false])) := by
  intro n C hC hsize
  obtain ⟨gates, o⟩ := C
  cases gates with
  | nil => simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hsize
  | cons g gs =>
    have hg := hC g (by simp)
    have htail : PEqualNP.MetaComplexity.FanInTwo ⟨gs, o⟩ := by
      intro h hh
      exact hC h (by simp [hh])
    refine ⟨⟨gs, o⟩, htail, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
    rcases PEqualNP.Outside.L_meta_3835.gate_rep n g hg with h | h
    · left
      obtain ⟨i, b, hval⟩ := h
      refine ⟨i, b, ?_⟩
      intro x hx
      rw [PEqualNP.Outside.L_meta_3835.eval_cons, hval x hx]
    · right
      obtain ⟨i, j, b, hij, hval⟩ := h
      refine ⟨i, j, b, hij, ?_⟩
      intro x hx
      rw [PEqualNP.Outside.L_meta_3835.eval_cons, hval x hx]
