import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11918

open PEqualNP.CircuitLowerBounds

-- A binary gate introduces at most one extra input when tracing the output
-- backwards. A NOT reads only its first input and introduces none.
private def isOrdinary (g : Gate) : Bool :=
  match g.op with
  | .not => false
  | _ => true

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def wires (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

private theorem wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wires (gs ++ [g]) x = step (wires gs x) g := by
  simp [wires]

private theorem wires_length (gs : List Gate) (x : List Bool) :
    (wires gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton gs g ih => rw [wires_snoc, step]; simp [ih, Nat.add_assoc]

private theorem wire_before (gs : List Gate) (g : Gate) (x : List Bool) {i : ℕ}
    (h : i < x.length + gs.length) :
    (wires (gs ++ [g]) x).getD i false = (wires gs x).getD i false := by
  rw [wires_snoc, step]
  have h' : i < (wires gs x).length := by simpa [wires_length] using h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h']

private theorem wire_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (wires (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wires gs x).getD i false) := by
  rw [wires_snoc, step, ← wires_length]
  simp [List.getD_eq_getElem?_getD]

private theorem wire_outside (gs : List Gate) (x : List Bool) {i : ℕ}
    (h : x.length + gs.length ≤ i) : (wires gs x).getD i false = false := by
  have h' : (wires gs x).length ≤ i := by simpa [wires_length] using h
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h']


private def reads (g : Gate) : List ℕ :=
  if isOrdinary g then g.inputs else g.inputs.take 1

private theorem eval_reads (g : Gate) (a b : ℕ → Bool)
    (agree : ∀ j ∈ reads g, a j = b j) :
    g.op.eval (g.inputs.map a) = g.op.eval (g.inputs.map b) := by
  by_cases hn : g.op = .not
  · cases h : g.inputs with
    | nil => simp [hn, GateOp.eval]
    | cons j js =>
      have eq := agree j (by simp [reads, isOrdinary, hn, h])
      simp [hn, GateOp.eval, eq]
  · apply congrArg g.op.eval
    have ho : isOrdinary g = true := by cases eq : g.op <;> simp_all [isOrdinary]
    exact List.map_congr_left (by simpa [reads, ho] using agree)

private theorem trace (n : ℕ) (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (P : Finset ℕ) (bounded : ∀ i ∈ P, i < n + gs.length) :
    ∃ D : Finset ℕ, D.card ≤ P.card + (gs.filter isOrdinary).length ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
      (∀ i ∈ D, x.getD i false = y.getD i false) →
      ∀ i ∈ P, (wires gs x).getD i false = (wires gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing P with
  | nil => exact ⟨P, by simp, fun _ _ _ _ agree => agree⟩
  | append_singleton gs g ih =>
    let k := n + gs.length
    let Q := if k ∈ P then P.erase k ∪ ((reads g).filter (fun i => i < k)).toFinset else P
    have oldBound (i : ℕ) (hi : i ∈ P) (hn : i ≠ k) : i < k := by
      have hb := bounded i hi
      simp [k] at hb hn ⊢
      omega
    have keep (i : ℕ) (hi : i ∈ P) (hne : i ≠ k) : i ∈ Q := by
      by_cases hk : k ∈ P
      · exact (by simpa only [Q, if_pos hk] using
          (Finset.mem_union_left ((List.filter (fun i => decide (i < k)) (reads g)).toFinset)
            (Finset.mem_erase.mpr ⟨hne, hi⟩)))
      · simpa [Q, hk] using hi
    have bounds : ∀ i ∈ Q, i < k := by
      intro i hi
      by_cases hk : k ∈ P
      · simp only [Q, if_pos hk, Finset.mem_union, Finset.mem_erase,
          List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hi
        exact hi.elim (fun h => oldBound i h.2 h.1) (fun h => h.2)
      · exact oldBound i (by simpa [Q,hk] using hi) (fun eq => hk (eq ▸ (by simpa [Q,hk] using hi : i ∈ P)))
    have ar := arity g (by simp)
    obtain ⟨D, card, sound⟩ := ih (fun h hh => arity h (by simp [hh])) Q bounds
    refine ⟨D, ?_, ?_⟩
    · rw [List.filter_append, List.length_append]
      by_cases hk : k ∈ P
      · have hu := Finset.card_union_le (P.erase k) ((reads g).filter (fun i => i < k)).toFinset
        have hl := List.toFinset_card_le ((reads g).filter (fun i => i < k))
        have hf := List.length_filter_le (fun i : ℕ => decide (i < k)) (reads g)
        have he := Finset.card_erase_add_one hk
        simp only [Q, if_pos hk] at card
        by_cases hn : g.op = .not
        · have hr : (reads g).length ≤ 1 := by simp [reads, isOrdinary,hn]
          have hh : isOrdinary g = false := by simp [isOrdinary,hn]
          simp [hh]
          omega
        · have hh : isOrdinary g = true := by
            cases ho : g.op <;> simp_all [isOrdinary]
          have hr : (reads g).length ≤ 2 := by simpa [reads,hh] using ar
          simp [hh]
          omega
      · simp [Q,hk] at card
        omega
    · intro x y hx hy agree i hi
      have before := sound x y hx hy agree
      by_cases e : i = k
      · subst i
        rw [show k = x.length + gs.length by simp [k,hx], wire_last,
          show x.length + gs.length = y.length + gs.length by rw [hx,hy], wire_last]
        apply eval_reads
        intro j hj
        by_cases hjk : j < k
        · exact before j (by simp [Q, hi, hj, hjk])
        · rw [wire_outside gs x (by simpa [hx,k] using Nat.le_of_not_gt hjk),
            wire_outside gs y (by simpa [hy,k] using Nat.le_of_not_gt hjk)]
      · have bound := oldBound i hi e
        rw [wire_before gs g x (by simpa [hx,k] using bound),
            wire_before gs g y (by simpa [hy,k] using bound)]
        exact before i (keep i hi e)

private def witness : List Gate := [⟨.or, [5, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [8, 10]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [11, 12]⟩]

private def target (x : Fin 7 → Bool) : Bool :=
  (⟨witness, 13⟩ : Circuit).eval (List.ofFn x)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem target_spec : ∀ x : Fin 7 → Bool, target x = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

private def neighbor (i : Fin 7) : Fin 7 := (![4, 4, 4, 5, 0, 0, 0] : Fin 7 → Fin 7) i

private def low (i j : Fin 7) : Bool := decide (j = neighbor i)

private def high (i j : Fin 7) : Bool := decide (j = neighbor i ∨ j = i)

set_option maxRecDepth 100000 in
private theorem pair_raises : ∀ i : Fin 7, target (low i) = false ∧ target (high i) = true := by
  decide +kernel

private theorem input_value {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> rfl

private theorem same_pair (i : Fin 7) (j : ℕ) (h : j ≠ i.val) :
    (List.ofFn (low i)).getD j false = (List.ofFn (high i)).getD j false := by
  rw [input_value, input_value]
  by_cases hj : j < 7
  · have hn : (⟨j, hj⟩ : Fin 7) ≠ i := fun eq => h (congrArg Fin.val eq)
    simp [hj, low, high, hn]
  · simp [hj]

end PEqualNP.Outside.L_meta_11918

open PEqualNP.Outside.L_meta_11918 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_11918 :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ evaluates
  by_cases enough : 7 ≤ gates.length
  · refine ⟨witness, 13, by simp [witness], enough, target_spec⟩
  by_cases hn : ∃ g ∈ gates, g.op = .not
  swap
  · refine ⟨gates, o, ?_, le_rfl, evaluates⟩
    intro g hg
    refine ⟨?_, (legal g hg).2⟩
    rcases (legal g hg).1 with ha | ho | hb
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (hn ⟨g, hg, hb⟩).elim
  have hf : ∀ x : Fin 7 → Bool, (⟨gates, o⟩ : Circuit).eval (List.ofFn x) = target x :=
    fun x => (evaluates x).trans (target_spec x).symm
  have ho : o < 7 + gates.length := by
    by_contra h
    have eq := hf (high 0)
    change (wires gates (List.ofFn (high 0))).getD o false = _ at eq
    rw [wire_outside gates _ (by simpa using Nat.le_of_not_gt h), (pair_raises 0).2] at eq
    cases eq

  obtain ⟨D, hc, same⟩ := trace 7 gates (fun g hg => (legal g hg).2) {o} (by simpa using ho)
  have covered : Finset.range 7 ⊆ D := by
    intro j hj
    by_contra missing
    let i : Fin 7 := ⟨j, Finset.mem_range.mp hj⟩
    have eq := same (List.ofFn (low i)) (List.ofFn (high i)) (by simp) (by simp)
      (fun k hk => same_pair i k (by rintro rfl; exact missing hk)) o (by simp)
    change (⟨gates, o⟩ : Circuit).eval (List.ofFn (low i)) =
      (⟨gates, o⟩ : Circuit).eval (List.ofFn (high i)) at eq
    rw [hf, hf, (pair_raises i).1, (pair_raises i).2] at eq
    cases eq
  have inputs : 7 ≤ D.card := by simpa using Finset.card_le_card covered
  obtain ⟨g, hg, hop⟩ := hn
  have strict : (gates.filter isOrdinary).length < gates.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨g, hg, by simp [isOrdinary,hop]⟩
  simp only [Finset.card_singleton] at hc
  omega
