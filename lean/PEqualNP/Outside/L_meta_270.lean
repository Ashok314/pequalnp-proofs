import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_270_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

private theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

private theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

private theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

private theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

private theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

private def val (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private theorem val_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C n x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, foldl_step_getD _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

private theorem val_none (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ)
    (hg : C.gates[j]? = none) : val C n x (n + j) = false := by
  unfold val
  apply getD_of_length_le
  rw [wires_eq, foldl_step_length]
  have := List.getElem?_eq_none_iff.mp hg
  simp only [List.length_ofFn]
  omega

private theorem val_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) :
    val C n x (n + j) =
      h.op.eval (h.inputs.map fun i => if i < n + j then val C n x i else false) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  have := gate_value C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at this
  exact this

private def singletonInput {n : ℕ} (p : Fin n) : Fin n → Bool :=
  fun q => decide (q = p)

private def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => val C n (singletonInput p) w = true

private def within {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  support C w ⊆ S ∧ 2 ≤ (support (n := n) C w).card

private theorem within_bounds {n : ℕ} (C : Circuit) (S : Finset (Fin n)) {w : ℕ}
    (hw : within C S w) : n ≤ w ∧ w < n + C.size := by
  classical
  obtain ⟨_, hcard⟩ := hw
  have hlo : n ≤ w := by
    by_contra! h
    have eq : support C w = {⟨w, h⟩} := by
      ext p
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and,
        val_input C n (singletonInput p) w h, singletonInput, decide_eq_true_eq, Finset.mem_singleton]
      exact eq_comm
    rw [eq, Finset.card_singleton] at hcard
    omega
  refine ⟨hlo, ?_⟩
  by_contra! h
  have eq : support (n := n) C w = ∅ := by
    ext p
    have none : C.gates[w - n]? = none :=
      List.getElem?_eq_none (by change n + C.gates.length ≤ w at h; omega)
    have hw' : n + (w - n) = w := by omega
    have hv := val_none C n (singletonInput p) (w - n) none
    rw [hw'] at hv
    simp [support, hv]
  simp [eq] at hcard

private abbrev Children := ℕ → ℕ × ℕ

private def readValue (f : ℕ → Bool) (w v : ℕ) : Bool :=
  if v < w then f v else false

private def gateValue (children : Children) (andGate : ℕ → Bool)
    (f : ℕ → Bool) (w : ℕ) : Bool :=
  let a := readValue f w (children w).1
  let b := readValue f w (children w).2
  if andGate w then a && b else a || b

private def cut (inside : ℕ → Prop) [DecidablePred inside]
    (children : Children) (andGate seed : ℕ → Bool) (w : ℕ) : Bool :=
  if inside w then
    let a := if _h : (children w).1 < w then cut inside children andGate seed (children w).1 else false
    let b := if _h : (children w).2 < w then cut inside children andGate seed (children w).2 else false
    if andGate w then a && b else a || b
  else seed w
termination_by w

private theorem cut_inside {inside : ℕ → Prop} [DecidablePred inside]
    (children : Children) (andGate seed : ℕ → Bool) {w : ℕ} (hw : inside w) :
    cut inside children andGate seed w = gateValue children andGate (cut inside children andGate seed) w := by
  rw [cut]
  simp [hw, gateValue, readValue, dite_eq_ite]

private theorem cut_outside {inside : ℕ → Prop} [DecidablePred inside]
    (children : Children) (andGate seed : ℕ → Bool) {w : ℕ} (hw : ¬ inside w) :
    cut inside children andGate seed w = seed w := by rw [cut]; simp [hw]

private def arcs (inside : ℕ → Prop) (children : Children) (w v : ℕ) : Prop :=
  inside w ∧ v < w ∧ (v = (children w).1 ∨ v = (children w).2)

private abbrev reachable (inside : ℕ → Prop) (children : Children) :=
  Relation.ReflTransGen (arcs inside children)

private theorem reachable_le {inside : ℕ → Prop} {children : Children} {r v : ℕ}
    (h : reachable inside children r v) : v ≤ r := by
  induction h with
  | refl => exact le_rfl
  | tail _ step ih => exact step.2.1.le.trans ih

private theorem boundary_bound (inside : ℕ → Prop) (children : Children) (r : ℕ)
    (allInside : Finset ℕ) (hAll : ∀ w, inside w → w ∈ allInside) :
    ∃ leaves : Finset ℕ, (∀ w, w ∈ leaves ↔ reachable inside children r w ∧ ¬ inside w) ∧
      leaves.card ≤ allInside.card + 1 := by
  classical
  let cone := (Finset.range (r + 1)).filter (reachable inside children r)
  let gates := cone.filter inside
  let leaves := cone.filter fun w => ¬ inside w
  have memCone : ∀ w, w ∈ cone ↔ reachable inside children r w := by
    intro w
    simp only [cone, Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun h => ⟨Nat.lt_succ_of_le (reachable_le h), h⟩⟩
  have root : r ∈ cone := (memCone r).2 Relation.ReflTransGen.refl
  -- Charge each wire other than the root to an operand slot of a retained gate.
  have cover : cone.erase r ⊆ gates.biUnion (fun w => {(children w).1, (children w).2}) := by
    intro w hw
    obtain ⟨hne, hc⟩ := Finset.mem_erase.mp hw
    cases (memCone w).1 hc with
    | refl => exact (hne rfl).elim
    | tail path edge =>
      obtain ⟨hi, _, hv⟩ := edge
      exact Finset.mem_biUnion.mpr
        ⟨_, Finset.mem_filter.mpr ⟨(memCone _).mpr path, hi⟩, by simpa using hv⟩
  have cardPairs : (gates.biUnion (fun w => {(children w).1, (children w).2})).card ≤ 2 * gates.card := by
    calc
      _ ≤ ∑ w ∈ gates, ({(children w).1, (children w).2} : Finset ℕ).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ gates, 2 := by
        apply Finset.sum_le_sum
        intro w _
        exact (Finset.card_insert_le _ _).trans (by simp)
      _ = _ := by simp [mul_comm]
  have bound := (Finset.card_le_card cover).trans cardPairs
  have erase := Finset.card_erase_add_one root
  have split : gates.card + leaves.card = cone.card := Finset.card_filter_add_card_filter_not inside
  have gc : gates.card ≤ allInside.card :=
    Finset.card_le_card (fun w hw => hAll w (Finset.mem_filter.mp hw).2)
  refine ⟨leaves, fun w => by simp [leaves, memCone], ?_⟩
  omega

private theorem cone_mono {inside : ℕ → Prop} {children : Children} {andGate : ℕ → Bool}
    {f g : ℕ → Bool} {r : ℕ}
    (hf : ∀ w, inside w → f w = gateValue children andGate f w)
    (hg : ∀ w, inside w → g w = gateValue children andGate g w)
    (hle : ∀ w, reachable inside children r w → ¬ inside w → f w = true → g w = true) :
    f r = true → g r = true := by
  suffices ∀ w, reachable inside children r w → f w = true → g w = true from
    this r Relation.ReflTransGen.refl
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw ht
    by_cases h : inside w
    · have child (v : ℕ) (hv : v = (children w).1 ∨ v = (children w).2)
          (hval : readValue f w v = true) : readValue g w v = true := by
        by_cases lt : v < w
        · rw [readValue, ite_eq_left lt] at hval ⊢
          exact ih _ lt (hw.tail ⟨h, lt, hv⟩) hval
        · simp [readValue, lt] at hval
      rw [hf w h, gateValue] at ht
      rw [hg w h, gateValue]
      by_cases hAnd : andGate w = true
      · simp only [ite_eq_left hAnd, Bool.and_eq_true] at ht ⊢
        exact ⟨child _ (Or.inl rfl) ht.1, child _ (Or.inr rfl) ht.2⟩
      · simp only [ite_eq_right hAnd, Bool.or_eq_true] at ht ⊢
        exact ht.imp (child _ (Or.inl rfl)) (child _ (Or.inr rfl))
    · exact hle w hw h ht

private theorem value_mono {n : ℕ} (C : Circuit)
    (shape : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) :
    ∀ w, val C n x w = true → val C n y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hv
    by_cases hw : w < n
    · rw [val_input _ _ _ _ hw] at hv ⊢
      exact hxy _ hv
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      cases h : C.gates[j]? with
      | none => simp [val_none C n x j h] at hv
      | some g =>
        obtain ⟨hop, hlen⟩ := shape g (List.mem_of_getElem? h)
        obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
        have read (v : ℕ) (hval : (if v < n + j then val C n x v else false) = true) :
            (if v < n + j then val C n y v else false) = true := by
          split_ifs at hval ⊢ with hv'
          · exact ih _ hv' hval
        rw [val_gate C n x j g h, hab] at hv
        rw [val_gate C n y j g h, hab]
        rcases hop with hop | hop
        · simp only [hop, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
            List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true] at hv ⊢
          exact ⟨read _ hv.1, read _ hv.2⟩
        · simp only [hop, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
            List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true] at hv ⊢
          exact hv.imp (read _) (read _)

private noncomputable def privateGates {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.range (n + C.size)).filter (within C S)

private theorem mem_privateGates {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : ℕ) :
    w ∈ privateGates C S ↔ within C S w := by
  classical
  simp only [privateGates, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨(within_bounds C S h).2, h⟩⟩

private theorem output_bound {n k c : ℕ} (C : Circuit) (S : Finset (Fin n)) (r : ℕ)
    (shape : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (target : support C r = S)
    (reject : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → val C n x r = false)
    (hck : c ≤ k) (hcs : c + 1 ≤ S.card) :
    c ≤ (privateGates C S).card := by
  classical
  let inside := within C S
  let gateAt (w : ℕ) := (C.gates[w - n]?).getD ⟨GateOp.and, []⟩
  let children : Children := fun w => ((gateAt w).inputs.getD 0 0, (gateAt w).inputs.getD 1 0)
  let andGate : ℕ → Bool := fun w => decide ((gateAt w).op = GateOp.and)
  let seed : ℕ → Bool := fun w => decide (¬ support C w ⊆ S)
  let trimmed := cut inside children andGate seed
  have hgenuine (x : Fin n → Bool) (w : ℕ) (hw : inside w) :
      val C n x w = gateValue children andGate (val C n x) w := by
    obtain ⟨low, high⟩ := within_bounds C S hw
    let j := w - n
    have hwj : n + j = w := by dsimp [j]; omega
    have hj : j < C.gates.length := by change w < n + C.gates.length at high; omega
    let gate := C.gates[j]
    have hget : C.gates[j]? = some gate := List.getElem?_eq_getElem hj
    have hgate : gateAt w = gate := by simp only [gateAt, j, hget, Option.getD_some]
    obtain ⟨hop, hlen⟩ := shape gate (List.mem_of_getElem? hget)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    have hv := val_gate C n x j gate hget
    rw [hwj, hab] at hv
    rw [hv]
    rcases hop with hop | hop
    · simp [gateValue, children, andGate, hgate, hab, hop, readValue, GateOp.eval]
    · simp [gateValue, children, andGate, hgate, hab, hop, readValue, GateOp.eval]
  have htrim (w : ℕ) (hw : inside w) :
      trimmed w = gateValue children andGate trimmed w := cut_inside children andGate seed hw
  have terminalValue (w : ℕ) (outside : ¬ inside w) : trimmed w = seed w :=
    cut_outside children andGate seed outside
  obtain ⟨leaves, leaf, leafBound⟩ :=
    boundary_bound inside children r (privateGates C S)
      (fun w hw => (mem_privateGates C S w).2 hw)
  by_contra! small
  have leafSmall : leaves.card ≤ c := by omega
  cases hroot : trimmed r with
  | true =>
    -- Turn on one point outside S for each terminal that the cut sets to true.
    let outsideLeaves := leaves.filter fun w => ¬ support C w ⊆ S
    have witness (w : {w // w ∈ outsideLeaves}) : ∃ p ∈ support C w.val, p ∉ S := by
      have notSub : ¬ support C w.val ⊆ S := (Finset.mem_filter.mp w.property).2
      by_contra! no
      exact notSub no
    choose pick inSupport outOfSet using witness
    let chosen : Finset (Fin n) := outsideLeaves.attach.image pick
    let x : Fin n → Bool := fun q => decide (q ∈ chosen)
    have hxsmall : (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k := by
      have eq : Finset.univ.filter (fun q : Fin n => x q = true) = chosen := by ext q; simp [x]
      rw [eq]
      have hp : chosen.card ≤ outsideLeaves.card := by simpa [chosen] using (Finset.card_image_le (s := outsideLeaves.attach) (f := pick))
      have he : outsideLeaves.card ≤ leaves.card := Finset.card_le_card (Finset.filter_subset _ _)
      omega
    have hxout : ∀ q ∈ S, x q = false := by
      intro q hq
      apply Bool.eq_false_iff.mpr
      intro hx
      have hmem : q ∈ chosen := by simpa [x] using hx
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hmem
      exact outOfSet w hq
    have terminal (w : ℕ) (reach : reachable inside children r w) (outside : ¬ inside w)
        (on : trimmed w = true) : val C n x w = true := by
      have hseed : ¬ support C w ⊆ S := by
        rw [terminalValue w outside] at on
        simpa [seed] using on
      let u : {w // w ∈ outsideLeaves} := ⟨w, Finset.mem_filter.mpr ⟨(leaf w).2 ⟨reach, outside⟩, hseed⟩⟩
      have pickOn : x (pick u) = true := by
        simp only [x, decide_eq_true_eq]
        exact Finset.mem_image.mpr ⟨u, Finset.mem_attach _ _, rfl⟩
      have fromSingleton : val C n (singletonInput (pick u)) w = true := (Finset.mem_filter.mp (inSupport u)).2
      apply value_mono C shape _ x _ w fromSingleton
      intro q hq
      obtain rfl : q = pick u := by simpa [singletonInput] using hq
      exact pickOn
    have on := cone_mono htrim (hgenuine x) terminal hroot
    rw [reject x hxsmall hxout] at on
    contradiction
  | false =>
    -- Each point in S must appear in the support of a terminal left at false.
    let internal := leaves.filter fun w => support C w ⊆ S
    let points := internal.biUnion (support (n := n) C)
    have pointsSmall : points.card ≤ leaves.card := by
      calc
        points.card ≤ ∑ w ∈ internal, (support (n := n) C w).card := Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ internal, 1 := by
          apply Finset.sum_le_sum
          intro w hw
          obtain ⟨hl, sub⟩ := Finset.mem_filter.mp hw
          have hn := ((leaf w).1 hl).2
          by_contra! h
          exact hn ⟨sub, by omega⟩
        _ = internal.card := by simp
        _ ≤ leaves.card := Finset.card_le_card (Finset.filter_subset _ _)
    have targets : S ⊆ points := by
      intro p hp
      by_contra absent
      have on : val C n (singletonInput p) r = true := by
        have mem : p ∈ support C r := by rwa [target]
        exact (Finset.mem_filter.mp mem).2
      have terminal (w : ℕ) (reach : reachable inside children r w) (outside : ¬ inside w)
          (hv : val C n (singletonInput p) w = true) : trimmed w = true := by
        rw [terminalValue w outside]
        simp only [seed, decide_eq_true_eq]
        intro subset
        exact absent (Finset.mem_biUnion.mpr
          ⟨w, Finset.mem_filter.mpr ⟨(leaf w).2 ⟨reach, outside⟩, subset⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩)
      have ht := cone_mono (hgenuine (singletonInput p)) htrim terminal on
      rw [hroot] at ht
      contradiction
    have hcard := (Finset.card_le_card targets).trans (pointsSmall.trans leafSmall)
    omega

end PEqualNP.Outside.L_meta_270_aux

open PEqualNP.Outside.L_meta_270_aux

theorem PEqualNP.Outside.L_meta_270 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size := by
  classical
  intro n m k S C o c intersect _sizeS shape singleton reject hck hcs
  let gates := fun i : Fin m => privateGates C (S i)
  have covered : ∀ i : Fin m, c i ≤ (gates i).card := by
    intro i
    have exactSupport : support C (o i) = S i := by
      ext p
      exact (Finset.mem_filter_univ p).trans (singleton i p)
    exact output_bound C (S i) (o i) shape exactSupport (reject i) (hck i) (hcs i)
  have disjoint : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint gates := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    have hi' := (mem_privateGates C (S i) w).1 hi
    have hj' := (mem_privateGates C (S j) w).1 hj
    have sub : support C w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨hi'.1 hp, hj'.1 hp⟩
    have card := (Finset.card_le_card sub).trans (intersect i j hij)
    have large := hi'.2
    omega
  have inRange : (Finset.univ.biUnion gates) ⊆ (Finset.range (n + C.size)).filter (fun w => n ≤ w) := by
    intro w hw
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨low, high⟩ := within_bounds C (S i) ((mem_privateGates C (S i) w).1 hi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr high, low⟩
  have rangeCard : ((Finset.range (n + C.size)).filter (fun w => n ≤ w)).card = C.size := by
    rw [← Nat.Ico_zero_eq_range]
    have eq : ((Finset.Ico 0 (n + C.size)).filter (fun w => n ≤ w)) = Finset.Ico n (n + C.size) := by
      ext w
      simp [Finset.mem_Ico, and_comm]
    rw [eq, Nat.card_Ico]
    omega
  calc
    ∑ i : Fin m, c i ≤ ∑ i : Fin m, (gates i).card := Finset.sum_le_sum (fun i _ => covered i)
    _ = (Finset.univ.biUnion gates).card := (Finset.card_biUnion disjoint).symm
    _ ≤ C.size := rangeCard ▸ Finset.card_le_card inRange
