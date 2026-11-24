import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3698

open scoped BigOperators

theorem incidenceCardLe {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hline : ∀ l, Fintype.card {p // I p l} = q + 1)
    (edges : Finset (Fin N × Fin N)) (hinc : ∀ e ∈ edges, I e.1 e.2) :
    edges.card ≤ N * (q + 1) := by
  classical
  let column (l : Fin N) : Finset (Fin N × Fin N) :=
    (Finset.univ.filter (fun p => I p l)).image (fun p => (p, l))
  have hsub : edges ⊆ Finset.univ.biUnion column := by
    intro e he
    exact Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc e he⟩, rfl⟩⟩
  have hcard (l : Fin N) : (column l).card = q + 1 := by
    dsimp only [column]
    rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
    simpa only [Fintype.card_subtype] using hline l
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (by simp [hcard]))

theorem boundWhenAllIncidencesFit {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hline : ∀ l, Fintype.card {p // I p l} = q + 1)
    (hbudget : N * (q + 1) ≤ 24 * C.size) :
    (Finset.univ.filter fun e : Fin N × Fin N =>
      I e.1 e.2 ∧
      PEqualNP.MetaComplexity.circuitFun (N + N) C
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true ∧
      PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
      PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false).card
      ≤ 24 * C.size := by
  refine (incidenceCardLe hline _ ?_).trans hbudget
  intro e he
  exact (Finset.mem_filter.mp he).2.1

theorem weightedNeighborsLeSupport {α β : Type*} [DecidableEq α] [DecidableEq β]
    (adj : β → Finset α) (lines : Finset β) (support : Finset α) (p : α)
    (weight : β → ℕ)
    (hp : p ∈ support)
    (hsub : ∀ l ∈ lines, adj l ⊆ support)
    (hthrough : ∀ l ∈ lines, p ∈ adj l)
    (hunique : ∀ l ∈ lines, ∀ k ∈ lines, l ≠ k →
      ∀ a ∈ adj l, a ∈ adj k → a = p)
    (hweight : ∀ l ∈ lines, weight l < (adj l).card) :
    1 + (∑ l ∈ lines, weight l) ≤ support.card := by
  let other (l : β) := (adj l).erase p
  have hdisj : (↑lines : Set β).PairwiseDisjoint other := by
    intro l hl k hk hne
    rw [Function.onFun, Finset.disjoint_left]
    intro a hal hak
    obtain ⟨hap, ha⟩ := Finset.mem_erase.mp hal
    exact hap (hunique l hl k hk hne a ha (Finset.mem_erase.mp hak).2)
  have hcontained : lines.biUnion other ⊆ support.erase p := by
    intro a ha
    obtain ⟨l, hl, hla⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨hap, hla⟩ := Finset.mem_erase.mp hla
    exact Finset.mem_erase.mpr ⟨hap, hsub l hl hla⟩
  have hsum : (∑ l ∈ lines, weight l) ≤ (lines.biUnion other).card := by
    rw [Finset.card_biUnion hdisj]
    refine Finset.sum_le_sum (fun l hl => ?_)
    have herase := Finset.card_erase_add_one (hthrough l hl)
    have hlt := hweight l hl
    change weight l ≤ ((adj l).erase p).card
    omega
  have hle := hsum.trans (Finset.card_le_card hcontained)
  have herase := Finset.card_erase_add_one hp
  omega

theorem heavyIncidenceNeighborhood {N : ℕ} {I : Fin N → Fin N → Prop}
    (edges : Finset (Fin N × Fin N)) (hinc : ∀ e ∈ edges, I e.1 e.2)
    (hunique : ∀ p a, p ≠ a → ∃! l, I p l ∧ I a l)
    (readers : Fin N → ℕ)
    (hheavy : ∀ l, (edges.filter (fun e => e.2 = l)).Nonempty →
      24 * max 1 (readers l) < (edges.filter (fun e => e.2 = l)).card)
    (p : Fin N) (hp : p ∈ edges.image Prod.fst) :
    1 + (∑ l ∈ (edges.filter (fun e => e.1 = p)).image Prod.snd,
      24 * max 1 (readers l)) ≤ (edges.image Prod.fst).card := by
  let adj (l : Fin N) := (edges.filter (fun e => e.2 = l)).image Prod.fst
  let lines := (edges.filter (fun e => e.1 = p)).image Prod.snd
  have adj_iff (a l : Fin N) : a ∈ adj l ↔ (a, l) ∈ edges := by
    constructor
    · intro h
      obtain ⟨⟨a', l'⟩, he, ha⟩ := Finset.mem_image.mp h
      obtain ⟨he, hl⟩ := Finset.mem_filter.mp he
      have same : (a', l') = (a, l) := Prod.ext ha hl
      exact same ▸ he
    · intro he
      exact Finset.mem_image.mpr ⟨(a, l), Finset.mem_filter.mpr ⟨he, rfl⟩, rfl⟩
  have through (l : Fin N) (hl : l ∈ lines) : p ∈ adj l := by
    obtain ⟨⟨a, l'⟩, he, hl'⟩ := Finset.mem_image.mp hl
    obtain ⟨he, ha⟩ := Finset.mem_filter.mp he
    have same : (a, l') = (p, l) := Prod.ext ha hl'
    exact (adj_iff p l).mpr (same ▸ he)
  refine weightedNeighborsLeSupport adj lines (edges.image Prod.fst) p
    (fun l => 24 * max 1 (readers l)) hp ?_ through ?_ ?_
  · intro l _ a ha
    exact Finset.mem_image.mpr ⟨(a, l), (adj_iff a l).mp ha, rfl⟩
  · intro l hl k hk hlk a ha hk'
    by_contra! hap
    obtain ⟨j, _, hj⟩ := hunique p a (Ne.symm hap)
    have hl' := hj l ⟨hinc _ ((adj_iff p l).mp (through l hl)), hinc _ ((adj_iff a l).mp ha)⟩
    have hk'' := hj k ⟨hinc _ ((adj_iff p k).mp (through k hk)), hinc _ ((adj_iff a k).mp hk')⟩
    exact hlk (hl'.trans hk''.symm)
  · intro l hl
    have hcard : (adj l).card = (edges.filter (fun e => e.2 = l)).card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb h
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      exact Prod.ext h (ha'.trans hb'.symm)
    rw [hcard]
    exact hheavy l ⟨(p, l), Finset.mem_filter.mpr ⟨(adj_iff p l).mp (through l hl), rfl⟩⟩

theorem noSmallCutOfNonincidentWitnesses {Wire Line : Type*} [DecidableEq Line]
    (cut : Finset Wire) {q : ℕ} (incident : Line → Prop)
    (wireTrue : Wire → Finset Line → Prop) (accepts : Finset Line → Prop)
    (hsize : cut.card ≤ q)
    (hsound : ∀ L : Finset Line, L.card ≤ q → accepts L → ∃ l ∈ L, incident l)
    (hmono : ∀ w, Monotone (wireTrue w))
    (hforces : ∀ L, (∀ w ∈ cut, wireTrue w L) → accepts L) :
    ∃ w ∈ cut, ∀ l, ¬ incident l → ¬ wireTrue w {l} := by
  classical
  by_contra! hmissing
  choose line havoids htrue using hmissing
  let witnesses := cut.attach.image (fun w => line w.val w.property)
  have hwitnesses : witnesses.card ≤ q := by
    exact Finset.card_image_le.trans (by simpa using hsize)
  have haccepts : accepts witnesses := by
    apply hforces
    intro w hw
    apply hmono w _ (htrue w hw)
    exact Finset.singleton_subset_iff.mpr
      (Finset.mem_image.mpr ⟨⟨w, hw⟩, Finset.mem_attach _ _, rfl⟩)
  obtain ⟨l, hl, hI⟩ := hsound witnesses hwitnesses haccepts
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hl
  exact havoids w.val w.property hI

open PEqualNP.CircuitLowerBounds

private def gateValue (wires : List Bool) (gate : Gate) : Bool :=
  gate.op.eval (gate.inputs.map (fun wire => wires.getD wire false))

private def values (gates : List Gate) (inputs : List Bool) : List Bool :=
  gates.foldl (fun wires gate => wires ++ [gateValue wires gate]) inputs

private theorem valuesCons (gate : Gate) (gates : List Gate) (inputs : List Bool) :
    values (gate :: gates) inputs = values gates (inputs ++ [gateValue inputs gate]) := rfl

private theorem valuesPreservePrefix (gates : List Gate) (inputs : List Bool) {i : ℕ}
    (hi : i < inputs.length) : (values gates inputs).getD i false = inputs.getD i false := by
  induction gates generalizing inputs with
  | nil => rfl
  | cons gate gates ih =>
    rw [valuesCons, ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem gateValueMono {gate : Gate} {before after : List Bool}
    (hgate : gate.op = .and ∨ gate.op = .or)
    (hwires : ∀ i ∈ gate.inputs, before.getD i false = true → after.getD i false = true)
    (htrue : gateValue before gate = true) : gateValue after gate = true := by
  rcases hgate with hand | hor
  · simp only [gateValue, hand, GateOp.eval, List.all_eq_true, List.mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, id_eq] at htrue ⊢
    exact fun i hi => hwires i hi (htrue i hi)
  · simp only [gateValue, hor, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at htrue ⊢
    obtain ⟨_, ⟨i, hi, rfl⟩, ht⟩ := htrue
    exact ⟨_, ⟨i, hi, rfl⟩, hwires i hi ht⟩

private theorem appendPreservesTruth {before after : List Bool} (beforeBit afterBit : Bool)
    (hlen : before.length = after.length) {i : ℕ}
    (hinput : before.getD i false = true → after.getD i false = true)
    (hbit : beforeBit = true → afterBit = true) :
    (before ++ [beforeBit]).getD i false = true → (after ++ [afterBit]).getD i false = true := by
  intro ht
  by_cases hbefore : i < before.length
  · have hafter : i < after.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hbefore] at ht
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hafter]
      using hinput (by simpa [List.getD_eq_getElem?_getD] using ht)
  · have hbefore' : before.length ≤ i := by omega
    by_cases hlast : i = before.length
    · subst i
      simpa [List.getD_eq_getElem?_getD, hlen] using
        hbit (by simpa [List.getD_eq_getElem?_getD] using ht)
    · have hidx : [beforeBit].length ≤ i - before.length := by
        simp only [List.length_singleton]
        omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hbefore',
        List.getElem?_eq_none hidx] at ht

private theorem valuesMono (gates : List Gate) (before after : List Bool)
    (hlen : before.length = after.length)
    (hops : ∀ g ∈ gates, g.op = .and ∨ g.op = .or)
    (hinputs : ∀ i, before.getD i false = true → after.getD i false = true) :
    ∀ i, (values gates before).getD i false = true → (values gates after).getD i false = true := by
  induction gates generalizing before after with
  | nil => exact hinputs
  | cons gate gates ih =>
    rw [valuesCons, valuesCons]
    apply ih _ _ (by simp [hlen]) (fun g hg => hops g (by simp [hg]))
    intro i
    exact appendPreservesTruth _ _ hlen (hinputs i)
      (gateValueMono (hops gate (by simp)) (fun w _ => hinputs w))

private theorem valuesPreservedByReaders (gates : List Gate) (v : ℕ) (before after : List Bool)
    (hlen : before.length = after.length) (hv : v < before.length)
    (hops : ∀ g ∈ gates, g.op = .and ∨ g.op = .or)
    (hinputs : ∀ i, i ≠ v → before.getD i false = true → after.getD i false = true)
    (hreaders : ∀ j : Fin gates.length, v ∈ (gates.get j).inputs →
      (values gates before).getD (before.length + j.val) false = true →
      (values gates after).getD (after.length + j.val) false = true) :
    ∀ i, i ≠ v → (values gates before).getD i false = true →
      (values gates after).getD i false = true := by
  induction gates generalizing before after with
  | nil => exact hinputs
  | cons gate gates ih =>
    let beforeStep := before ++ [gateValue before gate]
    let afterStep := after ++ [gateValue after gate]
    have hgate : gateValue before gate = true → gateValue after gate = true := by
      by_cases hreads : v ∈ gate.inputs
      · have hhead := hreaders ⟨0, by simp⟩ hreads
        simp only [Nat.add_zero, valuesCons] at hhead
        rw [valuesPreservePrefix _ _ (by simp), valuesPreservePrefix _ _ (by simp)] at hhead
        simpa [List.getD_eq_getElem?_getD] using hhead
      · exact gateValueMono (hops gate (by simp)) fun i hi =>
          hinputs i (fun hi' => hreads (hi' ▸ hi))
    rw [valuesCons, valuesCons]
    apply ih beforeStep afterStep (by simp [beforeStep, afterStep, hlen])
      (by simp [beforeStep]; omega) (fun g hg => hops g (by simp [hg]))
    · intro i hi
      exact appendPreservesTruth _ _ hlen (hinputs i hi) hgate
    · intro j hj
      have h := hreaders j.succ hj
      simpa only [valuesCons, beforeStep, afterStep, List.length_append, List.length_singleton,
        Fin.val_succ, Nat.add_assoc, Nat.add_comm 1] using h

theorem circuitPreservedByReaders (C : Circuit) (v : ℕ) (before after : List Bool)
    (hlen : before.length = after.length) (hv : v < before.length)
    (hops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (hout : C.output ≠ v)
    (hinputs : ∀ i, i ≠ v → before.getD i false = true → after.getD i false = true)
    (hreaders : ∀ j : Fin C.size, v ∈ (C.gates.get j).inputs →
      (C.wires before).getD (before.length + j.val) false = true →
      (C.wires after).getD (after.length + j.val) false = true) :
    C.eval before = true → C.eval after = true :=
  valuesPreservedByReaders C.gates v before after hlen hv hops hinputs hreaders C.output hout

theorem readerRejectsAllNonincidentSingletons {Line : Type*} [DecidableEq Line]
    (C : Circuit) (v q : ℕ) (before : List Bool) (inputs : Finset Line → List Bool)
    (incident : Line → Prop) (hv : v < before.length)
    (hout : C.output ≠ v) (haccepted : C.eval before = true)
    (hops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (hlen : ∀ L, before.length = (inputs L).length)
    (hprior : ∀ L i, i ≠ v → before.getD i false = true → (inputs L).getD i false = true)
    (hmono : ∀ L L' : Finset Line, L ⊆ L' → ∀ i,
      (inputs L).getD i false = true → (inputs L').getD i false = true)
    (hreadCount : (Finset.univ.filter fun j : Fin C.size => v ∈ (C.gates.get j).inputs).card ≤ q)
    (hsound : ∀ L, L.card ≤ q → C.eval (inputs L) = true → ∃ l ∈ L, incident l) :
    ∃ j : Fin C.size, v ∈ (C.gates.get j).inputs ∧
      (C.wires before).getD (before.length + j.val) false = true ∧
      ∀ l, ¬incident l →
        (C.wires (inputs {l})).getD ((inputs {l}).length + j.val) false ≠ true := by
  classical
  let cut := Finset.univ.filter fun j : Fin C.size => v ∈ (C.gates.get j).inputs ∧
    (C.wires before).getD (before.length + j.val) false = true
  have hcut : cut.card ≤ q := by
    apply le_trans (Finset.card_le_card ?_) hreadCount
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩
  have hwireMono (j : Fin C.size) : Monotone fun L =>
      (C.wires (inputs L)).getD ((inputs L).length + j.val) false = true := by
    intro L L' hL ht
    have hlen' := (hlen L).symm.trans (hlen L')
    rw [← hlen']
    exact valuesMono C.gates _ _ hlen' hops (hmono L L' hL) _ ht
  obtain ⟨j, hj, hbad⟩ := noSmallCutOfNonincidentWitnesses cut incident
    (fun j L => (C.wires (inputs L)).getD ((inputs L).length + j.val) false = true)
    (fun L => C.eval (inputs L) = true) hcut hsound hwireMono (by
      intro L hL
      refine circuitPreservedByReaders C v before (inputs L) (hlen L) hv hops hout (hprior L) ?_
        haccepted
      intro j hj htrue
      exact hL j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, htrue⟩))
  have hmem := (Finset.mem_filter.mp hj).2
  exact ⟨j, hmem.1, hmem.2, hbad⟩

private theorem getDOfFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if hi : i < n then f ⟨i, hi⟩ else false := by
  by_cases hi : i < n <;> simp [List.getD_eq_getElem?_getD, hi]

theorem incidentPairReader {q N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit)
    (p l : Fin N) (hq : 1 ≤ q) (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hsound : ∀ x : Fin (N + N) → Bool,
      Fintype.card {a : Fin N // x (Fin.natAdd N a) = true} ≤ q →
      (¬ ∃ b a, I b a ∧ x (Fin.castAdd N b) = true ∧ x (Fin.natAdd N a) = true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C x = false)
    (hreadCount : (Finset.univ.filter fun j : Fin C.size =>
      (Fin.natAdd N l).val ∈ (C.gates.get j).inputs).card ≤ q) :
    let pair : Fin (N + N) → Bool := fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
    PEqualNP.MetaComplexity.circuitFun (N + N) C pair = true →
    ∃ j : Fin C.size, (Fin.natAdd N l).val ∈ (C.gates.get j).inputs ∧
      (C.wires (List.ofFn pair)).getD (N + N + j.val) false = true ∧
      ∀ a, ¬I p a → (C.wires (List.ofFn (fun i : Fin (N + N) =>
        decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N a)))).getD (N + N + j.val) false = false := by
  classical
  intro pair haccepted
  let alternate (L : Finset (Fin N)) (i : Fin (N + N)) : Bool :=
    decide (i = Fin.castAdd N p ∨ ∃ a ∈ L, i = Fin.natAdd N a)
  have splitInputs (b a : Fin N) : Fin.castAdd N b ≠ Fin.natAdd N a := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    have hb := b.isLt
    omega
  have lInjective : Function.Injective (Fin.natAdd N : Fin N → Fin (N + N)) := by
    intro a b h
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val h)
  have hrow (L : Finset (Fin N)) (a : Fin N) : alternate L (Fin.natAdd N a) = true ↔ a ∈ L := by
    simp only [alternate, decide_eq_true_eq, Ne.symm (splitInputs p a), false_or, lInjective.eq_iff]
    exact ⟨fun ⟨b, hb, he⟩ => he.symm ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩
  have hcol (L : Finset (Fin N)) (b : Fin N) : alternate L (Fin.castAdd N b) = true → b = p := by
    simp only [alternate, decide_eq_true_eq]
    rintro (hb | ⟨a, _, ha⟩)
    · exact Fin.ext (congrArg (fun i : Fin (N + N) => i.val) hb)
    · exact (splitInputs b a ha).elim
  have hout : C.output ≠ (Fin.natAdd N l).val := by
    intro h
    let justLine : Fin (N + N) → Bool := fun i => decide (i = Fin.natAdd N l)
    have hn : Fintype.card {a : Fin N // justLine (Fin.natAdd N a) = true} ≤ q := by
      rw [Fintype.card_of_subtype {l} (fun a => by simp [justLine])]
      simpa using hq
    have hs := hsound justLine hn (by
      rintro ⟨b, a, _, hb, _⟩
      exact splitInputs b l (of_decide_eq_true hb))
    change (values C.gates (List.ofFn justLine)).getD C.output false = false at hs
    have hlist : (Fin.natAdd N l).val < (List.ofFn justLine).length := by simp
    rw [h, valuesPreservePrefix C.gates _ hlist, getDOfFn] at hs
    rw [dite_eq_left (Fin.natAdd N l).isLt] at hs
    have htrue : justLine ⟨(Fin.natAdd N l).val, (Fin.natAdd N l).isLt⟩ = true := by
      exact decide_eq_true (Fin.ext rfl)
    exact Bool.noConfusion (htrue.symm.trans hs)
  obtain ⟨j, hj, ht, hreject⟩ := readerRejectsAllNonincidentSingletons C (Fin.natAdd N l).val q
    (List.ofFn pair) (fun L => List.ofFn (alternate L)) (I p)
    (by simp) hout haccepted hAO.1
    (fun L => by simp) (by
      intro L i hi ht
      simp only [getDOfFn] at ht ⊢
      split_ifs at ht ⊢ with hbound
      · simp only [pair, decide_eq_true_eq] at ht
        rcases ht with hp | hl
        · simp [alternate, hp]
        · exact (hi (congrArg Fin.val hl)).elim) (by
      intro L L' hsub i ht
      simp only [getDOfFn] at ht ⊢
      split_ifs at ht ⊢
      · simp only [alternate, decide_eq_true_eq] at ht ⊢
        exact ht.elim Or.inl (fun ⟨a, ha, he⟩ => Or.inr ⟨a, hsub ha, he⟩)) hreadCount (by
      intro L hn ht
      by_contra! hno
      have hcard := Fintype.card_of_subtype L (fun a => (hrow L a).symm)
      have hfalse := hsound (alternate L) (by rw [hcard]; exact hn) (by
        rintro ⟨b, a, hab, hb, ha⟩
        have hbp := hcol L b hb
        exact hno a ((hrow L a).mp ha) (hbp ▸ hab))
      change C.eval (List.ofFn (alternate L)) = false at hfalse
      exact Bool.noConfusion (ht.symm.trans hfalse))
  refine ⟨j, hj, by simpa using ht, ?_⟩
  intro a ha
  have heq : alternate {a} = (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N a)) := by
    funext i
    simp [alternate]
  have h := Bool.eq_false_iff.mpr (hreject a ha)
  rw [heq] at h
  simpa only [List.length_ofFn] using h

theorem heavyLineReadCount {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (C : Circuit) (edges : Finset (Fin N × Fin N)) (p l : Fin N) (he : (p, l) ∈ edges)
    (hinc : ∀ e ∈ edges, I e.1 e.2)
    (hline : ∀ a, Fintype.card {b // I b a} = q + 1)
    (hheavy : ∀ v : Fin (N + N),
      let degree := (edges.filter (fun e => v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2)).card
      0 < degree → 24 * max 1 (Fintype.card {j : Fin C.size // v.val ∈ (C.gates.get j).inputs}) < degree) :
    24 * (Finset.univ.filter fun j : Fin C.size =>
      (Fin.natAdd N l).val ∈ (C.gates.get j).inputs).card ≤ q := by
  classical
  let fiber := edges.filter (fun e => e.2 = l)
  have hfiber : edges.filter (fun e => Fin.natAdd N l = Fin.castAdd N e.1 ∨
      Fin.natAdd N l = Fin.natAdd N e.2) = fiber := by
    ext e
    have hdisjoint : Fin.natAdd N l ≠ Fin.castAdd N e.1 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      have he := e.1.isLt
      omega
    simp only [fiber, Finset.mem_filter, hdisjoint, false_or]
    constructor
    · rintro ⟨he, hl⟩
      exact ⟨he, Fin.ext (Nat.add_left_cancel (congrArg Fin.val hl.symm))⟩
    · rintro ⟨he, hl⟩
      exact ⟨he, congrArg (Fin.natAdd N) hl.symm⟩
  have hnonempty : 0 < fiber.card :=
    Finset.card_pos.mpr ⟨(p, l), Finset.mem_filter.mpr ⟨he, rfl⟩⟩
  have hcard : fiber.card ≤ q + 1 := by
    have hproj : (fiber.image Prod.fst).card = fiber.card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb hh
      exact Prod.ext hh ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    have hsub : fiber.image Prod.fst ⊆ Finset.univ.filter (fun b => I b l) := by
      intro b hb
      obtain ⟨e, hmem, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨hm, heq⟩ := Finset.mem_filter.mp hmem
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq ▸ hinc e hm⟩
    have h := Finset.card_le_card hsub
    have hline' := hline l
    rw [Fintype.card_subtype] at hline'
    rw [hproj, hline'] at h
    exact h
  have hread := hheavy (Fin.natAdd N l)
  dsimp only at hread
  rw [hfiber] at hread
  have hlt := hread hnonempty
  rw [Fintype.card_subtype] at hlt
  have hmax := le_max_right 1
    (Finset.univ.filter fun j : Fin C.size => (Fin.natAdd N l).val ∈ (C.gates.get j).inputs).card
  omega

theorem heavyAcceptedEdgeHasReader {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (C : Circuit) (edges : Finset (Fin N × Fin N))
    (hq : 1 ≤ q) (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hline : ∀ a, Fintype.card {b // I b a} = q + 1)
    (hinc : ∀ e ∈ edges, I e.1 e.2)
    (hheavy : ∀ v : Fin (N + N),
      let degree := (edges.filter (fun e => v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2)).card
      0 < degree → 24 * max 1 (Fintype.card {j : Fin C.size // v.val ∈ (C.gates.get j).inputs}) < degree)
    (hsound : ∀ x : Fin (N + N) → Bool,
      Fintype.card {a : Fin N // x (Fin.natAdd N a) = true} ≤ q →
      (¬ ∃ b a, I b a ∧ x (Fin.castAdd N b) = true ∧ x (Fin.natAdd N a) = true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C x = false)
    (p l : Fin N) (he : (p, l) ∈ edges) :
    let pair : Fin (N + N) → Bool := fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
    PEqualNP.MetaComplexity.circuitFun (N + N) C pair = true →
    ∃ j : Fin C.size, (Fin.natAdd N l).val ∈ (C.gates.get j).inputs ∧
      (C.wires (List.ofFn pair)).getD (N + N + j.val) false = true ∧
      ∀ a, ¬I p a → (C.wires (List.ofFn (fun i : Fin (N + N) =>
        decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N a)))).getD (N + N + j.val) false = false := by
  have hread := heavyLineReadCount C edges p l he hinc hline hheavy
  exact incidentPairReader I C p l hq hAO hsound (by omega)

end PEqualNP.Outside.L_meta_3698
