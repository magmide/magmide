```
map_disjoint_sym: ∀ (K: Type) (M: Type → Type) (H0: ∀ A: Type, Lookup K A (M A)) (A: Type), Symmetric (map_disjoint: relation (M A))
map_disjoint_weaken_l: ∀ (K: Type) (M: Type → Type) (H0: ∀ A: Type, Lookup K A (M A)) (A: Type) (m1 m1' m2: M A), m1' ##ₘ m2 → m1 ⊆ m1' → m1 ##ₘ m2
map_disjoint_weaken_r: ∀ (K: Type) (M: Type → Type) (H0: ∀ A: Type, Lookup K A (M A)) (A: Type) (m1 m2 m2': M A), m1 ##ₘ m2' → m2 ⊆ m2' → m1 ##ₘ m2
map_disjoint_weaken: ∀ (K: Type) (M: Type → Type) (H0: ∀ A: Type, Lookup K A (M A)) (A: Type) (m1 m1' m2 m2': M A), m1' ##ₘ m2' → m1 ⊆ m1' → m2 ⊆ m2' → m1 ##ₘ m2
map_disjoint_Some_r: ∀ (K: Type) (M: Type → Type) (H0: ∀ A: Type, Lookup K A (M A)) (A: Type) (m1 m2: M A) (i: K) (x: A), m1 ##ₘ m2 → m2 !! i = Some x → m1 !! i = None
map_disjoint_Some_l: ∀ (K: Type) (M: Type → Type) (H0: ∀ A: Type, Lookup K A (M A)) (A: Type) (m1 m2: M A) (i: K) (x: A), m1 ##ₘ m2 → m1 !! i = Some x → m2 !! i = None
map_disjoint_proper: ∀ (K: Type) (M: Type → Type) (H0: ∀ A: Type, Lookup K A (M A)) (A: Type) (H7: Equiv A), Proper (equiv ==> equiv ==> iff) map_disjoint
map_disjoint_alt: ∀ (K: Type) (M: Type → Type) (H0: ∀ A: Type, Lookup K A (M A)) (A: Type) (m1 m2: M A), m1 ##ₘ m2 ↔ (∀ i: K, m1 !! i = None ∨ m2 !! i = None)
map_disjoint_spec:
  ∀ (K: Type) (M: Type → Type) (H0: ∀ A: Type, Lookup K A (M A)) (A: Type) (m1 m2: M A), m1 ##ₘ m2 ↔ (∀ (i: K) (x y: A), m1 !! i = Some x → m2 !! i = Some y → False)
map_disjoint_empty_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K), FinMap K M → ∀ (A: Type) (m: M A), m ##ₘ ∅
map_disjoint_empty_l:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K), FinMap K M → ∀ (A: Type) (m: M A), ∅ ##ₘ m
map_disjoint_delete_l:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2: M A) (i: K), m1 ##ₘ m2 → delete i m1 ##ₘ m2
map_disjoint_delete_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2: M A) (i: K), m1 ##ₘ m2 → m1 ##ₘ delete i m2
map_union_comm:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K), FinMap K M → ∀ (A: Type) (m1 m2: M A), m1 ##ₘ m2 → m1 ∪ m2 = m2 ∪ m1
map_disjoint_difference_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K), FinMap K M → ∀ (A: Type) (m1 m2: M A), m1 ⊆ m2 → m1 ##ₘ m2 ∖ m1
map_disjoint_difference_l:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K), FinMap K M → ∀ (A: Type) (m1 m2: M A), m1 ⊆ m2 → m2 ∖ m1 ##ₘ m1
map_union_subseteq_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K), FinMap K M → ∀ (A: Type) (m1 m2: M A), m1 ##ₘ m2 → m2 ⊆ m1 ∪ m2
map_disjoint_union_l_2:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2 m3: M A), m1 ##ₘ m3 → m2 ##ₘ m3 → m1 ∪ m2 ##ₘ m3
map_disjoint_union_r_2:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2 m3: M A), m1 ##ₘ m2 → m1 ##ₘ m3 → m1 ##ₘ m2 ∪ m3
map_disjoint_fmap:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A B: Type) (f1 f2: A → B) (m1 m2: M A), m1 ##ₘ m2 ↔ f1 <$> m1 ##ₘ f2 <$> m2
map_disjoint_omap:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A B: Type) (f1 f2: A → option B) (m1 m2: M A), m1 ##ₘ m2 → omap f1 m1 ##ₘ omap f2 m2
map_disjoint_union_list_l_2:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (ms: list (M A)) (m: M A), Forall (λ m2: M A, m2 ##ₘ m) ms → ⋃ ms ##ₘ m
map_disjoint_union_list_r_2:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (ms: list (M A)) (m: M A), Forall (λ m2: M A, m2 ##ₘ m) ms → m ##ₘ ⋃ ms
map_disjoint_union_l:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2 m3: M A), m1 ∪ m2 ##ₘ m3 ↔ m1 ##ₘ m3 ∧ m2 ##ₘ m3
map_disjoint_union_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2 m3: M A), m1 ##ₘ m2 ∪ m3 ↔ m1 ##ₘ m2 ∧ m1 ##ₘ m3
map_disjoint_foldr_delete_l:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2: M A) (is: list K), m1 ##ₘ m2 → foldr delete m1 is ##ₘ m2
map_disjoint_foldr_delete_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2: M A) (is: list K), m1 ##ₘ m2 → m1 ##ₘ foldr delete m2 is
map_disjoint_union_list_l:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (ms: list (M A)) (m: M A), ⋃ ms ##ₘ m ↔ Forall (λ m2: M A, m2 ##ₘ m) ms
map_disjoint_union_list_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (ms: list (M A)) (m: M A), m ##ₘ ⋃ ms ↔ Forall (λ m2: M A, m2 ##ₘ m) ms
map_Forall_union_1_2:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2: M A) (P: K → A → Prop), m1 ##ₘ m2 → map_Forall P (m1 ∪ m2) → map_Forall P m2
map_union_subseteq_r':
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K), FinMap K M → ∀ (A: Type) (m1 m2 m3: M A), m2 ##ₘ m3 → m1 ⊆ m3 → m1 ⊆ m2 ∪ m3
map_disjoint_singleton_l_2:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m: M A) (i: K) (x: A), m !! i = None → {[i := x]} ##ₘ m
map_disjoint_singleton_r_2:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m: M A) (i: K) (x: A), m !! i = None → m ##ₘ {[i := x]}
map_union_cancel_l:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2 m3: M A), m1 ##ₘ m3 → m2 ##ₘ m3 → m3 ∪ m1 = m3 ∪ m2 → m1 = m2
map_union_cancel_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2 m3: M A), m1 ##ₘ m3 → m2 ##ₘ m3 → m1 ∪ m3 = m2 ∪ m3 → m1 = m2
map_disjoint_singleton_l:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m: M A) (i: K) (x: A), {[i := x]} ##ₘ m ↔ m !! i = None
map_disjoint_singleton_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m: M A) (i: K) (x: A), m ##ₘ {[i := x]} ↔ m !! i = None
map_seq_app_disjoint:
  ∀ (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup nat A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter nat A (M A)) (H3: OMap M)
    (H4: Merge M) (H5: ∀ A: Type, FinMapToList nat A (M A)) (EqDecision0: EqDecision nat),
    FinMap nat M → ∀ (A: Type) (start: nat) (xs1 xs2: list A), map_seq start xs1 ##ₘ map_seq (start + length xs1) xs2
map_union_mono_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2 m3: M A), m2 ##ₘ m3 → m1 ⊆ m2 → m1 ∪ m3 ⊆ m2 ∪ m3
map_disjoint_insert_l_2:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2: M A) (i: K) (x: A), m2 !! i = None → m1 ##ₘ m2 → <[i:=x]> m1 ##ₘ m2
map_disjoint_insert_r_2:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2: M A) (i: K) (x: A), m1 !! i = None → m1 ##ₘ m2 → m1 ##ₘ <[i:=x]> m2
map_omap_union:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A B: Type) (f: A → option B) (m1 m2: M A), m1 ##ₘ m2 → omap f (m1 ∪ m2) = omap f m1 ∪ omap f m2
map_Forall_union:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2: M A) (P: K → A → Prop), m1 ##ₘ m2 → map_Forall P (m1 ∪ m2) ↔ map_Forall P m1 ∧ map_Forall P m2
lookup_union_Some_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2: M A) (i: K) (x: A), m1 ##ₘ m2 → m2 !! i = Some x → (m1 ∪ m2) !! i = Some x
map_union_reflecting_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2 m3: M A), m1 ##ₘ m3 → m2 ##ₘ m3 → m1 ∪ m3 ⊆ m2 ∪ m3 → m1 ⊆ m2
map_union_reflecting_l:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2 m3: M A), m3 ##ₘ m1 → m3 ##ₘ m2 → m3 ∪ m1 ⊆ m3 ∪ m2 → m1 ⊆ m2
map_disjoint_insert_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2: M A) (i: K) (x: A), m1 ##ₘ <[i:=x]> m2 ↔ m1 !! i = None ∧ m1 ##ₘ m2
map_disjoint_insert_l:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2: M A) (i: K) (x: A), <[i:=x]> m1 ##ₘ m2 ↔ m2 !! i = None ∧ m1 ##ₘ m2
map_size_disj_union:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2: M A), m1 ##ₘ m2 → base.size (m1 ∪ m2) = base.size m1 + base.size m2
map_not_disjoint:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2: M A), ¬ m1 ##ₘ m2 ↔ (∃ (i: K) (x1 x2: A), m1 !! i = Some x1 ∧ m2 !! i = Some x2)
map_disjoint_list_to_map_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m: M A) (ixs: list (K * A)), m ##ₘ list_to_map ixs ↔ Forall (λ ix: K * A, m !! ix.1 = None) ixs
map_disjoint_list_to_map_l:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m: M A) (ixs: list (K * A)), list_to_map ixs ##ₘ m ↔ Forall (λ ix: K * A, m !! ix.1 = None) ixs
map_disjoint_dom_2:
  ∀ (K: Type) (M: Type → Type) (D: Type) (H: ∀ A: Type, Dom (M A) D) (H0: FMap M) (H1: ∀ A: Type, Lookup K A (M A)) (H2: ∀ A: Type, Empty (M A))
    (H3: ∀ A: Type, PartialAlter K A (M A)) (H4: OMap M) (H5: Merge M) (H6: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K) (H7: ElemOf K D)
    (H8: Empty D) (H9: Singleton K D) (H10: Union D) (H11: Intersection D) (H12: Difference D), FinMapDom K M D → ∀ (A: Type) (m1 m2: M A), dom D m1 ## dom D m2 → m1 ##ₘ m2
map_disjoint_dom_1:
  ∀ (K: Type) (M: Type → Type) (D: Type) (H: ∀ A: Type, Dom (M A) D) (H0: FMap M) (H1: ∀ A: Type, Lookup K A (M A)) (H2: ∀ A: Type, Empty (M A))
    (H3: ∀ A: Type, PartialAlter K A (M A)) (H4: OMap M) (H5: Merge M) (H6: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K) (H7: ElemOf K D)
    (H8: Empty D) (H9: Singleton K D) (H10: Union D) (H11: Intersection D) (H12: Difference D), FinMapDom K M D → ∀ (A: Type) (m1 m2: M A), m1 ##ₘ m2 → dom D m1 ## dom D m2
lookup_union_Some:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m1 m2: M A) (i: K) (x: A), m1 ##ₘ m2 → (m1 ∪ m2) !! i = Some x ↔ m1 !! i = Some x ∨ m2 !! i = Some x
map_disjoint_dom:
  ∀ (K: Type) (M: Type → Type) (D: Type) (H: ∀ A: Type, Dom (M A) D) (H0: FMap M) (H1: ∀ A: Type, Lookup K A (M A)) (H2: ∀ A: Type, Empty (M A))
    (H3: ∀ A: Type, PartialAlter K A (M A)) (H4: OMap M) (H5: Merge M) (H6: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K) (H7: ElemOf K D)
    (H8: Empty D) (H9: Singleton K D) (H10: Union D) (H11: Intersection D) (H12: Difference D), FinMapDom K M D → ∀ (A: Type) (m1 m2: M A), m1 ##ₘ m2 ↔ dom D m1 ## dom D m2
map_disjoint_filter:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (P: K * A → Prop) (H7: ∀ x: K * A, Decision (P x)) (m1 m2: M A), m1 ##ₘ m2 → filter P m1 ##ₘ filter P m2
map_disjoint_list_to_map_zip_l_2:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m: M A) (is: list K) (xs: list A), length is = length xs → Forall (λ i: K, m !! i = None) is → list_to_map (zip is xs) ##ₘ m
map_disjoint_list_to_map_zip_r_2:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m: M A) (is: list K) (xs: list A), length is = length xs → Forall (λ i: K, m !! i = None) is → m ##ₘ list_to_map (zip is xs)
map_disjoint_list_to_map_zip_l:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m: M A) (is: list K) (xs: list A), length is = length xs → list_to_map (zip is xs) ##ₘ m ↔ Forall (λ i: K, m !! i = None) is
map_disjoint_list_to_map_zip_r:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (m: M A) (is: list K) (xs: list A), length is = length xs → m ##ₘ list_to_map (zip is xs) ↔ Forall (λ i: K, m !! i = None) is
map_disjoint_filter_complement:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (P: K * A → Prop) (H7: ∀ x: K * A, Decision (P x)) (m: M A), filter P m ##ₘ filter (λ v: K * A, ¬ P v) m
map_disjoint_kmap:
  ∀ (K1: Type) (M1: Type → Type) (H: FMap M1) (H0: ∀ A: Type, Lookup K1 A (M1 A)) (H1: ∀ A: Type, Empty (M1 A)) (H2: ∀ A: Type, PartialAlter K1 A (M1 A))
    (H3: OMap M1) (H4: Merge M1) (H5: ∀ A: Type, FinMapToList K1 A (M1 A)) (EqDecision0: EqDecision K1),
    FinMap K1 M1
    → ∀ (K2: Type) (M2: Type → Type) (H7: FMap M2) (H8: ∀ A: Type, Lookup K2 A (M2 A)) (H9: ∀ A: Type, Empty (M2 A)) (H10: ∀ A: Type, PartialAlter K2 A (M2 A))
        (H11: OMap M2) (H12: Merge M2) (H13: ∀ A: Type, FinMapToList K2 A (M2 A)) (EqDecision1: EqDecision K2),
        FinMap K2 M2 → ∀ f: K1 → K2, Inj eq eq f → ∀ (A: Type) (m1 m2: M1 A), kmap f m1 ##ₘ kmap f m2 ↔ m1 ##ₘ m2
map_filter_union:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M → ∀ (A: Type) (P: K * A → Prop) (H7: ∀ x: K * A, Decision (P x)) (m1 m2: M A), m1 ##ₘ m2 → filter P (m1 ∪ m2) = filter P m1 ∪ filter P m2
dom_union_inv_L:
  ∀ (K: Type) (M: Type → Type) (D: Type) (H: ∀ A: Type, Dom (M A) D) (H0: FMap M) (H1: ∀ A: Type, Lookup K A (M A)) (H2: ∀ A: Type, Empty (M A))
    (H3: ∀ A: Type, PartialAlter K A (M A)) (H4: OMap M) (H5: Merge M) (H6: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K) (H7: ElemOf K D)
    (H8: Empty D) (H9: Singleton K D) (H10: Union D) (H11: Intersection D) (H12: Difference D),
    FinMapDom K M D
    → LeibnizEquiv D → RelDecision elem_of → ∀ (A: Type) (m: M A) (X1 X2: D), X1 ## X2 → dom D m = X1 ∪ X2 → ∃ m1 m2: M A, m = m1 ∪ m2 ∧ m1 ##ₘ m2 ∧ dom D m1 = X1 ∧ dom D m2 = X2
map_cross_split:
  ∀ (K: Type) (M: Type → Type) (H: FMap M) (H0: ∀ A: Type, Lookup K A (M A)) (H1: ∀ A: Type, Empty (M A)) (H2: ∀ A: Type, PartialAlter K A (M A))
    (H3: OMap M) (H4: Merge M) (H5: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K),
    FinMap K M
    → ∀ (A: Type) (ma mb mc md: M A),
        ma ##ₘ mb
        → mc ##ₘ md
          → ma ∪ mb = mc ∪ md → ∃ mac mad mbc mbd: M A, mac ##ₘ mad ∧ mbc ##ₘ mbd ∧ mac ##ₘ mbc ∧ mad ##ₘ mbd ∧ mac ∪ mad = ma ∧ mbc ∪ mbd = mb ∧ mac ∪ mbc = mc ∧ mad ∪ mbd = md
dom_union_inv:
  ∀ (K: Type) (M: Type → Type) (D: Type) (H: ∀ A: Type, Dom (M A) D) (H0: FMap M) (H1: ∀ A: Type, Lookup K A (M A)) (H2: ∀ A: Type, Empty (M A))
    (H3: ∀ A: Type, PartialAlter K A (M A)) (H4: OMap M) (H5: Merge M) (H6: ∀ A: Type, FinMapToList K A (M A)) (EqDecision0: EqDecision K) (H7: ElemOf K D)
    (H8: Empty D) (H9: Singleton K D) (H10: Union D) (H11: Intersection D) (H12: Difference D),
    FinMapDom K M D → RelDecision elem_of → ∀ (A: Type) (m: M A) (X1 X2: D), X1 ## X2 → dom D m ≡ X1 ∪ X2 → ∃ m1 m2: M A, m = m1 ∪ m2 ∧ m1 ##ₘ m2 ∧ dom D m1 ≡ X1 ∧ dom D m2 ≡ X2





H0: registers s1 ##ₘ registers s2 ∪ registers s3
map_union_assoc:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ A : Type, Assoc eq union
map_union_idemp:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ A : Type, IdemP eq union
H: program_counter s1 ##ₘ program_counter s2 ∪ program_counter s3
map_union_empty:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ A : Type, RightId eq ∅ union
map_empty_union:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ A : Type, LeftId eq ∅ union
map_union_subseteq_l:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ (A : Type) (m1 m2 : M A), m1 ⊆ m1 ∪ m2
map_subseteq_union:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ (A : Type) (m1 m2 : M A), m1 ⊆ m2 → m1 ∪ m2 = m2
map_union_comm:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ (A : Type) (m1 m2 : M A), m1 ##ₘ m2 → m1 ∪ m2 = m2 ∪ m1
map_union_subseteq_r:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ (A : Type) (m1 m2 : M A), m1 ##ₘ m2 → m2 ⊆ m1 ∪ m2
map_positive_l:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ (A : Type) (m1 m2 : M A), m1 ∪ m2 = ∅ → m1 = ∅
map_disjoint_union_l_2:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 m3 : M A), m1 ##ₘ m3 → m2 ##ₘ m3 → m1 ∪ m2 ##ₘ m3
map_disjoint_union_r_2:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 m3 : M A), m1 ##ₘ m2 → m1 ##ₘ m3 → m1 ##ₘ m2 ∪ m3
map_Forall_union_1_1:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (P : K → A → Prop), map_Forall P (m1 ∪ m2) → map_Forall P m1
map_union_subseteq_l':
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ (A : Type) (m1 m2 m3 : M A), m1 ⊆ m2 → m1 ⊆ m2 ∪ m3
map_positive_l_alt:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ (A : Type) (m1 m2 : M A), m1 ≠ ∅ → m1 ∪ m2 ≠ ∅
map_disjoint_union_list_l_2:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (ms : list (M A)) (m : M A), Forall (λ m2 : M A, m2 ##ₘ m) ms → ⋃ ms ##ₘ m
map_disjoint_union_list_r_2:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (ms : list (M A)) (m : M A), Forall (λ m2 : M A, m2 ##ₘ m) ms → m ##ₘ ⋃ ms
map_disjoint_union_r:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 m3 : M A), m1 ##ₘ m2 ∪ m3 ↔ m1 ##ₘ m2 ∧ m1 ##ₘ m3
map_disjoint_union_l:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 m3 : M A), m1 ∪ m2 ##ₘ m3 ↔ m1 ##ₘ m3 ∧ m2 ##ₘ m3
map_disjoint_union_list_l:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (ms : list (M A)) (m : M A), ⋃ ms ##ₘ m ↔ Forall (λ m2 : M A, m2 ##ₘ m) ms
map_disjoint_union_list_r:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (ms : list (M A)) (m : M A), m ##ₘ ⋃ ms ↔ Forall (λ m2 : M A, m2 ##ₘ m) ms
map_difference_union:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ (A : Type) (m1 m2 : M A), m1 ⊆ m2 → m1 ∪ m2 ∖ m1 = m2
map_Forall_union_1_2:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (P : K → A → Prop), m1 ##ₘ m2 → map_Forall P (m1 ∪ m2) → map_Forall P m2
map_Forall_union_2:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (P : K → A → Prop), map_Forall P m1 → map_Forall P m2 → map_Forall P (m1 ∪ m2)
map_union_mono_l:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ (A : Type) (m1 m2 m3 : M A), m1 ⊆ m2 → m3 ∪ m1 ⊆ m3 ∪ m2
map_fmap_union:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A B : Type) (f : A → B) (m1 m2 : M A), f <$> m1 ∪ m2 = (f <$> m1) ∪ (f <$> m2)
map_union_subseteq_r':
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ (A : Type) (m1 m2 m3 : M A), m2 ##ₘ m3 → m1 ⊆ m3 → m1 ⊆ m2 ∪ m3
map_union_least:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K), FinMap K M → ∀ (A : Type) (m1 m2 m3 : M A), m1 ⊆ m3 → m2 ⊆ m3 → m1 ∪ m2 ⊆ m3
map_union_cancel_l:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 m3 : M A), m1 ##ₘ m3 → m2 ##ₘ m3 → m3 ∪ m1 = m3 ∪ m2 → m1 = m2
map_union_cancel_r:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 m3 : M A), m1 ##ₘ m3 → m2 ##ₘ m3 → m1 ∪ m3 = m2 ∪ m3 → m1 = m2
lookup_union_l:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K), is_Some (m1 !! i) → (m1 ∪ m2) !! i = m1 !! i
lookup_union_Some_l:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K) (x : A), m1 !! i = Some x → (m1 ∪ m2) !! i = Some x
insert_union_singleton_l:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m : M A) (i : K) (x : A), <[i:=x]> m = {[i := x]} ∪ m
map_union_mono_r:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 m3 : M A), m2 ##ₘ m3 → m1 ⊆ m2 → m1 ∪ m3 ⊆ m2 ∪ m3
lookup_union_r:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K), m1 !! i = None → (m1 ∪ m2) !! i = m2 !! i
lookup_union_is_Some:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K), is_Some ((m1 ∪ m2) !! i) ↔ is_Some (m1 !! i) ∨ is_Some (m2 !! i)
map_omap_union:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A B : Type) (f : A → option B) (m1 m2 : M A), m1 ##ₘ m2 → omap f (m1 ∪ m2) = omap f m1 ∪ omap f m2
insert_union_l:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K) (x : A), <[i:=x]> (m1 ∪ m2) = <[i:=x]> m1 ∪ m2
union_singleton_r:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m : M A) (i : K) (x y : A), m !! i = Some x → m ∪ {[i := y]} = m
map_Forall_union:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (P : K → A → Prop), m1 ##ₘ m2 → map_Forall P (m1 ∪ m2) ↔ map_Forall P m1 ∧ map_Forall P m2
lookup_union_Some_r:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K) (x : A), m1 ##ₘ m2 → m2 !! i = Some x → (m1 ∪ m2) !! i = Some x
map_union_reflecting_r:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 m3 : M A), m1 ##ₘ m3 → m2 ##ₘ m3 → m1 ∪ m3 ⊆ m2 ∪ m3 → m1 ⊆ m2
map_union_reflecting_l:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 m3 : M A), m3 ##ₘ m1 → m3 ##ₘ m2 → m3 ∪ m1 ⊆ m3 ∪ m2 → m1 ⊆ m2
lookup_union:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K), (m1 ∪ m2) !! i = union_with (λ x _ : A, Some x) (m1 !! i) (m2 !! i)
delete_union:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K), delete i (m1 ∪ m2) = delete i m1 ∪ delete i m2
map_size_disj_union:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A), m1 ##ₘ m2 → base.size (m1 ∪ m2) = base.size m1 + base.size m2
union_proper:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (H7 : Equiv A), Proper (equiv ==> equiv ==> equiv) union
lookup_union_Some_inv_r:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K) (x : A), (m1 ∪ m2) !! i = Some x → m1 !! i = None → m2 !! i = Some x
lookup_union_Some_inv_l:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K) (x : A), (m1 ∪ m2) !! i = Some x → m2 !! i = None → m1 !! i = Some x
lookup_union_None:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K), (m1 ∪ m2) !! i = None ↔ m1 !! i = None ∧ m2 !! i = None
insert_union_singleton_r:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m : M A) (i : K) (x : A), m !! i = None → <[i:=x]> m = m ∪ {[i := x]}
list_to_map_app:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (l1 l2 : list (K * A)), list_to_map (l1 ++ l2) = list_to_map l1 ∪ list_to_map l2
insert_union_r:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K) (x : A), m1 !! i = None → <[i:=x]> (m1 ∪ m2) = m1 ∪ <[i:=x]> m2
foldr_insert_union:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m : M A) (l : list (K * A)), foldr (λ p : K * A, <[p.1:=p.2]>) m l = list_to_map l ∪ m
map_seq_app:
  ∀ (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup nat A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter nat A (M A)) (H3 : OMap M)
    (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList nat A (M A)) (EqDecision0 : EqDecision nat),
    FinMap nat M → ∀ (A : Type) (start : nat) (xs1 xs2 : list A), map_seq start (xs1 ++ xs2) = map_seq start xs1 ∪ map_seq (start + length xs1) xs2
lookup_union_Some:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K) (x : A), m1 ##ₘ m2 → (m1 ∪ m2) !! i = Some x ↔ m1 !! i = Some x ∨ m2 !! i = Some x
union_delete_insert:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K) (x : A), m1 !! i = Some x → delete i m1 ∪ <[i:=x]> m2 = m1 ∪ m2
foldr_delete_union:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (is : list K), foldr delete (m1 ∪ m2) is = foldr delete m1 is ∪ foldr delete m2 is
lookup_union_Some_raw:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K) (x : A), (m1 ∪ m2) !! i = Some x ↔ m1 !! i = Some x ∨ m1 !! i = None ∧ m2 !! i = Some x
dom_union:
  ∀ (K : Type) (M : Type → Type) (D : Type) (H : ∀ A : Type, Dom (M A) D) (H0 : FMap M) (H1 : ∀ A : Type, Lookup K A (M A)) (H2 : ∀ A : Type, Empty (M A))
    (H3 : ∀ A : Type, PartialAlter K A (M A)) (H4 : OMap M) (H5 : Merge M) (H6 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K) (H7 : ElemOf K D)
    (H8 : Empty D) (H9 : Singleton K D) (H10 : Union D) (H11 : Intersection D) (H12 : Difference D),
    FinMapDom K M D → ∀ (A : Type) (m1 m2 : M A), dom D (m1 ∪ m2) ≡ dom D m1 ∪ dom D m2
dom_union_L:
  ∀ (K : Type) (M : Type → Type) (D : Type) (H : ∀ A : Type, Dom (M A) D) (H0 : FMap M) (H1 : ∀ A : Type, Lookup K A (M A)) (H2 : ∀ A : Type, Empty (M A))
    (H3 : ∀ A : Type, PartialAlter K A (M A)) (H4 : OMap M) (H5 : Merge M) (H6 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K) (H7 : ElemOf K D)
    (H8 : Empty D) (H9 : Singleton K D) (H10 : Union D) (H11 : Intersection D) (H12 : Difference D),
    FinMapDom K M D → LeibnizEquiv D → ∀ (A : Type) (m1 m2 : M A), dom D (m1 ∪ m2) = dom D m1 ∪ dom D m2
map_union_equiv_eq:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (H7 : Equiv A), Equivalence equiv → ∀ m1 m2a m2b : M A, m1 ≡ m2a ∪ m2b ↔ (∃ m2a' m2b' : M A, m1 = m2a' ∪ m2b' ∧ m2a' ≡ m2a ∧ m2b' ≡ m2b)
union_insert_delete:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A) (i : K) (x : A), m1 !! i = None → m2 !! i = Some x → <[i:=x]> m1 ∪ delete i m2 = m1 ∪ m2
map_filter_union_complement:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (P : K * A → Prop) (H7 : ∀ x : K * A, Decision (P x)) (m : M A), filter P m ∪ filter (λ v : K * A, ¬ P v) m = m
set_unfold_dom_union:
  ∀ (K : Type) (M : Type → Type) (D : Type) (H : ∀ A : Type, Dom (M A) D) (H0 : FMap M) (H1 : ∀ A : Type, Lookup K A (M A)) (H2 : ∀ A : Type, Empty (M A))
    (H3 : ∀ A : Type, PartialAlter K A (M A)) (H4 : OMap M) (H5 : Merge M) (H6 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K) (H7 : ElemOf K D)
    (H8 : Empty D) (H9 : Singleton K D) (H10 : Union D) (H11 : Intersection D) (H12 : Difference D),
    FinMapDom K M D
    → ∀ (A : Type) (i : K) (m1 m2 : M A) (Q1 Q2 : Prop), SetUnfoldElemOf i (dom D m1) Q1 → SetUnfoldElemOf i (dom D m2) Q2 → SetUnfoldElemOf i (dom D (m1 ∪ m2)) (Q1 ∨ Q2)
map_filter_union:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (P : K * A → Prop) (H7 : ∀ x : K * A, Decision (P x)) (m1 m2 : M A), m1 ##ₘ m2 → filter P (m1 ∪ m2) = filter P m1 ∪ filter P m2
kmap_union:
  ∀ (K1 : Type) (M1 : Type → Type) (H : FMap M1) (H0 : ∀ A : Type, Lookup K1 A (M1 A)) (H1 : ∀ A : Type, Empty (M1 A)) (H2 : ∀ A : Type, PartialAlter K1 A (M1 A))
    (H3 : OMap M1) (H4 : Merge M1) (H5 : ∀ A : Type, FinMapToList K1 A (M1 A)) (EqDecision0 : EqDecision K1),
    FinMap K1 M1
    → ∀ (K2 : Type) (M2 : Type → Type) (H7 : FMap M2) (H8 : ∀ A : Type, Lookup K2 A (M2 A)) (H9 : ∀ A : Type, Empty (M2 A)) (H10 : ∀ A : Type, PartialAlter K2 A (M2 A))
        (H11 : OMap M2) (H12 : Merge M2) (H13 : ∀ A : Type, FinMapToList K2 A (M2 A)) (EqDecision1 : EqDecision K2),
        FinMap K2 M2 → ∀ f : K1 → K2, Inj eq eq f → ∀ (A : Type) (m1 m2 : M1 A), kmap f (m1 ∪ m2) = kmap f m1 ∪ kmap f m2
dom_union_inv_L:
  ∀ (K : Type) (M : Type → Type) (D : Type) (H : ∀ A : Type, Dom (M A) D) (H0 : FMap M) (H1 : ∀ A : Type, Lookup K A (M A)) (H2 : ∀ A : Type, Empty (M A))
    (H3 : ∀ A : Type, PartialAlter K A (M A)) (H4 : OMap M) (H5 : Merge M) (H6 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K) (H7 : ElemOf K D)
    (H8 : Empty D) (H9 : Singleton K D) (H10 : Union D) (H11 : Intersection D) (H12 : Difference D),
    FinMapDom K M D
    → LeibnizEquiv D → RelDecision elem_of → ∀ (A : Type) (m : M A) (X1 X2 : D), X1 ## X2 → dom D m = X1 ∪ X2 → ∃ m1 m2 : M A, m = m1 ∪ m2 ∧ m1 ##ₘ m2 ∧ dom D m1 = X1 ∧ dom D m2 = X2
map_cross_split:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M
    → ∀ (A : Type) (ma mb mc md : M A),
        ma ##ₘ mb
        → mc ##ₘ md
          → ma ∪ mb = mc ∪ md → ∃ mac mad mbc mbd : M A, mac ##ₘ mad ∧ mbc ##ₘ mbd ∧ mac ##ₘ mbc ∧ mad ##ₘ mbd ∧ mac ∪ mad = ma ∧ mbc ∪ mbd = mb ∧ mac ∪ mbc = mc ∧ mad ∪ mbd = md
dom_union_inv:
  ∀ (K : Type) (M : Type → Type) (D : Type) (H : ∀ A : Type, Dom (M A) D) (H0 : FMap M) (H1 : ∀ A : Type, Lookup K A (M A)) (H2 : ∀ A : Type, Empty (M A))
    (H3 : ∀ A : Type, PartialAlter K A (M A)) (H4 : OMap M) (H5 : Merge M) (H6 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K) (H7 : ElemOf K D)
    (H8 : Empty D) (H9 : Singleton K D) (H10 : Union D) (H11 : Intersection D) (H12 : Difference D),
    FinMapDom K M D → RelDecision elem_of → ∀ (A : Type) (m : M A) (X1 X2 : D), X1 ## X2 → dom D m ≡ X1 ∪ X2 → ∃ m1 m2 : M A, m = m1 ∪ m2 ∧ m1 ##ₘ m2 ∧ dom D m1 ≡ X1 ∧ dom D m2 ≡ X2
map_intersection_filter:
  ∀ (K : Type) (M : Type → Type) (H : FMap M) (H0 : ∀ A : Type, Lookup K A (M A)) (H1 : ∀ A : Type, Empty (M A)) (H2 : ∀ A : Type, PartialAlter K A (M A))
    (H3 : OMap M) (H4 : Merge M) (H5 : ∀ A : Type, FinMapToList K A (M A)) (EqDecision0 : EqDecision K),
    FinMap K M → ∀ (A : Type) (m1 m2 : M A), m1 ∩ m2 = filter (λ kx : K * A, is_Some (m1 !! kx.1) ∧ is_Some (m2 !! kx.1)) (m1 ∪ m2)
```
