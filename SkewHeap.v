  Set Implicit Arguments.
  Require Import Coq.Program.Wf.
  Require Import Coq.Arith.Arith.
  Require Import Lia.
  Require Import Recdef.
  Require Import Coq.Lists.List.
  Require Import Coq.Sorting.Permutation.
  Require Import Coq.Arith.PeanoNat.
  Import ListNotations.


  (*---------------------------- Skew Heap Module Definitions and Important Functions ----------------------------*)

  Module SkewHeapNat.

  (* ---------- Skew heap type definition ---------- *)
  (* A skew heap is either a Leaf (empty heap) or a Node containing a value and two subtrees *)
  Inductive SHeap : Type :=
    | Leaf : SHeap
    | Node : nat -> SHeap -> SHeap -> SHeap.

  (* ---------- Helper functions ---------- *)

  (* Returns the size (number of nodes) of a heap *)
  Fixpoint size (h : SHeap) : nat :=
    match h with
    | Leaf        => 0
    | Node _ l r  => S (size l + size r)
    end.

  (* Computes the combined size of a pair of heaps (used for merge termination proof) *)
  Definition size_skew (p : SHeap * SHeap) : nat :=
    size (fst p) + size (snd p).

  (* ---------- Core operations ---------- *)

  (* Merges two skew heaps *)
  Function merge (p : SHeap * SHeap) {measure size_skew p} : SHeap :=
    match p with
    | (Leaf, h)          => h
    | (h, Leaf)          => h
    | (Node x l1 r1, Node y l2 r2) =>
        if Nat.ltb x y
        then Node x (merge (r1, snd p)) l1
        else Node y (merge (r2, fst p)) l2
    end.
  Proof.
    - intros.
      apply Nat.add_lt_le_mono.
      + simpl. lia.
      + apply Nat.le_refl.
    - intros.
      subst p.
      unfold size_skew; simpl.
      lia.
  Defined.

  (* Creates a singleton heap containing one element *)
  Definition singleton (x : nat) : SHeap := Node x Leaf Leaf.

  (* Inserts an element by merging it as a singleton heap *)
  Definition insert (x : nat) (h : SHeap) : SHeap :=
    merge ((Node x Leaf Leaf), h).

  (* Finds the minimum element (at the root) if it exists *)
  Definition find_min (h : SHeap) : option nat :=
    match h with
    | Leaf       => None
    | Node x _ _ => Some x
    end.

  (* Deletes the minimum element (the root) by merging its subtrees *)
  Definition delete_min (h : SHeap) : SHeap :=
    match h with
    | Leaf       => Leaf
    | Node _ l r => merge (l, r)
    end.

  (* Extracts the minimum element and the resulting heap *)
  Definition extract_min (h : SHeap) : option (nat * SHeap) :=
    match h with
    | Leaf       => None
    | Node x l r => Some (x, merge (l, r))
    end.

  (* ---------- Invariants and predicates ---------- *)

  (* Checks whether a given property P holds for every element in the heap *)
  Fixpoint All (P: nat -> Prop) (h: SHeap) : Prop :=
    match h with
    | Leaf       => True
    | Node x l r => P x /\ All P l /\ All P r
    end.

  (* Invariant that ensures that each node’s value is less than or equal to all values in its subtrees *)
  Fixpoint heap_order (h : SHeap) : Prop :=
    match h with
    | Leaf => True
    | Node x l r =>
        All (fun y => x <= y) l /\
        All (fun y => x <= y) r /\
        heap_order l /\
        heap_order r
    end.

  (* Predicate expressing that x occurs somewhere in the heap *)
  Inductive Elem (x : nat) : SHeap -> Prop :=
  | Elem_root : forall l r, Elem x (Node x l r)
  | Elem_l    : forall y l r, Elem x l -> Elem x (Node y l r)
  | Elem_r    : forall y l r, Elem x r -> Elem x (Node y l r).

  (* Checks if the heap is empty *)
  Definition isEmpty (h : SHeap) : bool :=
    match h with
    | Leaf => true
    | _ => false
    end.

  End SkewHeapNat.


  (*---------------------------- Skew Heap Merge Lemmas ----------------------------*)


  Module MergeLemmas.
  Import SkewHeapNat.

  (* Merging two heaps produces an empty heap if and only if both inputs are empty *)
  Lemma isEmpty_merge (h1 h2 : SHeap):
      isEmpty (merge (h1, h2)) = andb (isEmpty h1) (isEmpty h2).
  Proof.
      remember (h1, h2) as p.
      functional induction merge p; inversion Heqp; subst; clear Heqp.
      - destruct h2. 
        + reflexivity.
        + reflexivity.
     - destruct h1.
        + reflexivity.
        + reflexivity.
     - simpl. reflexivity.
     - simpl. reflexivity.
  Qed.

  (* Merging with an empty heap on the left returns the right heap unchanged *)
  Lemma merge_leaf_l (h : SHeap) : 
    merge (Leaf, h) = h.
  Proof.
    unfold merge; simpl.
    reflexivity.
  Qed.

  (* Merging with an empty heap on the right returns the left heap unchanged *)
  Lemma merge_leaf_r (h : SHeap): 
    merge (h, Leaf) = h.
  Proof.
    destruct h; simpl.
    - reflexivity.
    - unfold merge; simpl. reflexivity.
  Qed.


  (* ---------- Size-related properties ---------- *)

  (* The size of a Node is 1 plus the size of its two subtrees *)
  Lemma size_Node (x : nat) (l r : SHeap):
      size (Node x l r) = 1 + size l + size r.
  Proof.
    simpl. lia.
  Qed.

  (* The size of merging two heaps equals the sum of their sizes *)
  Lemma size_merge (h1 h2 : SHeap):
      size (merge (h1, h2)) = size h1 + size h2.
  Proof.
    remember (h1, h2) as p. revert h1 h2 Heqp.
    functional induction merge p; inversion 1.
    - destruct h2; simpl; reflexivity.
    - destruct h1; simpl. cbn. lia. lia.
    - assert (Hmerge := IHs r1 (Node y l2 r2) eq_refl).
      rewrite size_Node.
      rewrite Hmerge.
      rewrite size_Node. 
      rewrite !size_Node in *.
      lia.
    - rewrite size_Node.
      assert (Hmerge := IHs r2 (fst (Node x l1 r1, Node y l2 r2)) eq_refl).
      rewrite Hmerge.
      rewrite size_Node.
      rewrite !size_Node in *.
      simpl fst in *.
      rewrite size_Node.
      lia.
  Qed.


(* ---------- Heap-Order Invariant preservation ---------- *)

  (* Merging two heaps preserves a universal property P across elements *)
  Lemma merge_All (P : nat -> Prop) (h1 h2 : SHeap):
     All P h1 -> All P h2 -> All P (merge (h1, h2)).
  Proof.
    remember (h1, h2) as p. revert h1 h2 Heqp.
    functional induction (merge p) using merge_ind; intros h1 h2 Heqp; inversion Heqp; subst; clear Heqp; auto.
    - intros H1 H2. simpl in *.
      repeat split.
      + apply H1.
      + apply (IHs r1 (Node y l2 r2)); auto.
        apply H1.
      + apply H1.
    - intros H1 H2. simpl in *.
      repeat split.
      + apply H2.
      + apply (IHs r2 (Node x l1 r1)); auto.
        apply H2.
      + apply H2.
  Qed.
 

  (* Weakens a universal property: if P implies Q, then All P implies All Q *)
  Lemma weaken_All (P Q : nat -> Prop) (h : SHeap) :
      (forall x, P x -> Q x) ->
      All P h -> All Q h.
  Proof.
    intros HPQ.
    induction h as [| x l IHl r IHr]; simpl; intros H.
    - exact I.
    - destruct H as [Hx [Hl Hr]]. repeat split.
      + apply HPQ, Hx.
      + apply IHl, Hl.
      + apply IHr, Hr.
  Qed.

  (* Merging two heaps preserves the heap order invariant *)
  Lemma merge_preserves_heap_order (h1 h2 : SHeap):
      heap_order h1 ->
      heap_order h2 ->
      heap_order (merge (h1,h2)).
  Proof.
    intros Hh1 Hh2.
    remember (h1, h2) as p.
    revert h1 h2 Hh1 Hh2 Heqp.
    functional induction (merge p) using merge_ind; intros; inversion Heqp; subst; clear Heqp.
    - exact Hh2.
    - exact Hh1.
    - simpl. simpl in IHs. 
      repeat split.
      + apply merge_All.
        * apply Hh1.
        * simpl. apply Nat.ltb_lt in e0.
          repeat split.
          -- lia.
          -- apply weaken_All with (P := fun y0 => y <= y0). {
               intros y0 Hy0. lia.
             }
             apply Hh2.
          -- apply weaken_All with (P := fun y0 => y <= y0). {
               intros y0 Hy0. lia.
             }
             apply Hh2.
      + apply Hh1.
      + eapply (IHs r1 (Node y l2 r2)); eauto. inversion Hh1; subst. apply H0.
      + apply Hh1.
    - simpl. simpl in IHs. 
      repeat split.
      + apply merge_All.
        * apply Hh2.
        * simpl. 
          repeat split.
          -- apply Nat.ltb_ge in e0. lia.
          -- apply weaken_All with (P := fun y0 => x <= y0). {
               intros y0 Hy0.
               assert (y <= x) by (apply Nat.ltb_ge in e0; exact e0).
               lia.
             }
              apply Hh1.

          -- apply weaken_All with (P := fun y0 => x <= y0). {
               intros y0 Hy0.
               assert (y <= x) by (apply Nat.ltb_ge in e0; exact e0).
               lia.
             }
             apply Hh1.
      + apply Hh2.
      +  eapply (IHs r2 (Node x l1 r1)); eauto. inversion Hh2; subst. apply H0.
      + apply Hh2.
  Qed.

  (* ---------- Membership lemmas ---------- *)

  (* Element membership in a Node is equivalent to being the root or in a subtree *)
  Lemma Elem_Node (x y : nat) (l r : SHeap):
      Elem x (Node y l r) <-> x = y \/ Elem x l \/ Elem x r.
  Proof.
    split.
    - intros H. inversion H; subst; auto.
    - intros [Heq | [Hl | Hr]].
      + subst. apply Elem_root.
      + apply Elem_l. exact Hl.
      + apply Elem_r. exact Hr.
  Qed.


  (* Element membership in a merged heap corresponds to membership in either input *)
  Lemma Elem_merge (x : nat) (h1 h2 : SHeap):
      Elem x (merge (h1, h2)) <-> Elem x h1 \/ Elem x h2.
  Proof.
    remember (h1, h2) as p eqn:Heqp.
    revert h1 h2 Heqp.
    functional induction (merge p) using merge_ind; intros; inversion Heqp; subst; clear Heqp.
    - simpl. split; intro H; [right | destruct H; [inversion H |]]; assumption.
    - simpl. split; intro H; [left | destruct H; [|inversion H]]; assumption.
    - simpl.
      split; intro H.
      * inversion H; subst.
        + left. constructor.
        + assert (Elem x r1 \/ Elem x (Node y l2 r2)) as [Hr | Hr].
        {
          apply IHs with (h1 := r1) (h2 := Node y l2 r2).
          reflexivity.
          exact H1.
        }
          -- left. constructor 3. assumption.
          -- right. assumption.
        + left. constructor. assumption.
      * destruct H as [H1 | H2].
        -- rewrite Elem_Node in H1.
          destruct H1 as [-> | [Hl | Hr]].
          + constructor.
          + apply Elem_r. exact Hl.
          + apply Elem_l. apply IHs with (h1 := r1) (h2 := Node y l2 r2). reflexivity. left. exact Hr.
        -- apply Elem_l. apply IHs with (h1 := r1) (h2 := Node y l2 r2). reflexivity. right. exact H2.

    -  split; intro H.
        -- rewrite Elem_Node in H.
            destruct H as [-> | [Hl | Hr]].
            + right. constructor.
            + assert (Elem x r2 \/ Elem x (fst (Node x0 l1 r1, Node y l2 r2))) as [Hr | Hf].
              {
                apply IHs with (h1 := r2) (h2 := fst (Node x0 l1 r1, Node y l2 r2)).
                reflexivity. exact Hl.
              }
              --- right. apply Elem_r. exact Hr.
              --- left. apply Hf.
            + right. apply Elem_l. exact Hr.
        -- destruct H as [Hx0 | Hy].
            --- apply Elem_Node.
              right. left.
              apply IHs with (h1 := r2) (h2 := fst (Node x0 l1 r1, Node y l2 r2)).
              + reflexivity.
              + right. exact Hx0.

            --- apply Elem_Node. rewrite Elem_Node in Hy.
              destruct Hy as [Hxy | [Hl2 | Hr2]].
            * constructor 1. exact Hxy.
            * right. right. exact Hl2.
            * apply Elem_Node. apply Elem_Node. right. left.
              apply IHs with (h1 := r2) (h2 := fst (Node x0 l1 r1, Node y l2 r2)).
              + reflexivity.
              + left. exact Hr2.
  Qed.

  End MergeLemmas.

  (*---------------------------- Skew Heap Insert Lemmas ----------------------------*)

  Module InsertLemmas.
  Import SkewHeapNat.
  Import MergeLemmas.

  (* ---------- Size-related properties ---------- *)

  (* The size of inserting an element equals 1 plus the size of the original heap *)
  Lemma size_insert (x : nat) (h : SHeap):
      size (insert x h) = 1 + size h.
  Proof.
    unfold insert.
    rewrite size_merge.
    simpl. reflexivity.
  Qed.

  (* ---------- Heap-Order Invariant preservation ---------- *)

  (* Inserting an element into a heap preserves the heap_order property if it held before *)
  Lemma insert_preserves_heap_order (x : nat) (h : SHeap) :
    heap_order h ->
    heap_order (insert x h).
  Proof.
    intros Hh.
    unfold insert.
    apply merge_preserves_heap_order. 
      - simpl. repeat split; constructor.
      - exact Hh.
  Qed.

  (* ---------- Membership lemmas ---------- *)

  (* An element x belongs to singleton y if and only if x equals y *)
  Lemma Elem_singleton (x y : nat):
      Elem x (singleton y) <-> x = y.
  Proof.
    unfold singleton. simpl.
    split.
    - intros H. inversion H; subst.
      + reflexivity.
      + inversion H1.
      + inversion H1.
    - intros ->. apply Elem_root.
  Qed.

  (* An element x belongs to insert y h if and only if x equals y or x belongs to h *)
  Lemma Elem_insert (x y : nat) (h : SHeap):
      Elem x (insert y h) <-> x = y \/ Elem x h.
  Proof.
    unfold insert.
    rewrite Elem_merge.
    split; intro H.
    - destruct H as [H | H]; [left | right]; try now inversion H; auto. apply H.
    - destruct H as [-> | H]; [left | right]. constructor; assumption. apply H.
  Qed.

  End InsertLemmas.


  Module DeleteLemmas.
  Import SkewHeapNat.
  Import MergeLemmas.

  (* ---------- Size-related properties ---------- *)

  (* Deleting the minimum element from a non-empty heap reduces its size by 1 *)
  Lemma size_delete_min (h : SHeap) :
    h <> Leaf ->
    size (delete_min h) = size h - 1.
  Proof.
    intros Hh.
    destruct h as [| x l r].
    - contradiction.
    - simpl.
      rewrite size_merge.
      lia.
  Qed.

  (* ---------- Heap-Order Invariant preservation ---------- *)

  (* Deleting the minimum element preserves the heap_order property if it held before *)
  Lemma delete_min_preserves_heap_order (h : SHeap):
      heap_order h ->
      heap_order (delete_min h).
  Proof.
    intros H.
    unfold delete_min.
    destruct h as [| x l r].
    - simpl; constructor.
    - simpl.
      destruct H as (_ & _ & Hord_l & Hord_r).
      now apply merge_preserves_heap_order.
  Qed.

  (* ---------- Membership lemmas ---------- *)


  (* An element x belongs to delete_min h if and only if 
     x belonged to one of the subtrees of h (if h was non-empty) *)
  Lemma Elem_delete_min (x : nat) (h : SHeap):
      Elem x (delete_min h) <->
      match h with
      | Leaf => False
      | Node _ l r => Elem x l \/ Elem x r
      end.
  Proof.
    destruct h as [| y l r].
    - simpl. split; [intros H; inversion H | intros []].
    - simpl. rewrite Elem_merge.
      split.
      + intros [Hl | Hr]; [left | right]; assumption.
      + intros [Hl | Hr]; [left | right]; assumption.
  Qed.


  End DeleteLemmas.

  (*---------------------------- Skew Heap ExtractMin Lemmas ----------------------------*)

  Module ExtractMinLemmas.
  Import SkewHeapNat.
  Import MergeLemmas.

  (* ---------- Size-related properties ---------- *)


  (* If extract_min returns Some (x, h'), then the size of the original heap h is one more than the size of h' *)
  Lemma size_extract_min (x : nat) (h h' : SHeap):
      extract_min h = Some (x, h') -> size h = S (size h').
  Proof.
    intros Hext.
    destruct h as [| y l r']; simpl in Hext.
    - discriminate.
    - inversion Hext; subst.
      simpl. rewrite size_merge. reflexivity.
  Qed.

  (* ---------- Heap-Order Invariant preservation ---------- *)

  (* If extract_min returns Some (x, h'), then h' satisfies heap_order provided h did *)
  Lemma extract_min_preserves_heap_order (x : nat) (h h' : SHeap):
      heap_order h ->
      extract_min h = Some (x, h') ->
      heap_order h'.
  Proof.
    intros Hh Hext.
    destruct h.
    - simpl in Hext. discriminate.
    - simpl in Hext. inversion Hext. subst h'.
      destruct Hh as [Hroot [Hl Hr]].
      apply merge_preserves_heap_order. apply Hr. apply Hr.
  Qed.

  (* ---------- Membership lemmas ---------- *)

  (* If extract_min returns Some (x, h'), then x belonged to the original heap h *)
  Lemma Elem_extract_min (x : nat) (h h' : SHeap):
      extract_min h = Some (x, h') ->
      Elem x h.
  Proof.
    intros Hext.
    destruct h as [| y l r]; simpl in Hext.
    - discriminate.
    - destruct l, r; simpl in Hext;
      try (inversion Hext; subst; constructor);
      destruct (extract_min h) as [[m1 h1]|] eqn:He1;
      destruct (extract_min h0) as [[m2 h2]|] eqn:He2;
      destruct (m1 <? m2) eqn:Hcmp;
      inversion Hext; subst;
      try constructor 2; try constructor 3;
      apply Elem_extract_min with (t' := h1) in He1; assumption ||
      apply Elem_extract_min with (t' := h2) in He2; assumption.
  Qed.


  End ExtractMinLemmas.



  Module MinLemmas.
  Import SkewHeapNat.
  Import MergeLemmas.

  (* Compare two optional nats by taking the minimum when both present *)
  Definition min_opt (o1 o2 : option nat) : option nat :=
    match o1, o2 with
    | None,  o       => o
    | o,     None    => o
    | Some x, Some y => Some (Nat.min x y)
    end.

  (* ---------- Merge properties ---------- *)

  (* The minimum of a Node is its root value *)
  Lemma find_min_correct (v : nat) (n : nat) (l r : SHeap):
      find_min (Node v l r) = Some v.
  Proof.
    simpl. reflexivity.
  Qed.

  (* The minimum of merging two heaps is the minimum of the two heap roots *)
  Lemma find_min_merge (h1 h2 : SHeap) :
    find_min (merge (h1, h2)) = min_opt (find_min h1) (find_min h2).
  Proof.
    remember (h1, h2) as p eqn:Heqp.
    revert h1 h2 Heqp.
    functional induction (merge p) using merge_ind; intros; inversion Heqp; subst; clear Heqp.
    - destruct h2; simpl; reflexivity.
    - destruct h1; simpl; reflexivity.
    - simpl. f_equal. apply Nat.ltb_lt in e0.  lia.
    - simpl. f_equal. apply Nat.ltb_ge in e0. lia.
  Qed.

  (* ---------- Insert properties ---------- *)

  (* find_min of an insert compares the new element against the old min *)
  Lemma find_min_insert (x : nat) (h : SHeap) :
    find_min (insert x h) = min_opt (Some x) (find_min h).
  Proof.
    unfold insert; apply find_min_merge.
  Qed.

  (* ---------- DeleteMin properties ---------- *)

  (* A heap has no minimum if and only if it is Leaf *)
  Lemma find_min_empty_iff (h : SHeap) :
    find_min h = None <-> h = Leaf.
  Proof.
    split.
    - destruct h; simpl; auto; discriminate.
    - intros ->. simpl. reflexivity.
  Qed.

  (* If the heap is empty then delete_min returns Leaf *)
  Lemma find_min_delete_consistent (h : SHeap) :
    find_min h = None -> delete_min h = Leaf.
  Proof.
    intros H.
    destruct h.
    - reflexivity.
    - simpl in H. discriminate.
  Qed.
   
  (* After deleting the root from a non‐singleton heap, the new min is >= old *)
  Lemma find_min_delete_next (h : SHeap) (x : nat) :
    heap_order h ->
    find_min h = Some x ->
    delete_min h <> Leaf ->
    exists m', find_min (delete_min h) = Some m' /\ x <= m'.
  Proof.
    intros Hord Hmin Hne.
    destruct h as [| x' l r']; simpl in *; try contradiction.
    inversion Hmin; subst; clear Hmin.
    simpl. unfold delete_min. simpl.
    remember (merge (l, r')) as h'.
    destruct h' as [| m' l' r''].
    - exfalso. apply Hne. reflexivity.
    - exists m'. split; [reflexivity|].
      destruct Hord as [Hall_l [Hall_r [Hord_l Hord_r]]].

      assert (All (fun y => x <= y) (merge (l, r'))) as Hmerge_all.
      {
        apply merge_All; assumption.
      }

      simpl in Hmerge_all. rewrite <- Heqh' in Hmerge_all.
      destruct Hmerge_all as [Hx_le _].
      exact Hx_le.
  Qed.

  (* This is the same lemma as the one before but proven in a different way*)
  Lemma find_min_delete_next2 (h : SHeap) (m : nat) :
    heap_order h ->
    find_min h = Some m ->
    delete_min h <> Leaf ->
    exists m', find_min (delete_min h) = Some m' /\ m <= m'.
  Proof.
    intros Hord Hmin Hne.
    unfold delete_min in *.
    destruct h as [| x l r]; simpl in *; try contradiction.
    inversion Hmin; subst x; clear Hmin.
    destruct Hord as [Hall_l [Hall_r [Hord_l Hord_r]]].
    simpl.
    rewrite find_min_merge.
    unfold min_opt.
    destruct (find_min l) as [n1|] eqn:Hl.
    - destruct (find_min r) as [n2|] eqn:Hr.
      + exists (Nat.min n1 n2). split.
        * reflexivity.
        * destruct l as [| x1 l1 r1]; simpl in Hl; try discriminate.
          inversion Hl; subst n1.
          destruct r as [| x2 l2 r2]; simpl in Hr; try discriminate.
          inversion Hr; subst n2.
          simpl in Hall_l, Hall_r.
          destruct Hall_l as [Hle1 _].
          destruct Hall_r as [Hle2 _].
          apply Nat.min_glb; assumption.
      + exists n1. split; [reflexivity|].
        destruct l as [| x1 l1 r1]; simpl in Hl; try discriminate.
        inversion Hl; subst n1.
        simpl in Hall_l.
        destruct Hall_l as [Hle1 _].
        exact Hle1.
    - destruct (find_min r) as [n2|] eqn:Hr.
      + exists n2. split; [reflexivity|].
        destruct r as [| x2 l2 r2]; simpl in Hr; try discriminate.
        inversion Hr; subst n2.
        simpl in Hall_r.
        destruct Hall_r as [Hle2 _].
        exact Hle2.
      + destruct l, r; simpl in *; inversion Hl; inversion Hr.
        exfalso. apply Hne. reflexivity.
  Qed.


  End MinLemmas.

(*---------------------------- Skew Heap Permutation Lemmas ----------------------------*)

  Module SkewHeapNat_Permutation.
  Import SkewHeapNat.
  Import MinLemmas.

  (* ---------- Helper function ---------- *)

  (* Flattens a heap into a list *)
  Fixpoint to_list (h : SHeap) : list nat :=
    match h with
    | Leaf        => []
    | Node x l r  => x :: (to_list l ++ to_list r)
    end.


  (* ---------- Merge permutation properties ---------- *)

  (* Merging two heaps produces a heap whose elements are a permutation of the combined elements of both heaps *)
  Lemma to_list_merge (h1 h2 : SHeap):
        Permutation (to_list (merge (h1, h2)))
                    (to_list h1 ++ to_list h2).
  Proof.
    remember (h1, h2) as p eqn:Heqp.
    revert h1 h2 Heqp.
    functional induction (merge p) using merge_ind; intros; inversion Heqp; subst; clear Heqp; simpl; auto.
    - rewrite app_nil_r. reflexivity.
    - simpl in IHs.
     assert (Permutation (to_list (merge (r1, Node y l2 r2))) (to_list r1 ++ to_list (Node y l2 r2))) as HP.
     { eapply IHs; eauto. }
     simpl in HP.
     constructor. rewrite HP.
     rewrite Permutation_app_comm.
     rewrite app_assoc.
     reflexivity.
    - simpl in IHs.
    assert (Permutation (to_list (merge (r2, Node x l1 r1))) (to_list r2 ++ to_list (Node x l1 r1))) as Hperm.
    { eapply IHs; eauto. }
    simpl in Hperm.
    rewrite <- Permutation_app_comm.
    rewrite Hperm.
    rewrite app_assoc.
    rewrite <- Permutation_middle.
    rewrite perm_swap. constructor. 
    rewrite <- Permutation_middle.
    constructor.
    rewrite Permutation_app_comm. 
    reflexivity.
  Qed.


  (* ---------- Insert permutation properties ---------- *)

  (* The flattened list of a singleton is a singleton list *)
  Lemma to_list_singleton (x : nat) :
    to_list (singleton x) = [x].
  Proof.
    simpl. reflexivity. 
  Qed.

  (* Inserting x into a heap produces a heap whose elements are a permutation of x followed by the original elements *)
  Lemma to_list_insert (x : nat) (h : SHeap):
      Permutation (to_list (insert x h)) (x :: to_list h).
  Proof.
    unfold insert.
    rewrite to_list_merge.
    simpl.
    apply Permutation_refl.
  Qed.

  (* ---------- Delete_min permutation properties ---------- *)

  (* Deleting the minimum element produces a heap whose elements are a permutation of the tail of the original heap's flattened list *)
  Lemma to_list_delete_min (x : nat) (h : SHeap) :
      find_min h = Some x ->
      Permutation (to_list (delete_min h)) (tl (to_list h)).
  Proof.
    intros Hmin.
    destruct h as [| v l r'].
    - simpl in Hmin. discriminate.
    - simpl in Hmin. inversion Hmin; subst.
      simpl. rewrite to_list_merge.
      reflexivity.
  Qed.


  (* ---------- ExtractMin permutation properties ---------- *)

  (* If extract_min returns Some (x, h'), the original heap's elements are a permutation of x followed by the elements of h' *)
  Lemma to_list_extract_min (x : nat) (h h' : SHeap) :
      extract_min h = Some (x, h') ->
      Permutation (to_list h) (x :: to_list h').
  Proof.
    intros Hext.
    destruct h; simpl in Hext.
    - discriminate.
    - inversion Hext; subst.
      simpl.
      rewrite to_list_merge.
      reflexivity.
  Qed.

  (* ---------- Extra permutation properties ---------- *)

  (* From [All P h] we can conclude P holds for every y in [to_list h] *)
  Lemma All_to_list (P : nat -> Prop) (h : SHeap):
    All P h -> forall y, In y (to_list h) -> P y.
  Proof.
    intros H y Hin.
    induction h as [| x l r IHl IHr]; simpl in *.
    - inversion Hin.
    - destruct H as [Px [Hl Hr]].
      destruct Hin as [-> | Hin].
      + exact Px.
      + apply in_app_or in Hin as [Hinl | Hinr].
        * apply r; assumption.
        * apply IHr; assumption.
  Qed.

  (* Helper: if x is not in l, then removing x from l returns l unchanged *)
  Lemma remove_not_in {A : Type} (eq_dec : forall u v : A, {u = v} + {u <> v}) :
    forall x l,
      (forall y, In y l -> y <> x) ->
      remove eq_dec x l = l.
  Proof.
    induction l as [|a l IH]; simpl; auto.
    intros Hnot.
    destruct (eq_dec a x) as [Heq | Hneq].
    - subst a. exfalso. apply (Hnot x). left. reflexivity. reflexivity.
    - destruct (eq_dec x a) as [Heq' | Hneq'].
      + symmetry in Heq'. contradiction.
      + simpl. f_equal. apply IH. intros y Hy. apply Hnot. right. exact Hy.
  Qed.

  (* Defines the strict heap order property:
   every node's value is strictly smaller than all values in its subtrees,
   and the property holds recursively for both subtrees *)
  Fixpoint strict_heap_order (h : SHeap) : Prop :=
    match h with
    | Leaf => True
    | Node x l r =>
        All (fun y => x < y) l /\
        All (fun y => x < y) r /\
        strict_heap_order l /\
        strict_heap_order r
    end.

  (* Ensures that deleting the root removes exactly the first occurrence of the minimum *)
  Lemma to_list_delete_min_extra (x : nat) (h : SHeap):
      strict_heap_order h ->
      find_min h = Some x ->
      Permutation (to_list (delete_min h))
                  (remove Nat.eq_dec x (to_list h)).
  Proof.
    intros Hstr Hmin.
    destruct h as [|x' l r]; simpl in Hmin; try discriminate.
    inversion Hmin; subst x.
    simpl.
    rewrite to_list_merge; simpl.
    destruct Hstr as [Hall_l [Hall_r [_ _]]].
    assert (Hno : forall y, In y (to_list l ++ to_list r) -> y <> x').
    {
      intros y Hy.
      apply in_app_or in Hy as [Hy_l | Hy_r].
      - apply (All_to_list (fun z => x' < z) l Hall_l y) in Hy_l. lia.
      - apply (All_to_list (fun z => x' < z) r Hall_r y) in Hy_r. lia.

    }

  destruct (Nat.eq_dec x' x') as [_ | Hx]; [| contradiction].
  rewrite (remove_not_in Nat.eq_dec (to_list l ++ to_list r) Hno).
  apply Permutation_refl.
  Qed.

  End SkewHeapNat_Permutation.
