  Set Implicit Arguments.
  Require Import Coq.Program.Wf.
  Require Import Coq.Arith.Arith.
  Require Import Lia.
  Require Import Recdef.
  Require Import Coq.Lists.List.
  Require Import Coq.Sorting.Permutation.
  Require Import Coq.Arith.PeanoNat.
  Import ListNotations.



(*---------------------------- Leftist Heap Module Definitions and Important Functions ----------------------------*)

  Module LeftistHeapNat.

  (* ---------- Leftist heap type definition ---------- *)
  (* A leftist heap is either a Leaf (empty heap) or a Node containing rank, value, and two subtrees *)
  Inductive LHeap : Type :=
    | Leaf : LHeap
    | Node : nat -> nat -> LHeap -> LHeap -> LHeap.

  (* ---------- Helper functions ---------- *)

  (* Returns the rank of a heap (distance to nearest empty subtree) *)
  Definition rank (h : LHeap) : nat :=
    match h with
    | Leaf => 0
    | Node r _ _ _ => r
    end.

  (* Constructs a node while preserving the leftist property by ordering subtrees by rank *)
  Definition make_node (x : nat) (a b : LHeap) : LHeap :=
    if Nat.leb (rank a) (rank b)
    then Node (rank a + 1) x b a
    else Node (rank b + 1) x a b.

  (* Returns the size (number of nodes) of a heap *)
  Fixpoint size (h : LHeap) : nat :=
    match h with
    | Leaf => 0
    | Node _ _ l r => 1 + size l + size r
    end.

  (* Computes the combined size of a pair of heaps (used for merge termination proof) *)
  Definition sizeHeap (p : LHeap * LHeap) : nat :=
    size (fst p) + size (snd p).

  (* ---------- Core operations ---------- *)

  (* Merges two leftist heaps *)
  Function merge (p : LHeap * LHeap) {measure sizeHeap p} : LHeap :=
    match p with
    | (Leaf, h2) => h2
    | (h1, Leaf) => h1
    | (Node _ x1 l1 r1 as h1, Node _ x2 l2 r2 as h2) =>
        if Nat.leb x1 x2 then
          make_node x1 l1 (merge (r1, h2))
        else
          make_node x2 l2 (merge (h1, r2))
    end.
  Proof.
    - intros.
      apply Nat.add_lt_le_mono.
      + simpl. lia.
      + apply Nat.le_refl.
    - intros.
      subst p.
      simpl.
      apply Nat.add_lt_mono_l.
      simpl.
      lia.
  Defined.

  (* Creates a singleton heap containing one element *)
  Definition singleton (x : nat) : LHeap :=
    Node 0 x Leaf Leaf.

  (* Inserts an element by merging it as a singleton heap *)
  Definition insert (x : nat) (h : LHeap) : LHeap :=
    merge ((Node 0 x Leaf Leaf), h).

  (* Deletes the minimum element (the root) by merging its subtrees *)
  Definition delete_min (h : LHeap) : LHeap :=
    match h with
    | Leaf => Leaf
    | Node _ _ l r => merge (l, r)
    end.

  (* Finds the minimum element (at the root) if it exists *)
  Definition find_min (h : LHeap) : option nat :=
    match h with
    | Leaf => None
    | Node _ x _ _ => Some x
    end.

  (* Extracts the minimum element and the resulting heap *)
  Definition extract_min (h : LHeap) : option (nat * LHeap) :=
    match h with
    | Leaf => None
    | Node _ x l r => Some (x, merge (l, r))
    end.

  (* ---------- Invariants and predicates ---------- *)

  (* Invariant that checks if a heap satisfies the leftist property: rank of right <= rank of left *)
  Inductive Satisfies_leftist : LHeap -> Prop :=
    | Satisfies_leftist_Leaf : Satisfies_leftist Leaf
    | Satisfies_leftist_Node :
        forall (r : nat) (x : nat) (l r' : LHeap),
          rank r' <= rank l ->
          Satisfies_leftist l ->
          Satisfies_leftist r' ->
          Satisfies_leftist (Node r x l r').

  (* Checks whether a given property P holds for every element in the heap *)
  Fixpoint All (P: nat -> Prop) (h: LHeap) : Prop :=
    match h with
    | Leaf => True
    | Node _ x l r => P x /\ All P l /\ All P r
    end.

  (* Invariant that ensures that each node’s value is less than or equal to all values in its subtrees *)
  Fixpoint heap_order (h : LHeap) : Prop :=
    match h with
    | Leaf => True
    | Node _ x l r =>
        All (fun y => x <= y) l /\
        All (fun y => x <= y) r /\
        heap_order l /\
        heap_order r
    end.

  (* Predicate expressing that x occurs somewhere in the heap *)
  Inductive Elem (x : nat) : LHeap -> Prop :=
    | Elem_root : forall (r : nat) (l r' : LHeap), Elem x (Node r x l r')
    | Elem_l : forall (r : nat) (v : nat) (l r' : LHeap),
          Elem x l -> Elem x (Node r v l r')
    | Elem_r : forall (r : nat) (v : nat) (l r' : LHeap),
          Elem x r' -> Elem x (Node r v l r').

  (* Checks if the heap is empty *)
  Definition isEmpty (h : LHeap) : bool :=
    match h with
    | Leaf => true
    | _ => false
    end.

  End LeftistHeapNat.


(*---------------------------- Leftist Heap Merge Lemmas ----------------------------*)


  Module MergeLemmas.
  Import LeftistHeapNat.

  (* make_node always produces a non-empty heap *)
  Lemma isEmpty_make_node (x : nat) (l r : LHeap):
      isEmpty (make_node x l r) = false.
  Proof.
    unfold make_node, isEmpty.
    destruct (Nat.leb (rank l) (rank r)). 
    simpl.
    reflexivity.
    reflexivity.
  Qed.

  (* Merging two heaps produces an empty heap if and only if both inputs are empty *)
  Lemma isEmpty_merge (h1 h2 : LHeap):
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
    - rewrite isEmpty_make_node.
      reflexivity.
    - rewrite isEmpty_make_node. 
      reflexivity.
  Qed.

  (* Merging with an empty heap on the left returns the right heap unchanged *)
  Lemma merge_leaf_l (h : LHeap) :
      merge (Leaf, h) = h.
  Proof.
    unfold merge.
    destruct h.
     + simpl. reflexivity.
     + simpl. reflexivity.
  Qed.

  (* Merging with an empty heap on the right returns the left heap unchanged *)
  Lemma merge_leaf_r (h : LHeap):
      merge (h, Leaf) = h.
  Proof.
    unfold merge.
    destruct h.
     + simpl. reflexivity.
     + simpl. reflexivity.
  Qed.

  (* ---------- Size-related properties ---------- *)

  (* The size of make_node equals 1 plus the size of both subtrees *)
  Lemma size_make_node (x : nat) (l r : LHeap):
      size (make_node x l r) = 1 + size l + size r.
  Proof.
    unfold make_node.
    destruct (Nat.leb (rank l) (rank r)).
     + simpl. lia.
     + simpl. lia.
  Qed.

  (* The size of merging two heaps equals the sum of their sizes *)
  Lemma size_merge (h1 h2 : LHeap):
      size (merge (h1, h2)) = size h1 + size h2.
  Proof.
    remember (h1, h2) as p. revert h1 h2 Heqp.
    functional induction merge p; inversion 1.
    - destruct h2; simpl; reflexivity.
    - destruct h1; simpl. cbn. lia. lia.
    - simpl. rewrite size_make_node. simpl. 
      rewrite IHl with (h1 := r1) (h2 := Node _x0 x2 l2 r2).
       + simpl. lia.
       + reflexivity.
    - simpl. rewrite size_make_node. simpl. 
      rewrite IHl with (h1 := Node _x x1 l1 r1) (h2 := r2).
       + simpl. lia.
       + reflexivity.
  Qed.

  (* ---------- Leftist Invariant preservation ---------- *)

  (* make_node constructs a node that satisfies the leftist property when given two subtrees that satisfy it *)
  Lemma Satisfies_leftist_make_node (x : nat) (l r : LHeap):
      Satisfies_leftist l -> Satisfies_leftist r ->
      Satisfies_leftist (make_node x l r).
  Proof.
    intros Hl Hr.
    unfold make_node.
    destruct (Nat.leb (rank l) (rank r)) eqn:Hleb.
    - apply Nat.leb_le in Hleb.
      apply Satisfies_leftist_Node; try assumption; lia.
    - apply Nat.leb_gt in Hleb.
      apply Satisfies_leftist_Node; try assumption; lia.
  Qed.

  (* merge produces a heap that satisfies the leftist property if both input heaps do *)
  Lemma Satisfies_leftist_merge (h1 h2 : LHeap):
      Satisfies_leftist h1 -> Satisfies_leftist h2 -> Satisfies_leftist (merge (h1, h2)).
  Proof.
    intros H1 H2.
    remember (h1, h2) as p. revert h1 h2 Heqp H1 H2.
    functional induction (merge p) using merge_ind; intros; inversion Heqp; subst; clear Heqp.
    - exact H2.
    - exact H1.
    - inversion H1; subst.
      apply Satisfies_leftist_make_node; [assumption | now apply IHl with (h1 := r1) (h2 := Node _x0 x2 l2 r2)].
    - inversion H2; subst.
      apply Satisfies_leftist_make_node; [assumption | now apply IHl with (h1 := Node _x x1 l1 r1) (h2 := r2)].
  Qed.

  (* ---------- Heap-Order Invariant preservation ---------- *)

  (* make_node produces a heap where the property P holds for all elements if P holds for x and both subtrees *)
  Lemma All_make_node (P : nat -> Prop) (x : nat) (l r : LHeap):
      P x -> All P l -> All P r -> All P (make_node x l r).
  Proof.
    intros Hx Hl Hr.
    unfold make_node.
    destruct (Nat.leb (rank l) (rank r)); simpl; repeat split; assumption.
  Qed.


  (* merge produces a heap where the property P holds for all elements if it holds for both input heaps *)
  Lemma merge_All (P : nat -> Prop) (h1 h2 : LHeap):
      All P h1 -> All P h2 -> All P (merge (h1, h2)).
  Proof.
    intros H1 H2.
    remember (h1, h2) as p eqn:Hp.
    revert h1 h2 H1 H2 Hp.
    functional induction (merge p) using merge_ind; intros; inversion Hp; subst; clear Hp.
    - exact H2.
    - exact H1.
    - simpl. destruct H1 as [Hpx1 [Hl1 Hr1]].
      repeat split.
      apply All_make_node; auto. 
      apply IHl with (h1 := r1) (h2 := Node _x0 x2 l2 r2); [exact Hr1 | exact H2 | reflexivity].
    - simpl. destruct H2 as [Hpx2 [Hl2 Hr2]].
      repeat split. apply All_make_node; auto.
      apply IHl with (h1 := Node _x x1 l1 r1) (h2 := r2); [exact H1 | exact Hr2 | reflexivity].
  Qed.

  (* make_node produces a heap that satisfies heap_order when the subtrees do and all their elements are >= x *)
  Lemma heap_order_make_node (x : nat) (l r : LHeap):
      All (fun y => x <= y) l ->
      All (fun y => x <= y) r ->
      heap_order l ->
      heap_order r ->
      heap_order (make_node x l r).
  Proof.
    intros Hl Hr Hl_ord Hr_ord.
    unfold make_node.
    destruct (Nat.leb (rank l) (rank r)); simpl; repeat split; assumption.
  Qed.

  (* If P implies Q for all elements, then a heap where P holds everywhere also satisfies Q everywhere *)
  Lemma weaken_All (P Q : nat -> Prop) (h : LHeap):
      (forall x, P x -> Q x) ->
      All P h -> All Q h.
  Proof.
    intros HPQ.
    induction h as [| r x l IHl r' IHr]; simpl; intros H.
    - exact I.
    - destruct H as [Hx [Hl Hr]].
      repeat split.
      + apply HPQ, Hx.
      + apply IHl, Hl.
      + apply IHr, Hr.
  Qed.

  (* Asserts that All P holds for a Node if P holds at the root and in both subtrees *)
  Lemma All_Node (P : nat -> Prop) (x v : nat) (l r' : LHeap):
      P x -> All P l -> All P r' -> All P (Node v x l r').
  Proof.
    intros Hx Hl Hr.
    simpl.
    repeat split; assumption.
  Qed.

  (* merge produces a heap that satisfies heap_order if both inputs satisfy heap_order *)
  Lemma merge_preserves_heap_order (h1 h2 : LHeap):
      heap_order h1 -> heap_order h2 -> heap_order (merge (h1, h2)).
  Proof.
    intros Hh1 Hh2.
    remember (h1, h2) as p.
    revert h1 h2 Hh1 Hh2 Heqp.
    functional induction (merge p) using merge_ind; intros; inversion Heqp; subst; clear Heqp.
    - exact Hh2.
    - exact Hh1.
    - simpl.
      destruct Hh1 as [Hall1_l [Hall1_r [Hh1_l Hh1_r]]].
      repeat split.
      apply heap_order_make_node.
         -- exact Hall1_l.
         -- apply weaken_All with (P := fun y : nat => x1 <= y). {
            intros y0 Hy0. lia.
            } 
            apply merge_All.
            --- exact Hall1_r.
            --- apply All_Node. 
              ++ apply Nat.leb_le in e0. exact e0.
              ++ destruct Hh2 as [Hx2 [Hl2 Hr2]].
                 apply weaken_All with (P := fun y => x2 <= y).
                 ---- intros y Hy. apply Nat.leb_le in e0. lia.
                 ---- exact Hx2.
              ++ apply weaken_All with (P := fun y => x2 <= y).
                * intros y H. apply Nat.leb_le in e0. lia.
                * assert (All (fun y => x2 <= y) r2) as Hr2'.
                  {
                    destruct Hh2 as [_ Hhr2].
                    apply Hhr2.
                  }
                  exact Hr2'.
        -- exact Hh1_l.
        -- apply IHl with (h1 := r1) (h2 := Node _x0 x2 l2 r2); auto.

    - simpl.
      destruct Hh2 as [Hall2_l [Hall2_r [Hh2_l Hh2_r]]].
      repeat split.
      apply heap_order_make_node.
        -- exact Hall2_l.
        -- apply merge_All. apply weaken_All with (P := fun y => x2 <= y).
          --- intros y0 Hy0. apply Nat.leb_gt in e0. lia.
          --- assert (All (fun y => x2 <= y) (Node _x x1 l1 r1)) as Hx.
            {
              apply All_Node.
              * apply Nat.leb_gt in e0. lia. 
              * destruct Hh1 as [Hroot [Hall_l Hall_r]].
                apply weaken_All with (P := fun y => x1 <= y); try assumption.
                intros y Hy. apply Nat.leb_gt in e0. lia. 
              * destruct Hh1 as [Hroot [Hall_l Hall_r]].
                apply weaken_All with (P := fun y => x1 <= y); try assumption.
                intros y Hy. apply Nat.leb_gt in e0. lia.
            } exact Hx.
         --- exact Hall2_r.

        -- exact Hh2_l.
        -- assert (heap_order (merge (Node _x x1 l1 r1, r2))) as Hmerged.
          {
            apply IHl with (h1 := Node _x x1 l1 r1) (h2 := r2); auto.
          }
          exact Hmerged.
  Qed.

  (* ---------- Membership lemmas ---------- *)

  (* An element x belongs to make_node v l r if and only if x is the root value v or belongs to one of the subtrees *)
  Lemma Elem_make_node (x v : nat) (l r : LHeap):
      Elem x (make_node v l r) <-> x = v \/ Elem x l \/ Elem x r.
  Proof.
    unfold make_node.
    destruct (Nat.leb (rank l) (rank r)) eqn:Hleb.
    - split.
      + intros H. inversion H; subst; auto.
      + intros [-> | [Hl | Hr]].
        * apply Elem_root.
        * apply Elem_r. assumption.
        * apply Elem_l. assumption.
    - split.
      + intros H. inversion H; subst; auto.
      + intros [-> | [Hl | Hr]].
        * apply Elem_root.
        * apply Elem_l. assumption.
        * apply Elem_r. assumption.
  Qed.

  (* An element x belongs to Node n v l r if and only if x is the root value v or belongs to one of the subtrees *)
  Lemma Elem_Node (n : nat) (x v : nat) (l r : LHeap):
      Elem x (Node n v l r) <-> x = v \/ Elem x l \/ Elem x r.
  Proof.
    split.
    - intros H. inversion H; subst; eauto.
    - intros [-> | [Hl | Hr]].
      + apply Elem_root.
      + apply Elem_l. exact Hl.
      + apply Elem_r. exact Hr.
  Qed.

  (* An element x belongs to merge (h1, h2) if and only if x belongs to h1 or h2 *)
  Lemma Elem_merge (x : nat) (h1 h2 : LHeap):
      Elem x (merge (h1, h2)) <-> Elem x h1 \/ Elem x h2.
  Proof.
    remember (h1, h2) as p. revert h1 h2 Heqp.
    functional induction (merge p) using merge_ind; intros; inversion Heqp; subst; clear Heqp.
    - simpl. split; intro H; [right | destruct H; [inversion H |]]; assumption.
    - simpl. split; intro H; [left | destruct H; [|inversion H]]; assumption.
    - simpl. rewrite Elem_make_node. rewrite Elem_Node.
      rewrite Elem_Node. rewrite IHl with (h1 := r1) (h2 := Node _x0 x2 l2 r2). 
      + rewrite Elem_Node. tauto.
      + reflexivity. 
    - simpl. rewrite Elem_make_node. rewrite Elem_Node.
      rewrite Elem_Node. rewrite IHl with (h1 := Node _x x1 l1 r1) (h2 := r2). 
      + rewrite Elem_Node. tauto.
      + reflexivity. 
  Qed.

  End MergeLemmas.


  Module InsertLemmas.
  Import LeftistHeapNat.
  Import MergeLemmas.

  (* ---------- Size-related properties ---------- *)

  (* The size of inserting an element equals 1 plus the size of the original heap *)
  Lemma size_insert (x : nat) (h : LHeap):
      size (insert x h) = 1 + size h.
  Proof.
    unfold insert.
    rewrite size_merge.
    simpl. reflexivity.
  Qed.

  (* ---------- Leftist Invariant preservation ---------- *)

  (* A singleton heap always satisfies the leftist property as it doesn't have any children*)
  Lemma Satisfies_leftist_singleton (x : nat) :
      Satisfies_leftist (singleton x).
  Proof.
    intros. unfold singleton.
    apply Satisfies_leftist_Node; try constructor.
  Qed.

  (* Inserting an element into a heap produces a heap that satisfies the leftist property if the original heap did *)
  Lemma Satisfies_leftist_insert (x : nat) (h : LHeap):
      Satisfies_leftist h -> Satisfies_leftist (insert x h).
  Proof.
    unfold insert.
    apply Satisfies_leftist_merge; auto.
    constructor.
      + lia.
      + apply Satisfies_leftist_Leaf.
      + apply Satisfies_leftist_Leaf.
  Qed.

  (* ---------- Heap-Order Invariant preservation ---------- *)

  (* Inserting an element into a heap preserves the heap_order property if it held before *)
  Lemma insert_preserves_heap_order (x : nat) (h : LHeap):
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
  Lemma Elem_insert (x y : nat) (h : LHeap):
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
  Import LeftistHeapNat.
  Import MergeLemmas.

  (* ---------- Size-related properties ---------- *)

  (* Deleting the minimum element from a non-empty heap reduces its size by 1 *)
  Lemma size_delete_min (h : LHeap) :
    h <> Leaf ->
    size (delete_min h) = size h - 1.
  Proof.
    intros Hh.
    destruct h as [| r0 x l r].
    - contradiction.
    - simpl.
      rewrite size_merge.
      lia.
  Qed.

  (* ---------- Leftist Invariant preservation ---------- *)

  (* Deleting the minimum element produces a heap that satisfies the leftist property 
   if the original heap did *)
  Lemma Satisfies_leftist_delete_min (h : LHeap):
      Satisfies_leftist h -> Satisfies_leftist (delete_min h).
  Proof.
    intros H.
    unfold delete_min.
    destruct h as [| r x l r'].
    - constructor. 
    - inversion H; subst.
      apply Satisfies_leftist_merge; assumption.
  Qed.

  (* ---------- Heap-Order Invariant preservation ---------- *)

  (* Deleting the minimum element preserves the heap_order property if it held before *)
  Lemma delete_min_preserves_heap_order (h : LHeap):
      heap_order h ->
      heap_order (delete_min h).
  Proof.
    intros Hh.
    destruct h as [| r x l r'].
    - simpl. constructor.
    - simpl.
      destruct Hh as [Hroot [Hl Hr]].
      apply merge_preserves_heap_order. apply Hr. apply Hr.
  Qed.

  (* ---------- Membership lemmas ---------- *)

  (* An element x belongs to delete_min h if and only if
   x belonged to one of the subtrees of h (if h was non-empty) *)
  Lemma Elem_delete_min (x : nat) (h : LHeap):
      Elem x (delete_min h) <->
      match h with
      | Leaf => False
      | Node _ _ l r => Elem x l \/ Elem x r
      end.
  Proof.
    destruct h as [| rk val l r'].
    - simpl. split; intro H; inversion H.
    - simpl. rewrite Elem_merge. reflexivity.
  Qed.

  End DeleteLemmas.


  Module ExtractMinLemmas.
  Import LeftistHeapNat.
  Import MergeLemmas.

  (* ---------- Size-related properties ---------- *)

  (* If extract_min returns Some (x, h'), then the size of the original heap h is one more than the size of h' *)
  Lemma size_extract_min (x : nat) (h h' : LHeap):
      extract_min h = Some (x, h') -> size h = S (size h').
  Proof.
    intros Hext.
    destruct h as [| r y l r']; simpl in Hext.
    - discriminate.
    - inversion Hext; subst.
      simpl. rewrite size_merge. reflexivity.
  Qed.

  (* ---------- Leftist Invariant preservation ---------- *)

  (* If extract_min returns Some (x, h'), then h' satisfies the leftist property provided h did *)
  Lemma Satisfies_leftist_extract_min (x : nat) (h h' : LHeap):
      Satisfies_leftist h -> extract_min h = Some (x, h') ->
      Satisfies_leftist h'.
  Proof.
    intros Hbias Hext.
    destruct h as [| r y l r'].
    - simpl in Hext. discriminate.
    - simpl in Hext. inversion Hext; subst.
      inversion Hbias as [| r0 x0 l0 r0' Hr Hbl Hbr]; subst.
      apply Satisfies_leftist_merge; assumption.
  Qed.

  (* ---------- Heap-Order Invariant preservation ---------- *)

  (* If extract_min returns Some (x, h'), then h' satisfies heap_order provided h did *)
  Lemma extract_min_preserves_heap_order (x : nat) (h h' : LHeap):
      heap_order h ->
      extract_min h = Some (x, h') ->
      heap_order h'.
  Proof.
    intros Hh Hext.
    destruct h as [| r x0 l r0].
    - simpl in Hext. discriminate.
    - simpl in Hext. inversion Hext. subst h'.
      destruct Hh as [Hroot [Hl Hr]].
      apply merge_preserves_heap_order. apply Hr. apply Hr.
  Qed.

  (* ---------- Membership lemmas ---------- *)

  (* If extract_min returns Some (x, h'), then x was the minimum element at the root of h *)
  Lemma Elem_extract_min (x : nat) (h h' : LHeap):
      extract_min h = Some (x, h') ->
      Elem x h.
  Proof.
    intros Hext.
    destruct h as [| r y l r']; simpl in Hext.
    - discriminate.
    - inversion Hext; subst. constructor.
  Qed.

  End ExtractMinLemmas.

(*---------------------------- Leftist Heap Find_Min Lemmas ----------------------------*)

  Module FindMinLemmas.
  Import LeftistHeapNat.
  Import MergeLemmas.

  (* Helper function: computes the minimum of two option nat values *)
  Definition min_opt (o1 o2 : option nat) : option nat :=
    match o1, o2 with
    | None,  o       => o
    | o,     None    => o
    | Some x, Some y => Some (Nat.min x y)
    end.

(* ---------- Merge properties ---------- *)

  (* The minimum of a Node is its root value *)
  Lemma find_min_correct (v : nat) (n : nat) (l r : LHeap):
      find_min (Node n v l r) = Some v.
  Proof.
    simpl. reflexivity.
  Qed.

  (* The minimum of a make_node is its root value *)
  Lemma find_min_make_node (x : nat) (l r : LHeap):
      find_min (make_node x l r) = Some x.
  Proof.
    unfold find_min, make_node.
    destruct (Nat.leb (rank l) (rank r)); simpl; reflexivity.
  Qed.

  (* The minimum of merging two heaps is the minimum of the two heap roots *)
  Lemma find_min_merge (h1 h2 : LHeap) :
      find_min (merge (h1, h2)) = min_opt (find_min h1) (find_min h2).
  Proof.
    remember (h1, h2) as p eqn:Hp.
    functional induction (merge p) using merge_ind; inversion Hp; subst; simpl.
    - reflexivity.
    - destruct (find_min h1); simpl; reflexivity.
    - unfold min_opt.
      simpl. rewrite find_min_make_node.
      apply Nat.leb_le in e0.
      f_equal. lia.
    - unfold min_opt.
      rewrite find_min_make_node.
      f_equal. 
      assert (H : Nat.min x1 x2 = x2).
      {
        apply Nat.min_r.
        apply Nat.leb_gt in e0.
        lia.
      }
      rewrite H. reflexivity.
  Qed.

  (* ---------- Insert properties ---------- *)

  (* The minimum of inserting x into h equals the minimum of x and the minimum of h *)
  Lemma find_min_insert (x : nat) (h : LHeap):
      find_min (insert x h) = min_opt (Some x) (find_min h).
  Proof.
    unfold insert.
    rewrite find_min_merge.
    simpl. reflexivity.
  Qed.

  (* ---------- DeleteMin properties ---------- *)

  (* A heap has no minimum if and only if it is Leaf *)
  Lemma find_min_empty_iff (h : LHeap) :
      find_min h = None <-> h = Leaf.
  Proof.
    split.
    - destruct h; simpl; auto; discriminate.
    - intros ->. simpl. reflexivity.
  Qed.

  (* If a heap has no minimum, deleting the minimum yields Leaf *)
  Lemma find_min_delete_empty  (h : LHeap):
      find_min h = None -> delete_min h = Leaf.
  Proof.
    intros H.
    destruct h.
    - reflexivity.
    - simpl in H. discriminate.
  Qed.

  (* If the minimum of h is x and h satisfies heap_order,
   then deleting the minimum yields a heap whose minimum is at least x *)
  Lemma find_min_delete_next (h : LHeap) (x : nat) :
    heap_order h ->
    find_min h = Some x ->
    delete_min h <> Leaf ->
    exists m', find_min (delete_min h) = Some m' /\ x <= m'.
  Proof.
    intros Hord Hmin Hne.
    destruct h as [| r x' l r']; simpl in *; try contradiction.
    inversion Hmin; subst; clear Hmin.
    simpl. unfold delete_min. simpl.
    remember (merge (l, r')) as h'.
    destruct h' as [| r0 m' l' r''].
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

  End FindMinLemmas.

  (*---------------------------- Leftist Heap Permutation Lemmas ----------------------------*)

  Module PermutationLemmas.
  Import LeftistHeapNat.

(* ---------- Helper function ---------- *)

(* Flattens a heap into a list of its elements *)
  Fixpoint to_list (h : LHeap) : list nat :=
    match h with
    | Leaf => []
    | Node _ x l r => x :: (to_list l ++ to_list r)
    end.

  (* ---------- Merge permutation properties ---------- *)

  (* States that x followed by l1 and l2 is a permutation of l1 followed by x and l2 *)
  Lemma cons_app_comm (x : nat) (l1 l2 : list nat):
      Permutation (x :: l1 ++ l2) (l1 ++ x :: l2).
  Proof.
    induction l1 as [| y l1' IH].
    - simpl. reflexivity.
    - simpl.
      apply perm_trans with (y :: x :: l1' ++ l2).
      + apply perm_swap.
      + apply Permutation_cons. reflexivity. apply IH.
  Qed.

  (* The flattened list of make_node is a permutation of the left subtree, root, and right subtree *)
  Lemma to_list_make_node_perm (x : nat) (l r : LHeap) :
    Permutation
      (to_list (make_node x l r))
      (to_list l ++ x :: to_list r).
  Proof.
    unfold make_node.
    destruct (Nat.leb (rank l) (rank r)) eqn:H.
    - simpl. apply Permutation_cons_app. apply Permutation_app_comm.
    - simpl. apply cons_app_comm.
  Qed.

  (* Merging two heaps produces a heap whose elements are a permutation of both heap elements concatenated *)
  Lemma to_list_merge (h1 h2 : LHeap):
      Permutation (to_list (merge (h1,h2))) (to_list h1 ++ to_list h2).
  Proof.
    remember (h1, h2) as p eqn:Hp.
    revert h1 h2 Hp.
    functional induction (merge p) using merge_ind; intros; inversion Hp; subst; clear Hp.
    - reflexivity.
    - rewrite app_nil_r. reflexivity.
    - simpl.
      rewrite to_list_make_node_perm.
      assert (Permutation (to_list (merge (r1, Node _x0 x2 l2 r2))) (to_list r1 ++ to_list (Node _x0 x2 l2 r2))) as Hperm.
    { eapply IHl; eauto. }
      simpl in Hperm. rewrite <- Permutation_middle. constructor.
      rewrite Hperm. rewrite app_assoc. reflexivity.
    - simpl.
      rewrite to_list_make_node_perm.
      assert (Permutation (to_list (merge (Node _x x1 l1 r1, r2))) (to_list (Node _x x1 l1 r1) ++ to_list r2)) as Hperm.
    { eapply IHl; eauto. }
      simpl in Hperm. rewrite Hperm.
      rewrite <- Permutation_middle.
      rewrite <- Permutation_middle. 
      rewrite perm_swap.
      constructor. 
      rewrite <- Permutation_middle. 
      constructor. 
      rewrite Permutation_app_comm.
      repeat rewrite <- app_assoc. 
      apply Permutation_app_head. 
      apply Permutation_app_head.
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
  Lemma to_list_insert (x : nat) (h : LHeap) :
    Permutation (to_list (insert x h)) (x :: to_list h).
  Proof.
    unfold insert.
    rewrite to_list_merge.
    simpl.
    apply Permutation_refl.
  Qed.

  (* ---------- DeleteMin permutation properties ---------- *)

  (* Deleting the minimum element produces a heap whose elements are a permutation of the tail of the flattened list *)
  Lemma to_list_delete_min (x : nat) (h : LHeap) :
      find_min h = Some x ->
      Permutation (to_list (delete_min h)) (tl (to_list h)).
  Proof.
    intros Hmin.
    destruct h as [| r v l r'].
    - simpl in Hmin. discriminate.
    - simpl in Hmin. inversion Hmin; subst.
      simpl. rewrite to_list_merge.
      reflexivity.
  Qed.

  (* ---------- ExtractMin permutation properties ---------- *)

  (* If extract_min returns Some (x, h'), the original heap's elements are a permutation of x followed by h' elements *)
  Lemma to_list_extract_min (x : nat) (h h' : LHeap) :
      extract_min h = Some (x, h') ->
      Permutation (to_list h) (x :: to_list h').
  Proof.
    intros Hext.
    destruct h as [| r m l r']; simpl in Hext.
    - discriminate.
    - inversion Hext; subst.
      simpl.
      rewrite to_list_merge.
      reflexivity.
  Qed.



(*------------------------------------------------------*)
  Lemma All_to_list (P : nat -> Prop) (h : LHeap) :
    All P h -> forall y, In y (to_list h) -> P y.
  Proof.
    intros Hall y Hin.
    induction h as [| r x l IHl r' IHr]; simpl in *.
    - inversion Hin.
    - destruct Hall as [Px [Hl Hr]].
      simpl in Hin. destruct Hin as [-> | Hin].
      + exact Px.
      + apply in_app_or in Hin as [Hinl | Hinr].
        * apply IHl; assumption.
        * apply IHr; assumption.
  Qed.


  Lemma heap_order_root_min (h : LHeap) (x : nat) :
    heap_order h ->
    find_min h = Some x ->
    forall y, In y (to_list h) -> x <= y.
  Proof.
    intros Horder Hfind y Hin.
    unfold find_min in Hfind.
    destruct h as [| r v l r'].
    - discriminate Hfind.
    - simpl in Hfind. inversion Hfind; subst. 
      simpl in Hin.
      remember (to_list l ++ to_list r') as rest.
      simpl in *.
      destruct Horder as [Hvl [Hvr [Hl Hr]]].
      simpl in Hin.
      destruct Hin as [Hy | Hy]; subst.
      + lia.
      + apply in_app_or in Hy as [HinL | HinR].
        -- eapply All_to_list in Hvl; [|exact HinL]. lia.
        -- eapply All_to_list in Hvr; [|exact HinR]. lia.
  Qed.


  Fixpoint list_min (l : list nat) : option nat :=
    match l with
    | [] => None
    | x :: xs =>
        match list_min xs with
        | None => Some x
        | Some m => Some (Nat.min x m)
        end
    end.

  Lemma list_min_in (l : list nat) (m : nat) :
    list_min l = Some m -> In m l.
  Proof.
    induction l as [| x xs IH]; simpl.
    - discriminate.
    - destruct (list_min xs) eqn:E.
      -- intros H. injection H as <-.
        destruct (Nat.min_spec x n) as [[Hmin Hmax] | [Hmin Hmax]].
        + rewrite (Nat.min_l x n) by lia. apply in_eq.
        + right. apply IH. rewrite Hmax. reflexivity.
      -- intros H. injection H as <-. apply in_eq.
  Qed.

  Lemma find_min_correct (h : LHeap) (a : nat) :
    heap_order h ->
    find_min h = Some a ->
    list_min (to_list h) = Some a.
  Proof.
    intros Horder Hfind.
    destruct h as [| r v l r']; simpl in Hfind.
    - discriminate Hfind.
    - simpl in Hfind. inversion Hfind. subst a. clear Hfind.
      simpl. remember (to_list l ++ to_list r') as tail.
      destruct (list_min tail) eqn:Hrec.
      + pose proof (heap_order_root_min _ Horder eq_refl) as Hmin.
        assert (In n tail) as Hins.
          {
            subst tail; apply list_min_in; exact Hrec.
          }
        assert (v <= n) as Hv_le_n.
          { 
            apply Hmin.
            right. inversion Heqtail; subst. exact Hins.
          }
        rewrite (Nat.min_l v n) by lia.
        reflexivity.
      + reflexivity.
  Qed.






  End PermutationLemmas.



