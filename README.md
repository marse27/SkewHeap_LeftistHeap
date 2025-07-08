This project implements **Leftist Heaps** and **Skew Heaps** in Rocq, providing formal proofs for key properties and operations on these heap data structures.

## Structure

The project contains two main modules:

- `LeftistHeapNat`: An implementation of Leftist Heaps over `nat`.
- `SkewHeapNat`: An implementation of Skew Heaps over `nat`.

Both modules include definitions, operations, and associated lemmas to verify correctness properties such as heap order and element membership.

---

## Features

### Leftist Heap (LeftistHeapNat)

- Heap data type: `LHeap`
- Operations:
  - `merge`
  - `insert`
  - `delete_min`
  - `find_min`
  - `extract_min`
- Properties:
  - Heap order (`heap_order`)
  - Leftist structure (`Satisfies_leftist`)
  - Size (`size_merge`)
  - Element membership (`Elem`)
  - Conversion to list (`to_list`)
- Proofs of:
  - Preservation of heap order after operations
  - Correctness of merge, insert, deleteMin, find_min, extractMin
  - Permutation equivalence of `to_list` after operations

---

### Skew Heap (SkewHeapNat)

- Heap data type: `SHeap`
- Operations:
  - `merge`
  - `insert`
  - `delete_min`
  - `find_min`
  - `extract_min`
- Properties:
  - Heap order (`heap_order`)
  - Size (`size_merge`)
  - Element membership (`Elem`)
  - Conversion to list (`to_list`)
- Proofs of:
  - Preservation of heap order after operations
  - Correctness of merge, insert, delete_min, find_min, extract_min
  - Permutation equivalence of `to_list` after operations

---

## Files

- `LeftistHeap.v`  
  Contains the Leftist Heap implementation and proofs.
  
- `SkewHeap.v`  
  Contains the Skew Heap implementation and proofs.

---

## Example Properties Proved

- `merge_preserves_heap_order`  
- `insert_preserves_heap_order`  
- `deleteMin_preserves_heap_order`  
- `find_min_merge`  
- `Elem_merge`  
- `to_list_merge`  
- `to_list_delete_min`


## Installation and Running

### Prerequisites

- [Coq](https://coq.inria.fr/) (version 8.12 or later recommended)

### Installation

Download and install from https://coq.inria.fr/download

Clone the repository: 
``` bash
    git clone https://github.com/marse27/SkewHeap_LeftistHeap
```

Open LeftistHeap.v or SkewHeap.v in a Rocq enviroment and navigate through the proofs.
