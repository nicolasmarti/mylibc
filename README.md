This is a minimal C library, with specification in ACSL and verification using frama-c

* for now using
  * clang
  * frama-c
  * some provers: alt-ergo, coq, why3ide, ....
    there frama-c names are to be declared in the variable PROVERS of the Makefile
    

N.B.: 
* the bitmap library is not verifiable yet

Contensts:
* basetype:
  - contains: redefinition for integers, comparison and booleans type
  - provides: all comparison functions

* string:
  - contains: definition / specification for null terminated strings
  - provides: computation of string length, comparison of strings

* round_stack: a container preserving the order of inserted/extracted values
  - contains: definition for round stacks structure and their specifications
  - provides: insertion/extraction of elements at both the head and tail position of the stack

* list: some simply linked list
  - verification that a linked list has no cycle

* quicksort: formal verification

* bin_search