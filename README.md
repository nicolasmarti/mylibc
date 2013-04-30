This is a minimal C library, with specification in ACSL and verification using frama-c

* for now using
  * clang
  * frama-c-(fluorin/oxygen) + patch
  * framac-error plugin (https://github.com/sylvainnahas/framac-werror)
  
  * some provers: alt-ergo, coq, why3ide, ....
    there frama-c names are to be declared in the variable PROVERS of the Makefile
    

N.B.: 
* when WP is set for the Typed model, it seems to be able to generate goals for alt-ergo version 0.95
* Everything passes with alt-ergo 0.95
* the bitmap library is not verifiable yet due to some bug in frama-c          
* you can stipulate a set of option for frama-c per c files with a default available (<filename>.opt)
* inductive predicate code gen is completely wrong. A patch correct that
* with Fluorine, why3ide codegen does not work very well:
  - sometimes generated names cannot be parsed
  - sometimes codegen between different files conflict (e.g., with a make you will fail to process list.c, while make list.o will do ...)

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
  
* bitmap: a bitwise / treebased structure, allowing to search / keep track of flaged indexes efficiently

* list: some simply linked list
  