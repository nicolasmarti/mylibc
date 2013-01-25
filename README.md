This is a minimal C library, with specification in ACSL and verification using frama-c

* for now using
  * clang
  * frama-c-oxygen
  * framac-error plugin (https://github.com/sylvainnahas/framac-werror)
  
  * some provers: alt-ergo, coq, ....
    there frama-c names are to be declared in the variable PROVERS of the Makefile
    
    N.B.: for proof in coq, the script by default is (C-name)_proofs.v (c.f. FRAMACFLAGS in Makefile)
    