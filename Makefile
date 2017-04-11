EXEC=test.exe
LIBS=basetype.o string.o round_stack.o list.o quicksort.o bin_search.o

#Possible provers: alt-ergo altgr-ergo coq coqide simplify vampire yices cvc3 z3 zenon isabelle why why3
PROOF_OB_DIR=.proof_obligations

PROVERS=why3:Alt-Ergo,why3:z3,why3:cvc4
#PROVERS=why3ide
DEFAULT_CONFIG="-cpp-extra-args=\"-I`frama-c -print-path`/libc\" -wp -wp-rte -wp-model Typed -wp-split -wp-par 1 -wp-proof-trace -wp-proof " $(PROVERS) " -wp-out" $(PROOF_OB_DIR) " -wp-script $(*F)_proofs.v"


all: $(LIBS) $(EXEC)

%.o: %.c %.h
	@echo "****************************************************"
	@echo $<
	@echo "****************************************************"
	@echo "clang analysis:"
	@clang --analyze $<
	@rm $(*F).plist
	@echo "------------------------------------"
	@echo "frama-c analysis:"
	@time frama-c -cpp-extra-args="-I`frama-c -print-path`/libc" -wp -wp-rte -wp-model Typed -wp-timeout 10 -wp-proof-trace -wp-prover $(PROVERS) -wp-out $(PROOF_OB_DIR)_$< $< #-then -werror-no-no-unknown -werror -werror-no-external
	@echo "------------------------------------"
	@echo "compilation:"
	@clang -c -o $@ $<
	@echo "------------------------------------"
	@echo "\n\n"

%.opt:
	@echo $(DEFAULT_CONFIG) > $@
	#@cat $@

%.o: %.c

%.h:
	touch $@

%.gui: %.c %.h %.opt
	@echo "****************************************************"
	@echo $<
	@echo "****************************************************"
	@echo "frama-c analysis:"
	@frama-c-gui -cpp-extra-args="-I`frama-c -print-path`/libc" -wp -wp-rte -wp-model Typed -wp-prover $(PROVERS) -wp-out $(PROOF_OB_DIR)_$< $<
	@echo "------------------------------------"
	@echo "\n\n"

%.i: %.c %.h
	@echo "****************************************************"
	@echo $<
	@echo "****************************************************"
	@time frama-c -cpp-extra-args="-I`frama-c -print-path`/libc" -cpp-command 'gcc -C -E -I. -x c' -typecheck $< -rte -rte-all -rte-precond -no-unicode -ocode $@ 
	@echo "------------------------------------"
	@echo "\n\n"

%.exe: %.o $(LIBS) 
	@clang $^ -o $@

clean:
	@rm -Rf $(LIBS) $(EXEC) *.o $(PROOF_OB_DIR)_* *.plist *.i

.DEFAULT :=
