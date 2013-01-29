EXEC=test.exe
LIBS=basetype.o string.o

#Possible provers: alt-ergo altgr-ergo coq coqide simplify vampire yices cvc3 z3 zenon isabelle why why3
PROVERS= alt-ergo

PROOF_OB_DIR=.proof_obligations

DEFAULT_CONFIG="-wp -wp-rte -wp-warnings -wp-model Typed -wp-qed -wp-split -wp-par 1 -wp-dot -wp-proof" $(PROVERS) "-wp-out" $(PROOF_OB_DIR) "-wp-script $(*F)_proofs.v"

all: $(EXEC)

%.o: %.c %.h %.opt
	@echo "****************************************************"
	@echo $<
	@echo "****************************************************"
	@echo "clang analysis:"
	@clang --analyze $<
	@rm $(*F).plist
	@echo "------------------------------------"
	@echo "frama-c analysis:"
	@frama-c `cat $(*F).opt` $< -then -werror-no-no-unknown -werror -werror-no-external 
	@echo "------------------------------------"
	@echo "compilation:"
	@clang -c -o $@ $<
	@echo "------------------------------------"
	@echo "\n\n"

%.opt:
	echo $(DEFAULT_CONFIG) > $@

%.o: %.c

%.h:
	touch $@


%.exe: %.o $(LIBS) 
	@clang $^ -o $@

clean:
	@rm -Rf $(LIBS) $(EXEC) *.o $(PROOF_OB_DIR) *.plist

.DEFAULT :=
