EXEC=test.exe
LIBS=basetype.o string.o

#Possible provers: alt-ergo altgr-ergo coq coqide simplify vampire yices cvc3 z3 zenon
PROVERS= alt-ergo,coq 

PROOF_OB_DIR=.proof_obligations


all: $(EXEC)

%.o: %.c %.h %.opt
	@echo "****************************************************"
	@echo $<
	@echo "****************************************************"
	@echo "clang analysis:"
	@clang --analyze $<
	@echo "------------------------------------"
	@echo "frama-c analysis:"
	@frama-c `cat $(*F).opt` $< -then -werror-no-no-unknown -werror -werror-no-external 
	@echo "------------------------------------"
	@echo "compilation:"
	@clang -c -o $@ $<
	@echo "------------------------------------"
	@echo "\n\n"

%.opt:
	echo "-wp -wp-rte -wp-warnings -wp-proof" $(PROVERS) "-wp-out" $(PROOF_OB_DIR) "-wp-script $(*F)_proofs.v" > $@

%.o: %.c

%.h:
	touch $@


%.exe: %.o $(LIBS) 
	@clang $^ -o $@

clean:
	@rm -Rf $(LIBS) $(EXEC) *.o $(PROOF_OB_DIR) *.plist

.DEFAULT :=
