EXEC=test.exe
LIBS=basetype.o string.o

#Possible provers: alt-ergo altgr-ergo coq coqide simplify vampire yices cvc3 z3 zenon
PROVERS= alt-ergo,coq 

PROOF_OB_DIR=.proof_obligations

FRAMAC=frama-c
FRAMACFLAGS=-wp -wp-rte -wp-warnings -wp-proof $(PROVERS) -wp-out $(PROOF_OB_DIR) -wp-script $(*F)_proofs.v #-wp-print

all: $(EXEC)

%.o: %.c %.h
	@echo "****************************************************"
	@echo $<
	@echo "****************************************************"
	@echo "clang analysis:"
	@clang --analyze $<
	@echo "------------------------------------"
	@echo "frama-c analysis:"
	@$(FRAMAC) $(FRAMACFLAGS) $< -then -werror-no-no-unknown -werror -werror-no-external 
	@echo "------------------------------------"
	@echo "compilation:"
	@clang -c -o $@ $<
	@echo "------------------------------------"
	@echo "\n\n"


%.o: %.c
	@echo "****************************************************"
	@echo $<
	@echo "****************************************************"
	@echo "clang analysis:"
	@clang --analyze $<
	@echo "------------------------------------"
	@echo "frama-c analysis:"
	@$(FRAMAC) $(FRAMACFLAGS) $< -then -werror-no-no-unknown -werror -werror-no-external 
	@echo "------------------------------------"
	@echo "compilation:"
	@clang -c -o $@ $<
	@echo "------------------------------------"
	@echo "\n\n"

%.exe: %.o $(LIBS) 
	@clang $^ -o $@

clean:
	@rm -Rf $(LIBS) $(EXEC) *.o $(PROOF_OB_DIR) *.plist

