CC=clang
CFLAGS= 
LDFLAGS=
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
	@clang --analyze $<
	@echo "------------------------------------"
	@$(FRAMAC) $(FRAMACFLAGS) $< -then -werror-no-no-unknown -werror -werror-no-external 
	@echo "------------------------------------"
	@$(CC) -c -o $@ $(CFLAGS) $<
	@echo "\n\n"

%.o: %.c
	@echo "****************************************************"
	@echo $<
	@echo "****************************************************"
	@clang --analyze $<
	@echo "------------------------------------"
	@$(FRAMAC) $(FRAMACFLAGS) $< -then -werror-no-no-unknown -werror -werror-no-external 
	@echo "------------------------------------"
	@$(CC) -c -o $@ $(CFLAGS) $<
	@echo "\n\n"

%.exe: %.o $(LIBS) 
	@$(CC) $(CFLAGS) $^ $(LDFLAGS) -o $@

clean:
	@rm -Rf $(LIBS) $(EXEC) *.o $(PROOF_OB_DIR) *.plist



gui:
	frama-c-gui $(FRAMACFLAGS) $1